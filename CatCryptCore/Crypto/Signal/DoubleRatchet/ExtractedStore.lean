/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signal.DoubleRatchet.ExtractedCorrespondence
import HaxLean.FoldRange

/-!
# The store of skipped message keys of the extracted double ratchet

The extracted ratchet state (`RatchetState_T`) holds the store `MKSKIPPED` of skipped message
keys as `MAX_STORED = 32` slots in four arrays: slot `j` is occupied when `sk_used[j]` holds,
and then holds the ratchet key `sk_dh[j]`, the message number `sk_n[j]` and the message key
`sk_mk[j]`. The view `storeOf s` is the finite set of the triples of the occupied slots.

The store functions of the crate are loops over all 32 slots: `store_find` returns the
first occupied slot with a given ratchet key and message number, `store_take` returns the
message key of a slot and clears it, `store_insert` writes the first free slot.
`skip_message_keys` steps the receiving chain up to a message number and stores the message
key of each skipped position under the remote ratchet key. Under the equations `DrHom` of the
primitives, the stored keys are the encoded keys `chainKey F σ k` of the chain of `F` from the
state `σ` of the receiving chain. Message numbers are unbounded integers in the theorems; the
crate holds them as `u32`.

## Main definitions

* `slotAt`, `storeOf` — a slot of the store and the set of the occupied slots
* `StoreHit` — a slot is occupied by a given ratchet key and message number
* `SlotsInj` — distinct occupied slots hold distinct triples
* `SkipInv` — the loop invariant of `skip_message_keys`

## Main results

* `store_find_spec`, `store_take_eq`, `storeOf_store_take`, `store_insert_spec`,
  `storeOf_insert_slot`, `store_insert_some` — the three store functions
* `skip_message_keys_ckr_none`, `skip_message_keys_far` — skipping without a receiving chain
  and beyond `MAX_SKIP`
* `skip_message_keys_enc` — skipping to `until` adds the encoded keys of the positions
  `nr ≤ i < until` of the receiving chain to the store and leaves the encoded chain state after
  `until - nr` steps
* `try_skipped_none_iff`, `try_skipped_some`, `try_skipped_enc` — the lookup of a stored key
* `ratchet_receive_key_old`, `ratchet_receive_key_new` — the key derivation of a receipt on a
  known and on a new ratchet key
* `ratchet_decrypt_eq` — decryption is the key derivation followed by `aead_decrypt`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.DoubleRatchet.ExtractedStore

open CatCrypt.Crypto CatCrypt.Crypto.Messaging CatCrypt.Crypto.Assumptions
open CatCrypt.Crypto.Signal.DoubleRatchet.ExtractedCorrespondence
open CatCryptCore.Examples.CyclicGroupDDH
open Doubleratchet

noncomputable section

/-! ## The view of the store -/

/-- The slot `j` of the store of `s`: its ratchet key, message number and message key. -/
def slotAt (s : RatchetState_T) (j : Int) : Array Int × Int × Array Int :=
  (Hax.index («.sk_dh» s) j, Hax.index («.sk_n» s) j, Hax.index («.sk_mk» s) j)

/-- The store of skipped message keys of `s`: the triples of the occupied slots among the
`MAX_STORED = 32` slots. -/
def storeOf (s : RatchetState_T) : Finset (Array Int × Int × Array Int) :=
  ((Finset.range 32).filter fun j : ℕ => Hax.index («.sk_used» s) (j : Int) = true).image
    fun j : ℕ => slotAt s j

/-- The slot `j` of `s` is occupied by the ratchet key `dh` (under `eq32`) and the message
number `n`. -/
def StoreHit (s : RatchetState_T) (dh : Array Int) (n : Int) (j : Int) : Prop :=
  Hax.index («.sk_used» s) j = true ∧ eq32 (Hax.index («.sk_dh» s) j) dh = true ∧
    Hax.index («.sk_n» s) j = n

/-- Distinct occupied slots of `s` hold distinct triples. -/
def SlotsInj (s : RatchetState_T) : Prop :=
  ∀ j k : ℕ, j < 32 → k < 32 → Hax.index («.sk_used» s) (j : Int) = true →
    Hax.index («.sk_used» s) (k : Int) = true → slotAt s j = slotAt s k → j = k

/-- Membership in the store: an occupied slot holds the triple. -/
theorem mem_storeOf (s : RatchetState_T) (e : Array Int × Int × Array Int) :
    e ∈ storeOf s ↔ ∃ j : ℕ, j < 32 ∧ Hax.index («.sk_used» s) (j : Int) = true ∧
      slotAt s j = e := by
  simp only [storeOf, Finset.mem_image, Finset.mem_filter, Finset.mem_range, and_assoc]

/-- The store of a state depends only on its four store arrays. -/
theorem storeOf_eq_of_store {s t : RatchetState_T} (h₁ : «.sk_used» s = «.sk_used» t)
    (h₂ : «.sk_dh» s = «.sk_dh» t) (h₃ : «.sk_n» s = «.sk_n» t) (h₄ : «.sk_mk» s = «.sk_mk» t) :
    storeOf s = storeOf t := by
  unfold storeOf slotAt
  rw [h₁, h₂, h₃, h₄]

/-! ## `store_find` -/

/-- **`store_find`.** When it reports a hit, its index `i < 32` is the first slot occupied by
`(dh, n)`; when it reports none, no slot is. -/
theorem store_find_spec (s : RatchetState_T) (dh : Array Int) (n : Int) :
    ((store_find s dh n).1 = true →
      0 ≤ (store_find s dh n).2 ∧ (store_find s dh n).2 < 32 ∧
        StoreHit s dh n (store_find s dh n).2 ∧
        ∀ j, 0 ≤ j → j < (store_find s dh n).2 → ¬ StoreHit s dh n j) ∧
    ((store_find s dh n).1 = false → ∀ j, 0 ≤ j → j < 32 → ¬ StoreHit s dh n j) := by
  unfold store_find MAX_STORED
  refine Hax.foldRange_induct (P := fun i (acc : Bool × Int) =>
    (acc.1 = true → 0 ≤ acc.2 ∧ acc.2 < i ∧ StoreHit s dh n acc.2 ∧
        ∀ j, 0 ≤ j → j < acc.2 → ¬ StoreHit s dh n j) ∧
      (acc.1 = false → ∀ j, 0 ≤ j → j < i → ¬ StoreHit s dh n j)) (by decide) ?_ ?_
  · simp only [Bool.false_eq_true, false_implies, true_and]
    intro _ _ _ h; omega
  · rintro i ⟨b, k⟩ hi0 _ ⟨ht, hf⟩
    simp only [StoreHit, Hax.band, Hax.Not, Hax.HaxNot.not, Hax.beq] at ht hf ⊢
    cases b <;> grind

/-! ## `store_take` -/

/-- **`store_take`.** The message key of slot `i` and the state with slot `i` cleared. -/
theorem store_take_eq (sk pk rk : Array Int) (dhr cks ckr : Option (Array Int))
    (ns nr pn : Int) (u : Array Bool) (sd : Array (Array Int)) (sn : Array Int)
    (sm : Array (Array Int)) (i : Int) :
    store_take (sk, pk, dhr, rk, cks, ckr, ns, nr, pn, u, sd, sn, sm) i =
      ((sk, pk, dhr, rk, cks, ckr, ns, nr, pn, Hax.array_update u i false,
        Hax.array_update sd i (Hax.repeat_ 0 32), Hax.array_update sn i 0,
        Hax.array_update sm i (Hax.repeat_ 0 32)), Hax.index sm i) := by
  simp only [store_take, «.sk_used», «.sk_dh», «.sk_n», «.sk_mk», Hax.struct_update_fst,
    Hax.struct_update_snd]

/-- The store after `store_take` at an occupied slot `i` of a store of distinct slots is the
store without the triple of slot `i`. -/
theorem storeOf_store_take (sk pk rk : Array Int) (dhr cks ckr : Option (Array Int))
    (ns nr pn : Int) (u : Array Bool) (sd : Array (Array Int)) (sn : Array Int)
    (sm : Array (Array Int)) (hu : u.size = 32) (hd : sd.size = 32) (hn : sn.size = 32)
    (hm : sm.size = 32) (i : ℕ) (hi : i < 32) (hused : Hax.index u (i : Int) = true)
    (hinj : SlotsInj (sk, pk, dhr, rk, cks, ckr, ns, nr, pn, u, sd, sn, sm)) :
    storeOf (store_take (sk, pk, dhr, rk, cks, ckr, ns, nr, pn, u, sd, sn, sm) i).1 =
      (storeOf (sk, pk, dhr, rk, cks, ckr, ns, nr, pn, u, sd, sn, sm)).erase
        (slotAt (sk, pk, dhr, rk, cks, ckr, ns, nr, pn, u, sd, sn, sm) i) := by
  ext e
  simp only [store_take_eq, Finset.mem_erase, mem_storeOf, slotAt, «.sk_used», «.sk_dh»,
    «.sk_n», «.sk_mk»] at hinj ⊢
  unfold SlotsInj at hinj
  simp only [slotAt, «.sk_used», «.sk_dh», «.sk_n», «.sk_mk»] at hinj
  constructor
  · rintro ⟨j, hj, hju, rfl⟩
    have hji : j ≠ i := by
      rintro rfl
      grind
    grind
  · rintro ⟨hne, j, hj, hju, rfl⟩
    have hji : j ≠ i := by
      rintro rfl
      exact hne rfl
    grind

/-! ## `store_insert` -/

/-- **`store_insert`.** On a store whose slots are all occupied it returns nothing; otherwise
it writes `(d, n, mk)` into the first free slot `i`. -/
theorem store_insert_spec (sk pk rk : Array Int) (dhr cks ckr : Option (Array Int))
    (ns nr pn : Int) (u : Array Bool) (sd : Array (Array Int)) (sn : Array Int)
    (sm : Array (Array Int)) (d : Array Int) (n : Int) (mk : Array Int) :
    (store_insert (sk, pk, dhr, rk, cks, ckr, ns, nr, pn, u, sd, sn, sm) d n mk = none ∧
        ∀ j : ℕ, j < 32 → Hax.index u (j : Int) = true) ∨
      ∃ i : ℕ, i < 32 ∧ Hax.index u (i : Int) = false ∧
        (∀ j : ℕ, j < i → Hax.index u (j : Int) = true) ∧
        store_insert (sk, pk, dhr, rk, cks, ckr, ns, nr, pn, u, sd, sn, sm) d n mk =
          some (sk, pk, dhr, rk, cks, ckr, ns, nr, pn, Hax.array_update u i true,
            Hax.array_update sd i d, Hax.array_update sn i n, Hax.array_update sm i mk) := by
  unfold store_insert MAX_STORED
  simp only
  set FUN : Int → RatchetState_T × Bool → RatchetState_T × Bool := fun i x =>
        if Hax.band (!x.2) (Hax.Not (Hax.index («.sk_used» x.1) i)) = true then
          (RatchetState («.dhs_sk» x.1) («.dhs_pk» x.1) («.dhr» x.1) («.rk» x.1) («.cks» x.1)
            («.ckr» x.1) («.ns» x.1) («.nr» x.1) («RatchetState.pn» x.1)
            (Hax.array_update («.sk_used» x.1) i true) (Hax.array_update («.sk_dh» x.1) i d)
            (Hax.array_update («.sk_n» x.1) i n) (Hax.array_update («.sk_mk» x.1) i mk), true)
        else (x.1, x.2) with hFUN
  have hinv := Hax.foldRange_induct (lo := 0) (hi := 32)
      (init := ((sk, pk, dhr, rk, cks, ckr, ns, nr, pn, u, sd, sn, sm), false)) (f := FUN)
      (P := fun k (acc : RatchetState_T × Bool) =>
        (acc.2 = false → acc.1 = (sk, pk, dhr, rk, cks, ckr, ns, nr, pn, u, sd, sn, sm) ∧
          ∀ j : ℕ, (j : Int) < k → Hax.index u (j : Int) = true) ∧
        (acc.2 = true → ∃ i : ℕ, (i : Int) < k ∧ Hax.index u (i : Int) = false ∧
          (∀ j : ℕ, j < i → Hax.index u (j : Int) = true) ∧
          acc.1 = (sk, pk, dhr, rk, cks, ckr, ns, nr, pn, Hax.array_update u i true,
            Hax.array_update sd i d, Hax.array_update sn i n, Hax.array_update sm i mk)))
        (by decide) ?_ ?_
  · grind
  · grind
  · rintro k ⟨st', dn'⟩ hk0 _ ⟨hf, ht⟩
    cases dn'
    · obtain ⟨rfl, hall⟩ := hf rfl
      simp only [hFUN, «.sk_used», «.sk_dh», «.sk_n», «.sk_mk», «.dhs_sk», «.dhs_pk», «.dhr»,
        «.rk», «.cks», «.ckr», «.ns», «.nr», «RatchetState.pn», RatchetState, Hax.band, Hax.Not,
        Hax.HaxNot.not, Bool.not_false, Bool.true_and]
      by_cases hk : Hax.index u k = true
      · simp only [hk, Bool.not_true, Bool.false_eq_true, ite_false, true_implies,
          false_implies, and_true]
        refine ⟨trivial, fun j hj => ?_⟩
        by_cases hjk : (j : Int) < k
        · exact hall j hjk
        · rw [show (j : Int) = k by omega]; exact hk
      · simp only [hk, Bool.not_false, ite_true, Bool.true_eq_false, false_implies,
          true_implies, true_and]
        refine ⟨k.toNat, by omega, ?_, fun j hj => hall j (by omega), ?_⟩
        · rw [Int.toNat_of_nonneg hk0]; simpa using hk
        · rw [Int.toNat_of_nonneg hk0]
    · obtain ⟨i, hi, hfree, hfirst, hst⟩ := ht rfl
      simp only [hFUN, Hax.band, Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false,
        Bool.true_eq_false, false_implies, true_implies, true_and]
      exact ⟨i, by omega, hfree, hfirst, hst⟩

/-- The store after writing `(d, n, mk)` into the free slot `i` of a store of 32 slots is the
store with `(d, n, mk)` added. -/
theorem storeOf_insert_slot (sk pk rk : Array Int) (dhr cks ckr : Option (Array Int))
    (ns nr pn : Int) (u : Array Bool) (sd : Array (Array Int)) (sn : Array Int)
    (sm : Array (Array Int)) (hu : u.size = 32) (hd : sd.size = 32) (hn : sn.size = 32)
    (hm : sm.size = 32) (d : Array Int) (n : Int) (mk : Array Int) (i : ℕ) (hi : i < 32)
    (hfree : Hax.index u (i : Int) = false) :
    storeOf (sk, pk, dhr, rk, cks, ckr, ns, nr, pn, Hax.array_update u i true,
        Hax.array_update sd i d, Hax.array_update sn i n, Hax.array_update sm i mk) =
      insert (d, n, mk) (storeOf (sk, pk, dhr, rk, cks, ckr, ns, nr, pn, u, sd, sn, sm)) := by
  ext e
  simp only [Finset.mem_insert, mem_storeOf, slotAt, «.sk_used», «.sk_dh», «.sk_n», «.sk_mk»]
  constructor
  · rintro ⟨j, hj, hju, rfl⟩
    by_cases hji : j = i
    · subst hji
      grind
    · grind
  · rintro (rfl | ⟨j, hj, hju, rfl⟩)
    · grind
    · have hji : j ≠ i := by
        rintro rfl
        grind
      grind

/-- **`store_insert` on success.** The result keeps the nine components before the store, has
32 slots and its store is the store with `(d, n, mk)` added. -/
theorem store_insert_some (sk pk rk : Array Int) (dhr cks ckr : Option (Array Int))
    (ns nr pn : Int) (u : Array Bool) (sd : Array (Array Int)) (sn : Array Int)
    (sm : Array (Array Int)) (hu : u.size = 32) (hd : sd.size = 32) (hn : sn.size = 32)
    (hm : sm.size = 32) (d : Array Int) (n : Int) (mk : Array Int) (t : RatchetState_T)
    (h : store_insert (sk, pk, dhr, rk, cks, ckr, ns, nr, pn, u, sd, sn, sm) d n mk = some t) :
    ∃ (u' : Array Bool) (sd' : Array (Array Int)) (sn' : Array Int) (sm' : Array (Array Int)),
      t = (sk, pk, dhr, rk, cks, ckr, ns, nr, pn, u', sd', sn', sm') ∧ u'.size = 32 ∧
        sd'.size = 32 ∧ sn'.size = 32 ∧ sm'.size = 32 ∧
        storeOf t = insert (d, n, mk)
          (storeOf (sk, pk, dhr, rk, cks, ckr, ns, nr, pn, u, sd, sn, sm)) := by
  rcases store_insert_spec sk pk rk dhr cks ckr ns nr pn u sd sn sm d n mk with
    ⟨hnone, _⟩ | ⟨i, hi, hfree, _, hsome⟩
  · rw [hnone] at h
    exact absurd h (by simp)
  · rw [hsome, Option.some.injEq] at h
    subst h
    refine ⟨_, _, _, _, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · grind
    · grind
    · grind
    · grind
    · exact storeOf_insert_slot sk pk rk dhr cks ckr ns nr pn u sd sn sm hu hd hn hm d n mk i hi
        hfree

/-! ## `skip_message_keys` -/

section Skip

variable {Dp : Type} [Inhabited Dp] [DoubleRatchetDeps Dp]
  {RK Sa W Ct Sk A Hd : Type} [SampleableType W] {G : Type} [CG : CyclicGroup G]
  {R : PRGDef (RK × G) (RK × Sa)} {F : PRGDef Sa (W × Sa)} {D : AEADDef W Ct (A × Hd)}
  {ptLen : Int} {encR : RK → Array Int} {encG : G → Array Int} {encSk : Sk → Array Int}
  {decE : Sk → CG.Exp} {encS : Sa → Array Int} {encW : W → Array Int}
  {encPt : W → Array Int} {encC : Ct → Array Int} {encAD : A → Array Int}
  {encH : Hd → MessageHeader_T}

/-- **Skipping without a receiving chain.** `skip_message_keys` at a state without a receiving
chain key and a target within `MAX_SKIP` of `nr` returns the state. -/
theorem skip_message_keys_ckr_none (sk pk rk : Array Int) (dhr cks : Option (Array Int))
    (ns nr pn : Int) (u : Array Bool) (sd : Array (Array Int)) (sn : Array Int)
    (sm : Array (Array Int)) (untl : Int) (hb : untl - nr ≤ 16) :
    skip_message_keys (D := Dp) (sk, pk, dhr, rk, cks, none, ns, nr, pn, u, sd, sn, sm) untl =
      some (sk, pk, dhr, rk, cks, none, ns, nr, pn, u, sd, sn, sm) := by
  simp only [skip_message_keys, «.nr», «.ckr», Hax.band, Hax.gt, Hax.sub, MAX_SKIP]
  grind

/-- **Skipping beyond `MAX_SKIP`.** `skip_message_keys` refuses a target more than
`MAX_SKIP = 16` positions beyond `nr`. -/
theorem skip_message_keys_far (s : RatchetState_T) (untl : Int) (hb : 16 < untl - «.nr» s) :
    skip_message_keys (D := Dp) s untl = none := by
  simp only [skip_message_keys, Hax.band, Hax.gt, Hax.sub, MAX_SKIP]
  grind

/-- The invariant of the loop of `skip_message_keys` after `i` of its `MAX_SKIP` iterations,
for `m` positions to skip: while no insertion has failed, the state has stepped the chain from
`σ` `min i m` times, advanced `nr` by as much, kept the other components and added the encoded
keys of the skipped positions under the ratchet key `d` to the store of `s0`. -/
def SkipInv (F : PRGDef Sa (W × Sa)) (encS : Sa → Array Int) (encW : W → Array Int) (σ : Sa)
    (sk pk rk : Array Int) (dhr cks : Option (Array Int)) (ns nr pn : Int)
    (s0 : RatchetState_T) (d : Array Int) (m : ℕ) (i : Int)
    (acc : RatchetState_T × Array Int × Bool) : Prop :=
  acc.2.2 = true → ∃ (u' : Array Bool) (sd' : Array (Array Int)) (sn' : Array Int)
    (sm' : Array (Array Int)),
    acc.1 = (sk, pk, dhr, rk, cks,
      some (encS ((fun s => (F.stretch s).2)^[min i.toNat m] σ)), ns,
      nr + ((min i.toNat m : ℕ) : Int), pn, u', sd', sn', sm') ∧
    acc.2.1 = encS ((fun s => (F.stretch s).2)^[min i.toNat m] σ) ∧
    u'.size = 32 ∧ sd'.size = 32 ∧ sn'.size = 32 ∧ sm'.size = 32 ∧
    storeOf acc.1 = storeOf s0 ∪
      (Finset.range (min i.toNat m)).image fun k : ℕ => (d, nr + (k : Int), encW (chainKey F σ k))

/-- **Skipping message keys at an encoded receiving chain.** If `skip_message_keys` at a state
whose receiving chain key is the encoding of `σ` succeeds with the target `untl`, then
`m = (untl - nr).toNat ≤ MAX_SKIP`; the result keeps the components other than `ckr`, `nr` and
the store; its receiving chain key is the encoding of the state of `F` after `m` steps from `σ`;
`nr` is advanced by `m`; and its store is the store of the input with the encoded keys
`chainKey F σ k` at the positions `nr + k`, `k < m`, under the remote ratchet key `DHr` (the zero
array when there is none). -/
theorem skip_message_keys_enc
    (h : DrHom Dp G R F D ptLen encR encG encSk decE encS encW encPt encC encAD encH)
    (σ : Sa) (sk pk rk : Array Int) (dhr cks : Option (Array Int)) (ns nr pn : Int)
    (u : Array Bool) (sd : Array (Array Int)) (sn : Array Int) (sm : Array (Array Int))
    (hu : u.size = 32) (hd : sd.size = 32) (hn : sn.size = 32) (hm : sm.size = 32)
    (untl : Int) (s' : RatchetState_T)
    (hs : skip_message_keys (D := Dp)
      (sk, pk, dhr, rk, cks, some (encS σ), ns, nr, pn, u, sd, sn, sm) untl = some s') :
    (untl - nr).toNat ≤ 16 ∧
    ∃ (u' : Array Bool) (sd' : Array (Array Int)) (sn' : Array Int) (sm' : Array (Array Int)),
      s' = (sk, pk, dhr, rk, cks,
        some (encS ((fun s => (F.stretch s).2)^[(untl - nr).toNat] σ)), ns,
        nr + (((untl - nr).toNat : ℕ) : Int), pn, u', sd', sn', sm') ∧
      u'.size = 32 ∧ sd'.size = 32 ∧ sn'.size = 32 ∧ sm'.size = 32 ∧
      storeOf s' = storeOf (sk, pk, dhr, rk, cks, some (encS σ), ns, nr, pn, u, sd, sn, sm) ∪
        (Finset.range (untl - nr).toNat).image
          fun k : ℕ => (dhr.getD (Hax.repeat_ 0 32), nr + (k : Int), encW (chainKey F σ k)) := by
  have h16 : untl - nr ≤ 16 := by
    by_contra hc
    rw [skip_message_keys_far _ _ (by simp only [«.nr»]; omega)] at hs
    exact absurd hs (by simp)
  refine ⟨by omega, ?_⟩
  have hg : Hax.band (Hax.gt untl
      («.nr» (sk, pk, dhr, rk, cks, some (encS σ), ns, nr, pn, u, sd, sn, sm)))
      (Hax.gt (Hax.sub untl
        («.nr» (sk, pk, dhr, rk, cks, some (encS σ), ns, nr, pn, u, sd, sn, sm))) MAX_SKIP) =
      false := by
    simp only [Hax.band, Hax.gt, Hax.sub, MAX_SKIP, «.nr», Bool.and_eq_false_iff]
    grind
  unfold skip_message_keys at hs
  rw [hg] at hs
  simp only [Bool.false_eq_true, ite_false, «.nr», «.ckr», «.dhr»] at hs
  clear hg
  obtain ⟨st, ck, hinv, rfl⟩ : ∃ st ck, SkipInv F encS encW σ sk pk rk dhr cks ns nr pn
      (sk, pk, dhr, rk, cks, some (encS σ), ns, nr, pn, u, sd, sn, sm)
      (dhr.getD (Hax.repeat_ 0 32)) (untl - nr).toNat MAX_SKIP (st, ck, true) ∧ s' = st := by
    revert hs
    suffices key : ∀ f : Int → RatchetState_T × Array Int × Bool →
        RatchetState_T × Array Int × Bool,
        (∀ i acc, 0 ≤ i → i < MAX_SKIP →
          SkipInv F encS encW σ sk pk rk dhr cks ns nr pn
            (sk, pk, dhr, rk, cks, some (encS σ), ns, nr, pn, u, sd, sn, sm)
            (dhr.getD (Hax.repeat_ 0 32)) (untl - nr).toNat i acc →
          SkipInv F encS encW σ sk pk rk dhr cks ns nr pn
            (sk, pk, dhr, rk, cks, some (encS σ), ns, nr, pn, u, sd, sn, sm)
            (dhr.getD (Hax.repeat_ 0 32)) (untl - nr).toNat (i + 1) (f i acc)) →
        (if (Hax.foldRange 0 MAX_SKIP
            ((sk, pk, dhr, rk, cks, some (encS σ), ns, nr, pn, u, sd, sn, sm), encS σ, true)
            f).2.2 = true then
          some (Hax.foldRange 0 MAX_SKIP
            ((sk, pk, dhr, rk, cks, some (encS σ), ns, nr, pn, u, sd, sn, sm), encS σ, true)
            f).1 else none) = some s' →
        ∃ st ck, SkipInv F encS encW σ sk pk rk dhr cks ns nr pn
          (sk, pk, dhr, rk, cks, some (encS σ), ns, nr, pn, u, sd, sn, sm)
          (dhr.getD (Hax.repeat_ 0 32)) (untl - nr).toNat MAX_SKIP (st, ck, true) ∧ s' = st by
      intro hs
      refine key _ ?_ hs
      rintro i ⟨st, ck, ok⟩ hi0 hi16 hinv
      cases ok
      · simp [SkipInv, Hax.band]
      obtain ⟨u', sd', sn', sm', rfl, rfl, h1, h2, h3, h4, hstore⟩ := hinv rfl
      simp only [Hax.band, Hax.lt, Bool.true_and, decide_eq_true_eq, kdf_ck_enc h]
      unfold SkipInv
      by_cases hlt : nr + ((min i.toNat (untl - nr).toNat : ℕ) : Int) < untl
      · simp only [hlt, ↓reduceIte]
        have hk1 : min (i + 1).toNat (untl - nr).toNat = min i.toNat (untl - nr).toNat + 1 := by
          omega
        split
        · rename_i st1 hins
          obtain ⟨u'', sd'', sn'', sm'', rfl, g1, g2, g3, g4, hstore'⟩ :=
            store_insert_some sk pk rk dhr cks _ ns _ pn u' sd' sn' sm' h1 h2 h3 h4 _ _ _ _ hins
          intro _
          refine ⟨u'', sd'', sn'', sm'', ?_, ?_, g1, g2, g3, g4, ?_⟩
          · simp only [RatchetState, «.dhs_sk», «.dhs_pk», «.rk», «.cks», «.ns»,
              «RatchetState.pn», «.sk_used», «.sk_dh», «.sk_n», «.sk_mk», hk1, Hax.add,
              Function.iterate_succ_apply', Nat.cast_add, Nat.cast_one, add_assoc]
          · simp only [hk1, Function.iterate_succ_apply']
          · simp only [RatchetState, «.sk_used», «.sk_dh», «.sk_n», «.sk_mk», hk1] at hstore' ⊢
            refine (storeOf_eq_of_store rfl rfl rfl rfl).trans (hstore'.trans ?_)
            rw [hstore, Finset.range_add_one, Finset.image_insert, Finset.union_insert]
            congr 1
            cases dhr <;> rfl
        · intro hc
          simp at hc
      · simp only [hlt, ↓reduceIte]
        intro _
        have hm' : min (i + 1).toNat (untl - nr).toNat = min i.toNat (untl - nr).toNat := by
          omega
        rw [hm']
        exact ⟨u', sd', sn', sm', rfl, rfl, h1, h2, h3, h4, hstore⟩
    intro f hstep hs
    have hinv := Hax.foldRange_induct (lo := 0) (hi := MAX_SKIP)
      (init := ((sk, pk, dhr, rk, cks, some (encS σ), ns, nr, pn, u, sd, sn, sm), encS σ, true))
      (f := f) (P := SkipInv F encS encW σ sk pk rk dhr cks ns nr pn
        (sk, pk, dhr, rk, cks, some (encS σ), ns, nr, pn, u, sd, sn, sm)
        (dhr.getD (Hax.repeat_ 0 32)) (untl - nr).toNat) (by decide) ?_ hstep
    · generalize Hax.foldRange 0 MAX_SKIP
        ((sk, pk, dhr, rk, cks, some (encS σ), ns, nr, pn, u, sd, sn, sm), encS σ, true) f = acc
        at hinv hs
      obtain ⟨st, ck, ok⟩ := acc
      cases ok
      · simp at hs
      simp only [ite_true, Option.some.injEq] at hs
      exact ⟨st, ck, hinv, hs.symm⟩
    · intro _
      refine ⟨u, sd, sn, sm, ?_, ?_, hu, hd, hn, hm, ?_⟩ <;> simp
  obtain ⟨u', sd', sn', sm', hst, -, h1, h2, h3, h4, hstore⟩ := hinv rfl
  have hmin : min (MAX_SKIP.toNat) (untl - nr).toNat = (untl - nr).toNat := by
    simp only [MAX_SKIP]
    omega
  simp only at hst hstore
  rw [hmin] at hst hstore
  exact ⟨u', sd', sn', sm', hst, h1, h2, h3, h4, hstore⟩

end Skip

/-! ## `try_skipped_message_keys` -/

/-- **No stored key.** `try_skipped_message_keys` returns nothing exactly when no slot is
occupied by the header's ratchet key and message number. -/
theorem try_skipped_none_iff (s : RatchetState_T) (hd : MessageHeader_T) :
    try_skipped_message_keys s hd = none ↔
      ∀ j : ℕ, j < 32 → ¬ StoreHit s («.dh» hd) («.n» hd) j := by
  have hspec := store_find_spec s («.dh» hd) («.n» hd)
  unfold try_skipped_message_keys
  cases hf : store_find s («.dh» hd) («.n» hd) with
  | mk b i =>
    rw [hf] at hspec
    cases b
    · simp only [Bool.false_eq_true, ite_false, true_iff]
      intro j hj
      exact hspec.2 rfl j (by omega) (by omega)
    · simp only [ite_true, reduceCtorEq, false_iff, not_forall, not_not]
      obtain ⟨h0, h32, hhit, -⟩ := hspec.1 rfl
      exact ⟨i.toNat, by omega, by rwa [Int.toNat_of_nonneg h0]⟩

/-- **A stored key.** When `try_skipped_message_keys` returns `(t, mk)`, the first slot `i`
occupied by the header's ratchet key and message number gives `(t, mk) = store_take s i`. -/
theorem try_skipped_some (s : RatchetState_T) (hd : MessageHeader_T) (t : RatchetState_T)
    (mk : Array Int) (h : try_skipped_message_keys s hd = some (t, mk)) :
    ∃ i : ℕ, i < 32 ∧ StoreHit s («.dh» hd) («.n» hd) i ∧
      (∀ j : ℕ, j < i → ¬ StoreHit s («.dh» hd) («.n» hd) j) ∧ store_take s i = (t, mk) := by
  have hspec := store_find_spec s («.dh» hd) («.n» hd)
  unfold try_skipped_message_keys at h
  cases hf : store_find s («.dh» hd) («.n» hd) with
  | mk b i =>
    rw [hf] at hspec h
    cases b
    · simp at h
    · simp only [ite_true, Option.some.injEq] at h
      obtain ⟨h0, h32, hhit, hfirst⟩ := hspec.1 rfl
      refine ⟨i.toNat, by omega, ?_, ?_, ?_⟩
      · rwa [Int.toNat_of_nonneg h0]
      · intro j hj
        exact hfirst j (by omega) (by omega)
      · rwa [Int.toNat_of_nonneg h0]

/-- **A stored key at the store view.** When `try_skipped_message_keys` at a state of 32 slots
with distinct triples returns `(t, mk)`, the store holds a triple `e` with the header's ratchet
key (under `eq32`), message number and the key `mk`; `t` keeps the nine components before the
store and its store is the store without `e`. -/
theorem try_skipped_enc (sk pk rk : Array Int) (dhr cks ckr : Option (Array Int))
    (ns nr pn : Int) (u : Array Bool) (sd : Array (Array Int)) (sn : Array Int)
    (sm : Array (Array Int)) (hu : u.size = 32) (hd : sd.size = 32) (hn : sn.size = 32)
    (hm : sm.size = 32) (hinj : SlotsInj (sk, pk, dhr, rk, cks, ckr, ns, nr, pn, u, sd, sn, sm))
    (hdr : MessageHeader_T) (t : RatchetState_T) (mk : Array Int)
    (h : try_skipped_message_keys (sk, pk, dhr, rk, cks, ckr, ns, nr, pn, u, sd, sn, sm) hdr =
      some (t, mk)) :
    ∃ e ∈ storeOf (sk, pk, dhr, rk, cks, ckr, ns, nr, pn, u, sd, sn, sm),
      eq32 e.1 («.dh» hdr) = true ∧ e.2.1 = «.n» hdr ∧ e.2.2 = mk ∧
      (∃ (u' : Array Bool) (sd' : Array (Array Int)) (sn' : Array Int)
          (sm' : Array (Array Int)),
          t = (sk, pk, dhr, rk, cks, ckr, ns, nr, pn, u', sd', sn', sm')) ∧
      storeOf t = (storeOf (sk, pk, dhr, rk, cks, ckr, ns, nr, pn, u, sd, sn, sm)).erase e := by
  obtain ⟨i, hi, hhit, -, htake⟩ := try_skipped_some _ hdr t mk h
  have hpair := htake
  rw [store_take_eq, Prod.mk.injEq] at hpair
  obtain ⟨ht, hmk⟩ := hpair
  simp only [StoreHit, «.sk_used», «.sk_dh», «.sk_n»] at hhit
  refine ⟨slotAt (sk, pk, dhr, rk, cks, ckr, ns, nr, pn, u, sd, sn, sm) i, ?_, ?_, ?_, ?_,
    ⟨_, _, _, _, ht.symm⟩, ?_⟩
  · exact (mem_storeOf _ _).2 ⟨i, hi, hhit.1, rfl⟩
  · exact hhit.2.1
  · exact hhit.2.2
  · exact hmk
  · have := storeOf_store_take sk pk rk dhr cks ckr ns nr pn u sd sn sm hu hd hn hm i hi hhit.1
      hinj
    simpa only [htake] using this

/-! ## Receiving and decrypting -/

section Receive

variable {Dp : Type} [Inhabited Dp] [DoubleRatchetDeps Dp]

/-- **Receipt on a known ratchet key.** On a header whose key is in the store, or whose ratchet
key is the remote ratchet key `DHr` (under `eq32`), `ratchet_receive_key` does not depend on
the new key pair. -/
theorem ratchet_receive_key_old (s : RatchetState_T) (hd : MessageHeader_T)
    (sk₁ pk₁ sk₂ pk₂ : Array Int)
    (hold : (try_skipped_message_keys s hd).isSome ∨
      ∃ r, «.dhr» s = some r ∧ eq32 r («.dh» hd) = true) :
    ratchet_receive_key (D := Dp) s hd sk₁ pk₁ = ratchet_receive_key (D := Dp) s hd sk₂ pk₂ := by
  unfold ratchet_receive_key
  rcases hold with hsome | ⟨r, hr, he⟩
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
    simp only [hx]
  · cases try_skipped_message_keys s hd <;>
      simp only [hr, he, Hax.Not, Hax.HaxNot.not, Bool.not_true, Bool.false_eq_true,
        ite_false]

/-- **Receipt on a new ratchet key.** On a header whose key is not in the store and whose
ratchet key differs from the remote ratchet key `DHr` (under `eq32`), or at a state without
`DHr`, `ratchet_receive_key` skips the current receiving chain to `pn`, runs the receiving and
the sending half of the Diffie–Hellman ratchet, skips the new receiving chain to `n` and steps it
once. -/
theorem ratchet_receive_key_new (s : RatchetState_T) (hd : MessageHeader_T) (sk pk : Array Int)
    (hnone : try_skipped_message_keys s hd = none)
    (hnew : ∀ r, «.dhr» s = some r → eq32 r («.dh» hd) = false) :
    ratchet_receive_key (D := Dp) s hd sk pk =
      ((skip_message_keys (D := Dp) s («MessageHeader.pn» hd)).bind fun t =>
        skip_message_keys (D := Dp)
          (dh_ratchet_send_half (D := Dp) (dh_ratchet_recv_half (D := Dp) t («.dh» hd)) sk pk)
          («.n» hd)).bind fun t₂ =>
        («.ckr» t₂).map fun ck =>
          (RatchetState («.dhs_sk» t₂) («.dhs_pk» t₂) («.dhr» t₂) («.rk» t₂) («.cks» t₂)
            (some (kdf_ck (D := Dp) ck).1) («.ns» t₂) (Hax.add («.nr» t₂) 1)
            («RatchetState.pn» t₂) («.sk_used» t₂) («.sk_dh» t₂) («.sk_n» t₂) («.sk_mk» t₂),
            (kdf_ck (D := Dp) ck).2) := by
  unfold ratchet_receive_key dh_ratchet
  rw [hnone]
  rcases hr : «.dhr» s with _ | r
  · simp only [ite_true]
    grind
  · have hf := hnew r hr
    simp only [hf, Hax.Not, Hax.HaxNot.not, Bool.not_false, ite_true]
    grind

/-- **Decryption.** `ratchet_decrypt` is `ratchet_receive_key` followed by `aead_decrypt` under
the derived message key at the associated data `concat_ad ad h`; it returns nothing when either
step refuses. -/
theorem ratchet_decrypt_eq (s : RatchetState_T) (hd : MessageHeader_T) (ct : Array Int)
    (n : Int) (ad sk pk : Array Int) :
    ratchet_decrypt (D := Dp) s hd ct n ad sk pk =
      (ratchet_receive_key (D := Dp) s hd sk pk).bind fun r =>
        (DoubleRatchetDeps.aead_decrypt (Self := Dp) r.2 ct n (concat_ad ad hd)).map
          fun p => (r.1, p.1, p.2) := by
  unfold ratchet_decrypt
  cases ratchet_receive_key (D := Dp) s hd sk pk with
  | none => rfl
  | some r =>
    simp only [Option.bind_some]
    cases DoubleRatchetDeps.aead_decrypt (Self := Dp) r.2 ct n (concat_ad ad hd) <;> rfl

end Receive

end

end CatCrypt.Crypto.Signal.DoubleRatchet.ExtractedStore
