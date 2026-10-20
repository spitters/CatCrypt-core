/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Assumptions.AEAD
public import CatCryptCore.Crypto.Messaging.FSPRG

/-!
# Forward-secure authenticated encryption

A forward-secure AEAD scheme (FS-AEAD) encrypts the `j`-th message of an epoch under the
`j`-th output of a forward-secure PRG, so that the state of the PRG after the epoch reveals
nothing about the keys of the messages sent in it (Alwen, Coretti and Dodis, §4.3). The
confidentiality game gives the adversary the ciphertexts of the messages `msgs` and the
generator state after them, against uniform ciphertexts and a uniform state.

The proof has two parts: the keys are replaced by uniform keys at the cost of the FS-PRG
advantage of `fsaeadPost`, and the ciphertexts under uniform keys are replaced by uniform
ciphertexts one at a time, each step at the cost of the AEAD advantage of `fsaeadRed`.

## Main definitions

* `encAll` — the ciphertexts of a list of messages `(pt, ad)` under a list of keys
* `fsaead_real`, `fsaead_ideal`, `FSAEAD_Advantage` — the FS-AEAD confidentiality game
* `fsaeadPostOf`, `fsaeadPost` — the FS-PRG distinguisher that encrypts the messages under
  its keys
* `fsaeadHyb` — the hybrid with `j` uniform ciphertexts followed by encryptions under `r`
  uniform keys
* `fsaeadView`, `fsaeadRedOf`, `fsaeadRed` — the AEAD distinguisher of hybrid step `j`

## Main results

* `fsaead_real_bind_eq` — the real game is the FS-PRG real game followed by encryption
* `fsaeadHyb_bind_eq_real`, `fsaeadHyb_succ_bind_eq_ideal` — hybrid step `j` is the AEAD
  game of `fsaeadRed`
* `fsaead_advantage_le` — for every adversary `A`, the FS-AEAD advantage is at most the
  PRG advantages of the FS-PRG reductions plus the AEAD advantages of the encryption
  reductions
* `fsaeadPostOf.tree.timeBound_timed`, `fsaeadRedOf.tree.timeBound_timed` — the times of the
  costed reductions

## References

* J. Alwen, S. Coretti, Y. Dodis, *The Double Ratchet: Security Notions, Proofs, and
  Modularization for the Signal Protocol*, EUROCRYPT 2019, §4.3
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open scoped ENNReal

variable {St W C : Type} [Fintype St] [Nonempty St] [SampleableType W] [SampleableType C]

/-- The ciphertexts of the messages `msgs`, each a pair of a plaintext and associated data,
under the keys `keys`, position by position. -/
def encAll (D : AEADDef W C) (keys : List W) (msgs : List (W × W)) : List C :=
  List.zipWith (fun k m => D.encrypt k m.1 m.2) keys msgs

/-! ## The confidentiality game -/

/-- FS-AEAD real game: the messages encrypted under the outputs of the generator `G` from a
uniform state, and the state after the epoch. -/
noncomputable def fsaead_real (G : PRGDef St (W × St)) (D : AEADDef W C)
    (msgs : List (W × W)) : SPComp (List C × St) := do
  let s ← SPComp.sample St
  SPComp.pure (encAll D (fsprgRun G msgs.length s).1 msgs, (fsprgRun G msgs.length s).2)

/-- FS-AEAD ideal game: uniform ciphertexts and a uniform state. -/
noncomputable def fsaead_ideal (msgs : List (W × W)) : SPComp (List C × St) := do
  let v ← SPComp.sample (Fin msgs.length → C)
  let s ← SPComp.sample St
  SPComp.pure (List.ofFn v, s)

/-- FS-AEAD confidentiality advantage of the distinguisher `A`. -/
noncomputable def FSAEAD_Advantage (G : PRGDef St (W × St)) (D : AEADDef W C)
    (msgs : List (W × W)) (A : List C × St → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (fsaead_real G D msgs) (fsaead_ideal msgs) A

/-! ## Reductions and hybrids -/

/-- The FS-PRG distinguisher with the encryption function `encode`: call `A` with the
encryptions `encode ks.1` of the received keys and the received state `ks.2`. -/
noncomputable def fsaeadPostOf (encode : List W → List C) (A : List C × St → SPComp Bool)
    (ks : List W × St) : SPComp Bool :=
  A (encode ks.1, ks.2)

/-- The FS-PRG distinguisher: encrypt the messages under the received keys and call `A` with
the ciphertexts and the received state. -/
noncomputable def fsaeadPost (D : AEADDef W C) (msgs : List (W × W))
    (A : List C × St → SPComp Bool) : List W × St → SPComp Bool :=
  fsaeadPostOf (fun ks => encAll D ks msgs) A

/-- Hybrid `(j, r)`: `j` uniform ciphertexts, followed by the encryptions of the messages from
position `j` on under `r` uniform keys, and a uniform state. -/
noncomputable def fsaeadHyb (D : AEADDef W C) (msgs : List (W × W)) (j r : ℕ) :
    SPComp (List C × St) := do
  let vc ← SPComp.sample (Fin j → C)
  let vk ← SPComp.sample (Fin r → W)
  let s ← SPComp.sample St
  SPComp.pure (List.ofFn vc ++ encAll D (List.ofFn vk) (msgs.drop j), s)

/-- The ciphertexts of hybrid step `j` built from the `j` uniform ciphertexts `vc`, the `r`
uniform keys `vk` and the AEAD challenge `c`: `vc`, then `c`, then the encryptions of the
messages after position `j` under `vk`. -/
def fsaeadView (D : AEADDef W C) (msgs : List (W × W)) (j r : ℕ) (vc : Fin j → C)
    (vk : Fin r → W) (c : C) : List C :=
  List.ofFn vc ++ c :: encAll D (List.ofFn vk) (msgs.drop (j + 1))

/-- The AEAD distinguisher with the view function `view`: on the challenge ciphertext `c` it
samples `j` uniform ciphertexts, `r` uniform keys and a state, and calls `A`. -/
noncomputable def fsaeadRedOf {j r : ℕ} (view : (Fin j → C) → (Fin r → W) → C → List C)
    (A : List C × St → SPComp Bool) (c : C) : SPComp Bool := do
  let vc ← SPComp.sample (Fin j → C)
  let vk ← SPComp.sample (Fin r → W)
  let s ← SPComp.sample St
  A (view vc vk c, s)

/-- The AEAD distinguisher of hybrid step `j`: `fsaeadRedOf` with the view `fsaeadView`. -/
noncomputable def fsaeadRed (D : AEADDef W C) (msgs : List (W × W)) (j r : ℕ)
    (A : List C × St → SPComp Bool) : C → SPComp Bool :=
  fsaeadRedOf (fsaeadView D msgs j r) A

omit [SampleableType C] in
/-- The real game is the FS-PRG real game followed by `fsaeadPost`. -/
theorem fsaead_real_bind_eq (G : PRGDef St (W × St)) (D : AEADDef W C) (msgs : List (W × W))
    (A : List C × St → SPComp Bool) :
    (fsaead_real G D msgs).bind A = (fsprg_real G msgs.length).bind (fsaeadPost D msgs A) := by
  simp only [fsaead_real, fsprg_real, fsaeadPost, fsaeadPostOf, SPComp.monad_bind_eq,
    SPComp.bind_assoc, SPComp.pure_bind]

/-- The FS-PRG ideal game followed by `fsaeadPost` is hybrid `(0, n)`. -/
theorem fsaeadHyb_zero_bind_eq (D : AEADDef W C) (msgs : List (W × W))
    (A : List C × St → SPComp Bool) :
    (fsaeadHyb D msgs 0 msgs.length).bind A =
      (fsprg_ideal (St := St) msgs.length).bind (fsaeadPost D msgs A) := by
  simp only [fsaeadHyb, fsprg_ideal, fsaeadPost, fsaeadPostOf, SPComp.monad_bind_eq,
    SPComp.bind_assoc, SPComp.pure_bind, sample_bind_unique, List.ofFn_zero, List.nil_append,
    List.drop_zero]

/-- Hybrid `(n, 0)` is the ideal game. -/
theorem fsaeadHyb_self (D : AEADDef W C) (msgs : List (W × W)) :
    fsaeadHyb (St := St) D msgs msgs.length 0 = fsaead_ideal msgs := by
  simp only [fsaeadHyb, fsaead_ideal, SPComp.monad_bind_eq, sample_bind_unique,
    List.ofFn_zero, List.drop_length, encAll, List.zipWith_nil_left, List.append_nil]

/-- Hybrid `(j, r + 1)` is the real AEAD game of `fsaeadRed` for the message at `j`. -/
theorem fsaeadHyb_bind_eq_real (D : AEADDef W C) (msgs : List (W × W)) {j : ℕ}
    (hj : j < msgs.length) (r : ℕ) (A : List C × St → SPComp Bool) :
    (fsaeadHyb D msgs j (r + 1)).bind A =
      AEAD_Game_Real D msgs[j].1 msgs[j].2 (fsaeadRed D msgs j r A) := by
  simp only [fsaeadHyb, AEAD_Game_Real, fsaeadRed, fsaeadRedOf, fsaeadView,
    SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
  rw [SPComp.isPure_bind_comm_left _ _ _ (SPComp.sample_isPure W)]
  congr 1; funext vc
  rw [← SPComp.sample_bind_equiv (Fin.consEquiv fun _ => W)]
  have he : ∀ (a : W) (v : Fin r → W), (Fin.consEquiv fun _ => W) (a, v) =
      Fin.cons (α := fun _ => W) a v := fun _ _ => rfl
  simp only [SPComp.sample_prod_eq, SPComp.bind_assoc, SPComp.pure_bind, he, ofFn_cons,
    List.drop_eq_getElem_cons hj, encAll, List.zipWith_cons_cons]

/-- Hybrid `(j + 1, r)` is the ideal AEAD game of `fsaeadRed`. -/
theorem fsaeadHyb_succ_bind_eq_ideal (D : AEADDef W C) (msgs : List (W × W)) (j r : ℕ)
    (A : List C × St → SPComp Bool) :
    (fsaeadHyb D msgs (j + 1) r).bind A = AEAD_Game_Ideal (fsaeadRed D msgs j r A) := by
  simp only [fsaeadHyb, SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
  rw [← SPComp.sample_bind_equiv (Fin.snocEquiv fun _ => C)]
  have he : ∀ (a : C) (v : Fin j → C), (Fin.snocEquiv fun _ => C) (a, v) =
      Fin.snoc (α := fun _ => C) v a := fun _ _ => rfl
  simp only [AEAD_Game_Ideal, fsaeadRed, fsaeadRedOf, fsaeadView, SPComp.sample_prod_eq,
    SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind, he, ofFn_snoc,
    List.append_assoc, List.singleton_append]

/-- **FS-AEAD confidentiality from PRG and AEAD security.** For every distinguisher `A`, the
FS-AEAD advantage over the messages `msgs` of length `n` is at most the PRG advantages of the
FS-PRG reductions `fsprgRed G n i (fsaeadPost D msgs A)` plus the AEAD advantages of the
encryption reductions `fsaeadRed D msgs j (n - (j + 1)) A` for the message at `j`. -/
theorem fsaead_advantage_le (G : PRGDef St (W × St)) (D : AEADDef W C) (msgs : List (W × W))
    (A : List C × St → SPComp Bool) :
    FSAEAD_Advantage G D msgs A ≤
      ∑ i ∈ Finset.range msgs.length,
          PRG_Advantage G (fsprgRed G msgs.length i (fsaeadPost D msgs A)) +
        ∑ j ∈ Finset.range msgs.length,
          AEAD_Advantage D (msgs.getD j default).1 (msgs.getD j default).2
            (fsaeadRed D msgs j (msgs.length - (j + 1)) A) := by
  set n := msgs.length with hn
  unfold FSAEAD_Advantage AdvantageA
  rw [fsaead_real_bind_eq]
  refine (advantage_triangle _ ((fsprg_ideal (St := St) n).bind (fsaeadPost D msgs A)) _).trans
    (add_le_add (fsprg_advantage_le G n _) ?_)
  have h0 : fsaeadHyb (St := St) D msgs 0 (n - 0) = fsaeadHyb D msgs 0 n := rfl
  have hn' : fsaeadHyb (St := St) D msgs n (n - n) = fsaead_ideal msgs := by
    rw [Nat.sub_self]; exact fsaeadHyb_self D msgs
  rw [← fsaeadHyb_zero_bind_eq, ← hn', ← h0]
  refine (HybridArgument.advantage_hybrid_dep (fun i => fsaeadHyb (St := St) D msgs i (n - i))
    A n).trans (Finset.sum_le_sum fun i hi => le_of_eq ?_)
  have hi' : i < msgs.length := Finset.mem_range.mp hi
  have hr : n - i = n - (i + 1) + 1 := by omega
  simp only [AdvantageA]
  have hg : msgs.getD i default = msgs[i] := by
    simp [List.getD_eq_getElem?_getD, hi']
  rw [hr, fsaeadHyb_bind_eq_real D msgs hi', fsaeadHyb_succ_bind_eq_ideal, hg]
  rfl

/-! ## The costed reductions -/

derive_reduction fsaeadRedOf (adv := A)

derive_reduction fsaeadPostOf (adv := A)

omit [Fintype St] [Nonempty St] [SampleableType W] [SampleableType C] in
/-- **Time of the FS-PRG distinguisher of FS-AEAD.** With the costed adversary `A` of time at
most `T` and call cost at most `a`, and the encryption of the keys of cost at most `te`, the
costed distinguisher has time at most `T + a + te + 2`. For `fsaeadPost D msgs A` the
encryption is `encAll D · msgs`. -/
theorem fsaeadPostOf.tree.timeBound_timed (encode : List W → List C)
    (encodeCost : List W → ℕ) (A : List C × St → SPTree.Timed Bool) (ACost : List C × St → ℕ)
    {T a te : ℕ} (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a)
    (he : ∀ ks, encodeCost ks ≤ te) (ks : List W × St) :
    SPTree.Timed.stepTime (fsaeadPostOf.tree.timed encode encodeCost A ACost ks) ≤
      T + a + te + 2 := by
  simp only [SPTree.Timed.stepTime, fsaeadPostOf.tree.timed]
  have := hA (encode ks.1, ks.2); have := hAc (encode ks.1, ks.2); have := he ks.1
  omega

/-- **Time of the AEAD reduction.** With the costed adversary `A` of time at most `T` and call
cost at most `a`, and the view function of cost at most `tv`, the costed reduction has time at
most `T + a + tv + 5`: three samples (the uniform ciphertexts, the uniform keys and the
state), one view and one adversary call. For `fsaeadRed D msgs j r A` the view is
`fsaeadView D msgs j r`, whose cost is that of `r` encryptions. -/
theorem fsaeadRedOf.tree.timeBound_timed {j r : ℕ}
    (view : (Fin j → C) → (Fin r → W) → C → List C)
    (viewCost : (Fin j → C) → (Fin r → W) → C → ℕ)
    (A : List C × St → SPTree.Timed Bool) (ACost : List C × St → ℕ)
    {T a tv : ℕ} (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a)
    (hv : ∀ vc vk c, viewCost vc vk c ≤ tv) (c : C) :
    SPTree.Timed.stepTime (fsaeadRedOf.tree.timed view viewCost A ACost c) ≤
      T + a + tv + 5 := by
  simp only [SPTree.Timed.stepTime, fsaeadRedOf.tree.timed, zero_add]
  refine (timedSample_time_le _ _ _ _ _ (T + a + tv + 4) fun vc => ?_).trans
    (by omega)
  rw [zero_add]
  refine (timedSample_time_le _ _ _ _ _ (T + a + tv + 3) fun vk => ?_).trans
    (by omega)
  rw [zero_add]
  refine (timedSample_time_le _ _ _ _ _ (T + a + tv + 2) fun s => ?_).trans
    (by omega)
  have := hA (view vc vk c, s); have := hAc (view vc vk c, s); have := hv vc vk c
  omega

end CatCrypt.Crypto.Messaging
