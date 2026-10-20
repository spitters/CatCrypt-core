/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.SigmaProtocol.SurfaceDeps

/-!
# The fixed-shape Schnorr and DLEQ functions of `sigma-proofs-hax`

The module `src/fixed.rs` of the crate `sigma-proofs-hax` computes the Schnorr proof
(one scalar `x`, one equation `X = g^x`) and the DLEQ proof (one scalar `x`, equations
`X = g^x` and `Y = H^x`) of draft-irtf-cfrg-sigma-protocols-03 over four 64-bit limbs per
32-byte encoding, eight limbs per pair of elements, and status words (`0` accepts). Its
extraction is in `Extraction/SigmaProofs_haxpipe.lean`. Under a `GroupEncoding E` whose
encodings are 32-byte arrays (`BytesEncoding E`), with the operations of
`groupSigmaProofsDeps E`, this file identifies the fixed-shape functions with the linear
Σ-protocols of `dlogRelation` and `dleqRelation` (`FiatShamirROM/LinearRelation.lean`).

## Main definitions

* `IsBytes32`, `BytesEncoding` — 32-byte arrays, and encodings whose values are such arrays
* `limbsS`, `limbsG`, `ofLimbsS`, `ofLimbsG`, `pairG`, `ofPairG` — encodings as limbs
* `fixedSchnorrSigma`, `fixedDleqSigma` — the Σ-protocols whose commitment, response,
  verifier and simulator are the extracted fixed-shape functions
* `schnorrEquations`, `dleqEquations` — the equations of the two instances in the encoding of
  the generic extracted core

## Main results

* `limbs_to_bytes_bytes_to_limbs` — converting a 32-byte array to limbs and back returns it;
  `fixed_eq_bytes_to_limbs` — `fixed_eq` on the limbs of two 32-byte arrays is `0` when they
  are equal and `1` otherwise; `fixed_first_pair`, `fixed_second_pair` — the halves of a pair
* `ristrettoEncoding_bytes` — the ristretto255 encodings are 32-byte arrays
* `fixedSchnorrSigma_eq`, `fixedDleqSigma_eq` — the fixed-shape Σ-protocols are
  `linearSigma` of the Schnorr and DLEQ relations; with `fixedSchnorrSigma_complete`,
  `fixedSchnorrSigma_specialSound`, `fixedSchnorrSigma_perfectHVZK`,
  `fixedSchnorrSigma_statHVZKAt`, `fixedSchnorrSigma_ksExtractProb_ge`,
  `fixedSchnorrSigma_zkReal_le_zkSim`, `fixedSchnorrSigma_dsKsExtractProb_ge`,
  `fixedSchnorrSigma_dsZkReal_le_zkSim` and their DLEQ counterparts, the strong Fiat–Shamir
  and duplex-sponge proofs whose prover and verifier are the fixed-shape functions are
  complete, knowledge sound and zero knowledge
* `schnorr_compact_eq_zero_iff`, `dleq_compact_eq_zero_iff` — the compact commitment
  followed by `fixed_compact_accept` returns `0` exactly when `linearCompactVerify` accepts
* `dleq_verify_batchable_eq_zero_iff` — the batched DLEQ verifier returns `0` exactly when
  the batched equation holds; `fixed_encodable_eq_zero_iff`, `dleq_encodable_eq_zero_iff` —
  the encodability tests return `0` exactly when no element is the identity
* `schnorrInstance_map_image`, `dleqInstance_map_image` — the relation that the generic core
  decodes from the instance `Instance_new` builds has the map and image of the Schnorr and
  DLEQ relation; `extSigma_verify_eq_fixedSchnorr`, `extSigma_verify_eq_fixedDleq` — on that
  instance the verifiers of `extSigma` and of the fixed-shape protocol agree
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SigmaProtocol.FixedShape

open CatCrypt.Examples CatCrypt.Crypto.FiatShamirROM CatCrypt.Crypto.SigmaProtocol.SurfaceDeps

/-! ## Limb codec -/

/-- A byte array of length 32: 32 entries, each in `[0, 256)`. -/
def IsBytes32 (b : Array Int) : Prop :=
  b.size = 32 ∧ ∀ p : ℕ, p < 32 → 0 ≤ Hax.index b (p : Int) ∧ Hax.index b (p : Int) < 256

/-- `Hax.index` of an in-bounds `Hax.array_update` at non-negative indices. -/
theorem index_update {α : Type} [Inhabited α] (a : Array α) (e p : Int) (x : α) (he0 : 0 ≤ e)
    (he : e.toNat < a.size) (hp0 : 0 ≤ p) (hp : p.toNat < a.size) :
    Hax.index (Hax.array_update a e x) p = if p = e then x else Hax.index a p := by
  split
  · subst p
    exact Hax.index_array_update_same x he
  · exact Hax.index_array_update_of_ne x hp (by omega)

/-- The little-endian value of bytes `8k` to `8k + j − 1` of a byte array; at `j = 8` the
value of limb `k`. -/
def limbPart (b : Array Int) (k j : ℕ) : Int :=
  ∑ i ∈ Finset.range j, Hax.index b ((8 * k + i : ℕ) : Int) * 256 ^ i

/-- One step of the limb accumulation: or-ing in a byte shifted past the bytes already
present adds it. -/
theorem bitor_shl_eq_add {a x : Int} {j : ℕ} (hj : j < 8) (ha0 : 0 ≤ a) (ha : a < 256 ^ j)
    (hx0 : 0 ≤ x) (hx : x < 256) :
    Hax.bitor_w 64 a (Hax.shl_w 64 (Hax.castVal_w 64 x) (Hax.castVal_w 64 (Hax.mul 8 (j : Int)))) =
      a + x * 256 ^ j := by
  lift a to ℕ using ha0
  lift x to ℕ using hx0
  have hpow : (256 : ℕ) ^ j = 2 ^ (8 * j) := by rw [pow_mul]; norm_num
  have ha' : a < 2 ^ (8 * j) := by rw [← hpow]; exact_mod_cast ha
  have h56 : 2 ^ (8 * j) ≤ 2 ^ 56 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hxs : x * 2 ^ (8 * j) < 2 ^ 64 :=
    calc x * 2 ^ (8 * j) < 256 * 2 ^ 56 :=
          Nat.mul_lt_mul_of_lt_of_le (by omega) h56 (by positivity)
      _ = 2 ^ 64 := by norm_num
  have ha64 : a < 2 ^ 64 := lt_of_lt_of_le ha' (h56.trans (by norm_num))
  have hcx : Hax.castVal_w 64 (x : Int) = x := Hax.castVal_w_of_lt (by positivity) (by omega)
  have hcs : Hax.castVal_w 64 (Hax.mul 8 (j : Int)) = ((8 * j : ℕ) : Int) := by
    rw [show Hax.mul 8 (j : Int) = ((8 * j : ℕ) : Int) by simp [Hax.mul]]
    exact Hax.castVal_w_of_lt (by positivity) (by norm_num; omega)
  have hshl : Hax.shl_w 64 (x : Int) ((8 * j : ℕ) : Int) = ((x <<< (8 * j) : ℕ) : Int) := by
    unfold Hax.shl_w
    rw [Int.toNat_natCast, Int.toNat_natCast, Hax.mod2w_of_lt (by positivity)
      (by rw [Nat.shiftLeft_eq]; exact_mod_cast hxs)]
  rw [hcx, hcs, hshl]
  unfold Hax.bitor_w
  rw [Int.toNat_natCast, Int.toNat_natCast, Nat.mod_eq_of_lt ha64,
    Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; exact hxs), Nat.or_comm,
    ← Nat.shiftLeft_add_eq_or_of_lt ha', Nat.shiftLeft_eq, ← hpow]
  push_cast
  ring

theorem limbPart_succ (b : Array Int) (k j : ℕ) :
    limbPart b k (j + 1) = limbPart b k j + Hax.index b ((8 * k + j : ℕ) : Int) * 256 ^ j := by
  unfold limbPart
  rw [Finset.sum_range_succ]

theorem limbPart_bound {b : Array Int} (hb : IsBytes32 b) (k j : ℕ) (hk : k < 4) (hj : j ≤ 8) :
    0 ≤ limbPart b k j ∧ limbPart b k j < 256 ^ j := by
  induction j with
  | zero => simp [limbPart]
  | succ j ih =>
    obtain ⟨h0, h1⟩ := ih (by omega)
    obtain ⟨hx0, hx1⟩ := hb.2 (8 * k + j) (by omega)
    have hp : (0 : Int) < 256 ^ j := by positivity
    rw [limbPart_succ, pow_succ]
    constructor <;> nlinarith

/-- The entry `k` of a step of `fixed_bytes_to_limbs`. -/
theorem bytes_to_limbs_step {b : Array Int} (hb : IsBytes32 b) {n k : ℕ} (hn : n < 8)
    (hk : k < 4) {old e : Int} (hold : old = limbPart b k n) (he : e = ((8 * k + n : ℕ) : Int)) :
    Hax.bitor_w 64 old
        (Hax.shl_w 64 (Hax.castVal_w 64 (Hax.index b e)) (Hax.castVal_w 64 (Hax.mul 8 (n : Int)))) =
      limbPart b k (n + 1) := by
  have hbd := limbPart_bound hb k n hk hn.le
  have hx := hb.2 (8 * k + n) (by omega)
  subst hold he
  rw [limbPart_succ, bitor_shl_eq_add hn hbd.1 hbd.2 hx.1 hx.2]

/-- Byte `r` of a little-endian value of eight bytes. -/
theorem digit_of_limbPart (x : ℕ → Int) (hx : ∀ i, i < 8 → 0 ≤ x i ∧ x i < 256) (r : ℕ)
    (hr : r < 8) :
    Hax.mod2w 8 ((∑ i ∈ Finset.range 8, x i * 256 ^ i) / 2 ^ (8 * r)) = x r := by
  obtain ⟨h0, h0'⟩ := hx 0 (by omega)
  obtain ⟨h1, h1'⟩ := hx 1 (by omega)
  obtain ⟨h2, h2'⟩ := hx 2 (by omega)
  obtain ⟨h3, h3'⟩ := hx 3 (by omega)
  obtain ⟨h4, h4'⟩ := hx 4 (by omega)
  obtain ⟨h5, h5'⟩ := hx 5 (by omega)
  obtain ⟨h6, h6'⟩ := hx 6 (by omega)
  obtain ⟨h7, h7'⟩ := hx 7 (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [Hax.mod2w_eq_emod (by positivity)]
  interval_cases r <;> norm_num <;> omega

section Codec

/- The functions of the extraction take a `SigmaProofsDeps` instance they do not use; the
lemmas below hold for every instance, which is an implicit argument so that a use site
unifies it with the instance of its goal. -/
variable {inst : SigmaProofs.SigmaProofsDeps}

/-- `fixed_bytes_to_limbs` of a 32-byte array has four entries, entry `k` the little-endian
value of bytes `8k` to `8k + 7`. -/
theorem bytes_to_limbs_spec {b : Array Int} (hb : IsBytes32 b) :
    (SigmaProofs.fixed_bytes_to_limbs b).size = 4 ∧ ∀ k : ℕ, k < 4 →
      Hax.index (SigmaProofs.fixed_bytes_to_limbs b) (k : Int) = limbPart b k 8 := by
  unfold SigmaProofs.fixed_bytes_to_limbs
  dsimp only
  refine Hax.foldRange_induct (P := fun (i : Int) (out : Array Int) =>
      out.size = 4 ∧ ∀ k : ℕ, k < 4 → Hax.index out (k : Int) = limbPart b k i.toNat)
    (by omega) ?_ ?_
  · exact ⟨by simp only [Hax.size_repeat_]; rfl, fun k hk => by
      simp only [limbPart, Hax.index, Hax.repeat_]
      interval_cases k <;> simp⟩
  · intro i a h0 hi ⟨hs, hv⟩
    lift i to ℕ using h0
    have hn : i < 8 := by omega
    refine ⟨by simp only [Hax.size_array_update_eq, hs], fun k hk => ?_⟩
    rw [show ((i : Int) + 1).toNat = i + 1 by omega]
    simp (disch := (first | omega | (simp only [Hax.size_array_update_eq, hs]; omega))) only
      [index_update]
    interval_cases k <;> simp only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Int.reduceEq,
      if_true, if_false] <;>
      exact bytes_to_limbs_step hb hn (by omega) (by exact_mod_cast hv _ (by omega))
        (by first | omega | (simp only [Hax.add]; omega))

theorem size_bytes_to_limbs (b : Array Int) : (SigmaProofs.fixed_bytes_to_limbs b).size = 4 := by
  unfold SigmaProofs.fixed_bytes_to_limbs
  exact Hax.foldRange_induct (P := fun _ (out : Array Int) => out.size = 4) (by omega)
    (by simp only [Hax.size_repeat_]; rfl) (fun i a _ _ h => by simp only [Hax.size_array_update_eq, h])

omit inst in
/-- The byte of a step of `fixed_limbs_to_bytes` written at position `p = 8k + n`. -/
theorem limbs_to_bytes_step (l : Array Int) {n k p : ℕ} (hn : n < 8) (hp : p = 8 * k + n) :
    Hax.castVal_w 8 (Hax.shr_w 64 (Hax.index l (k : Int)) (Hax.castVal_w 64 (Hax.mul 8 (n : Int)))) =
      Hax.mod2w 8 (Hax.mod2w 64 (Hax.index l ((p / 8 : ℕ) : Int)) / 2 ^ (8 * (p % 8))) := by
  have h1 : p / 8 = k := by omega
  have h2 : p % 8 = n := by omega
  have hcs : Hax.castVal_w 64 (Hax.mul 8 (n : Int)) = ((8 * n : ℕ) : Int) := by
    rw [show Hax.mul 8 (n : Int) = ((8 * n : ℕ) : Int) by simp [Hax.mul]]
    exact Hax.castVal_w_of_lt (by positivity) (by norm_num; omega)
  rw [h1, h2, hcs, Hax.castVal_w_eq_mod2w, Hax.shr_w_eq_div, Int.toNat_natCast]

/-- `fixed_limbs_to_bytes` has 32 entries, entry `p` the byte `p mod 8` of the 64-bit
truncation of limb `p / 8`. -/
theorem limbs_to_bytes_spec' (l : Array Int) :
    (SigmaProofs.fixed_limbs_to_bytes l).size = 32 ∧ ∀ p : ℕ, p < 32 → p % 8 < (8 : Int).toNat →
      Hax.index (SigmaProofs.fixed_limbs_to_bytes l) (p : Int) =
        Hax.mod2w 8 (Hax.mod2w 64 (Hax.index l ((p / 8 : ℕ) : Int)) / 2 ^ (8 * (p % 8))) := by
  unfold SigmaProofs.fixed_limbs_to_bytes
  dsimp only
  refine Hax.foldRange_induct (P := fun (i : Int) (out : Array Int) =>
      out.size = 32 ∧ ∀ p : ℕ, p < 32 → p % 8 < i.toNat → Hax.index out (p : Int) =
        Hax.mod2w 8 (Hax.mod2w 64 (Hax.index l ((p / 8 : ℕ) : Int)) / 2 ^ (8 * (p % 8))))
    (by omega) ?_ ?_
  · exact ⟨by simp only [Hax.size_repeat_]; rfl, fun p _ h => absurd h (by simp)⟩
  · intro i a h0 hi ⟨hs, hv⟩
    lift i to ℕ using h0
    have hn : i < 8 := by omega
    refine ⟨by simp only [Hax.size_array_update_eq, hs], fun p hp hpi => ?_⟩
    rw [show ((i : Int) + 1).toNat = i + 1 by omega] at hpi
    simp only [Hax.add]
    simp (disch := (first | omega | (simp only [Hax.size_array_update_eq, hs]; omega))) only
      [index_update]
    split_ifs with h3 h2 h1 h0
    · exact limbs_to_bytes_step l (k := 3) hn (by omega)
    · exact limbs_to_bytes_step l (k := 2) hn (by omega)
    · exact limbs_to_bytes_step l (k := 1) hn (by omega)
    · exact limbs_to_bytes_step l (k := 0) hn (by omega)
    · exact hv p hp (by omega)

theorem size_limbs_to_bytes (l : Array Int) : (SigmaProofs.fixed_limbs_to_bytes l).size = 32 :=
  (limbs_to_bytes_spec' l).1

theorem index_limbs_to_bytes (l : Array Int) (p : ℕ) (hp : p < 32) :
    Hax.index (SigmaProofs.fixed_limbs_to_bytes l) (p : Int) =
      Hax.mod2w 8 (Hax.mod2w 64 (Hax.index l ((p / 8 : ℕ) : Int)) / 2 ^ (8 * (p % 8))) :=
  (limbs_to_bytes_spec' l).2 p hp (by simp; omega)

/-- Converting a 32-byte array to limbs and back returns the array. -/
theorem limbs_to_bytes_bytes_to_limbs {b : Array Int} (hb : IsBytes32 b) :
    SigmaProofs.fixed_limbs_to_bytes (SigmaProofs.fixed_bytes_to_limbs b) = b := by
  apply Hax.ext_index 32 (size_limbs_to_bytes _) hb.1
  intro p hp
  have hbd := limbPart_bound hb (p / 8) 8 (by omega) le_rfl
  rw [index_limbs_to_bytes _ p hp, (bytes_to_limbs_spec hb).2 _ (by omega),
    Hax.mod2w_of_lt hbd.1 (lt_of_lt_of_le hbd.2 (by norm_num))]
  have hx : ∀ i, i < 8 → 0 ≤ Hax.index b ((8 * (p / 8) + i : ℕ) : Int) ∧
      Hax.index b ((8 * (p / 8) + i : ℕ) : Int) < 256 := fun i hi => hb.2 _ (by omega)
  have hpe : p = 8 * (p / 8) + p % 8 := by omega
  conv_rhs => rw [hpe]
  exact digit_of_limbPart _ hx (p % 8) (by omega)

/-! ## Limb comparison -/

omit inst in
theorem bitor_w_bound (x y : Int) : 0 ≤ Hax.bitor_w 64 x y ∧ Hax.bitor_w 64 x y < 2 ^ 64 := by
  unfold Hax.bitor_w
  refine ⟨by positivity, ?_⟩
  have := Nat.or_lt_two_pow (Nat.mod_lt x.toNat (Nat.two_pow_pos 64))
    (Nat.mod_lt y.toNat (Nat.two_pow_pos 64))
  exact_mod_cast this

omit inst in
theorem bitor_w_eq_zero_iff (x y : Int) :
    Hax.bitor_w 64 x y = 0 ↔ Hax.mod2w 64 x = 0 ∧ Hax.mod2w 64 y = 0 := by
  unfold Hax.bitor_w Hax.mod2w
  simp only [Int.natCast_eq_zero, Nat.or_eq_zero_iff]

omit inst in
theorem bitxor_w_eq_zero_iff (x y : Int) :
    Hax.mod2w 64 (Hax.bitxor_w 64 x y) = 0 ↔ Hax.mod2w 64 x = Hax.mod2w 64 y := by
  unfold Hax.bitxor_w Hax.mod2w
  have := Nat.xor_lt_two_pow (Nat.mod_lt x.toNat (Nat.two_pow_pos 64))
    (Nat.mod_lt y.toNat (Nat.two_pow_pos 64))
  simp only [Int.toNat_natCast, Nat.mod_eq_of_lt this, Int.natCast_eq_zero, Int.natCast_inj]
  exact ⟨fun h => Nat.eq_of_testBit_eq fun i => by
    have := congrArg (Nat.testBit · i) h; simpa [Nat.testBit_xor] using this,
    fun h => by rw [h, Nat.xor_self]⟩

omit inst in
/-- The final step of `fixed_eq`: the top bit of `acc ||| −acc` is set exactly when `acc` is
non-zero. -/
theorem shr_or_neg_eq (acc : Int) (h0 : 0 ≤ acc) (h : acc < 2 ^ 64) :
    Hax.shr_w 64 (Hax.bitor_w 64 acc (Hax.wrapping_neg_w 64 acc)) 63 =
      if acc = 0 then 0 else 1 := by
  lift acc to ℕ using h0
  have hn : acc < 2 ^ 64 := by exact_mod_cast h
  have hneg : Hax.wrapping_neg_w 64 (acc : Int) = ((2 ^ 64 - acc) % 2 ^ 64 : ℕ) := by
    unfold Hax.wrapping_neg_w Hax.mod2w
    congr 2
    push_cast
    omega
  rw [hneg]
  unfold Hax.shr_w Hax.bitor_w
  simp only [Int.toNat_natCast]
  by_cases hz : acc = 0
  · subst hz
    simp
  · rw [if_neg (by exact_mod_cast hz), Nat.mod_eq_of_lt hn,
      Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num)), Nat.mod_eq_of_lt (by omega : 2 ^ 64 - acc < 2 ^ 64)]
    have hlt : acc ||| (2 ^ 64 - acc) < 2 ^ 64 := Nat.or_lt_two_pow hn (by omega)
    have hl := Nat.left_le_or (n := acc) (m := 2 ^ 64 - acc)
    have hr := Nat.right_le_or (n := acc) (m := 2 ^ 64 - acc)
    have h63 : (63 : Int).toNat = 63 := rfl
    rw [Nat.shiftRight_eq_div_pow, h63]
    omega

/-- `fixed_eq` is `0` when the first four entries of its arguments agree modulo `2^64` and
`1` otherwise. -/
theorem fixed_eq_eq (a b : Array Int) :
    SigmaProofs.fixed_eq a b =
      if ∀ k : ℕ, k < 4 → Hax.mod2w 64 (Hax.index a (k : Int)) = Hax.mod2w 64 (Hax.index b (k : Int))
      then 0 else 1 := by
  unfold SigmaProofs.fixed_eq
  dsimp only
  have key := Hax.foldRange_induct (P := fun (i : Int) (acc : Int) =>
      0 ≤ acc ∧ acc < 2 ^ 64 ∧ (acc = 0 ↔ ∀ k : ℕ, k < i.toNat →
        Hax.mod2w 64 (Hax.index a (k : Int)) = Hax.mod2w 64 (Hax.index b (k : Int))))
    (lo := 0) (hi := 4) (init := 0)
    (f := fun i acc => Hax.bitor_w 64 acc (Hax.bitxor_w 64 (Hax.index a i) (Hax.index b i)))
    (by omega) (by simp) (by
      intro i acc h0 hi ⟨ha0, ha1, hiff⟩
      lift i to ℕ using h0
      refine ⟨(bitor_w_bound _ _).1, (bitor_w_bound _ _).2, ?_⟩
      rw [bitor_w_eq_zero_iff, Hax.mod2w_of_lt ha0 ha1, hiff, bitxor_w_eq_zero_iff,
        show ((i : Int) + 1).toNat = i + 1 by omega]
      constructor
      · rintro ⟨h1, h2⟩ k hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact h1 k hk
        · exact h2
      · intro h
        exact ⟨fun k hk => h k (by omega), h i (by omega)⟩)
  rw [shr_or_neg_eq _ key.1 key.2.1]
  have hiff := key.2.2
  simp only [show (4 : Int).toNat = 4 from rfl] at hiff
  by_cases hc : ∀ k : ℕ, k < 4 →
      Hax.mod2w 64 (Hax.index a (k : Int)) = Hax.mod2w 64 (Hax.index b (k : Int))
  · rw [if_pos (hiff.mpr hc), if_pos hc]
  · rw [if_neg (fun h => hc (hiff.mp h)), if_neg hc]

theorem mod2w_index_bytes_to_limbs {b : Array Int} (hb : IsBytes32 b) (k : ℕ) (hk : k < 4) :
    Hax.mod2w 64 (Hax.index (SigmaProofs.fixed_bytes_to_limbs b) (k : Int)) =
      Hax.index (SigmaProofs.fixed_bytes_to_limbs b) (k : Int) := by
  rw [(bytes_to_limbs_spec hb).2 k hk]
  have := limbPart_bound hb k 8 hk le_rfl
  exact Hax.mod2w_of_lt this.1 (lt_of_lt_of_le this.2 (by norm_num))

/-- `fixed_eq` on the limbs of two 32-byte arrays is `0` when they are equal and `1`
otherwise. -/
theorem fixed_eq_bytes_to_limbs {a b : Array Int} (ha : IsBytes32 a) (hb : IsBytes32 b) :
    SigmaProofs.fixed_eq (SigmaProofs.fixed_bytes_to_limbs a) (SigmaProofs.fixed_bytes_to_limbs b) =
      if a = b then 0 else 1 := by
  rw [fixed_eq_eq]
  by_cases hab : a = b
  · subst hab
    rw [if_pos (fun k _ => rfl), if_pos rfl]
  · rw [if_neg hab, if_neg]
    intro h
    apply hab
    have e : SigmaProofs.fixed_bytes_to_limbs a = SigmaProofs.fixed_bytes_to_limbs b :=
      Hax.ext_index 4 (size_bytes_to_limbs a) (size_bytes_to_limbs b) fun k hk => by
        rw [← mod2w_index_bytes_to_limbs ha k hk, ← mod2w_index_bytes_to_limbs hb k hk]
        exact h k hk
    rw [← limbs_to_bytes_bytes_to_limbs ha, e, limbs_to_bytes_bytes_to_limbs hb]

/-! ## Pairs of limb arrays -/

/-- `fixed_pair x y` has eight entries: the first four entries of `x`, then those of `y`. -/
theorem fixed_pair_spec (x y : Array Int) :
    (SigmaProofs.fixed_pair x y).size = 8 ∧ ∀ p : ℕ, p < 8 →
      Hax.index (SigmaProofs.fixed_pair x y) (p : Int) =
        if p < 4 then Hax.index x (p : Int) else Hax.index y ((p - 4 : ℕ) : Int) := by
  unfold SigmaProofs.fixed_pair
  dsimp only
  have key := Hax.foldRange_induct (P := fun (i : Int) (out : Array Int) =>
      out.size = 8 ∧ ∀ p : ℕ, p < 8 → (p % 4) < i.toNat → Hax.index out (p : Int) =
        if p < 4 then Hax.index x (p : Int) else Hax.index y ((p - 4 : ℕ) : Int))
    (lo := 0) (hi := 4) (init := Hax.repeat_ (0 : Int) 8)
    (f := fun i out => Hax.array_update (Hax.array_update out i (Hax.index x i)) (Hax.add i 4)
      (Hax.index y i))
    (by omega) ⟨by simp only [Hax.size_repeat_]; rfl, fun p _ h => absurd h (by simp)⟩ (by
      intro i a h0 hi ⟨hs, hv⟩
      lift i to ℕ using h0
      refine ⟨by simp only [Hax.size_array_update_eq, hs], fun p hp hpi => ?_⟩
      rw [show ((i : Int) + 1).toNat = i + 1 by omega] at hpi
      simp only [Hax.add]
      simp (disch := (first | omega | (simp only [Hax.size_array_update_eq, hs]; omega))) only
        [index_update]
      split_ifs <;> first
        | omega
        | (congr 1; omega)
        | (rw [hv p hp (by omega), if_pos ‹_›])
        | (rw [hv p hp (by omega), if_neg ‹_›]))
  exact ⟨key.1, fun p hp => key.2 p hp (by simp; omega)⟩

/-- The first half of a pair of four-limb arrays is the first array. -/
theorem fixed_first_pair {x : Array Int} (y : Array Int) (hx : x.size = 4) :
    SigmaProofs.fixed_first (SigmaProofs.fixed_pair x y) = x := by
  have hp := fixed_pair_spec (inst := inst) x y
  unfold SigmaProofs.fixed_first
  dsimp only
  refine Hax.ext_index 4 (by rw [Hax.size_foldRange_update, Hax.size_repeat_]; rfl) hx
    fun k hk => ?_
  rw [Hax.index_foldRange_update _ 4 (Hax.repeat_ (0 : Int) 4) k (by omega)
    (by rw [Hax.size_repeat_]; exact hk), hp.2 k (by omega),
    if_pos hk]

/-- The second half of a pair of four-limb arrays is the second array. -/
theorem fixed_second_pair (x : Array Int) {y : Array Int} (hy : y.size = 4) :
    SigmaProofs.fixed_second (SigmaProofs.fixed_pair x y) = y := by
  have hp := fixed_pair_spec (inst := inst) x y
  unfold SigmaProofs.fixed_second
  dsimp only
  refine Hax.ext_index 4 (by rw [Hax.size_foldRange_update, Hax.size_repeat_]; rfl) hy
    fun k hk => ?_
  rw [Hax.index_foldRange_update (fun i => Hax.index (SigmaProofs.fixed_pair x y) (Hax.add i 4))
    4 (Hax.repeat_ (0 : Int) 4) k (by omega) (by rw [Hax.size_repeat_]; exact hk)]
  simp only [Hax.add]
  rw [show (k : Int) + 4 = ((k + 4 : ℕ) : Int) by push_cast; rfl, hp.2 (k + 4) (by omega),
    if_neg (by omega), Nat.add_sub_cancel]

end Codec

/-! ## Encodings as limbs -/

section Fixed

variable {gp : GroupParam} (E : GroupEncoding gp)

/-- The encodings of `E` are 32-byte arrays. -/
def BytesEncoding : Prop := (∀ s, IsBytes32 (E.encS s)) ∧ ∀ x, IsBytes32 (E.encG x)

/-- The limbs of the encoding of a scalar. -/
def limbsS (s : gp.Scalar) : Array Int :=
  @SigmaProofs.fixed_bytes_to_limbs (groupSigmaProofsDeps E) (E.encS s)

/-- The limbs of the encoding of a group element. -/
def limbsG (x : gp.G) : Array Int :=
  @SigmaProofs.fixed_bytes_to_limbs (groupSigmaProofsDeps E) (E.encG x)

/-- The scalar decoded from limbs. -/
def ofLimbsS (l : Array Int) : gp.Scalar :=
  E.decS (@SigmaProofs.fixed_limbs_to_bytes (groupSigmaProofsDeps E) l)

/-- The group element decoded from limbs. -/
def ofLimbsG (l : Array Int) : gp.G :=
  E.decG (@SigmaProofs.fixed_limbs_to_bytes (groupSigmaProofsDeps E) l)

/-- The eight limbs of a pair of group elements. -/
def pairG (x y : gp.G) : Array Int :=
  @SigmaProofs.fixed_pair (groupSigmaProofsDeps E) (limbsG E x) (limbsG E y)

/-- The pair of group elements decoded from eight limbs. -/
def ofPairG (p : Array Int) : Fin 2 → gp.G :=
  ![ofLimbsG E (@SigmaProofs.fixed_first (groupSigmaProofsDeps E) p),
    ofLimbsG E (@SigmaProofs.fixed_second (groupSigmaProofsDeps E) p)]

variable {E}

theorem limbs_to_bytes_encS (hE : BytesEncoding E) (s : gp.Scalar) :
    @SigmaProofs.fixed_limbs_to_bytes (groupSigmaProofsDeps E) (limbsS E s) = E.encS s :=
  limbs_to_bytes_bytes_to_limbs (hE.1 s)

theorem limbs_to_bytes_encG (hE : BytesEncoding E) (x : gp.G) :
    @SigmaProofs.fixed_limbs_to_bytes (groupSigmaProofsDeps E) (limbsG E x) = E.encG x :=
  limbs_to_bytes_bytes_to_limbs (hE.2 x)

@[simp] theorem ofLimbsS_limbsS (hE : BytesEncoding E) (s : gp.Scalar) :
    ofLimbsS E (limbsS E s) = s := by
  rw [ofLimbsS, limbs_to_bytes_encS hE, E.decS_encS]

@[simp] theorem ofLimbsG_limbsG (hE : BytesEncoding E) (x : gp.G) :
    ofLimbsG E (limbsG E x) = x := by
  rw [ofLimbsG, limbs_to_bytes_encG hE, E.decG_encG]

/-- `fixed_eq` on the limbs of two group elements is `0` when they are equal and `1`
otherwise. -/
theorem fixed_eq_limbsG (hE : BytesEncoding E) (x y : gp.G) :
    @SigmaProofs.fixed_eq (groupSigmaProofsDeps E) (limbsG E x) (limbsG E y) =
      if x = y then 0 else 1 := by
  rw [limbsG, limbsG, fixed_eq_bytes_to_limbs (hE.2 x) (hE.2 y)]
  by_cases h : x = y
  · rw [if_pos (congrArg E.encG h), if_pos h]
  · rw [if_neg (fun e => h (by rw [← E.decG_encG x, e, E.decG_encG])), if_neg h]

/-- `fixed_eq` on the limbs of two scalars is `0` when they are equal and `1` otherwise. -/
theorem fixed_eq_limbsS (hE : BytesEncoding E) (s t : gp.Scalar) :
    @SigmaProofs.fixed_eq (groupSigmaProofsDeps E) (limbsS E s) (limbsS E t) =
      if s = t then 0 else 1 := by
  rw [limbsS, limbsS, fixed_eq_bytes_to_limbs (hE.1 s) (hE.1 t)]
  by_cases h : s = t
  · rw [if_pos (congrArg E.encS h), if_pos h]
  · rw [if_neg (fun e => h (by rw [← E.decS_encS s, e, E.decS_encS])), if_neg h]

@[simp] theorem fixed_first_pairG (x y : gp.G) :
    @SigmaProofs.fixed_first (groupSigmaProofsDeps E) (pairG E x y) = limbsG E x :=
  fixed_first_pair _ (size_bytes_to_limbs _)

@[simp] theorem fixed_second_pairG (x y : gp.G) :
    @SigmaProofs.fixed_second (groupSigmaProofsDeps E) (pairG E x y) = limbsG E y :=
  fixed_second_pair _ (size_bytes_to_limbs _)

/-- The pair of a pair of limb arrays of encodings decodes to the pair of elements. -/
theorem ofPairG_fixed_pair (hE : BytesEncoding E) (x y : gp.G) :
    ofPairG E (@SigmaProofs.fixed_pair (groupSigmaProofsDeps E) (limbsG E x) (limbsG E y)) =
      ![x, y] := by
  rw [ofPairG, ← pairG, fixed_first_pairG, fixed_second_pairG, ofLimbsG_limbsG hE,
    ofLimbsG_limbsG hE]

/-! ## Schnorr -/

attribute [local instance] GroupParam.scalarCommRing

/-- The simulated commitment of the Schnorr relation: `g^z · X^(−c)`. -/
theorem dlogRelation_simCommit (X : gp.G) (c : gp.Scalar) (z : Fin 1 → gp.Scalar) (i : Fin 1) :
    (dlogRelation gp X).simCommit c z i =
      gp.groupMul (gp.groupExp gp.generator (z 0)) (gp.groupExp X (gp.scalarNeg c)) := by
  simp only [LinearRelation.simCommit, dlogRelation_map, gp.groupInv_groupExp,
    ← gp.groupExp_generator]
  rfl

variable (E) in
/-- The Schnorr Σ-protocol of the fixed-shape functions: statements `X`, commitment
`schnorr_commit`, response `schnorr_response`, verifier `schnorr_verify` (status `0`
accepts) and simulator `schnorr_simulate_commitment`, on the limbs of the encodings, with
decoded results. The extractor is that of `linearSigma`. -/
noncomputable def fixedSchnorrSigma (gen : PMF (gp.G × (Fin 1 → gp.Scalar))) : Sigma where
  Stmt := gp.G
  Wit := Fin 1 → gp.Scalar
  Com := Fin 1 → gp.G
  Ch := gp.Scalar
  Resp := Fin 1 → gp.Scalar
  Rand := Fin 1 → gp.Scalar
  SimRand := Fin 1 → gp.Scalar
  inhWit := ⟨fun _ => gp.scalarZero⟩
  rel X w := (dlogRelation gp X).Holds w
  gen := gen
  commit _ _ r := fun _ =>
    ofLimbsG E (@SigmaProofs.schnorr_commit (groupSigmaProofsDeps E) (limbsS E (r 0)))
  respond _ w r c := fun _ =>
    ofLimbsS E (@SigmaProofs.schnorr_response (groupSigmaProofsDeps E) (limbsS E (w 0))
      (limbsS E (r 0)) (limbsS E c))
  verify X a c z :=
    decide (@SigmaProofs.schnorr_verify (groupSigmaProofsDeps E) (limbsG E X) (limbsG E (a 0))
      (limbsS E c) (limbsS E (z 0)) = 0)
  simulate X c z := (fun _ => ofLimbsG E (@SigmaProofs.schnorr_simulate_commitment
      (groupSigmaProofsDeps E) (limbsG E X) (limbsS E c) (limbsS E (z 0))), z)
  extract _ _ c z c' z' j := gp.scalarDiv (gp.scalarSub (z j) (z' j)) (gp.scalarSub c c')

theorem schnorr_commit_eq (hE : BytesEncoding E) (k : gp.Scalar) :
    ofLimbsG E (@SigmaProofs.schnorr_commit (groupSigmaProofsDeps E) (limbsS E k)) = gp.exp k := by
  simp only [SigmaProofs.schnorr_commit, limbs_to_bytes_encS hE, groupSigmaProofsDeps_generator,
    groupSigmaProofsDeps_group_mul, E.decG_encG, E.decS_encS]
  rw [← limbsG, ofLimbsG_limbsG hE, gp.groupExp_generator]

theorem schnorr_response_eq (hE : BytesEncoding E) (x k c : gp.Scalar) :
    ofLimbsS E (@SigmaProofs.schnorr_response (groupSigmaProofsDeps E) (limbsS E x) (limbsS E k)
      (limbsS E c)) = gp.scalarAdd k (gp.scalarMul c x) := by
  simp only [SigmaProofs.schnorr_response, limbs_to_bytes_encS hE,
    groupSigmaProofsDeps_scalar_mul, groupSigmaProofsDeps_scalar_add, E.decS_encS]
  rw [← limbsS, ofLimbsS_limbsS hE, GroupParam.scalarMul_eq_mul, GroupParam.scalarMul_eq_mul,
    mul_comm]

theorem schnorr_simulate_commitment_eq (hE : BytesEncoding E) (X : gp.G) (c z : gp.Scalar) :
    @SigmaProofs.schnorr_simulate_commitment (groupSigmaProofsDeps E) (limbsG E X) (limbsS E c)
      (limbsS E z) =
        limbsG E (gp.groupMul (gp.groupExp gp.generator z) (gp.groupExp X (gp.scalarNeg c))) := by
  simp only [SigmaProofs.schnorr_simulate_commitment, limbs_to_bytes_encS hE,
    limbs_to_bytes_encG hE, groupSigmaProofsDeps_generator, groupSigmaProofsDeps_group_mul,
    groupSigmaProofsDeps_group_add, groupSigmaProofsDeps_scalar_neg, E.decG_encG, E.decS_encS]
  rfl

/-- `schnorr_verify` returns `0` exactly when the commitment is `g^z · X^(−c)`. -/
theorem schnorr_verify_eq_zero_iff (hE : BytesEncoding E) (X a : gp.G) (c z : gp.Scalar) :
    @SigmaProofs.schnorr_verify (groupSigmaProofsDeps E) (limbsG E X) (limbsG E a) (limbsS E c)
      (limbsS E z) = 0 ↔
        a = gp.groupMul (gp.groupExp gp.generator z) (gp.groupExp X (gp.scalarNeg c)) := by
  simp only [SigmaProofs.schnorr_verify]
  rw [schnorr_simulate_commitment_eq hE, fixed_eq_limbsG hE]
  split_ifs with h
  · simp [h]
  · simp only [one_ne_zero, false_iff]
    exact fun e => h e.symm

variable {gen : PMF (gp.G × (Fin 1 → gp.Scalar))}

/-- The Schnorr Σ-protocol of the fixed-shape functions is `linearSigma` of the Schnorr
relation `dlogRelation`. -/
theorem fixedSchnorrSigma_eq (hE : BytesEncoding E) :
    fixedSchnorrSigma E gen = linearSigma gp 1 1 (dlogRelation gp) gen := by
  unfold fixedSchnorrSigma linearSigma
  congr 1
  · funext X w r i
    rw [schnorr_commit_eq hE, dlogRelation_map]
  · funext X w r c i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact schnorr_response_eq hE _ _ _
  · funext X a c z
    refine Bool.eq_iff_iff.mpr ((decide_eq_true_iff.trans (schnorr_verify_eq_zero_iff hE ..)).trans
      (Iff.trans ?_ (linearSigma_verify_iff (dlogRelation gp) gen X a c z).symm))
    rw [funext_iff, Fin.forall_fin_one, dlogRelation_simCommit]
  · funext X c z
    refine Prod.ext (funext fun i => ?_) rfl
    rw [schnorr_simulate_commitment_eq hE, ofLimbsG_limbsG hE]
    exact (dlogRelation_simCommit X c z i).symm

/-- The verifier of the fixed-shape Schnorr protocol accepts exactly the commitments the
simulator of the Schnorr relation recomputes. -/
theorem fixedSchnorrSigma_verify_iff (hE : BytesEncoding E) (X : gp.G) (a : Fin 1 → gp.G)
    (c : gp.Scalar) (z : Fin 1 → gp.Scalar) :
    (fixedSchnorrSigma E gen).verify X a c z = true ↔ a = (dlogRelation gp X).simCommit c z := by
  simp only [fixedSchnorrSigma, decide_eq_true_iff]
  rw [schnorr_verify_eq_zero_iff hE, funext_iff, Fin.forall_fin_one, dlogRelation_simCommit]

/-! ## DLEQ -/

/-- The linear map of the DLEQ relation: `w ↦ (g^w₀, H^w₀)`. -/
theorem dleqRelation_map (H X Y : gp.G) (w : Fin 1 → gp.Scalar) :
    (dleqRelation gp H X Y).map w = ![gp.exp (w 0), gp.groupExp H (w 0)] := by
  funext i
  fin_cases i <;> simp [LinearRelation.map, LinearRelation.elem, dleqRelation, vecGet,
    gp.groupMul_identity, gp.groupExp_generator]

/-- The simulated commitment of the DLEQ relation: `(g^z · X^(−c), H^z · Y^(−c))`. -/
theorem dleqRelation_simCommit (H X Y : gp.G) (c : gp.Scalar) (z : Fin 1 → gp.Scalar) :
    (dleqRelation gp H X Y).simCommit c z =
      ![gp.groupMul (gp.groupExp gp.generator (z 0)) (gp.groupExp X (gp.scalarNeg c)),
        gp.groupMul (gp.groupExp H (z 0)) (gp.groupExp Y (gp.scalarNeg c))] := by
  funext i
  simp only [LinearRelation.simCommit, dleqRelation_map, gp.groupInv_groupExp]
  fin_cases i <;> simp [LinearRelation.image, LinearRelation.elem, dleqRelation,
    gp.groupExp_generator]

variable (E) in
/-- The comparison of two pairs of four-limb arrays: `fixed_eq` on each half, the results
or-ed; `0` when both halves are equal. -/
def fixedPairEq (p q : Array Int) : Int :=
  Hax.bitor_w 64
    (@SigmaProofs.fixed_eq (groupSigmaProofsDeps E) (@SigmaProofs.fixed_first (groupSigmaProofsDeps E) p)
      (@SigmaProofs.fixed_first (groupSigmaProofsDeps E) q))
    (@SigmaProofs.fixed_eq (groupSigmaProofsDeps E) (@SigmaProofs.fixed_second (groupSigmaProofsDeps E) p)
      (@SigmaProofs.fixed_second (groupSigmaProofsDeps E) q))

theorem fixedPairEq_eq_zero_iff (hE : BytesEncoding E) (x y x' y' : gp.G) :
    fixedPairEq E (pairG E x y) (pairG E x' y') = 0 ↔ x = x' ∧ y = y' := by
  rw [fixedPairEq, bitor_w_eq_zero_iff, fixed_first_pairG, fixed_first_pairG, fixed_second_pairG,
    fixed_second_pairG, fixed_eq_limbsG hE, fixed_eq_limbsG hE]
  split_ifs with h1 h2 h2 <;> simp [Hax.mod2w, h1, h2]

variable (E) in
/-- The DLEQ Σ-protocol of the fixed-shape functions on statements `(H, X, Y)`: commitment
`dleq_commit`, response `dleq_response`, simulator `dleq_simulate_commitment`, on the limbs of
the encodings, with decoded results; the verifier compares the commitment with the one
`dleq_simulate_commitment` recomputes, half by half with `fixed_eq` (`fixedPairEq`). The
extractor is that of `linearSigma`. -/
noncomputable def fixedDleqSigma (gen : PMF ((gp.G × gp.G × gp.G) × (Fin 1 → gp.Scalar))) :
    Sigma where
  Stmt := gp.G × gp.G × gp.G
  Wit := Fin 1 → gp.Scalar
  Com := Fin 2 → gp.G
  Ch := gp.Scalar
  Resp := Fin 1 → gp.Scalar
  Rand := Fin 1 → gp.Scalar
  SimRand := Fin 1 → gp.Scalar
  inhWit := ⟨fun _ => gp.scalarZero⟩
  rel s w := (dleqRelation gp s.1 s.2.1 s.2.2).Holds w
  gen := gen
  commit s _ r :=
    ofPairG E (@SigmaProofs.dleq_commit (groupSigmaProofsDeps E) (limbsG E s.1) (limbsS E (r 0)))
  respond _ w r c := fun _ =>
    ofLimbsS E (@SigmaProofs.dleq_response (groupSigmaProofsDeps E) (limbsS E (w 0))
      (limbsS E (r 0)) (limbsS E c))
  verify s a c z :=
    decide (fixedPairEq E (@SigmaProofs.dleq_simulate_commitment (groupSigmaProofsDeps E)
      (limbsG E s.1) (pairG E s.2.1 s.2.2) (limbsS E c) (limbsS E (z 0))) (pairG E (a 0) (a 1)) = 0)
  simulate s c z := (ofPairG E (@SigmaProofs.dleq_simulate_commitment (groupSigmaProofsDeps E)
      (limbsG E s.1) (pairG E s.2.1 s.2.2) (limbsS E c) (limbsS E (z 0))), z)
  extract _ _ c z c' z' j := gp.scalarDiv (gp.scalarSub (z j) (z' j)) (gp.scalarSub c c')

theorem dleq_commit_eq (hE : BytesEncoding E) (H : gp.G) (k : gp.Scalar) :
    ofPairG E (@SigmaProofs.dleq_commit (groupSigmaProofsDeps E) (limbsG E H) (limbsS E k)) =
      ![gp.exp k, gp.groupExp H k] := by
  simp only [SigmaProofs.dleq_commit, limbs_to_bytes_encS hE, limbs_to_bytes_encG hE,
    groupSigmaProofsDeps_generator, groupSigmaProofsDeps_group_mul, E.decG_encG, E.decS_encS]
  rw [← limbsG, ← limbsG, ofPairG_fixed_pair hE, gp.groupExp_generator]

theorem dleq_response_eq (hE : BytesEncoding E) (x k c : gp.Scalar) :
    ofLimbsS E (@SigmaProofs.dleq_response (groupSigmaProofsDeps E) (limbsS E x) (limbsS E k)
      (limbsS E c)) = gp.scalarAdd k (gp.scalarMul c x) := by
  simp only [SigmaProofs.dleq_response]
  exact schnorr_response_eq hE x k c

theorem dleq_simulate_commitment_eq (hE : BytesEncoding E) (H X Y : gp.G) (c z : gp.Scalar) :
    @SigmaProofs.dleq_simulate_commitment (groupSigmaProofsDeps E) (limbsG E H) (pairG E X Y)
      (limbsS E c) (limbsS E z) =
        pairG E (gp.groupMul (gp.groupExp gp.generator z) (gp.groupExp X (gp.scalarNeg c)))
          (gp.groupMul (gp.groupExp H z) (gp.groupExp Y (gp.scalarNeg c))) := by
  simp only [SigmaProofs.dleq_simulate_commitment, fixed_first_pairG, fixed_second_pairG,
    limbs_to_bytes_encS hE, limbs_to_bytes_encG hE, groupSigmaProofsDeps_generator,
    groupSigmaProofsDeps_group_mul, groupSigmaProofsDeps_group_add,
    groupSigmaProofsDeps_scalar_neg, E.decG_encG, E.decS_encS]
  rfl

variable {gen' : PMF ((gp.G × gp.G × gp.G) × (Fin 1 → gp.Scalar))}

/-- The DLEQ Σ-protocol of the fixed-shape functions is `linearSigma` of the DLEQ relation
`dleqRelation`. -/
theorem fixedDleqSigma_eq (hE : BytesEncoding E) :
    fixedDleqSigma E gen' =
      linearSigma gp 1 2 (fun s => dleqRelation gp s.1 s.2.1 s.2.2) gen' := by
  unfold fixedDleqSigma linearSigma
  congr 1
  · funext s w r
    rw [dleq_commit_eq hE, dleqRelation_map]
  · funext s w r c i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact dleq_response_eq hE _ _ _
  · funext s a c z
    refine Bool.eq_iff_iff.mpr ((decide_eq_true_iff.trans ?_).trans
      (linearSigma_verify_iff (fun s => dleqRelation gp s.1 s.2.1 s.2.2) gen' s a c z).symm)
    rw [dleq_simulate_commitment_eq hE, fixedPairEq_eq_zero_iff hE, dleqRelation_simCommit,
      funext_iff, Fin.forall_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, eq_comm]
  · funext s c z
    refine Prod.ext ?_ rfl
    rw [dleq_simulate_commitment_eq hE, pairG, ofPairG_fixed_pair hE, dleqRelation_simCommit]

/-- The verifier of the fixed-shape DLEQ protocol accepts exactly the commitments the
simulator of the DLEQ relation recomputes. -/
theorem fixedDleqSigma_verify_iff (hE : BytesEncoding E) (s : gp.G × gp.G × gp.G)
    (a : Fin 2 → gp.G) (c : gp.Scalar) (z : Fin 1 → gp.Scalar) :
    (fixedDleqSigma E gen').verify s a c z = true ↔
      a = (dleqRelation gp s.1 s.2.1 s.2.2).simCommit c z := by
  simp only [fixedDleqSigma, decide_eq_true_iff]
  rw [dleq_simulate_commitment_eq hE, fixedPairEq_eq_zero_iff hE, dleqRelation_simCommit,
    funext_iff, Fin.forall_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, eq_comm]

/-! ## Compact proofs -/

/-- The compact Schnorr verification of `(c, z)`, `schnorr_compact_commitment` followed by
`fixed_compact_accept` of `c` against the limbs of the challenge `H` of the decoded
commitment, returns `0` exactly when `linearCompactVerify` of the Schnorr relation accepts. -/
theorem schnorr_compact_eq_zero_iff (hE : BytesEncoding E)
    (H : gp.G → (Fin 1 → gp.G) → gp.Scalar) (X : gp.G) (c : gp.Scalar) (z : Fin 1 → gp.Scalar) :
    @SigmaProofs.fixed_compact_accept (groupSigmaProofsDeps E) (limbsS E c)
        (limbsS E (H X fun _ => ofLimbsG E (@SigmaProofs.schnorr_compact_commitment
          (groupSigmaProofsDeps E) (limbsG E X) (limbsS E c) (limbsS E (z 0))))) = 0 ↔
      linearCompactVerify (dlogRelation gp) H X c z = true := by
  simp only [SigmaProofs.fixed_compact_accept, SigmaProofs.schnorr_compact_commitment]
  rw [schnorr_simulate_commitment_eq hE, ofLimbsG_limbsG hE, fixed_eq_limbsS hE,
    linearCompactVerify, decide_eq_true_iff,
    show (dlogRelation gp X).simCommit c z = _ from funext (dlogRelation_simCommit X c z)]
  split_ifs with h
  · exact ⟨fun _ => h.symm, fun _ => rfl⟩
  · simp only [one_ne_zero, false_iff]
    exact fun e => h e.symm

/-- The compact DLEQ verification of `(c, z)`, `dleq_compact_commitment` followed by
`fixed_compact_accept` of `c` against the limbs of the challenge `H` of the decoded
commitment, returns `0` exactly when `linearCompactVerify` of the DLEQ relation accepts. -/
theorem dleq_compact_eq_zero_iff (hE : BytesEncoding E)
    (Hc : gp.G × gp.G × gp.G → (Fin 2 → gp.G) → gp.Scalar) (s : gp.G × gp.G × gp.G)
    (c : gp.Scalar) (z : Fin 1 → gp.Scalar) :
    @SigmaProofs.fixed_compact_accept (groupSigmaProofsDeps E) (limbsS E c)
        (limbsS E (Hc s (ofPairG E (@SigmaProofs.dleq_compact_commitment (groupSigmaProofsDeps E)
          (limbsG E s.1) (pairG E s.2.1 s.2.2) (limbsS E c) (limbsS E (z 0)))))) = 0 ↔
      linearCompactVerify (fun s => dleqRelation gp s.1 s.2.1 s.2.2) Hc s c z = true := by
  simp only [SigmaProofs.fixed_compact_accept, SigmaProofs.dleq_compact_commitment]
  rw [dleq_simulate_commitment_eq hE, pairG, ofPairG_fixed_pair hE, fixed_eq_limbsS hE,
    linearCompactVerify, decide_eq_true_iff, dleqRelation_simCommit]
  split_ifs with h
  · exact ⟨fun _ => h.symm, fun _ => rfl⟩
  · simp only [one_ne_zero, false_iff]
    exact fun e => h e.symm

/-! ## Batched DLEQ verification and encodability -/

/-- `dleq_verify_batchable` with randomness `r` returns `0` exactly when the batched DLEQ
equation `A₀ · A₁^r · g^(−z) · H^(−r·z) · X^c · Y^(r·c) = 1` holds. -/
theorem dleq_verify_batchable_eq_zero_iff (hE : BytesEncoding E) (H X Y A₀ A₁ : gp.G)
    (c z r : gp.Scalar) :
    @SigmaProofs.dleq_verify_batchable (groupSigmaProofsDeps E) (limbsG E H) (pairG E X Y)
        (pairG E A₀ A₁) (limbsS E c) (limbsS E z) (limbsS E r) = 0 ↔
      gp.groupMul (gp.groupMul (gp.groupMul (gp.groupMul (gp.groupMul A₀ (gp.groupExp A₁ r))
        (gp.groupExp gp.generator (gp.scalarNeg z)))
        (gp.groupExp H (gp.scalarNeg (gp.scalarMul r z)))) (gp.groupExp X c))
        (gp.groupExp Y (gp.scalarMul r c)) = gp.identity := by
  simp only [SigmaProofs.dleq_verify_batchable, fixed_first_pairG, fixed_second_pairG,
    limbs_to_bytes_encS hE, limbs_to_bytes_encG hE, groupSigmaProofsDeps_generator,
    groupSigmaProofsDeps_identity, groupSigmaProofsDeps_group_mul, groupSigmaProofsDeps_group_add,
    groupSigmaProofsDeps_scalar_neg, groupSigmaProofsDeps_scalar_mul, E.decG_encG, E.decS_encS]
  rw [← limbsG, ← limbsG, fixed_eq_limbsG hE]
  split_ifs with h
  · simp [h]
  · simp [h]

/-- `fixed_encodable` of the limbs of an element is `1` on the identity and `0` otherwise. -/
theorem fixed_encodable_eq (hE : BytesEncoding E) (x : gp.G) :
    @SigmaProofs.fixed_encodable (groupSigmaProofsDeps E) (limbsG E x) =
      if x = gp.identity then 1 else 0 := by
  simp only [SigmaProofs.fixed_encodable, groupSigmaProofsDeps_identity]
  rw [← limbsG, fixed_eq_limbsG hE]
  split_ifs <;> rfl

/-- `fixed_encodable` of the limbs of an element returns `0` exactly when the element is not
the identity. -/
theorem fixed_encodable_eq_zero_iff (hE : BytesEncoding E) (x : gp.G) :
    @SigmaProofs.fixed_encodable (groupSigmaProofsDeps E) (limbsG E x) = 0 ↔ x ≠ gp.identity := by
  rw [fixed_encodable_eq hE]
  split_ifs with h <;> simp [h]

/-- `dleq_encodable` of the limbs of a pair returns `0` exactly when neither element is the
identity. -/
theorem dleq_encodable_eq_zero_iff (hE : BytesEncoding E) (x y : gp.G) :
    @SigmaProofs.dleq_encodable (groupSigmaProofsDeps E) (pairG E x y) = 0 ↔
      x ≠ gp.identity ∧ y ≠ gp.identity := by
  simp only [SigmaProofs.dleq_encodable, fixed_first_pairG, fixed_second_pairG]
  rw [bitor_w_eq_zero_iff, fixed_encodable_eq hE, fixed_encodable_eq hE]
  split_ifs with h1 h2 h2 <;> simp [Hax.mod2w, h1, h2]

/-! ## Security of the fixed-shape protocols -/

open scoped ENNReal
open CatCrypt.Crypto.FiatShamirROM.DuplexSponge

noncomputable instance : DecidableEq (fixedSchnorrSigma E gen).Stmt := Classical.decEq _

noncomputable instance : DecidableEq (fixedDleqSigma E gen').Stmt := Classical.decEq _

theorem fixedSchnorrSigma_complete (hE : BytesEncoding E) : (fixedSchnorrSigma E gen).Complete :=
  fixedSchnorrSigma_eq hE ▸ linearSigma_complete _ gen

theorem fixedSchnorrSigma_specialSound (hE : BytesEncoding E) :
    (fixedSchnorrSigma E gen).SpecialSound :=
  fixedSchnorrSigma_eq hE ▸ linearSigma_specialSound _ gen

theorem fixedSchnorrSigma_perfectHVZK (hE : BytesEncoding E)
    (hgen : ∀ s w, (s, w) ∈ gen.support → (dlogRelation gp s).Holds w) :
    (fixedSchnorrSigma E gen).PerfectHVZK :=
  fixedSchnorrSigma_eq hE ▸ linearSigma_perfectHVZK _ gen hgen

/-- The fixed-shape Schnorr protocol has perfect HVZK at every pair of the relation. -/
theorem fixedSchnorrSigma_statHVZKAt (hE : BytesEncoding E) (s : gp.G) (w : Fin 1 → gp.Scalar)
    (hw : (dlogRelation gp s).Holds w) : (fixedSchnorrSigma E gen).StatHVZKAt s w 0 :=
  (fixedSchnorrSigma_perfectHVZK (gen := PMF.pure (s, w)) hE fun s' w' hsw => by
    rw [PMF.support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hsw
    obtain ⟨rfl, rfl⟩ := hsw
    exact hw).statHVZK s w ((PMF.mem_support_pure_iff _ _).mpr rfl)

/-- **Knowledge soundness of the strong Fiat–Shamir proofs of the fixed-shape Schnorr
protocol.** For every adversary `A` with at most `qH` random-oracle queries, with
`ε = ksAdvantage A`, `ε·(ε/(qH + 1) − 1/|Scalar|) ≤ ksExtractProb A`. -/
theorem fixedSchnorrSigma_ksExtractProb_ge (hE : BytesEncoding E) {Sid : Type} [DecidableEq Sid]
    {qH : ℕ} (A : KSAdversary (fixedSchnorrSigma E gen) Sid qH) :
    ksAdvantage A * (ksAdvantage A / ((qH + 1 : ℕ) : ℝ≥0∞) - 1 / Fintype.card gp.Scalar) ≤
      ksExtractProb A :=
  ksExtractProb_ge (fixedSchnorrSigma_specialSound hE) A

/-- **Zero knowledge of the strong Fiat–Shamir proofs of the fixed-shape Schnorr protocol.**
For a commitment bound `γ` at every pair of the relation and every distinguisher with at most
`qH` random-oracle and `qP` proving queries, `zkReal D ≤ zkSim D + qP·(qH + qP)·γ`. -/
theorem fixedSchnorrSigma_zkReal_le_zkSim (hE : BytesEncoding E) {Sid : Type} [DecidableEq Sid]
    {γ : ℝ≥0∞}
    (hγ : ∀ s w, (dlogRelation gp s).Holds w → (fixedSchnorrSigma E gen).CommitBoundAt s w γ)
    {qH qP : ℕ} (D : ZKDistinguisher (fixedSchnorrSigma E gen) Sid qH qP) :
    zkReal D ≤ zkSim D + ((qP * (qH + qP) : ℕ) : ℝ≥0∞) * γ := by
  have h := zkReal_le_zkSim (P := fixedSchnorrSigma E gen) (δ := 0) (γ := γ)
    (fun s w hw => fixedSchnorrSigma_statHVZKAt hE s w hw) hγ D
  simpa only [mul_zero, zero_add] using h

/-- **Knowledge soundness of the duplex-sponge proofs of the fixed-shape Schnorr protocol.**
For prefix-free encodings and a challenge decoding with the minorant `(1 − β)·uniform`, every
adversary with at most `qH` oracle queries satisfies, with
`ε = dsKsAdvantage A − (qH + 1)·β`, `ε·(ε/(qH + 1) − 1/|Scalar|) ≤ ksExtractProb A`. -/
theorem fixedSchnorrSigma_dsKsExtractProb_ge (hE : BytesEncoding E)
    (Dp : DSParams (fixedSchnorrSigma E gen)) (hX : PrefixFree Dp.encX) (hA : PrefixFree Dp.encA)
    {β : ℝ≥0∞} (hβ : ∀ c, (1 - β) * PMF.uniformOfFintype gp.Scalar c ≤
      (PMF.uniformOfFintype (Fin Dp.L → UInt8)).map Dp.decB c)
    {qH : ℕ} (A : KSAdversary (fixedSchnorrSigma E gen) SessionId qH) :
    (dsKsAdvantage Dp A - (qH + 1 : ℕ) * β) *
        ((dsKsAdvantage Dp A - (qH + 1 : ℕ) * β) / ((qH + 1 : ℕ) : ℝ≥0∞) -
          1 / Fintype.card gp.Scalar) ≤
      ksExtractProb A :=
  dsKsExtractProb_ge Dp (fixedSchnorrSigma_specialSound hE) hX hA hβ A

/-- **Zero knowledge of the duplex-sponge proofs of the fixed-shape Schnorr protocol.** For a
commitment bound `γ` at every pair of the relation and every distinguisher with at most `qH`
random-oracle and `qP` proving queries against the transform with byte challenges,
`zkReal D ≤ zkSim D + qP·(qH + qP)·γ`. -/
theorem fixedSchnorrSigma_dsZkReal_le_zkSim (hE : BytesEncoding E)
    (Dp : DSParams (fixedSchnorrSigma E gen)) {γ : ℝ≥0∞}
    (hγ : ∀ s w, (dlogRelation gp s).Holds w → (fixedSchnorrSigma E gen).CommitBoundAt s w γ)
    {qH qP : ℕ} (Dz : ZKDistinguisher Dp.sigmaBytes SessionId qH qP) :
    zkReal Dz ≤ zkSim Dz + ((qP * (qH + qP) : ℕ) : ℝ≥0∞) * γ := by
  have h := dsZkReal_le_zkSim Dp (δ := 0) (γ := γ)
    (fun s w hw => fixedSchnorrSigma_statHVZKAt hE s w hw) hγ Dz
  simpa only [mul_zero, zero_add] using h

theorem fixedDleqSigma_complete (hE : BytesEncoding E) : (fixedDleqSigma E gen').Complete :=
  fixedDleqSigma_eq hE ▸ linearSigma_complete _ gen'

theorem fixedDleqSigma_specialSound (hE : BytesEncoding E) :
    (fixedDleqSigma E gen').SpecialSound :=
  fixedDleqSigma_eq hE ▸ linearSigma_specialSound _ gen'

theorem fixedDleqSigma_perfectHVZK (hE : BytesEncoding E)
    (hgen : ∀ s w, (s, w) ∈ gen'.support → (dleqRelation gp s.1 s.2.1 s.2.2).Holds w) :
    (fixedDleqSigma E gen').PerfectHVZK :=
  fixedDleqSigma_eq hE ▸ linearSigma_perfectHVZK _ gen' hgen

/-- The fixed-shape DLEQ protocol has perfect HVZK at every pair of the relation. -/
theorem fixedDleqSigma_statHVZKAt (hE : BytesEncoding E) (s : gp.G × gp.G × gp.G)
    (w : Fin 1 → gp.Scalar) (hw : (dleqRelation gp s.1 s.2.1 s.2.2).Holds w) :
    (fixedDleqSigma E gen').StatHVZKAt s w 0 :=
  (fixedDleqSigma_perfectHVZK (gen' := PMF.pure (s, w)) hE fun s' w' hsw => by
    rw [PMF.support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hsw
    obtain ⟨rfl, rfl⟩ := hsw
    exact hw).statHVZK s w ((PMF.mem_support_pure_iff _ _).mpr rfl)

/-- **Knowledge soundness of the strong Fiat–Shamir proofs of the fixed-shape DLEQ
protocol.** For every adversary `A` with at most `qH` random-oracle queries, with
`ε = ksAdvantage A`, `ε·(ε/(qH + 1) − 1/|Scalar|) ≤ ksExtractProb A`. -/
theorem fixedDleqSigma_ksExtractProb_ge (hE : BytesEncoding E) {Sid : Type} [DecidableEq Sid]
    {qH : ℕ} (A : KSAdversary (fixedDleqSigma E gen') Sid qH) :
    ksAdvantage A * (ksAdvantage A / ((qH + 1 : ℕ) : ℝ≥0∞) - 1 / Fintype.card gp.Scalar) ≤
      ksExtractProb A :=
  ksExtractProb_ge (fixedDleqSigma_specialSound hE) A

/-- **Zero knowledge of the strong Fiat–Shamir proofs of the fixed-shape DLEQ protocol.** For
a commitment bound `γ` at every pair of the relation and every distinguisher with at most `qH`
random-oracle and `qP` proving queries, `zkReal D ≤ zkSim D + qP·(qH + qP)·γ`. -/
theorem fixedDleqSigma_zkReal_le_zkSim (hE : BytesEncoding E) {Sid : Type} [DecidableEq Sid]
    {γ : ℝ≥0∞}
    (hγ : ∀ s w, (dleqRelation gp s.1 s.2.1 s.2.2).Holds w →
      (fixedDleqSigma E gen').CommitBoundAt s w γ)
    {qH qP : ℕ} (D : ZKDistinguisher (fixedDleqSigma E gen') Sid qH qP) :
    zkReal D ≤ zkSim D + ((qP * (qH + qP) : ℕ) : ℝ≥0∞) * γ := by
  have h := zkReal_le_zkSim (P := fixedDleqSigma E gen') (δ := 0) (γ := γ)
    (fun s w hw => fixedDleqSigma_statHVZKAt hE s w hw) hγ D
  simpa only [mul_zero, zero_add] using h

/-- **Knowledge soundness of the duplex-sponge proofs of the fixed-shape DLEQ protocol.** For
prefix-free encodings and a challenge decoding with the minorant `(1 − β)·uniform`, every
adversary with at most `qH` oracle queries satisfies, with
`ε = dsKsAdvantage A − (qH + 1)·β`, `ε·(ε/(qH + 1) − 1/|Scalar|) ≤ ksExtractProb A`. -/
theorem fixedDleqSigma_dsKsExtractProb_ge (hE : BytesEncoding E)
    (Dp : DSParams (fixedDleqSigma E gen')) (hX : PrefixFree Dp.encX) (hA : PrefixFree Dp.encA)
    {β : ℝ≥0∞} (hβ : ∀ c, (1 - β) * PMF.uniformOfFintype gp.Scalar c ≤
      (PMF.uniformOfFintype (Fin Dp.L → UInt8)).map Dp.decB c)
    {qH : ℕ} (A : KSAdversary (fixedDleqSigma E gen') SessionId qH) :
    (dsKsAdvantage Dp A - (qH + 1 : ℕ) * β) *
        ((dsKsAdvantage Dp A - (qH + 1 : ℕ) * β) / ((qH + 1 : ℕ) : ℝ≥0∞) -
          1 / Fintype.card gp.Scalar) ≤
      ksExtractProb A :=
  dsKsExtractProb_ge Dp (fixedDleqSigma_specialSound hE) hX hA hβ A

/-- **Zero knowledge of the duplex-sponge proofs of the fixed-shape DLEQ protocol.** For a
commitment bound `γ` at every pair of the relation and every distinguisher with at most `qH`
random-oracle and `qP` proving queries against the transform with byte challenges,
`zkReal D ≤ zkSim D + qP·(qH + qP)·γ`. -/
theorem fixedDleqSigma_dsZkReal_le_zkSim (hE : BytesEncoding E)
    (Dp : DSParams (fixedDleqSigma E gen')) {γ : ℝ≥0∞}
    (hγ : ∀ s w, (dleqRelation gp s.1 s.2.1 s.2.2).Holds w →
      (fixedDleqSigma E gen').CommitBoundAt s w γ)
    {qH qP : ℕ} (Dz : ZKDistinguisher Dp.sigmaBytes SessionId qH qP) :
    zkReal Dz ≤ zkSim Dz + ((qP * (qH + qP) : ℕ) : ℝ≥0∞) * γ := by
  have h := dsZkReal_le_zkSim Dp (δ := 0) (γ := γ)
    (fun s w hw => fixedDleqSigma_statHVZKAt hE s w hw) hγ Dz
  simpa only [mul_zero, zero_add] using h

/-! ## The fixed shape is the generic core on its instance -/

variable (E) in
/-- The equation of the Schnorr instance in the encoding of the extracted core: image
`[(1, 1)]` and terms `[(0, 0, 1)]`, coefficients the encoding of the scalar one. -/
def schnorrEquations : Array ((Array (Int × Array Int)) × (Array (Int × Int × Array Int))) :=
  #[(#[((1 : Int), E.encS gp.scalarOne)], #[((0 : Int), (0 : Int), E.encS gp.scalarOne)])]

/-- The element array of an instance built by the extracted `Instance_new` is the generator
followed by the statement elements. -/
theorem Instance_new_elements {els : Array (Array Int)}
    {eqs : Array ((Array (Int × Array Int)) × (Array (Int × Int × Array Int)))}
    {inst : SigmaProofs.Instance_T}
    (h : @SigmaProofs.Instance_new (groupSigmaProofsDeps E) els eqs = .ok inst) :
    inst.1 = #[E.encG gp.generator] ++ els := by
  unfold SigmaProofs.Instance_new at h
  simp only [Hax.deref] at h
  rw [@instance_elements_eq (groupSigmaProofsDeps E) els, groupSigmaProofsDeps_generator] at h
  split at h
  · simp only [SigmaProofs.Instance, Except.ok.injEq] at h
    subst h
    rfl
  · simp at h

/-- The relation that the extracted core decodes from the Schnorr instance built by
`Instance_new` from `[encG X]` has the linear map and the image of `dlogRelation gp X`. -/
theorem schnorrInstance_map_image {X : gp.G} {inst : SigmaProofs.Instance_T}
    (h : @SigmaProofs.Instance_new (groupSigmaProofsDeps E) #[E.encG X] (schnorrEquations E) =
      .ok inst) :
    (decodeRel E 1 1 inst).map = (dlogRelation gp X).map ∧
      (decodeRel E 1 1 inst).image = (dlogRelation gp X).image := by
  obtain ⟨heqs, himg⟩ := Instance_new_image h 1
  have hels := Instance_new_elements h
  have hsz : (schnorrEquations E).size = 1 := rfl
  constructor
  · funext w i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    rw [dlogRelation_map]
    have hterm := decodeRel_elem_term E 1 1 inst 0 0 (by omega)
      (by simp [heqs, schnorrEquations, Hax.index])
    have hterms : ((decodeRel E 1 1 inst).equations 0).terms = [(0, 1 + 0 * termBound inst + 0)] := by
      simp [decodeRel, heqs, schnorrEquations, uidx, Hax.index, Hax.castVal_w, Hax.mod2w]
    simp only [LinearRelation.map, hterms, List.map_cons, List.map_nil, List.foldr_cons,
      List.foldr_nil, hterm]
    simp [termElem, hels, heqs, schnorrEquations, Hax.index, Hax.castVal_w, Hax.mod2w, vecGet,
      E.decG_encG, E.decS_encS, gp.groupExp_one, gp.groupMul_identity, gp.groupExp_generator]
  · funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have h0 := himg ⟨0, by rw [hsz]; omega⟩
    refine h0.trans ?_
    rw [hels]
    simp [imageComb, schnorrEquations, LinearRelation.image, LinearRelation.elem, dlogRelation,
      Hax.index, Hax.castVal_w, Hax.mod2w, E.decG_encG, E.decS_encS, gp.groupExp_one,
      gp.groupMul_identity]

/-- On the Schnorr instance built by `Instance_new`, the verifier of the generic extracted
protocol `extSigma` and the verifier of the fixed-shape protocol agree. -/
theorem extSigma_verify_eq_fixedSchnorr (hE : BytesEncoding E) {X : gp.G}
    {inst : SigmaProofs.Instance_T}
    (h : @SigmaProofs.Instance_new (groupSigmaProofsDeps E) #[E.encG X] (schnorrEquations E) =
      .ok inst)
    (hw : WellFormed E 1 1 inst) (genE : PMF (ExtStmt E 1 1 × (Fin 1 → gp.Scalar)))
    (a : Fin 1 → gp.G) (c : gp.Scalar) (z : Fin 1 → gp.Scalar) :
    (extSigma E 1 1 genE).verify ⟨inst, hw⟩ a c z = (fixedSchnorrSigma E gen).verify X a c z := by
  have hsim : (decodeRel E 1 1 inst).simCommit c z = (dlogRelation gp X).simCommit c z := by
    obtain ⟨hm, hi⟩ := schnorrInstance_map_image h
    unfold LinearRelation.simCommit
    rw [hm, hi]
  exact Bool.eq_iff_iff.mpr ((extSigma_verify_iff ⟨inst, hw⟩ a c z).trans
    (hsim ▸ (fixedSchnorrSigma_verify_iff hE X a c z).symm))

variable (E) in
/-- The equations of the DLEQ instance in the encoding of the extracted core: image
`[(2, 1)]` with terms `[(0, 0, 1)]`, and image `[(3, 1)]` with terms `[(0, 1, 1)]`,
coefficients the encoding of the scalar one. -/
def dleqEquations : Array ((Array (Int × Array Int)) × (Array (Int × Int × Array Int))) :=
  #[(#[((2 : Int), E.encS gp.scalarOne)], #[((0 : Int), (0 : Int), E.encS gp.scalarOne)]),
    (#[((3 : Int), E.encS gp.scalarOne)], #[((0 : Int), (1 : Int), E.encS gp.scalarOne)])]

/-- The relation that the extracted core decodes from the DLEQ instance built by
`Instance_new` from `[encG H, encG X, encG Y]` has the linear map and the image of
`dleqRelation gp H X Y`. -/
theorem dleqInstance_map_image {H X Y : gp.G} {inst : SigmaProofs.Instance_T}
    (h : @SigmaProofs.Instance_new (groupSigmaProofsDeps E) #[E.encG H, E.encG X, E.encG Y]
      (dleqEquations E) = .ok inst) :
    (decodeRel E 1 2 inst).map = (dleqRelation gp H X Y).map ∧
      (decodeRel E 1 2 inst).image = (dleqRelation gp H X Y).image := by
  obtain ⟨heqs, himg⟩ := Instance_new_image h 1
  have hels := Instance_new_elements h
  have hsz : (dleqEquations E).size = 2 := rfl
  constructor
  · funext w i
    rw [dleqRelation_map]
    have hterm : ∀ j : ℕ, j < 2 →
        (decodeRel E 1 2 inst).elem (2 + j * termBound inst + 0) = termElem E inst j 0 :=
      fun j hj => decodeRel_elem_term E 1 2 inst j 0 hj (by
        interval_cases j <;> simp [heqs, dleqEquations, Hax.index])
    have hterms : ∀ j : Fin 2, ((decodeRel E 1 2 inst).equations j).terms =
        [(0, 2 + (j : ℕ) * termBound inst + 0)] := by
      intro j
      fin_cases j <;> simp [decodeRel, heqs, dleqEquations, uidx, Hax.index, Hax.castVal_w,
        Hax.mod2w]
    simp only [LinearRelation.map, hterms, List.map_cons, List.map_nil, List.foldr_cons,
      List.foldr_nil, hterm i i.isLt]
    fin_cases i <;> simp [termElem, hels, heqs, dleqEquations, Hax.index, Hax.castVal_w,
      Hax.mod2w, vecGet, E.decG_encG, E.decS_encS, gp.groupExp_one, gp.groupMul_identity,
      gp.groupExp_generator]
  · funext i
    have h0 := himg ⟨i, by rw [hsz]; exact i.isLt⟩
    refine h0.trans ?_
    rw [hels]
    fin_cases i <;> simp [imageComb, dleqEquations, LinearRelation.image, LinearRelation.elem,
      dleqRelation, Hax.index, castVal_usize_of_lt, E.decG_encG, E.decS_encS, gp.groupExp_one,
      gp.groupMul_identity]

/-- On the DLEQ instance built by `Instance_new`, the verifier of the generic extracted
protocol `extSigma` and the verifier of the fixed-shape protocol agree. -/
theorem extSigma_verify_eq_fixedDleq (hE : BytesEncoding E) {H X Y : gp.G}
    {inst : SigmaProofs.Instance_T}
    (h : @SigmaProofs.Instance_new (groupSigmaProofsDeps E) #[E.encG H, E.encG X, E.encG Y]
      (dleqEquations E) = .ok inst)
    (hw : WellFormed E 1 2 inst) (genE : PMF (ExtStmt E 1 2 × (Fin 1 → gp.Scalar)))
    (a : Fin 2 → gp.G) (c : gp.Scalar) (z : Fin 1 → gp.Scalar) :
    (extSigma E 1 2 genE).verify ⟨inst, hw⟩ a c z =
      (fixedDleqSigma E gen').verify (H, X, Y) a c z := by
  have hsim : (decodeRel E 1 2 inst).simCommit c z = (dleqRelation gp H X Y).simCommit c z := by
    obtain ⟨hm, hi⟩ := dleqInstance_map_image h
    unfold LinearRelation.simCommit
    rw [hm, hi]
  exact Bool.eq_iff_iff.mpr ((extSigma_verify_iff ⟨inst, hw⟩ a c z).trans
    (hsim ▸ (fixedDleqSigma_verify_iff hE (H, X, Y) a c z).symm))

end Fixed

/-! ## The default encoding -/

/-- The 32 little-endian digits `bytesLE32 x` form a 32-byte array. -/
theorem isBytes32_bytesLE32 (x : ℕ) : IsBytes32 (bytesLE32 x) := by
  refine ⟨by simp [bytesLE32], fun p hp => ?_⟩
  rw [bytesLE32, index_ofFn _ p hp]
  have := Nat.mod_lt (x / 256 ^ p) (by norm_num : 0 < 256)
  constructor <;> omega

/-- The encodings of ristretto255 scalars and elements, `ristrettoEncoding`, are 32-byte
arrays. -/
theorem ristrettoEncoding_bytes : BytesEncoding ristrettoEncoding :=
  ⟨fun _ => isBytes32_bytesLE32 _, fun _ => isBytes32_bytesLE32 _⟩

end CatCrypt.Crypto.SigmaProtocol.FixedShape
