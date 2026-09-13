/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.Commitments.KZG.Def
public import CatCryptCore.Crypto.AGM
public import CatCryptCore.Crypto.ForkingLemma
public import Mathlib.Algebra.Field.ZMod

/-!
# KZG Knowledge Soundness in the AGM

This file proves knowledge soundness of KZG in the Algebraic Group Model:
any adversary that produces a valid evaluation proof must "know" the
committed polynomial (in the AGM sense).

## Main theorems

* `KZG_knowledge_sound` — the knowledge soundness game is bounded by
  `(t + 1)` times the t-SDH advantage of the reduction `ks_to_tSDH`
* `honestAGMOutput_checks` — the honest committer's output passes the game's
  representation and pairing checks, with representations extracting to the
  committed polynomial and its witness polynomial (`honestAGMOutput_toPoly`)

## Proof outline

In the AGM, the adversary outputs:
- Commitment C with representation `[c₀, ..., cₜ]` (implying polynomial φ)
- Evaluation proof (z, y, w) with representation `[d₀, ..., dₜ]` (implying polynomial ψ)

The game checks both representations against the SRS it sampled; an output
with an invalid representation loses. For valid representations,
`C = g₁^(φ(α))` and `w = g₁^(ψ(α))`, and the pairing verification equation forces:
  `φ(α) - y = ψ(α) · (α - z)` in the exponent

In the AGM, this is a polynomial identity `φ(X) - y = ψ(X) · (X - z)` modulo
a polynomial that vanishes at α. If this identity doesn't hold as polynomials,
we can extract a nontrivial polynomial with α as a root, which breaks t-SDH.

## References

* [Rothmann, Kreuzer — KZG_Knowledge_Soundness.thy in Isabelle]
* [Kate, Zaverucha, Goldberg, 2010 — Theorem 2 (informal)]
-/

@[expose] public section

namespace CatCrypt.Examples.Commitments.KZG

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open CatCrypt.Crypto.PairingGroup CatCrypt.Crypto.ForkingLemma
open Polynomial
open scoped ENNReal

variable (P : PairingGroup) (t : ℕ)

/-! ## Full Knowledge Soundness Game -/

/-- Knowledge soundness game for KZG in the algebraic group model.

    The game samples `α`, runs the adversary on the SRS `srs₁ α t`, and the
    adversary wins if:
    1. The commitment representation is valid for that SRS;
    2. The witness representation is valid for that SRS;
    3. The evaluation proof verifies: `verify_eval vk C z y w`;
    4. The claimed value is wrong: `y ≠ φ(z)` where φ is the extracted polynomial.

    An output whose representations do not match the supplied SRS loses. -/
noncomputable def KnowledgeSoundness_Game_Full (A : AGMAdversary P t) : SPComp Bool :=
  SPComp.bind (SPComp.sample (ZMod P.p)) fun α =>
  SPComp.bind (A.run (srs₁ (P := P) α t)) fun out =>
    let C_repr := out.1
    let z := out.2.1
    let y := out.2.2.1
    let w_repr := out.2.2.2
    let φ := C_repr.toPoly
    let vk := srs₂ (P := P) α
    SPComp.pure (decide (C_repr.Valid P t (srs₁ (P := P) α t) ∧
      w_repr.Valid P t (srs₁ (P := P) α t) ∧
      verify_eval P vk C_repr.element z y w_repr.element ∧ y ≠ φ.eval z))

/-! ## Reduction -/

/-- The reduction: converts a knowledge soundness adversary (in AGM) into
    a t-SDH adversary.

    Given AGM adversary A that wins the knowledge soundness game:
    1. Run A on SRS to get (C_repr, z, y, w_repr)
    2. Extract φ from C_repr and ψ from w_repr
    3. Compute δ(X) = φ(X) - y - ψ(X) · (X - z)
    4. If δ = 0, A didn't actually break knowledge soundness
    5. If δ ≠ 0, then δ(α) = 0 (from the pairing check).
       Find a root r and guess r = α. If correct, compute t-SDH solution directly.

    The reduction uses the same "guess the secret" strategy as `poly_binding_to_tSDH`:
    when the guessed root r equals α, we know the secret and can construct the
    t-SDH solution `(c, g₁^(1/(α+c)))`. -/
noncomputable def ks_to_tSDH (A : AGMAdversary P t) :
    tSDH_Adversary P t :=
  fun pk =>
  SPComp.bind (A.run pk) fun out =>
    let C_repr := out.1
    let z := out.2.1
    let y := out.2.2.1
    let w_repr := out.2.2.2
    let φ := C_repr.toPoly
    let ψ := w_repr.toPoly
    -- Compute δ(X) = φ(X) - C(y) - ψ(X) · (X - C(z))
    let δ := φ - C y - ψ * (X - C z)
    -- Sample random root index and guess it equals α
    SPComp.bind (SPComp.sample (Fin (t + 1))) fun i =>
      match (δ.roots.toList)[i.val]? with
      | some r =>
        if r = 0 then
          SPComp.pure (1, P.g₁)
        else
          SPComp.pure (0, P.g₁ ^ᵍ r⁻¹)
      | none => SPComp.pure (0, 1)

/-! ## Pairing Helpers -/

/-- If e(g₁^a, g₂) = e(g₁^b, g₂^c) and e is non-degenerate,
    then a = b·c in the exponent.

    This is the key property for extracting polynomial identities
    from pairing verification equations in the AGM. -/
theorem pairing_exponent_eq (a b c : ZMod P.p)
    (h : P.e (P.g₁ ^ᵍ a) P.g₂ = P.e (P.g₁ ^ᵍ b) (P.g₂ ^ʰ c)) :
    a = b * c := by
  -- Rewrite both sides to expose exponents of e(g₁, g₂)
  rw [e_zpowZMod_left, e_zpowZMod] at h
  -- Extract modular congruence from zpow equality
  have h_mod : (a.val : ℤ) ≡ (b.val : ℤ) * (c.val : ℤ) [ZMOD (P.p : ℤ)] := by
    have := (zpow_eq_zpow_iff_modEq (x := P.e P.g₁ P.g₂)).mp h
    rwa [orderOf_eT] at this
  -- Convert Int.ModEq to ZMod equality
  have h_cast := (ZMod.intCast_eq_intCast_iff _ _ P.p).mpr h_mod
  -- Simplify casts: (↑a.val : ZMod p) = a, and (↑b.val * ↑c.val : ZMod p) = b * c
  push_cast at h_cast
  simp only [ZMod.natCast_zmod_val] at h_cast
  exact h_cast

/-! ## Algebraic Helpers -/

/-- When both representations are valid for `srs₁ α t`, the verification
    equation holds and y ≠ φ(z), the polynomial δ(X) = φ(X) - y - ψ(X) · (X - z)
    is nonzero, has α as a root, and has degree at most t + 1. -/
theorem knowledge_soundness_implies_root (α z y : ZMod P.p)
    (C_repr w_repr : AGMRepr P t)
    (heval : y ≠ (C_repr.toPoly).eval z)
    (hvalid : verify_eval P (srs₂ (P := P) α) C_repr.element z y w_repr.element)
    (hC : C_repr.Valid P t (srs₁ (P := P) α t))
    (hw : w_repr.Valid P t (srs₁ (P := P) α t)) :
    let φ := C_repr.toPoly
    let ψ := w_repr.toPoly
    let δ := φ - C y - ψ * (X - C z)
    δ ≠ 0 ∧ δ.IsRoot α ∧ δ.natDegree ≤ t + 1 := by
  set φ := C_repr.toPoly
  set ψ := w_repr.toPoly
  set δ := φ - C y - ψ * (X - C z)
  refine ⟨?_, ?_, ?_⟩
  · -- δ ≠ 0
    intro h_eq
    have h_delta_z : eval z φ - y = 0 := by simpa using congr_arg (eval z) h_eq
    exact heval (sub_eq_zero.mp h_delta_z).symm
  · -- δ.IsRoot α
    -- From AGM validity + verify_eval, we get φ(α) - y = ψ(α) · (α - z)
    unfold IsRoot
    simp only [eval_sub, eval_C, eval_mul, eval_X]
    have hC_eval : C_repr.element = P.g₁ ^ᵍ (φ.eval α) :=
      AGMRepr.element_eq_of_valid_srs₁ P t α C_repr hC
    have hw_eval : w_repr.element = P.g₁ ^ᵍ (ψ.eval α) :=
      AGMRepr.element_eq_of_valid_srs₁ P t α w_repr hw
    -- Now use verify_eval to extract the polynomial equation
    -- verify_eval: e(C * g₁^(-y), g₂) = e(w, vk.2 * g₂^(-z))
    -- With C = g₁^φ(α), w = g₁^ψ(α), vk.2 = g₂^α:
    -- e(g₁^(φ(α) - y), g₂) = e(g₁^ψ(α), g₂^(α - z))
    -- e(g₁, g₂)^(φ(α) - y) = e(g₁, g₂)^(ψ(α) · (α - z))
    -- Since e is non-degenerate, φ(α) - y = ψ(α) · (α - z)
    unfold verify_eval srs₂ at hvalid
    -- hvalid : e(C * g₁^(-y), g₂) = e(w, g₂^α * g₂^(-z))
    rw [hC_eval, hw_eval] at hvalid
    -- Now: e(g₁^(φ.eval α) * (g₁^y)⁻¹, g₂) = e(g₁^(ψ.eval α), g₂^α * (g₂^z)⁻¹)
    rw [← zpowZMod₁_sub, ← zpowZMod₂_sub] at hvalid
    -- Now: e(g₁^(φ.eval α - y), g₂) = e(g₁^(ψ.eval α), g₂^(α - z))
    exact sub_eq_zero.mpr (pairing_exponent_eq P (φ.eval α - y) (ψ.eval α) (α - z) hvalid)
  · -- deg(δ) ≤ t + 1
    calc δ.natDegree
      = (φ - C y - ψ * (X - C z)).natDegree := rfl
    _ ≤ max (φ - C y).natDegree (ψ * (X - C z)).natDegree :=
        natDegree_sub_le _ _
    _ ≤ max (max φ.natDegree (C y).natDegree) (ψ.natDegree + (X - C z).natDegree) := by
        gcongr
        · exact natDegree_sub_le _ _
        · exact natDegree_mul_le
    _ = max (max φ.natDegree 0) (ψ.natDegree + (X - C z).natDegree) := by
        simp [natDegree_C]
    _ = max φ.natDegree (ψ.natDegree + (X - C z).natDegree) := by
        simp
    _ ≤ max t (t + 1) := by
        gcongr
        · exact AGMRepr.toPoly_natDegree_le P t C_repr
        · exact AGMRepr.toPoly_natDegree_le P t w_repr
        · exact le_trans (natDegree_X_sub_C_le z) (by norm_num)
    _ = t + 1 := by omega

/-! ## Root Helpers (duplicated from PolyBinding since those are private) -/

/-- α ∈ roots(δ) implies α appears in roots.toList at some valid index. -/
theorem root_in_list (δ : Poly P) (α : ZMod P.p)
    (hne : δ ≠ 0) (hroot : δ.IsRoot α) :
    ∃ i : ℕ, i < δ.roots.toList.length ∧ (δ.roots.toList)[i]? = some α := by
  have hmem : α ∈ δ.roots := (mem_roots hne).mpr hroot
  rw [← Multiset.mem_toList] at hmem
  obtain ⟨i, hi, hval⟩ := List.mem_iff_getElem.mp hmem
  exact ⟨i, hi, List.getElem?_eq_getElem hi ▸ congr_arg some hval⟩

/-- roots.toList.length ≤ natDegree for nonzero polynomials. -/
theorem roots_list_length_le_deg (δ : Poly P) (_hne : δ ≠ 0) :
    δ.roots.toList.length ≤ δ.natDegree := by
  simpa using card_roots' δ

/-- When a root r of δ equals α, the tSDH check passes. -/
theorem tsdh_of_root_eq (α : ZMod P.p) :
    let c := if α = 0 then (1 : ZMod P.p) else 0
    let h := if α = 0 then P.g₁ else P.g₁ ^ᵍ α⁻¹
    P.e h (P.g₂ ^ʰ (α + c)) = P.e P.g₁ P.g₂ := by
  by_cases hα : α = 0
  · subst hα; simp only [ite_true]
    rw [show (0 : ZMod P.p) + 1 = 1 from zero_add 1, zpowZMod₂_eq_pow, ZMod.val_one, pow_one]
  · simp only [if_neg hα]
    rw [show α + (0 : ZMod P.p) = α from add_zero α, e_zpowZMod]
    rw [show (α⁻¹.val : ℤ) * (α.val : ℤ) = ((α⁻¹.val * α.val : ℕ) : ℤ) from by push_cast; ring]
    rw [zpow_natCast, eT_pow_mod, ← ZMod.val_mul, inv_mul_cancel₀ hα]
    simp [ZMod.val_one]

/-! ## Knowledge Soundness Theorem -/

/-- KZG is knowledge-sound in the AGM:
    any AGM adversary that breaks knowledge soundness can be used to break t-SDH.

    More precisely, the probability that an AGM adversary produces a valid
    evaluation proof for an incorrect value is bounded by `(t+1) × tSDH_Advantage`.

    The factor `t+1` (vs `t` in polynomial binding) comes from δ having degree ≤ t+1
    since δ(X) = φ(X) - y - ψ(X)·(X - z) involves the product ψ·(X - z). -/
theorem KZG_knowledge_sound (A : AGMAdversary P t) :
    prTrue (KnowledgeSoundness_Game_Full P t A) Heap.empty ≤
    (t + 1) * tSDH_Advantage P t (ks_to_tSDH P t A) := by
  -- Unfold both games to expose shared structure
  unfold tSDH_Advantage tSDH_Game ks_to_tSDH KnowledgeSoundness_Game_Full
  simp only [SPComp.monad_bind_eq, SPComp.bind_assoc]
  -- Apply scaled monotonicity over the α sample
  apply prTrue_bind_mono_const
  intro α h_α
  -- Apply scaled monotonicity over A's output
  apply prTrue_bind_mono_const
  intro out h_out
  -- Leaf comparison
  set C_repr := out.1
  set z := out.2.1
  set y := out.2.2.1
  set w_repr := out.2.2.2
  set φ := C_repr.toPoly
  set ψ := w_repr.toPoly
  set δ := φ - C y - ψ * (X - C z)
  by_cases hwin : C_repr.Valid P t (srs₁ (P := P) α t) ∧
      w_repr.Valid P t (srs₁ (P := P) α t) ∧
      verify_eval P (srs₂ (P := P) α) C_repr.element z y w_repr.element ∧ y ≠ φ.eval z
  · -- Winning case: LHS = 1
    rw [prTrue_pure_bool, if_pos (decide_eq_true hwin)]
    -- Goal: 1 ≤ (↑t + 1) * prTrue(sample >>= K) h_out
    obtain ⟨hC, hw, hvalid, heval⟩ := hwin
    obtain ⟨hδ_ne, hδ_root, hδ_deg⟩ :=
      knowledge_soundness_implies_root P t α z y C_repr w_repr heval hvalid hC hw
    obtain ⟨i₀, hi₀_lt, hi₀_eq⟩ := root_in_list P δ α hδ_ne hδ_root
    have hi₀_lt_t1 : i₀ < t + 1 :=
      lt_of_lt_of_le hi₀_lt (le_trans (roots_list_length_le_deg P δ hδ_ne) hδ_deg)
    have h_pos : (↑t + 1 : ℝ≥0∞) ≠ 0 := by positivity
    have h_top : (↑t + 1 : ℝ≥0∞) ≠ ⊤ := ENNReal.add_ne_top.mpr
      ⟨ENNReal.natCast_ne_top t, ENNReal.one_ne_top⟩
    -- Suffices: (↑t + 1)⁻¹ ≤ prTrue(sample >>= K) h_out
    -- Then 1 = (↑t + 1) * (↑t + 1)⁻¹ ≤ (↑t + 1) * prTrue(...)
    suffices h_inv : (↑t + 1 : ℝ≥0∞)⁻¹ ≤ prTrue _ h_out by
      calc (1 : ℝ≥0∞)
        = (↑t + 1) * (↑t + 1)⁻¹ := (ENNReal.mul_inv_cancel h_pos h_top).symm
        _ ≤ (↑t + 1) * prTrue _ h_out := by gcongr
    -- Lower bound by sampling witness ⟨i₀, hi₀_lt_t1⟩
    calc (↑t + 1 : ℝ≥0∞)⁻¹
      = (Fintype.card (Fin (t + 1)) : ℝ≥0∞)⁻¹ * 1 := by
          rw [Fintype.card_fin, Nat.cast_succ, mul_one]
      _ ≤ (Fintype.card (Fin (t + 1)) : ℝ≥0∞)⁻¹ * prTrue _ h_out := by
          gcongr
          -- Goal: 1 ≤ prTrue(K ⟨i₀, hi₀_lt_t1⟩) h_out
          -- K at i₀: match on roots[i₀] = some α, then tSDH check
          simp only [hi₀_eq]
          by_cases hα0 : α = 0
          · subst hα0
            simp only [ite_true, SPComp.pure_bind, prTrue_pure_bool]
            rw [show (0 : ZMod P.p) + (1 : ZMod P.p) = 1 from zero_add 1]
            rw [zpowZMod₂_eq_pow, ZMod.val_one, pow_one]
            simp
          · simp only [if_neg hα0, SPComp.pure_bind, prTrue_pure_bool]
            rw [show α + (0 : ZMod P.p) = α from add_zero α]
            have : P.e (P.g₁ ^ᵍ α⁻¹) (P.g₂ ^ʰ α) = P.e P.g₁ P.g₂ := by
              rw [e_zpowZMod]
              rw [show (α⁻¹.val : ℤ) * (α.val : ℤ) = ((α⁻¹.val * α.val : ℕ) : ℤ) from
                by push_cast; ring]
              rw [zpow_natCast, eT_pow_mod, ← ZMod.val_mul, inv_mul_cancel₀ hα0]
              simp [ZMod.val_one]
            simp [this]
      _ ≤ prTrue _ h_out :=
          prTrue_sample_bind_ge _ (⟨i₀, hi₀_lt_t1⟩ : Fin (t + 1)) h_out
  · -- Non-winning case: LHS = 0
    rw [prTrue_pure_bool]
    simp only [decide_eq_false_iff_not.mpr hwin]
    exact zero_le

/-! ## Honest Algebraic Adversary -/

/-- The honest committer's output on basis `pk`: the commitment to `φ` with the
    coefficients of `φ` as representation, the point `z`, the value `φ(z)`, and
    the witness commitment with the coefficients of `witnessPoly φ z` as
    representation. -/
noncomputable def honestAGMOutput (φ : Poly P) (z : ZMod P.p) (pk : Fin (t + 1) → P.G₁) :
    AGMRepr P t × ZMod P.p × ZMod P.p × AGMRepr P t :=
  (AGMRepr.ofCoeffs P t pk (fun i => φ.coeff i), z, φ.eval z,
    AGMRepr.ofCoeffs P t pk (fun i => (witnessPoly P φ z).coeff i))

/-- The honest committer as an AGM adversary. -/
noncomputable def honestAGMAdversary (φ : Poly P) (z : ZMod P.p) : AGMAdversary P t :=
  ⟨fun pk => SPComp.pure (honestAGMOutput P t φ z pk)⟩

/-- The honest commitment and witness elements are `commit` and `create_witness`. -/
theorem honestAGMOutput_elements (φ : Poly P) (z : ZMod P.p) (pk : Fin (t + 1) → P.G₁) :
    (honestAGMOutput P t φ z pk).1.element = commit P t pk φ ∧
      ((honestAGMOutput P t φ z pk).2.2.2.element, (honestAGMOutput P t φ z pk).2.2.1) =
        create_witness P t pk φ z :=
  ⟨rfl, rfl⟩

/-- Both honest representations pass the game's validity check for every basis. -/
theorem honestAGMOutput_valid (φ : Poly P) (z : ZMod P.p) (pk : Fin (t + 1) → P.G₁) :
    (honestAGMOutput P t φ z pk).1.Valid P t pk ∧
      (honestAGMOutput P t φ z pk).2.2.2.Valid P t pk :=
  ⟨AGMRepr.ofCoeffs_valid P t pk _, AGMRepr.ofCoeffs_valid P t pk _⟩

/-- The witness polynomial of a polynomial of degree at most `t` has degree at most `t`. -/
theorem witnessPoly_natDegree_le (φ : Poly P) (z : ZMod P.p) (hdeg : φ.natDegree ≤ t) :
    (witnessPoly P φ z).natDegree ≤ t := by
  unfold witnessPoly
  rw [natDegree_divByMonic _ (monic_X_sub_C z)]
  have h : (φ - C (φ.eval z)).natDegree ≤ t :=
    le_trans (natDegree_sub_le _ _) (max_le hdeg (by simp))
  omega

/-- For `φ` of degree at most `t`, the honest representations extract to `φ` and
    to `witnessPoly φ z`. -/
theorem honestAGMOutput_toPoly (φ : Poly P) (z : ZMod P.p) (pk : Fin (t + 1) → P.G₁)
    (hdeg : φ.natDegree ≤ t) :
    (honestAGMOutput P t φ z pk).1.toPoly = φ ∧
      (honestAGMOutput P t φ z pk).2.2.2.toPoly = witnessPoly P φ z :=
  ⟨AGMRepr.toPoly_ofCoeffs_coeff P t pk φ hdeg,
    AGMRepr.toPoly_ofCoeffs_coeff P t pk _ (witnessPoly_natDegree_le P t φ z hdeg)⟩

/-- For `φ` of degree at most `t`, the honest output on `srs₁ α t` passes the
    validity and pairing checks of `KnowledgeSoundness_Game_Full` and fails only
    the mismatch condition `y ≠ φ(z)`. -/
theorem honestAGMOutput_checks (φ : Poly P) (z α : ZMod P.p) (hdeg : φ.natDegree ≤ t) :
    let out := honestAGMOutput P t φ z (srs₁ (P := P) α t)
    out.1.Valid P t (srs₁ (P := P) α t) ∧ out.2.2.2.Valid P t (srs₁ (P := P) α t) ∧
      verify_eval P (srs₂ (P := P) α) out.1.element out.2.1 out.2.2.1 out.2.2.2.element ∧
      out.2.2.1 = out.1.toPoly.eval out.2.1 := by
  intro out
  obtain ⟨hC, hw⟩ := honestAGMOutput_valid P t φ z (srs₁ (P := P) α t)
  obtain ⟨hφ, hψ⟩ := honestAGMOutput_toPoly P t φ z (srs₁ (P := P) α t) hdeg
  refine ⟨hC, hw, ?_, ?_⟩
  · have hC_eval := AGMRepr.element_eq_of_valid_srs₁ P t α _ hC
    have hw_eval := AGMRepr.element_eq_of_valid_srs₁ P t α _ hw
    rw [hφ] at hC_eval
    rw [hψ] at hw_eval
    unfold verify_eval srs₂
    rw [hC_eval, hw_eval, ← zpowZMod₁_sub, ← zpowZMod₂_sub]
    have heval : φ.eval α - φ.eval z = (witnessPoly P φ z).eval α * (α - z) := by
      have h := congr_arg (Polynomial.eval α) (witnessPoly_spec P φ z)
      simp only [eval_mul, eval_sub, eval_X, eval_C] at h
      rw [mul_comm] at h
      exact h.symm
    show P.e (P.g₁ ^ᵍ (φ.eval α - φ.eval z)) P.g₂ =
      P.e (P.g₁ ^ᵍ (witnessPoly P φ z).eval α) (P.g₂ ^ʰ (α - z))
    rw [heval]
    exact e_zpowZMod_prod _ _
  · show φ.eval z = out.1.toPoly.eval z
    rw [hφ]

end CatCrypt.Examples.Commitments.KZG
