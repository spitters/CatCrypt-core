/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Examples.Commitments.KZG.Def
import CatCryptCore.Crypto.AGM
import CatCryptCore.Crypto.ForkingLemma
import Mathlib.Algebra.Field.ZMod

/-!
# KZG Knowledge Soundness in the AGM

This file proves knowledge soundness of KZG in the Algebraic Group Model:
any adversary that produces a valid evaluation proof must "know" the
committed polynomial (in the AGM sense).

## Main theorems

* `KZG_knowledge_sound` — Knowledge soundness advantage ≤ t-SDH advantage

## Proof outline

In the AGM, the adversary outputs:
- Commitment C with representation `[c₀, ..., cₜ]` (implying polynomial φ)
- Evaluation proof (z, y, w) with representation `[d₀, ..., dₜ]` (implying polynomial ψ)

The pairing verification equation forces:
  `φ(α) - y = ψ(α) · (α - z)` in the exponent

In the AGM, this is a polynomial identity `φ(X) - y = ψ(X) · (X - z)` modulo
a polynomial that vanishes at α. If this identity doesn't hold as polynomials,
we can extract a nontrivial polynomial with α as a root, which breaks t-SDH.

## References

* [Rothmann, Kreuzer — KZG_Knowledge_Soundness.thy in Isabelle]
* [Kate, Zaverucha, Goldberg, 2010 — Theorem 2 (informal)]
-/

namespace CatCrypt.Examples.Commitments.KZG

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open CatCrypt.Crypto.PairingGroup CatCrypt.Crypto.ForkingLemma
open Polynomial
open scoped ENNReal

variable (P : PairingGroup) (t : ℕ)

/-! ## Full Knowledge Soundness Game -/

/-- Full knowledge soundness game with verification check.

    Unlike the simplified game in AGM.lean, this version includes the pairing
    verification equation which is essential for establishing that δ(α) = 0.

    Adversary wins if:
    1. The evaluation proof verifies: `verify_eval vk C z y w`
    2. But the claimed value is wrong: `y ≠ φ(z)` where φ = extracted polynomial -/
noncomputable def KnowledgeSoundness_Game_Full (A : AGMAdversary P t) : SPComp Bool :=
  SPComp.bind (SPComp.sample (ZMod P.p)) fun α =>
  SPComp.bind (A.run (srs₁ (P := P) α t)) fun out =>
    let C_repr := out.1
    let z := out.2.1
    let y := out.2.2.1
    let w_repr := out.2.2.2
    let φ := C_repr.toPoly
    let vk := srs₂ (P := P) α
    -- Adversary wins if verification passes but evaluation is wrong
    SPComp.pure (decide (verify_eval P vk C_repr.element z y w_repr.element ∧ y ≠ φ.eval z))

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

/-- In the AGM, when the verification equation holds and y ≠ φ(z),
    the polynomial δ(X) = φ(X) - y - ψ(X) · (X - z) is nonzero but has α as a root.

    This lemma establishes the key algebraic property needed for the reduction:
    if the adversary wins the knowledge soundness game, we can extract a
    nontrivial polynomial with α as a root. -/
theorem knowledge_soundness_implies_root (α z y : ZMod P.p)
    (C_repr w_repr : AGMRepr P t)
    (heval : y ≠ (C_repr.toPoly).eval z)
    (hvalid : verify_eval P (srs₂ (P := P) α) C_repr.element z y w_repr.element) :
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
    -- Need to show: φ.eval α - y - (ψ.eval α * (α - z)) = 0
    -- This follows from the pairing equation
    have hC_eval : C_repr.element = P.g₁ ^ᵍ (φ.eval α) := by
      have := C_repr.valid (srs₁ (P := P) α t)
      unfold srs₁ at this
      rw [this]
      -- Goal: ∏ i, (g₁ ^ᵍ (α ^ i)) ^ᵍ (C_repr.coeffs i) = g₁ ^ᵍ (φ.eval α)
      simp_rw [zpowZMod₁_zpowZMod₁, mul_comm (α ^ _)]
      rw [zpowZMod₁_finprod_univ]
      congr 1
      -- Show ∑ i, coeffs i * α^i = φ.eval α
      calc ∑ i : Fin (t + 1), C_repr.coeffs i * α ^ i.val
        _ = (∑ i : Fin (t + 1), C (C_repr.coeffs i) * X ^ i.val).eval α := by
            simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
                       Polynomial.eval_pow, Polynomial.eval_X]
        _ = φ.eval α := rfl
    have hw_eval : w_repr.element = P.g₁ ^ᵍ (ψ.eval α) := by
      have := w_repr.valid (srs₁ (P := P) α t)
      unfold srs₁ at this
      rw [this]
      simp_rw [zpowZMod₁_zpowZMod₁, mul_comm (α ^ _)]
      rw [zpowZMod₁_finprod_univ]
      congr 1
      -- Show ∑ i, coeffs i * α^i = ψ.eval α
      calc ∑ i : Fin (t + 1), w_repr.coeffs i * α ^ i.val
        _ = (∑ i : Fin (t + 1), C (w_repr.coeffs i) * X ^ i.val).eval α := by
            simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
                       Polynomial.eval_pow, Polynomial.eval_X]
        _ = ψ.eval α := rfl
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
  by_cases hwin : verify_eval P (srs₂ (P := P) α) C_repr.element z y w_repr.element ∧ y ≠ φ.eval z
  · -- Winning case: LHS = 1
    rw [prTrue_pure_bool, if_pos (decide_eq_true hwin)]
    -- Goal: 1 ≤ (↑t + 1) * prTrue(sample >>= K) h_out
    obtain ⟨hvalid, heval⟩ := hwin
    obtain ⟨hδ_ne, hδ_root, hδ_deg⟩ :=
      knowledge_soundness_implies_root P t α z y C_repr w_repr heval hvalid
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

end CatCrypt.Examples.Commitments.KZG
