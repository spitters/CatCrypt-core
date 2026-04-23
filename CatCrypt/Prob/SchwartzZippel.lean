/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Core.Code
import CatCrypt.Prob.SDistr
import CatCrypt.Crypto.Advantage
import CatCrypt.Crypto.ForkingLemma
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic

/-!
# Schwartz-Zippel Lemma

This file proves the Schwartz-Zippel lemma over finite fields:
for a non-zero polynomial φ over ZMod p, a uniformly random point
is a root with probability at most deg(φ) / p.

## Main theorem

* `schwartz_zippel` — Pr[φ(x) = 0] ≤ deg(φ) / p for φ ≠ 0

## Application

Used in KZGBatch binding proof: if the adversary outputs inconsistent
openings, we extract a non-zero polynomial δ with δ(α) = 0. By
Schwartz-Zippel, this happens with probability at most deg(δ) / p.

## References

* [Schwartz 1980, Zippel 1979 — Probabilistic algorithms for sparse polynomials]
* [Mitzenmacher-Upfal, *Probability and Computing*, §7.2]
-/

namespace CatCrypt.Prob

open CatCrypt.Core CatCrypt.Crypto CatCrypt.Crypto.ForkingLemma
open Polynomial
open scoped ENNReal

variable (p : ℕ) [Fact (Nat.Prime p)]

/-! ## Schwartz-Zippel Lemma -/

/-- The Schwartz-Zippel lemma: for a non-zero polynomial φ over ZMod p,
    a uniformly random point is a root with probability at most deg(φ) / p.

    **Proof outline**:
    1. Use `prTrue_sample_pure_bool` to convert probability to fraction
    2. Bound the number of roots using Polynomial.card_roots'
    3. Divide by p to get the bound -/
theorem schwartz_zippel (φ : Polynomial (ZMod p)) (hφ : φ ≠ 0) :
    prTrue (do let x ← SPComp.sample (ZMod p)
               SPComp.pure (decide (φ.eval x = 0))) Heap.empty
    ≤ (φ.natDegree : ℝ≥0∞) / (p : ℝ≥0∞) := by
  -- Step 1: Use prTrue_sample_pure_bool to convert to cardinality
  have h1 : prTrue (do let x ← SPComp.sample (ZMod p)
                       SPComp.pure (decide (φ.eval x = 0))) Heap.empty =
            (Finset.univ.filter (fun x => decide (φ.eval x = 0))).card /
            (Fintype.card (ZMod p) : ℝ≥0∞) := by
    exact prTrue_sample_pure_bool (fun x => decide (φ.eval x = 0)) Heap.empty
  rw [h1]
  -- Step 2: Show Fintype.card (ZMod p) = p
  have h2 : Fintype.card (ZMod p) = p := ZMod.card p
  rw [h2]
  -- Step 3: Bound the filter cardinality and divide both sides by p
  have h3 : (Finset.univ.filter (fun x => decide (φ.eval x = 0))).card ≤ φ.natDegree := by
    -- The filter counts points where φ evaluates to 0
    -- This is bounded by the number of roots, which is ≤ degree
    have h_subset : Finset.univ.filter (fun x => decide (φ.eval x = 0)) ⊆
                    φ.roots.toFinset := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hx
      rw [Multiset.mem_toFinset]
      rw [Polynomial.mem_roots hφ]
      exact hx
    calc (Finset.univ.filter (fun x => decide (φ.eval x = 0))).card
      _ ≤ φ.roots.toFinset.card := Finset.card_le_card h_subset
      _ ≤ φ.roots.card := Multiset.toFinset_card_le φ.roots
      _ ≤ φ.natDegree := Polynomial.card_roots' φ
  gcongr

/-! ## Corollary: Polynomial Identity Testing -/

/-- Polynomial identity testing (direct corollary of Schwartz-Zippel):
    for distinct polynomials φ ≠ ψ over ZMod p, a uniformly random point
    satisfies φ(x) = ψ(x) with probability at most max(deg φ, deg ψ) / p.

    Proof: apply `schwartz_zippel` to the nonzero polynomial φ - ψ, then
    use `natDegree_add_le` + `natDegree_neg` to bound its degree. -/
theorem poly_identity_test (φ ψ : Polynomial (ZMod p)) (hne : φ ≠ ψ) :
    prTrue (do let x ← SPComp.sample (ZMod p)
               SPComp.pure (decide (φ.eval x = ψ.eval x))) Heap.empty
    ≤ (max φ.natDegree ψ.natDegree : ℝ≥0∞) / (p : ℝ≥0∞) := by
  -- Rewrite: decide (φ.eval x = ψ.eval x) ↔ decide ((φ - ψ).eval x = 0)
  have h_eq : ∀ x : ZMod p,
      decide (φ.eval x = ψ.eval x) = decide ((φ - ψ).eval x = 0) := by
    intro x; congr 1; rw [eval_sub, sub_eq_zero]
  simp_rw [h_eq]
  -- Apply Schwartz-Zippel to φ - ψ
  have h_sub_ne : φ - ψ ≠ 0 := sub_ne_zero_of_ne hne
  calc prTrue (do let x ← SPComp.sample (ZMod p)
                  SPComp.pure (decide ((φ - ψ).eval x = 0))) Heap.empty
    _ ≤ ((φ - ψ).natDegree : ℝ≥0∞) / (p : ℝ≥0∞) := schwartz_zippel p (φ - ψ) h_sub_ne
    _ ≤ (max φ.natDegree ψ.natDegree : ℝ≥0∞) / (p : ℝ≥0∞) := by
        gcongr
        -- Goal: ↑(φ - ψ).natDegree ≤ max ↑φ.natDegree ↑ψ.natDegree
        have h_deg : (φ - ψ).natDegree ≤ max φ.natDegree ψ.natDegree :=
          calc (φ - ψ).natDegree = (φ + (-ψ)).natDegree := by rw [sub_eq_add_neg]
            _ ≤ max φ.natDegree (-ψ).natDegree := natDegree_add_le φ (-ψ)
            _ = max φ.natDegree ψ.natDegree := by rw [natDegree_neg]
        rcases le_max_iff.mp h_deg with h | h
        · exact le_trans (Nat.cast_le.mpr h) (le_max_left _ _)
        · exact le_trans (Nat.cast_le.mpr h) (le_max_right _ _)

end CatCrypt.Prob
