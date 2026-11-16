/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Uniform samples span a finite vector space with high probability

Let `V` be a vector space over a finite field `K` with `q = |K|`. Among the `|V|ᵐ` tuples
`v : Fin m → V`, those whose entries do not span `V` number at most `|V|ᵐ · |V| / qᵐ`. So
`m` independent uniform samples span `V` with probability at least `1 - |V| / qᵐ`, which for
`K = 𝔽₂` and `dim V = d` is `1 - 2^{d-m}`.

The proof is a union bound over hyperplanes: a tuple that does not span `V` lies in the kernel
of a nonzero linear functional `φ` (`Submodule.exists_le_ker_of_lt_top`); the kernel of `φ` has
`|V| / q` elements, so `φ` vanishes on all entries of `(|V| / q)ᵐ` tuples, and there are fewer
than `|V|` nonzero functionals. This is the counting step of Simon's algorithm (Simon 1994;
Nielsen–Chuang, Section 5.4.3 and Appendix 2).

## Main results

* `Module.card_ker_mul_card` — `|ker φ| · q = |V|` for a nonzero functional `φ`.
* `Module.card_not_span_mul_pow_le` — `#{v | span (range v) ≠ ⊤} · qᵐ ≤ |V| · |V|ᵐ`.
* `Module.one_sub_le_card_span_div` — the spanning probability is at least `1 - |V| / qᵐ`.
* `Submodule.card_not_span_mul_two_pow_le` — for a subspace `W` of `Fin n → ZMod 2` of
  dimension `d`, `#{v : Fin m → W | span (range v) ≠ ⊤} · 2ᵐ ≤ 2ᵈ · 2^{dm}`.
-/

@[expose] public section

set_option autoImplicit false

open Module

namespace Module

variable {K V : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Fintype V]

/-- The kernel of a nonzero linear functional on a finite vector space has `|V| / |K|`
elements. -/
theorem card_ker_mul_card {φ : Module.Dual K V} (hφ : φ ≠ 0) :
    Nat.card (LinearMap.ker φ) * Fintype.card K = Fintype.card V := by
  have hsurj : Function.Surjective φ := by
    obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
      by_contra h
      push Not at h
      exact hφ (LinearMap.ext h)
    intro c
    exact ⟨(c / φ v) • v, by simp [hv]⟩
  have hrange : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hdim := LinearMap.finrank_range_add_finrank_ker φ
  rw [hrange, finrank_top, Module.finrank_self] at hdim
  rw [Module.natCard_eq_pow_finrank (K := K) (V := LinearMap.ker φ),
    Module.card_eq_pow_finrank (K := K) (V := V), ← hdim, pow_add, pow_one, mul_comm,
    Nat.card_eq_fintype_card]

/-- **Union bound over hyperplanes.** The tuples `v : Fin m → V` whose entries do not span `V`
number at most `|V| · |V|ᵐ / qᵐ`. -/
theorem card_not_span_mul_pow_le (m : ℕ) :
    (Finset.univ.filter fun v : Fin m → V => Submodule.span K (Set.range v) ≠ ⊤).card *
        Fintype.card K ^ m ≤ Fintype.card V * Fintype.card (Fin m → V) := by
  classical
  let e : V ≃ₗ[K] Module.Dual K V := (Module.Free.chooseBasis K V).toDualEquiv
  have hsub : (Finset.univ.filter fun v : Fin m → V => Submodule.span K (Set.range v) ≠ ⊤) ⊆
      (Finset.univ.filter fun w : V => w ≠ 0).biUnion fun w =>
        Fintype.piFinset fun _ : Fin m => Finset.univ.filter fun x : V => e w x = 0 := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨φ, hφ0, hle⟩ := (Submodule.span K (Set.range v)).exists_le_ker_of_lt_top
      (lt_top_iff_ne_top.mpr hv)
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      Fintype.mem_piFinset]
    refine ⟨e.symm φ, by simpa using hφ0, fun i => ?_⟩
    simp only [LinearEquiv.apply_symm_apply]
    exact hle (Submodule.subset_span ⟨i, rfl⟩)
  have hcard : ∀ w : V, w ≠ 0 →
      (Fintype.piFinset fun _ : Fin m => Finset.univ.filter fun x : V => e w x = 0).card *
        Fintype.card K ^ m = Fintype.card V ^ m := by
    intro w hw
    have hk := card_ker_mul_card (K := K) (V := V) (φ := e w) (by simpa using hw)
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← mul_pow, ← hk]
    congr 2
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    rfl
  calc (Finset.univ.filter fun v : Fin m → V => Submodule.span K (Set.range v) ≠ ⊤).card *
        Fintype.card K ^ m
      ≤ (∑ w ∈ Finset.univ.filter fun w : V => w ≠ 0,
          (Fintype.piFinset fun _ : Fin m => Finset.univ.filter fun x : V => e w x = 0).card) *
          Fintype.card K ^ m :=
        Nat.mul_le_mul_right _ ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)
    _ = ∑ w ∈ Finset.univ.filter fun w : V => w ≠ 0, Fintype.card V ^ m := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun w hw => hcard w (by simpa using hw)
    _ ≤ ∑ _w : V, Fintype.card V ^ m :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = Fintype.card V * Fintype.card (Fin m → V) := by
        simp [Finset.sum_const]

/-- **Uniform samples span with high probability.** `m` independent uniform samples from `V`
span `V` with probability at least `1 - |V| / qᵐ`. -/
theorem one_sub_le_card_span_div (m : ℕ) :
    1 - (Fintype.card V : ℝ) / Fintype.card K ^ m ≤
      ((Finset.univ.filter fun v : Fin m → V => Submodule.span K (Set.range v) = ⊤).card : ℝ) /
        Fintype.card (Fin m → V) := by
  classical
  have hb := card_not_span_mul_pow_le (K := K) (V := V) m
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m → V))) fun v => Submodule.span K (Set.range v) = ⊤
  have hN : (0 : ℝ) < Fintype.card (Fin m → V) := by exact_mod_cast Fintype.card_pos
  have hq : (0 : ℝ) < Fintype.card K ^ m := by positivity
  rw [Finset.card_univ] at hsplit
  have hb' : ((Finset.univ.filter fun v : Fin m → V =>
      ¬ Submodule.span K (Set.range v) = ⊤).card : ℝ) * Fintype.card K ^ m ≤
      Fintype.card V * Fintype.card (Fin m → V) := by exact_mod_cast hb
  have hs' : ((Finset.univ.filter fun v : Fin m → V =>
      Submodule.span K (Set.range v) = ⊤).card : ℝ) + (Finset.univ.filter fun v : Fin m → V =>
      ¬ Submodule.span K (Set.range v) = ⊤).card = Fintype.card (Fin m → V) := by
    exact_mod_cast hsplit
  rw [sub_le_iff_le_add, div_add_div _ _ hN.ne' hq.ne', le_div_iff₀ (by positivity)]
  nlinarith

end Module

namespace Submodule

open Classical in
/-- **Counting step of Simon's algorithm.** For a subspace `W` of `Fin n → ZMod 2` of dimension
`d`, the tuples of `m` vectors of `W` that do not span `W` number at most `2ᵈ · 2^{dm} / 2ᵐ`;
`m` uniform samples from `W` span `W` with probability at least `1 - 2^{d-m}`. -/
theorem card_not_span_mul_two_pow_le {n : ℕ} (W : Submodule (ZMod 2) (Fin n → ZMod 2))
    (m : ℕ) :
    (Finset.univ.filter fun v : Fin m → W => Submodule.span (ZMod 2) (Set.range v) ≠ ⊤).card *
        2 ^ m ≤ 2 ^ finrank (ZMod 2) W * 2 ^ (finrank (ZMod 2) W * m) := by
  have h := Module.card_not_span_mul_pow_le (K := ZMod 2) (V := W) m
  rw [Fintype.card_fun, Fintype.card_fin, Module.card_eq_pow_finrank (K := ZMod 2) (V := W),
    ZMod.card, ← pow_mul] at h
  exact h

end Submodule
