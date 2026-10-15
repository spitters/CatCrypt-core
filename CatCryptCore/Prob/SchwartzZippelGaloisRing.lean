/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Prob.SchwartzZippel
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Schwartz-Zippel over finite local rings with a principal nilpotent maximal ideal

Let `R` be a finite commutative ring with a surjective ring homomorphism `π : R →+* F` onto a
finite field whose kernel is the principal ideal `(t)`, with `t` nilpotent. Galois rings
`GR(p^k, d)` are of this form, with `t = p`. For a nonzero polynomial `f` over `R`, a uniformly
random point of `R` is a root of `f` with probability at most `deg f / |F|`.

The proof writes `f = t^s • g` with `s` maximal, so that some coefficient of `g` lies outside
`(t)`. Elements outside `(t)` are units, hence every root `x` of `f` is a root of `g`, and `π x`
is a root of the nonzero reduction `g.map π`. Each fibre of `π` has `|R| / |F|` elements.

## Main results

* `isUnit_of_not_mem_span_residue` — an element outside `(t)` is a unit.
* `exists_C_pow_mul_residue` — the factorisation `f = C (t^s) * g` with `g.map π ≠ 0`.
* `card_roots_mul_card_le_of_residue` — `#{x | f.eval x = 0} * |F| ≤ deg f * |R|`.
* `schwartz_zippel_of_residue` — `Pr[f(x) = 0] ≤ deg f / |F|`.
-/

@[expose] public section

namespace CatCrypt.Prob

open CatCrypt.Core CatCrypt.Crypto CatCrypt.Crypto.ForkingLemma
open Polynomial
open scoped ENNReal

variable {R F : Type} [CommRing R] [Field F]

/-- An element outside the kernel `(t)` of a surjection onto a field, with `t` nilpotent,
is a unit. -/
theorem isUnit_of_not_mem_span_residue (π : R →+* F) (hπ : Function.Surjective π) (t : R)
    (hker : RingHom.ker π = Ideal.span {t}) (k : ℕ) (htk : t ^ k = 0) {x : R}
    (hx : x ∉ Ideal.span {t}) : IsUnit x := by
  have hπx : π x ≠ 0 := by
    intro h; apply hx; rw [← hker]; exact h
  obtain ⟨y, hy⟩ := hπ (π x)⁻¹
  have hmem : x * y - 1 ∈ Ideal.span {t} := by
    rw [← hker, RingHom.mem_ker, map_sub, map_mul, hy, map_one, mul_inv_cancel₀ hπx, sub_self]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
  have hnil : IsNilpotent (a * t) := ⟨k, by rw [mul_pow, htk, mul_zero]⟩
  have hxy : x * y = 1 + a * t := by rw [ha]; ring
  exact isUnit_of_mul_isUnit_left (y := y) (by rw [hxy]; exact IsNilpotent.isUnit_one_add hnil)

/-- A nonzero polynomial over `R` factors as `C (t ^ s) * g` with `natDegree g ≤ natDegree f`
and with nonzero reduction of `g` modulo `(t)`. -/
theorem exists_C_pow_mul_residue (π : R →+* F) (t : R)
    (hker : RingHom.ker π = Ideal.span {t}) (k : ℕ) (htk : t ^ k = 0)
    (f : R[X]) (hf : f ≠ 0) :
    ∃ (s : ℕ) (g : R[X]),
      f = C (t ^ s) * g ∧ g.natDegree ≤ f.natDegree ∧ g.map π ≠ 0 := by
  classical
  let P : ℕ → Prop := fun s => ∀ i, f.coeff i ∈ Ideal.span {t ^ s}
  have hk : ¬ P k := by
    intro h; apply hf; ext i
    simpa [htk, Ideal.mem_span_singleton'] using h i
  have hex : ∃ n, ¬ P (n + 1) := ⟨k, fun h => hk fun i =>
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow t (Nat.le_succ k)) (h i)⟩
  have hPn : P (Nat.find hex) := by
    rcases hn : Nat.find hex with _ | m
    · intro i; simp
    · by_contra h
      exact Nat.find_min hex (show m < Nat.find hex by omega) h
  obtain ⟨j, hj⟩ := not_forall.mp (Nat.find_spec hex)
  set s := Nat.find hex
  choose c hc using fun i => Ideal.mem_span_singleton'.mp (hPn i)
  let g : R[X] := ∑ i ∈ f.support, monomial i (c i)
  have hgc : ∀ i, g.coeff i = if i ∈ f.support then c i else 0 := by
    intro i
    simp only [g, finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq']
  have hfg : f = C (t ^ s) * g := by
    ext i
    rw [coeff_C_mul, hgc]
    split_ifs with hi
    · rw [← hc i, mul_comm]
    · rw [mul_zero]; exact notMem_support_iff.mp hi
  refine ⟨s, g, hfg, ?_, ?_⟩
  · refine natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
    rw [hgc, if_neg]
    exact notMem_support_iff.mpr (coeff_eq_zero_of_natDegree_lt hN)
  · intro h0
    have hπj : π (g.coeff j) = 0 := by rw [← coeff_map, h0, coeff_zero]
    have hmem : g.coeff j ∈ Ideal.span {t} := by rw [← hker]; exact hπj
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hmem
    apply hj
    rw [hfg, coeff_C_mul, ← hb, Ideal.mem_span_singleton']
    exact ⟨b, by ring⟩

/-- Root counting: `#{x | f.eval x = 0} * |F| ≤ natDegree f * |R|` for nonzero `f`. -/
theorem card_roots_mul_card_le_of_residue [Fintype R] [DecidableEq R] [Fintype F]
    [DecidableEq F] (π : R →+* F) (hπ : Function.Surjective π) (t : R)
    (hker : RingHom.ker π = Ideal.span {t}) (k : ℕ) (htk : t ^ k = 0)
    (f : R[X]) (hf : f ≠ 0) :
    (Finset.univ.filter (fun x => f.eval x = 0)).card * Fintype.card F
      ≤ f.natDegree * Fintype.card R := by
  obtain ⟨s, g, hfg, hdeg, hg0⟩ := exists_C_pow_mul_residue π t hker k htk f hf
  set S := (g.map π).roots.toFinset
  set c := (Finset.univ.filter (fun x => π x = 0)).card
  have hfib : ∀ y : F, (Finset.univ.filter (fun x => π x = y)).card = c := fun y =>
    AddMonoidHom.card_fiber_eq_of_mem_range π (hπ y) ⟨0, map_zero π⟩
  have hmaps : ∀ x ∈ Finset.univ.filter (fun x => f.eval x = 0), π x ∈ S := by
    intro x hx
    rw [Finset.mem_filter] at hx
    have h0 : t ^ s * g.eval x = 0 := by
      rw [← eval_C (a := t ^ s) (x := x), ← eval_mul, ← hfg]; exact hx.2
    rw [Multiset.mem_toFinset, mem_roots hg0, IsRoot, eval_map, eval₂_at_apply]
    by_contra hne
    have hu : IsUnit (g.eval x) := isUnit_of_not_mem_span_residue π hπ t hker k htk
      (fun hm => hne (by rw [← hker] at hm; exact hm))
    apply hf
    rw [hfg, hu.mul_left_eq_zero.mp h0, map_zero, zero_mul]
  have hZ := Finset.card_le_mul_card_image_of_maps_to hmaps c fun y _ =>
    (Finset.card_le_card (Finset.monotone_filter_left _ (Finset.subset_univ _))).trans_eq (hfib y)
  have hS : S.card ≤ f.natDegree :=
    (Multiset.toFinset_card_le _).trans ((card_roots' _).trans ((natDegree_map_le).trans hdeg))
  have hR : Fintype.card R = Fintype.card F * c := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := π) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
    simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [hR]
  calc _ ≤ c * S.card * Fintype.card F := Nat.mul_le_mul_right _ hZ
    _ ≤ c * f.natDegree * Fintype.card F := by gcongr
    _ = f.natDegree * (Fintype.card F * c) := by ring

/-- Schwartz-Zippel over a finite ring `R` with a surjection `π` onto a finite field `F` whose
kernel is generated by a nilpotent `t`: a uniformly random point is a root of a nonzero `f` with
probability at most `natDegree f / |F|`. -/
theorem schwartz_zippel_of_residue [Fintype R] [DecidableEq R] [Fintype F] [DecidableEq F]
    (π : R →+* F) (hπ : Function.Surjective π) (t : R)
    (hker : RingHom.ker π = Ideal.span {t}) (k : ℕ) (htk : t ^ k = 0)
    (f : R[X]) (hf : f ≠ 0) :
    prTrue (do let x ← SPComp.sample R
               SPComp.pure (decide (f.eval x = 0))) Heap.empty
      ≤ (f.natDegree : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  rw [show prTrue (do let x ← SPComp.sample R
                      SPComp.pure (decide (f.eval x = 0))) Heap.empty =
        (Finset.univ.filter (fun x => decide (f.eval x = 0))).card /
          (Fintype.card R : ℝ≥0∞) from
      prTrue_sample_pure_bool (fun x => decide (f.eval x = 0)) Heap.empty]
  have h := card_roots_mul_card_le_of_residue π hπ t hker k htk f hf
  simp only [decide_eq_true_eq]
  have hF : (Fintype.card F : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine ENNReal.div_le_of_le_mul ?_
  rw [mul_comm, ← mul_div_assoc, mul_comm,
    ENNReal.le_div_iff_mul_le (Or.inl hF) (Or.inl (ENNReal.natCast_ne_top _))]
  exact_mod_cast h

end CatCrypt.Prob
