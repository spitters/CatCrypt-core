/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Relational.Approx

/-!
# Approximate couplings with a point mass

A subdistribution whose mass on the elements related to `b` is at least `1 - ε` is related to the
point mass at `b` at grade `ε`. The graded relational judgment against `pure b` follows at equal
initial heaps.

## Main results

* `CatCrypt.Prob.liftRApprox_pure_right_of_mass` — the graded sub-coupling with a point mass from a
  bound on the mass outside the relation.
* `CatCrypt.Relational.rHoareApprox_pure_right_of_mass` — the graded judgment of a computation
  against `pure b` from the same bound at every initial heap.

## Search words

approximate coupling, point mass, sub-coupling, graded relational Hoare logic, mass bound
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Prob

open scoped ENNReal

variable {α β : Type}

open Classical in
/-- **A sub-coupling with a point mass.** When the mass of `d` on the elements related to `b` is
    at least `1 - ε`, `d` and the point mass at `b` are related at grade `ε`. -/
theorem liftRApprox_pure_right_of_mass {d : SDistr α} {b : β} {R : α → β → Prop} {ε : ℝ≥0∞}
    (h : 1 - ∑' a, (if R a b then d (some a) else 0) ≤ ε) :
    liftRApprox ε R d (SDistr.pure b) := by
  set M := ∑' a, (if R a b then d (some a) else 0) with hM
  set w : SDistr (α × β) := d.bind fun x => if R x b then SDistr.pure (x, b) else SDistr.fail
  have hjoint : ∀ a b', w (some (a, b')) = if R a b ∧ b' = b then d (some a) else 0 := by
    intro a b'
    rw [SDistr.bind_apply_some, tsum_eq_single a]
    · by_cases hb : b' = b
      · subst hb; by_cases hR : R a b' <;> simp [hR, SDistr.pure_apply_some, SDistr.fail_apply_some]
      · by_cases hR : R a b <;>
          simp [hR, hb, Ne.symm hb, SDistr.pure_apply_some, SDistr.fail_apply_some]
    · intro x hx
      by_cases hR : R x b <;> simp [hR, SDistr.pure_apply_some, SDistr.fail_apply_some, hx]
  have hrow : ∀ a, ∑' b', w (some (a, b')) = if R a b then d (some a) else 0 := by
    intro a
    simp_rw [hjoint]
    rw [tsum_eq_single b fun b' hb => by simp [hb]]
    simp
  have hcol : ∀ b', ∑' a, w (some (a, b')) = if b' = b then M else 0 := by
    intro b'
    simp_rw [hjoint]
    by_cases hb : b' = b <;> simp [hb, hM]
  have htot : ∑' a, d (some a) ≤ 1 := by
    have hone : d none + ∑' a, d (some a) = 1 := by
      rw [← SDistr.tsum_option_eq_add]; exact d.tsum_coe
    exact hone ▸ le_add_self
  have hM1 : M ≤ 1 :=
    (ENNReal.tsum_le_tsum fun a => by split_ifs <;> simp).trans htot
  have hsplit : ∑' a, (d (some a) - if R a b then d (some a) else 0) + M =
      ∑' a, d (some a) := by
    rw [hM, ← ENNReal.tsum_add]
    exact tsum_congr fun a => by split_ifs <;> simp
  refine ⟨⟨w, fun a => ?_, fun b' => ?_, ?_, ?_⟩, ?_⟩
  · rw [hrow]; split_ifs <;> simp
  · rw [hcol]; split_ifs with hb <;> simp [hb, SDistr.pure_apply_some, hM1]
  · simp_rw [hrow]
    refine le_trans ?_ h
    refine ENNReal.le_sub_of_add_le_right (ne_top_of_le_ne_top ENNReal.one_ne_top hM1) ?_
    exact hsplit ▸ htot
  · simp_rw [hcol]
    rw [tsum_eq_single b fun b' hb => by simp [hb, SDistr.pure_apply_some, Ne.symm hb]]
    simpa [SDistr.pure_apply_some] using h
  · intro a b' hw
    rw [hjoint] at hw
    grind

end CatCrypt.Prob

namespace CatCrypt.Relational

open CatCrypt.Core CatCrypt.Prob
open scoped ENNReal

variable {α β : Type}

/-- **A graded judgment against a point mass.** When, at every initial heap `s`, the mass of
    `c s` on the pairs related to `(b, s)` by `Ψ` is at least `1 - ε`, `c` and `pure b` are
    related at grade `ε` at equal initial heaps. -/
theorem rHoareApprox_pure_right_of_mass {c : SPComp α} {b : β} {Ψ : RPost α β} {ε : ℝ≥0∞}
    (h : ∀ s, 1 - ∑' p : α × Heap,
      (open Classical in if Ψ p.1 p.2 b s then c s (some p) else 0) ≤ ε) :
    rHoareApprox ε eqPre c (SPComp.pure b) Ψ := by
  rintro s s' (rfl : s = s')
  exact liftRApprox_pure_right_of_mass (R := fun (p : α × Heap) (q : β × Heap) => Ψ p.1 p.2 q.1 q.2)
    (h s)

end CatCrypt.Relational
