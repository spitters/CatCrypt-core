/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.PFunctorChargeUnder
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Vector charges, prices and simulation under allowed answers

A charge `c : P.A → ι → R` with values in the pointwise lattice `ι → R` counts one resource per
index `i`. Since suprema and sums in `ι → R` are pointwise, the component `i` of the charge fold
is the scalar charge fold at `fun a => c a i`, and a vector bound is the family of its component
bounds. Pricing the components by `p : ι → ℕ∞` turns a vector bound `u` into the scalar bound
`∑ i, p i * u i` on the fold at the priced charge `fun a => ∑ i, p i * c a i`.

A program simulated through a handler whose allowed returns at `a` satisfy `allowsP a` costs, under
the answers allowed by `allows`, at most the program read under `allowsP` with each call at `a`
charged the handler's worst-case cost at `a`.

## Main results

* `PFunctor.FreeM.wpFold_chargeUnder_pi_apply` — the component `i` of a vector charge fold is
  the scalar charge fold at the component `i` of the charge
* `PFunctor.FreeM.wpFold_chargeUnder_pi_le_iff` — a vector bound on the charge fold is the family
  of its component bounds
* `PFunctor.FreeM.wpFold_chargeUnder_price_le` — a vector bound `u` gives the scalar bound
  `∑ i, p i * u i` on the fold at the priced charge
* `PFunctor.FreeM.wpFold_charge_price_le` — the same with every answer allowed
* `PFunctor.FreeM.wpFold_chargeUnder_liftM_le` — simulation overhead under allowed answers
-/

@[expose] public section

set_option autoImplicit false

universe uA uB uA₂ v w

open scoped BigOperators

namespace PFunctor

namespace FreeM

variable {P : PFunctor.{uA, uB}}

section Vector

variable {α : Type v}

/-- The component `i` of the charge fold at a vector charge is the charge fold at the component
`i` of the charge, with the component `i` of the postcondition. -/
theorem wpFold_chargeUnder_pi_apply {ι : Type*} {R : Type w} [CompleteLattice R] [Add R]
    (c : P.A → ι → R) (allows : (a : P.A) → P.B a → Prop) (x : FreeM P α) (post : α → ι → R)
    (i : ι) :
    wpFold (OpSpec.chargeUnder c allows) x post i =
      wpFold (OpSpec.chargeUnder (fun a => c a i) allows) x (fun r => post r i) := by
  induction x with
  | pure r => rfl
  | lift_bind a r ih =>
    change (c a + ⨆ b, ⨆ (_ : allows a b), wpFold (OpSpec.chargeUnder c allows) (r b) post) i =
      c a i + ⨆ b, ⨆ (_ : allows a b),
        wpFold (OpSpec.chargeUnder (fun a => c a i) allows) (r b) (fun r => post r i)
    simp only [Pi.add_apply, iSup_apply, ih]

/-- A vector bound on the charge fold is the family of the component bounds, each a bound on the
scalar charge fold at the component of the charge. -/
theorem wpFold_chargeUnder_pi_le_iff {ι : Type*} {R : Type w} [CompleteLattice R] [Add R]
    (c : P.A → ι → R) (allows : (a : P.A) → P.B a → Prop) (x : FreeM P α) (post : α → ι → R)
    (u : ι → R) :
    wpFold (OpSpec.chargeUnder c allows) x post ≤ u ↔
      ∀ i, wpFold (OpSpec.chargeUnder (fun a => c a i) allows) x (fun r => post r i) ≤ u i := by
  simp only [Pi.le_def, wpFold_chargeUnder_pi_apply]

/-- The fold at a priced charge is at most the priced vector fold: at the price `p`, the charge
`fun a => ∑ i, p i * c a i` folds to at most `∑ i, p i * (fold at c) i`. -/
theorem wpFold_chargeUnder_price_le_sum {ι : Type*} [Fintype ι] (c : P.A → ι → ℕ∞)
    (allows : (a : P.A) → P.B a → Prop) (p : ι → ℕ∞) (x : FreeM P α) (post : α → ι → ℕ∞) :
    wpFold (OpSpec.chargeUnder (fun a => ∑ i, p i * c a i) allows) x
        (fun r => ∑ i, p i * post r i) ≤
      ∑ i, p i * wpFold (OpSpec.chargeUnder c allows) x post i := by
  induction x with
  | pure r => exact le_rfl
  | lift_bind a r ih =>
    change (∑ i, p i * c a i) + ⨆ b, ⨆ (_ : allows a b),
        wpFold (OpSpec.chargeUnder (fun a => ∑ i, p i * c a i) allows) (r b)
          (fun r => ∑ i, p i * post r i) ≤
      ∑ i, p i * (c a + ⨆ b, ⨆ (_ : allows a b),
        wpFold (OpSpec.chargeUnder c allows) (r b) post) i
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    refine add_le_add le_rfl (iSup₂_le fun b hb => (ih b).trans ?_)
    refine Finset.sum_le_sum fun i _ => mul_le_mul_right ?_ (p i)
    exact le_iSup₂_of_le (f := fun b (_ : allows a b) =>
      wpFold (OpSpec.chargeUnder c allows) (r b) post) b hb le_rfl i

/-- **Pricing a vector bound.** If the charge fold at the vector charge `c` is at most `u`, then
at every price `p` the charge fold at `fun a => ∑ i, p i * c a i` is at most
`∑ i, p i * u i`. -/
theorem wpFold_chargeUnder_price_le {ι : Type*} [Fintype ι] (c : P.A → ι → ℕ∞)
    (allows : (a : P.A) → P.B a → Prop) (p : ι → ℕ∞) {x : FreeM P α} {u : ι → ℕ∞}
    (hu : wpFold (OpSpec.chargeUnder c allows) x (fun _ => 0) ≤ u) :
    wpFold (OpSpec.chargeUnder (fun a => ∑ i, p i * c a i) allows) x (fun _ => 0) ≤
      ∑ i, p i * u i := by
  have h := wpFold_chargeUnder_price_le_sum c allows p x (fun _ => 0)
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h
  exact h.trans (Finset.sum_le_sum fun i _ => mul_le_mul_right (hu i) (p i))

/-- **Pricing a vector bound**, with every answer allowed. -/
theorem wpFold_charge_price_le {ι : Type*} [Fintype ι] (c : P.A → ι → ℕ∞) (p : ι → ℕ∞)
    {x : FreeM P α} {u : ι → ℕ∞} (hu : wpFold (OpSpec.charge c) x (fun _ => 0) ≤ u) :
    wpFold (OpSpec.charge fun a => ∑ i, p i * c a i) x (fun _ => 0) ≤ ∑ i, p i * u i := by
  rw [← OpSpec.chargeUnder_true] at hu ⊢
  exact wpFold_chargeUnder_price_le c _ p hu

end Vector

section Simulation

variable {α : Type uB}

/-- **Simulation overhead under allowed answers.** If every return of the handler at `a` allowed
by `allows` satisfies `allowsP a`, a program simulated through the handler costs, under
`allows`, at most the program read under `allowsP` with each call at `a` charged the handler's
worst-case cost at `a` under `allows`. -/
theorem wpFold_chargeUnder_liftM_le {Q : PFunctor.{uA₂, uB}} (c : Q.A → ℕ∞)
    (allows : (a : Q.A) → Q.B a → Prop) (allowsP : (a : P.A) → P.B a → Prop)
    (handler : (a : P.A) → FreeM Q (P.B a))
    (hhandler : ∀ a, wpFold (OpSpec.demonicUnder allows) (handler a) (allowsP a))
    (x : FreeM P α) :
    wpFold (OpSpec.chargeUnder c allows) (x.liftM handler) (fun _ => 0) ≤
      wpFold (OpSpec.chargeUnder
        (fun a => wpFold (OpSpec.chargeUnder c allows) (handler a) fun _ => 0) allowsP)
        x (fun _ => 0) := by
  rw [wpFold_liftM]
  induction x with
  | pure r => exact le_rfl
  | lift_bind a r ih =>
    change wpFold (OpSpec.chargeUnder c allows) (handler a)
        (fun u => wpFold ((OpSpec.chargeUnder c allows).pullback handler) (r u) _) ≤
      wpFold (OpSpec.chargeUnder c allows) (handler a) (fun _ => 0) + ⨆ b, ⨆ (_ : allowsP a b),
        wpFold (OpSpec.chargeUnder
          (fun a => wpFold (OpSpec.chargeUnder c allows) (handler a) fun _ => 0) allowsP)
          (r b) (fun _ => 0)
    refine wpFold_chargeUnder_le_add_of_demonicUnder c allows (hhandler a) fun b hb => ?_
    exact (ih b).trans (le_iSup₂_of_le (f := fun b (_ : allowsP a b) =>
      wpFold (OpSpec.chargeUnder
        (fun a => wpFold (OpSpec.chargeUnder c allows) (handler a) fun _ => 0) allowsP)
        (r b) (fun _ => 0)) b hb le_rfl)

end Simulation

end FreeM

end PFunctor
