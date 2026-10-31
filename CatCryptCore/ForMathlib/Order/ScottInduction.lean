/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Order.FixedPoints

/-!
# Scott induction in ω-complete partial orders

Scott induction (fixed-point induction) proves a property of a least fixed point, or of the
supremum of the iterates of a map, from the property at the start of the iteration, its
preservation by the map, and admissibility: an admissible predicate holds at the supremum of
every chain all of whose elements satisfy it.

## Main definitions

* `OmegaCompletePartialOrder.Admissible`: the admissible predicates of an ω-complete partial
  order (closed under suprema of chains).

## Main results

* `OmegaCompletePartialOrder.Admissible.and`, `Admissible.forall_`, `Admissible.comp`,
  `Admissible.apply`, `Admissible.le`, `Admissible.le_const`, `Admissible.eq`: admissibility of
  conjunctions, universal quantifications, preimages under ω-Scott-continuous maps,
  evaluations of functions, inequalities `f x ≤ g x` with `f` continuous and `g` monotone, and
  equations between continuous maps.
* `OmegaCompletePartialOrder.ωSup_induction`: Scott induction along a chain whose successors are
  the images of its elements under a map.
* `OmegaCompletePartialOrder.ωSup_iterateChain_induction`: Scott induction for the supremum of
  the iterates of a monotone map.
* `OrderHom.lfp_scott_induction`: Scott induction for the least fixed point of an
  ω-Scott-continuous map on a complete lattice, from the property at `⊥`.

Mathlib's `OrderHom.lfp_induction` asks for closure under arbitrary suprema and no continuity;
the statements here ask only for suprema of chains.
-/

@[expose] public section

set_option autoImplicit false

namespace OmegaCompletePartialOrder

variable {α β : Type*} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]

/-- A predicate on an ω-complete partial order is admissible when it holds at the supremum of
every chain all of whose elements satisfy it. -/
def Admissible (P : α → Prop) : Prop :=
  ∀ c : Chain α, (∀ n, P (c n)) → P (ωSup c)

namespace Admissible

/-- The constant true predicate is admissible. -/
theorem const_true : Admissible fun _ : α => True := fun _ _ => trivial

/-- A conjunction of admissible predicates is admissible. -/
theorem and {P Q : α → Prop} (hP : Admissible P) (hQ : Admissible Q) :
    Admissible fun x => P x ∧ Q x :=
  fun c h => ⟨hP c fun n => (h n).1, hQ c fun n => (h n).2⟩

/-- A universal quantification of admissible predicates is admissible. -/
theorem forall_ {ι : Sort*} {P : ι → α → Prop} (hP : ∀ i, Admissible (P i)) :
    Admissible fun x => ∀ i, P i x :=
  fun c h i => hP i c fun n => h n i

/-- The preimage of an admissible predicate under an ω-Scott-continuous map is admissible. -/
theorem comp {P : β → Prop} (hP : Admissible P) {f : α → β} (hf : ωScottContinuous f) :
    Admissible fun x => P (f x) := fun c h => by
  dsimp only
  rw [hf.map_ωSup c]
  exact hP _ h

/-- An admissible predicate on the values at `a` of functions is admissible on the functions. -/
theorem apply {ι : Type*} {γ : ι → Type*} [∀ i, OmegaCompletePartialOrder (γ i)] (a : ι)
    {P : γ a → Prop} (hP : Admissible P) : Admissible fun h : (∀ i, γ i) => P (h a) :=
  hP.comp (ωScottContinuous.apply a)

/-- An inequality `f x ≤ g x` with `f` ω-Scott-continuous and `g` monotone is admissible. -/
theorem le {f g : α → β} (hf : ωScottContinuous f) (hg : Monotone g) :
    Admissible fun x => f x ≤ g x := fun c h => by
  dsimp only
  rw [hf.map_ωSup c]
  exact ωSup_le _ _ fun n => (h n).trans (hg (le_ωSup c n))

/-- An upper bound by a constant is admissible. -/
theorem le_const (b : α) : Admissible fun x => x ≤ b := fun _ h => ωSup_le _ _ h

/-- An equation between ω-Scott-continuous maps is admissible. -/
theorem eq {f g : α → β} (hf : ωScottContinuous f) (hg : ωScottContinuous g) :
    Admissible fun x => f x = g x := fun c h => by
  dsimp only
  rw [hf.map_ωSup c, hg.map_ωSup c]
  exact le_antisymm (ωSup_le _ _ fun n => le_ωSup_of_le n (h n).le)
    (ωSup_le _ _ fun n => le_ωSup_of_le n (h n).ge)

end Admissible

/-- **Scott induction along a chain.** When every element after the first of the chain `c` is
the image of its predecessor under `f`, an admissible predicate that holds at `c 0` and is
preserved by `f` holds at the supremum of `c`. -/
theorem ωSup_induction {P : α → Prop} (hP : Admissible P) (c : Chain α) (f : α → α)
    (hc : ∀ n, c (n + 1) = f (c n)) (h0 : P (c 0)) (hstep : ∀ x, P x → P (f x)) :
    P (ωSup c) :=
  hP c fun n => by
    induction n with
    | zero => exact h0
    | succ n ih => rw [hc]; exact hstep _ ih

/-- **Scott induction for iterates.** An admissible predicate that holds at `x` and is preserved
by `f` holds at the supremum of the iterates of `f` on `x`. -/
theorem ωSup_iterateChain_induction (f : α →o α) (x : α) (h : x ≤ f x) {P : α → Prop}
    (hP : Admissible P) (h0 : P x) (hstep : ∀ y, P y → P (f y)) :
    P (ωSup (fixedPoints.iterateChain f x h)) :=
  ωSup_induction hP _ f (fun n => Function.iterate_succ_apply' f n x) h0 hstep

end OmegaCompletePartialOrder

namespace OrderHom

open OmegaCompletePartialOrder

/-- **Scott induction** (fixed-point induction). On a complete lattice, an admissible predicate
that holds at `⊥` and is preserved by an ω-Scott-continuous map `f` holds at the least fixed
point of `f`. -/
theorem lfp_scott_induction {γ : Type*} [CompleteLattice γ] (f : γ →o γ)
    (hf : ωScottContinuous f) {P : γ → Prop} (hP : Admissible P) (h0 : P ⊥)
    (hstep : ∀ x, P x → P (f x)) : P f.lfp := by
  have hlfp : f.lfp = ωSup (fixedPoints.iterateChain f ⊥ bot_le) := by
    rw [fixedPoints.lfp_eq_sSup_iterate f hf]
    exact le_antisymm (iSup_le fun n => le_ωSup (fixedPoints.iterateChain f ⊥ bot_le) n)
      (ωSup_le _ _ fun n => le_iSup (fun n => f^[n] ⊥) n)
  rw [hlfp]
  exact ωSup_iterateChain_induction f ⊥ bot_le hP h0 hstep

end OrderHom
