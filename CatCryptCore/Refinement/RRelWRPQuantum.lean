/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.Instrument
public import CatCryptCore.ForMathlib.Order.LeanOrderENNReal
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
public import RefinementWP.Classes

/-!
# Refinement weakest preconditions of quantum channels

A quantum computation with one outcome is a predicate transformer on observations of quantum
states, by precomposition. A state is a positive semidefinite matrix and an observation is an
arbitrary function from states to `ℝ≥0∞`, ordered pointwise. Observations need be neither linear
nor monotone in the state, so they separate states, and positive semidefinite matrices span all
matrices. Refinement along the identity in the sense of `RefinementWP.Refines` is therefore
equality of computations, and refinement in one direction implies refinement in the other.

A compiler pass that preserves the channel of each circuit thus refines in both directions.

## Main definitions

* `PSDState d`: the positive semidefinite matrices of dimension `d`.
* `channelState I`: the action of a computation with one outcome on these states.
* `instWPChannel`: the `Std.WP` instance of computations with one outcome.
* `ChannelRefines c a`: refinement of `a` by `c` along the identity, under `⊤`.

## Main results

* `channelRefines_iff`, `channelRefines_both_iff`: refinement is equality of computations.
* `ChannelRefines.trans`: refinements compose, by vertical pasting.

## Search words

quantum channel, weakest precondition, wrp, refinement, observation, compiler pass
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum RefinementWP
open Std.WP (WP wp)
open scoped Matrix ComplexOrder MatrixOrder ENNReal

noncomputable section

namespace CatCrypt.Refinement.ChannelWRP

variable {d : ℕ}

/-! ## States and the weakest precondition of a channel -/

/-- The states of dimension `d`: the positive semidefinite matrices, normalised or not. -/
abbrev PSDState (d : ℕ) : Type := {ρ : Matrix (Fin d) (Fin d) ℂ // ρ.PosSemidef}

/-- The state after a quantum computation with one outcome. -/
def channelState (I : QComp d Unit) (ρ : PSDState d) : PSDState d :=
  ⟨I.branch () ρ.1, I.branch_psd () ρ.1 ρ.2⟩

/-- A computation with one outcome is determined by its action on positive semidefinite
matrices, since these span all matrices. -/
theorem channelState_injective :
    Function.Injective (channelState : QComp d Unit → PSDState d → PSDState d) :=
  fun _ _ h => QComp.ext fun _ => LinearMap.ext_on CStarAlgebra.span_nonneg fun ρ hρ =>
    congrArg Subtype.val (congrFun h ⟨ρ, Matrix.nonneg_iff_posSemidef.mp hρ⟩)

/-- The weakest precondition of a computation with one outcome at an observation is the
observation precomposed with the computation. There is no exceptional exit. -/
instance instWPChannel : WP (QComp d Unit) Unit (PSDState d → ℝ≥0∞) Unit where
  trans I := ⟨fun Q _ ρ => Q () (channelState I ρ)⟩
  trans_monotone _ := fun _ _ _ _ _ hQ _ => hQ () _

/-- The weakest precondition of a channel at a state: the unfolding lemma of `instWPChannel`. -/
theorem wp_channel_apply (I : QComp d Unit) (Q : Unit → PSDState d → ℝ≥0∞) (E : Unit)
    (ρ : PSDState d) : wp I Q E ρ = Q () (channelState I ρ) := rfl

/-! ## Refinement along the identity -/

/-- `c` refines `a` along the identity concretization, the identity exception map and the
equality of return values, under `⊤`. -/
abbrev ChannelRefines (c a : QComp d Unit) : Prop :=
  RefinesTop Concretization.id (fun e : Unit => e) eqRel c a

/-- On the one return value, the postcondition along the identity is the postcondition. -/
theorem post_id_eqRel (Q : Unit → PSDState d → ℝ≥0∞) :
    Concretization.id.post eqRel Q = Q := by
  funext v
  apply Lean.Order.PartialOrder.rel_antisymm
  · exact Lean.Order.iSup_le _ _ fun _ => Lean.Order.meet_le_right _ _
  · refine Lean.Order.PartialOrder.rel_trans ?_ (Lean.Order.le_iSup _ v)
    exact Lean.Order.le_meet _ _ _ (Lean.Order.CompleteLattice.le_ofProp _ _ rfl)
      Lean.Order.PartialOrder.rel_refl

/-- Refinement along the identity is the pointwise inequality of the precomposed
observations. -/
theorem channelRefines_iff_le {c a : QComp d Unit} :
    ChannelRefines c a ↔ ∀ (f : PSDState d → ℝ≥0∞) (ρ : PSDState d),
      f (channelState a ρ) ≤ f (channelState c ρ) := by
  rw [ChannelRefines, RefinesTop, refines_top_iff]
  simp only [post_id_eqRel]
  exact ⟨fun h f ρ => h (fun _ => f) () ρ, fun h Q _ ρ => h (Q ()) ρ⟩

/-- Refinement along the identity, in one direction, is equality of computations. -/
theorem channelRefines_iff {c a : QComp d Unit} : ChannelRefines c a ↔ a = c := by
  classical
  rw [channelRefines_iff_le]
  constructor
  · intro h
    refine channelState_injective (funext fun ρ => ?_)
    have hρ := h (fun σ => if σ = channelState a ρ then 1 else 0) ρ
    grind [one_ne_zero, zero_lt_one, not_le]
  · rintro rfl f ρ
    exact le_rfl

/-- Refinement in both directions along the identity is equality of computations. -/
theorem channelRefines_both_iff {c a : QComp d Unit} :
    ChannelRefines c a ∧ ChannelRefines a c ↔ a = c := by
  grind [channelRefines_iff]

/-- Refinements along the identity compose, by vertical pasting. -/
theorem ChannelRefines.trans {c b a : QComp d Unit} (h₂ : ChannelRefines c b)
    (h₁ : ChannelRefines b a) : ChannelRefines c a := by
  have h := RefinesTop.trans h₂ h₁
  have hcomp : (Concretization.id (APred := PSDState d → ℝ≥0∞)).relComp
      (eqRel (CVal := Unit)) (eqRel (CVal := Unit)) = eqRel := by
    funext v w
    apply Lean.Order.PartialOrder.rel_antisymm
    · exact Lean.Order.CompleteLattice.le_ofProp _ _ rfl
    · refine Lean.Order.PartialOrder.rel_trans ?_ (Lean.Order.le_iSup _ v)
      exact Lean.Order.le_meet _ _ _ (Lean.Order.CompleteLattice.le_ofProp _ _ rfl)
        Lean.Order.PartialOrder.rel_refl
  rwa [hcomp] at h

end CatCrypt.Refinement.ChannelWRP
