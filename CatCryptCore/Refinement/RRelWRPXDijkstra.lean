/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import RefinementWP.Compose
public import CatCryptCore.XDijkstra.XStdWP
public import CatCryptCore.XDijkstra.XMorphismInstance

/-!
# Transfer of weakest preconditions in XDijkstra as refinement

An observation `XCoreWP m Pred EPred G` of XDijkstra, at assertion types that are complete
lattices of `Std.WP` whose order `≤` is `⊑` (`LERelCompat`), reads as a `Std.WP` interpretation
of the programs of `m`; the grade is forgotten. At these readings a morphism of observations
`XCoreWPHom` along `θ : m → n` is a refinement of `Std.WP` programs (`RefinementWP.Refines`):
the image `θ c` refines `c` along the concretization of the morphism's precondition map, at
every return relation and exception map whose concrete postconditions the morphism's
postcondition map carries above the abstract ones.

The two morphisms of XDijkstra are instances. For an observation pulled back along a family of
maps `h : m → n` (`XCoreWP.pullback`), `c` and `h c` refine each other at the identity
concretization and the equality relation, and so do the instances of `WPMonad` that the bridge
`XCoreWP.toWPMonadOfLe` builds when `h` is a monad morphism. For the base change
`thetaX : XPredTrans (graded G (arg σ pure)) → XPredTrans (graded G (arg σ (except PUnit pure)))`
of `instXWPMorphismBaseChange`, `thetaX x` refines `x` along the concretization of the
morphism (the identity on state predicates), at the equality relation and every exception map
into the failure postconditions.

## Main definitions

* `XCoreWP.toStdWP`: the `Std.WP` interpretation of the programs of an `XCoreWP` observation.
* `XCoreWPHom.toConc`: the concretization of the precondition map of a morphism of
  observations.
* `idToStateM σ`: the embedding of `Id` into `StateM σ` by `pure`.
* `assertionM`, `assertionN`, `eAssertionM`, `eAssertionN`: the assertion and exception
  postcondition types of the two shapes of the base change as `Std.WP` assertion types.

## Main results

* `refines_of_wpHom`: the image of a program under a morphism of observations refines it.
* `refines_pullback_image`, `refines_image_pullback`: `c` and `h c` refine each other at the
  identity concretization and `eqRel`; `refines_pullback_image_wpMonad`,
  `refines_image_pullback_wpMonad`: the same at the `WPMonad` instances of the bridge;
  `refines_idToStateM`: their hypotheses hold at `idToStateM σ`
  (`isMonadMorphism_idToStateM`).
* `refines_thetaX`: the base change `thetaX x` refines `x`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Refinement.WRP

open Std.WP Lean.Order RefinementWP CatCrypt.XDijkstra CatCrypt.StdWPBridge

universe u v w w' g

/-! ## The `Std.WP` reading of an observation -/

/-- The `Std.WP` interpretation of the programs of an `XCoreWP` observation: the weakest
    precondition of `c` is the map of its transformer. The grade is forgotten. -/
@[reducible] def XCoreWP.toStdWP (m : Type u → Type v) (Pred : Type w) (EPred : Type w')
    {G : Type g} [Assertion Pred] [Assertion EPred] [LE Pred] [LE EPred] [LERelCompat Pred]
    [LERelCompat EPred] [XCoreWP m Pred EPred G] (α : Type u) : WP (m α) α Pred EPred where
  wpTrans c := ⟨(XCoreWP.wp c : XCorePT Pred EPred G α).apply⟩
  wp_trans_monotone c := fun _ _ _ _ hepost hpost =>
    (LERelCompat.le_iff_rel _ _).1
      ((XCoreWP.wp c : XCorePT Pred EPred G α).mono
        (fun a => (LERelCompat.le_iff_rel _ _).2 (hpost a))
        ((LERelCompat.le_iff_rel _ _).2 hepost))

/-! ## Morphisms of observations as refinements -/

section Hom

variable {m n : Type u → Type v} {Pred₁ Pred₂ : Type w} {EPred₁ EPred₂ : Type w'}
  {G₁ G₂ : Type g}
  [Assertion Pred₁] [Assertion Pred₂] [Assertion EPred₁] [Assertion EPred₂]
  [LE Pred₁] [LE Pred₂] [LE EPred₁] [LE EPred₂]
  [LERelCompat Pred₁] [LERelCompat Pred₂] [LERelCompat EPred₁] [LERelCompat EPred₂]
  [XCoreWP m Pred₁ EPred₁ G₁] [XCoreWP n Pred₂ EPred₂ G₂]
  {θ : {α : Type u} → m α → n α}

/-- The concretization of the precondition map of a morphism of observations. -/
def _root_.CatCrypt.XDijkstra.XCoreWPHom.toConc
    (H : XCoreWPHom (m := m) (n := n) Pred₁ EPred₁ Pred₂ EPred₂ (G₁ := G₁) (G₂ := G₂) θ) :
    Concretization Pred₂ Pred₁ where
  pred := H.preMap
  pred_mono h :=
    (LERelCompat.le_iff_rel _ _).1 (H.preMap_mono ((LERelCompat.le_iff_rel _ _).2 h))

/-- The image `θ c` of a program under a morphism of observations refines `c`, under every
    precondition, along the concretization of the morphism, at a return relation `Q` and an
    exception map `eps` whose concrete postconditions the postcondition map of the morphism
    carries above the abstract postconditions. -/
theorem refines_of_wpHom
    (H : XCoreWPHom (m := m) (n := n) Pred₁ EPred₁ Pred₂ EPred₂ (G₁ := G₁) (G₂ := G₂) θ)
    {α : Type u} (P : Pred₂) (c : m α) (Q : α → α → Pred₂) (eps : EPred₁ → EPred₂)
    (hpost : ∀ (Qa : α → Pred₁) (Ea : EPred₁),
      Qa ⊑ (H.postMap (H.toConc.post Q Qa, eps Ea)).1 ∧
        Ea ⊑ (H.postMap (H.toConc.post Q Qa, eps Ea)).2) :
    letI := XCoreWP.toStdWP m Pred₁ EPred₁ α
    letI := XCoreWP.toStdWP n Pred₂ EPred₂ α
    Refines P H.toConc eps (θ c) c Q := by
  let _ := XCoreWP.toStdWP m Pred₁ EPred₁ α
  let _ := XCoreWP.toStdWP n Pred₂ EPred₂ α
  apply wrp_intro
  intro Qa Ea
  refine PartialOrder.rel_trans (meet_le_right _ _) ?_
  change H.preMap _ ⊑ (XCoreWP.wp (θ c) : XCorePT Pred₂ EPred₂ G₂ α).apply _ _
  rw [H.transfer]
  exact H.toConc.pred_mono
    (WP.wp_monotone (x := c) (hpost Qa Ea).1 (hpost Qa Ea).2)

end Hom

/-! ## Observations pulled back along a monad morphism -/

section Pullback

variable {m n : Type u → Type v} {Pred : Type w} {EPred : Type w'} {G : Type g}
  [Assertion Pred] [Assertion EPred] [LE Pred] [LE EPred] [LERelCompat Pred]
  [LERelCompat EPred] [XCoreWP n Pred EPred G] (h : {α : Type u} → m α → n α)

/-- A program refines its image under `h`, at the observation pulled back along `h`, the
    identity concretization, the identity exception map and the equality relation. -/
theorem refines_pullback_image {α : Type u} (P : Pred) (c : m α) :
    @Refines (m α) (n α) α α Pred Pred EPred EPred _ _ _ _
      (@XCoreWP.toStdWP m Pred EPred G _ _ _ _ _ _ (XCoreWP.pullback @h) α)
      (XCoreWP.toStdWP n Pred EPred α)
      P Concretization.id (fun e => e) c (h c) (eqRel (CPred := Pred)) :=
  @Refines.refl (n α) α Pred EPred _ _ (XCoreWP.toStdWP n Pred EPred α) P (h c)

/-- The image under `h` of a program refines it, at the observation pulled back along `h`, the
    identity concretization, the identity exception map and the equality relation. -/
theorem refines_image_pullback {α : Type u} (P : Pred) (c : m α) :
    @Refines (n α) (m α) α α Pred Pred EPred EPred _ _ _ _
      (XCoreWP.toStdWP n Pred EPred α)
      (@XCoreWP.toStdWP m Pred EPred G _ _ _ _ _ _ (XCoreWP.pullback @h) α)
      P Concretization.id (fun e => e) (h c) c (eqRel (CPred := Pred)) :=
  @Refines.refl (n α) α Pred EPred _ _ (XCoreWP.toStdWP n Pred EPred α) P (h c)

variable [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]

/-- A program refines its image under a monad morphism `h`, at the `WPMonad` instances that
    `XCoreWP.toWPMonadOfLe` builds for the observation of `n` and its pull-back. -/
theorem refines_pullback_image_wpMonad (hh : IsMonadMorphism m n @h)
    (hL : XCoreWP.LowerLaws n (Pred := Pred) (EPred := EPred) (G := G)) {α : Type u}
    (P : Pred) (c : m α) :
    letI := XCoreWP.toWPMonadOfLe n hL
    letI := @XCoreWP.toWPMonadOfLe m Pred EPred G _ _ _ _ _ _ _ _ (XCoreWP.pullback @h)
      (lowerLaws_pullback @h hh hL)
    Refines P Concretization.id (fun e => e) c (h c) (eqRel (CPred := Pred)) :=
  refines_pullback_image @h P c

/-- The image of a program under a monad morphism `h` refines it, at the `WPMonad` instances
    that `XCoreWP.toWPMonadOfLe` builds for the observation of `n` and its pull-back. -/
theorem refines_image_pullback_wpMonad (hh : IsMonadMorphism m n @h)
    (hL : XCoreWP.LowerLaws n (Pred := Pred) (EPred := EPred) (G := G)) {α : Type u}
    (P : Pred) (c : m α) :
    letI := XCoreWP.toWPMonadOfLe n hL
    letI := @XCoreWP.toWPMonadOfLe m Pred EPred G _ _ _ _ _ _ _ _ (XCoreWP.pullback @h)
      (lowerLaws_pullback @h hh hL)
    Refines P Concretization.id (fun e => e) (h c) c (eqRel (CPred := Pred)) :=
  refines_image_pullback @h P c

end Pullback

section PullbackInstance

/-- The order `≤ := ⊑` on the empty exception postcondition. -/
local instance : LE EStack⟨⟩ := relLE EStack⟨⟩

local instance : LERelCompat EStack⟨⟩ := relLE_compat EStack⟨⟩

/-- The embedding of `Id` into `StateM σ` by `pure`. -/
def idToStateM (σ : Type) {α : Type} (c : Id α) : StateM σ α := pure c.run

/-- The embedding `Id → StateM σ` by `pure` is a monad morphism. -/
theorem isMonadMorphism_idToStateM (σ : Type) :
    IsMonadMorphism Id (StateM σ) (@idToStateM σ) where
  map_pure _ := rfl
  map_bind c f := by simp [idToStateM]

/-- The hypotheses of `refines_pullback_image_wpMonad` hold at the embedding `Id → StateM σ`
    and the `WPMonad` instance of `StateM σ`. -/
theorem refines_idToStateM (σ α : Type) (P : σ → Prop) (c : Id α) :
    letI : XCoreWP (StateM σ) (σ → Prop) EStack⟨⟩ Unit := XCoreWP.ofWPMonad (StateM σ)
    letI instN := XCoreWP.toWPMonadOfLe (StateM σ) lowerLaws_ofWPMonad
    letI instM := @XCoreWP.toWPMonadOfLe Id (σ → Prop) EStack⟨⟩ Unit _ _ _ _ _ _ _ _
      (XCoreWP.pullback (@idToStateM σ))
      (lowerLaws_pullback (@idToStateM σ) (isMonadMorphism_idToStateM σ) lowerLaws_ofWPMonad)
    @Refines (Id α) (StateM σ α) α α (σ → Prop) (σ → Prop) EStack⟨⟩ EStack⟨⟩ _ _ _ _
      (instM.toWP α) (instN.toWP α)
      P Concretization.id (fun e => e) c (idToStateM σ c) (eqRel (CPred := σ → Prop)) :=
  letI : XCoreWP (StateM σ) (σ → Prop) EStack⟨⟩ Unit := XCoreWP.ofWPMonad (StateM σ)
  refines_pullback_image_wpMonad (@idToStateM σ) (isMonadMorphism_idToStateM σ)
    lowerLaws_ofWPMonad P c

end PullbackInstance

/-! ## The base change `StateM σ → StateT σ Option` -/

section BaseChange

variable {G σ : Type}

attribute [local instance] XAssertion.preorder XExceptConds.preorder XWP.toCoreWP

/-- The state predicates of the total state shape as a `Std.WP` assertion type. -/
@[reducible] def assertionM : Assertion (XAssertion (.graded G (.arg σ .pure)) Prop) :=
  inferInstanceAs (Assertion (σ → Prop))

/-- The state predicates of the state shape with a failure layer as a `Std.WP` assertion
    type. -/
@[reducible] def assertionN :
    Assertion (XAssertion (.graded G (.arg σ (.except PUnit .pure))) Prop) :=
  inferInstanceAs (Assertion (σ → Prop))

/-- The exception postconditions of the total state shape as a `Std.WP` assertion type. -/
@[reducible] def eAssertionM : Assertion (XExceptConds (.graded G (.arg σ .pure)) Prop) :=
  inferInstanceAs (Assertion Unit)

/-- The exception postconditions of the state shape with a failure layer as a `Std.WP`
    assertion type: the failure postcondition. -/
@[reducible] def eAssertionN :
    Assertion (XExceptConds (.graded G (.arg σ (.except PUnit .pure))) Prop) :=
  inferInstanceAs (Assertion ((PUnit → Prop) × Unit))

attribute [local instance] assertionM assertionN eAssertionM eAssertionN

local instance : LERelCompat (XAssertion (.graded G (.arg σ .pure)) Prop) :=
  ⟨fun _ _ => Iff.rfl⟩

local instance : LERelCompat (XAssertion (.graded G (.arg σ (.except PUnit .pure))) Prop) :=
  ⟨fun _ _ => Iff.rfl⟩

local instance : LERelCompat (XExceptConds (.graded G (.arg σ .pure)) Prop) :=
  ⟨fun _ _ => Iff.rfl⟩

local instance :
    LERelCompat (XExceptConds (.graded G (.arg σ (.except PUnit .pure))) Prop) :=
  ⟨fun _ _ => Iff.rfl⟩

/-- The base change `thetaX x` refines `x`, under every precondition, along the concretization
    of the base-change morphism `instXWPMorphismBaseChange`, at the equality relation and every
    exception map `eps` into the failure postconditions. -/
theorem refines_thetaX {α : Type} (P : XAssertion (.graded G (.arg σ (.except PUnit .pure))) Prop)
    (x : XPredTrans (.graded G (.arg σ .pure)) Prop α)
    (eps : XExceptConds (.graded G (.arg σ .pure)) Prop →
      XExceptConds (.graded G (.arg σ (.except PUnit .pure))) Prop) :
    letI := XCoreWP.toStdWP (XPredTrans (.graded G (.arg σ .pure)) Prop)
      (XAssertion (.graded G (.arg σ .pure)) Prop)
      (XExceptConds (.graded G (.arg σ .pure)) Prop) α
    letI := XCoreWP.toStdWP (XPredTrans (.graded G (.arg σ (.except PUnit .pure))) Prop)
      (XAssertion (.graded G (.arg σ (.except PUnit .pure))) Prop)
      (XExceptConds (.graded G (.arg σ (.except PUnit .pure))) Prop) α
    Refines P (XWPMorphism.toCoreWPHom (Ω := Prop) (psm := .graded G (.arg σ .pure))
        (psn := .graded G (.arg σ (.except PUnit .pure))) (@thetaX G σ Prop _)).toConc
      eps (thetaX x) x eqRel := by
  refine refines_of_wpHom _ P x eqRel eps fun Qa Ea => ⟨?_, ?_⟩
  · intro v
    exact le_iSup_of_le v (le_meet _ _ _ (CompleteLattice.le_ofProp _ _ rfl) PartialOrder.rel_refl)
  · exact PartialOrder.rel_refl

end BaseChange

end CatCrypt.Refinement.WRP
