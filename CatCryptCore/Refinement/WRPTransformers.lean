/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.CategoryTheory.ThinDoubleCategory
public import RefinementWP

/-!
# The double category of predicate transformers

A vertical arrow with concretization `γ` and return relation `R` determines a concretization
between function lattices, `Q ↦ γ.post R Q`, its conjoint. A square with top `u`, left `f`,
right `g` and bottom `w` is the inequality of transformers `f* ∘ u ⊑ w ∘ g*`, where `f*` and
`g*` are the conjoints, at every exception postcondition `E` mapped by `g.eps`. The conjoints
preserve suprema, so each has a right adjoint `f*ʳ`, and the square is equivalently the
inequality `u ⊑ f*ʳ ∘ w ∘ g*`: the abstract transformer is below the concrete transformer
between decoding and encoding.

This file defines the thin double category `Obj` of predicate transformers, whose squares are
these inequalities. The weakest precondition of a family of levels of programs is a thin double
functor into it (`WRPLevels.wpDouble`), full on squares; the refinement squares of `WRPDouble`
are its instance at monad levels.

## Main definitions

* `Lat`: a Heyting assertion lattice with an exception postcondition type.
* `Obj`: a lattice and a value type; `Trans A X Y`: monotone transformers
  `(Y → A.Pred) → A.E → X → A.Pred`; `VHom`, `HHom`, `Sq`: the arrows and squares of the
  double category of predicate transformers; `VHom.conj f`, the conjoint
  `RefinementWP.Concretization.conjoint` of a vertical arrow.

## Main results

* `refines_iff_post_le`: a family of refinements is an inequality of transformers.
* `instThinDoubleCategoryObj`: predicate transformers form a thin double category.
* `Sq.iff_le_rightAdjoint`: the decode/encode form of a square.
-/

@[expose] public section

set_option autoImplicit false

open Std.WP Lean.Order

universe u v w w'

namespace CatCrypt.Refinement.WRPTransformers

open CategoryTheory RefinementWP

/-! ## The double category of predicate transformers -/

/-- A Heyting assertion lattice `Pred` with an exception postcondition type `E`. -/
structure Lat where
  /-- The assertions. -/
  Pred : Type w
  /-- The exception postconditions. -/
  E : Type w'
  [instPred : Assertion Pred]
  [instHeyting : Heyting Pred]
  [instE : Assertion E]

attribute [instance] Lat.instPred Lat.instHeyting Lat.instE

/-- An object: a lattice and a value type. -/
structure Obj where
  /-- The lattice. -/
  lat : Lat.{w, w'}
  /-- The value type. -/
  carrier : Type v

/-- A monotone predicate transformer of the lattice `A` from postconditions on `Y` to
preconditions on `X`, with an exception postcondition. -/
@[ext]
structure Trans (A : Lat.{w, w'}) (X Y : Type v) where
  /-- The precondition of a postcondition and an exception postcondition. -/
  tr : (Y → A.Pred) → A.E → X → A.Pred
  /-- `tr` is monotone in the postcondition. -/
  mono {Q Q' : Y → A.Pred} (E : A.E) : Q ⊑ Q' → tr Q E ⊑ tr Q' E

namespace Trans

variable {A : Lat.{w, w'}}

/-- The identity transformer: evaluation of the postcondition. -/
def id (X : Type v) : Trans A X X where
  tr Q _ := Q
  mono _ h := h

/-- The composite transformer in program order: `u` first, then `u'`. -/
def comp {X Y Z : Type v} (u : Trans A X Y) (u' : Trans A Y Z) : Trans A X Z where
  tr Q E := u.tr (u'.tr Q E) E
  mono E h := u.mono E (u'.mono E h)

end Trans

/-- A vertical arrow from `a` (abstract) to `c` (concrete): a concretization of assertions that
preserves suprema, binary meets, `⊥` and `⊤`, an exception map, and a return relation. -/
@[ext]
structure VHom (a c : Obj.{v, w, w'}) where
  /-- The concretization of assertions. -/
  γ : Concretization c.lat.Pred a.lat.Pred
  /-- `γ` preserves suprema. -/
  sup : γ.SupPreserving.{w, v}
  /-- `γ` preserves binary meets. -/
  meet : γ.MeetPreserving
  /-- `γ` is strict. -/
  bot : γ.pred bot ⊑ bot
  /-- `γ` preserves the top element. -/
  top : top ⊑ γ.pred top
  /-- The exception map. -/
  eps : a.lat.E → c.lat.E
  /-- The return relation between concrete and abstract values. -/
  R : c.carrier → a.carrier → c.lat.Pred

namespace VHom

/-- The identity vertical arrow. -/
noncomputable def id (a : Obj.{v, w, w'}) : VHom a a where
  γ := Concretization.id
  sup _ := PartialOrder.rel_refl
  meet _ _ := PartialOrder.rel_refl
  bot := PartialOrder.rel_refl
  top := PartialOrder.rel_refl
  eps e := e
  R := eqRel

/-- The composite vertical arrow. -/
noncomputable def comp {a b c : Obj.{v, w, w'}} (f : VHom a b) (g : VHom b c) : VHom a c where
  γ := g.γ.comp f.γ
  sup p := PartialOrder.rel_trans (g.γ.pred_mono (f.sup p)) (g.sup _)
  meet p q := PartialOrder.rel_trans (g.meet _ _) (g.γ.pred_mono (f.meet p q))
  bot := PartialOrder.rel_trans (g.γ.pred_mono f.bot) g.bot
  top := PartialOrder.rel_trans g.top (g.γ.pred_mono f.top)
  eps e := g.eps (f.eps e)
  R := g.γ.relComp g.R f.R

/-- The conjoint of a vertical arrow: the concretization of postconditions on its values. -/
noncomputable def conj {a c : Obj.{v, w, w'}} (f : VHom a c) :
    Concretization (c.carrier → c.lat.Pred) (a.carrier → a.lat.Pred) :=
  f.γ.conjoint f.R

/-- The conjoint of the identity is the identity. -/
theorem conj_id (a : Obj.{v, w, w'}) (Q : a.carrier → a.lat.Pred) :
    (VHom.id a).conj.pred Q = Q :=
  Concretization.id_post_eqRel Q

/-- The conjoint of a composite is the composite of the conjoints. -/
theorem conj_comp {a b c : Obj.{v, w, w'}} (f : VHom a b) (g : VHom b c)
    (Q : a.carrier → a.lat.Pred) : (f.comp g).conj.pred Q = g.conj.pred (f.conj.pred Q) :=
  Concretization.comp_post_relComp g.sup g.meet g.R f.R Q

end VHom

/-- The vertical category of predicate transformers. -/
noncomputable instance instCategoryObj : Category Obj.{v, w, w'} where
  Hom := VHom
  id := VHom.id
  comp := VHom.comp
  id_comp f := by
    apply VHom.ext
    · rfl
    · rfl
    · exact Concretization.relComp_eqRel f.γ f.bot f.top f.R
  comp_id f := by
    apply VHom.ext
    · rfl
    · rfl
    · exact Concretization.id_relComp_eqRel f.R
  assoc f g h := by
    apply VHom.ext
    · rfl
    · rfl
    · exact Concretization.relComp_assoc h.γ g.γ h.sup h.meet h.R g.R f.R

/-- A horizontal arrow: a monotone transformer of one lattice. -/
inductive HHom : Obj.{v, w, w'} → Obj.{v, w, w'} → Type (max (v + 1) (w + 1) (w' + 1))
  | mk {A : Lat.{w, w'}} {X Y : Type v} (t : Trans A X Y) : HHom ⟨A, X⟩ ⟨A, Y⟩

namespace HHom

/-- The identity transformer. -/
def id (a : Obj.{v, w, w'}) : HHom a a :=
  HHom.mk (A := a.lat) (X := a.carrier) (Trans.id a.carrier)

/-- Composition of transformers in program order. -/
def comp : {a b c : Obj.{v, w, w'}} → HHom a b → HHom b c → HHom a c
  | _, _, _, .mk u, .mk u' => .mk (u.comp u')

/-- The identity is a left unit. -/
theorem id_comp {a b : Obj.{v, w, w'}} (f : HHom a b) : (HHom.id a).comp f = f := by
  cases f
  rfl

/-- The identity is a right unit. -/
theorem comp_id {a b : Obj.{v, w, w'}} (f : HHom a b) : f.comp (HHom.id b) = f := by
  cases f
  rfl

/-- Composition is associative. -/
theorem comp_assoc {a b c d : Obj.{v, w, w'}} (f : HHom a b) (g : HHom b c) (h : HHom c d) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  cases f
  cases g
  cases h
  rfl

end HHom

/-- The horizontal category of predicate transformers. -/
instance instCategoryHorObj : Category (Hor Obj.{v, w, w'}) where
  Hom a b := HHom a b
  id a := HHom.id a
  comp f g := HHom.comp f g
  id_comp f := HHom.id_comp f
  comp_id f := HHom.comp_id f
  assoc f g h := HHom.comp_assoc f g h

/-- The square with top `u`, left `f`, right `g` and bottom `w`: the vertical arrows have the
same concretization and exception map, and `f* ∘ u ⊑ w ∘ g*` at every exception
postcondition, with `f*`, `g*` the conjoints. -/
def Sq : {a b c d : Obj.{v, w, w'}} → HHom a b → VHom a c → VHom b d → HHom c d → Prop
  | _, _, _, _, .mk u, f, g, .mk w =>
    f.γ = g.γ ∧ f.eps = g.eps ∧ ∀ Q E, f.conj.pred (u.tr Q E) ⊑ w.tr (g.conj.pred Q) (g.eps E)

/-- Vertical pasting of squares of transformers. -/
theorem Sq.vcomp {a b c d c' d' : Obj.{v, w, w'}} {u : HHom a b} {f : VHom a c}
    {g : VHom b d} {w : HHom c d} {f' : VHom c c'} {g' : VHom d d'} {z : HHom c' d'}
    (s : Sq u f g w) (t : Sq w f' g' z) : Sq u (f.comp f') (g.comp g') z := by
  cases u
  cases w
  cases z
  obtain ⟨s1, s2, s3⟩ := s
  obtain ⟨t1, t2, t3⟩ := t
  refine ⟨?_, ?_, ?_⟩
  · simp only [VHom.comp, s1, t1]
  · simp only [VHom.comp, s2, t2]
  · intro Q E
    rw [VHom.conj_comp, VHom.conj_comp]
    exact PartialOrder.rel_trans (f'.conj.pred_mono (s3 Q E)) (t3 _ _)

/-- Horizontal pasting of squares of transformers. -/
theorem Sq.hcomp {a b b' c d d' : Obj.{v, w, w'}} {u : HHom a b} {f : VHom a c}
    {g : VHom b d} {w : HHom c d} {u' : HHom b b'} {k : VHom b' d'}
    {w' : HHom d d'} (s : Sq u f g w) (s' : Sq u' g k w') :
    Sq (u.comp u') f k (w.comp w') := by
  cases u
  cases w
  cases u'
  cases w'
  obtain ⟨s1, s2, s3⟩ := s
  obtain ⟨t1, t2, t3⟩ := s'
  refine ⟨s1.trans t1, s2.trans t2, ?_⟩
  intro Q E
  have h := t3 Q E
  rw [← t2] at h ⊢
  exact PartialOrder.rel_trans (s3 _ E) (Trans.mono _ _ h)

/-- The vertical identity square. -/
theorem Sq.vid {a b : Obj.{v, w, w'}} (u : HHom a b) : Sq u (VHom.id a) (VHom.id b) u := by
  cases u
  refine ⟨rfl, rfl, ?_⟩
  intro Q E
  rw [VHom.conj_id, VHom.conj_id]
  exact PartialOrder.rel_refl

/-- The horizontal identity square. -/
theorem Sq.hid {a c : Obj.{v, w, w'}} (f : VHom a c) : Sq (HHom.id a) f f (HHom.id c) :=
  ⟨rfl, rfl, fun _ _ => PartialOrder.rel_refl⟩

/-- Predicate transformers form a thin double category. -/
noncomputable instance instThinDoubleCategoryObj : ThinDoubleCategory Obj.{v, w, w'} where
  Sq u f g w := Sq u f g w
  vcomp s t := Sq.vcomp s t
  hcomp s t := Sq.hcomp s t
  vid u := Sq.vid u
  hid f := Sq.hid f

/-- The decode/encode form of a square: `u ⊑ f*ʳ ∘ w ∘ g*`, with `f*ʳ` the right adjoint of the
conjoint of `f`, when the concretization of `f` preserves suprema indexed by the universe of
the function lattices. -/
theorem Sq.iff_le_rightAdjoint {A B : Lat.{w, w'}} {X Y X' Y' : Type v} {u : Trans A X Y}
    {f : VHom ⟨A, X⟩ ⟨B, X'⟩} {g : VHom ⟨A, Y⟩ ⟨B, Y'⟩} {w : Trans B X' Y'}
    (hf : f.γ.SupPreserving.{_, max v w}) :
    Sq (.mk u) f g (.mk w) ↔ f.γ = g.γ ∧ f.eps = g.eps ∧
      ∀ Q E, u.tr Q E ⊑ f.conj.rightAdjoint (w.tr (g.conj.pred Q) (g.eps E)) := by
  refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun Q =>
    forall_congr' fun E => ?_
  exact Concretization.rightAdjoint_isRightAdjoint
    (Concretization.conjoint_supPreserving f.R hf) _ _

/-! ## Refinement as an inequality of transformers -/

/-- A family of refinements of the abstract programs `pu xa` by the concrete programs `pw xc`
under the preconditions `R xc xa` is the inequality of transformers
`γ.post R ∘ wp pu ⊑ wp pw ∘ γ.post S`. -/
theorem refines_iff_post_le {CProg AProg : Type u} {CIn AIn CVal AVal : Type v}
    {CPred APred : Type w} {CE AE : Type w'} [Assertion CPred] [Heyting CPred]
    [Assertion APred] [Assertion CE] [Assertion AE] [WP CProg CVal CPred CE]
    [WP AProg AVal APred AE] (γ : Concretization CPred APred) (eps : AE → CE)
    (R : CIn → AIn → CPred) (S : CVal → AVal → CPred) (pu : AIn → AProg) (pw : CIn → CProg) :
    (∀ xc xa, Refines (R xc xa) γ eps (pw xc) (pu xa) S) ↔
      ∀ Qa Ea, γ.post R (fun xa => wp (pu xa) Qa Ea) ⊑
        fun xc => wp (pw xc) (γ.post S Qa) (eps Ea) := by
  constructor
  · intro h Qa Ea xc
    exact iSup_le _ _ fun xa => wrp_transport (h xc xa) Qa Ea
  · intro h xc xa
    exact wrp_intro fun Qa Ea =>
      PartialOrder.rel_trans
        (le_iSup (fun xa' => meet (R xc xa') (γ.pred (wp (pu xa') Qa Ea))) xa) (h Qa Ea xc)

end CatCrypt.Refinement.WRPTransformers
