/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Refinement.WRPLevels

/-!
# Lax squares of relations as refinement squares

A relational semantics `S` of a horizontal category (`ThinDoubleCategory.RelSemantics`) gives a
level of programs in the sense of `WRPLevels`: the objects are those of the horizontal category,
the value type of `a` is the carrier `X a`, the assertions are `Prop` with the trivial exception
type `Unit`, and the weakest precondition of a program `u` is the demonic transformer of the
relation `S.sem u`, `Q ↦ fun x => ∀ y, S.sem u x y → Q y`, which is strict for relational
composition.

A relation `f : X a → X c → Prop`, a vertical arrow of `ThinDoubleCategory.ofRelSemantics S`,
goes to the vertical arrow of predicate transformers with the identity concretization, the
identity exception map and the return relation the converse of `f`: the vertical arrows of
`WRPLevels` relate concrete values (bottom) to abstract values (top), while `f` relates the
values of the top to those of the bottom. Top and bottom keep their places: a lax square
`f ; ⟦w⟧ ⊆ ⟦u⟧ ; g` says that the top `u` simulates the bottom `w`, and the refinement square
at the demonic weakest precondition says that the bottom `w` refines the top `u`. The two are
equivalent, so the map is a thin double functor full on squares. The angelic weakest
precondition `∃ y, r x y ∧ Q y` would instead make the refinement square the simulation of the
top by the bottom.

## Main definitions

* `propLat`: the assertion lattice `Prop` with the exception type `Unit`.
* `boxTrans r`: the demonic weakest precondition transformer of a relation `r`.
* `relVHom f`: the vertical arrow of predicate transformers of a relation, with the converse
  of `f` as its return relation.
* `relLevel S`, `relFamily S`: the level of a relational semantics and the one-level family.
* `relDouble S`: the thin double functor from `ThinDoubleCategory.ofRelSemantics S` into the
  refinement squares of `relFamily S`.

## Main results

* `boxTrans_eq`, `boxTrans_comp`: the demonic transformer is strict.
* `relVHom_id`, `relVHom_comp`: the vertical map preserves identities and composites.
* `laxSq_iff_sq`: a lax square of relations is a square of demonic transformers.
* `relDouble_sq_iff`: `relDouble S` is full on squares.
* `relDouble_sq_iff_box`: a refinement square of `relDouble S` as a statement about
  postconditions.
-/

@[expose] public section

set_option autoImplicit false

open Std.WP Lean.Order

universe u u' w

namespace CatCrypt.Refinement.WRPRelSemantics

open CategoryTheory ThinDoubleCategory RefinementWP

/-- The assertion lattice `Prop` with the trivial exception type `Unit`. -/
abbrev propLat : WRPTransformers.Lat.{0, 0} where
  Pred := Prop
  E := Unit

/-- The demonic weakest precondition transformer of a relation: the precondition of `Q` holds
at `x` when `Q` holds at every `y` related to `x`. -/
def boxTrans {α β : Type u'} (r : α → β → Prop) : WRPTransformers.Trans propLat α β where
  tr Q _ x := ∀ y, r x y → Q y
  mono _ h _ hx y hy := (h y : _ → _) (hx y hy)

/-- The demonic transformer of equality is the identity transformer. -/
theorem boxTrans_eq (α : Type u') :
    boxTrans (fun x y : α => x = y) = WRPTransformers.Trans.id α := by
  apply WRPTransformers.Trans.ext
  funext Q _ x
  exact propext ⟨fun h => h x rfl, fun h y (hy : x = y) => by cases hy; exact h⟩

/-- The demonic transformer of a relational composite is the composite transformer. -/
theorem boxTrans_comp {α β γ : Type u'} (r : α → β → Prop) (s : β → γ → Prop) :
    boxTrans (Relation.Comp r s) = (boxTrans r).comp (boxTrans s) := by
  apply WRPTransformers.Trans.ext
  funext Q _ x
  exact propext ⟨fun h m hm z hz => h z ⟨m, hm, hz⟩, fun h z ⟨m, hm, hz⟩ => h m hm z hz⟩

/-- The vertical arrow of predicate transformers of a relation `f` from the values of the
abstract object to those of the concrete object: the identity concretization of `Prop`, the
identity exception map and the converse of `f` as return relation. -/
noncomputable def relVHom {α β : Type u'} (f : α → β → Prop) :
    WRPTransformers.VHom (⟨propLat, α⟩ : WRPTransformers.Obj) ⟨propLat, β⟩ where
  γ := Concretization.id
  sup _ := PartialOrder.rel_refl
  meet _ _ := PartialOrder.rel_refl
  bot := PartialOrder.rel_refl
  top := PartialOrder.rel_refl
  eps e := e
  R y x := f x y

/-- The conjoint of `relVHom f` at `Q` holds at `y` when `Q` holds at a value related to `y`
by `f`. -/
theorem relVHom_conj_pred {α β : Type u'} (f : α → β → Prop) (Q : α → Prop) (y : β) :
    (relVHom f).conj.pred Q y ↔ ∃ x, f x y ∧ Q x := by
  simp [WRPTransformers.VHom.conj, Concretization.conjoint, Concretization.post, relVHom,
    Concretization.id, iSup_prop_eq_exists, meet_prop_eq_and]

/-- `relVHom` sends equality to the identity vertical arrow. -/
theorem relVHom_id (α : Type u') :
    relVHom (fun x y : α => x = y) = WRPTransformers.VHom.id ⟨propLat, α⟩ := by
  apply WRPTransformers.VHom.ext
  · rfl
  · rfl
  · funext y x
    simp [relVHom, WRPTransformers.VHom.id, eqRel, eq_comm]

/-- `relVHom` sends a relational composite to the composite vertical arrow. -/
theorem relVHom_comp {α β γ : Type u'} (f : α → β → Prop) (g : β → γ → Prop) :
    relVHom (Relation.Comp f g) = (relVHom f).comp (relVHom g) := by
  apply WRPTransformers.VHom.ext
  · rfl
  · rfl
  · funext z x
    simp [relVHom, WRPTransformers.VHom.comp, Concretization.relComp, Concretization.id,
      Relation.Comp, iSup_prop_eq_exists, meet_prop_eq_and, and_comm]

variable {C : Type u} {X : C → Type u'} [Category.{w} (Hor C)]

/-- A lax square of relations is a square of the demonic transformers of its horizontal sides
between the vertical arrows of its vertical sides. -/
theorem laxSq_iff_sq (S : RelSemantics X) {a b c d : C} (u : Hor.of a ⟶ Hor.of b)
    (f : X a → X c → Prop) (g : X b → X d → Prop) (w : Hor.of c ⟶ Hor.of d) :
    S.LaxSq u f g w ↔
      WRPTransformers.Sq (.mk (boxTrans (S.sem u))) (relVHom f) (relVHom g)
        (.mk (boxTrans (S.sem w))) := by
  change _ ↔ _ = _ ∧ _ = _ ∧ ∀ Q E, _
  refine ⟨fun h => ⟨rfl, rfl, ?_⟩, fun ⟨_, _, h⟩ => ?_⟩
  · intro Q _ y hy y' hw
    obtain ⟨x, hf, hQ⟩ := (relVHom_conj_pred f _ y).1 hy
    obtain ⟨x', hu, hg⟩ := h x y y' hf hw
    exact (relVHom_conj_pred g Q y').2 ⟨x', hg, hQ x' hu⟩
  · intro x y y' hf hw
    have h1 := (h (fun x' => S.sem u x x') () y : _ → _)
      ((relVHom_conj_pred f _ y).2 ⟨x, hf, fun _ hx' => hx'⟩) y' hw
    obtain ⟨x', hg, hu⟩ := (relVHom_conj_pred g _ y').1 h1
    exact ⟨x', hu, hg⟩

/-- The level of a relational semantics: the programs of the horizontal category, the
carriers as value types, the assertions `Prop` and the demonic weakest precondition. -/
def relLevel (S : RelSemantics X) : WRPLevels.CatLevel.{u, w, u', 0, 0} where
  Ob := Hor C
  carrier a := X a.as
  lat := propLat
  wp u := boxTrans (S.sem u)
  wp_id a := by
    change boxTrans (S.sem (𝟙 (Hor.of a.as))) = _
    rw [S.sem_id]
    exact boxTrans_eq _
  wp_comp {A B D} f g :=
    (congrArg boxTrans (S.sem_comp (a := A.as) (b := B.as) (c := D.as) f g)).trans
      (boxTrans_comp _ _)

/-- The family with the single level `relLevel S`. -/
abbrev relFamily (S : RelSemantics X) : Unit → WRPLevels.CatLevel.{u, w, u', 0, 0} :=
  fun _ => relLevel S

/-- The thin double functor from the lax squares of relations over `S` into the refinement
squares of `relFamily S`: an object `a` goes to `a` at the single level, a relation `f` to
`relVHom f`, and a horizontal arrow to itself as a program of the level. -/
noncomputable def relDouble (S : RelSemantics X) :
    @ThinDoubleFunctor C (relCategory X) _ (ofRelSemantics S) (WRPLevels.Obj (relFamily S))
      _ _ _ :=
  letI := relCategory X
  letI := ofRelSemantics S
  { obj a := ⟨(), Hor.of a⟩
    mapV f := relVHom f
    mapH u := WRPLevels.HHom.mk (i := ()) u
    mapV_id a := relVHom_id (X a)
    mapV_comp f g := relVHom_comp f g
    mapH_id _ := rfl
    mapH_comp _ _ := rfl
    map_sq s := (laxSq_iff_sq S _ _ _ _).1 s }

/-- `relDouble S` is full on squares: a lax square of relations holds if and only if its image
refinement square holds. -/
theorem relDouble_sq_iff (S : RelSemantics X) {a b c d : C} (u : Hor.of a ⟶ Hor.of b)
    (f : X a → X c → Prop) (g : X b → X d → Prop) (w : Hor.of c ⟶ Hor.of d) :
    letI := relCategory X
    letI := ofRelSemantics S
    ThinDoubleCategory.Sq (a := a) (b := b) (c := c) (d := d) u f g w ↔
      ThinDoubleCategory.Sq ((relDouble S).mapH u) ((relDouble S).mapV (a := a) (c := c) f)
        ((relDouble S).mapV (a := b) (c := d) g) ((relDouble S).mapH w) :=
  laxSq_iff_sq S u f g w

/-- A refinement square of `relDouble S` with top `u`, left `f`, right `g` and bottom `w`:
every postcondition `Q` that `u` establishes from an input related to `y` by `f`, `w`
establishes from `y` up to `g`. -/
theorem relDouble_sq_iff_box (S : RelSemantics X) {a b c d : C} (u : Hor.of a ⟶ Hor.of b)
    (f : X a → X c → Prop) (g : X b → X d → Prop) (w : Hor.of c ⟶ Hor.of d) :
    letI := relCategory X
    letI := ofRelSemantics S
    ThinDoubleCategory.Sq ((relDouble S).mapH u) ((relDouble S).mapV (a := a) (c := c) f)
        ((relDouble S).mapV (a := b) (c := d) g) ((relDouble S).mapH w) ↔
      ∀ (Q : X b → Prop) (y : X c), (∃ x, f x y ∧ ∀ x', S.sem u x x' → Q x') →
        ∀ y', S.sem w y y' → ∃ x', g x' y' ∧ Q x' := by
  refine (relDouble_sq_iff S u f g w).symm.trans ⟨fun h => ?_, fun h => ?_⟩
  · intro Q y ⟨x, hf, hQ⟩ y' hw
    obtain ⟨x', hu, hg⟩ := h x y y' hf hw
    exact ⟨x', hg, hQ x' hu⟩
  · intro x y y' hf hw
    obtain ⟨x', hg, hu⟩ := h (S.sem u x) y ⟨x, hf, fun _ hx => hx⟩ y' hw
    exact ⟨x', hu, hg⟩

end CatCrypt.Refinement.WRPRelSemantics
