/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.PolyRGraph

/-!
# The universe of the polynomial model over the reflexive-graph model

This module gives the universe of containers of the polynomial model of
`CatCryptCore.Container.PolyRGraph`, after the construction of Cavallo and Höfer (§3) of the
universe of `Poly(M)` from a universe of `M`, and in the layout of
`CatCryptCore.Container.RGraphUniverse`.

A code of the universe is a container `PFunctor.{u, u}`. As in the base model, where the universe
is the context extension `RGraphCwF.extU`, the universe is a context extension `extU`: its shapes
are pairs of a shape of the context and a code, and its positions are those of the context, since
the universe has no positions. An edge of the shapes between two codes `P` and `Q` is an edge of the
context with a dependent signature relation (`DSigRel P Q`): a relation of shapes and, over each
witness that two shapes are related, a relation of positions. The reflexive edge carries the
identity relation (`DSigRel.id`). The decoding `El` has the shapes of the code as shapes and its
positions as positions, related by the relation of the edge.

Relativity. Over a fixed edge of the context, the edges of the universe are in bijection with the
dependent signature relations between the two codes (`relativity`), through the relation read by
`El` (`bridgeRel`) and the edge of a relation (`gel`).

The product over the universe (`Ty.piU`) has as shapes the families of shapes that preserve every
relation between codes, and as positions a code with a position of the family at it. Positions are
related over an edge only at the identity relation of their common code: identity extension forces
two positions related over a reflexive edge to be equal, so a positions relation over an arbitrary
relation of codes is not available while relations are propositions. Abstraction over the universe
(`Tm.lamU`) is defined over every context; application (`Tm.appU`) is defined over the empty
context, which has no positions, and there the two are mutually inverse (`Tm.lamUEquiv`).

Free theorem. Every closed term of `Π (X : U). X → X` has, at every code, the identity shape
(`Tm.polyId_shape_eq`): its forward map on shapes is the identity, and its backward map on positions
is total and the identity. Totality holds because the positions on which the backward map is
undefined are positions of the term's type, which a closed term maps back into the empty positions
of the empty context; the identity follows from parametricity at the code with one shape and one
position.

## Main definitions

* `DSigRel`, `DSigRel.id` — dependent signature relations between codes and the identity;
* `extUA`, `extU`, `wkU`, `El` — the universe extension and its decoding;
* `bridgeRel`, `gel`, `relativity`, `relativityClosed` — relativity;
* `Ty.piU`, `Tm.lamU`, `Tm.appU` — the product over the universe;
* `polyIdTy`, `idShape` — the type `Π (X : U). X → X` and the identity shape at a code.

## Main results

* `bridgeRel_gel`, `gel_bridgeRel`, `relativity` — relativity for containers;
* `bridgeRel_refl`, `gel_refl` — the reflexive edge of the universe;
* `Tm.appU_lamU`, `Tm.lamU_appU`, `Tm.lamUEquiv` — the product over the universe at the empty
  context;
* `Tm.polyId_fwd`, `Tm.polyId_back`, `Tm.polyId_shape_eq` — every closed term of
  `Π (X : U). X → X` has identity forward and identity backward maps.

## References

* E. Cavallo, T. Höfer, *Univalence without function extensionality*, arXiv:2605.00812, §3;
* E. Cavallo, R. Harper, *Internal parametricity for cubical type theory*, CSL 2020, LIPIcs 152;
* R. Atkey, N. Ghani, P. Johann, *A relationally parametric model of dependent type theory*,
  POPL 2014;
* S. Moss, T. von Glehn, *Dialectica models of type theory*, LICS 2018, §6.

Search words: universe, polynomial model, container model, reflexive graph, relativity, Gel type,
bridge, relational parametricity, free theorem, polymorphic identity, lens, signature relation.
-/

set_option autoImplicit false

@[expose] public section

universe u

namespace CatCrypt.Container.PolyRGraph

/-! ## Dependent signature relations -/

/-- A dependent signature relation between two containers: a relation of shapes and, over each
witness that two shapes are related, a relation of positions. -/
structure DSigRel (P Q : PFunctor.{u, u}) : Type u where
  /-- The relation of shapes. -/
  pos : P.A → Q.A → Prop
  /-- The relation of positions over a witness that the shapes are related. -/
  dir : ∀ a b, pos a b → P.B a → Q.B b → Prop

/-- The identity dependent signature relation: equality of shapes, heterogeneous equality of
positions. -/
def DSigRel.id (P : PFunctor.{u, u}) : DSigRel P P :=
  ⟨fun a b => a = b, fun _ _ _ x y => HEq x y⟩

/-! ## The universe extension -/

/-- The reflexive graph of shapes of the universe extension: a shape of the context with a code,
an edge of the context with a dependent signature relation, and the identity relation on the
reflexive edge. -/
def extUA (Γ : RGraphCwF.Ctx.{u + 1}) : RGraphCwF.Ctx.{u + 1} where
  V := Γ.V × PFunctor.{u, u}
  E p q := Γ.E p.1 q.1 × DSigRel p.2 q.2
  refl p := (Γ.refl p.1, DSigRel.id p.2)

/-- The projection from the shapes of the universe extension. -/
def wkUA (Γ : RGraphCwF.Ctx.{u + 1}) : RGraphCwF.Hom (extUA Γ) Γ where
  map := Prod.fst
  rel := Prod.fst
  rel_refl _ := rfl

/-- The extension of a context by the universe: shapes extended by a code, positions those of the
context. -/
def extU (Γ : Ctx.{u + 1}) : Ctx.{u + 1} := ⟨extUA Γ.A, Γ.B.sub (wkUA Γ.A)⟩

/-- Weakening of the universe variable. -/
def wkU (Γ : Ctx.{u + 1}) : Hom (extU Γ) Γ where
  f := wkUA Γ.A
  b := ⟨fun p => p.2, fun e => e.2⟩

/-- The decoding of the universe variable: the shapes and positions of the code, related by the
relation of the edge. -/
def El (Γ : Ctx.{u + 1}) : Ty (extU Γ) where
  S := ⟨fun p => ULift.{u + 1} p.2.A, fun e a b => e.2.pos a.down b.down,
    fun _ _ _ => ULift.ext_iff.symm⟩
  P := ⟨fun q => ULift.{u + 1} (q.1.2.B q.2.down), fun e x y => e.1.2.dir _ _ e.2 x.down y.down,
    fun _ _ _ => heq_iff_eq.trans ULift.ext_iff.symm⟩

/-! ## Relativity -/

section Relativity

variable {Γ : Ctx.{u + 1}}

/-- The dependent signature relation between two codes that an edge of the universe carries, read
through the decoding `El`. -/
def bridgeRel {p q : (extU Γ).A.V} (c : (extU Γ).A.E p q) : DSigRel p.2 q.2 :=
  ⟨fun a b => (El Γ).S.E c ⟨a⟩ ⟨b⟩,
    fun a b r x y => (El Γ).P.E (γ := ⟨p, ⟨a⟩⟩) (γ' := ⟨q, ⟨b⟩⟩) ⟨c, r⟩ ⟨x⟩ ⟨y⟩⟩

/-- The edge of the universe over an edge of the context with a given dependent signature
relation, the Gel type of Cavallo and Harper. -/
def gel {p q : (extU Γ).A.V} (e : Γ.A.E p.1 q.1) (R : DSigRel p.2 q.2) : (extU Γ).A.E p q :=
  (e, R)

/-- The relation of the edge of a relation is that relation (an unfolding lemma of `gel`). -/
theorem bridgeRel_gel {p q : (extU Γ).A.V} (e : Γ.A.E p.1 q.1) (R : DSigRel p.2 q.2) :
    bridgeRel (gel e R) = R := rfl

/-- Every edge of the universe is the edge of its relation over its edge of the context (an
unfolding lemma of `bridgeRel`). -/
theorem gel_bridgeRel {p q : (extU Γ).A.V} (c : (extU Γ).A.E p q) : gel c.1 (bridgeRel c) = c :=
  rfl

/-- **Relativity for containers.** Over an edge `e` of the context, the edges of the universe
between two codes are in bijection with the dependent signature relations between them. -/
def relativity {p q : (extU Γ).A.V} (e : Γ.A.E p.1 q.1) :
    {c : (extU Γ).A.E p q // c.1 = e} ≃ DSigRel p.2 q.2 where
  toFun c := bridgeRel c.1
  invFun R := ⟨gel e R, rfl⟩
  left_inv := by
    rintro ⟨c, rfl⟩
    rfl
  right_inv _ := rfl

/-- Relativity at the empty context: the edges of the closed universe between two codes are the
dependent signature relations between them. -/
def relativityClosed (P Q : PFunctor.{u, u}) :
    (extU unit.{u + 1}).A.E (⟨⟩, P) (⟨⟩, Q) ≃ DSigRel P Q where
  toFun c := bridgeRel c
  invFun R := gel (Γ := unit) ⟨⟩ R
  left_inv _ := rfl
  right_inv _ := rfl

/-- The relation of the reflexive edge of the universe is the identity (an unfolding lemma of
`bridgeRel`). -/
theorem bridgeRel_refl (p : (extU Γ).A.V) : bridgeRel ((extU Γ).A.refl p) = DSigRel.id p.2 :=
  rfl

/-- The edge of the identity relation over a reflexive edge is the reflexive edge of the
universe (an unfolding lemma of `gel`). -/
theorem gel_refl (p : (extU Γ).A.V) :
    gel (Γ.A.refl p.1) (DSigRel.id p.2) = (extU Γ).A.refl p := rfl

end Relativity

/-! ## The product over the universe -/

section PiU

variable {Γ : Ctx.{u + 1}}

/-- The shapes of the product over the universe: the families of shapes that preserve every
relation between codes. -/
def piUS (B : Ty (extU Γ)) : RGraphCwF.Ty Γ.A where
  V γ := {f : ∀ X : PFunctor.{u, u}, B.S.V (γ, X) //
    ∀ (X Y : PFunctor.{u, u}) (R : DSigRel X Y), B.S.E (Γ.A.refl γ, R) (f X) (f Y)}
  E e f g := ∀ (X Y : PFunctor.{u, u}) (R : DSigRel X Y), B.S.E (e, R) (f.1 X) (g.1 Y)
  refl_iff γ f g := by
    constructor
    · intro h
      exact Subtype.ext (funext fun X => (B.S.refl_iff (γ, X) _ _).mp (h X X (DSigRel.id X)))
    · rintro rfl
      exact f.2

/-- The relation of positions of the product over the universe over an edge: two positions at the
same code, related over the identity relation of that code. -/
inductive PiUPosRel (B : Ty (extU Γ)) {γ γ' : Γ.A.V} (e : Γ.A.E γ γ') (f : (piUS B).V γ)
    (g : (piUS B).V γ') (r : (piUS B).E e f g) :
    (Σ X : PFunctor.{u, u}, B.P.V ⟨(γ, X), f.1 X⟩) →
      (Σ X : PFunctor.{u, u}, B.P.V ⟨(γ', X), g.1 X⟩) → Prop
  | mk (X : PFunctor.{u, u}) (y : B.P.V ⟨(γ, X), f.1 X⟩) (y' : B.P.V ⟨(γ', X), g.1 X⟩) :
    B.P.E (γ := ⟨(γ, X), f.1 X⟩) (γ' := ⟨(γ', X), g.1 X⟩) ⟨(e, DSigRel.id X), r X X _⟩ y y' →
      PiUPosRel B e f g r ⟨X, y⟩ ⟨X, y'⟩

/-- Induction on the relation of positions of the product over the universe: a property of pairs
of positions that holds at related positions of a common code holds at every related pair. -/
theorem PiUPosRel.induction {B : Ty (extU Γ)} {γ γ' : Γ.A.V} {e : Γ.A.E γ γ'}
    {f : (piUS B).V γ} {g : (piUS B).V γ'} {r : (piUS B).E e f g}
    {C : (Σ X : PFunctor.{u, u}, B.P.V ⟨(γ, X), f.1 X⟩) →
      (Σ X : PFunctor.{u, u}, B.P.V ⟨(γ', X), g.1 X⟩) → Prop}
    (k : ∀ (X : PFunctor.{u, u}) (y : B.P.V ⟨(γ, X), f.1 X⟩) (y' : B.P.V ⟨(γ', X), g.1 X⟩),
      B.P.E (γ := ⟨(γ, X), f.1 X⟩) (γ' := ⟨(γ', X), g.1 X⟩) ⟨(e, DSigRel.id X), r X X _⟩ y y' →
        C ⟨X, y⟩ ⟨X, y'⟩)
    {x x'} (h : PiUPosRel B e f g r x x') : C x x' := by
  cases h with
  | mk X y y' hy => exact k X y y' hy

/-- The dependent product over the universe: shapes are the parametric families of shapes,
positions a code with a position of the family at it. -/
def Ty.piU (B : Ty (extU Γ)) : Ty Γ where
  S := piUS B
  P := ⟨fun p => Σ X : PFunctor.{u, u}, B.P.V ⟨(p.1, X), p.2.1 X⟩,
    fun {p q} e x y => PiUPosRel B e.1 p.2 q.2 e.2 x y,
    fun p x y => by
      constructor
      · rintro ⟨X, z, z', h⟩
        obtain rfl := (B.P.refl_iff ⟨(p.1, X), p.2.1 X⟩ z z').mp h
        rfl
      · rintro rfl
        obtain ⟨X, z⟩ := x
        exact .mk X z z ((B.P.refl_iff ⟨(p.1, X), p.2.1 X⟩ z z).mpr rfl)⟩

/-- λ-abstraction over the universe. -/
def Tm.lamU {B : Ty (extU Γ)} (t : Tm (extU Γ) B) : Tm Γ (Ty.piU B) where
  S := ⟨fun γ => ⟨fun X => t.S.V (γ, X),
      fun X Y R => t.S.E (γ := (γ, X)) (γ' := (γ, Y)) (Γ.A.refl γ, R)⟩,
    fun {γ γ'} e X Y R => t.S.E (γ := (γ, X)) (γ' := (γ', Y)) (e, R)⟩
  P := ⟨fun p => t.P.V ⟨(p.1, p.2.1), p.2.2⟩, fun {p q} e => by
    obtain ⟨γ, x⟩ := p
    obtain ⟨γ', x'⟩ := q
    obtain ⟨e0, h⟩ := e
    exact PiUPosRel.induction
      (C := fun (x : Σ X : PFunctor.{u, u}, B.P.V ⟨(γ, X), t.S.V (γ, X)⟩)
        (x' : Σ X : PFunctor.{u, u}, B.P.V ⟨(γ', X), t.S.V (γ', X)⟩) =>
          Γ.B.E e0 (t.P.V ⟨(γ, x.1), x.2⟩) (t.P.V ⟨(γ', x'.1), x'.2⟩))
      (fun X y y' hy => t.P.E (γ := ⟨(γ, X), y⟩) (γ' := ⟨(γ', X), y'⟩)
        ⟨(e0, DSigRel.id X), hy⟩) h⟩

/-- Application to the universe variable at the empty context. -/
def Tm.appU {B : Ty (extU unit.{u + 1})} (f : Tm unit (Ty.piU B)) : Tm (extU unit) B where
  S := ⟨fun p => (f.S.V p.1).1 p.2, fun e => f.S.E e.1 _ _ e.2⟩
  P := ⟨fun q => f.P.V ⟨q.1.1, ⟨q.1.2, q.2⟩⟩,
    fun {q} _ => PEmpty.elim (f.P.V ⟨q.1.1, ⟨q.1.2, q.2⟩⟩)⟩

/-- The β law of the product over the universe at the empty context. -/
theorem Tm.appU_lamU {B : Ty (extU unit.{u + 1})} (t : Tm (extU unit) B) :
    Tm.appU (Tm.lamU t) = t := by
  obtain ⟨S, P⟩ := t
  exact Tm.ext_P fun p => PEmpty.elim (P.V p)

/-- The η law of the product over the universe at the empty context. -/
theorem Tm.lamU_appU {B : Ty (extU unit.{u + 1})} (f : Tm unit (Ty.piU B)) :
    Tm.lamU (Tm.appU f) = f := by
  obtain ⟨S, P⟩ := f
  exact Tm.ext_P fun p => PEmpty.elim (P.V p)

/-- **Closed terms of the product over the universe are the terms in the context of the
universe.** -/
def Tm.lamUEquiv {B : Ty (extU unit.{u + 1})} : Tm (extU unit) B ≃ Tm unit (Ty.piU B) where
  toFun := Tm.lamU
  invFun := Tm.appU
  left_inv := Tm.appU_lamU
  right_inv := Tm.lamU_appU

end PiU

/-! ## The free theorem of the polymorphic identity -/

section FreeTheorem

/-- The type `X → X` in the context of the universe. -/
abbrev endoTy : Ty (extU unit.{u + 1}) :=
  Ty.pi (El unit) ((El unit).sub (wk (El unit)))

/-- The type `Π (X : U). X → X`. -/
def polyIdTy : Ty unit.{u + 1} := Ty.piU endoTy

/-- The identity shape of `X → X` at a code: the identity on shapes, and the total identity on
positions. -/
def idShape (X : PFunctor.{u, u}) : endoTy.S.V ((⟨⟩ : unit.{u + 1}.A.V), X) :=
  ⟨fun a => a, fun _ y => some y⟩

/-- Two lifts with heterogeneously equal contents are heterogeneously equal. -/
theorem heq_of_heq_down {α β : Type u} {x : ULift.{u + 1} α} {y : ULift.{u + 1} β}
    (h : HEq x.down y.down) : HEq x y := by
  obtain rfl := type_eq_of_heq h
  exact heq_of_eq (ULift.ext (eq_of_heq h))

/-- Two options related with a defined right side have a defined left side, related to it. -/
theorem optionRel_some_of_isSome {α β : Type (u + 1)} {R : α → β → Prop} {x : Option α}
    {y : Option β} (h : Option.Rel R x y) (hy : y.isSome) : ∃ d d', x = some d ∧ R d d' := by
  cases h with
  | none => simp at hy
  | some h => exact ⟨_, _, rfl, h⟩

variable (t : Tm unit polyIdTy.{u})

/-- The backward map of a closed term of `Π (X : U). X → X` is total: a position on which it is
undefined is a position of the type, which the term maps into the empty positions of the empty
context. -/
theorem Tm.polyId_back_isSome (X : PFunctor.{u, u}) (a : ULift.{u + 1} X.A)
    (y : ULift.{u + 1} (X.B ((t.S.V ⟨⟩).1 X |>.fwd a).down)) :
    (((t.S.V ⟨⟩).1 X).back a y).isSome := by
  rcases h : ((t.S.V ⟨⟩).1 X).back a y with _ | d
  · exact PEmpty.elim (t.P.V ⟨⟨⟩, ⟨X, ⟨⟨a, y⟩, h⟩⟩⟩)
  · rfl

/-- **The forward map of a closed term of `Π (X : U). X → X` is the identity.** -/
theorem Tm.polyId_fwd (X : PFunctor.{u, u}) (a : ULift.{u + 1} X.A) :
    ((t.S.V ⟨⟩).1 X).fwd a = a := by
  have h := ((t.S.V ⟨⟩).2 X ⟨PUnit, fun _ => PEmpty⟩
    ⟨fun a' _ => a' = a.down, fun _ _ _ _ _ => True⟩).1 a ⟨⟨⟩⟩ rfl
  exact ULift.ext h

/-- **The backward map of a closed term of `Π (X : U). X → X` is the identity.** -/
theorem Tm.polyId_back (X : PFunctor.{u, u}) (a : ULift.{u + 1} X.A)
    (y : ULift.{u + 1} (X.B ((t.S.V ⟨⟩).1 X |>.fwd a).down)) :
    ∃ d, ((t.S.V ⟨⟩).1 X).back a y = some d ∧ HEq d y := by
  have hf := Tm.polyId_fwd t X a
  have h := ((t.S.V ⟨⟩).2 X ⟨PUnit, fun _ => PUnit⟩
    ⟨fun a' _ => a' = a.down, fun _ _ _ z _ => HEq z y.down⟩).2 a ⟨⟨⟩⟩ rfl
    (congrArg ULift.down hf) y ⟨⟨⟩⟩ HEq.rfl
  obtain ⟨d, _, hd, hr⟩ := optionRel_some_of_isSome h
    (Tm.polyId_back_isSome t ⟨PUnit, fun _ => PUnit⟩ ⟨⟨⟩⟩ ⟨⟨⟩⟩)
  exact ⟨d, hd, heq_of_heq_down hr⟩

/-- **Free theorem.** At every code, a closed term of `Π (X : U). X → X` has the identity shape:
identity forward map on shapes and identity backward map on positions. -/
theorem Tm.polyId_shape_eq (X : PFunctor.{u, u}) : (t.S.V ⟨⟩).1 X = idShape X := by
  refine CwF.PiShape.ext_iff_cast.mpr ⟨funext (Tm.polyId_fwd t X), fun a y => ?_⟩
  obtain ⟨d, hd, hdy⟩ := Tm.polyId_back t X a y
  rw [hd]
  unfold idShape
  grind

end FreeTheorem

end CatCrypt.Container.PolyRGraph
