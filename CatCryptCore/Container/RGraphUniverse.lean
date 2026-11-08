/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.PolyRGraph
public import Mathlib.Logic.Equiv.Defs

/-!
# Relativity and free theorems for the universe of the reflexive-graph model

This module states, in shallow form over `Type`, the relativity principle of Cavallo and Harper
for the universe extension `extU` of the reflexive-graph category with families of
`CatCryptCore.Container.RGraphCwF`, the function extensionality of its products along edges, and
free theorems for closed polymorphic terms.

Relativity. An edge of `extU Γ` between `(γ, X)` and `(γ', Y)` is an edge of `Γ` with a relation
`X → Y → Prop`. The relation of an edge read through the decoding `El` (`bridgeRel`) and the edge
built from a relation (`gel`, after the Gel type of Cavallo and Harper) are mutually inverse: over
a fixed edge of `Γ`, the edges of the universe are in bijection with the relations between the
two small types (`relativity`). Over the reflexive edge with the equality relation, `gel` gives the
reflexive edge of the universe, and an endo-edge of the universe is reflexive exactly when it lies
over a reflexive edge and its relation is equality (`eq_refl_iff`).

Function extensionality. Two functions are related over an edge exactly when they send related
arguments to related values (`Ty.pi_E_iff`, `Ty.piU_E_iff`); pointwise equal functions are related
over the reflexive edge (`Ty.pi_E_refl_of_forall_eq`), and terms of a product are determined by
their values at each argument (`Tm.pi_ext`, `Tm.piU_ext`).

Free theorems. A term of `Π (X : U). X → X` over any context is the identity at every vertex
(`Tm.polyIdAt_eq`); a closed term commutes with every function (`Tm.polyId_natural`); the type has
exactly one closed term (`Tm.polyId`, `Tm.polyId_unique`). A closed term of
`Π (X : U). X → X → X` returns, at every type, the argument selected by its value at the booleans
(`Tm.polyChoice_eq`).

## Main definitions

* `bridgeRel`, `gel` — the relation of an edge of the universe and the edge of a relation;
* `relativity` — the bijection between edges of the universe over an edge of `Γ` and relations;
* `Tm.polyId` — the identity term of `Π (X : U). X → X`;
* `polyChoiceTy` — the type `Π (X : U). X → X → X`.

## Main results

* `bridgeRel_gel`, `gel_bridgeRel`, `relativity` — relativity (Cavallo–Harper, Theorem 2.4);
* `bridgeRel_refl`, `gel_refl`, `eq_refl_iff` — the reflexive edge of the universe;
* `Ty.pi_E_iff`, `Ty.piU_E_iff`, `Ty.pi_E_refl_of_forall_eq`, `Tm.pi_ext`, `Tm.piU_ext` —
  function extensionality along edges;
* `Tm.polyIdAt_eq`, `Tm.polyId_natural`, `Tm.polyId_unique`, `Tm.polyChoice_eq` — free theorems.

## References

* E. Cavallo, R. Harper, *Internal parametricity for cubical type theory*, CSL 2020, LIPIcs 152;
  extended version in Logical Methods in Computer Science 17(4), 2021;
* R. Atkey, N. Ghani, P. Johann, *A relationally parametric model of dependent type theory*,
  POPL 2014;
* J. C. Reynolds, *Types, abstraction and parametric polymorphism*, IFIP Congress 1983.

Search words: relativity, Gel type, bridge, universe, relational parametricity, function
extensionality, free theorem, polymorphic identity, Church booleans, reflexive graph.
-/

set_option autoImplicit false

@[expose] public section

universe u

namespace CatCrypt.Container.RGraphCwF

section Relativity

variable {Γ : Ctx.{u + 1}}

/-- The relation between small types that an edge of the universe extension carries, read
through the decoding `El`. -/
def bridgeRel {p q : (extU Γ).V} (c : (extU Γ).E p q) : p.2 → q.2 → Prop :=
  fun a b => (El Γ).E c ⟨a⟩ ⟨b⟩

/-- The edge of the universe extension over an edge of `Γ` with a given relation between the
small types, the Gel type of Cavallo and Harper. -/
def gel {p q : (extU Γ).V} (e : Γ.E p.1 q.1) (R : p.2 → q.2 → Prop) : (extU Γ).E p q :=
  (e, R)

/-- The edge of a relation lies over the given edge of `Γ`. -/
theorem gel_fst {p q : (extU Γ).V} (e : Γ.E p.1 q.1) (R : p.2 → q.2 → Prop) :
    (gel e R).1 = e := rfl

/-- The relation of the edge of a relation is that relation. -/
theorem bridgeRel_gel {p q : (extU Γ).V} (e : Γ.E p.1 q.1) (R : p.2 → q.2 → Prop) :
    bridgeRel (gel e R) = R := rfl

/-- Every edge of the universe is the edge of its relation over its edge of `Γ`. -/
theorem gel_bridgeRel {p q : (extU Γ).V} (c : (extU Γ).E p q) : gel c.1 (bridgeRel c) = c :=
  rfl

/-- The decoding `El` relates two elements over the edge of a relation exactly when the relation
holds. -/
theorem El_E_gel {p q : (extU Γ).V} (e : Γ.E p.1 q.1) (R : p.2 → q.2 → Prop)
    (a : (El Γ).V p) (b : (El Γ).V q) : (El Γ).E (gel e R) a b ↔ R a.down b.down := Iff.rfl

/-- Relativity: over an edge `e` of `Γ`, the edges of the universe extension between `(γ, X)`
and `(γ', Y)` are in bijection with the relations `X → Y → Prop`. -/
def relativity {p q : (extU Γ).V} (e : Γ.E p.1 q.1) :
    {c : (extU Γ).E p q // c.1 = e} ≃ (p.2 → q.2 → Prop) where
  toFun c := bridgeRel c.1
  invFun R := ⟨gel e R, rfl⟩
  left_inv := by
    rintro ⟨c, rfl⟩
    rfl
  right_inv _ := rfl

/-- Relativity at the terminal context: the edges of the closed universe between two small types
are in bijection with the relations between them. -/
def relativityClosed (X Y : Type u) :
    (extU unit.{u + 1}).E (⟨⟩, X) (⟨⟩, Y) ≃ (X → Y → Prop) where
  toFun c := bridgeRel c
  invFun R := gel ⟨⟩ R
  left_inv _ := rfl
  right_inv _ := rfl

/-- The relation of the reflexive edge of the universe is equality. -/
theorem bridgeRel_refl (p : (extU Γ).V) : bridgeRel ((extU Γ).refl p) = fun a b => a = b := rfl

/-- The edge of the equality relation over a reflexive edge is the reflexive edge of the
universe. -/
theorem gel_refl (p : (extU Γ).V) :
    gel (Γ.refl p.1) (fun a b : p.2 => a = b) = (extU Γ).refl p := rfl

/-- An endo-edge of the universe is the reflexive edge exactly when it lies over the reflexive
edge of `Γ` and its relation is equality. -/
theorem eq_refl_iff (p : (extU Γ).V) (c : (extU Γ).E p p) :
    c = (extU Γ).refl p ↔ c.1 = Γ.refl p.1 ∧ ∀ a b, bridgeRel c a b ↔ a = b := by
  constructor
  · rintro rfl
    exact ⟨rfl, fun _ _ => Iff.rfl⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨c1, c2⟩ := c
    refine Prod.ext h1 ?_
    funext a b
    exact propext (h2 a b)

end Relativity

section Funext

variable {Γ : Ctx.{u}} {A : Ty Γ} {B : Ty (ext Γ A)}

/-- Function extensionality along edges: two functions are related over an edge exactly when
they send related arguments to related values. -/
theorem Ty.pi_E_iff {γ γ' : Γ.V} (e : Γ.E γ γ') (f : (Ty.pi A B).V γ) (g : (Ty.pi A B).V γ') :
    (Ty.pi A B).E e f g ↔ ∀ a a' (r : A.E e a a'), B.E ⟨e, r⟩ (f a) (g a') := Iff.rfl

/-- Pointwise equal functions are related over the reflexive edge. -/
theorem Ty.pi_E_refl_of_forall_eq {γ : Γ.V} (f g : (Ty.pi A B).V γ) (h : ∀ a, f a = g a) :
    (Ty.pi A B).E (Γ.refl γ) f g :=
  ((Ty.pi A B).refl_iff γ f g).mpr (funext h)

/-- Terms of a product are equal when their values agree at every vertex and argument. -/
theorem Tm.pi_ext {t s : Tm Γ (Ty.pi A B)} (h : ∀ γ a, t.V γ a = s.V γ a) : t = s :=
  PolyRGraph.Base.tm_ext fun γ => funext (h γ)

end Funext

section FunextU

variable {Γ : Ctx.{u + 1}} {B : Ty (extU Γ)}

/-- Function extensionality along edges for the product over the universe: two elements are
related over an edge exactly when they send every relation between small types to a relation
over the corresponding edge of the universe. -/
theorem Ty.piU_E_iff {γ γ' : Γ.V} (e : Γ.E γ γ') (f : (Ty.piU B).V γ) (g : (Ty.piU B).V γ') :
    (Ty.piU B).E e f g ↔ ∀ (X Y : Type u) (R : X → Y → Prop), B.E (gel (p := (γ, X))
      (q := (γ', Y)) e R) (f.1 X) (g.1 Y) := Iff.rfl

/-- Terms of the product over the universe are equal when their values agree at every vertex
and small type. -/
theorem Tm.piU_ext {t s : Tm Γ (Ty.piU B)} (h : ∀ γ X, (t.V γ).1 X = (s.V γ).1 X) : t = s :=
  PolyRGraph.Base.tm_ext fun γ => Subtype.ext (funext (h γ))

end FunextU

section FreeTheorems

/-- A term of `Π (X : U). X → X` over any context is the identity at every vertex. -/
theorem Tm.polyIdAt_eq {Γ : Ctx.{u + 1}}
    (t : Tm Γ (Ty.piU (Ty.pi (El Γ) ((El Γ).sub (wk (El Γ))))))
    (γ : Γ.V) (X : Type u) (x : X) : ((t.V γ).1 X ⟨x⟩).down = x :=
  (t.V γ).2 X PUnit (fun a _ => a = x) ⟨x⟩ ⟨⟨⟩⟩ rfl

/-- A closed term of `Π (X : U). X → X` commutes with every function between small types. -/
theorem Tm.polyId_natural (t : Tm unit polyIdTy.{u}) {X Y : Type u} (f : X → Y) (x : X) :
    ((t.V ⟨⟩).1 Y ⟨f x⟩).down = f ((t.V ⟨⟩).1 X ⟨x⟩).down :=
  ((t.V ⟨⟩).2 X Y (fun a b => f a = b) ⟨x⟩ ⟨f x⟩ rfl).symm

/-- The identity term of `Π (X : U). X → X`. -/
def Tm.polyId : Tm unit polyIdTy.{u} where
  V := fun _ => ⟨fun _ a => a, fun _ _ _ _ _ r => r⟩
  E := fun _ _ _ _ _ _ r => r

/-- The identity is the only closed term of `Π (X : U). X → X`. -/
theorem Tm.polyId_unique (t : Tm unit polyIdTy.{u}) : t = Tm.polyId :=
  Tm.piU_ext fun _ X => funext fun a => ULift.ext (Tm.polyId_eq t X a.down)

instance : Unique (Tm unit polyIdTy.{u}) where
  default := Tm.polyId
  uniq := Tm.polyId_unique

/-- The type `Π (X : U). X → X → X`. -/
def polyChoiceTy : Ty (unit.{u + 1}) :=
  Ty.piU (Ty.pi (El unit) (Ty.pi ((El unit).sub (wk (El unit)))
    ((El unit).sub ((wk (El unit)).comp (wk ((El unit).sub (wk (El unit))))))))

/-- A closed term of `Π (X : U). X → X → X` returns, at every small type, the first argument when
its value at the booleans on `true` and `false` is `true`, and the second otherwise. -/
theorem Tm.polyChoice_eq (t : Tm unit polyChoiceTy.{u}) (X : Type u) (x y : X) :
    ((t.V ⟨⟩).1 X ⟨x⟩ ⟨y⟩).down =
      if ((t.V ⟨⟩).1 (ULift.{u} Bool) ⟨⟨true⟩⟩ ⟨⟨false⟩⟩).down.down then x else y :=
  (t.V ⟨⟩).2 X (ULift.{u} Bool) (fun a b => a = if b.down then x else y)
    ⟨x⟩ ⟨⟨true⟩⟩ rfl ⟨y⟩ ⟨⟨false⟩⟩ rfl

end FreeTheorems

end CatCrypt.Container.RGraphCwF
