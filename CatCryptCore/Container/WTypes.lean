/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import PolyFun.IPFunctor.Basic
public import Mathlib.Data.W.Basic

/-!
# W-types of containers, their maps and their relators

An indexed container `P : IPFunctor I I` (PolyFun's indexed polynomial: shapes `P.A i` at each
index, positions `P.B i a` at a shape, and the index `P.src i a b` of the child at a position) has
the indexed W-type `IPW P : I → Type`, the initial algebra of its extension: a node at the index
`i` is a shape `a : P.A i` with a child at the index `P.src i a b` for each position `b`. An
unindexed container has Mathlib's `WType` of its positions. These are the W-types of the
polynomial model (von Glehn, *Polynomials and models of type theory*, 2015; Gambino and Hyland,
*Wellfounded trees and dependent polynomial functors*, TYPES 2003).

The containers of the inductive types of D have shapes a constructor with its field and positions
that depend on the constructor only. For them, `wmapF` and `iwmapF` map the fields of the W-type,
and `WLift` and `IWLift` lift a relation on the fields of each constructor to the W-type (two
nodes of one constructor with related fields and related children): the relators of the
W-types, through which the logical relations of D (`CatCrypt.Complexity.D.ValRel`,
`CatCrypt.Complexity.D.Sim`) are defined at inductive types. The values of an inductive type of D
are the `WType` of its container (`CatCrypt.Complexity.D.Sig.den`) and those of an indexed family
the `IPW` of its indexed container (`CatCrypt.Complexity.D.IW`).

## Main definitions

* `IPW`: the indexed W-type of an indexed container;
* `wmapF`, `iwmapF`: the maps of the fields;
* `WLift`, `IWLift`: the relators.

## Main results

* `WLift.iff_eq`, `IWLift.iff_eq`: the lifting of equality is equality;
* `cast_wmapF`, `cast_iwmapF`: a cast between W-types whose fields are cast is the map of the cast
  of the fields.

Search words: indexed W-type, inductive family, indexed container, indexed polynomial functor,
initial algebra, well-founded tree, relator, relational lifting.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Container

/-- The indexed W-type of the indexed container `P`: at the index `i`, a shape `a : P.A i` and, at
each position `b : P.B i a`, a child at the index `P.src i a b`. -/
inductive IPW {I : Type} (P : IPFunctor.{0, 0, 0, 0} I I) : I → Type where
  /-- A node: its index, its shape and its children. -/
  | mk (i : I) (a : P.A i) (k : (b : P.B i a) → IPW P (P.src i a b)) : IPW P i

/-- The map of the fields of an indexed W-type whose shapes are a constructor with its field. -/
def iwmapF {I : Type} {C : I → Type} {F G P : (i : I) → C i → Type}
    {nx : (i : I) → (c : C i) → P i c → I} (m : (i : I) → (c : C i) → F i c → G i c) :
    {i : I} → IPW ⟨fun i => (c : C i) × F i c, fun i a => P i a.1, fun i a p => nx i a.1 p⟩ i →
      IPW ⟨fun i => (c : C i) × G i c, fun i a => P i a.1, fun i a p => nx i a.1 p⟩ i
  | _, .mk i ⟨c, x⟩ k => .mk i ⟨c, m i c x⟩ fun p => iwmapF m (k p)

/-- The map of the fields of a W-type whose shapes are a constructor with its field. -/
def wmapF {C : Type} {F G P : C → Type} (m : (c : C) → F c → G c) :
    WType (fun s : (c : C) × F c => P s.1) → WType (fun s : (c : C) × G c => P s.1)
  | ⟨⟨c, x⟩, k⟩ => ⟨⟨c, m c x⟩, fun p => wmapF m (k p)⟩

/-- The lifting of a relation on the fields of the constructors to W-types whose shapes are a
constructor with its field and whose positions depend on the constructor only: two nodes are
related when they have the same constructor, related fields and related children. -/
inductive WLift {C : Type} {F G P : C → Type} (R : (c : C) → F c → G c → Prop) :
    WType (fun s : (c : C) × F c => P s.1) → WType (fun s : (c : C) × G c => P s.1) → Prop
  | mk {c : C} {x : F c} {y : G c} {k : P c → WType (fun s : (c : C) × F c => P s.1)}
      {k' : P c → WType (fun s : (c : C) × G c => P s.1)} :
      R c x y → (∀ p, WLift R (k p) (k' p)) → WLift R ⟨⟨c, x⟩, k⟩ ⟨⟨c, y⟩, k'⟩

/-- The lifting of equality is equality. -/
theorem WLift.iff_eq {C : Type} {F P : C → Type} {R : (c : C) → F c → F c → Prop}
    (hR : ∀ c x y, R c x y ↔ x = y) (u v : WType (fun s : (c : C) × F c => P s.1)) :
    WLift R u v ↔ u = v := by
  constructor
  · intro h
    induction h with
    | mk hxy _ ih =>
      rw [(hR _ _ _).1 hxy, funext ih]
  · rintro rfl
    induction u with
    | mk a k ih =>
      obtain ⟨c, x⟩ := a
      exact .mk ((hR c x x).2 rfl) ih

/-- The lifting of a relation on the fields of the constructors to indexed W-types whose shapes
are a constructor with its field: two nodes at one index are related when they have the same
constructor, related fields and related children. -/
inductive IWLift {I : Type} {C : I → Type} {F G P : (i : I) → C i → Type}
    {nx : (i : I) → (c : C i) → P i c → I} (R : (i : I) → (c : C i) → F i c → G i c → Prop) :
    {i : I} → IPW ⟨fun i => (c : C i) × F i c, fun i a => P i a.1, fun i a p => nx i a.1 p⟩ i →
      IPW ⟨fun i => (c : C i) × G i c, fun i a => P i a.1, fun i a p => nx i a.1 p⟩ i → Prop
  | mk {i : I} {c : C i} {x : F i c} {y : G i c}
      {k : (p : P i c) →
        IPW ⟨fun i => (c : C i) × F i c, fun i a => P i a.1, fun i a p => nx i a.1 p⟩ (nx i c p)}
      {k' : (p : P i c) →
        IPW ⟨fun i => (c : C i) × G i c, fun i a => P i a.1, fun i a p => nx i a.1 p⟩ (nx i c p)} :
      R i c x y → (∀ p, IWLift R (k p) (k' p)) → IWLift R (IPW.mk i ⟨c, x⟩ k) (IPW.mk i ⟨c, y⟩ k')

/-- The lifting of equality to indexed W-types is equality. -/
theorem IWLift.iff_eq {I : Type} {C : I → Type} {F P : (i : I) → C i → Type}
    {nx : (i : I) → (c : C i) → P i c → I} {R : (i : I) → (c : C i) → F i c → F i c → Prop}
    (hR : ∀ i c x y, R i c x y ↔ x = y) {i : I}
    (u v : IPW ⟨fun i => (c : C i) × F i c, fun i a => P i a.1, fun i a p => nx i a.1 p⟩ i) :
    IWLift R u v ↔ u = v := by
  constructor
  · intro h
    induction h with
    | mk hxy _ ih => rw [(hR _ _ _ _).1 hxy, funext ih]
  · rintro rfl
    induction u with
    | mk i a k ih =>
      obtain ⟨c, x⟩ := a
      exact .mk ((hR i c x x).2 rfl) ih

/-- A cast between indexed W-types whose fields are cast is the map of the cast of the
fields. -/
theorem cast_iwmapF {I : Type} {C : I → Type} {F G P : (i : I) → C i → Type}
    {nx : (i : I) → (c : C i) → P i c → I} (e : ∀ i c, F i c = G i c) {i : I}
    (p : IPW ⟨fun i => (c : C i) × F i c, fun i a => P i a.1, fun i a p => nx i a.1 p⟩ i =
      IPW ⟨fun i => (c : C i) × G i c, fun i a => P i a.1, fun i a p => nx i a.1 p⟩ i)
    (u : IPW ⟨fun i => (c : C i) × F i c, fun i a => P i a.1, fun i a p => nx i a.1 p⟩ i) :
    cast p u = iwmapF (fun i c x => cast (e i c) x) u := by
  have hFG : F = G := funext fun i => funext (e i)
  subst hFG
  simp only [cast_eq]
  clear p e
  induction u with
  | mk i a k ih =>
    obtain ⟨c, x⟩ := a
    rw [iwmapF]
    exact congrArg _ (funext ih)

/-- A cast between W-types whose fields are cast is the map of the cast of the fields. -/
theorem cast_wmapF {C : Type} {F G P : C → Type} (e : ∀ c, F c = G c)
    (p : WType (fun s : (c : C) × F c => P s.1) = WType (fun s : (c : C) × G c => P s.1))
    (u : WType (fun s : (c : C) × F c => P s.1)) :
    cast p u = wmapF (fun c x => cast (e c) x) u := by
  have hFG : F = G := funext e
  subst hFG
  simp only [cast_eq]
  induction u with
  | mk a k ih =>
    obtain ⟨c, x⟩ := a
    show WType.mk ⟨c, x⟩ k = WType.mk ⟨c, x⟩ (fun q => wmapF _ (k q))
    exact congrArg _ (funext ih)

end CatCrypt.Container
