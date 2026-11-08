/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.DNRel
public import CatCryptCore.ForMathlib.Difunctional

/-!
# Relations of containers as subobjects of the product

A relation of containers `P` and `Q` in the category of lenses is a subobject of `P * Q`. A lens
into `P * Q` is a monomorphism when its forward map is injective and its backward maps are
surjective, so a subobject is a relation on shapes together with, over each related pair of shapes
`(a, b)`, an equivalence relation on `P.B a ⊕ Q.B b` (`PolyRel`). Its container `PolyRel.toCont`
has the related pairs as shapes and the quotients as positions, and `PolyRel.incl` is the
monomorphism into the product.

A signature relation (`SigRel`) relates the positions of related shapes directly. The two notions
are compared by the maps of `CatCryptCore.ForMathlib.Difunctional` taken fibrewise:
`SigRel.toPolyRel` (`Φ`) takes the equivalence closure of the cross pairs, and `PolyRel.toSigRel`
(`Ψ`) restricts a corelation across the sum. Over each pair of lenses they form an adjunction
`Ψ ⊣ Φ` between squares of signature relations (`SigRel.Square`) and morphisms of relations
(`PolyRel.Hom`). The counit `Ψ Φ S → S` is the difunctional closure and is an isomorphism exactly at
difunctional position relations; the unit `R → Φ Ψ R` is an isomorphism exactly at cross-generated
corelations. The adjunction restricts to an equivalence between these two classes.

## Main definitions

* `PolyRel` — a relation of shapes and a corelation of positions over related shapes
* `PolyRel.toCont`, `PolyRel.incl` — the container of a relation and its inclusion into `P * Q`
* `PolyRel.Hom` — a morphism of relations over a pair of lenses
* `PolyRel.graph` — the graph of a lens, the image of `⟨id, f⟩ : P → P * Q`
* `SigRel.toPolyRel`, `PolyRel.toSigRel` — the comparison maps `Φ` and `Ψ`

## Main results

* `PolyRel.incl_toFunA_injective`, `PolyRel.incl_toFunB_surjective` — the inclusion is mono
* `PolyRel.Hom.id`, `PolyRel.Hom.comp` — relations and their morphisms form a category
* `PolyRel.square_toSigRel_iff` — the comparison adjunction `Ψ ⊣ Φ`
* `PolyRel.hom_toSigRel_toPolyRel`, `SigRel.square_toPolyRel_toSigRel` — unit and counit
* `SigRel.toPolyRel_toSigRel_dir_iff` — the counit is the difunctional closure
* `SigRel.toPolyRel_toSigRel_iff` — the counit is invertible exactly at difunctional relations
* `PolyRel.toSigRel_toPolyRel_iff` — the unit is invertible exactly at cross-generated corelations
* `PolyRel.toSigRel_graph` — the graph of a lens relates positions along its backward map

## References

* D. I. Spivak, *Generalized lens categories via functors `C^op → Cat`*, arXiv:1908.02202.
* J. Riguet, *Relations binaires, fermetures, correspondances de Galois*, Bull. Soc. Math. France
  76 (1948) 114–155.
* S. K. Moss, T. von Glehn, *Dialectica models of type theory*, LICS 2018.
-/

set_option autoImplicit false

@[expose] public section

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ u₅ v₅ u₆ v₆

namespace CatCrypt.Container

open PFunctor

variable {P : PFunctor.{u₁, v₁}} {Q : PFunctor.{u₂, v₂}} {P' : PFunctor.{u₃, v₃}}
  {Q' : PFunctor.{u₄, v₄}} {P'' : PFunctor.{u₅, v₅}} {Q'' : PFunctor.{u₆, v₆}}

/-- A relation of containers in the category of lenses, a subobject of `P * Q`: a relation on
shapes and, over related shapes, an equivalence relation on the sum of the positions. -/
structure PolyRel (P : PFunctor.{u₁, v₁}) (Q : PFunctor.{u₂, v₂}) where
  /-- The relation of shapes. -/
  pos : P.A → Q.A → Prop
  /-- The corelation of positions at two shapes. -/
  cor : ∀ a b, P.B a ⊕ Q.B b → P.B a ⊕ Q.B b → Prop
  /-- Over related shapes the corelation is an equivalence relation. -/
  equiv : ∀ {a b}, pos a b → Equivalence (cor a b)

namespace PolyRel

/-- The container of a relation: related shapes, and the quotient of the positions. -/
def toCont (R : PolyRel P Q) : PFunctor.{max u₁ u₂, max v₁ v₂} where
  A := {ab : P.A × Q.A // R.pos ab.1 ab.2}
  B x := Quot (R.cor x.1.1 x.1.2)

/-- The inclusion of a relation into the product `P * Q`. -/
def incl (R : PolyRel P Q) :
    Lens.{max u₁ u₂, max v₁ v₂, max u₁ u₂, max v₁ v₂} R.toCont (P * Q) where
  toFunA x := x.1
  toFunB _ := Quot.mk _

/-- The forward map of the inclusion is injective. -/
theorem incl_toFunA_injective (R : PolyRel P Q) : Function.Injective R.incl.toFunA :=
  Subtype.val_injective

/-- The backward maps of the inclusion are surjective. -/
theorem incl_toFunB_surjective (R : PolyRel P Q) (x : R.toCont.A) :
    Function.Surjective (R.incl.toFunB x) :=
  Quot.mk_surjective

/-- A morphism of relations over a pair of lenses: related shapes go to related shapes, and
positions related at the images pull back to related positions. -/
structure Hom (R : PolyRel P Q) (R' : PolyRel P' Q') (f : Lens P P') (g : Lens Q Q') :
    Prop where
  /-- Related shapes go to related shapes. -/
  shape : ∀ {a b}, R.pos a b → R'.pos (f.toFunA a) (g.toFunA b)
  /-- Related positions pull back to related positions. -/
  pos : ∀ {a b}, R.pos a b → ∀ x y, R'.cor (f.toFunA a) (g.toFunA b) x y →
    R.cor a b (Sum.map (f.toFunB a) (g.toFunB b) x) (Sum.map (f.toFunB a) (g.toFunB b) y)

/-- The identity lenses form a morphism of a relation to itself. -/
theorem Hom.id (R : PolyRel P Q) : R.Hom R (Lens.id P) (Lens.id Q) where
  shape h := h
  pos _ x y hxy := by
    cases x <;> cases y <;> exact hxy

/-- Morphisms of relations compose. -/
theorem Hom.comp {R : PolyRel P Q} {R' : PolyRel P' Q'} {R'' : PolyRel P'' Q''}
    {f : Lens P P'} {g : Lens Q Q'} {f' : Lens P' P''} {g' : Lens Q' Q''}
    (s : R.Hom R' f g) (s' : R'.Hom R'' f' g') : R.Hom R'' (f'.comp f) (g'.comp g) where
  shape h := s'.shape (s.shape h)
  pos h x y hxy := by
    have := s.pos h _ _ (s'.pos (s.shape h) x y hxy)
    cases x <;> cases y <;> exact this

/-- The key of the graph of a lens at a shape: positions of `P` stay, positions of `Q` are pulled
back along the lens. -/
def graphKey (f : Lens P Q) (a : P.A) : P.B a ⊕ Q.B (f.toFunA a) → P.B a :=
  Sum.elim id (f.toFunB a)

/-- The graph of a lens, the image of `⟨id, f⟩ : P → P * Q`: shapes `a` and `f a`, and positions
identified when they have the same image in `P.B a`. -/
def graph (f : Lens P Q) : PolyRel P Q where
  pos a b := f.toFunA a = b
  cor a b x y := ∀ h : f.toFunA a = b,
    graphKey f a (h ▸ x : P.B a ⊕ Q.B (f.toFunA a)) =
      graphKey f a (h ▸ y : P.B a ⊕ Q.B (f.toFunA a))
  equiv _ :=
    { refl := fun _ _ => rfl
      symm := fun hxy h => (hxy h).symm
      trans := fun hxy hyz h => (hxy h).trans (hyz h) }

/-- `Ψ`: the relation of positions across the sum. -/
def toSigRel (R : PolyRel P Q) : SigRel P Q where
  pos := R.pos
  dir a b := Relation.across (R.cor a b)

end PolyRel

/-- `Φ`: the corelation generated by a relation of positions, the equivalence closure of its
cross pairs. -/
def SigRel.toPolyRel (S : SigRel P Q) : PolyRel P Q where
  pos := S.pos
  cor a b := Relation.EqvGen (Relation.Cross (S.dir a b))
  equiv _ := Relation.EqvGen.is_equivalence _

/-- **The comparison adjunction** `Ψ ⊣ Φ`: over each pair of lenses, a square from `Ψ R` to `S`
is a morphism of relations from `R` to `Φ S`. -/
theorem PolyRel.square_toSigRel_iff (R : PolyRel P Q) (S : SigRel P' Q') (f : Lens P P')
    (g : Lens Q Q') : SigRel.Square R.toSigRel S f g ↔ R.Hom S.toPolyRel f g := by
  constructor
  · intro sq
    refine ⟨sq.shape, fun {a b} h x y hxy => ?_⟩
    have hE : Equivalence fun x y =>
        R.cor a b (Sum.map (f.toFunB a) (g.toFunB b) x) (Sum.map (f.toFunB a) (g.toFunB b) y) :=
      { refl := fun _ => (R.equiv h).refl _
        symm := fun h' => (R.equiv h).symm h'
        trans := fun h₁ h₂ => (R.equiv h).trans h₁ h₂ }
    exact (Relation.eqvGen_cross_le_iff hE).2 (fun d e hde => sq.pos h d e hde) x y hxy
  · intro hom
    exact ⟨hom.shape, fun h d e hde => hom.pos h (.inl d) (.inr e) (Relation.EqvGen.rel _ _ hde)⟩

/-- The unit of the comparison: a relation maps to `Φ Ψ` of itself over the identity lenses. -/
theorem PolyRel.hom_toSigRel_toPolyRel (R : PolyRel P Q) :
    R.Hom R.toSigRel.toPolyRel (Lens.id P) (Lens.id Q) := by
  refine ⟨fun h => h, fun {a b} h x y hxy => ?_⟩
  have := (Relation.eqvGen_cross_le_iff (R.equiv h)).2 (fun _ _ hde => hde) x y hxy
  cases x <;> cases y <;> exact this

/-- The counit of the comparison: `Ψ Φ` of a signature relation maps to it over the identity
lenses. -/
theorem SigRel.square_toPolyRel_toSigRel (S : SigRel P Q) :
    SigRel.Square S.toPolyRel.toSigRel S (Lens.id P) (Lens.id Q) :=
  ⟨fun h => h, fun _ d e hde => Relation.EqvGen.rel (Sum.inl d) (Sum.inr e) hde⟩

/-- The counit: `Ψ Φ` is the difunctional closure. -/
theorem SigRel.toPolyRel_toSigRel_dir_iff (S : SigRel P Q) {a : P.A} {b : Q.A} (d : P.B a)
    (e : Q.B b) :
    S.toPolyRel.toSigRel.dir a b d e ↔ Relation.DifClosure (S.dir a b) d e :=
  Relation.eqvGen_cross_inl_inr_iff

/-- The counit is an isomorphism exactly at difunctional position relations. -/
theorem SigRel.toPolyRel_toSigRel_iff (S : SigRel P Q) :
    (∀ a b, S.pos a b → ∀ d e, S.toPolyRel.toSigRel.dir a b d e ↔ S.dir a b d e) ↔
      ∀ a b, S.pos a b → Difunctional (S.dir a b) := by
  simp only [SigRel.toPolyRel_toSigRel_dir_iff,
    Relation.difunctional_iff_difClosure_le]
  constructor
  · intro H a b h d e hde
    exact (H a b h d e).1 hde
  · intro H a b h d e
    exact ⟨H a b h d e, Relation.le_difClosure⟩

/-- The unit is an isomorphism exactly at cross-generated corelations. -/
theorem PolyRel.toSigRel_toPolyRel_iff (R : PolyRel P Q) :
    (∀ a b, R.pos a b → ∀ x y, R.toSigRel.toPolyRel.cor a b x y ↔ R.cor a b x y) ↔
      ∀ a b, R.pos a b → CrossGenerated (R.cor a b) := by
  constructor
  · intro H a b h x y hxy
    exact (H a b h x y).2 hxy
  · intro H a b h x y
    exact ⟨(Relation.eqvGen_cross_le_iff (R.equiv h)).2 (fun _ _ hde => hde) x y, H a b h x y⟩

/-- The relation of positions of a corelation is difunctional over related shapes. -/
theorem PolyRel.difunctional_toSigRel (R : PolyRel P Q) {a : P.A} {b : Q.A} (h : R.pos a b) :
    Difunctional (R.toSigRel.dir a b) :=
  Relation.difunctional_across ⟨R.cor a b, R.equiv h⟩

/-- The corelation generated by a signature relation is cross-generated. -/
theorem SigRel.crossGenerated_toPolyRel (S : SigRel P Q) (a : P.A) (b : Q.A) :
    CrossGenerated (S.toPolyRel.cor a b) :=
  Relation.crossGenerated_corel (S.dir a b)

/-- The graph of a lens relates a position of `P` and a position of `Q` at `f a` exactly when the
first is the image of the second under the backward map. -/
theorem PolyRel.toSigRel_graph (f : Lens P Q) {a : P.A} (d : P.B a) (e : Q.B (f.toFunA a)) :
    (PolyRel.graph f).toSigRel.dir a (f.toFunA a) d e ↔ f.toFunB a e = d := by
  constructor
  · intro h
    exact (h rfl).symm
  · intro h _
    exact h.symm

end CatCrypt.Container
