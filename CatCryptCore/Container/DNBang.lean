/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.DillerNahm
public import CatCryptCore.Container.ExpectedDN
public import CatCryptCore.ForMathlib.MultisetSum
public import PolyFun.PFunctor.Category.Monoidal
public import Mathlib.CategoryTheory.Monad.Kleisli
public import Mathlib.CategoryTheory.Monoidal.Comon_
public import Mathlib.Data.Multiset.Sum

/-!
# The multiset exponential and the Diller–Nahm category as its co-Kleisli category

The exponential `bang P` of a polynomial functor `P` has the shapes of `P` and, at a shape `a`,
the finite multisets of positions of `P` at `a` as positions. A lens `bang P ⇆ Q` has the data of
a Diller–Nahm morphism `P → Q`: a forward map on shapes and a backward map from a position of `Q`
to a finite multiset of positions of `P`.

On the category of lenses `bang` is a comonad: the counit sends a position to the singleton
multiset, and the comultiplication sends a multiset of multisets to its sum (`Multiset.join`).
The Diller–Nahm category is its co-Kleisli category (de Paiva, *The Dialectica categories*,
Tech. Rep. UCAM-CL-TR-213, 1991; Hofstra, *The Dialectica monad and its cousins*, CRM Proc.
Lecture Notes 53, 2011; Moss and von Glehn, *Dialectica models of type theory*, LICS 2018, §8).
For the parallel product `⊗` each `bang P` is a commutative comonoid, by weakening (the empty
multiset) and contraction (the sum of two multisets), and `bang` sends the cartesian product `*`
to the parallel product and the terminal object `1` to the unit `y` (the Seely isomorphisms).

The exponential `bangW S P` with weights in a commutative semiring `S` has the finitely supported
weightings `P.B a →₀ S` as positions; at `S = ℝ≥0` the lenses out of it are the morphisms with
expected demands `EDNLens`.

## Main definitions

* `bang`, `bangMap`, `bangCounit`, `bangComult` — the exponential, its action on lenses, its
  counit (dereliction) and its comultiplication (digging);
* `bangFunctor`, `bangComonad` — the comonad on `LensCat`;
* `DNLens.toBangLens`, `DNLens.ofBangLens`, `DNLens.equivBangLens` — a Diller–Nahm morphism
  as a lens out of the exponential;
* `DNCat` — the Diller–Nahm category; `dnCokleisliEquiv` — its equivalence with the co-Kleisli
  category of `bangComonad`, the identity on objects and `DNLens.equivBangLens` on hom-sets;
* `bangWeak`, `bangContr` — weakening and contraction;
* `multisetSumEquiv`, `seely`, `seelyUnit` — the Seely isomorphisms
  `bang (P * Q) ≃ₗ bang P ⊗ bang Q` and `bang 1 ≃ₗ y`;
* `bangW`, `bangWMap`, `bangWCounit`, `bangWComult`, `EDNLens.equivBangWLens` — the exponential
  with weights in a semiring, and the morphisms with expected demands as lenses out of it.

## Main results

* `bangMap_id`, `bangMap_comp`, `bangCounit_natural`, `bangComult_natural`,
  `bangCounit_comult`, `bangMap_counit_comult`, `bangComult_coassoc` — the comonad laws;
* `DNLens.toBangLens_id`, `DNLens.toBangLens_comp` — the identity of the Diller–Nahm category is
  the counit, and its composite is the co-Kleisli composite `g ∘ bang f ∘ δ`;
* `bangContr_weak_left`, `bangContr_weak_right`, `bangContr_assoc`, `bangContr_comm` and the
  instances `ComonObj`, `IsCommComonObj` on `TensorCat.of (bang P)` — the commutative comonoid;
* `seely_contr` — contraction is the Seely image of the exponential of the diagonal;
* `EDNLens.toBangWLens_id`, `EDNLens.toBangWLens_comp` — the same statements for expected
  demands at weights in `ℝ≥0`.

Search words: Dialectica category, Diller–Nahm, linear logic, exponential, of-course modality,
comonad, co-Kleisli category, commutative comonoid, weakening, contraction, dereliction, digging,
Seely isomorphism, finite multiset, weighted exponential, expected demand, lens, polynomial
functor.
-/

set_option autoImplicit false

@[expose] public section

universe u v w u₁ v₁ u₂ v₂ u₃ v₃

namespace CatCrypt.Container

open PFunctor CategoryTheory

/-! ## The exponential and its comonad structure -/

/-- The multiset exponential of the Diller–Nahm category: the shapes of `P`, and at a shape the
finite multisets of positions of `P` at it. -/
abbrev bang (P : PFunctor.{u, v}) : PFunctor.{u, v} := ⟨P.A, fun a => Multiset (P.B a)⟩

/-- A lens with equal forward maps is determined by its backward map. -/
theorem lens_mk_congr {P : PFunctor.{u₁, v₁}} {Q : PFunctor.{u₂, v₂}} {fA : P.A → Q.A}
    {b₁ b₂ : ∀ a, Q.B (fA a) → P.B a} (h : ∀ a y, b₁ a y = b₂ a y) :
    (Lens.mk fA b₁ : Lens P Q) = Lens.mk fA b₂ := by
  congr 1
  funext a y
  exact h a y

/-- The sum of a multiset of multisets of multisets is associative. -/
theorem multiset_join_join {α : Type u} (m : Multiset (Multiset (Multiset α))) :
    m.join.join = (m.map Multiset.join).join := by
  induction m using Multiset.induction_on <;>
    simp_all [Multiset.join_cons, Multiset.join_add]

variable {P : PFunctor.{u₁, v₁}} {Q : PFunctor.{u₂, v₂}} {R : PFunctor.{u₃, v₃}}

/-- The action of the exponential on a lens: the backward map acts on each element of a
multiset. -/
def bangMap (l : Lens P Q) : Lens (bang P) (bang Q) where
  toFunA := l.toFunA
  toFunB a m := m.map (l.toFunB a)

/-- The counit (dereliction): a position demands itself once. -/
def bangCounit (P : PFunctor.{u, v}) : Lens (bang P) P where
  toFunA a := a
  toFunB _ y := {y}

/-- The comultiplication (digging): a multiset of multisets demands their sum. -/
def bangComult (P : PFunctor.{u, v}) : Lens (bang P) (bang (bang P)) where
  toFunA a := a
  toFunB _ m := m.join

/-- The exponential preserves identities. -/
theorem bangMap_id : bangMap (Lens.id P) = Lens.id (bang P) :=
  lens_mk_congr fun _ m => Multiset.map_id m

/-- The exponential preserves composition. -/
theorem bangMap_comp (m : Lens Q R) (l : Lens P Q) :
    bangMap (Lens.comp m l) = Lens.comp (bangMap m) (bangMap l) :=
  lens_mk_congr fun a s => (Multiset.map_map (l.toFunB a) (m.toFunB (l.toFunA a)) s).symm

/-- The counit is natural. -/
theorem bangCounit_natural (l : Lens P Q) :
    Lens.comp (bangCounit Q) (bangMap l) = Lens.comp l (bangCounit P) :=
  lens_mk_congr fun _ _ => Multiset.map_singleton _ _

/-- The comultiplication is natural. -/
theorem bangComult_natural (l : Lens P Q) :
    Lens.comp (bangComult Q) (bangMap l) = Lens.comp (bangMap (bangMap l)) (bangComult P) :=
  lens_mk_congr fun _ mm => Multiset.map_join _ mm

/-- Left counit law: the counit at `bang P` after the comultiplication is the identity. -/
theorem bangCounit_comult (P : PFunctor.{u, v}) :
    Lens.comp (bangCounit (bang P)) (bangComult P) = Lens.id (bang P) :=
  lens_mk_congr fun _ m => Multiset.singleton_join m

/-- Right counit law: the exponential of the counit after the comultiplication is the
identity. -/
theorem bangMap_counit_comult (P : PFunctor.{u, v}) :
    Lens.comp (bangMap (bangCounit P)) (bangComult P) = Lens.id (bang P) :=
  lens_mk_congr fun _ m => (Multiset.bind_singleton m fun y => y).trans (Multiset.map_id' m)

/-- Coassociativity of the comultiplication. -/
theorem bangComult_coassoc (P : PFunctor.{u, v}) :
    Lens.comp (bangComult (bang P)) (bangComult P) =
      Lens.comp (bangMap (bangComult P)) (bangComult P) :=
  lens_mk_congr fun _ m => multiset_join_join m

/-! ## Diller–Nahm morphisms as lenses out of the exponential -/

namespace DNLens

/-- A Diller–Nahm morphism as a lens out of the exponential. -/
def toBangLens (g : DNLens P Q) : Lens (bang P) Q where
  toFunA := g.toFunA
  toFunB := g.toFunB

/-- A lens out of the exponential as a Diller–Nahm morphism. -/
def ofBangLens (l : Lens (bang P) Q) : DNLens P Q where
  toFunA := l.toFunA
  toFunB := l.toFunB

/-- The Diller–Nahm morphisms `P → Q` are the lenses `bang P ⇆ Q`. -/
def equivBangLens : DNLens P Q ≃ Lens (bang P) Q where
  toFun := toBangLens
  invFun := ofBangLens
  left_inv _ := rfl
  right_inv _ := rfl

/-- The identity of the Diller–Nahm category is the counit of the exponential. -/
theorem toBangLens_id (P : PFunctor.{u, v}) : (DNLens.id P).toBangLens = bangCounit P :=
  lens_mk_congr fun _ _ => rfl

/-- The composite of the Diller–Nahm category is the co-Kleisli composite
`g ∘ bang f ∘ δ`. -/
theorem toBangLens_comp (g : DNLens Q R) (f : DNLens P Q) :
    (comp g f).toBangLens =
      Lens.comp g.toBangLens (Lens.comp (bangMap f.toBangLens) (bangComult P)) :=
  lens_mk_congr fun _ _ => rfl

end DNLens

/-! ## The Diller–Nahm category -/

set_option linter.checkUnivs false in
/-- The Diller–Nahm category: polynomial functors with Diller–Nahm morphisms. -/
structure DNCat : Type max (u + 1) (v + 1) where
  /-- Regard a polynomial functor as an object of the Diller–Nahm category. -/
  of ::
  /-- The polynomial functor underlying an object. -/
  toPFunctor : PFunctor.{u, v}

namespace DNCat

instance instCategory : Category DNCat.{u, v} where
  Hom P Q := DNLens P.toPFunctor Q.toPFunctor
  id P := DNLens.id P.toPFunctor
  comp f g := DNLens.comp g f
  id_comp f := DNLens.comp_id f
  comp_id f := DNLens.id_comp f
  assoc f g h := (DNLens.comp_assoc h g f).symm

end DNCat

/-! ## Weakening and contraction -/

/-- Weakening: no position is demanded. -/
def bangWeak (P : PFunctor.{u, v}) : Lens (bang P) y.{u, v} where
  toFunA _ := PUnit.unit
  toFunB _ _ := 0

/-- Contraction: a shape is duplicated, and a pair of multisets demands their sum. -/
def bangContr (P : PFunctor.{u, v}) : Lens (bang P) (bang P ⊗ bang P) where
  toFunA a := (a, a)
  toFunB _ m := m.1 + m.2

/-- Weakening on the left after contraction is the left unitor. -/
theorem bangContr_weak_left (P : PFunctor.{u, v}) :
    Lens.comp (Lens.tensorMap (bangWeak P) (Lens.id (bang P))) (bangContr P) =
      Lens.Equiv.yTensor.invLens :=
  lens_mk_congr fun _ m => zero_add m.2

/-- Weakening on the right after contraction is the right unitor. -/
theorem bangContr_weak_right (P : PFunctor.{u, v}) :
    Lens.comp (Lens.tensorMap (Lens.id (bang P)) (bangWeak P)) (bangContr P) =
      Lens.Equiv.tensorY.invLens :=
  lens_mk_congr fun _ m => add_zero m.1

/-- Contraction is coassociative. -/
theorem bangContr_assoc (P : PFunctor.{u, v}) :
    Lens.comp (Lens.tensorMap (Lens.id (bang P)) (bangContr P)) (bangContr P) =
      Lens.comp Lens.Equiv.tensorAssoc.toLens
        (Lens.comp (Lens.tensorMap (bangContr P) (Lens.id (bang P))) (bangContr P)) :=
  lens_mk_congr fun _ _ => (add_assoc _ _ _).symm

/-- Contraction is cocommutative. -/
theorem bangContr_comm (P : PFunctor.{u, v}) :
    Lens.comp (Lens.Equiv.tensorComm (bang P) (bang P)).toLens (bangContr P) = bangContr P :=
  lens_mk_congr fun _ _ => add_comm _ _

/-! ## The Seely isomorphism -/

/-- A finite multiset over a sum is a pair of finite multisets. -/
def multisetSumEquiv (α β : Type u) : Multiset (α ⊕ β) ≃ Multiset α × Multiset β where
  toFun m := (m.filterMap Sum.getLeft?, m.filterMap Sum.getRight?)
  invFun st := st.1.disjSum st.2
  left_inv m := Multiset.map_filterMap_getLeft_add_getRight m
  right_inv st :=
    Prod.ext (Multiset.filterMap_getLeft_map_add st.1 st.2)
      (Multiset.filterMap_getRight_map_add st.1 st.2)

/-- **The Seely isomorphism**: the exponential of a cartesian product is the parallel product of
the exponentials. -/
def seely (P Q : PFunctor.{u, v}) : bang (P * Q) ≃ₗ bang P ⊗ bang Q where
  toLens := Lens.mk id fun ab st => (multisetSumEquiv (P.B ab.1) (Q.B ab.2)).symm st
  invLens := Lens.mk id fun ab m => multisetSumEquiv (P.B ab.1) (Q.B ab.2) m
  left_inv := lens_mk_congr fun ab m =>
    (multisetSumEquiv (P.B ab.1) (Q.B ab.2)).symm_apply_apply m
  right_inv := lens_mk_congr fun ab st =>
    (multisetSumEquiv (P.B ab.1) (Q.B ab.2)).apply_symm_apply st

/-- **The Seely isomorphism at the unit**: the exponential of the terminal object is the unit of
the parallel product. -/
def seelyUnit : bang (1 : PFunctor.{u, v}) ≃ₗ y.{u, v} where
  toLens := Lens.mk (fun _ => PUnit.unit) fun _ _ => 0
  invLens := Lens.mk (fun _ => PUnit.unit) fun _ _ => PUnit.unit
  left_inv := lens_mk_congr fun _ _ =>
    (Multiset.eq_zero_of_forall_notMem fun x _ => PEmpty.elim x).symm
  right_inv := rfl

/-- Contraction is the Seely image of the exponential of the diagonal. -/
theorem seely_contr (P : PFunctor.{u, v}) :
    Lens.comp (seely P P).toLens (bangMap (Lens.prodPair (Lens.id P) (Lens.id P))) =
      bangContr P :=
  lens_mk_congr fun _ m => by
    simp [seely, multisetSumEquiv, bangMap, Lens.prodPair, Multiset.disjSum,
      Multiset.map_map, Function.comp_def]

/-! ## The exponential with weights in a semiring -/

section Weighted

variable (S : Type w) [CommSemiring S]

/-- The exponential with weights in `S`: the shapes of `P`, and at a shape the finitely supported
weightings of the positions of `P` at it. -/
abbrev bangW (P : PFunctor.{u, v}) : PFunctor.{u, max v w} := ⟨P.A, fun a => P.B a →₀ S⟩

variable {S}

/-- The action of the weighted exponential on a lens: the weights are pushed along the backward
map. -/
noncomputable def bangWMap (l : Lens P Q) : Lens (bangW S P) (bangW S Q) where
  toFunA := l.toFunA
  toFunB a w := Finsupp.mapDomain (l.toFunB a) w

variable (S) in
/-- The counit of the weighted exponential: a position demands itself with weight one. -/
noncomputable def bangWCounit (P : PFunctor.{u, v}) : Lens (bangW S P) P where
  toFunA a := a
  toFunB _ y := Finsupp.single y 1

variable (S) in
/-- The comultiplication of the weighted exponential: a weighting of weightings demands their
weighted sum. -/
noncomputable def bangWComult (P : PFunctor.{u, v}) : Lens (bangW S P) (bangW S (bangW S P)) where
  toFunA a := a
  toFunB _ ww := Finsupp.linearCombination S id ww

end Weighted

namespace EDNLens

/-- A morphism with expected demands as a lens out of the exponential with weights in `ℝ≥0`. -/
def toBangWLens (g : EDNLens P Q) : Lens (bangW NNReal P) Q where
  toFunA := g.toFunA
  toFunB := g.toFunB

/-- A lens out of the exponential with weights in `ℝ≥0` as a morphism with expected demands. -/
def ofBangWLens (l : Lens (bangW NNReal P) Q) : EDNLens P Q where
  toFunA := l.toFunA
  toFunB := l.toFunB

/-- The morphisms with expected demands `P → Q` are the lenses `bangW ℝ≥0 P ⇆ Q`. -/
def equivBangWLens : EDNLens P Q ≃ Lens (bangW NNReal P) Q where
  toFun := toBangWLens
  invFun := ofBangWLens
  left_inv _ := rfl
  right_inv _ := rfl

/-- The identity with expected demands is the counit of the weighted exponential. -/
theorem toBangWLens_id (P : PFunctor.{u, v}) :
    (EDNLens.id P).toBangWLens = bangWCounit NNReal P :=
  lens_mk_congr fun _ _ => rfl

/-- The composite with expected demands is the co-Kleisli composite of the weighted
exponential. -/
theorem toBangWLens_comp (g : EDNLens Q R) (f : EDNLens P Q) :
    (comp g f).toBangWLens =
      Lens.comp g.toBangWLens (Lens.comp (bangWMap f.toBangWLens) (bangWComult NNReal P)) :=
  lens_mk_congr fun a z =>
    (Finsupp.linearCombination_mapDomain (R := NNReal) (v' := id) (f := f.toFunB a)
      (l := g.toFunB (f.toFunA a) z)).symm

end EDNLens

open MonoidalCategory

/-! ## The comonad on the category of lenses and the co-Kleisli category -/

/-- The exponential as an endofunctor of the category of lenses. -/
def bangFunctor : LensCat.{u, v} ⥤ LensCat.{u, v} where
  obj X := LensCat.of (bang X.toPFunctor)
  map f := bangMap f
  map_id _ := bangMap_id
  map_comp f g := bangMap_comp g f

/-- The exponential as a comonad on the category of lenses. -/
def bangComonad : Comonad LensCat.{u, v} where
  toFunctor := bangFunctor
  ε := { app X := bangCounit X.toPFunctor, naturality _ _ f := bangCounit_natural f }
  δ := { app X := bangComult X.toPFunctor, naturality _ _ f := bangComult_natural f }
  coassoc X := (bangComult_coassoc X.toPFunctor).symm
  left_counit X := bangCounit_comult X.toPFunctor
  right_counit X := bangMap_counit_comult X.toPFunctor

namespace DNCat

/-- The functor from the Diller–Nahm category to the co-Kleisli category of the exponential:
the identity on objects and `DNLens.toBangLens` on morphisms. -/
def toCokleisli : DNCat.{u, v} ⥤ Cokleisli bangComonad.{u, v} where
  obj P := .mk _ (LensCat.of P.toPFunctor)
  map f := .mk (DNLens.toBangLens f)
  map_id P := Cokleisli.hom_ext _ (DNLens.toBangLens_id P.toPFunctor)
  map_comp f g := Cokleisli.hom_ext _ (DNLens.toBangLens_comp g f)

/-- The functor from the co-Kleisli category of the exponential to the Diller–Nahm category:
the identity on objects and `DNLens.ofBangLens` on morphisms. -/
def ofCokleisli : Cokleisli bangComonad.{u, v} ⥤ DNCat.{u, v} where
  obj X := of X.of.toPFunctor
  map f := DNLens.ofBangLens f.of
  map_id X := DNLens.equivBangLens.symm_apply_eq.2 (DNLens.toBangLens_id X.of.toPFunctor).symm
  map_comp f g := DNLens.equivBangLens.symm_apply_eq.2
    (DNLens.toBangLens_comp (DNLens.ofBangLens g.of) (DNLens.ofBangLens f.of)).symm

end DNCat

/-- **The Diller–Nahm category is the co-Kleisli category of the exponential.** The equivalence
is the identity on objects and `DNLens.equivBangLens` on hom-sets; its unit and counit are
identities. -/
def dnCokleisliEquiv : DNCat.{u, v} ≌ Cokleisli bangComonad.{u, v} :=
  CategoryTheory.Equivalence.mk DNCat.toCokleisli DNCat.ofCokleisli
    (NatIso.ofComponents (fun _ => Iso.refl _)
      fun f => (Category.comp_id f).trans (Category.id_comp f).symm)
    (NatIso.ofComponents (fun _ => Iso.refl _)
      fun f => (Category.comp_id f).trans (Category.id_comp f).symm)

/-! ## The commutative comonoid structure of the exponential -/

/-- `bang P` is a comonoid for the parallel product, by weakening and contraction. -/
instance instComonObjBang (P : PFunctor.{u, v}) : ComonObj (TensorCat.of (bang P)) where
  counit := bangWeak P
  comul := bangContr P
  counit_comul := bangContr_weak_left P
  comul_counit := bangContr_weak_right P
  comul_assoc := bangContr_assoc P

/-- The comonoid `bang P` is commutative. -/
instance instIsCommComonObjBang (P : PFunctor.{u, v}) :
    IsCommComonObj (TensorCat.of (bang P)) where
  comul_comm := bangContr_comm P

end CatCrypt.Container
