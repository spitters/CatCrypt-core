/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Deep.Package
import CatCryptCore.Deep.Eval
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Package Category

This file proves that CatCrypt's deep packages form a category.

## Main definitions

* `PkgHom I E` - Semantic package morphism from interface I to interface E
* `Category DeepInterface` - Category instance (all laws hold by `rfl`)
* `DeepPackage.toPkgHom` - Embedding of concrete packages into semantic morphisms

## Main results

* All three category laws (id_comp, comp_id, assoc) hold by `rfl`
* `DeepPackage.toPkgHom_id` - Identity package maps to identity morphism
* Tensor product of interfaces via list append

## Design

The key insight is that semantic package morphisms (`PkgHom`) abstract away
from concrete code representations and work purely with oracle handlers.
This gives all category laws definitionally (by `rfl`), following the
Kleisli category construction for the State+Prob monad.
-/

namespace CatCrypt.Deep

open CategoryTheory
open CatCrypt.Core

universe u

/-! ## Semantic Package Morphisms -/

/-- Semantic package morphism from interface I to interface E.

    A `PkgHom I E` represents a package that exports operations in `E` and
    imports operations from `I`. For each exported operation, given a domain
    value and an oracle handler for I's operations, it produces an SPComp
    computation.

    This abstracts over concrete code representations (RawCode, ValidCode)
    and works purely at the semantic level, giving clean categorical properties.

    In the Kleisli category interpretation:
    - Objects are interfaces (types of operations)
    - Morphisms are semantic oracle-transforming functions
    - Composition is oracle handler chaining (= package linking)
    - Identity forwards all operations to the handler -/
def PkgHom (I E : DeepInterface.{u}) : Type (u + 1) :=
  ∀ (op : ℕ) (dom codom : Type u), (op, dom, codom) ∈ E.ops → dom →
    (∀ (op' : ℕ) (dom' codom' : Type u), (op', dom', codom') ∈ I.ops →
      dom' → SPComp codom') →
    SPComp codom

namespace PkgHom

variable {I J K L M E : DeepInterface.{u}}

/-- Identity morphism: forwards each operation call to the oracle handler. -/
def id (I : DeepInterface.{u}) : PkgHom I I :=
  fun op dom codom h x handler => handler op dom codom h x

/-- Composition of morphisms (diagrammatic order: f ≫ g = "first f, then g").

    Given `f : PkgHom I M` and `g : PkgHom M E`, the composition has g
    resolve its oracle calls through f, which in turn resolves through
    the external handler. -/
def comp (f : PkgHom I M) (g : PkgHom M E) : PkgHom I E :=
  fun op dom codom h_exp x handler_I =>
    g op dom codom h_exp x (fun op' dom' codom' h_M x' =>
      f op' dom' codom' h_M x' handler_I)

/-- Left identity: `id ≫ f = f`. Holds by eta-reduction. -/
theorem id_comp (f : PkgHom I E) : comp (id I) f = f := rfl

/-- Right identity: `f ≫ id = f`. Holds by beta-reduction. -/
theorem comp_id (f : PkgHom I E) : comp f (id E) = f := rfl

/-- Associativity: `(f ≫ g) ≫ h = f ≫ (g ≫ h)`. Holds definitionally. -/
theorem comp_assoc (f : PkgHom I J) (g : PkgHom J K) (h : PkgHom K L) :
    comp (comp f g) h = comp f (comp g h) := rfl

end PkgHom

/-! ## Category Instance -/

/-- **Category of deep interfaces and semantic package morphisms.**

    Objects are `DeepInterface`s (specifying operation signatures).
    Morphisms are `PkgHom`s (semantic oracle-transforming functions).
    All three category laws (id_comp, comp_id, assoc) hold definitionally. -/
instance instCategoryDeepInterface : Category.{u+1} DeepInterface.{u} where
  Hom := PkgHom
  id := PkgHom.id
  comp := PkgHom.comp
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-! ## Connection to DeepPackage

    Every concrete `DeepPackage` gives rise to a semantic `PkgHom` via
    evaluation. This embedding preserves the identity package structure. -/

/-- Embed a concrete DeepPackage into a semantic PkgHom.

    Given a package p with imports I and exports E, we get a PkgHom by
    evaluating each operation's code with the provided oracle handler
    via `evalWith`. -/
noncomputable def DeepPackage.toPkgHom (p : DeepPackage.{u}) :
    PkgHom p.imports p.exports :=
  fun op dom codom h_exp x handler =>
    (p.impl op dom codom h_exp x).code.evalWith
      (fun op' dom' codom' x' =>
        have := Classical.dec ((op', dom', codom') ∈ p.imports.ops)
        if h : (op', dom', codom') ∈ p.imports.ops
        then handler op' dom' codom' h x'
        else SPComp.fail)

/-- The identity package maps to the identity PkgHom.

    The identity package implements each operation as an oracle call,
    and `evalWith` maps oracle calls to the handler, giving identity. -/
theorem DeepPackage.toPkgHom_id (iface : DeepInterface.{u}) :
    (DeepPackage.id iface).toPkgHom = PkgHom.id iface := by
  funext op dom codom h x handler
  simp only [DeepPackage.toPkgHom, PkgHom.id, DeepPackage.id, RawCode.evalWith]
  exact dif_pos h

/-! ## Tensor Product of Interfaces -/

/-- Tensor product of interfaces: concatenation of operation lists. -/
def tensorObj (I J : DeepInterface.{u}) : DeepInterface.{u} :=
  ⟨I.ops ++ J.ops⟩

/-- The tensor unit: empty interface with no operations. -/
def tensorUnit' : DeepInterface.{u} := ⟨[]⟩

/-- Tensor product is associative. -/
theorem tensorObj_assoc (I J K : DeepInterface.{u}) :
    tensorObj (tensorObj I J) K = tensorObj I (tensorObj J K) :=
  DeepInterface.ext (List.append_assoc I.ops J.ops K.ops)

/-- Empty interface is a left unit for tensor. -/
theorem tensorObj_unit_left (I : DeepInterface.{u}) :
    tensorObj tensorUnit' I = I :=
  DeepInterface.ext (List.nil_append I.ops)

/-- Empty interface is a right unit for tensor. -/
theorem tensorObj_unit_right (I : DeepInterface.{u}) :
    tensorObj I tensorUnit' = I :=
  DeepInterface.ext (List.append_nil I.ops)

/-! ## Tensor Product of Morphisms

    The tensor product of two morphisms dispatches exported operations
    to the appropriate morphism and restricts oracle handlers accordingly.
    This requires classical decidability since `Type u` membership in
    lists is not computably decidable. -/

/-- Tensor product of morphisms: parallel composition.

    Given `f : PkgHom I₁ E₁` and `g : PkgHom I₂ E₂`, produces
    `PkgHom (tensorObj I₁ I₂) (tensorObj E₁ E₂)` by dispatching:
    - Operations in E₁: handled by f (with handler restricted to I₁)
    - Operations in E₂: handled by g (with handler restricted to I₂) -/
noncomputable def PkgHom.tensor
    {I₁ E₁ I₂ E₂ : DeepInterface.{u}}
    (f : PkgHom I₁ E₁) (g : PkgHom I₂ E₂) :
    PkgHom (tensorObj I₁ I₂) (tensorObj E₁ E₂) :=
  fun op dom codom h_exp x handler =>
    have := Classical.dec ((op, dom, codom) ∈ E₁.ops)
    if h₁ : (op, dom, codom) ∈ E₁.ops then
      f op dom codom h₁ x (fun op' dom' codom' h_I x' =>
        handler op' dom' codom' (List.mem_append_left _ h_I) x')
    else
      have h₂ : (op, dom, codom) ∈ E₂.ops :=
        (List.mem_append.mp h_exp).resolve_left h₁
      g op dom codom h₂ x (fun op' dom' codom' h_I x' =>
        handler op' dom' codom' (List.mem_append_right _ h_I) x')

/-- Left whiskering: tensor identity on the left with a morphism.

    `whiskerLeft X f : (X ⊗ Y₁) ⟶ (X ⊗ Y₂)` for `f : Y₁ ⟶ Y₂`.
    Operations in X are forwarded to the handler (identity);
    operations in Y₂ are handled by f. -/
noncomputable def PkgHom.whiskerLeft
    (X : DeepInterface.{u}) {Y₁ Y₂ : DeepInterface.{u}}
    (f : PkgHom Y₁ Y₂) :
    PkgHom (tensorObj X Y₁) (tensorObj X Y₂) :=
  fun op dom codom h_exp x handler =>
    have := Classical.dec ((op, dom, codom) ∈ X.ops)
    if h₁ : (op, dom, codom) ∈ X.ops then
      handler op dom codom (List.mem_append_left _ h₁) x
    else
      have h₂ : (op, dom, codom) ∈ Y₂.ops :=
        (List.mem_append.mp h_exp).resolve_left h₁
      f op dom codom h₂ x (fun op' dom' codom' h_Y₁ x' =>
        handler op' dom' codom' (List.mem_append_right _ h_Y₁) x')

/-- Right whiskering: tensor a morphism on the left with identity on the right.

    `whiskerRight f Y : (X₁ ⊗ Y) ⟶ (X₂ ⊗ Y)` for `f : X₁ ⟶ X₂`.
    Operations in X₂ are handled by f;
    operations in Y are forwarded to the handler (identity). -/
noncomputable def PkgHom.whiskerRight
    {X₁ X₂ : DeepInterface.{u}} (f : PkgHom X₁ X₂)
    (Y : DeepInterface.{u}) :
    PkgHom (tensorObj X₁ Y) (tensorObj X₂ Y) :=
  fun op dom codom h_exp x handler =>
    have := Classical.dec ((op, dom, codom) ∈ X₂.ops)
    if h₁ : (op, dom, codom) ∈ X₂.ops then
      f op dom codom h₁ x (fun op' dom' codom' h_X₁ x' =>
        handler op' dom' codom' (List.mem_append_left _ h_X₁) x')
    else
      have h₂ : (op, dom, codom) ∈ Y.ops :=
        (List.mem_append.mp h_exp).resolve_left h₁
      handler op dom codom (List.mem_append_right _ h₂) x

/-! ## Pass-through Morphisms

    A "pass-through" morphism is one that just forwards all operations to
    the oracle handler, converting membership proofs via a list equality.
    This is the key building block for structural morphisms (associator,
    unitors, braiding).

    The crucial property: any two pass-through morphisms between the same
    types are equal, by proof irrelevance on the membership proofs. -/

/-- A pass-through morphism that forwards to the handler, converting
    membership proofs via a list equality. -/
def PkgHom.ofOpsEq {I E : DeepInterface.{u}} (h : E.ops = I.ops) :
    PkgHom I E :=
  fun op dom codom hE x handler =>
    handler op dom codom (h ▸ hE) x

/-- `ofOpsEq rfl` is the identity. -/
theorem PkgHom.ofOpsEq_rfl (I : DeepInterface.{u}) :
    PkgHom.ofOpsEq (rfl : I.ops = I.ops) = PkgHom.id I := by
  funext op dom codom h x handler; rfl

/-- Composition of pass-throughs is a pass-through. -/
theorem PkgHom.ofOpsEq_comp {I M E : DeepInterface.{u}}
    (h₁ : M.ops = I.ops) (h₂ : E.ops = M.ops) :
    PkgHom.comp (PkgHom.ofOpsEq h₁) (PkgHom.ofOpsEq h₂) =
    PkgHom.ofOpsEq (h₂.trans h₁) := by
  funext op dom codom h x handler; rfl

/-- Any two pass-throughs between the same types are equal. -/
theorem PkgHom.ofOpsEq_unique {I E : DeepInterface.{u}}
    (h₁ h₂ : E.ops = I.ops) :
    PkgHom.ofOpsEq h₁ = (PkgHom.ofOpsEq h₂ : PkgHom I E) := by
  funext op dom codom h x handler; rfl

/-! ## Whisker Laws -/

/-- Whiskering on the left with the identity is the identity. -/
theorem PkgHom.whiskerLeft_id (X Y : DeepInterface.{u}) :
    PkgHom.whiskerLeft X (𝟙 Y : PkgHom Y Y) = 𝟙 (tensorObj X Y) := by
  funext op dom codom h x handler
  simp only [PkgHom.whiskerLeft, CategoryStruct.id, PkgHom.id]
  split <;> rfl

/-- Whiskering on the right with the identity is the identity. -/
theorem PkgHom.whiskerRight_id (X Y : DeepInterface.{u}) :
    PkgHom.whiskerRight (𝟙 X : PkgHom X X) Y = 𝟙 (tensorObj X Y) := by
  funext op dom codom h x handler
  simp only [PkgHom.whiskerRight, CategoryStruct.id, PkgHom.id]
  split <;> rfl

/-! ## Monoidal Category Instance

    `DeepInterface` forms a (strict) monoidal category with:
    - Tensor product = list append of operations
    - Unit = empty interface
    - Associator/unitors defined directly as pass-through morphisms
    - All coherence axioms follow from proof irrelevance -/

/-- Associator: pass-through using `List.append_assoc`. -/
noncomputable def assocIso (X Y Z : DeepInterface.{u}) :
    tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z) where
  hom := PkgHom.ofOpsEq (by simp [tensorObj, List.append_assoc])
  inv := PkgHom.ofOpsEq (by simp [tensorObj, List.append_assoc])
  hom_inv_id := by funext op dom codom h x handler; rfl
  inv_hom_id := by funext op dom codom h x handler; rfl

/-- Left unitor: pass-through using `List.nil_append`. -/
noncomputable def leftUnitorIso (X : DeepInterface.{u}) :
    tensorObj tensorUnit' X ≅ X where
  hom := PkgHom.ofOpsEq (by simp [tensorObj, tensorUnit'])
  inv := PkgHom.ofOpsEq (by simp [tensorObj, tensorUnit'])
  hom_inv_id := by funext op dom codom h x handler; rfl
  inv_hom_id := by funext op dom codom h x handler; rfl

/-- Right unitor: pass-through using `List.append_nil`. -/
noncomputable def rightUnitorIso (X : DeepInterface.{u}) :
    tensorObj X tensorUnit' ≅ X where
  hom := PkgHom.ofOpsEq (by simp [tensorObj, tensorUnit'])
  inv := PkgHom.ofOpsEq (by simp [tensorObj, tensorUnit'])
  hom_inv_id := by funext op dom codom h x handler; rfl
  inv_hom_id := by funext op dom codom h x handler; rfl

/-! ## Monoidal Category Structure

    We provide `MonoidalCategoryStruct` (the tensor product data) and prove
    the coherence axioms (pentagon, triangle) that hold unconditionally.

    **Important**: The naturality axioms (`tensorHom_comp_tensorHom`,
    `associator_naturality`, `braiding_naturality`) require that tensor
    components have **disjoint** operation lists. This matches Rocq SSProve,
    which enforces disjointness via `:|:` (disjoint union of finite maps).
    With overlapping operations, `dite`-based dispatch becomes inconsistent
    between left-whiskered and right-whiskered morphisms.

    The coherence axioms (pentagon, triangle, hexagons, symmetry) hold
    unconditionally because they involve only structural morphisms
    (pass-throughs and braiding), not arbitrary morphisms `f`, `g`. -/

noncomputable instance instMonoidalCategoryStructDeepInterface :
    MonoidalCategoryStruct.{u+1} DeepInterface.{u} where
  tensorObj := tensorObj
  whiskerLeft := PkgHom.whiskerLeft
  whiskerRight := PkgHom.whiskerRight
  tensorUnit := tensorUnit'
  associator := assocIso
  leftUnitor := leftUnitorIso
  rightUnitor := rightUnitorIso

/-! ### Unconditionally valid monoidal axioms -/

/-- Tensor of identities is identity. -/
theorem pkg_id_tensor_id (X₁ X₂ : DeepInterface.{u}) :
    PkgHom.comp (PkgHom.whiskerRight (PkgHom.id X₁) X₂)
                (PkgHom.whiskerLeft X₁ (PkgHom.id X₂)) =
    PkgHom.id (tensorObj X₁ X₂) := by
  funext op dom codom h x handler
  simp only [PkgHom.comp, PkgHom.whiskerRight, PkgHom.whiskerLeft, PkgHom.id]
  split <;> rfl

/-- Right unitor is natural. -/
theorem pkg_rightUnitor_naturality {X Y : DeepInterface.{u}} (f : X ⟶ Y) :
    PkgHom.comp (PkgHom.whiskerRight f tensorUnit') (rightUnitorIso Y).hom =
    PkgHom.comp (rightUnitorIso X).hom f := by
  funext op dom codom h x handler
  simp only [PkgHom.comp, rightUnitorIso, PkgHom.whiskerRight, PkgHom.ofOpsEq]
  split_ifs
  all_goals rfl

/-- Pentagon coherence for associators. -/
theorem pkg_pentagon (W X Y Z : DeepInterface.{u}) :
    PkgHom.comp (PkgHom.whiskerRight (assocIso W X Y).hom Z)
      (PkgHom.comp (assocIso W (tensorObj X Y) Z).hom
        (PkgHom.whiskerLeft W (assocIso X Y Z).hom)) =
    PkgHom.comp (assocIso (tensorObj W X) Y Z).hom
      (assocIso W X (tensorObj Y Z)).hom := by
  funext op dom codom h x handler
  simp only [PkgHom.comp,
             assocIso, PkgHom.whiskerLeft, PkgHom.whiskerRight, PkgHom.ofOpsEq]
  split_ifs <;> rfl

/-- Triangle coherence for associator and unitors. -/
theorem pkg_triangle (X Y : DeepInterface.{u}) :
    PkgHom.comp (assocIso X tensorUnit' Y).hom
      (PkgHom.whiskerLeft X (leftUnitorIso Y).hom) =
    PkgHom.whiskerRight (rightUnitorIso X).hom Y := by
  funext op dom codom h x handler
  simp only [PkgHom.comp,
             assocIso, leftUnitorIso, rightUnitorIso,
             PkgHom.whiskerLeft, PkgHom.whiskerRight, PkgHom.ofOpsEq]

/-! ## Braided and Symmetric Structure

    The braiding swaps the two halves of a tensor product.
    Since our tensor is list append, braiding reindexes operations
    via commutativity of `∨` in list membership.

    Coherence axioms (hexagons, symmetry) hold unconditionally.
    Naturality requires disjoint interfaces (see above). -/

/-- Braiding morphism: swap the two halves of a tensor product. -/
noncomputable def PkgHom.braiding (X Y : DeepInterface.{u}) :
    PkgHom (tensorObj X Y) (tensorObj Y X) :=
  fun op dom codom h_exp x handler =>
    handler op dom codom
      (List.mem_append.mpr (List.mem_append.mp h_exp).symm) x

/-- Braiding composed with itself is identity (by proof irrelevance). -/
theorem PkgHom.braiding_braiding (X Y : DeepInterface.{u}) :
    PkgHom.comp (PkgHom.braiding X Y) (PkgHom.braiding Y X) = PkgHom.id _ := by
  funext op dom codom h x handler; rfl

/-- Braiding isomorphism: `X ⊗ Y ≅ Y ⊗ X`. -/
noncomputable def braidingIso (X Y : DeepInterface.{u}) :
    tensorObj X Y ≅ tensorObj Y X where
  hom := PkgHom.braiding X Y
  inv := PkgHom.braiding Y X
  hom_inv_id := PkgHom.braiding_braiding X Y
  inv_hom_id := PkgHom.braiding_braiding Y X

theorem pkg_hexagon_forward (X Y Z : DeepInterface.{u}) :
    PkgHom.comp (assocIso X Y Z).hom
      (PkgHom.comp (PkgHom.braiding X (tensorObj Y Z))
        (assocIso Y Z X).hom) =
    PkgHom.comp (PkgHom.whiskerRight (PkgHom.braiding X Y) Z)
      (PkgHom.comp (assocIso Y X Z).hom
        (PkgHom.whiskerLeft Y (PkgHom.braiding X Z))) := by
  funext op dom codom h x handler
  simp only [PkgHom.comp,
             assocIso, PkgHom.whiskerLeft, PkgHom.whiskerRight,
             PkgHom.braiding, PkgHom.ofOpsEq]
  split_ifs <;> rfl

theorem pkg_hexagon_reverse (X Y Z : DeepInterface.{u}) :
    PkgHom.comp (assocIso X Y Z).inv
      (PkgHom.comp (PkgHom.braiding (tensorObj X Y) Z)
        (assocIso Z X Y).inv) =
    PkgHom.comp (PkgHom.whiskerLeft X (PkgHom.braiding Y Z))
      (PkgHom.comp (assocIso X Z Y).inv
        (PkgHom.whiskerRight (PkgHom.braiding X Z) Y)) := by
  funext op dom codom h x handler
  simp only [PkgHom.comp,
             assocIso, PkgHom.whiskerLeft, PkgHom.whiskerRight,
             PkgHom.braiding, PkgHom.ofOpsEq]
  split_ifs <;> rfl

/-- Braiding is a symmetric involution. -/
theorem pkg_symmetry (X Y : DeepInterface.{u}) :
    PkgHom.comp (PkgHom.braiding X Y) (PkgHom.braiding Y X) =
    PkgHom.id (tensorObj X Y) :=
  PkgHom.braiding_braiding X Y

end CatCrypt.Deep
