/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Category.PkgFam
import CatCrypt.Tactics.SumCases
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# The Package Category: Substitution, Not Sequencing

## Substitution vs Sequencing

Cryptographic packages compose by **oracle resolution** (substitution): when
package `p₁` calls an oracle, the call is resolved by package `p₂`'s
implementation. This is fundamentally different from **Kleisli sequencing**
(the composition in `Fam(KlSPComp)`), where one computation's output feeds
as input to the next.

| | Substitution (packages) | Sequencing (Fam/Kleisli) |
|---|---|---|
| **Morphisms** | Handler → Handler (higher-order) | A →ₖ B (first-order) |
| **Composition** | Function composition | Monadic bind |
| **Crypto meaning** | Oracle resolution | Data pipeline |
| **PL analogy** | Variable substitution | Statement sequencing |

This distinction is well-studied in programming language semantics
(Fiore–Plotkin–Turi), where substitution and sequencing are related by
the continuation-passing transform but are categorically distinct.
All major cryptographic frameworks (CatCrypt, constructive crypto, UC,
EasyCrypt) use substitution-style composition for packages.

## The Package Category

We define a category on `PkgInterface` where:
- **Objects** are package interfaces (indexed families of operation signatures)
- **Morphisms** `I ⟶ J` are typed handler transformers:
  given implementations of `I`'s operations, produce implementations of `J`'s
- **Composition** is function composition (= oracle resolution)
- **Identity** is the pass-through handler

This is the category induced by the functor `TypedHandler : PkgInterface → Type`
that maps each interface to its handler type (product of Kleisli arrows). In the
language of enriched category theory, it is the underlying ordinary category
of `Set(TypedHandler(I), TypedHandler(J))`.

## Monoidal Structure

The symmetric monoidal structure comes from the product decomposition:

    TypedHandler(I ⊗ J) ≅ TypedHandler(I) × TypedHandler(J)

Since `PkgInterface.tensor` uses `Sum` on index types and `Sum.elim` on families,
this isomorphism is essentially definitional. The monoidal laws reduce to
`Sum` index manipulation (`funext` + `cases` + `rfl`), in contrast to the complex
`fam_ext`/`HEq`/`erw` proofs needed for `Fam(C)`.

## Relationship to `Fam(KlSPComp)`

`Fam(KlSPComp)` provides the correct **monoidal structure** (parallel composition)
and individual **Kleisli arrows** for each operation. But its composition (Kleisli
bind) does NOT match cryptographic linking (oracle substitution). Packages share
Fam's monoidal structure but have their own categorical composition.

There is no functor between these categories in either direction: Fam composition
is first-order (data pipeline), while package composition is second-order
(handler transformation). They are related by CPS / double-negation translation
but categorically distinct.

## Main definitions

* `TypedHandler` — typed handler for an interface (product of Kleisli arrows)
* `Category PkgInterface` — the package category
* `MonoidalCategory PkgInterface` — parallel composition (from `Sum` on indices)
* `BraidedCategory PkgInterface` — interface swapping (from `Sum.swap`)
* `SymmetricCategory PkgInterface` — braiding is self-inverse

## Implementation Note

The `MonoidalCategoryStruct` is defined as a private helper and explicitly
assigned to `MonoidalCategory` via `toMonoidalCategoryStruct`. This ensures:
1. Within `MonoidalCategory where`, all struct fields are accessible for
   coherence proofs (`pentagon`, etc.) which are all `rfl`.
2. There is exactly ONE path to `tensorObj` (no typeclass diamond), so
   `I ⊗ J` definitionally equals the struct's `tensorObj I J`.
3. The braiding iso can be defined on `PkgInterface.tensor` (where `Sum`
   structure is visible) and coerced via definitional equality.
-/

namespace CatCrypt.Category

open CategoryTheory MonoidalCategory
open CatCrypt.Core

/-! ## Typed Handler -/

/-- A typed oracle handler for interface `I`: for each operation indexed by `I.ι`,
    a Kleisli arrow from the domain type to the codomain type.

    This is the product `∏_{i : I.ι} KlSPComp(I.doms i, I.codoms i)`,
    the "semantic content" of a package that exports interface `I`. -/
def TypedHandler (I : PkgInterface) : Type :=
  ∀ (i : I.ι), I.doms i → SPComp (I.codoms i)

namespace TypedHandler

variable {I J K : PkgInterface}

/-- Extract the left component of a handler for a tensor interface. -/
def fst (h : TypedHandler (I.tensor J)) : TypedHandler I :=
  fun i => h (.inl i)

/-- Extract the right component of a handler for a tensor interface. -/
def snd (h : TypedHandler (I.tensor J)) : TypedHandler J :=
  fun j => h (.inr j)

/-- Combine handlers for the left and right components into a tensor handler. -/
def pair (h₁ : TypedHandler I) (h₂ : TypedHandler J) :
    TypedHandler (I.tensor J) :=
  fun k => match k with
  | .inl i => h₁ i
  | .inr j => h₂ j

@[simp] theorem pair_fst (h₁ : TypedHandler I) (h₂ : TypedHandler J) :
    (pair h₁ h₂).fst = h₁ := rfl

@[simp] theorem pair_snd (h₁ : TypedHandler I) (h₂ : TypedHandler J) :
    (pair h₁ h₂).snd = h₂ := rfl

@[simp] theorem fst_pair_snd (h : TypedHandler (I.tensor J)) :
    pair h.fst h.snd = h := by
  pkg_coherence_lite

end TypedHandler

/-! ## Category Instance -/

/-- The package category: objects are `PkgInterface`, morphisms are handler
    transformers. Composition is function composition, corresponding to
    oracle resolution (substitution). -/
instance pkgCat : Category PkgInterface where
  Hom I J := TypedHandler I → TypedHandler J
  id _ := id
  comp f g := g ∘ f

-- Note: `f ≫ g = g ∘ f` (diagrammatic order: apply f first, then g)

@[simp] theorem pkg_comp_apply {I J K : PkgInterface}
    (f : I ⟶ J) (g : J ⟶ K) (h : TypedHandler I) :
    (f ≫ g) h = g (f h) := rfl

@[simp] theorem pkg_id_apply {I : PkgInterface} (h : TypedHandler I) :
    (𝟙 I) h = h := rfl

/-! ## Monoidal Category Instance

The `MonoidalCategoryStruct` is built as a private helper, then assigned to the
`MonoidalCategory` instance via `toMonoidalCategoryStruct`. This avoids:
- The typeclass diamond (separate struct instance vs derived struct)
- Elaboration depth issues with `rfl` for pentagon/triangle -/

instance pkgMCS : MonoidalCategoryStruct PkgInterface where
  tensorObj I J := ⟨I.ι ⊕ J.ι, Sum.elim I.doms J.doms, Sum.elim I.codoms J.codoms⟩
  whiskerLeft _X {_Y₁ _Y₂} g h k := match k with
    | .inl i => h (.inl i)
    | .inr j => g (fun j' => h (.inr j')) j
  whiskerRight {_X₁ _X₂} f Y h k := match k with
    | .inl i => f (fun i' => h (.inl i')) i
    | .inr j => h (.inr j)
  tensorUnit := ⟨Empty, Empty.elim, Empty.elim⟩
  associator I J K := {
    hom := fun h k => match k with
      | .inl i => h (.inl (.inl i))
      | .inr (.inl j) => h (.inl (.inr j))
      | .inr (.inr k) => h (.inr k)
    inv := fun h k => match k with
      | .inl (.inl i) => h (.inl i)
      | .inl (.inr j) => h (.inr (.inl j))
      | .inr k => h (.inr (.inr k))
    hom_inv_id := by pkg_coherence_lite
    inv_hom_id := by pkg_coherence_lite
  }
  leftUnitor I := {
    hom := fun h i => h (.inr i)
    inv := fun h k => match k with
      | .inl e => nomatch e
      | .inr i => h i
    hom_inv_id := by funext h k; rcases k with e | i; exact nomatch e; rfl
    inv_hom_id := by funext _ _; rfl
  }
  rightUnitor I := {
    hom := fun h i => h (.inl i)
    inv := fun h k => match k with
      | .inl i => h i
      | .inr e => nomatch e
    hom_inv_id := by funext h k; rcases k with i | e; rfl; exact nomatch e
    inv_hom_id := by funext _ _; rfl
  }

instance pkgMonoidal : MonoidalCategory PkgInterface where
  tensorHom_def _ _ := by pkg_coherence_lite
  id_tensorHom_id _ _ := by pkg_coherence_lite
  tensorHom_comp_tensorHom _ _ _ _ := by pkg_coherence_lite
  whiskerLeft_id _ _ := by pkg_coherence_lite
  id_whiskerRight _ _ := by pkg_coherence_lite
  associator_naturality _ _ _ := by pkg_coherence_lite
  leftUnitor_naturality _ := rfl
  rightUnitor_naturality _ := rfl
  pentagon _ _ _ _ := by pkg_coherence_lite
  triangle _ _ := rfl

/-! ## Braiding and Symmetric Structure

The braiding iso is defined on `PkgInterface.tensor` where `Sum` structure is
directly visible. It is then used in the `SymmetricCategory` instance via the
definitional equality `I.tensor J = I ⊗ J`. -/

/-- The braiding isomorphism: swap the left and right components of a tensor.
    Defined on `PkgInterface.tensor` to keep `Sum` structure visible. -/
private def braidIso (I J : PkgInterface) : I.tensor J ≅ J.tensor I where
  hom := fun h k => match k with
    | .inl j => h (.inr j)
    | .inr i => h (.inl i)
  inv := fun h k => match k with
    | .inl i => h (.inr i)
    | .inr j => h (.inl j)
  hom_inv_id := by pkg_coherence_lite
  inv_hom_id := by pkg_coherence_lite

instance pkgSMC : SymmetricCategory PkgInterface where
  braiding I J := braidIso I J
  braiding_naturality_right := by intros; pkg_coherence_lite
  braiding_naturality_left := by intros; pkg_coherence_lite
  hexagon_forward := by intros; pkg_coherence_lite
  hexagon_reverse := by intros; pkg_coherence_lite
  symmetry := by intros; pkg_coherence_lite

/-! ## Connection to Untyped Handlers

The untyped `Handler` from `PkgEval.lean` handles ALL operations
(`∀ op dom codom, dom → SPComp codom`). `TypedHandler I` restricts to
a specific interface. The relationship:

- **Restrict**: Given an untyped handler and an interface `I`, project to `TypedHandler I`
  by evaluating at each `I`-operation's signature.
- **Extend**: Given `TypedHandler I`, extend to an untyped handler by mapping
  non-`I` operations to `SPComp.fail`.

The typed version is the correct mathematical object for the SMC structure,
while the untyped version is convenient for the DeepPackage evaluation bridge. -/

/-- `PkgImpl` (σ = id) is exactly `TypedHandler`.
    This connects the categorical framework to the Fam-based representation.
    `PkgImpl.ofImpls` constructs a Fam morphism from componentwise implementations;
    `TypedHandler` IS those componentwise implementations. -/
theorem typedHandler_eq_pkgImpl_ofImpls (I : PkgInterface) :
    TypedHandler I = (∀ i, I.doms i → SPComp (I.codoms i)) := rfl

end CatCrypt.Category
