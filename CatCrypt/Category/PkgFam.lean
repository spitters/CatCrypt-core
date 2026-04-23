/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Category.Fam
import CatCrypt.Category.KlSPComp
import CatCrypt.Deep.Package

/-!
# Package Interfaces and Fam(KlSPComp) Morphisms

A **package interface** specifies operation signatures via an index type `ι` with
domain and codomain families in `KlSPComp`.

A **package implementation** (`PkgImpl`) is a morphism in `Fam(KlSPComp)` from the
domain family to the codomain family. Fam composition is Kleisli sequencing
(bind at each operation), NOT oracle substitution. See `SemPkg.lean` for the
package category with substitution-style composition.

**Linking vs composition**: `PkgImpl.link` computes as `SPComp.bind` at each
operation index — this is a data pipeline (first-order), not oracle resolution
(second-order). Cryptographic package linking is oracle substitution, which is
modeled by the `Category PkgInterface` in `SemPkg.lean`.

**Parallel composition** (`PkgImpl.par`) dispatches operations by `Sum` index.
This IS the correct parallel composition and is shared with the package category.

## Main definitions

* `PkgInterface` — operation signatures (index type, domains, codomains)
* `PkgInterface.tensor` — parallel combination (Sum on indices)
* `PkgInterface.unit` — empty interface (Empty index)
* `PkgImpl` — Fam(KlSPComp) morphism (Kleisli arrow at each operation)
* `PkgImpl.ofImpls` — construct from componentwise implementations (σ = id)
* `PkgImpl.link` — Kleisli-bind composition (NOT oracle substitution)
* `PkgImpl.par` — parallel composition via Fam tensor
* `DeepInterface.toPkgInterface` — bridge from deep-embedding interfaces

## Semantic characterization

* `link_map`: linking at operation `i` is `SPComp.bind (p₁.map i x) (p₂.map (p₁.σ i))`
* `par_map_inl`: parallel at `.inl i` dispatches to `p₁.map i`
* `par_map_inr`: parallel at `.inr j` dispatches to `p₂.map j`

## SMC structure

Since `PkgInterface.tensor`/`unit` correspond definitionally to `FamObj.tensorObj`/`unitObj`,
the monoidal category laws apply directly to `PkgImpl` parallel composition.
The full SMC structure on `PkgInterface` (with substitution-style composition)
is in `SemPkg.lean`.
-/

namespace CatCrypt.Category

open CategoryTheory MonoidalCategory
open CatCrypt.Core

/-! ## Package Interface -/

/-- A package interface specifies operation signatures.
    Each operation is indexed by `ι` with domain type `doms i` and codomain type `codoms i`,
    both living in `KlSPComp` (= Type, viewed as objects of the Kleisli category of SPComp). -/
structure PkgInterface where
  /-- Index type for operations -/
  ι : Type
  /-- Domain type of each operation -/
  doms : ι → KlSPComp
  /-- Codomain type of each operation -/
  codoms : ι → KlSPComp

namespace PkgInterface

/-- The domain family as a `FamObj KlSPComp`. -/
def domFam (I : PkgInterface) : FamObj KlSPComp := ⟨I.ι, I.doms⟩

/-- The codomain family as a `FamObj KlSPComp`. -/
def codomFam (I : PkgInterface) : FamObj KlSPComp := ⟨I.ι, I.codoms⟩

/-! ### Tensor and Unit -/

/-- Parallel combination of interfaces: index by `Sum`, families by `Sum.elim`. -/
def tensor (I J : PkgInterface) : PkgInterface where
  ι := I.ι ⊕ J.ι
  doms := Sum.elim I.doms J.doms
  codoms := Sum.elim I.codoms J.codoms

/-- The empty interface (no operations). -/
def unit : PkgInterface where
  ι := Empty
  doms := Empty.elim
  codoms := Empty.elim

/-! ### Correspondence with Fam's tensor and unit

These are all `rfl` because both sides expand to the same `⟨ι₁ ⊕ ι₂, Sum.elim ...⟩`
(resp. `⟨Empty, Empty.elim⟩`). This definitional equality is the key insight:
packages inherit their SMC structure from `Fam.lean` with zero proof effort. -/

@[simp] theorem tensor_domFam (I J : PkgInterface) :
    (I.tensor J).domFam = FamObj.tensorObj I.domFam J.domFam := rfl

@[simp] theorem tensor_codomFam (I J : PkgInterface) :
    (I.tensor J).codomFam = FamObj.tensorObj I.codomFam J.codomFam := rfl

@[simp] theorem unit_domFam :
    PkgInterface.unit.domFam = (FamObj.unitObj : FamObj KlSPComp) := rfl

@[simp] theorem unit_codomFam :
    PkgInterface.unit.codomFam = (FamObj.unitObj : FamObj KlSPComp) := rfl

end PkgInterface

/-! ## Package Implementation -/

/-- A package implementation for interface `I` is a morphism in `Fam(KlSPComp)`
    from the domain family to the codomain family.

    Concretely, this consists of:
    - An equivalence `σ : I.ι ≃ I.ι` permuting operation indices
    - Implementations `map i : I.doms i → SPComp (I.codoms (σ i))` for each operation

    When `σ = id` (the common case), each operation `i` has a direct implementation
    `I.doms i → SPComp (I.codoms i)`. -/
abbrev PkgImpl (I : PkgInterface) := I.domFam ⟶ I.codomFam

namespace PkgImpl

variable {I J : PkgInterface}

/-! ### Construction -/

/-- Construct a package from componentwise implementations (with `σ = id`). -/
def ofImpls (I : PkgInterface)
    (impls : ∀ i, I.doms i → SPComp (I.codoms i)) : PkgImpl I :=
  ⟨Equiv.refl _, impls⟩

@[simp] theorem ofImpls_σ (I : PkgInterface)
    (impls : ∀ i, I.doms i → SPComp (I.codoms i)) :
    (ofImpls I impls).σ = Equiv.refl _ := rfl

@[simp] theorem ofImpls_map (I : PkgInterface)
    (impls : ∀ i, I.doms i → SPComp (I.codoms i)) (i : I.ι) :
    (ofImpls I impls).map i = impls i := rfl

/-! ### Linking = Fam Composition (Kleisli Sequencing)

**Note**: This is Kleisli-bind composition (sequencing), not oracle substitution.
At each operation `i`, `link` computes as `SPComp.bind (p₁.map i x) (p₂.map (p₁.σ i))`,
i.e., run `p₁`, then feed the result into `p₂`. This models a data pipeline, not
cryptographic package linking (which is oracle resolution — see `SemPkg.lean`). -/

/-- Linking two packages: composition in `Fam(KlSPComp)`. -/
noncomputable def link {D M C : FamObj KlSPComp}
    (p₁ : D ⟶ M) (p₂ : M ⟶ C) : D ⟶ C := p₁ ≫ p₂

/-- The index permutation of a linked package is the composition of permutations. -/
@[simp] theorem link_σ {D M C : FamObj KlSPComp}
    (p₁ : D ⟶ M) (p₂ : M ⟶ C) :
    (link p₁ p₂).σ = p₁.σ.trans p₂.σ := rfl

/-- Linking computes as Kleisli bind at each operation:
    run `p₁` on the input, then feed the result to `p₂`. -/
@[simp] theorem link_map {D M C : FamObj KlSPComp}
    (p₁ : D ⟶ M) (p₂ : M ⟶ C) (i : D.ι) (x : D.objs i) :
    (link p₁ p₂).map i x = SPComp.bind (p₁.map i x) (p₂.map (p₁.σ i)) := rfl

/-! ### Parallel Composition = Fam Tensor

Parallel composition dispatches operations to the correct component:
- Operations indexed by `Sum.inl i` go to the left package `p₁`
- Operations indexed by `Sum.inr j` go to the right package `p₂` -/

/-- Parallel composition of packages: tensor in `Fam(KlSPComp)`. -/
noncomputable def par (p₁ : PkgImpl I) (p₂ : PkgImpl J) : PkgImpl (I.tensor J) :=
  p₁ ⊗ₘ p₂

/-- Left operations are permuted by `p₁`'s permutation. -/
@[simp] theorem par_σ_inl (p₁ : PkgImpl I) (p₂ : PkgImpl J) (i : I.ι) :
    (par p₁ p₂).σ (.inl i) = .inl (p₁.σ i) := rfl

/-- Right operations are permuted by `p₂`'s permutation. -/
@[simp] theorem par_σ_inr (p₁ : PkgImpl I) (p₂ : PkgImpl J) (j : J.ι) :
    (par p₁ p₂).σ (.inr j) = .inr (p₂.σ j) := rfl

/-- At a left operation `.inl i`, parallel composition dispatches to `p₁`. -/
@[simp] theorem par_map_inl (p₁ : PkgImpl I) (p₂ : PkgImpl J) (i : I.ι) (x : I.doms i) :
    (par p₁ p₂).map (.inl i) x = p₁.map i x :=
  SPComp.bind_pure (p₁.map i x)

/-- At a right operation `.inr j`, parallel composition dispatches to `p₂`. -/
@[simp] theorem par_map_inr (p₁ : PkgImpl I) (p₂ : PkgImpl J) (j : J.ι) (x : J.doms j) :
    (par p₁ p₂).map (.inr j) x = p₂.map j x :=
  SPComp.pure_bind x (p₂.map j)

/-! ### SMC Laws for Parallel Composition

The monoidal laws for parallel composition (tensor, associator, braiding) hold
for `PkgImpl` via the definitional equality between `PkgInterface.tensor`/`unit`
and `FamObj.tensorObj`/`unitObj`. These are inherited from `Fam.lean`.

The full symmetric monoidal category structure on `PkgInterface` — with
substitution-style composition (oracle resolution) rather than Fam's Kleisli
sequencing — is in `SemPkg.lean`. -/

end PkgImpl

/-! ## Bridge: DeepInterface → PkgInterface -/

open CatCrypt.Deep in
/-- Convert a `DeepInterface` (list-based, from the deep embedding) to a `PkgInterface`
    (family-based, for the categorical framework) via `Fin` indexing.
    Each position in the operation list becomes a `Fin` index. -/
def DeepInterface.toPkgInterface (I : DeepInterface) : PkgInterface where
  ι := Fin I.ops.length
  doms i := (I.ops.get i).2.1
  codoms i := (I.ops.get i).2.2

open CatCrypt.Deep in
/-- Append two deep interfaces (concatenate operation lists). -/
def DeepInterface.append (I J : DeepInterface) : DeepInterface := ⟨I.ops ++ J.ops⟩

/-! The tensor of `toPkgInterface` corresponds to the append of `DeepInterface`:
`(I.append J).toPkgInterface` and `I.toPkgInterface.tensor J.toPkgInterface`
have the same operations, indexed by `Fin (m + n)` vs `Fin m ⊕ Fin n` respectively.
The equivalence `finSumFinEquiv` from Mathlib connects these index types,
with `List.getElem_append_left`/`List.getElem_append_right` showing the families match. -/

end CatCrypt.Category
