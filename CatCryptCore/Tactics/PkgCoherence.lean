/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Bridge.SemPkg
import CatCryptCore.Bridge.GamePkgView

/-!
# Package Coherence Tactic

Automation for proving structural equalities between package compositions.

## Design (Canonicalization by Normalization)

`PkgInterface` already carries genuine Mathlib `MonoidalCategory` and
`SymmetricCategory` instances (`pkgMonoidal` / `pkgSMC` in
`Bridge/SemPkg.lean`), so the structural isos `α_`, `λ_`, `ρ_`, `β_` used
below are Mathlib's own. `pkg_coherence` re-implements the coherence decider
at the **applied-handler** level:

1. **`funext`** to introduce the handler argument
2. **`sum_cases`** to exhaustively case-split on nested `Sum` types
3. **`simp`** with handler + package simp lemmas to normalize
4. **`rfl`** to close each branch

This works because the monoidal structure on `PkgInterface` uses `Sum` on
index types, so all structural morphisms (associators, unitors, braiding)
reduce to `Sum` case analysis with `rfl` closures.

## Main Tactic

* `pkg_coherence` — closes goals of the form `f = g` where `f, g` are
  handler transformers built from structural operations
-/

set_option autoImplicit false

open CatCrypt.Core CatCrypt.Category CatCrypt.Bridge.PkgView
open CategoryTheory MonoidalCategory

/-! ## Package Coherence Simp Set

Collects all simp lemmas needed for package-level structural equalities. -/

/-- Close structural equalities between package handler expressions.

    Works on goals of the form:
    - `TypedHandler.pair h₁ h₂ = TypedHandler.pair h₃ h₄`
    - `(f ≫ g) h = g (f h)` (package category composition)
    - `(α_ I J K).hom h k = ...` (monoidal structural isos)
    - Handler equality under reassociation, braiding, etc.

    Strategy:
    1. Try `rfl` for trivially equal terms
    2. Try `funext` + `sum_cases` + `simp` + `rfl` for structural terms
    3. Fall back to `funext` + `ext` + `sum_cases` for deeper goals -/
macro "pkg_coherence" : tactic =>
  `(tactic| (
    first
    | rfl
    | (funext _
       sum_cases
       all_goals (
         simp only [
           -- Package category
           pkg_comp_apply, pkg_id_apply,
           -- Handler operations
           TypedHandler.pair_inl, TypedHandler.pair_inr,
           TypedHandler.pair_fst, TypedHandler.pair_snd,
           TypedHandler.fst_pair_snd,
           -- GamePkg
           GamePkg.ofGame_apply, GamePkg.ofGame_toGame,
           -- SPComp monad laws
           SPComp.pure_bind, SPComp.bind_pure, SPComp.bind_assoc,
           SPComp.bind_fail_right']
         <;> rfl))
    | (funext _ _
       sum_cases
       all_goals (
         simp only [
           pkg_comp_apply, pkg_id_apply,
           TypedHandler.pair_inl, TypedHandler.pair_inr,
           TypedHandler.pair_fst, TypedHandler.pair_snd,
           TypedHandler.fst_pair_snd,
           GamePkg.ofGame_apply, GamePkg.ofGame_toGame,
           SPComp.pure_bind, SPComp.bind_pure, SPComp.bind_assoc,
           SPComp.bind_fail_right']
         <;> rfl))))

/-! ## Test Suite -/

section PkgCoherenceTests

variable {I J K L : PkgInterface}

-- Identity laws
example (f : I ⟶ J) (h : TypedHandler I) : (𝟙 I ≫ f) h = f h := by pkg_coherence
example (f : I ⟶ J) (h : TypedHandler I) : (f ≫ 𝟙 J) h = f h := by pkg_coherence

-- Associativity of composition
example (f : I ⟶ J) (g : J ⟶ K) (h₁ : K ⟶ L) (x : TypedHandler I) :
    ((f ≫ g) ≫ h₁) x = (f ≫ (g ≫ h₁)) x := by pkg_coherence

-- Handler pair reconstruction
example (h : TypedHandler (I.tensor J)) :
    TypedHandler.pair h.fst h.snd = h := by pkg_coherence

-- Pair projections
example (h₁ : TypedHandler I) (h₂ : TypedHandler J) :
    (TypedHandler.pair h₁ h₂).fst = h₁ := by pkg_coherence

example (h₁ : TypedHandler I) (h₂ : TypedHandler J) :
    (TypedHandler.pair h₁ h₂).snd = h₂ := by pkg_coherence

-- Tensor structural iso: associator
example (h : TypedHandler ((I.tensor J).tensor K)) (k : I.ι) :
    (pkgMCS.associator I J K).hom h (.inl k) = h (.inl (.inl k)) := by rfl

example (h : TypedHandler ((I.tensor J).tensor K)) (k : J.ι) :
    (pkgMCS.associator I J K).hom h (.inr (.inl k)) = h (.inl (.inr k)) := by rfl

example (h : TypedHandler ((I.tensor J).tensor K)) (k : K.ι) :
    (pkgMCS.associator I J K).hom h (.inr (.inr k)) = h (.inr k) := by rfl

-- Braiding: swap components (via symmetric category instance)
example (h : TypedHandler (I.tensor J)) (i : I.ι) :
    (β_ I J).hom h (.inr i) = h (.inl i) := by rfl

example (h : TypedHandler (I.tensor J)) (j : J.ι) :
    (β_ I J).hom h (.inl j) = h (.inr j) := by rfl

-- GamePkg roundtrip
example {A B : Type} (game : A → SPComp B) :
    (GamePkg.ofGame game).toGame = game := by pkg_coherence

end PkgCoherenceTests

/-! ## Oracle Coherence

Higher-level tactic for oracle game proofs: apply structural
simplification to oracle-parameterized games. -/

/-- Simplify oracle game expressions.

    Unfolds `OracleGame.run`, `OracleGame.mk`, `GamePkg.toGame`,
    `GamePkg.ofGame` and then applies `pkg_coherence`. -/
macro "oracle_simp" : tactic =>
  `(tactic| (
    simp only [OracleGame.run, OracleGame.mk, OracleGame.ofSingleOracle,
               GamePkg.toGame, GamePkg.ofGame, GamePkg.ofGame_apply,
               GamePkg.ofGame_toGame]))
