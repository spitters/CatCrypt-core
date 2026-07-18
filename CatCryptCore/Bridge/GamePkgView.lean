/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Bridge.SemPkg

/-!
# Game Package View: UC-Free Game/Handler Layer

The UC-free core of the PackageView framework: the isomorphism between SPComp
games and single-operation typed handlers, plus the handler simp lemmas that
drive the `pkg_coherence` tactic.

The statistical-distance / UC machinery (`handlerSdist`, oracle-swap theorems,
`OracleGame`, `PackageView`) lives downstream in the dev-repo layer over this
file.

## Main Definitions

* `singleIface` — interface with one operation
* `GamePkg.ofGame` / `GamePkg.toGame` — isomorphism `(A → SPComp B) ≃ GamePkg A B`
-/

set_option autoImplicit false

/-! ## Supporting SPComp law

`bind_fail_right'` is a pure `SPComp` algebra law consumed by the
`pkg_coherence` simp set (and by `uc_coherence` in the larger UC development). -/

namespace CatCrypt.Core

open CatCrypt.Prob

/-- Binding into a constant-failure continuation gives failure. -/
theorem SPComp.bind_fail_right' {α β : Type} (c : SPComp α) :
    SPComp.bind c (fun _ => (SPComp.fail : SPComp β)) = SPComp.fail := by
  funext h
  simp only [SPComp.bind_def, SPComp.fail]
  show SDistr.bind (c h) (fun _ => SDistr.fail) = SDistr.fail
  simp only [SDistr.bind, SDistr.fail]
  calc PMF.bind (c h) _ = PMF.bind (c h) (fun _ => PMF.pure (none : Option (β × Heap))) := by
        congr 1; funext oa; cases oa <;> rfl
    _ = PMF.pure none := PMF.bind_const _ _

end CatCrypt.Core

namespace CatCrypt.Bridge.PkgView

open CatCrypt.Core CatCrypt.Category
open CategoryTheory

/-! ## Single-Operation Interface -/

/-- A package interface with exactly one operation of type `A → SPComp B`. -/
def singleIface (A B : Type) : PkgInterface where
  ι := Unit
  doms := fun _ => A
  codoms := fun _ => B

/-- A handler for a single-operation interface.
    Isomorphic to `A → SPComp B` via `ofGame`/`toGame`. -/
abbrev GamePkg (A B : Type) := TypedHandler (singleIface A B)

/-- Wrap an SPComp game as a single-operation handler. -/
def GamePkg.ofGame {A B : Type} (game : A → SPComp B) : GamePkg A B :=
  fun _ => game

/-- Extract the game from a single-operation handler. -/
def GamePkg.toGame {A B : Type} (pkg : GamePkg A B) : A → SPComp B :=
  pkg ()

@[simp] theorem GamePkg.ofGame_toGame {A B : Type} (game : A → SPComp B) :
    (GamePkg.ofGame game).toGame = game := rfl

@[simp] theorem GamePkg.toGame_ofGame {A B : Type} (pkg : GamePkg A B) :
    GamePkg.ofGame pkg.toGame = pkg := by
  funext ⟨⟩; rfl

/-- The isomorphism between games and single-operation handlers. -/
def gamePkgEquiv (A B : Type) : (A → SPComp B) ≃ GamePkg A B where
  toFun := GamePkg.ofGame
  invFun := GamePkg.toGame
  left_inv _ := rfl
  right_inv pkg := by funext ⟨⟩; rfl

/-! ## Oracle Games (Package Category Morphisms) -/

/-- An oracle game is a morphism in the package category: it takes an oracle
    handler and produces a game.

    Concretely, `OracleGame O A B` is `TypedHandler O → TypedHandler (singleIface A B)`,
    i.e., a morphism `O ⟶ singleIface A B` in `pkgCat`. -/
abbrev OracleGame (O : PkgInterface) (A B : Type) :=
  O ⟶ singleIface A B

/-- Construct an oracle game from a function that takes an oracle handler
    and produces a game. -/
def OracleGame.mk {O : PkgInterface} {A B : Type}
    (run : TypedHandler O → A → SPComp B) : OracleGame O A B :=
  fun h => GamePkg.ofGame (run h)

/-- Run an oracle game with a specific handler. -/
def OracleGame.run {O : PkgInterface} {A B : Type}
    (game : OracleGame O A B) (h : TypedHandler O) : A → SPComp B :=
  GamePkg.toGame (game h)

/-- An oracle game from a single-oracle function.
    The common case: the game takes one oracle `X → SPComp Y`. -/
def OracleGame.ofSingleOracle {X Y A B : Type}
    (run : (X → SPComp Y) → A → SPComp B) : OracleGame (singleIface X Y) A B :=
  OracleGame.mk (fun h => run (h ()))

/-! ## Handler Simp Lemmas for `pkg_coherence`

These lemmas reduce handler operations to pointwise equalities,
enabling the `pkg_coherence` tactic. -/

@[simp] theorem TypedHandler.pair_inl {I J : PkgInterface}
    (h₁ : TypedHandler I) (h₂ : TypedHandler J) (i : I.ι) :
    TypedHandler.pair h₁ h₂ (.inl i) = h₁ i := rfl

@[simp] theorem TypedHandler.pair_inr {I J : PkgInterface}
    (h₁ : TypedHandler I) (h₂ : TypedHandler J) (j : J.ι) :
    TypedHandler.pair h₁ h₂ (.inr j) = h₂ j := rfl

@[simp] theorem GamePkg.ofGame_apply {A B : Type} (game : A → SPComp B) :
    (GamePkg.ofGame game) () = game := rfl

@[simp] theorem singleIface_doms {A B : Type} :
    (singleIface A B).doms = fun _ => A := rfl

@[simp] theorem singleIface_codoms {A B : Type} :
    (singleIface A B).codoms = fun _ => B := rfl

end CatCrypt.Bridge.PkgView
