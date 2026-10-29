/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimedStructure
public import CatCryptCore.Tactics.StdCosts
public import CatCryptCore.Complexity.HandlerCost

/-!
# Tests of the registered costs of `Finset.toList` and `Fin.foldl`, and of
`derive_timed_structure` on universe-polymorphic structures and handler kinds

* `Fin.foldl.timedCost` at a constant step cost, and `derive_cost` of a function folding over
  `Fin n`: its cost is `4 n + 2`, by `Fin.foldl.timedCost_const` and by `Fin.foldl.timedCost_le`.
* `derive_cost` of the length of `s.toList`: its cost is `4 |s| + 4`.
* `UAdv.{u}`, a universe-polymorphic structure with a package field `pkg : ℕ → DeepPackage.{u}`
  and a computation field: its mirror `UAdv.Timed.{u}` and its time bound.
* `derive_timed_structure DeepPackage` is refused: a package is a handler kind.
* A package-valued reduction is certified by the time bound of the package it returns.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CatCrypt.Tactics.StdCostsFoldTest

open CatCrypt.Deep CatCrypt.Core

/-! ## `Fin.foldl` and `Finset.toList` -/

/-- Three steps of constant cost two cost sixteen units. -/
example : Fin.foldl.timedCost ℕ 3 (fun a i => a + i.val) (fun _ _ => 2) 0 = 16 := by
  simp [Fin.foldl.timedCost_const]

/-- The sum of the indices below `n`. -/
def sumFin (n : ℕ) : ℕ := Fin.foldl n (fun a i => a + i.val) 0

derive_cost sumFin

/-- The derived cost of `sumFin n`, through the constant step cost. -/
example (n : ℕ) : sumFin.timedCost n = 4 * n + 2 := by
  simp [sumFin.timedCost, Fin.foldl.timedCost_const]; omega

/-- The derived cost of `sumFin n`, through the bound on the step cost. -/
example (n : ℕ) : sumFin.timedCost n ≤ 4 * n + 2 := by
  have := Fin.foldl.timedCost_le n (fun a i => a + i.val) (fun _ _ => 1) (k := 1)
    (fun _ _ => le_rfl) 0
  simp only [sumFin.timedCost]; omega

/-- The length of the enumeration of a finite set. -/
def cardList (s : Finset ℕ) : ℕ := s.toList.length

derive_cost cardList

/-- The derived cost of `cardList s` is linear in the cardinality. -/
example (s : Finset ℕ) : cardList.timedCost s = 4 * s.card + 4 := by
  simp [cardList.timedCost, Finset.toList.timedCost_eq, List.length.timedCost_eq]; omega

/-! ## Universe-polymorphic structures -/

/-- A universe-polymorphic adversary with a package field and a computation field. -/
structure UAdv.{u} where
  /-- A package for each index. -/
  pkg : ℕ → DeepPackage.{u}
  /-- A computation. -/
  run : SPComp Bool

derive_timed_structure UAdv

/-- The time bound of the mirror bounds every package and the computation. -/
example (A' : UAdv.Timed.{1}) (h : ℕ → ℕ) (T R : ℕ) :
    UAdv.Timed.TimeBound A' h T R ↔
      (∀ n, (A'.pkg n).TimeBound h T) ∧ SPTree.Timed.stepTime (A'.runCost, A'.run) ≤ R :=
  Iff.rfl

/-! ## Handler kinds -/

/--
error: derive_timed_structure: `CatCrypt.Deep.DeepPackage` is a handler kind, priced by `CatCrypt.Deep.DeepPackage.handlerBound` wherever a value of it occurs; it has no costed mirror
-/
#guard_msgs in
derive_timed_structure DeepPackage

/-- A package-valued reduction: the empty package at every index. -/
def emptyRed (_ : ℕ) : DeepPackage.{0} := DeepPackage.empty

/-- A package-valued reduction is certified by the time bound of its result. -/
theorem emptyRed.timeBound (x : ℕ) (h : ℕ → ℕ) : (emptyRed x).TimeBound h 0 := by
  intro _ _ _ hmem
  cases hmem

end CatCrypt.Tactics.StdCostsFoldTest
