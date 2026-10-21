/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCryptCore.XDijkstra.XTimedMonad
public meta import CatCryptCore.Crypto.Messaging.KEMCKA
import all CatCryptCore.Crypto.Messaging.KEMCKA

@[expose] public meta section
set_option autoImplicit false

/-!
# Tests for `XTimedMonad`

The time bound `ckaPubRedOf.tree.timeBound_timed` of the costed distinguisher of `KEMCKA`,
proved through the `TimedM` view: the costed tree is the tree of a `gdo` block, and `xmvcgen!`
reduces the grade bound of the block to an inequality between numbers.
-/

namespace CatCrypt.XDijkstra.XTimedMonadTest

open CatCrypt.Core CatCrypt.Crypto.Messaging

/-- The costed distinguisher of `ckaPubRedOf` as a `gdo` block: the costed public computation
`pubT`, lifted at its time, then the call of `A` behind its step cost, moved to the common index
`T + a + tv + 2`. -/
def pubRedT {Y P V : Type} (view : P → Y → V) (viewCost : P → Y → ℕ)
    (A : V → SPTree.Timed Bool) (ACost : V → ℕ) {T a tv : ℕ}
    (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a) (hv : ∀ c y, viewCost c y ≤ tv)
    (pubT : SPTree.Timed P) (y : Y) : TimedM (pubT.time + (T + a + tv + 2)) Bool := gdo
  let x ← TimedM.lift pubT
  (TimedM.ofStep (1 + (ACost (view x y) + (1 + viewCost x y))) (A (view x y))).relax (by
    have := hA (view x y); have := hAc (view x y); have := hv x y
    omega)

/-- The tree of `pubRedT` is the costed form `ckaPubRedOf.tree.timed`. -/
theorem pubRedT_tree {Y P V : Type} (pub : SPComp P) (view : P → Y → V)
    (viewCost : P → Y → ℕ) (A : V → SPTree.Timed Bool) (ACost : V → ℕ) {T a tv : ℕ}
    (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a) (hv : ∀ c y, viewCost c y ≤ tv)
    (pubT : SPTree.Timed P) (y : Y) :
    (pubRedT view viewCost A ACost hA hAc hv pubT y).tree =
      ckaPubRedOf.tree.timed pub view viewCost A ACost y pubT := by
  simp only [pubRedT, TimedM.gbind_eq, TimedM.tree_bind, TimedM.tree_lift, TimedM.tree_relax,
    TimedM.tree_ofStep, SPTree.Timed.delay, Nat.zero_add, Prod.mk.eta, ckaPubRedOf.tree.timed]

/-- `ckaPubRedOf.tree.timeBound_timed` through the `TimedM` view: `xmvcgen!` reduces the grade
bound of `pubRedT` to `pubT.time + (T + a + tv + 2) ≤ T + a + tv + tp + 2`. -/
theorem ckaPubRedOf_timeBound_xmvcgen {Y P V : Type} (pub : SPComp P) (view : P → Y → V)
    (viewCost : P → Y → ℕ) (A : V → SPTree.Timed Bool) (ACost : V → ℕ) {T a tv tp : ℕ}
    (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a) (hv : ∀ c y, viewCost c y ≤ tv)
    (pubT : SPTree.Timed P) (hp : pubT.time ≤ tp) (y : Y) :
    SPTree.Timed.stepTime (ckaPubRedOf.tree.timed pub view viewCost A ACost y pubT) ≤
      T + a + tv + tp + 2 := by
  have hb : (XWP.xwp (ps := psTimed) (Ω := Prop)
      (pubRedT view viewCost A ACost hA hAc hv pubT y)).grade.1 ≤ T + a + tv + tp + 2 := by
    xmvcgen!
    omega
  rw [← pubRedT_tree pub view viewCost A ACost hA hAc hv pubT y]
  exact (pubRedT view viewCost A ACost hA hAc hv pubT y).stepTime_le.trans hb

end CatCrypt.XDijkstra.XTimedMonadTest
