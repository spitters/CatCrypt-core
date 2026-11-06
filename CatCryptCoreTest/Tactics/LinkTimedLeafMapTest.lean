/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.LinkTimed

/-!
# Tests of `link_timed` through the soundness theorem at a leaf map of zero cost

Fresh definitions whose costed trees contain a costed bind with a continuation that returns a
function of the bound value at zero cost (the leaf map of the comparison, `TreeLeA.map_right`,
`TreeLeA.map_left`); the theorem `T.d_run`, which `link_timed` proves only through the soundness
theorem, is checked for each. In `lmTriple` and `lmTermProj` the term binds the call as the
costed form does, and the stuck binds compare by `CostLeA.bind`; in `lmTable.coins` and
`lmTableFirst.coins` the first trees of the binds have different leaves and the comparison reads
the leaf map of the costed side (without it, the first falls back to the walk and the second is
refused).

* `lmTriple`: a sample, a call returning a triple, and the projection onto two components;
* `lmTermProj`: a call returning a pair and the first component, projected in the term;
* `lmTable.coins`: the coin stage of a structure-valued reduction that calls the coin stage of
  its argument, samples a table `Fin 3 → Bool` and returns the coins with the table; its costed
  form returns the costed table of `derive_timed` and projects it onto the plain one, a leaf map
  after a costed call and a costed table sample, against one call in the term;
* `lmTableFirst.coins`: the same with the table `Fin 2 → R` over a type parameter sampled before
  the call.

## Main definitions

* `lmTriple`, `lmTermProj`, `LmStage`, `lmTable`, `lmTableFirst`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.LinkTimedLeafMapTest

open CatCrypt.Core CatCrypt.Complexity.D CatCrypt.Complexity.D.Reflect

/-- Sample a bit, call the adversary on it and return the first two components of its answer. -/
noncomputable def lmTriple (A : Bool → SPComp (Bool × Bool × Bool)) : SPComp (Bool × Bool) := do
  let b ← SPComp.sample Bool
  let t ← A b
  return (t.1, t.2.1)

derive_reduction lmTriple (adv := A)

reflect_d lmTriple.tree

link_timed lmTriple

example := @lmTriple.tree.d_run

/-- Call the adversary and return the first component of its answer. -/
noncomputable def lmTermProj (A : Bool → SPComp (Bool × Bool)) (x : Bool) : SPComp Bool :=
  Prod.fst <$> A x

derive_reduction lmTermProj (adv := A)

reflect_d lmTermProj.tree

link_timed lmTermProj

example := @lmTermProj.tree.d_run

/-- A two-stage adversary: a coin stage and a response map. -/
structure LmStage (X C : Type) where
  /-- The coin stage. -/
  coins : X → SPComp C
  /-- The response map. -/
  out : X → C → Bool

end CatCrypt.Tactics.LinkTimedLeafMapTest

derive_timed_structure CatCrypt.Tactics.LinkTimedLeafMapTest.LmStage

namespace CatCrypt.Tactics.LinkTimedLeafMapTest

open CatCrypt.Core

/-- The coin stage of `A`, then a sampled table `Fin 3 → Bool`, returned with the coins. -/
noncomputable def lmTable {X : Type} (A : LmStage X Bool) : LmStage X (Bool × (Fin 3 → Bool))
    where
  coins x := do
    let c ← A.coins x
    let tab ← SPComp.sample (Fin 3 → Bool)
    return (c, tab)
  out x p := A.out x p.1

derive_reduction lmTable

reflect_d lmTable.coins.tree

link_timed lmTable.coins

example := @lmTable.coins.tree.d_run

/-- A sampled table `Fin 2 → R` over a type parameter, then the coin stage of `A`, returned
together. -/
noncomputable def lmTableFirst {X R : Type} [Fintype R] [Nonempty R] (A : LmStage X Bool) :
    LmStage X (Bool × (Fin 2 → R)) where
  coins x := do
    let tab ← SPComp.sample (Fin 2 → R)
    let c ← A.coins x
    return (c, tab)
  out x p := A.out x p.1

derive_reduction lmTableFirst

reflect_d lmTableFirst.coins.tree

link_timed lmTableFirst.coins

example := @lmTableFirst.coins.tree.d_run

end CatCrypt.Tactics.LinkTimedLeafMapTest
