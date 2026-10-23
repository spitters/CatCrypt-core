/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.AutoTime

/-!
# Tests for field paths in type positions, the cost of the empty set and carriers in `Type`

Reductions of the shapes of the simulators `groth16_game_sim`, `plonk_game_sim`,
`adaptiveSimulator`, `blindSim` and `friSim`:

* a simulator over a parameter structure whose input is a statement–witness pair in the
  subtype `{xw // P.relation xw.1 xw.2 = true}` of a relation field: the field `P.relation`
  occurs in the type of the input binder and stays a projection of `P`;
* a computation that passes the empty finite set to an adversary, priced by the registered
  cost `Finset.empty.timedCost`;
* the blinding simulator and the FRI opening simulator at carriers in `Type`.

Each is derived by `derive_reduction`; the compile equation and the erasure theorem of the
first two are pinned, and the time of each is bounded by `time_bound`.

## Main results

* the time theorems of the four test reductions, each by `time_bound`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveReductionFieldTypeTest

open CatCrypt.Core

/-! ## A relation field in the type of the input -/

/-- Parameters of a proof system: statements, witnesses, proofs, a reference string, a
trapdoor, a simulator and a relation. -/
structure ZKParams where
  Statement : Type
  Witness : Type
  Proof : Type
  CRS : Type
  Trapdoor : Type
  /-- The simulator: a proof from the reference string, the trapdoor and the statement. -/
  simulate : CRS → Trapdoor → Statement → SPComp Proof
  /-- The relation. -/
  relation : Statement → Witness → Bool

/-- Statement–witness pairs in the relation of `P`. -/
abbrev ZKRel (P : ZKParams) : Type :=
  {xw : P.Statement × P.Witness // P.relation xw.1 xw.2 = true}

/-- The simulated game: the simulator's proof for the statement of the pair. -/
noncomputable def zkSim (P : ZKParams) (crs : P.CRS) (td : P.Trapdoor) :
    ZKRel P → SPComp P.Proof :=
  fun xw => P.simulate crs td xw.1.1

derive_reduction zkSim

example (P : ZKParams) (crs : P.CRS) (td : P.Trapdoor) (xw : ZKRel P)
    (simulate : P.CRS → P.Trapdoor → P.Statement → SPTree P.Proof)
    (h : ∀ c t x, (simulate c t x).compile = P.simulate c t x) :
    (zkSim.tree P crs td xw simulate).compile = zkSim P crs td xw :=
  zkSim.compile_tree P crs td xw simulate h

example (P : ZKParams) (crs : P.CRS) (td : P.Trapdoor) (xw : ZKRel P)
    (simulate : P.CRS → P.Trapdoor → P.Statement → SPTree.Timed P.Proof)
    (simulateCost : P.CRS → P.Trapdoor → P.Statement → ℕ) :
    (zkSim.tree.timed P crs td xw simulate simulateCost).2.erase =
      zkSim.tree P crs td xw fun c t x => (simulate c t x).erase :=
  zkSim.tree.erase_timed P crs td xw simulate simulateCost

/-- The simulated game runs in the time of the simulator, its cost and one step. -/
theorem zkSim.timeBound (P : ZKParams) (crs : P.CRS) (td : P.Trapdoor) (xw : ZKRel P)
    (sim : P.CRS → P.Trapdoor → P.Statement → SPTree.Timed P.Proof)
    (simCost : P.CRS → P.Trapdoor → P.Statement → ℕ) {T a : ℕ}
    (hs : ∀ c t x, (sim c t x).time ≤ T) (hc : ∀ c t x, simCost c t x ≤ a) :
    SPTree.Timed.stepTime (zkSim.tree.timed P crs td xw sim simCost) ≤ T + a + 1 := by
  time_bound

/-! ## The empty finite set -/

/-- Call the adversary on the empty set of indices. -/
noncomputable def emptyRed (n : ℕ) (A : Finset (Fin n) → SPComp Bool) : SPComp Bool :=
  A ∅

derive_reduction emptyRed

example (n : ℕ) (A : Finset (Fin n) → SPTree Bool) :
    (emptyRed.tree n A).compile = emptyRed n fun s => (A s).compile :=
  emptyRed.compile_tree n A

example (n : ℕ) (A : Finset (Fin n) → SPTree.Timed Bool) (ACost : Finset (Fin n) → ℕ) :
    (emptyRed.tree.timed n A ACost).2.erase = emptyRed.tree n fun s => (A s).erase :=
  emptyRed.tree.erase_timed n A ACost

/-- The call on the empty set runs in the time of the adversary, its cost and three steps. -/
theorem emptyRed.timeBound (n : ℕ) (A : Finset (Fin n) → SPTree.Timed Bool)
    (ACost : Finset (Fin n) → ℕ) {T a : ℕ}
    (hA : ∀ s, (A s).time ≤ T) (hc : ∀ s, ACost s ≤ a) :
    SPTree.Timed.stepTime (emptyRed.tree.timed n A ACost) ≤ T + a + 3 := by
  time_bound

/-! ## Simulators at carriers in `Type` -/

/-- A fresh uniform group element, the blinding simulator at a carrier in `Type`. -/
noncomputable def blindSim {G : Type} [AddCommGroup G] [Fintype G] [Nonempty G] : SPComp G :=
  SPComp.bind (SPComp.sample G) (fun r => SPComp.pure r)

derive_reduction blindSim

/-- The blinding simulator takes one step. -/
theorem blindSim.timeBound {G : Type} [AddCommGroup G] [Fintype G] [Nonempty G] :
    SPTree.Timed.stepTime (blindSim.tree.timed (G := G)) ≤ 1 := by
  time_bound

/-- A fresh uniform vector, the FRI opening simulator at a carrier in `Type`. -/
noncomputable def friSim {F : Type} [Field F] [Fintype F] {n : ℕ} : SPComp (Fin n → F) :=
  SPComp.bind (SPComp.sample (Fin n → F)) (fun m => SPComp.pure m)

derive_reduction friSim

/-- The FRI opening simulator takes one step. -/
theorem friSim.timeBound {F : Type} [Field F] [Fintype F] {n : ℕ} :
    SPTree.Timed.stepTime (friSim.tree.timed (F := F) (n := n)) ≤ 1 := by
  time_bound

end CatCrypt.Tactics.DeriveReductionFieldTypeTest
