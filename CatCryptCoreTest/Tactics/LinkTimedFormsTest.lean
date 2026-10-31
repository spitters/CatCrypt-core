/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.LinkTimed
public import CatCryptCore.Crypto.OTExtension.IKNPSquareTimed
public import CatCryptCore.Crypto.OT.DualModeOTTimed

/-!
# Tests of `link_timed` on the costed forms that `link_timed` resolves by name

`link_timed x` links the tree `x.tree` (or `x.treeHat`) when it exists, and `x` otherwise:

* `lfTree`, an `SPTree`-valued definition with the costed form `lfTree.timed` of `derive_timed`
  and no reduction tree: allowance `1`;
* `twoRed.choose` and `twoRed.guess`, the fields of a structure-valued reduction of
  `derive_reduction`, linked through the field trees `twoRed.choose.tree` and
  `twoRed.guess.tree`: allowances `1` and `0`;
* `flipSim.start` and `flipSim.resume`, the steps of a multi-call simulator of
  `derive_reduction`, linked through the step trees, whose leaves are sums (`DSim.inl`,
  `DSim.inr`);
* `dualOT_sim`, the simulator of the dual-mode OT of
  `CatCryptCore.Crypto.OT.DualModeOTTimed`, a conditional whose branches call the adversary on
  re-paired arguments, each branch derived at its own allowance: allowance `4`.

## Main definitions

* `lfTree`, `TwoStage`, `twoRed`, `flipSim`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.LinkTimedFormsTest

open CatCrypt.Core

/-- Sample a bit and call the tree adversary on its conjunction with the negation of `b`. -/
noncomputable def lfTree (A : Bool → SPTree Bool) (b : Bool) : SPTree Bool :=
  SPTree.sample Bool inferInstance inferInstance fun x => A (!b && x)

derive_timed lfTree

reflect_d lfTree

link_timed lfTree

example := @lfTree.d_timedSim

/-- A two-stage adversary. -/
structure TwoStage where
  /-- The first stage. -/
  choose : Bool → SPComp Bool
  /-- The second stage. -/
  guess : Bool → SPComp Bool

derive_timed_structure TwoStage

/-- A structure-valued reduction: the first stage samples a bit and calls the adversary, the
second calls it on the negated input. -/
noncomputable def twoRed (A : Bool → SPComp Bool) : TwoStage where
  choose b := do
    let x ← SPComp.sample Bool
    A (b && x)
  guess b := A (!b)

derive_reduction twoRed (adv := A)

reflect_d twoRed.choose.tree

link_timed twoRed.choose

example := @twoRed.choose.tree.d_timedSim

reflect_d twoRed.guess.tree

link_timed twoRed.guess

example := @twoRed.guess.tree.d_cost_le

open CatCrypt.Crypto.UCTransparent in
/-- A multi-call simulator on Boolean events and answers whose steps return sums. -/
noncomputable def flipSim : MultiHybrid Bool Bool Bool Bool Bool where
  init := false
  fuel := 0
  start s e := SPComp.pure (s, .inl (!e))
  resume s o := SPComp.pure (!s, .inr (s && o))
  finish s o := SPComp.pure (s, o)
  start_noFail _ _ := CatCrypt.Crypto.SPComp.pure_noFail _
  resume_noFail _ _ := CatCrypt.Crypto.SPComp.pure_noFail _
  finish_noFail _ _ := CatCrypt.Crypto.SPComp.pure_noFail _

derive_reduction flipSim

reflect_d flipSim.start.tree

link_timed flipSim.start

example := @flipSim.start.tree.d_timedSim

reflect_d flipSim.resume.tree

link_timed flipSim.resume

example := @flipSim.resume.tree.d_cost_le

reflect_d CatCrypt.Crypto.OT.DualModeOT.dualOT_sim.tree

link_timed CatCrypt.Crypto.OT.DualModeOT.dualOT_sim

example := @CatCrypt.Crypto.OT.DualModeOT.dualOT_sim.tree.d_cost_le

end CatCrypt.Tactics.LinkTimedFormsTest
