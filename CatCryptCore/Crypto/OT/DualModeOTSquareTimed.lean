/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OT.DualModeOTSquare
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveSimulator
public import CatCryptCore.Tactics.DeriveTimeBound

/-!
# Running time of the simulator of the dual-mode OT square

`dualOTSquareSim` is the bundled simulator of `dualOT_square`: `simWrapSim ev` of `dualOT_sim`
at the dummy adversary. `derive_simulator` builds its costed form, its erasure theorem and its
time theorem, over a costed form of `dualOT_sim` as a binder; `derive_reduction` and
`derive_time_bound` build the costed form of `dualOT_sim` and its time theorem.

No module imports this file.

## Main definitions

* `dualOTSquareSim` — the bundled simulator of `dualOT_square`
* `dualOTSquareSim.timed`, `dualOT_sim.tree.timed` — the costed forms

## Main results

* `dualOTSquareSim.erase_timed`, `dualOTSquareSim.timeBound_timed`
* `dualOT_sim.tree.erase_timed`, `dualOT_sim.tree.timeBound_timed`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OT.DualModeOT

open CatCrypt.Core CatCrypt.Crypto.UCTransparent CatCrypt.Examples

variable (gp : GroupParam)

/-- The bundled simulator of `dualOT_square`: `simWrapSim ev` of `dualOT_sim` at the dummy
adversary. -/
noncomputable def dualOTSquareSim (crs : DualModeCRS gp)
    (ev : OTInput gp → OTInput gp → Prop) :=
  simWrapSim (out := Unit) ev (dualOT_sim gp crs _ SPComp.pure) (dualOT_sim_pure_noFail gp crs)

end CatCrypt.Crypto.OT.DualModeOT

derive_simulator CatCrypt.Crypto.OT.DualModeOT.dualOTSquareSim
derive_reduction CatCrypt.Crypto.OT.DualModeOT.dualOT_sim
derive_time_bound CatCrypt.Crypto.OT.DualModeOT.dualOT_sim.tree
