/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Commitment.PedersenUCSquare
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveSimulator
public import CatCryptCore.Tactics.DeriveTimeBound

/-!
# Running time of the simulator of the Pedersen commit-phase square

`pedersenSquareSim` is the bundled simulator of `pedersen_commit_phase_square`: `simWrapSim ev`
of `pedersen_commit_sim` at the dummy adversary. `derive_simulator` builds its costed form, its
erasure theorem and its time theorem, over a costed form of `pedersen_commit_sim` as a binder;
`derive_reduction` and `derive_time_bound` build the costed form of `pedersen_commit_sim` and
its time theorem.

No module imports this file.

## Main definitions

* `pedersenSquareSim` — the bundled simulator of `pedersen_commit_phase_square`
* `pedersenSquareSim.timed`, `pedersen_commit_sim.tree.timed` — the costed forms

## Main results

* `pedersenSquareSim.erase_timed`, `pedersenSquareSim.timeBound_timed`
* `pedersen_commit_sim.tree.erase_timed`, `pedersen_commit_sim.tree.timeBound_timed`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Commitment.PedersenUC

open CatCrypt.Core CatCrypt.Crypto.UCTransparent CatCrypt.Examples

variable (gp : GroupParam)

/-- The bundled simulator of `pedersen_commit_phase_square`: `simWrapSim ev` of
`pedersen_commit_sim` at the dummy adversary. -/
noncomputable def pedersenSquareSim (ev : gp.Scalar → gp.Scalar → Prop) :=
  simWrapSim (out := Unit) ev (pedersen_commit_sim gp _ SPComp.pure)
    (pedersen_commit_sim_pure_noFail gp)

end CatCrypt.Crypto.Commitment.PedersenUC

derive_simulator CatCrypt.Crypto.Commitment.PedersenUC.pedersenSquareSim
derive_reduction CatCrypt.Crypto.Commitment.PedersenUC.pedersen_commit_sim
derive_time_bound CatCrypt.Crypto.Commitment.PedersenUC.pedersen_commit_sim.tree
