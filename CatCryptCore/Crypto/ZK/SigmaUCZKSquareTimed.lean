/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.ZK.SigmaUCZKSquare
public import CatCryptCore.Category.ProtBicatReactiveTimed
public import CatCryptCore.Crypto.ZK.SigmaUCZKTimed
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveSimulator
public import CatCryptCore.Tactics.DeriveTimeBound

/-!
# Running time of the simulator of the Σ-protocol UC-ZK square

`sigmaSquareSim` is the bundled simulator of `sigma_uc_zk_square`: `simWrapSim ev` of
`sigma_uc_sim` at the dummy adversary. `derive_simulator` builds its costed form, its erasure
theorem and its time theorem, over a costed form of `sigma_uc_sim` as a binder; the costed
form of `sigma_uc_sim` and its time theorem come from `SigmaUCZKTimed`.

No module imports this file.

## Main definitions

* `sigmaSquareSim` — the bundled simulator of `sigma_uc_zk_square`
* `sigmaSquareSim.timed`, `sigma_uc_sim.tree.timed` — the costed forms

## Main results

* `sigmaSquareSim.erase_timed`, `sigmaSquareSim.timeBound_timed`
* `sigma_uc_sim.tree.erase_timed`, `sigma_uc_sim.tree.timeBound_timed`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.ZK.SigmaUCZK

open CatCrypt.Core CatCrypt.Crypto.UCTransparent

variable (sp : CatCrypt.Examples.Sigma.SigmaProtocol)

/-- The bundled simulator of `sigma_uc_zk_square`: `simWrapSim ev` of `sigma_uc_sim` at the
dummy adversary. -/
noncomputable def sigmaSquareSim (hsim : ∀ x e, SPComp.NoFail (sp.simulate x e))
    (ev : sp.Statement × sp.Witness → sp.Statement × sp.Witness → Prop) :=
  simWrapSim (out := Unit) ev (sigma_uc_sim sp _ SPComp.pure) (sigma_uc_sim_pure_noFail sp hsim)

end CatCrypt.Crypto.ZK.SigmaUCZK

derive_simulator CatCrypt.Crypto.ZK.SigmaUCZK.sigmaSquareSim
