/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.LinkTimed
public import CatCryptCore.Crypto.Commitment.PedersenUCTimed
public import CatCryptCore.Examples.ElGamalDDHTimed

/-!
# Tests of `link_timed` on reductions that project and re-pair a pair argument

`pedersen_sim` matches its argument as a pair `(s, m)`, calls curried scalar functions on the
components and calls the adversary on `(s, r)`; `reflect_d` represents the projections and the
re-pairing as data function values `v ↦ v.1`, `v ↦ v.2`, `v ↦ (v.1, v.2)`, which `derive_timed`
charges nothing for, so `link_timed` charges their applications to the allowance (`5`: one `letE`
and four applications). The ElGamal DDH `Reduction` matches its challenge as a triple and re-pairs
the ciphertext (allowance `2`); its step-cost inequality has atoms that agree up to the
representation of their implicit arguments.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Commitment.PedersenUC

reflect_d pedersen_sim.tree

link_timed pedersen_sim

example := @pedersen_sim.tree.d_timedSim

example := @pedersen_sim.tree.d_cost_le

end CatCrypt.Crypto.Commitment.PedersenUC

namespace CatCryptCore.Examples.ElGamalDDH

reflect_d Reduction.tree

link_timed Reduction

example := @Reduction.tree.d_timedSim

example := @Reduction.tree.d_cost_le

end CatCryptCore.Examples.ElGamalDDH
