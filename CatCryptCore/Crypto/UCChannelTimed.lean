/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCChannel
public import CatCryptCore.Crypto.UCSimulatorTimed
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.StdCosts

/-!
# Running time of the simulator of the capability order

The costed form of the simulator `capSim` of `UCChannel.lean`, derived by `derive_reduction`,
and the time theorems of its three steps, derived by `derive_time_bound`. The leakage `ℓ` is a
primitive of the derivation with the cost `ℓCost`. The simulator of the cell
`FChan_realizes_of_le` is the tensor of the forwarding simulator with `capSim`, whose time
follows from `MultiHybrid.tensor.timeBound_timed`. No module imports this file.

## Main results

* `capSim.timed`, `capSim.erase_timed`: the costed form and its erasure.
* `capSim.timeBound_timed`: the time bound of the steps of the costed form.
-/

@[expose] public section

set_option autoImplicit false

derive_reduction CatCrypt.Crypto.UCTransparent.capSim
derive_time_bound CatCrypt.Crypto.UCTransparent.capSim.start.tree
derive_time_bound CatCrypt.Crypto.UCTransparent.capSim.resume.tree
derive_time_bound CatCrypt.Crypto.UCTransparent.capSim.finish.tree

namespace CatCrypt.Crypto.UCTransparent

/-- **Running time of the simulator of the capability order**: if the leakage `ℓ` costs at most
`t` on every value, `start` of the costed form costs at most `4`, and `resume` and `finish` at
most `t + 9`. -/
theorem capSim.timeBound_timed {V Leak : Type} (c₁ : Choreography.ChannelCap) (ℓ : V → Leak)
    (ℓCost : V → ℕ) {t : ℕ} (ht : ∀ a, ℓCost a ≤ t) :
    (capSim.timed c₁ ℓ ℓCost).TimeBound 4 (t + 9) (t + 9) :=
  ⟨fun s e => le_of_le_of_eq (capSim.start.tree.timeBound_timed c₁ ℓ ℓCost s e ht) (by grind),
    fun s o => le_of_le_of_eq (capSim.resume.tree.timeBound_timed c₁ ℓ ℓCost s o ht)
      (by grind),
    fun s o => le_of_le_of_eq (capSim.finish.tree.timeBound_timed c₁ ℓ ℓCost s o ht)
      (by grind)⟩

end CatCrypt.Crypto.UCTransparent
