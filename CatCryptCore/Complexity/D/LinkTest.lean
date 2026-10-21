/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.Link

/-!
# Tests of the link between costed trees and D evaluation trees

Instances of `CTree.toTimed`, `TimeRealizer.toTimed` and `TimedSim` on small trees: a sampled bit
after one step, related to its costed form at factor `1`, with the cost bound and the meaning
that `TimedSim.cost_le` and `TimedSim.run` give, and a map of it by negation.
-/

set_option autoImplicit false

namespace CatCrypt.Complexity.D.LinkTest

open CatCrypt.Core

/-- One step, then a sampled bit. -/
def coin : CTree Bool := .tick (.sample .bool .ret)

/-- The costed tree of `coin` under the oracle of time zero has time at most its cost. -/
example : SPTree.Timed.stepTime (coin.toTimed CostedOracle.zero) ≤ coin.cost := by
  have := CTree.stepTime_toTimed_le CostedOracle.zero coin
  simpa [CostedOracle.zero] using this

/-- The costed tree of `coin` compiles to its denotation. -/
example :
    ((coin.toTimed (O := CTree.Oracle.zero) CostedOracle.zero).2.erase.compile) =
      coin.run CTree.Oracle.zero :=
  CTree.compile_erase_toTimed CostedOracle.zero coin

/-- A realizer at time `n` gives a costed adversary of time at most `n` under the oracle of
time zero. -/
example {a b : Ty} {n : ℕ} {f : Val a → SPComp (Val b)}
    (r : TimeRealizer CTree.Oracle.zero n f) (x : Val a) :
    SPTree.Timed.stepTime (r.toTimed CostedOracle.zero x) ≤ n :=
  r.stepTime_toTimed_le_of_time_zero CostedOracle.zero rfl x

/-- The costed coin: a unit step cost, then a sample over `Bool`. -/
noncomputable def coinTimed : ℕ × SPTree.Timed Bool :=
  SPTree.Timed.delay 1 (0, .sample Bool inferInstance inferInstance (fun _ => 0) .ret)

/-- `coin` is simulated by the costed coin at factor `1`, with no allowance. -/
theorem coin_sim : TimedSim (fun a v => v = a) 1 0 coinTimed coin :=
  TimedSim.delay_tick le_rfl
    (TimedSim.sample le_rfl .bool (Equiv.refl Bool) fun _ => TimedSim.ret rfl)

/-- The cost bound of the simulation. -/
example : coin.cost ≤ 0 + 1 * SPTree.Timed.stepTime coinTimed :=
  coin_sim.cost_le

/-- The meaning of the simulation: `coin` denotes the compilation of the costed coin. -/
example (O : CTree.Oracle) :
    coin.run O = SPComp.bind coinTimed.2.erase.compile fun a => SPComp.pure a :=
  coin_sim.run (fun _ => trivial) O

/-- `coin` is simulated by its costed tree at factor `1`. -/
example : TimedSim (· = ·) 1 0 coin.costTree coin := CTree.timedSim_costTree coin

/-- A map of the coin by negation at no step cost; the β-step of the D bind is paid by the
allowance `1`. -/
example : TimedSim (fun a v => v = a) 1 (0 + 1)
    (SPTree.Timed.delay coinTimed.1 (coinTimed.2.map (fun a => !a) fun _ => 0))
    (coin.bind fun v => .tick (.ret (!v))) :=
  TimedSim.map coin_sim (fun a v h => by subst h; rfl) fun _ => le_rfl

end CatCrypt.Complexity.D.LinkTest
