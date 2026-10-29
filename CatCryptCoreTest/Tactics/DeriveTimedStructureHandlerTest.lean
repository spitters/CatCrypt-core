/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimedStructure
public import CatCryptCore.Complexity.HandlerCost

/-!
# Tests of `derive_timed_structure` on handler-priced fields

A structure `HAdv` with a circuit field `circ : Bool → QAdv 1 1 1 q`, a package field
`pkg : ℕ → DeepPackage` and a code field `code : RawCode Bool`. The mirror `HAdv.Timed` holds
costed circuits over the gate-set parameter `circGS` with the cost companion `circCost`, and
keeps the package and the code. A concrete mirror over the gate set `unitGS` (one gate, the
identity of weight one) erases to the corresponding value of `HAdv`, and runs within
`q + 1 + q * (1 + h)` under the handler cost `h`, with the empty package and `ret true` bounded
at every handler cost.

## Main results

* `erases` — the generated erasure of the concrete mirror
* `timeBound` — the generated time bound of the concrete mirror
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CatCrypt.Tactics.DeriveTimedStructureHandlerTest

open CatCrypt.Complexity.HandlerCost CatCrypt.Quantum CatCrypt.Quantum.QROM CatCrypt.Deep

/-- A structure with one field of each handler kind. -/
structure HAdv (q : ℕ) where
  /-- A circuit for each bit. -/
  circ : Bool → QAdv 1 1 1 q
  /-- A package for each index. -/
  pkg : ℕ → DeepPackage.{0}
  /-- Package code. -/
  code : RawCode Bool

derive_timed_structure HAdv

/-- One gate, the identity, of weight one. -/
def unitGS : GateSet (1 * 1 * 1) where
  G := Unit
  den _ := 1
  weight _ := 1

variable {q : ℕ} (ρ : DensityMatrix (1 * 1 * 1))

/-- The circuit with identity unitaries, initial state `ρ` and final projector zero. -/
def circ0 : QAdv 1 1 1 q where
  U _ := 1
  init := ρ
  final := 0
  final_conjTranspose := by simp
  final_mul_self := by simp

/-- The costed circuit with one identity gate per unitary. -/
def circ0' : QAdv.Timed unitGS q where
  gates _ := [()]
  init := ρ
  final := 0

/-- The concrete value of `HAdv`. -/
def adv : HAdv q := ⟨fun _ => circ0 ρ, fun _ => DeepPackage.empty, .ret true⟩

/-- The concrete mirror, at set-up cost zero. -/
def adv' : HAdv.Timed q unitGS := ⟨fun _ => circ0' ρ, fun _ => 0, fun _ => DeepPackage.empty,
  .ret true⟩

/-- The concrete mirror erases to the concrete value. -/
theorem erases : HAdv.Timed.Erases unitGS (adv' (q := q) ρ) (adv ρ) := by
  refine ⟨fun _ => circ0 ρ, fun _ => ⟨fun _ => ?_, rfl, rfl⟩, rfl⟩
  simp [unitGS, GateSet.eval, circ0', circ0, adv']

/-- The concrete mirror runs within `q + 1 + q * (1 + hq)` under the handler cost `hq` per
oracle call, and its package and code within zero at every handler cost. -/
theorem timeBound (hp hc : ℕ → ℕ) (hq : ℕ) :
    HAdv.Timed.TimeBound unitGS (adv' (q := q) ρ) hq (q + 1 + q * (1 + hq)) hp 0 hc 0 := by
  refine ⟨fun _ => ?_, fun _ => ?_, .ret true 0⟩
  · simp [adv', circ0', QAdv.Timed.time, QAdv.Timed.gateTime, GateSet.cost, unitGS]
  · intro _ _ _ hmem
    cases hmem

end CatCrypt.Tactics.DeriveTimedStructureHandlerTest
