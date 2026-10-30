/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveSimulator
public import CatCryptCore.Category.ProtBicatReactive
public import CatCryptCore.Crypto.UCGlobalSquare

/-!
# Tests of `derive_simulator`

Costed forms, erasure theorems and time theorems of bundled simulators derived by
`derive_simulator`:

* `gSim`, the simulator over a global functionality: a costed multi-call simulator built from
  the tensor of forwarding simulators with a simulator binder `S`, which is a costed binder;
* `gSimB`, the composite of `gSim` with the router `gRouter`, whose costed form and step
  theorems the command derives, and which reuses the costed form of `gSim`;
* `idTensor`, the tensor `Simulator.tensor` of two forwarding simulators.

The time theorems are instantiated at a bound `t` on every step of the costed simulator binder.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveSimulatorTest

open CatCrypt.Crypto.UCTransparent

/-- The tensor of the forwarding simulators on `(E, O)` and `(E', O')`. -/
noncomputable def idTensor {E O E' O' : Type} (V : PubView E O) (V' : PubView E' O') :
    Simulator (E ⊕ E') (O ⊕ O') (E ⊕ E') (O ⊕ O') (V.sum V') (V.sum V') :=
  Simulator.tensor (MultiHybrid.idSim E O) (MultiHybrid.idSim E' O')
    (MultiHybrid.idSim_opaque V) (MultiHybrid.idSim_opaque V')

end CatCrypt.Tactics.DeriveSimulatorTest

derive_simulator CatCrypt.Crypto.UCTransparent.gSim
derive_simulator CatCrypt.Crypto.UCTransparent.gSimB
derive_simulator CatCrypt.Tactics.DeriveSimulatorTest.idTensor

namespace CatCrypt.Tactics.DeriveSimulatorTest

open CatCrypt.Crypto.UCTransparent

variable {σS EH OH EA OA EA' OA' EG OG : Type} {VH : PubView EH OH} {VA : PubView EA OA}
  {WA : PubView EA' OA'}

/-- The costed form of `gSim` over a costed simulator whose steps cost at most `t` takes the
time `t + 14`. -/
example (WG : PubView EG OG) (S : MultiHybrid σS EA OA EA' OA') (hS : S.Opaque VA WA)
    (ST : MultiHybrid.Timed σS EA OA EA' OA') (hT : ST.Erases S) {t : ℕ}
    (ht : ST.TimeBound t t t) :
    (gSim.timed (VH := VH) (EH := EH) (OH := OH) WG S ST).Erases (gSim WG S hS) ∧
      (gSim.timed (VH := VH) (VA := VA) (WA := WA) (EH := EH) (OH := OH) WG S ST).TimeBound
        (t + 14) :=
  ⟨gSim.erase_timed WG S hS ST hT, (gSim.timeBound_timed WG S ST ht).mono (by omega)⟩

/-- The costed form of `gSimB` over a costed simulator whose steps cost at most `t` takes the
time `t + 18`. -/
example (WG : PubView EG OG) (S : MultiHybrid σS EA OA (EA' ⊕ EG) (OA' ⊕ OG))
    (hS : S.Opaque VA (WA.sum WG)) (ST : MultiHybrid.Timed σS EA OA (EA' ⊕ EG) (OA' ⊕ OG))
    (hT : ST.Erases S) {t : ℕ} (ht : ST.TimeBound t t t) :
    (gSimB.timed (VH := VH) (EH := EH) (OH := OH) WG S ST).Erases (gSimB WG S hS) ∧
      (gSimB.timed (VH := VH) (VA := VA) (WA := WA) (EH := EH) (OH := OH) WG S ST).TimeBound
        (t + 18) :=
  ⟨gSimB.erase_timed WG S hS ST hT, (gSimB.timeBound_timed WG S ST ht).mono (by omega)⟩

/-- The costed form of the tensor of two forwarding simulators takes the time `7`. -/
example {E O E' O' : Type} (V : PubView E O) (V' : PubView E' O') :
    (idTensor.timed V V').Erases (idTensor V V') ∧ (idTensor.timed V V').TimeBound 7 :=
  ⟨idTensor.erase_timed V V', idTensor.timeBound_timed V V'⟩

end CatCrypt.Tactics.DeriveSimulatorTest
