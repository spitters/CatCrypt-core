/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveSimulator
public import CatCryptCore.Crypto.UCSimulatorTimed
public import CatCryptCore.Category.ProtBicatReactive
public import CatCryptCore.Crypto.UCGlobalSquare

/-!
# Tests of `derive_simulator`: changes of views and the constructions of the command

Costed forms, erasure theorems and time theorems of bundled simulators under `Simulator.mono`:

* `idMono`, a forwarding simulator at other views;
* `compMono`, a composite at other views, with a change of views on a part.

The command also derives the simulators of `DeriveSimulatorTest.lean` (`gSim`, `gSimB`,
`idTensor`), with the bounds stated there.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveSimulatorMonoTest

open CatCrypt.Crypto.UCTransparent

variable {E O : Type}

/-- The forwarding simulator at other views. -/
noncomputable def idMono (V V' W' : PubView E O) (hVev : ∀ e e', V'.ev e e' → V.ev e e')
    (hVout : ∀ o o', V.out o o' → V'.out o o') (hWev : ∀ g g', V.ev g g' → W'.ev g g')
    (hWout : ∀ o o', W'.out o o' → V.out o o') : Simulator E O E O V' W' :=
  (Simulator.ofMultiHybrid (MultiHybrid.idSim E O) (MultiHybrid.idSim_opaque V)).mono
    hVev hVout hWev hWout

derive_simulator idMono

/-- The costed form of `idMono` erases to it and takes the time `0`. -/
example (V V' W' : PubView E O) (h₁ : ∀ e e', V'.ev e e' → V.ev e e')
    (h₂ : ∀ o o', V.out o o' → V'.out o o') (h₃ : ∀ g g', V.ev g g' → W'.ev g g')
    (h₄ : ∀ o o', W'.out o o' → V.out o o') :
    (idMono.timed V V' W').Erases (idMono V V' W' h₁ h₂ h₃ h₄) ∧
      (idMono.timed V V' W').TimeBound 0 :=
  ⟨idMono.erase_timed V V' W' h₁ h₂ h₃ h₄, idMono.timeBound_timed V V' W'⟩

/-- A composite of forwarding simulators at other views, with a change of views on a part. -/
noncomputable def compMono (V V' : PubView E O) (hVev : ∀ e e', V'.ev e e' → V.ev e e')
    (hVout : ∀ o o', V.out o o' → V'.out o o') : Simulator E O E O V' V :=
  ((Simulator.ofMultiHybrid (MultiHybrid.idSim E O) (MultiHybrid.idSim_opaque V)).comp
    ((Simulator.ofMultiHybrid (MultiHybrid.idSim E O) (MultiHybrid.idSim_opaque V)).mono
      (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h => h))).mono
    hVev hVout (fun _ _ h => h) (fun _ _ h => h)

derive_simulator compMono

/-- The costed form of `compMono` erases to it and takes the time `0`. -/
example (V V' : PubView E O) (h₁ : ∀ e e', V'.ev e e' → V.ev e e')
    (h₂ : ∀ o o', V.out o o' → V'.out o o') :
    (compMono.timed V V').Erases (compMono V V' h₁ h₂) ∧ (compMono.timed V V').TimeBound 0 :=
  ⟨compMono.erase_timed V V' h₁ h₂, compMono.timeBound_timed V V'⟩

end CatCrypt.Tactics.DeriveSimulatorMonoTest

derive_simulator CatCrypt.Crypto.UCTransparent.gSim
derive_simulator CatCrypt.Crypto.UCTransparent.gSimB

namespace CatCrypt.Tactics.DeriveSimulatorMonoTest

open CatCrypt.Crypto.UCTransparent

variable {σS EH OH EA OA EA' OA' EG OG : Type} {VH : PubView EH OH} {VA : PubView EA OA}
  {WA : PubView EA' OA'}

/-- The tensor of the forwarding simulators on `(E, O)` and `(E', O')`. -/
noncomputable def idTensor {E O E' O' : Type} (V : PubView E O) (V' : PubView E' O') :
    Simulator (E ⊕ E') (O ⊕ O') (E ⊕ E') (O ⊕ O') (V.sum V') (V.sum V') :=
  Simulator.tensor (MultiHybrid.idSim E O) (MultiHybrid.idSim E' O')
    (MultiHybrid.idSim_opaque V) (MultiHybrid.idSim_opaque V')

derive_simulator idTensor

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

end CatCrypt.Tactics.DeriveSimulatorMonoTest
