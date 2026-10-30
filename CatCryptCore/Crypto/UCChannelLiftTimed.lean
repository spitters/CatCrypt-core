/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCChannelLift
public import CatCryptCore.Crypto.UCInterleaveCost
public import CatCryptCore.Crypto.UCSimulatorTimed

/-!
# Running time of the simulator moved over a channel

The costed form of the simulator `chanSim` of `UCChannelLift.lean`, the tensor of forwarding on
the honest ports with the subroutine's simulator `S` and forwarding on the channel's adversary
port, over a costed form `ST` of `S`. Its steps cost at most those of `ST` plus `14`. No module
imports this file.

## Main results

* `chanSim.timed`, `chanSim.erase_timed`: the costed form and its erasure.
* `chanSim.timeBound_timed`: the time bound of the steps of the costed form.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

variable {σS EA OA EA' OA' : Type}

/-- The costed form of `chanSim` over a costed form `ST` of the subroutine's simulator. -/
noncomputable def chanSim.timed (EH OH EC OC ED OD : Type) (S : MultiHybrid σS EA OA EA' OA')
    (ST : MultiHybrid.Timed σS EA OA EA' OA') :
    MultiHybrid.Timed (Unit × (σS × Unit)) ((EH ⊕ EC) ⊕ (EA ⊕ ED)) ((OH ⊕ OC) ⊕ (OA ⊕ OD))
      ((EH ⊕ EC) ⊕ (EA' ⊕ ED)) ((OH ⊕ OC) ⊕ (OA' ⊕ OD)) :=
  MultiHybrid.Timed.tensor (MultiHybrid.idSim (EH ⊕ EC) (OH ⊕ OC))
    (S.tensor (MultiHybrid.idSim ED OD)) (MultiHybrid.idSim.timed (EH ⊕ EC) (OH ⊕ OC))
    (MultiHybrid.Timed.tensor S (MultiHybrid.idSim ED OD) ST (MultiHybrid.idSim.timed ED OD))

/-- **Erasure of the costed `chanSim`**: over a costed form of `S`, it erases to `chanSim`. -/
theorem chanSim.erase_timed (EH OH EC OC ED OD : Type) (S : MultiHybrid σS EA OA EA' OA')
    (ST : MultiHybrid.Timed σS EA OA EA' OA') (hT : ST.Erases S) :
    (chanSim.timed EH OH EC OC ED OD S ST).Erases (chanSim EH OH EC OC ED OD S) :=
  MultiHybrid.Timed.tensor_erases (MultiHybrid.idSim.erase_timed _ _)
    (MultiHybrid.Timed.tensor_erases hT (MultiHybrid.idSim.erase_timed _ _))

/-- **Running time of `chanSim`**: over a costed form of `S` whose steps cost at most `a`, `b`
and `c`, the steps of the costed `chanSim` cost at most `a + 14`, `b + 14` and `c + 6`. -/
theorem chanSim.timeBound_timed (EH OH EC OC ED OD : Type) (S : MultiHybrid σS EA OA EA' OA')
    (ST : MultiHybrid.Timed σS EA OA EA' OA') {a b c : ℕ} (hT : ST.TimeBound a b c) :
    (chanSim.timed EH OH EC OC ED OD S ST).TimeBound (a + 14) (b + 14) (c + 6) := by
  have h := MultiHybrid.Timed.tensor_timeBound (MultiHybrid.idSim (EH ⊕ EC) (OH ⊕ OC))
    (S.tensor (MultiHybrid.idSim ED OD)) (MultiHybrid.idSim.timeBound_timed (EH ⊕ EC) (OH ⊕ OC))
    (MultiHybrid.Timed.tensor_timeBound S (MultiHybrid.idSim ED OD) hT
      (MultiHybrid.idSim.timeBound_timed ED OD))
  simpa [chanSim.timed, Nat.add_assoc] using h

end CatCrypt.Crypto.UCTransparent
