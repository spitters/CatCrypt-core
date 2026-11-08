/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SignalStackPQXDH
public import CatCryptCore.Crypto.Messaging.SignalStackUCTimed
public import CatCryptCore.Crypto.AKE.PQXDHSquareTimed

/-!
# Time certificate of the PQXDH Signal stack simulator

The time certificate of the simulator `chanSim (simProt P G) pqFwd` of
`SignalStackPQXDH.lean`: the instance of `chanSim.timeBoundGraded_of` of
`SignalStackUCTimed.lean` at `pqFwd` and the graded time `simProtK.timeBoundGraded_timed` of the
costed PQXDH simulator (`PQXDHSquareTimed.lean`); the `i`-th activation costs at most
`a + 4 + tr + tp + 40 i`. No module imports this file.

## Main results

* `pqChanSim.timeBoundGraded_timed`: the graded time of the costed simulator over `F_SC`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Messaging.SignalStackPQXDH

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Messaging
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.Messaging.SignalStackUC
open CatCrypt.Crypto.AKE.PQXDHSquare
open CatCrypt.Crypto.KEM.Games (Scheme)
open CatCrypt.Crypto.PAKE.DHExtract (DHGroup)
open scoped ENNReal

section Time

variable {S W K PK SK SS C V : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS]

/-- **Graded time of the simulator of the PQXDH Signal stack.** At the costed `start` step of
the PQXDH simulator over the KEM operations `O`, with the costs of `coe`, of the exponentiation,
of `toFun`, of key generation, of encapsulation (tree and companion) and of decapsulation at most
`tc`, `te`, `tf`, `tk`, `tenc`, `tec`, `tdc`, and the costs of the reset and the phase of `pqFwd`
at most `tr`, `tp`, the `i`-th activation of the costed simulator `chanSim.timed` over `F_SC`
costs at most `a + 4 + tr + tp + 40 i` with
`a = 100 + 20 tc + 8 te + 3 tf + tk + tec + tenc + tdc`, the bound of
`simProtK.timeBoundGraded_timed` plus the cost of the wrapper. -/
theorem pqChanSim.timeBoundGraded_timed (O : KemOps PK SK SS C) (G : DHGroup S W)
    (coe : S ≃ W → S → W) (coeCost : S ≃ W → S → ℕ)
    (decaps : SK → C → Option SS) (decapsCost : SK → C → ℕ) (keygen : SPTree.Timed (PK × SK))
    (encaps : PK → SPTree.Timed (SS × C)) (encapsCost : PK → ℕ) (expCost : W → S → ℕ)
    (toFunCost : S → ℕ) {tc te tf tk tenc tec tdc : ℕ} (hc : ∀ a b, coeCost a b ≤ tc)
    (he : ∀ a b, expCost a b ≤ te) (hf : ∀ a, toFunCost a ≤ tf) (hkg : keygen.time ≤ tk)
    (henc : ∀ pk, (encaps pk).time ≤ tenc) (hec : ∀ pk, encapsCost pk ≤ tec)
    (hdc : ∀ a b, decapsCost a b ≤ tdc)
    (resetCost phaseCost : SimSt S W K PK SK SS C → ℕ) {tr tp : ℕ} (hr : ∀ s, resetCost s ≤ tr)
    (hp : ∀ s, phaseCost s ≤ tp) :
    (chanSim.timed (V := V) (simProtK (K := K) O G) pqFwd resetCost phaseCost
        (simProtK.timed O G coe coeCost decaps decapsCost keygen encaps encapsCost expCost
          toFunCost).start
        (simProtK.timed O G coe coeCost decaps decapsCost keygen encaps encapsCost expCost
          toFunCost).startCost).TimeBoundGraded
      (100 + 20 * tc + 8 * te + 3 * tf + tk + tec + tenc + tdc + 4 + tr + tp) 40 := by
  obtain ⟨h0, hst, -, -⟩ := simProtK.timeBoundGraded_timed (K := K) O G coe coeCost decaps
    decapsCost keygen encaps encapsCost expCost toFunCost hc he hf hkg henc hec hdc
  exact chanSim.timeBoundGraded_of _ _ _ _ _ _ AKE.PQXDHSquare.SimInv h0 hst
    (fun i s hs => ⟨hs.1.trans (Nat.le_succ i), hs.2.trans (Nat.le_succ i)⟩) hr hp

end Time

end CatCrypt.Crypto.Messaging.SignalStackPQXDH
