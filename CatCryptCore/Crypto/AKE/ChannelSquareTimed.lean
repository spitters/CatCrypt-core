/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.ChannelSquare
public import CatCryptCore.Crypto.UCOracleGameTimed
public import CatCryptCore.Crypto.UCSimulatorTimed
import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
public import CatCryptCore.Tactics.DeriveSimulator
import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.DeriveTimeBound.Basic

/-!
# Running time of the channel adversary and the channel simulator

`derive_reduction` builds the costed form of the channel adversary `chanAdv` of
`ChannelSquare.lean`: the reduction of an environment against the channel protocol with a
given transcript, asking the AEAD calls of the protocol as oracle queries.

`derive_reduction`, `derive_time_bound` and `derive_hybrid_time` build the costed form of the
adversary-port simulator `secSimA` and the time theorems of its three steps, whose draw of the
transcript is a `sampleDist` node; `derive_simulator` builds the costed form of the bundled
simulator `secSim`, whose steps cost at most `20`.

## Main definitions

* `chanAdv.timed` — the costed channel adversary
* `secSimA.timed`, `secSim.timed` — the costed simulators

## Main results

* `chanAdv.erase_timed` — the costed channel adversary erases to `chanAdv N ad Zv pk c t`
* `secProg.timeBound_ofAdv` — an activation of the channel protocol asks at most one query
* `chanAdv.timeBound_timed` — the time of the costed channel adversary, linear in the rounds
  of the environment
* `secSimA.erase_timed`, `secSimA.timeBound_timed` — erasure and step bounds of `secSimA`
* `secSim.erase_timed`, `secSim.timeBound_timed` — erasure and the bound `20` of `secSim`

No module imports this file.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.ChannelSquare

open CatCrypt.Core

derive_reduction chanAdv

section Time

open CatCrypt.Crypto.OracleAdv.Timed

variable {W Ct Tr : Type}

/-- **Time of an activation of the channel protocol**: the oracle program `secProg N ad tr t e`
asks at most one query. -/
theorem secProg.timeBound_ofAdv (N : ℕ) (ad : ℕ → W) (tr : Tr) (t : SecSt W Ct) (e : SecEv W) :
    (ofAdv (secProg N ad tr t e)).TimeBound 1 := by
  rcases e with e | e
  · simp [secProg, ofAdv, TimeBound]
  · cases e with
    | poll =>
      simp only [secProg]
      split <;> simp [ofAdv, TimeBound]
    | deliver =>
      simp only [secProg]
      split <;> simp [ofAdv, TimeBound]
    | drop =>
      simp only [secProg]
      split <;> simp [ofAdv, TimeBound]
    | tamper v => simp [secProg, ofAdv, TimeBound]
    | idle => simp [secProg, ofAdv, TimeBound]

variable {PK : Type} {C T : Type} {ζ : Type}

/-- **Time of the channel adversary.** When the distinguisher of `Z` costs at most `cd`, its steps
at most `cn` and `co`, and the step of the protocol at most `cs`, the costed channel adversary
runs in time `3 + (1 + (rounds * (cn + cs + 1 + co + 12) + (cd + 1 + 6)))`, linear in the number of
rounds of `Z`. -/
theorem chanAdv.timeBound_timed (N : ℕ) (ad : ℕ → W) (adCost : ℕ → ℕ) (pk : PK) (c : C) (t : T)
    (Zv : UCConcrete.Env (UCTransparent.Strat ζ (SecEv W) (SecOut W (PK × C × T) Ct)) ζ)
    (distCost nextCost : ζ → ℕ) (stepCost : SecSt W Ct → SecEv W → ℕ)
    (obsCost : ζ → SecOut W (PK × C × T) Ct → ℕ) {cd cn cs co : ℕ}
    (hd : ∀ z, distCost z ≤ cd) (hn : ∀ z, nextCost z ≤ cn) (hs : ∀ t e, stepCost t e ≤ cs)
    (ho : ∀ z o, obsCost z o ≤ co) :
    StepTimeBound (chanAdv.timed N ad adCost Zv pk c t distCost nextCost stepCost obsCost)
      (3 + (1 + (Zv.input.rounds * (cn + cs + 1 + co + 12) + (cd + 1 + 6)))) := by
  unfold chanAdv.timed
  exact stepTimeBound_delay (UCTransparent.OProt.reduction.timeBound_timed
    (secProt (Ct := Ct) N ad (pk, c, t)) Zv distCost nextCost stepCost obsCost hd hn hs ho
    (s := 1) fun t e => secProg.timeBound_ofAdv N ad _ t e)

end Time

derive_reduction secSimA
derive_time_bound secSimA.start.tree
derive_time_bound secSimA.resume.tree
derive_time_bound secSimA.finish.tree
derive_hybrid_time secSimA
derive_simulator secSim

end CatCrypt.Crypto.AKE.ChannelSquare
