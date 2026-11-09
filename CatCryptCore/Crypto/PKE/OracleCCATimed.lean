/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PKE.OracleCCA
import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic

/-!
# Time of the oracle adversary of a two-stage IND-CCA adversary

The costed form of `indccaOracleReduction` by `derive_reduction`, its erasure theorem, and its
time bound. Only time companion files import this file.

## Cost model

The rules of `CatCryptCore.Tactics.DeriveTimed`: one unit per `rand` and `query` node and per
bookkeeping step; the derived relabelling `OracleAdv.mapQueryAnswer.timed` charges a constant per
node of the stage and per answer read as a decryption result.

## Main results

* `indccaOracleReduction.timed`, `indccaOracleReduction.erase_timed` — the costed reduction and
  its erasure.
* `decStage.timeBound_timed` — a stage of time at most `T` with at most `q` queries takes time
  at most `2 + 4 * T + 5 * q` through `decStage`.
* `indccaOracleReduction.timeBound_timed` — for stages of times `T₁`, `T₂`, call costs `a₁`,
  `a₂` and at most `q₁`, `q₂` queries, the oracle adversary takes time at most
  `13 + a₁ + a₂ + 4 * T₁ + 4 * T₂ + 5 * q₁ + 5 * q₂`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.PKE.Games

open CatCrypt.Crypto

derive_reduction indccaOracleReduction

variable {PK M C : Type}

/-- **Time of a stage through `decStage`.** A costed stage of time at most `T` with at most `q`
queries takes time at most `2 + 4 * T + 5 * q` through `decStage`. -/
theorem decStage.timeBound_timed {α : Type} {W : OracleAdv.Timed C (Option M) α} {T q : ℕ}
    (hW : W.TimeBound T) (hq : W.erase.IsQueryBound q) :
    OracleAdv.Timed.StepTimeBound (decStage.timed (PK := PK) W) (2 + 4 * T + 5 * q) := by
  have h := OracleAdv.mapQueryAnswer.timeBound_timed (INDCCAQuery.dec (M := M))
    (gCost := fun _ => 0) (INDCCAAns.decOut (PK := PK) (C := C)) (hCost := fun _ => 2) (a := 0)
    (b := 2) (fun _ => le_rfl) (fun _ => le_rfl) hW hq
  exact (OracleAdv.Timed.stepTimeBound_delay (c := 1) h).mono (by omega)

/-- **Time of the challenge step.** For a costed second stage of time at most `T₂` with at most
`q₂` queries and call cost at most `a₂`, the challenge step takes time at most
`6 + a₂ + 4 * T₂ + 5 * q₂`. -/
theorem indccaOracleChal.timeBound_timed {St : Type}
    (guess : St → C → OracleAdv.Timed C (Option M) Bool) (guessCost : St → C → ℕ)
    {T₂ a₂ q₂ : ℕ} (hg : ∀ st c, (guess st c).TimeBound T₂)
    (hgc : ∀ st c, guessCost st c ≤ a₂) (hq₂ : ∀ st c, (guess st c).erase.IsQueryBound q₂)
    (x : M × M × St) :
    OracleAdv.Timed.StepTimeBound (indccaOracleChal.timed (PK := PK) guess guessCost x)
      (6 + a₂ + 4 * T₂ + 5 * q₂) := by
  unfold indccaOracleChal.timed
  rw [OracleAdv.Timed.stepTimeBound_zero]
  refine (OracleAdv.Timed.timeBound_query_iff _ _ _ _).2 ⟨by omega, fun a => ?_⟩
  cases a
  case chal c =>
    have h := decStage.timeBound_timed (PK := PK) (hg x.2.2 c) (hq₂ x.2.2 c)
    have h2 := OracleAdv.Timed.stepTimeBound_delay (c := 1)
      (OracleAdv.Timed.stepTimeBound_delay (c := 2 + guessCost x.2.2 c) h)
    exact h2.mono (by have := hgc x.2.2 c; omega)
  all_goals exact ⟨by dsimp only; omega, trivial⟩

/-- **Time of the oracle adversary of a two-stage adversary.** For costed stages `choose`,
`guess` of times at most `T₁`, `T₂`, call costs at most `a₁`, `a₂` and at most `q₁`, `q₂`
queries, the costed `indccaOracleReduction` takes time at most
`13 + a₁ + a₂ + 4 * T₁ + 4 * T₂ + 5 * q₁ + 5 * q₂`: linear in the time of the adversary. -/
theorem indccaOracleReduction.timeBound_timed {St : Type}
    (choose : PK → OracleAdv.Timed C (Option M) (M × M × St)) (chooseCost : PK → ℕ)
    (guess : St → C → OracleAdv.Timed C (Option M) Bool) (guessCost : St → C → ℕ)
    {T₁ T₂ a₁ a₂ q₁ q₂ : ℕ} (hc : ∀ pk, (choose pk).TimeBound T₁)
    (hg : ∀ st c, (guess st c).TimeBound T₂) (hcc : ∀ pk, chooseCost pk ≤ a₁)
    (hgc : ∀ st c, guessCost st c ≤ a₂) (hq₁ : ∀ pk, (choose pk).erase.IsQueryBound q₁)
    (hq₂ : ∀ st c, (guess st c).erase.IsQueryBound q₂) :
    OracleAdv.Timed.StepTimeBound (indccaOracleReduction.timed choose chooseCost guess guessCost)
      (13 + a₁ + a₂ + 4 * T₁ + 4 * T₂ + 5 * q₁ + 5 * q₂) := by
  unfold indccaOracleReduction.timed
  rw [OracleAdv.Timed.stepTimeBound_zero]
  refine (OracleAdv.Timed.timeBound_query_iff _ _ _ _).2 ⟨by omega, fun a => ?_⟩
  cases a
  case pk pk =>
    have hd := decStage.timeBound_timed (PK := PK) (hc pk) (hq₁ pk)
    have hb := OracleAdv.Timed.timeBound_bind
      (f := fun x => OracleAdv.Timed.delay 1 (indccaOracleChal.timed guess guessCost x)) hd.2
      fun x => OracleAdv.Timed.stepTimeBound_delay (c := 1)
        (indccaOracleChal.timeBound_timed guess guessCost hg hgc hq₂ x)
    have h3 := OracleAdv.Timed.stepTimeBound_delay (c := 1)
      (OracleAdv.Timed.stepTimeBound_delay
        (c := 2 + chooseCost pk + (decStage.timed (PK := PK) (choose pk)).1) hb)
    exact h3.mono (by have := hd.1; have := hcc pk; omega)
  all_goals exact ⟨by dsimp only; omega, trivial⟩

end CatCrypt.Crypto.PKE.Games
