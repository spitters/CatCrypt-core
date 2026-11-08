/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.PRFMAC
import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Tactics.DeriveTimed.Basic
public import CatCryptCore.Tactics.StdCosts

/-!
# Time of the PRF-to-MAC reduction

The costed forms of the reduction `prfMacRed` of `CatCryptCore.Examples.PRFMAC` and of its
recursion `prfMacRedAux`, derived by `derive_timed`. `prfMacRedAux` runs the forger by
structural recursion over its oracle tree, so its costed form is a recursion over the costed
tree of the forger. Its time is proved by induction on that tree with the log generalized, since
the final test walks a log that grows with the queries, so that the leaf cost is not uniform in the
state as `OracleAdv.Timed.timeBound_fold` requires.

## Cost model

The registered costs of `CatCryptCore.Crypto.OracleAdversaryTimed`: one unit per `rand` and
per `query` node; the rules of `CatCryptCore.Tactics.DeriveTimed` for the bookkeeping (the
case analysis of a node, the call of the recursion and the comparison of the tag). The test
`m ∈ log` is priced by a walk of the log at one unit per comparison of messages
(`derive_timed.priceProps`, on by default). The log grows by one message per query and each
query costs one unit of the time of the forger.

## Main results

* `prfMacRedAux.timeBound_timed` — from a log `log`, a forger of time `T` is run in time
  `8 * T + 4 * |log| + 6`
* `prfMacRed.timeBound_timed` — a forger of time `T` gives a distinguisher of time `8 * T + 7`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Examples.PRFMAC

open CatCrypt.Crypto

derive_timed prfMacRedAux

derive_timed prfMacRed

open OracleAdv.Timed in
/-- From a log `log`, a forger of time `T` is run with its final test of the forged message
against the log, at most `8 T + 4 |log| + 6`: each query of the forger costs one unit of `T` and
adds one message to the log, which the final test walks. -/
theorem prfMacRedAux.timeBound_timed {D T : Type} [DecidableEq D] [DecidableEq T]
    {A : OracleAdv.Timed D T (D × T)} {n : ℕ} (hA : A.TimeBound n) (log : List D) :
    StepTimeBound (prfMacRedAux.timed A log) (8 * n + 4 * log.length + 6) := by
  induction A generalizing n log with
  | ret a =>
    have he := List.elem.timedCost_le a.1 log
    simp only [prfMacRedAux.timed, delay]
    split <;> simp only [StepTimeBound, OracleAdv.Timed.TimeBound, and_true, Nat.add_zero]
    · omega
    · exact ⟨by omega, by omega, fun _ => by omega⟩
  | rand p c k ih =>
    obtain ⟨h0, hk⟩ := hA
    rw [prfMacRedAux.timed]
    simp only [StepTimeBound, OracleAdv.Timed.TimeBound]
    refine ⟨by omega, by omega, fun b => ?_⟩
    have h1 := hk b
    have h2 := ih b h1.2 log
    exact ⟨by have := h2.1; have := h1.1; omega, h2.2.mono (by have := h1.1; omega)⟩
  | query d c k ih =>
    obtain ⟨h0, hk⟩ := hA
    rw [prfMacRedAux.timed]
    simp only [StepTimeBound, OracleAdv.Timed.TimeBound]
    refine ⟨by omega, by omega, fun b => ?_⟩
    have h1 := hk b
    have h2 := ih b h1.2 (d :: log)
    simp only [List.length_cons] at h2
    exact ⟨by have := h2.1; have := h1.1; omega, h2.2.mono (by have := h1.1; omega)⟩

open OracleAdv.Timed in
/-- **Time of the PRF-to-MAC reduction.** A forger of time `T` gives a PRF distinguisher of
time at most `8 T + 7`. -/
theorem prfMacRed.timeBound_timed {D T : Type} [DecidableEq D] [DecidableEq T]
    {A : OracleAdv.Timed D T (D × T)} {n : ℕ} (hA : A.TimeBound n) :
    StepTimeBound (prfMacRed.timed A) (8 * n + 7) :=
  (stepTimeBound_delay (c := 1) (prfMacRedAux.timeBound_timed hA [])).mono (by simp; omega)

end CatCrypt.Examples.PRFMAC
