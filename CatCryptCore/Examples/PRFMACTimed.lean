/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.PRFMAC
public import CatCryptCore.Tactics.DeriveTimed

/-!
# Time of the PRF-to-MAC reduction

The costed forms of the reduction `prfMacRed` of `CatCryptCore.Examples.PRFMAC` and of its
recursion `prfMacRedAux`, derived by `derive_timed`. `prfMacRedAux` runs the forger by
structural recursion over its oracle tree, so its costed form is a recursion over the costed
tree of the forger, and its time follows from `OracleAdv.Timed.timeBound_fold`.

## Cost model

The registered costs of `CatCryptCore.Crypto.OracleAdversaryTimed`: one unit per `rand` and
per `query` node; the rules of `CatCryptCore.Tactics.DeriveTimed` for the bookkeeping (the
case analysis of a node, the call of the recursion, the test `m ∈ log` and the comparison of
the tag).

## Main results

* `prfMacRedAux.timeBound_timed` — from any log, a forger of time `T` is run in time
  `4 * T + 5`
* `prfMacRed.timeBound_timed` — a forger of time `T` gives a distinguisher of time
  `4 * T + 6`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Examples.PRFMAC

open CatCrypt.Crypto

derive_timed prfMacRedAux

derive_timed prfMacRed

/-- From any log, a forger of time `T` is run in time at most `4 * T + 5`: each node of the
forger is handled at three units of overhead per unit of its time, and the final check queries
the forgery once. -/
theorem prfMacRedAux.timeBound_timed {D T : Type} [DecidableEq D] [DecidableEq T]
    {A : OracleAdv.Timed D T (D × T)} {n : ℕ} (hA : A.TimeBound n) (log : List D) :
    OracleAdv.Timed.StepTimeBound (prfMacRedAux.timed A log) (4 * n + 5) := by
  refine OracleAdv.Timed.timeBound_fold (h := 3) (r := 5) (fun A s => prfMacRedAux.timed A s)
    ?_ ?_ ?_ hA log
  · intro a s
    simp only [prfMacRedAux.timed, OracleAdv.Timed.delay]
    split <;> simp_all [OracleAdv.Timed.StepTimeBound, OracleAdv.Timed.TimeBound]
  · intro γ p c k s M hM0 hM hk
    rw [prfMacRedAux.timed]
    simp only [OracleAdv.Timed.StepTimeBound, OracleAdv.Timed.TimeBound]
    refine ⟨by omega, by omega, fun b => ?_⟩
    have h1 := hM b
    have h2 := hk b s
    exact ⟨by have := h2.1; omega, h2.2.mono (by omega)⟩
  · intro d c k s M hM0 hM hk
    rw [prfMacRedAux.timed]
    simp only [OracleAdv.Timed.StepTimeBound, OracleAdv.Timed.TimeBound]
    refine ⟨by omega, by omega, fun b => ?_⟩
    have h1 := hM b
    have h2 := hk b (d :: s)
    exact ⟨by have := h2.1; omega, h2.2.mono (by omega)⟩

/-- **Time of the PRF-to-MAC reduction.** A forger of time `T` gives a PRF distinguisher of
time at most `4 * T + 6`. -/
theorem prfMacRed.timeBound_timed {D T : Type} [DecidableEq D] [DecidableEq T]
    {A : OracleAdv.Timed D T (D × T)} {n : ℕ} (hA : A.TimeBound n) :
    OracleAdv.Timed.StepTimeBound (prfMacRed.timed A) (4 * n + 6) :=
  (OracleAdv.Timed.stepTimeBound_delay (c := 1) (prfMacRedAux.timeBound_timed hA [])).mono
    (by omega)

end CatCrypt.Examples.PRFMAC
