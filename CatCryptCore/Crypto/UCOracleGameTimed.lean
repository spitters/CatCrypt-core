/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCOracleGame
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.AutoTime

/-!
# Running time of the environment reduction of an oracle protocol

`derive_reduction` builds the costed forms of `OProt.reduce`, the environment `Z` with its
distinguisher run against the program of an oracle protocol `P` as an oracle adversary, and of
`OProt.reduction`, `reduce` from the initial states of `Z` and `P`.

No module imports this file.

## Main definitions

* `OProt.reduce.timed`, `OProt.reduction.timed` — the costed reductions

## Main results

* `OProt.reduce.erase_timed`, `OProt.reduction.erase_timed` — their erasure theorems
* `OProt.reduce.timeBound_timed`, `OProt.reduction.timeBound_timed` — their time bounds, linear
  in the number of activations, over bounds on the costs of the steps of the environment, the
  distinguisher, the protocol's steps and the time of its oracle programs
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent.OProt

open CatCrypt.Core OracleAdv.Timed

derive_reduction reduce
derive_reduction reduction
/-- **Time of `reduce`.** When the distinguisher costs at most `cd`, the steps of the environment
at most `cn` and `co`, the protocol's step at most `cs` and its oracle program runs in time `s`,
`n` activations of the costed `reduce` take `n * (cn + cs + s + co + 12) + (cd + 6)`. -/
theorem reduce.timeBound_timed {τ E O Q A ζ : Type} (P : OProt τ E O Q A) (Z : Strat ζ E O)
    (dist : ζ → SPComp Bool) (distCost : ζ → ℕ) (nextCost : ζ → ℕ) (stepCost : τ → E → ℕ)
    (obsCost : ζ → O → ℕ) {cd cn cs co s : ℕ} (hd : ∀ z, distCost z ≤ cd)
    (hn : ∀ z, nextCost z ≤ cn) (hs : ∀ t e, stepCost t e ≤ cs) (ho : ∀ z o, obsCost z o ≤ co)
    (hP : ∀ t e, (ofAdv (P.step t e)).TimeBound s) (n : ℕ) :
    ∀ z t h, StepTimeBound (reduce.timed P Z dist distCost n z t h nextCost stepCost obsCost)
      (n * (cn + cs + s + co + 12) + (cd + 6)) := by
  induction n with
  | zero =>
    intro z t h
    simp only [reduce.timed]
    time_bound
  | succ n ih =>
    intro z t h
    rw [Nat.succ_mul]
    generalize n * (cn + cs + s + co + 12) = m at ih ⊢
    simp only [reduce.timed]
    have hz := hn z
    refine (stepTimeBound_delay (c := 1) (n := m + (cn + cs + s + co + 12) + (cd + 6) - 1)
      ⟨by omega, (timeBound_rand_iff _ _ _ _).2 ⟨by omega, fun o => ?_⟩⟩).mono (by omega)
    rcases o with _ | ⟨⟨z₁, e⟩, h₁⟩
    · exact ⟨by grind, trivial⟩
    have he := hs t e
    refine (stepTimeBound_delay (c := 1) (stepTimeBound_delay (c := 1 + stepCost t e)
      (timeBound_bind (hP t e) (n := co + (m + (cd + 6)) + 5) fun p => ?_))).mono (by omega)
    have hp := ho z₁ p.2
    refine ⟨by omega, (timeBound_rand_iff _ _ _ _).2 ⟨by omega, fun o' => ?_⟩⟩
    rcases o' with _ | ⟨z₂, h₂⟩
    · exact ⟨by grind, trivial⟩
    exact (stepTimeBound_delay (c := 1) (stepTimeBound_delay (c := 1) (ih z₂ p.1 h₂))).mono
      (by omega)

/-- **Time of the environment reduction.** Under the cost bounds of `reduce.timeBound_timed`,
the costed reduction of `Z` against `P` takes
`1 + (Z.input.rounds * (cn + cs + s + co + 12) + (cd + 1 + 6))`. -/
theorem reduction.timeBound_timed {τ E O Q A ζ : Type} (P : OProt τ E O Q A)
    (Z : UCConcrete.Env (Strat ζ E O) ζ) (distCost : ζ → ℕ) (nextCost : ζ → ℕ)
    (stepCost : τ → E → ℕ) (obsCost : ζ → O → ℕ) {cd cn cs co s : ℕ} (hd : ∀ z, distCost z ≤ cd)
    (hn : ∀ z, nextCost z ≤ cn) (hs : ∀ t e, stepCost t e ≤ cs) (ho : ∀ z o, obsCost z o ≤ co)
    (hP : ∀ t e, (ofAdv (P.step t e)).TimeBound s) :
    StepTimeBound (reduction.timed P Z distCost nextCost stepCost obsCost)
      (1 + (Z.input.rounds * (cn + cs + s + co + 12) + (cd + 1 + 6))) :=
  stepTimeBound_delay (reduce.timeBound_timed P Z.input Z.dist (fun a => 1 + distCost a)
    nextCost stepCost obsCost (cd := cd + 1) (fun z => by grind) hn hs ho hP _ _ _ _)

end CatCrypt.Crypto.UCTransparent.OProt
