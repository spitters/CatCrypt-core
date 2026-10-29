/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCCoupling
public import CatCryptCore.Crypto.UCSimulator
public import CatCryptCore.Crypto.UCSquare
public import CatCryptCore.Crypto.UCTransparentMulti

/-!
# Realization by a compiled transition

A source system whose step is factored into a coin distribution and a deterministic transition
`δ` (`Sys.ofCore`), and the code system with the same initial state and coins whose step runs a
partial function `code` in place of `δ` and fails where `code` returns `none` (`Sys.ofCode`).
The compiled step is a stateless transition invoked once per activation; the protocol state is
kept at the Lean level and passed to `code` as an argument.

## Main results

* `CompiledStep δ code Inv` — `code` returns `δ` on every state satisfying `Inv`, and `δ`
  preserves `Inv`.
* `realizes_zero_of_compiledStep` — under `CompiledStep` and `Inv init`, the code system
  realizes the source system at distance `0`.
* `RealizesSim.ofCompiled` — a realization of an ideal system behind a simulator by the source
  system is one by the code system, with the same simulator and bound.
* `Square.ofCompiled` — the same statement as a square whose horizontal edges are closed
  systems (the closed column of `Square.closed_iff`).
-/

@[expose] public section
set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCCoupling
open scoped ENNReal

variable {τ E O C : Type}

namespace Sys

/-- The system with initial state `init` whose step from state `t` on event `e` samples coins
`r` from `coins t e` and returns `δ t e r`. -/
noncomputable def ofCore (init : τ) (coins : τ → E → SPComp C) (δ : τ → E → C → τ × O) :
    Sys τ E O :=
  ⟨init, fun t e => SPComp.bind (coins t e) fun r => SPComp.pure (δ t e r)⟩

/-- The system with initial state `init` whose step from state `t` on event `e` samples coins
`r` from `coins t e` and returns the result of `code t e r`, failing where it is `none`. -/
noncomputable def ofCode (init : τ) (coins : τ → E → SPComp C)
    (code : τ → E → C → Option (τ × O)) : Sys τ E O :=
  ⟨init, fun t e => SPComp.bind (coins t e) fun r => (code t e r).elim SPComp.fail SPComp.pure⟩

end Sys

/-- The partial transition `code` agrees with the transition `δ` on states satisfying `Inv`,
and `δ` preserves `Inv`. -/
structure CompiledStep (δ : τ → E → C → τ × O) (code : τ → E → C → Option (τ × O))
    (Inv : τ → Prop) : Prop where
  /-- On a state satisfying `Inv`, `code` returns the transition `δ`. -/
  agree : ∀ t e r, Inv t → code t e r = some (δ t e r)
  /-- The transition `δ` preserves `Inv`. -/
  inv : ∀ t e r, Inv t → Inv (δ t e r).1

/-- **Compiled transitions realize at distance `0`.** If `code` agrees with `δ` on the states
satisfying `Inv`, `δ` preserves `Inv` and the initial state satisfies it, the code system
realizes the source system at distance `0`. -/
theorem realizes_zero_of_compiledStep {init : τ} {coins : τ → E → SPComp C}
    {δ : τ → E → C → τ × O} {code : τ → E → C → Option (τ × O)} {Inv : τ → Prop}
    (h : CompiledStep δ code Inv) (h0 : Inv init) :
    Realizes (Sys.ofCode init coins code) (Sys.ofCore init coins δ) (fun _ _ => 0) := by
  refine (realizes_zero_of_coupling (R := Sys.ofCode init coins code)
    (I := Sys.ofCore init coins δ) (rel := fun t u => t = u ∧ Inv t) ⟨⟨rfl, h0⟩, ?_⟩).1
  rintro t u e ⟨rfl, ht⟩
  have hc : (Sys.ofCode init coins code).step t e = (Sys.ofCore init coins δ).step t e := by
    simp only [Sys.ofCode, Sys.ofCore, h.agree t e _ ht, Option.elim]
  rw [hc]
  exact rHoare_bind (rHoare_refl _) fun a b => rHoare_ret fun h₁ h₂ hh => by
    grind [stepPost, eqPost, CompiledStep]

/-- **Transport behind a simulator.** Under `CompiledStep` and `Inv init`, a realization of `I`
behind the simulator `S` by the source system is a realization by the code system, with the
same simulator and bound. -/
theorem RealizesSim.ofCompiled {υ EG OG : Type} {V : PubView E O} {W : PubView EG OG}
    {init : τ} {coins : τ → E → SPComp C} {δ : τ → E → C → τ × O}
    {code : τ → E → C → Option (τ × O)} {Inv : τ → Prop} {I : Sys υ EG OG}
    {S : Simulator E O EG OG V W} {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    (h : CompiledStep δ code Inv) (h0 : Inv init)
    (hs : RealizesSim (Sys.ofCore init coins δ) I S b) :
    RealizesSim (Sys.ofCode init coins code) I S b := by
  have := Realizes.trans (realizes_zero_of_compiledStep (coins := coins) h h0) hs
  unfold RealizesSim
  simpa only [zero_add] using this

/-- **The closed column of a compiled transition.** Under `CompiledStep` and `Inv init`, a
realization of `I` behind `S` by the source system gives the square whose horizontal edges are
the closed code system and the closed `I`, with the identity on the left and every subroutine
admissible. -/
theorem Square.ofCompiled {υ EG OG : Type} {V : PubView E O} {W : PubView EG OG}
    {VU : PubView Unit Unit} {init : τ} {coins : τ → E → SPComp C} {δ : τ → E → C → τ × O}
    {code : τ → E → C → Option (τ × O)} {Inv : τ → Prop} {I : Sys υ EG OG}
    {S : Simulator E O EG OG V W} {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    (h : CompiledStep δ code Inv) (h0 : Inv init)
    (hs : RealizesSim (Sys.ofCore init coins δ) I S b) :
    Square (Open.closed (Sys.ofCode init coins code)) (Open.closed I)
      (Simulator.id Unit Unit VU) S (fun _ => True) (fun _ => b) :=
  Square.closed_iff.2 (RealizesSim.ofCompiled h h0 hs)

end CatCrypt.Crypto.UCTransparent
