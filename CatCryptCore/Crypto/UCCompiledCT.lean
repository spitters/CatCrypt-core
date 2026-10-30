/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCCompiled
public import CatCryptCore.Crypto.UCGlobal

/-!
# Realization by a compiled transition with leakage

A system whose outputs are augmented by a leakage `ℓ e o`, a function of the event `e` of the
activation and of its output `o` (`Sys.augmentOut`), is the system on ports relabelled by
`Sys.relabel`, with the event as its tag. Realization lifts to augmented systems at the reduced
environment of the relabelling (`Realizes.augmentOut`). A simulator augmented by `ℓ`
(`Simulator.augmentOut`) is opaque for the view of `V` that also relates equal leakages when
`ℓ` sends events and outputs related by `V` to equal leakages (`RespectsView`).

A compiled transition with leakage is a `CompiledStep` of the transition whose outputs carry
the leakage (`augmentCore δ ℓ`): on every state satisfying the invariant, the code returns the
new state, the output and the leakage `ℓ e o`. Its code system realizes the augmented source
system at distance `0`, and a realization of an ideal system behind a simulator by the source
system gives one by the code system behind the augmented simulator.

## Main results

* `Realizes.augmentOut` — realization lifts to systems with outputs augmented by `ℓ`.
* `Sys.Opaque.augmentOut`, `Simulator.augmentOut` — augmentation by a leakage that respects
  the view preserves opacity.
* `RealizesSim.augmentOut` — realization behind a simulator lifts to augmented outputs.
* `realizes_zero_ofCore_augmentCore` — the system of the augmented transition realizes the
  augmented system at distance `0`.
* `RealizesSim.ofCompiledL`, `Square.ofCompiledL` — transport of a realization behind a
  simulator to the code system of a compiled transition with leakage.
-/

@[expose] public section
set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete
open scoped ENNReal

variable {τ υ E O C L EG OG : Type}

namespace Sys

/-- The system `X` with each output `o` of an activation on the event `e` augmented by the
leakage `ℓ e o`: `X` on ports relabelled with the event as the tag. -/
noncomputable def augmentOut (X : Sys τ E O) (ℓ : E → O → L) : Sys τ E (O × L) :=
  X.relabel (fun e => (e, e)) fun e o => (o, ℓ e o)

end Sys

namespace PubView

/-- The view `V` on outputs augmented by a leakage: the outputs are related by `V.out` and the
leakages are equal. -/
def augmentOut (V : PubView E O) (L : Type) : PubView E (O × L) where
  ev := V.ev
  out p p' := V.out p.1 p'.1 ∧ p.2 = p'.2

end PubView

/-- The leakage `ℓ` respects the view `V`: events related by `V.ev` and outputs related by
`V.out` have equal leakages. -/
def RespectsView (V : PubView E O) (ℓ : E → O → L) : Prop :=
  ∀ e e' o o', V.ev e e' → V.out o o' → ℓ e o = ℓ e' o'

/-- The open system of the augmentation by `ℓ`, from the initial tag `e₀`. -/
noncomputable def Open.augmentOut (e₀ : E) (ℓ : E → O → L) : Open E (O × L) E O :=
  Open.relabel e₀ (fun e => (e, e)) fun e o => (o, ℓ e o)

/-- **Realization lifts to augmented outputs.** If `R` realizes `I` with bound `b`, then `R`
with outputs augmented by `ℓ` realizes `I` with outputs augmented by `ℓ`, with the bound `b`
at the reduced environment, which remembers the pending event from the initial event `e₀`. -/
theorem Realizes.augmentOut (e₀ : E) (ℓ : E → O → L) {R : Sys τ E O} {I : Sys υ E O}
    {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞} (h : Realizes R I b) :
    Realizes (R.augmentOut ℓ) (I.augmentOut ℓ)
      (fun ζ Z => b (ζ × E) ((Open.augmentOut e₀ ℓ).reduceEnv Z)) :=
  Open.realizes_relabel e₀ _ _ h

/-- **Augmentation preserves opacity.** If `X` is opaque for `V` and the leakage `ℓ` respects
`V`, then `X` with outputs augmented by `ℓ` is opaque for the augmented view. -/
theorem Sys.Opaque.augmentOut {X : Sys τ E O} {V : PubView E O} {ℓ : E → O → L}
    (hℓ : RespectsView V ℓ) (h : X.Opaque V) : (X.augmentOut ℓ).Opaque (V.augmentOut L) := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T, hT.init, fun t t' e e' ht he => ?_⟩
  change rHoare eqPre (SPComp.bind (X.step t e) fun q => SPComp.pure (q.1, (q.2, ℓ e q.2)))
    (SPComp.bind (X.step t' e') fun q => SPComp.pure (q.1, (q.2, ℓ e' q.2))) _
  exact rHoare_bind (hT.step t t' e e' ht he) fun p p' => rHoare_ret fun h₁ h₂ hp =>
    ⟨hp.1, hp.2.1, hp.2.2, hℓ _ _ _ _ he hp.2.2⟩

/-- **The augmented simulator.** The simulator `S` with outer outputs augmented by a leakage
`ℓ` that respects its outer view; it is opaque for the augmented view. -/
noncomputable def Simulator.augmentOut {V : PubView E O} {W : PubView EG OG}
    (S : Simulator E O EG OG V W) (ℓ : E → O → L) (hℓ : RespectsView V ℓ) :
    Simulator E (O × L) EG OG (V.augmentOut L) W where
  St := S.St
  withSub X := (S.withSub X).augmentOut ℓ
  isOpaque X h := (S.isOpaque X h).augmentOut hℓ

/-- **Realization behind a simulator lifts to augmented outputs.** If `R` realizes `I` behind
`S` with bound `b`, then `R` with outputs augmented by `ℓ` realizes `I` behind the augmented
simulator, with the bound `b` at the reduced environment. -/
theorem RealizesSim.augmentOut {V : PubView E O} {W : PubView EG OG} (e₀ : E)
    {ℓ : E → O → L} (hℓ : RespectsView V ℓ) {R : Sys τ E O} {I : Sys υ EG OG}
    {S : Simulator E O EG OG V W} {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    (h : RealizesSim R I S b) :
    RealizesSim (R.augmentOut ℓ) I (S.augmentOut ℓ hℓ)
      (fun ζ Z => b (ζ × E) ((Open.augmentOut e₀ ℓ).reduceEnv Z)) :=
  Realizes.augmentOut e₀ ℓ h

/-- The transition `δ` with its outputs augmented by the leakage `ℓ`: from state `t` on event
`e` with coins `r`, the new state of `δ t e r`, its output `o` and the leakage `ℓ e o`. -/
def augmentCore (δ : τ → E → C → τ × O) (ℓ : E → O → L) : τ → E → C → τ × (O × L) :=
  fun t e r => ((δ t e r).1, ((δ t e r).2, ℓ e (δ t e r).2))

/-- **The augmented transition.** The system of the transition `δ` augmented by `ℓ` realizes
the system of `δ` with outputs augmented by `ℓ` at distance `0`. -/
theorem realizes_zero_ofCore_augmentCore (init : τ) (coins : τ → E → SPComp C)
    (δ : τ → E → C → τ × O) (ℓ : E → O → L) :
    Realizes (Sys.ofCore init coins (augmentCore δ ℓ)) ((Sys.ofCore init coins δ).augmentOut ℓ)
      (fun _ _ => 0) :=
  (realizes_zero_of_step_eq (Sys.ofCore init coins (augmentCore δ ℓ))
    ((Sys.ofCore init coins δ).augmentOut ℓ) rfl fun t e => by
    simp only [Sys.ofCore, Sys.augmentOut, Sys.relabel, augmentCore, SPComp.map,
      SPComp.bind_assoc, SPComp.pure_bind]).1

/-- **Transport behind a simulator, with leakage.** If `code` is a compiled step of `δ`
augmented by the leakage `ℓ` under `Inv`, `Inv init` holds and `ℓ` respects the outer view,
then a realization of `I` behind `S` by the source system gives a realization by the code
system behind the simulator `S` augmented by `ℓ`, with the bound at the reduced environment
of the augmentation. -/
theorem RealizesSim.ofCompiledL {V : PubView E O} {W : PubView EG OG} {init : τ}
    {coins : τ → E → SPComp C} {δ : τ → E → C → τ × O} {ℓ : E → O → L}
    {code : τ → E → C → Option (τ × (O × L))} {Inv : τ → Prop} {I : Sys υ EG OG}
    {S : Simulator E O EG OG V W} {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞} (e₀ : E)
    (hℓ : RespectsView V ℓ) (h : CompiledStep (augmentCore δ ℓ) code Inv) (h0 : Inv init)
    (hs : RealizesSim (Sys.ofCore init coins δ) I S b) :
    RealizesSim (Sys.ofCode init coins code) I (S.augmentOut ℓ hℓ)
      (fun ζ Z => b (ζ × E) ((Open.augmentOut e₀ ℓ).reduceEnv Z)) := by
  have := Realizes.trans (realizes_zero_of_compiledStep (coins := coins) h h0)
    (Realizes.trans (realizes_zero_ofCore_augmentCore init coins δ ℓ)
      (RealizesSim.augmentOut e₀ hℓ hs))
  unfold RealizesSim
  simpa only [zero_add] using this

/-- **The closed column of a compiled transition with leakage.** The statement of
`RealizesSim.ofCompiledL` as a square whose horizontal edges are the closed code system and
the closed `I`, with the identity on the left and every subroutine admissible. -/
theorem Square.ofCompiledL {V : PubView E O} {W : PubView EG OG}
    {VU : PubView Unit Unit} {init : τ} {coins : τ → E → SPComp C} {δ : τ → E → C → τ × O}
    {ℓ : E → O → L} {code : τ → E → C → Option (τ × (O × L))} {Inv : τ → Prop}
    {I : Sys υ EG OG} {S : Simulator E O EG OG V W}
    {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞} (e₀ : E)
    (hℓ : RespectsView V ℓ) (h : CompiledStep (augmentCore δ ℓ) code Inv) (h0 : Inv init)
    (hs : RealizesSim (Sys.ofCore init coins δ) I S b) :
    Square (Open.closed (Sys.ofCode init coins code)) (Open.closed I)
      (Simulator.id Unit Unit VU) (S.augmentOut ℓ hℓ) (fun _ => True)
      (fun _ ζ Z => b (ζ × E) ((Open.augmentOut e₀ ℓ).reduceEnv Z)) :=
  Square.closed_iff.2 (RealizesSim.ofCompiledL e₀ hℓ h h0 hs)

end CatCrypt.Crypto.UCTransparent
