/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Deep.Deterministic
public import CatCryptCore.Deep.Eval

/-!
# Deterministic Code Interpretation

This file provides `interpDet`, which interprets deterministic `RawCode`
into `StateM Heap`, and proves soundness: `interpDet` agrees with `eval`
on deterministic code (evaluating to a Dirac distribution).

## Main definitions

* `interpDet` - Interpret deterministic RawCode into `StateM Heap`
* `interpDet_sound` - Soundness: `interpDet` agrees with `eval`
* `eval_eq_of_interpDet_run_eq` - deterministic programs with equal `interpDet`
  runs from a heap have equal evaluations from that heap; it takes the place
  of `det_self_advantage_zero`, whose conclusion `c.eval h = c.eval h` held by
  reflexivity

## Design

`interpDet` takes an `IsDeterministic` proof to eliminate the `sample`/`fail`
cases via `absurd`. We recurse on `RawCode` (which lives in `Type`) since
`IsDeterministic` lives in `Prop` and cannot eliminate into `Type`.
-/

@[expose] public section

namespace CatCrypt.Deep

open CatCrypt.Core
open CatCrypt.Prob

/-- Interpret deterministic `RawCode` into `StateM Heap`.

    This gives a concrete, efficient semantics for deterministic code.
    The result is a pure state-passing function with no probability involved.

    Takes the `IsDeterministic` proof to eliminate the `sample`/`fail` cases
    via `absurd`. We recurse on `RawCode` (which lives in `Type`) and use
    the proof to derive `False` in unreachable branches. -/
noncomputable def interpDet : {α : Type} → (c : RawCode α) → IsDeterministic c → StateM Heap α
  | _, .ret a, _ => pure a
  | _, .bind c k, h =>
    do let a ← interpDet c h.of_bind_left
       interpDet (k a) (h.of_bind_right a)
  | _, .get ℓ, _ =>
    do let h ← StateT.get; pure ⟨Heap.get h ℓ⟩
  | _, .put ℓ v, _ =>
    do let h ← StateT.get; StateT.set (Heap.set h ℓ v); pure ⟨()⟩
  | _, @RawCode.sample T _ft _ne, h => absurd h IsDeterministic.not_sample
  | _, .fail, h => absurd h IsDeterministic.not_fail
  | _, .oracleCall _ _ _ _, h => absurd h IsDeterministic.not_oracleCall
  | _, .embed _, h => absurd h IsDeterministic.not_embed

/-- Convert a `DetCode` to `StateM Heap` using `interpDet`. -/
noncomputable def DetCode.toStateM {α : Type} (dc : DetCode α) : StateM Heap α :=
  interpDet dc.code dc.isDet

/-! ## Soundness

The key theorem: for deterministic code, `interpDet` computes the same
result as `eval`, but deterministically (as a Dirac distribution). -/

/-- Running `interpDet` on a deterministic code produces a result `(a, h')`
    such that `eval c` from heap `h` gives the Dirac distribution on `(some (a, h'))`.

    This connects the deterministic (StateM) and probabilistic (SPComp) semantics:
    for deterministic code, there is exactly one possible outcome with probability 1. -/
theorem interpDet_sound {α : Type} (c : RawCode α) (hdet : IsDeterministic c) (h : Heap) :
    c.eval h = SDistr.pure ((interpDet c hdet).run h) := by
  induction c generalizing h with
  | ret a =>
    simp only [eval_ret, SPComp.pure, interpDet]
    rfl
  | bind c k ihc ihk =>
    have hc := hdet.of_bind_left
    have hk := hdet.of_bind_right
    simp only [eval_bind, SPComp.bind, interpDet]
    rw [ihc hc h]
    -- Under 4.29 the surface `(SDistr.pure ...).bind fun x ↦ (k x.1).eval x.2`
    -- displays as `Bind.bind` (the Monad instance method), not the raw
    -- `SDistr.bind`. Normalise via the change tactic, then apply the
    -- standard left-unit law and finish via `ihk`.
    change (SDistr.bind (SDistr.pure _) _) = _
    rw [SDistr.pure_bind]
    exact ihk _ (hk _) _
  | @sample T _ _ => exact absurd hdet IsDeterministic.not_sample
  | fail => exact absurd hdet IsDeterministic.not_fail
  | get ℓ =>
    simp only [eval_get, SPComp.bind, SPComp.get, SDistr.pure_bind, SPComp.pure, interpDet]
    rfl
  | put ℓ v =>
    simp only [eval_put, SPComp.bind, SPComp.set, SDistr.pure_bind, SPComp.pure, interpDet]
    rfl
  | oracleCall _ _ _ _ => exact absurd hdet IsDeterministic.not_oracleCall
  | embed _ => exact absurd hdet IsDeterministic.not_embed

/-- Two deterministic programs whose `interpDet` runs agree from a heap `h`
    have the same output distribution from `h`, so no distinguisher separates
    them there. -/
theorem eval_eq_of_interpDet_run_eq {α : Type} (c₁ c₂ : RawCode α)
    (hdet₁ : IsDeterministic c₁) (hdet₂ : IsDeterministic c₂) (h : Heap)
    (hrun : (interpDet c₁ hdet₁).run h = (interpDet c₂ hdet₂).run h) :
    c₁.eval h = c₂.eval h := by
  rw [interpDet_sound c₁ hdet₁ h, interpDet_sound c₂ hdet₂ h, hrun]

end CatCrypt.Deep
