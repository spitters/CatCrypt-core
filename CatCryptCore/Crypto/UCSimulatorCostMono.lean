/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCSimulatorCostSized

/-!
# Costed simulators at other views

The costed mirror of `Simulator.mono` of `UCSimulator.lean`: a costed simulator at other views,
with the same costed machines, its erasure to `S.mono hVev hVout hWev hWout`, and its time bounds.

## Main definitions

* `Simulator.Timed.mono`: a costed simulator at other views.
* `MultiHybrid.Opaque.mono`: opacity of a multi-call simulator is monotone in its views.
* `Simulator.mono.erase_timed`, `Simulator.mono.timeBound_timed`,
  `Simulator.mono.timeBoundGraded_timed`, `Simulator.mono.timeBoundSized_timed`: erasure and
  time of a costed simulator at other views.
* `Simulator.mono.answerSizeLe`: the sizes of its answers.
-/

public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Relational

/-- The relation `V.StepRel W` on decisions is monotone in the outer outputs and the subroutine
events. -/
theorem PubView.StepRel.mono {E O EG OG : Type} {V V' : PubView E O} {W W' : PubView EG OG}
    (hVout : ∀ o o', V.out o o' → V'.out o o') (hWev : ∀ g g', W.ev g g' → W'.ev g g')
    {d d' : EG ⊕ O} (h : V.StepRel W d d') : V'.StepRel W' d d' := by
  rcases d with g | o <;> rcases d' with g' | o'
  · exact hWev _ _ h
  · exact h
  · exact h
  · exact hVout _ _ h

/-- Opacity of a multi-call simulator for views gives opacity for an outer view that relates
fewer events and more outputs and a subroutine view that relates more events and fewer
answers. -/
theorem MultiHybrid.Opaque.mono {σ E O EG OG : Type} {π : MultiHybrid σ E O EG OG}
    {V V' : PubView E O} {W W' : PubView EG OG} (h : π.Opaque V W)
    (hVev : ∀ e e', V'.ev e e' → V.ev e e') (hVout : ∀ o o', V.out o o' → V'.out o o')
    (hWev : ∀ g g', W.ev g g' → W'.ev g g') (hWout : ∀ o o', W'.out o o' → W.out o o') :
    π.Opaque V' W' := by
  obtain ⟨R, hR⟩ := h
  refine ⟨R, hR.init, fun s s' e e' hs he => ?_, fun s s' o o' hs ho => ?_,
    fun s s' o o' hs ho => ?_⟩
  · exact rHoare_conseq (fun _ _ hh => hh)
      (fun _ _ _ _ hp => ⟨hp.1, hp.2.1, PubView.StepRel.mono hVout hWev hp.2.2⟩)
      (hR.start s s' e e' hs (hVev e e' he))
  · exact rHoare_conseq (fun _ _ hh => hh)
      (fun _ _ _ _ hp => ⟨hp.1, hp.2.1, PubView.StepRel.mono hVout hWev hp.2.2⟩)
      (hR.resume s s' o o' hs (hWout o o' ho))
  · exact rHoare_conseq (fun _ _ hh => hh)
      (fun _ _ _ _ hp => ⟨hp.1, hp.2.1, hVout _ _ hp.2.2⟩)
      (hR.finish s s' o o' hs (hWout o o' ho))

/-- A costed simulator at the outer view `V'` and the subroutine view `W'`. The views index the
type and constrain only the erasure, so the costed machines are unchanged; the middle view of a
composite and the inner view of a relabelling are kept. -/
@[expose] def Simulator.Timed.mono : {E O EG OG : Type} → {V : PubView E O} → {W : PubView EG OG} →
    Simulator.Timed E O EG OG V W → (V' : PubView E O) → (W' : PubView EG OG) →
    Simulator.Timed E O EG OG V' W'
  | _, _, _, _, _, _, .ofMultiHybrid πT, _, _ => .ofMultiHybrid πT
  | _, _, _, _, _, _, .ofMultiHybridHat εσ εE εO εEG εOG πT, _, _ =>
    .ofMultiHybridHat εσ εE εO εEG εOG πT
  | _, _, _, _, _, _, .comp (U := U) T₁ T₂, V', W' =>
    .comp (U := U) (Simulator.Timed.mono T₁ V' U) (Simulator.Timed.mono T₂ U W')
  | _, _, _, _, _, _, .mapPorts (U := U) T f g, _, W' =>
    .mapPorts (U := U) (Simulator.Timed.mono T U W') f g

namespace Simulator

variable {E O EG OG : Type} {V V' : PubView E O} {W W' : PubView EG OG}

/-- **Erasure of a costed simulator at other views**: a costed simulator that erases to `S`
erases, at the views `V'` and `W'`, to `S.mono hVev hVout hWev hWout`. -/
theorem mono.erase_timed {S : Simulator E O EG OG V W} {T : Simulator.Timed E O EG OG V W}
    (hT : T.Erases S) (hVev : ∀ e e', V'.ev e e' → V.ev e e')
    (hVout : ∀ o o', V.out o o' → V'.out o o') (hWev : ∀ g g', W.ev g g' → W'.ev g g')
    (hWout : ∀ o o', W'.out o o' → W.out o o') :
    (T.mono V' W').Erases (S.mono hVev hVout hWev hWout) := by
  induction T with
  | ofMultiHybrid πT =>
    obtain ⟨π, h, hp, rfl⟩ := hT
    exact ⟨π, h.mono hVev hVout hWev hWout, hp, rfl⟩
  | ofMultiHybridHat εσ εE εO εEG εOG πT =>
    obtain ⟨π, h, hp, rfl⟩ := hT
    exact ⟨π, h.mono hVev hVout hWev hWout, hp, rfl⟩
  | comp T₁ T₂ ih₁ ih₂ =>
    obtain ⟨S₁, S₂, h₁, h₂, rfl⟩ := hT
    exact ⟨_, _, ih₁ h₁ hVev hVout (fun _ _ h => h) (fun _ _ h => h),
      ih₂ h₂ (fun _ _ h => h) (fun _ _ h => h) hWev hWout, rfl⟩
  | mapPorts T f g ih =>
    obtain ⟨S₀, hf, hg, h₀, rfl⟩ := hT
    exact ⟨_, fun e e' h => hf e e' (hVev e e' h), fun o o' h => hVout _ _ (hg o o' h),
      ih h₀ (fun _ _ h => h) (fun _ _ h => h) hWev hWout, rfl⟩

/-- **Running time of a costed simulator at other views**: the time of the costed simulator. -/
theorem mono.timeBound_timed {T : Simulator.Timed E O EG OG V W} {t : ℕ} (hT : T.TimeBound t)
    (V' : PubView E O) (W' : PubView EG OG) : (T.mono V' W').TimeBound t := by
  induction T generalizing t with
  | ofMultiHybrid πT => exact hT
  | ofMultiHybridHat εσ εE εO εEG εOG πT => exact hT
  | comp T₁ T₂ ih₁ ih₂ =>
    obtain ⟨t₁, t₂, h₁, h₂, hle⟩ := hT
    exact ⟨t₁, t₂, ih₁ h₁ _ _, ih₂ h₂ _ _, hle⟩
  | mapPorts T f g ih => exact ih hT _ _

/-- **Graded running time of a costed simulator at other views**: the graded time of the costed
simulator. -/
theorem mono.timeBoundGraded_timed {T : Simulator.Timed E O EG OG V W} {a b : ℕ}
    (hT : T.TimeBoundGraded a b) (V' : PubView E O) (W' : PubView EG OG) :
    (T.mono V' W').TimeBoundGraded a b := by
  induction T generalizing a b with
  | ofMultiHybrid πT => exact hT
  | ofMultiHybridHat εσ εE εO εEG εOG πT => exact hT
  | comp T₁ T₂ ih₁ ih₂ =>
    obtain ⟨a₁, b₁, a₂, b₂, h₁, h₂, h3, h4⟩ := hT
    exact ⟨a₁, b₁, a₂, b₂, ih₁ h₁ _ _, ih₂ h₂ _ _, h3, h4⟩
  | mapPorts T f g ih => exact ih hT _ _

/-- The answers of a costed simulator at other views have the sizes bounded by the times of
its steps that those of the costed simulator have. -/
theorem mono.answerSizeLe {T : Simulator.Timed E O EG OG V W} {sA : O → ℕ}
    (hT : T.AnswerSizeLe sA) (V' : PubView E O) (W' : PubView EG OG) :
    (T.mono V' W').AnswerSizeLe sA := by
  induction T with
  | ofMultiHybrid πT => exact hT
  | ofMultiHybridHat εσ εE εO εEG εOG πT => exact hT
  | comp T₁ T₂ ih₁ _ => exact ih₁ hT _ _
  | mapPorts T f g ih => exact ih hT _ _

/-- **Size-graded running time of a costed simulator at other views**: the size-graded time of
the costed simulator. -/
theorem mono.timeBoundSized_timed {T : Simulator.Timed E O EG OG V W} {sE : E → ℕ} {sO : OG → ℕ}
    {a b c : ℕ} (hT : T.TimeBoundSized sE sO a b c) (V' : PubView E O) (W' : PubView EG OG) :
    (T.mono V' W').TimeBoundSized sE sO a b c := by
  induction T generalizing a b c with
  | ofMultiHybrid πT => exact hT
  | ofMultiHybridHat εσ εE εO εEG εOG πT => exact hT
  | comp T₁ T₂ ih₁ ih₂ =>
    obtain ⟨sM, a₁, b₁, c₁, a₂, b₂, c₂, h₁, h₂, hM, h3, h4, h5⟩ := hT
    exact ⟨sM, a₁, b₁, c₁, a₂, b₂, c₂, ih₁ h₁ _ _, ih₂ h₂ _ _, mono.answerSizeLe hM _ _, h3, h4,
      h5⟩
  | mapPorts T f g ih =>
    obtain ⟨sM, hM, h⟩ := hT
    exact ⟨sM, hM, ih h _ _⟩

end Simulator

end CatCrypt.Crypto.UCTransparent
