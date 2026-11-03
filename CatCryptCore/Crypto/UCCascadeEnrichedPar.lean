/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCCascadeEnriched
public import CatCryptCore.Crypto.UCParallel
public import CatCryptCore.Crypto.UCFeedback

/-!
# Parallel composition and feedback in the Lawvere metric enrichment

The realization distance `Cell1.dist` makes each hom-type of `RSysBicat` a Lawvere metric space,
and the cascade is non-expansive (`Cell1.dist_seq_le`). This module adds the parallel composition
`Cell1.par` and the bounded feedback `Cell1.loopback` of classes of lossless systems and shows
both non-expansive under a side condition on idle events:

* `dist (f.par g) (f'.par g') ≤ dist f f' + dist g g'` (`Cell1.dist_par_le`), the `ℓ¹`
  distance on pairs, as for the cascade;
* `dist (f.loopback n cut) (f'.loopback n cut) ≤ dist f f'` (`Cell1.dist_loopback_le`), for every
  fuel `n` and cut-off map `cut`.

The side condition is `Cell1.IdleAt f e`: the class `f` has a representative that stays in its
state on the event `e` and answers it with a fixed output. Parallel composition and feedback are
one-hole contexts whose environment reduction runs the hole for a fixed number of rounds and
pads the rounds in which the hole is not activated with the idle event (`realizes_par`,
`Realizes.loopback`); a system that changes its state or its output on every event has no such
padding. The condition is a property of the class, invariant under step equivalence by
construction, so the classes idle at given events form a subspace of each hom-object, and the
operations restricted to these subspaces are non-expansive maps of Lawvere metric spaces. Each operation of a parallel
composition carries one idle event per factor, shared by the two classes compared; the feedback
carries one idle event on its full interface `E ⊕ X`.

## Main definitions

* `LSysObj.par`, `LSysObj.loopback`: parallel composition and bounded feedback of lossless
  systems.
* `Cell1.par`, `Cell1.loopback`: the same operations on step equivalence classes.
* `Cell1.IdleAt`: the class has a representative idle at an event.

## Main results

* `Cell1.holds_par`, `Cell1.holds_loopback`: realization at statistical bounds is preserved,
  the bounds of parallel factors adding.
* `Cell1.dist_par_le`: parallel composition is non-expansive for the `ℓ¹` distance on pairs.
* `Cell1.dist_loopback_le`: feedback is non-expansive.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open scoped ENNReal

namespace LSysObj

variable {E O E' O' X : Type}

/-- The rest of an activation of a multi-call hybrid over a lossless subroutine never fails. -/
private theorem drive_noFail {σ τ EG OG : Type} (π : MultiHybrid σ E O EG OG)
    (S : Sys τ EG OG) (hS : ∀ t g, SPComp.NoFail (S.step t g)) :
    ∀ n s d t, SPComp.NoFail (π.drive S n s d t) := by
  intro n
  induction n with
  | zero =>
    rintro s (g | o) t
    · exact Assumptions.SPComp.bind_noFail (hS _ _) fun _ =>
        Assumptions.SPComp.bind_noFail (π.finish_noFail _ _) fun _ => SPComp.pure_noFail _
    · exact SPComp.pure_noFail _
  | succ n ih =>
    rintro s (g | o) t
    · exact Assumptions.SPComp.bind_noFail (hS _ _) fun _ =>
        Assumptions.SPComp.bind_noFail (π.resume_noFail _ _) fun _ => ih _ _ _
    · exact SPComp.pure_noFail _

/-- The parallel composition of lossless systems. -/
noncomputable def par (A : LSysObj E O) (B : LSysObj E' O') : LSysObj (E ⊕ E') (O ⊕ O') where
  obj := A.obj.par B.obj
  noFail s e := by
    cases e with
    | inl e =>
      exact Assumptions.SPComp.bind_noFail (A.noFail s.1 e) fun q =>
        SPComp.pure_noFail (((q.1, s.2), Sum.inl q.2) : (A.obj.St × B.obj.St) × (O ⊕ O'))
    | inr e =>
      exact Assumptions.SPComp.bind_noFail (B.noFail s.2 e) fun q =>
        SPComp.pure_noFail (((s.1, q.1), Sum.inr q.2) : (A.obj.St × B.obj.St) × (O ⊕ O'))

/-- The loopback of a lossless system along its wire `X`, with fuel `n` and cut-off map `cut`. -/
noncomputable def loopback (A : LSysObj (E ⊕ X) (O ⊕ X)) (n : ℕ) (cut : X → O) :
    LSysObj E O where
  obj := A.obj.loopback n cut
  noFail t e := by
    change SPComp.NoFail (((MultiHybrid.fbHybrid n cut).withSub A.obj.sys).step t e)
    simp only [MultiHybrid.withSub]
    exact Assumptions.SPComp.bind_noFail ((MultiHybrid.fbHybrid n cut).start_noFail _ _)
      fun _ => Assumptions.SPComp.bind_noFail (drive_noFail _ _ A.noFail _ _ _ _) fun _ =>
        SPComp.pure_noFail _

end LSysObj

namespace Cell1

variable {E O E' O' X : Type}

/-- The parallel composition of step equivalence classes. -/
noncomputable def par (f : Cell1 E O) (g : Cell1 E' O') : Cell1 (E ⊕ E') (O ⊕ O') :=
  Quotient.map₂ LSysObj.par (fun _ _ h₁ _ _ h₂ => Sys.StepEq.par h₁ h₂) f g

/-- The loopback of a step equivalence class along the wire `X`, with fuel `n` and cut-off map
`cut`. -/
noncomputable def loopback (f : Cell1 (E ⊕ X) (O ⊕ X)) (n : ℕ) (cut : X → O) : Cell1 E O :=
  Quotient.map (fun A => A.loopback n cut) (fun _ _ h => Sys.StepEq.loopback h n cut) f

/-- The class `f` has a representative idle at the event `e`: it stays in its state on `e` and
answers it with a fixed output. -/
def IdleAt (f : Cell1 E O) (e : E) : Prop :=
  ∃ A : LSysObj E O, (⟦A⟧ : Cell1 E O) = f ∧ ∃ o, MultiHybrid.IdleAt A.obj.sys e o

/-- The class of a system idle at `e` is idle at `e`. -/
theorem idleAt_mk {A : LSysObj E O} {e : E} {o : O} (h : MultiHybrid.IdleAt A.obj.sys e o) :
    Cell1.IdleAt (⟦A⟧ : Cell1 E O) e :=
  ⟨A, rfl, o, h⟩

/-- **Parallel composition of realizations at statistical bounds.** For classes idle at `eL`
on the left and at `eR` on the right, realizations at bounds `ε` and `δ` compose in parallel to
a realization at bound `ε + δ`. -/
theorem holds_par {f f' : Cell1 E O} {g g' : Cell1 E' O'} {eL : E} {eR : E'}
    (hf : f.IdleAt eL) (hf' : f'.IdleAt eL) (hg : g.IdleAt eR) (hg' : g'.IdleAt eR)
    {ε δ : ℝ≥0∞} (h₁ : Holds f f' ε) (h₂ : Holds g g' δ) :
    Holds (f.par g) (f'.par g') (ε + δ) := by
  obtain ⟨A, rfl, oA, hA⟩ := hf
  obtain ⟨A', rfl, oA', hA'⟩ := hf'
  obtain ⟨B, rfl, oB, hB⟩ := hg
  obtain ⟨B', rfl, oB', hB'⟩ := hg'
  exact realizes_par B.noFail A'.noFail eL eR hA hA' hB hB' h₁ h₂

/-- **Feedback of a realization at a statistical bound.** For classes idle at `e`, a realization
at bound `ε` is preserved by the loopback with every fuel and cut-off map. -/
theorem holds_loopback {f f' : Cell1 (E ⊕ X) (O ⊕ X)} {e : E ⊕ X} (hf : f.IdleAt e)
    (hf' : f'.IdleAt e) {ε : ℝ≥0∞} (h : Holds f f' ε) (n : ℕ) (cut : X → O) :
    Holds (f.loopback n cut) (f'.loopback n cut) ε := by
  obtain ⟨A, rfl, oA, hA⟩ := hf
  obtain ⟨A', rfl, oA', hA'⟩ := hf'
  exact Realizes.loopback e oA oA' hA hA' h n cut

/-- **Parallel composition is non-expansive** for the `ℓ¹` distance on pairs, on classes idle at
`eL` on the left and at `eR` on the right. -/
theorem dist_par_le {f f' : Cell1 E O} {g g' : Cell1 E' O'} {eL : E} {eR : E'}
    (hf : f.IdleAt eL) (hf' : f'.IdleAt eL) (hg : g.IdleAt eR) (hg' : g'.IdleAt eR) :
    dist (f.par g) (f'.par g') ≤ dist f f' + dist g g' :=
  dist_le_iff.2 (holds_par hf hf' hg hg' (holds_dist f f') (holds_dist g g'))

/-- **Feedback is non-expansive** on classes idle at `e`, for every fuel and cut-off map. -/
theorem dist_loopback_le {f f' : Cell1 (E ⊕ X) (O ⊕ X)} {e : E ⊕ X} (hf : f.IdleAt e)
    (hf' : f'.IdleAt e) (n : ℕ) (cut : X → O) :
    dist (f.loopback n cut) (f'.loopback n cut) ≤ dist f f' :=
  dist_le_iff.2 (holds_loopback hf hf' (holds_dist f f') n cut)

end Cell1

end CatCrypt.Crypto.UCTransparent
