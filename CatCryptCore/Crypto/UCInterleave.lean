/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCSquare

/-!
# Tensor of multi-call hybrids and the modular UC theorem

The tensor `π.tensor π'` of two multi-call hybrids runs them side by side on the sum of their
interfaces: an outer event `inl e` activates `π` and `inr e'` activates `π'`, and a subroutine
answer goes to the component named by its tag. The state is the pair of states and the fuel is
the larger of the two fuels; a component of smaller fuel receives `resume` where it would
receive `finish`, which leaves its behaviour unchanged when its `resume` ends the activation on
every answer (as for the forwarding simulator `idSim`). Opacity is closed under the tensor, for
the sum of the views (`MultiHybrid.Opaque.tensor`).

The extension `extendFwd EF OF S` of a simulator `S` on an adversary port is the tensor of the
forwarding simulator on the port `(EF, OF)` with `S`. A protocol `πH` with honest outer port
`(EF, OF)` and honest subroutine port `(EH, OH)` forwards an adversary port `(EA, OA)` as
`πH.tensor (idSim EA OA)` (`MultiHybrid.Forwards`). The interchange law
(`MultiHybrid.realizes_interchange`) states that `πH` forwarding the adversary port of
`(idSim EH OH).tensor S` over `K` and `extendFwd EF OF S` over `πH` forwarding the adversary port
of `K` realize each other at distance `0`, for every `K` that answers each event on the port of
the event (`Sys.PortTyped`). As a square (`Square.interchange`) it gives the modular UC theorem
(`RealizesSim.modular`): if `ρ` realizes `G` behind `(idSim EH OH).tensor S` and the hybrid
protocol over `G` realizes `F` behind `SF`, then the protocol over `ρ` realizes `F` behind
`extendFwd EF OF S` composed with `SF`.

## Main definitions

* `PubView.sum`: the view of a sum interface.
* `MultiHybrid.tensor`, `MultiHybrid.extendFwd`: the tensor and the extension by forwarding.
* `MultiHybrid.Forwards`: forwarding of a port without a change of state.
* `MultiHybrid.stepFuel`: one activation with a given number of calls.
* `Sys.PortTyped`: a system that answers each event on the port of the event.
* `Simulator.tensor`, `SimR.tensor`: the tensor of opaque multi-call simulators.

## Main results

* `MultiHybrid.Opaque.tensor`: opacity of the tensor.
* `MultiHybrid.forwards_tensor_idSim`: `πH.tensor (idSim EA OA)` forwards `(EA, OA)`.
* `MultiHybrid.realizes_interchange`, `Square.interchange`: the interchange law.
* `RealizesSim.modular`: the modular UC theorem.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Relational
open scoped ENNReal

/-! ## Views of a sum interface -/

namespace PubView

variable {E O E' O' EG OG EG' OG' : Type}

/-- The view of the sum interface `(E ⊕ E', O ⊕ O')`: events and outputs on the same port,
related by the view of that port. -/
def sum (V : PubView E O) (V' : PubView E' O') : PubView (E ⊕ E') (O ⊕ O') where
  ev := Sum.LiftRel V.ev V'.ev
  out := Sum.LiftRel V.out V'.out

/-- Related decisions on the left port are related decisions of the sum. -/
theorem stepRel_sum_inl {V : PubView E O} {W : PubView EG OG} {V' : PubView E' O'}
    {W' : PubView EG' OG'} {d d' : EG ⊕ O} (h : StepRel V W d d') :
    StepRel (V.sum V') (W.sum W') (Sum.map Sum.inl Sum.inl d) (Sum.map Sum.inl Sum.inl d') := by
  rcases d with g | o <;> rcases d' with g' | o'
  · exact Sum.LiftRel.inl h
  · exact h.elim
  · exact h.elim
  · exact Sum.LiftRel.inl h

/-- Related decisions on the right port are related decisions of the sum. -/
theorem stepRel_sum_inr {V : PubView E O} {W : PubView EG OG} {V' : PubView E' O'}
    {W' : PubView EG' OG'} {d d' : EG' ⊕ O'} (h : StepRel V' W' d d') :
    StepRel (V.sum V') (W.sum W') (Sum.map Sum.inr Sum.inr d) (Sum.map Sum.inr Sum.inr d') := by
  rcases d with g | o <;> rcases d' with g' | o'
  · exact Sum.LiftRel.inr h
  · exact h.elim
  · exact h.elim
  · exact Sum.LiftRel.inr h

end PubView

/-- A coupling of `c₁` and `c₂` gives a coupling of their images under `f₁` and `f₂`. -/
private theorem rHoare_map {α β γ δ : Type} {Φ : RPre} {c₁ : SPComp α} {c₂ : SPComp β}
    {f₁ : α → γ} {f₂ : β → δ} {Ψ : RPost α β} {Θ : RPost γ δ} (h : rHoare Φ c₁ c₂ Ψ)
    (hf : ∀ a h₁ b h₂, Ψ a h₁ b h₂ → Θ (f₁ a) h₁ (f₂ b) h₂) :
    rHoare Φ (SPComp.map f₁ c₁) (SPComp.map f₂ c₂) Θ :=
  rHoare_bind h fun a b => rHoare_ret fun h₁ h₂ hΨ => hf a h₁ b h₂ hΨ

/-! ## The tensor -/

namespace MultiHybrid

variable {σ σ' τ E O E' O' EG OG EG' OG' : Type}

/-- The tensor of `π` and `π'` on the sum of their interfaces: an outer event activates the
component on its port, a subroutine answer resumes the component named by its tag, and the fuel
is the larger of the two fuels. -/
noncomputable def tensor (π : MultiHybrid σ E O EG OG) (π' : MultiHybrid σ' E' O' EG' OG') :
    MultiHybrid (σ × σ') (E ⊕ E') (O ⊕ O') (EG ⊕ EG') (OG ⊕ OG') where
  init := (π.init, π'.init)
  fuel := max π.fuel π'.fuel
  start s := Sum.elim
    (fun e => SPComp.map (fun r => ((r.1, s.2), Sum.map Sum.inl Sum.inl r.2)) (π.start s.1 e))
    (fun e => SPComp.map (fun r => ((s.1, r.1), Sum.map Sum.inr Sum.inr r.2)) (π'.start s.2 e))
  resume s := Sum.elim
    (fun o => SPComp.map (fun r => ((r.1, s.2), Sum.map Sum.inl Sum.inl r.2)) (π.resume s.1 o))
    (fun o => SPComp.map (fun r => ((s.1, r.1), Sum.map Sum.inr Sum.inr r.2))
      (π'.resume s.2 o))
  finish s := Sum.elim
    (fun o => SPComp.map (fun r => ((r.1, s.2), Sum.inl r.2)) (π.finish s.1 o))
    (fun o => SPComp.map (fun r => ((s.1, r.1), Sum.inr r.2)) (π'.finish s.2 o))
  start_noFail s e := by
    rcases e with e | e <;> simp only [Sum.elim_inl, Sum.elim_inr, SPComp.map]
    · exact Assumptions.SPComp.bind_noFail (π.start_noFail _ _) fun _ => SPComp.pure_noFail _
    · exact Assumptions.SPComp.bind_noFail (π'.start_noFail _ _) fun _ => SPComp.pure_noFail _
  resume_noFail s o := by
    rcases o with o | o <;> simp only [Sum.elim_inl, Sum.elim_inr, SPComp.map]
    · exact Assumptions.SPComp.bind_noFail (π.resume_noFail _ _) fun _ => SPComp.pure_noFail _
    · exact Assumptions.SPComp.bind_noFail (π'.resume_noFail _ _) fun _ => SPComp.pure_noFail _
  finish_noFail s o := by
    rcases o with o | o <;> simp only [Sum.elim_inl, Sum.elim_inr, SPComp.map]
    · exact Assumptions.SPComp.bind_noFail (π.finish_noFail _ _) fun _ => SPComp.pure_noFail _
    · exact Assumptions.SPComp.bind_noFail (π'.finish_noFail _ _) fun _ => SPComp.pure_noFail _

section TensorUnfold

variable (π : MultiHybrid σ E O EG OG) (π' : MultiHybrid σ' E' O' EG' OG') (s : σ × σ')

/-- Unfolding lemma of `tensor`: `start` on a left event. -/
@[simp] theorem tensor_start_inl (e : E) : (π.tensor π').start s (.inl e) =
    SPComp.map (fun r => ((r.1, s.2), Sum.map Sum.inl Sum.inl r.2)) (π.start s.1 e) := rfl

/-- Unfolding lemma of `tensor`: `start` on a right event. -/
@[simp] theorem tensor_start_inr (e : E') : (π.tensor π').start s (.inr e) =
    SPComp.map (fun r => ((s.1, r.1), Sum.map Sum.inr Sum.inr r.2)) (π'.start s.2 e) := rfl

/-- Unfolding lemma of `tensor`: `resume` on a left answer. -/
@[simp] theorem tensor_resume_inl (o : OG) : (π.tensor π').resume s (.inl o) =
    SPComp.map (fun r => ((r.1, s.2), Sum.map Sum.inl Sum.inl r.2)) (π.resume s.1 o) := rfl

/-- Unfolding lemma of `tensor`: `resume` on a right answer. -/
@[simp] theorem tensor_resume_inr (o : OG') : (π.tensor π').resume s (.inr o) =
    SPComp.map (fun r => ((s.1, r.1), Sum.map Sum.inr Sum.inr r.2)) (π'.resume s.2 o) := rfl

/-- Unfolding lemma of `tensor`: `finish` on a left answer. -/
@[simp] theorem tensor_finish_inl (o : OG) : (π.tensor π').finish s (.inl o) =
    SPComp.map (fun r => ((r.1, s.2), Sum.inl r.2)) (π.finish s.1 o) := rfl

/-- Unfolding lemma of `tensor`: `finish` on a right answer. -/
@[simp] theorem tensor_finish_inr (o : OG') : (π.tensor π').finish s (.inr o) =
    SPComp.map (fun r => ((s.1, r.1), Sum.inr r.2)) (π'.finish s.2 o) := rfl

end TensorUnfold

/-! ## Opacity of the tensor -/

section Opacity

variable {π : MultiHybrid σ E O EG OG} {π' : MultiHybrid σ' E' O' EG' OG'}
  {V : PubView E O} {W : PubView EG OG} {V' : PubView E' O'} {W' : PubView EG' OG'}

/-- Unwinding relations `R` of `π` and `R'` of `π'` give the unwinding relation `R × R'` of
the tensor, for the sums of the views. -/
theorem Unwinding.tensor {R : σ → σ → Prop} {R' : σ' → σ' → Prop} (h : π.Unwinding V W R)
    (h' : π'.Unwinding V' W' R') :
    (π.tensor π').Unwinding (V.sum V') (W.sum W') (fun s t => R s.1 t.1 ∧ R' s.2 t.2) where
  init := ⟨h.init, h'.init⟩
  start := by
    rintro ⟨s₁, s₁'⟩ ⟨s₂, s₂'⟩ e e' ⟨hs, hs'⟩ he
    cases he with
    | inl he =>
      simp only [tensor_start_inl]
      exact rHoare_map (h.start _ _ _ _ hs he) fun _ _ _ _ hp =>
        ⟨hp.1, ⟨hp.2.1, hs'⟩, PubView.stepRel_sum_inl hp.2.2⟩
    | inr he =>
      simp only [tensor_start_inr]
      exact rHoare_map (h'.start _ _ _ _ hs' he) fun _ _ _ _ hp =>
        ⟨hp.1, ⟨hs, hp.2.1⟩, PubView.stepRel_sum_inr hp.2.2⟩
  resume := by
    rintro ⟨s₁, s₁'⟩ ⟨s₂, s₂'⟩ o o' ⟨hs, hs'⟩ ho
    cases ho with
    | inl ho =>
      simp only [tensor_resume_inl]
      exact rHoare_map (h.resume _ _ _ _ hs ho) fun _ _ _ _ hp =>
        ⟨hp.1, ⟨hp.2.1, hs'⟩, PubView.stepRel_sum_inl hp.2.2⟩
    | inr ho =>
      simp only [tensor_resume_inr]
      exact rHoare_map (h'.resume _ _ _ _ hs' ho) fun _ _ _ _ hp =>
        ⟨hp.1, ⟨hs, hp.2.1⟩, PubView.stepRel_sum_inr hp.2.2⟩
  finish := by
    rintro ⟨s₁, s₁'⟩ ⟨s₂, s₂'⟩ o o' ⟨hs, hs'⟩ ho
    cases ho with
    | inl ho =>
      simp only [tensor_finish_inl]
      exact rHoare_map (h.finish _ _ _ _ hs ho) fun _ _ _ _ hp =>
        ⟨hp.1, ⟨hp.2.1, hs'⟩, Sum.LiftRel.inl hp.2.2⟩
    | inr ho =>
      simp only [tensor_finish_inr]
      exact rHoare_map (h'.finish _ _ _ _ hs' ho) fun _ _ _ _ hp =>
        ⟨hp.1, ⟨hs, hp.2.1⟩, Sum.LiftRel.inr hp.2.2⟩

/-- **Opacity under the tensor**: the tensor of a simulator opaque from `W` to `V` and a
simulator opaque from `W'` to `V'` is opaque from `W.sum W'` to `V.sum V'`. -/
theorem Opaque.tensor (h : π.Opaque V W) (h' : π'.Opaque V' W') :
    (π.tensor π').Opaque (V.sum V') (W.sum W') := by
  obtain ⟨R, hR⟩ := h
  obtain ⟨R', hR'⟩ := h'
  exact ⟨_, hR.tensor hR'⟩

end Opacity

/-! ## Forwarding -/

/-- The extension of the simulator `S` by forwarding on the port `(EF, OF)`: the tensor of the
forwarding simulator on `(EF, OF)` with `S`. -/
noncomputable def extendFwd (EF OF : Type) (S : MultiHybrid σ E O EG OG) :
    MultiHybrid (Unit × σ) (EF ⊕ E) (OF ⊕ O) (EF ⊕ EG) (OF ⊕ OG) :=
  (idSim EF OF).tensor S

/-- The extension by forwarding of a simulator opaque from `W` to `V` is opaque from
`VF.sum W` to `VF.sum V`, for every view `VF` of the forwarded port. -/
theorem Opaque.extendFwd {EF OF : Type} {S : MultiHybrid σ E O EG OG} {V : PubView E O}
    {W : PubView EG OG} (VF : PubView EF OF) (h : S.Opaque V W) :
    (extendFwd EF OF S).Opaque (VF.sum V) (VF.sum W) :=
  (idSim_opaque VF).tensor h

/-- The multi-call hybrid `π` forwards the port `(EA, OA)`: an event `inr a` is passed on as the
subroutine event `inr a`, an answer `inr o` is returned as the outer output `inr o`, and the
state does not change. -/
structure Forwards {EF OF EH OH EA OA : Type}
    (π : MultiHybrid σ (EF ⊕ EA) (OF ⊕ OA) (EH ⊕ EA) (OH ⊕ OA)) : Prop where
  /-- An event on the port is passed on. -/
  start : ∀ s a, π.start s (.inr a) = SPComp.pure (s, .inl (.inr a))
  /-- An answer on the port is returned. -/
  resume : ∀ s o, π.resume s (.inr o) = SPComp.pure (s, .inr (.inr o))
  /-- An answer on the port to the last allowed call is returned. -/
  finish : ∀ s o, π.finish s (.inr o) = SPComp.pure (s, .inr o)

/-- The tensor of `πH` with the forwarding simulator on `(EA, OA)` forwards `(EA, OA)`. -/
theorem forwards_tensor_idSim {EF OF EH OH : Type} (πH : MultiHybrid σ EF OF EH OH)
    (EA OA : Type) : Forwards (πH.tensor (idSim EA OA)) where
  start _ _ := by simp [idSim]
  resume _ _ := by simp [idSim]
  finish _ _ := by simp [idSim]

/-! ## Activations of the tensor -/

/-- One activation of `π` against `X` on the event `e` from the state `t`, with `n` calls
allowed after the first. -/
noncomputable def stepFuel (π : MultiHybrid σ E O EG OG) (X : Sys τ EG OG) (n : ℕ)
    (t : σ × τ) (e : E) : SPComp ((σ × τ) × O) :=
  SPComp.bind (π.start t.1 e) fun r =>
    SPComp.bind (π.drive X n r.1 r.2 t.2) fun p => SPComp.pure ((p.1, p.2.1), p.2.2)

/-- The rest of an activation of the tensor on a decision of the left component, against a
subroutine that answers left events on the left port with `XL`, is the rest of the activation
of `π` against `XL`. -/
theorem tensor_drive_inl (π : MultiHybrid σ E O EG OG) (π' : MultiHybrid σ' E' O' EG' OG')
    (X : Sys τ (EG ⊕ EG') (OG ⊕ OG')) (XL : Sys τ EG OG)
    (hX : ∀ t g, X.step t (.inl g) = SPComp.map (fun q => (q.1, .inl q.2)) (XL.step t g)) :
    ∀ n s s' d t, (π.tensor π').drive X n (s, s') (Sum.map Sum.inl Sum.inl d) t =
      SPComp.map (fun p => ((p.1, s'), p.2.1, Sum.inl p.2.2)) (π.drive XL n s d t) := by
  intro n
  induction n with
  | zero =>
    rintro s s' (g | o) t
    · simp [drive, hX, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    · simp [drive]
  | succ n ih =>
    rintro s s' (g | o) t
    · simp [drive, hX, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, ih]
    · simp [drive]

/-- The rest of an activation of the tensor on a decision of the right component, against a
subroutine that answers right events on the right port with `XR`, is the rest of the
activation of `π'` against `XR`. -/
theorem tensor_drive_inr (π : MultiHybrid σ E O EG OG) (π' : MultiHybrid σ' E' O' EG' OG')
    (X : Sys τ (EG ⊕ EG') (OG ⊕ OG')) (XR : Sys τ EG' OG')
    (hX : ∀ t g, X.step t (.inr g) = SPComp.map (fun q => (q.1, .inr q.2)) (XR.step t g)) :
    ∀ n s s' d t, (π.tensor π').drive X n (s, s') (Sum.map Sum.inr Sum.inr d) t =
      SPComp.map (fun p => ((s, p.1), p.2.1, Sum.inr p.2.2)) (π'.drive XR n s' d t) := by
  intro n
  induction n with
  | zero =>
    rintro s s' (g | o) t
    · simp [drive, hX, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    · simp [drive]
  | succ n ih =>
    rintro s s' (g | o) t
    · simp [drive, hX, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, ih]
    · simp [drive]

/-- A step of the tensor over `X` on a left event is an activation of `π` against `XL`, with the
fuel of the tensor. -/
theorem tensor_withSub_step_inl (π : MultiHybrid σ E O EG OG)
    (π' : MultiHybrid σ' E' O' EG' OG') (X : Sys τ (EG ⊕ EG') (OG ⊕ OG')) (XL : Sys τ EG OG)
    (hX : ∀ t g, X.step t (.inl g) = SPComp.map (fun q => (q.1, .inl q.2)) (XL.step t g))
    (s : σ) (s' : σ') (t : τ) (e : E) :
    ((π.tensor π').withSub X).step ((s, s'), t) (.inl e) =
      SPComp.map (fun p => (((p.1.1, s'), p.1.2), Sum.inl p.2))
        (π.stepFuel XL (max π.fuel π'.fuel) (s, t) e) := by
  simp only [withSub, tensor_start_inl, tensor_drive_inl π π' X XL hX, stepFuel, SPComp.map,
    SPComp.bind_assoc, SPComp.pure_bind]
  rfl

/-- A step of the tensor over `X` on a right event is an activation of `π'` against `XR`, with
the fuel of the tensor. -/
theorem tensor_withSub_step_inr (π : MultiHybrid σ E O EG OG)
    (π' : MultiHybrid σ' E' O' EG' OG') (X : Sys τ (EG ⊕ EG') (OG ⊕ OG')) (XR : Sys τ EG' OG')
    (hX : ∀ t g, X.step t (.inr g) = SPComp.map (fun q => (q.1, .inr q.2)) (XR.step t g))
    (s : σ) (s' : σ') (t : τ) (e : E') :
    ((π.tensor π').withSub X).step ((s, s'), t) (.inr e) =
      SPComp.map (fun p => (((s, p.1.1), p.1.2), Sum.inr p.2))
        (π'.stepFuel XR (max π.fuel π'.fuel) (s', t) e) := by
  simp only [withSub, tensor_start_inr, tensor_drive_inr π π' X XR hX, stepFuel, SPComp.map,
    SPComp.bind_assoc, SPComp.pure_bind]
  rfl

/-- An activation of the forwarding simulator, with any fuel, is one step of the subroutine. -/
theorem idSim_stepFuel (X : Sys τ E O) (n : ℕ) (u : Unit) (t : τ) (e : E) :
    (idSim E O).stepFuel X n (u, t) e = SPComp.map (fun q => (((), q.1), q.2)) (X.step t e) := by
  cases n <;> simp [stepFuel, idSim, drive, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

end MultiHybrid

/-! ## Systems on a component of the state -/

namespace Sys

variable {ρ τ E O E' O' : Type}

/-- The system `X` on the second component of the state `ρ × τ`, the first component
unchanged. -/
noncomputable def onSnd (X : Sys τ E O) (r : ρ) : Sys (ρ × τ) E O where
  init := (r, X.init)
  step y e := SPComp.map (fun q => ((y.1, q.1), q.2)) (X.step y.2 e)

/-- Unfolding lemma of `Sys.onSnd`: a step on the state `(a, t)`. -/
@[simp] theorem onSnd_step (X : Sys τ E O) (r a : ρ) (t : τ) (e : E) :
    (X.onSnd r).step (a, t) e = SPComp.map (fun q => ((a, q.1), q.2)) (X.step t e) := rfl

/-- The system `K` on the sum interface answers every event on the port of the event: its
steps on left events are those of a system `KL` with left answers, and its steps on right
events are those of a system `KR` with right answers. -/
def PortTyped {τ : Type} (K : Sys τ (E ⊕ E') (O ⊕ O')) : Prop :=
  ∃ (KL : Sys τ E O) (KR : Sys τ E' O'),
    (∀ t e, K.step t (.inl e) = SPComp.map (fun q => (q.1, .inl q.2)) (KL.step t e)) ∧
    (∀ t e, K.step t (.inr e) = SPComp.map (fun q => (q.1, .inr q.2)) (KR.step t e))

end Sys

namespace MultiHybrid

variable {σ ρ τ E O EG OG : Type}

/-- The rest of an activation against `X.onSnd r` is the rest of the activation against `X`,
with the first component of the subroutine state unchanged. -/
theorem drive_onSnd (π : MultiHybrid σ E O EG OG) (X : Sys τ EG OG) (r : ρ) :
    ∀ n s d (a : ρ) t, π.drive (X.onSnd r) n s d (a, t) =
      SPComp.map (fun p => (p.1, (a, p.2.1), p.2.2)) (π.drive X n s d t) := by
  intro n
  induction n with
  | zero =>
    rintro s (g | o) a t
    · simp [drive, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    · simp [drive]
  | succ n ih =>
    rintro s (g | o) a t
    · simp [drive, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, ih]
    · simp [drive]

/-- An activation against `X.onSnd r` is an activation against `X`, with the first component of
the subroutine state unchanged. -/
theorem stepFuel_onSnd (π : MultiHybrid σ E O EG OG) (X : Sys τ EG OG) (r : ρ) (n : ℕ)
    (s : σ) (a : ρ) (t : τ) (e : E) :
    π.stepFuel (X.onSnd r) n (s, (a, t)) e =
      SPComp.map (fun p => ((p.1.1, (a, p.1.2)), p.2)) (π.stepFuel X n (s, t) e) := by
  simp [stepFuel, drive_onSnd, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-! ## The interchange law -/

variable {σS EF OF EH OH EA OA EA' OA' : Type}

/-- **Interchange** (dummy-adversary forwarding). For a subroutine `K` that answers every event
on the port of the event, `πH` forwarding the adversary port over `(idSim EH OH).tensor S` over
`K`, and `extendFwd EF OF S` over `πH` forwarding the adversary port over `K`, realize each
other at distance `0`. -/
theorem realizes_interchange (πH : MultiHybrid σ EF OF EH OH)
    (S : MultiHybrid σS EA OA EA' OA') (K : Sys τ (EH ⊕ EA') (OH ⊕ OA'))
    (KL : Sys τ EH OH) (KR : Sys τ EA' OA')
    (hL : ∀ t h, K.step t (.inl h) = SPComp.map (fun q => (q.1, .inl q.2)) (KL.step t h))
    (hR : ∀ t a, K.step t (.inr a) = SPComp.map (fun q => (q.1, .inr q.2)) (KR.step t a)) :
    Realizes ((πH.tensor (idSim EA OA)).withSub (((idSim EH OH).tensor S).withSub K))
      ((extendFwd EF OF S).withSub ((πH.tensor (idSim EA' OA')).withSub K))
      (fun _ _ => 0) := by
  unfold extendFwd
  refine realizes_zero_of_stepMap _ _ (fun p => (p.2.1, (p.1, p.2.2))) rfl ?_
  rintro ⟨⟨s, ⟨⟩⟩, ⟨⟨⟩, sS⟩, t⟩ (ef | a)
  · have hY : ∀ y h, (((idSim EH OH).tensor S).withSub K).step y (.inl h) =
        SPComp.map (fun q => (q.1, .inl q.2)) ((KL.onSnd ((), S.init)).step y h) := by
      rintro ⟨⟨⟨⟩, sS'⟩, t'⟩ h
      rw [tensor_withSub_step_inl _ _ K KL hL, idSim_stepFuel, Sys.onSnd_step]
      simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    have hZ : ∀ z e, ((πH.tensor (idSim EA' OA')).withSub K).step z (.inl e) =
        SPComp.map (fun q => (q.1, .inl q.2))
          ((⟨((πH.init, ()), K.init), fun z e =>
            SPComp.map (fun p => (((p.1.1, ()), p.1.2), p.2))
              (πH.stepFuel KL (max πH.fuel (idSim EA' OA').fuel) (z.1.1, z.2) e)⟩ :
            Sys ((σ × Unit) × τ) EF OF).step z e) := by
      rintro ⟨⟨s', ⟨⟩⟩, t'⟩ e
      rw [tensor_withSub_step_inl _ _ K KL hL]
      simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    dsimp only
    rw [tensor_withSub_step_inl _ _ _ _ hY, stepFuel_onSnd, tensor_withSub_step_inl _ _ _ _ hZ,
      idSim_stepFuel]
    simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    rfl
  · have hY : ∀ y a, (((idSim EH OH).tensor S).withSub K).step y (.inr a) =
        SPComp.map (fun q => (q.1, .inr q.2))
          ((⟨(((), S.init), K.init), fun y a =>
            SPComp.map (fun p => ((((), p.1.1), p.1.2), p.2))
              (S.stepFuel KR (max (idSim EH OH).fuel S.fuel) (y.1.2, y.2) a)⟩ :
            Sys ((Unit × σS) × τ) EA OA).step y a) := by
      rintro ⟨⟨⟨⟩, sS'⟩, t'⟩ a
      rw [tensor_withSub_step_inr _ _ K KR hR]
      simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    have hZ : ∀ z a, ((πH.tensor (idSim EA' OA')).withSub K).step z (.inr a) =
        SPComp.map (fun q => (q.1, .inr q.2)) ((KR.onSnd (πH.init, ())).step z a) := by
      rintro ⟨⟨s', ⟨⟩⟩, t'⟩ a
      rw [tensor_withSub_step_inr _ _ K KR hR, idSim_stepFuel, Sys.onSnd_step]
      simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    dsimp only
    rw [tensor_withSub_step_inr _ _ _ _ hY, idSim_stepFuel, tensor_withSub_step_inr _ _ _ _ hZ,
      stepFuel_onSnd]
    simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    rfl

end MultiHybrid

/-! ## Simulators and squares -/

namespace Simulator

variable {σ σ' E O E' O' EG OG EG' OG' : Type} {V : PubView E O} {W : PubView EG OG}
  {V' : PubView E' O'} {W' : PubView EG' OG'}

/-- The tensor of two opaque multi-call simulators, as a simulator for the sums of the
views. -/
noncomputable def tensor (π : MultiHybrid σ E O EG OG) (π' : MultiHybrid σ' E' O' EG' OG')
    (h : π.Opaque V W) (h' : π'.Opaque V' W') :
    Simulator (E ⊕ E') (O ⊕ O') (EG ⊕ EG') (OG ⊕ OG') (V.sum V') (W.sum W') :=
  ofMultiHybrid (π.tensor π') (h.tensor h')

end Simulator

namespace SimR

variable {σ σ' E O E' O' EG OG EG' OG' : Type} {V : PubView E O} {W : PubView EG OG}
  {V' : PubView E' O'} {W' : PubView EG' OG'}

/-- The tensor of two opaque multi-call simulators, with the environment reduction at the idle
event `idle`. -/
noncomputable def tensor (π : MultiHybrid σ E O EG OG) (π' : MultiHybrid σ' E' O' EG' OG')
    (h : π.Opaque V W) (h' : π'.Opaque V' W') (idle : EG ⊕ EG') :
    SimR (E ⊕ E') (O ⊕ O') (EG ⊕ EG') (OG ⊕ OG') (V.sum V') (W.sum W') :=
  ofMultiHybrid (π.tensor π') (h.tensor h') idle

end SimR

open MultiHybrid in
/-- **The interchange square**: top `πH` forwarding the adversary port `(EA, OA)`, bottom `πH`
forwarding `(EA', OA')`, left `(idSim EH OH).tensor S` and right `extendFwd EF OF S`, at bound
`0`, for the subroutines that answer every event on the port of the event. -/
theorem Square.interchange {σ σS EF OF EH OH EA OA EA' OA' : Type} {VF : PubView EF OF}
    {VH : PubView EH OH} {VA : PubView EA OA} {WA : PubView EA' OA'}
    (πH : MultiHybrid σ EF OF EH OH) (S : MultiHybrid σS EA OA EA' OA') (hS : S.Opaque VA WA)
    (idle : EH ⊕ EA) (idleK : EH ⊕ EA') :
    Square (Open.ofMultiHybrid (πH.tensor (idSim EA OA)) idle)
      (Open.ofMultiHybrid (πH.tensor (idSim EA' OA')) idleK)
      (Simulator.tensor (idSim EH OH) S (idSim_opaque VH) hS)
      (Simulator.ofMultiHybrid (extendFwd EF OF S) (hS.extendFwd VF))
      (fun K => K.PortTyped) (fun _ _ _ => 0) := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨KL, KR, hL, hR⟩ := hK
  exact realizes_interchange πH S K KL KR hL hR

open MultiHybrid in
/-- **Modular UC theorem.** Let `πH` be a protocol with outer port `(EF, OF)` that uses the
honest port `(EH, OH)` of its subroutine and forwards the adversary port. If `ρ` realizes `G`
behind `(idSim EH OH).tensor S` with bound `bρ`, and `πH` over `G` realizes `F` behind `SF` with
bound `bF`, then `πH` over `ρ` realizes `F` behind `extendFwd EF OF S` composed with `SF`, with
bound `bρ` at the environment reduced through the protocol plus `bF` at the environment reduced
through `extendFwd EF OF S`. The subroutine `G` answers every event on the port of the event,
and the systems involved are idle at the idle events of the reductions; `idleG` is an event of
the interface of `G`, the idle event of the bottom edge of the interchange square. -/
theorem RealizesSim.modular {σ σS τρ τG τF EF OF EH OH EA OA EA' OA' EI OI : Type}
    {VF : PubView EF OF} {VH : PubView EH OH} {VA : PubView EA OA} {WA : PubView EA' OA'}
    {VI : PubView EI OI}
    (πH : MultiHybrid σ EF OF EH OH) (S : MultiHybrid σS EA OA EA' OA') (hS : S.Opaque VA WA)
    (ρ : Sys τρ (EH ⊕ EA) (OH ⊕ OA)) (G : Sys τG (EH ⊕ EA') (OH ⊕ OA')) (hG : G.PortTyped)
    (F : Sys τF EI OI) (SF : Simulator (EF ⊕ EA') (OF ⊕ OA') EI OI (VF.sum WA) VI)
    (idle : EH ⊕ EA) (idleG : EH ⊕ EA') (idle' : EF ⊕ EA')
    (hρI : ∃ o, IdleAt ρ idle o)
    (hGI : ∃ o, IdleAt (((idSim EH OH).tensor S).withSub G) idle o)
    (hπGI : ∃ o, IdleAt ((πH.tensor (idSim EA' OA')).withSub G) idle' o)
    (hFI : ∃ o, IdleAt (SF.withSub F) idle' o)
    {bρ : (ζ : Type) → Env (Strat ζ (EH ⊕ EA) (OH ⊕ OA)) ζ → ℝ≥0∞}
    {bF : (ζ : Type) → Env (Strat ζ (EF ⊕ EA') (OF ⊕ OA')) ζ → ℝ≥0∞}
    (hρ : RealizesSim ρ G (Simulator.tensor (idSim EH OH) S (idSim_opaque VH) hS) bρ)
    (hF : RealizesSim ((πH.tensor (idSim EA' OA')).withSub G) F SF bF) :
    RealizesSim ((πH.tensor (idSim EA OA)).withSub ρ) F
      ((Simulator.ofMultiHybrid (extendFwd EF OF S) (hS.extendFwd VF)).comp SF)
      (fun ζ Z => bρ (RState (σ × Unit) ζ (EH ⊕ EA) (OF ⊕ OA))
          ((πH.tensor (idSim EA OA)).reduceEnv idle Z) +
        bF (RState (Unit × σS) ζ (EF ⊕ EA') (OF ⊕ OA))
          ((extendFwd EF OF S).reduceEnv idle' Z)) := by
  let VU : PubView Unit Unit := PubView.ofProj _root_.id _root_.id
  let SE := SimR.ofMultiHybrid (extendFwd EF OF S) (hS.extendFwd VF) idle'
  have hβ := Square.ofRealizesSim (VU := VU) hρ (fun _ => True)
  have hh := Square.hcomp (Square.interchange (VF := VF) (VH := VH) πH S hS idle idleG) hβ
    (A := fun _ => True) fun _ _ => ⟨trivial, hG, hρI, hGI⟩
  have hγ : Square ((Open.ofMultiHybrid (πH.tensor (idSim EA' OA')) idleG).comp (Open.closed G))
      (Open.closed F) (Simulator.id Unit Unit VU) SF (fun _ => True) (fun _ => bF) :=
    ⟨fun _ _ => hF⟩
  have hv := Square.vcomp (SF := SE) (A := fun _ => True) hh hγ fun _ _ =>
    ⟨trivial, trivial, hπGI, hFI⟩
  have h := hv.realizes (⟨(), fun t _ => SPComp.pure (t, ())⟩ : Sys Unit Unit Unit) trivial
  intro ζ Z
  refine le_of_le_of_eq (h ζ Z) ?_
  simp only [add_zero]
  exact congrArg₂ (fun E E' => bρ (RState (σ × Unit) ζ (EH ⊕ EA) (OF ⊕ OA)) E +
      bF (RState (Unit × σS) ζ (EF ⊕ EA') (OF ⊕ OA)) E')
    (Open.reduceEnv_ofMultiHybrid _ idle Z) (Open.reduceEnv_ofMultiHybrid _ idle' Z)

end CatCrypt.Crypto.UCTransparent
