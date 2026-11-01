/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Party.Derived
public import CatCryptCore.Crypto.Party.Relational
public import CatCryptCore.Crypto.Party.Compose

/-!
# Refinement of party programs by information flow, and per-event coupling rules

Refinement by an abstraction of the state. For a map `g : α → β` of return values, the
residual programs of a party program `p : Prog E O α` are sent to residual programs of `g <$> p`
by `g <$> ·`, and the activations commute with this map (`Prog.act_map`, `Prog.stepWith_map`).
The denotation `toSys p` therefore has a step map onto `toSys (g <$> p)`
(`Prog.toSys_stepMapOn_map`). For a loop of `body : σ → Prog E O σ` and an abstraction
`g : σ → σ'` of its state, an abstract body `body'` with `g <$> body s = body' (g s)` gives a step
map from the loop of `body` onto the loop of `body'` on the `g`-images of the states
(`Prog.loopSys_stepMapOn_map`), hence step equivalence, equal views and realization at distance
`0`.

Information flow. The hypothesis above holds when the iterations read their state only through
`g`: iterations from states with equal `g`-images are related by the information-flow relation
`ProgE.ViewRel PubView.eqView` of `Party/Derived.lean`, with return values related through `g`
(`ProgE.ViewRel.map_eq`). The abstract body is then the iteration from any preimage, chosen by a
section of `g` (`Prog.absBody`), and the loop refines the abstract loop on the `g`-images
(`Prog.loopSys_stepMapOn_absBody`, `Prog.loopSys_stepEq_absBody`,
`Prog.loopSys_view_eq_absBody`). This is the pattern of the hand-written refinement of the IKNP
parties onto an abstract system on the public flags and the inputs
(`IKNPWake.view_realW_eq`), stated once for programs.

Per-event coupling. A loop whose iteration receives one event and dispatches on it,
`fun s => .recv (h s)`, is coupled with another such loop when the branches at each event are
related by the relational triple `Prog.RelTriple` of `Party/Relational.lean`
(`Prog.loopSys_couplingBisim_perEvent`, `Prog.loopSys_stepEq_perEvent`,
`Prog.loopSys_emulatesΩ_perEvent`). A coupling proof is then a case analysis on the events of the
program, branch by branch: one activation of two receives at related events is coupled when the
two branches are (`Prog.RelTriple.act_recv_rHoare`), a branch that emits and returns is related
when its outputs and returned states are (`Prog.RelTriple.sendRet`), and a branch that samples
uniformly is related along a bijection of the samples (`Prog.RelTriple.sample_bij`).

Search words: party language, refinement, information flow, abstraction, coupling, step map,
per-event coupling, abstract system.

## Main definitions

* `Party.Prog.absBody`: the abstract iteration of a loop on the images of an abstraction.

## Main results

* `Party.Prog.act_map`, `Party.Prog.stepWith_map`: activations commute with mapping returns.
* `Party.Prog.toSys_stepMapOn_map`, `Party.Prog.loopSys_stepMapOn_map`: refinement by a map of
  the returns or of the loop state.
* `Party.ProgE.ViewRel.map_eq`: information flow through `g` gives equal abstract programs.
* `Party.Prog.loopSys_stepMapOn_absBody`, `Party.Prog.loopSys_stepEq_absBody`,
  `Party.Prog.loopSys_view_eq_absBody`: refinement of a loop by information flow.
* `Party.Prog.RelTriple.act_recv_rHoare`, `Party.Prog.RelTriple.sendRet`,
  `Party.Prog.RelTriple.sample_bij`: per-event rules.
* `Party.Prog.loopSys_couplingBisim_perEvent`, `Party.Prog.loopSys_stepEq_perEvent`,
  `Party.Prog.loopSys_emulatesΩ_perEvent`: coupling of event-dispatching loops branch by branch.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Party

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Crypto.UCTransparent
open CatCrypt.Crypto.UCCoupling CatCrypt.Crypto.UCLoopbackObservation
open CatCrypt.Crypto.UCLoopbackOpenTheory

namespace ProgE

variable {Op E O α β : Type}

/-- **Information flow through an abstraction.** Programs related by information flow for the
equality view, with return values related through `g`, are equal after mapping the returns by
`g`. -/
theorem ViewRel.map_eq {g : α → β} {p p' : ProgE Op E O α}
    (h : ViewRel PubView.eqView (fun a a' => g a = g a') p p') : g <$> p = g <$> p' := by
  induction h with
  | ret h => exact congrArg ProgE.ret h
  | recv _ ih =>
    simp only [ProgE.map_eq, ProgE.bind] at ih ⊢
    exact congrArg ProgE.recv (funext fun e => ih e e rfl)
  | send ho _ ih =>
    simp only [ProgE.map_eq, ProgE.bind] at ih ⊢
    rw [ih]
    exact congrArg (fun o => ProgE.send o _) ho
  | opN q _ ih =>
    simp only [ProgE.map_eq, ProgE.bind] at ih ⊢
    exact congrArg (ProgE.opN q) (funext ih)
  | fail => rfl

end ProgE

namespace Prog

variable {E O α β σ σ' : Type}

/-! ## Activations commute with mapping returns -/

/-- The emit phase of a program with returns mapped by `g` is the emit phase of the program,
with the residual mapped by `g`. -/
theorem emitK_map (g : α → β) (p : Prog E O α) :
    emitK (fun o q => SPComp.pure (q, o)) (fun _ => SPComp.fail) (g <$> p) =
      SPComp.map (fun x => (g <$> x.1, x.2))
        (emitK (fun o q => SPComp.pure (q, o)) (fun _ => SPComp.fail) p) := by
  induction p with
  | ret a => simp [ProgE.bind, SPComp.map, SPComp.fail_bind]
  | recv k _ => simp [ProgE.bind, SPComp.map, SPComp.fail_bind]
  | send o p _ => simp [ProgE.bind, SPComp.map_pure]
  | opN μ k ih => simp_all [ProgE.bind, SPComp.map, SPComp.bind_assoc]
  | fail => simp [ProgE.bind, SPComp.map, SPComp.fail_bind]

/-- **Activations commute with mapping returns**: an activation of `g <$> p` is an activation of
`p` with the residual mapped by `g`, when the restarts commute with the map. -/
theorem stepWith_map (g : α → β) {restart : α → E → SPComp (Prog E O α × O)}
    {restart' : β → E → SPComp (Prog E O β × O)}
    (hr : ∀ a e, restart' (g a) e = SPComp.map (fun x => (g <$> x.1, x.2)) (restart a e))
    (p : Prog E O α) (e : E) :
    stepWith restart' (g <$> p) e =
      SPComp.map (fun x => (g <$> x.1, x.2)) (stepWith restart p e) := by
  induction p with
  | ret a => exact hr a e
  | recv k _ => exact emitK_map g (k e)
  | send o p _ => simp [stepWith_def, ProgE.bind, SPComp.map, SPComp.fail_bind]
  | opN μ k ih => simp_all [stepWith_def, ProgE.bind, SPComp.map, SPComp.bind_assoc]
  | fail => simp [stepWith_def, ProgE.bind, SPComp.map, SPComp.fail_bind]

/-- An activation of `g <$> p` is an activation of `p` with the residual mapped by `g`. -/
theorem act_map (g : α → β) (p : Prog E O α) (e : E) :
    act (g <$> p) e = SPComp.map (fun x => (g <$> x.1, x.2)) (act p e) :=
  stepWith_map g (restart := fun _ _ => SPComp.fail) (restart' := fun _ _ => SPComp.fail)
    (fun _ _ => by simp [SPComp.map, SPComp.fail_bind]) p e

/-! ## Refinement by an abstraction -/

/-- **Refinement by a map of the returns.** Mapping the residual programs by `g <$> ·` is a step
map from the denotation of `p` onto the denotation of `g <$> p`. -/
theorem toSys_stepMapOn_map (g : α → β) (p : Prog E O α) :
    Sys.StepMapOn (toSys p) (toSys (g <$> p)) (fun _ => True) (g <$> ·) where
  init_inv := trivial
  init_map := rfl
  pres _ _ _ _ _ := trivial
  step t e _ := (act_map g t e).symm

/-- **Refinement of a loop by an abstraction of its state.** When the iteration from `s`, its
returned state mapped by `g`, is the abstract iteration from `g s`, mapping the residual
programs by `g <$> ·` is a step map from the loop of `body` onto the loop of `body'` on the
`g`-images. -/
theorem loopSys_stepMapOn_map (g : σ → σ') {body : σ → Prog E O σ} {body' : σ' → Prog E O σ'}
    (hb : ∀ s, g <$> body s = body' (g s)) (s₀ : σ) :
    Sys.StepMapOn (loopSys body s₀) (loopSys body' (g s₀)) (fun _ => True) (g <$> ·) where
  init_inv := trivial
  init_map := rfl
  pres _ _ _ _ _ := trivial
  step t e _ :=
    (stepWith_map g (fun s e => by rw [← hb s]; exact act_map g (body s) e) t e).symm

/-- The abstract iteration of a loop on the images of `g`: the iteration from the preimage
`sec x` chosen by a section `sec` of `g`, with its returned state mapped by `g`. -/
def absBody (g : σ → σ') (sec : σ' → σ) (body : σ → Prog E O σ) (x : σ') : Prog E O σ' :=
  g <$> body (sec x)

/-- An iteration that reads its state only through `g` is the abstract iteration at the image of
its state. -/
theorem map_body_eq_absBody {g : σ → σ'} {sec : σ' → σ} (hsec : ∀ x, g (sec x) = x)
    {body : σ → Prog E O σ}
    (hflow : ∀ s s', g s = g s' →
      ProgE.ViewRel PubView.eqView (fun a a' => g a = g a') (body s) (body s'))
    (s : σ) : g <$> body s = absBody g sec body (g s) :=
  ProgE.ViewRel.map_eq (hflow s (sec (g s)) (hsec (g s)).symm)

/-- **Refinement by information flow.** A loop whose iterations read their state only through
`g` (iterations from states with equal `g`-images are related by information flow, with returned
states related through `g`) refines the abstract loop on the `g`-images by the step map
`g <$> ·`. -/
theorem loopSys_stepMapOn_absBody {g : σ → σ'} {sec : σ' → σ} (hsec : ∀ x, g (sec x) = x)
    {body : σ → Prog E O σ}
    (hflow : ∀ s s', g s = g s' →
      ProgE.ViewRel PubView.eqView (fun a a' => g a = g a') (body s) (body s'))
    (s₀ : σ) :
    Sys.StepMapOn (loopSys body s₀) (loopSys (absBody g sec body) (g s₀)) (fun _ => True)
      (g <$> ·) :=
  loopSys_stepMapOn_map g (map_body_eq_absBody hsec hflow) s₀

/-- A loop that reads its state only through `g` is step-equivalent to the abstract loop on the
`g`-images. -/
theorem loopSys_stepEq_absBody {g : σ → σ'} {sec : σ' → σ} (hsec : ∀ x, g (sec x) = x)
    {body : σ → Prog E O σ}
    (hflow : ∀ s s', g s = g s' →
      ProgE.ViewRel PubView.eqView (fun a a' => g a = g a') (body s) (body s'))
    (s₀ : σ) :
    Sys.StepEq ⟨_, loopSys body s₀⟩ ⟨_, loopSys (absBody g sec body) (g s₀)⟩ :=
  (loopSys_stepMapOn_absBody hsec hflow s₀).stepEq

/-- A loop that reads its state only through `g` and the abstract loop on the `g`-images have
equal views for every environment. -/
theorem loopSys_view_eq_absBody {ζ : Type} {g : σ → σ'} {sec : σ' → σ}
    (hsec : ∀ x, g (sec x) = x) {body : σ → Prog E O σ}
    (hflow : ∀ s s', g s = g s' →
      ProgE.ViewRel PubView.eqView (fun a a' => g a = g a') (body s) (body s'))
    (s₀ : σ) (Z : Strat ζ E O) :
    view (loopSys body s₀) Z = view (loopSys (absBody g sec body) (g s₀)) Z :=
  view_eq_of_stepMap _ _ (g <$> ·) rfl
    (fun t e => (loopSys_stepMapOn_absBody hsec hflow s₀).step t e trivial) Z

/-! ## Per-event coupling -/

/-- **One activation of two receives.** On related events at which the branches are related,
the activations of the two receives are coupled into related residuals and related outputs. -/
theorem RelTriple.act_recv_rHoare {V : PubView E O} {RA : α → β → Prop}
    {k : E → Prog E O α} {k' : E → Prog E O β} {e e' : E}
    (h : RelTriple V RA (k e) (k' e')) :
    rHoare eqPre (act (.recv k) e) (act (.recv k') e')
      (fun r h r' h' => h = h' ∧ RelTriple V RA r.1 r'.1 ∧ V.out r.2 r'.2) :=
  RelTriple.emitK_rHoare h

/-- A branch that emits and returns is related when its outputs and returned values are. -/
theorem RelTriple.sendRet {V : PubView E O} {RA : α → β → Prop} {o o' : O} {a : α} {b : β}
    (ho : V.out o o') (hab : RA a b) :
    RelTriple V RA (.send o (.ret a)) (.send o' (.ret b)) :=
  RelTriple.send ho (RelTriple.ret hab)

/-- A branch that samples uniformly is related along a bijection `f` of the samples when the
continuations at `b` and `f b` are related. -/
theorem RelTriple.sample_bij {V : PubView E O} {RA : α → β → Prop} {ρ ρ' : Type} [Fintype ρ]
    [Fintype ρ'] [Nonempty ρ] [Nonempty ρ'] (f : ρ ≃ ρ') {k : ρ → Prog E O α}
    {k' : ρ' → Prog E O β} (hk : ∀ b, RelTriple V RA (k b) (k' (f b))) :
    RelTriple V RA (Prog.sample (SPComp.sample ρ) k) (Prog.sample (SPComp.sample ρ') k') :=
  RelTriple.sampleC (fun b b' => f b = b')
    (rHoare_mono_post (rHoare_sample_bij ρ ρ' f) fun _ _ _ _ hp => ⟨hp.1, hp.2⟩)
    fun b _ hb => hb ▸ hk b

/-- **Per-event coupling of loops.** Two loops whose iterations receive an event and dispatch on
it, with branches related at each event from states related by `Inv`, the returned states
related by `Inv`, are related by a coupling bisimulation. -/
theorem loopSys_couplingBisim_perEvent {Inv : σ → σ' → Prop} (h : σ → E → Prog E O σ)
    (h' : σ' → E → Prog E O σ') {s₀ : σ} {s₀' : σ'} (h₀ : Inv s₀ s₀')
    (hb : ∀ s s', Inv s s' → ∀ e, RelTriple PubView.eqView Inv (h s e) (h' s' e)) :
    CouplingBisim (loopSys (fun s => .recv (h s)) s₀) (loopSys (fun s => .recv (h' s)) s₀')
      (RelTriple PubView.eqView Inv) :=
  loopSys_couplingBisim _ _ h₀ fun s s' hs =>
    RelTriple.recv fun e e' he => by
      change e = e' at he
      subst he
      exact hb s s' hs e

/-- Event-dispatching loops with branches related at each event are step-equivalent. -/
theorem loopSys_stepEq_perEvent {Inv : σ → σ' → Prop} (h : σ → E → Prog E O σ)
    (h' : σ' → E → Prog E O σ') {s₀ : σ} {s₀' : σ'} (h₀ : Inv s₀ s₀')
    (hb : ∀ s s', Inv s s' → ∀ e, RelTriple PubView.eqView Inv (h s e) (h' s' e)) :
    Sys.StepEq ⟨_, loopSys (fun s => .recv (h s)) s₀⟩ ⟨_, loopSys (fun s => .recv (h' s)) s₀'⟩ :=
  (loopSys_couplingBisim_perEvent h h' h₀ hb).stepEq

/-- Event-dispatching loops with branches related at each event give emulating systems. -/
theorem loopSys_emulatesΩ_perEvent {Inv : σ → σ' → Prop} (h : σ → E → Prog E O σ)
    (h' : σ' → E → Prog E O σ') {s₀ : σ} {s₀' : σ'} (h₀ : Inv s₀ s₀')
    (hb : ∀ s s', Inv s s' → ∀ e, RelTriple PubView.eqView Inv (h s e) (h' s' e)) :
    EmulatesΩ (sysObj (loopSys (fun s => .recv (h s)) s₀))
      (sysObj (loopSys (fun s => .recv (h' s)) s₀')) :=
  (loopSys_couplingBisim_perEvent h h' h₀ hb).emulatesΩ

end Prog

end CatCrypt.Crypto.Party
