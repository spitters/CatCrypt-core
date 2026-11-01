/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Party.Derived
public import CatCryptCore.Crypto.UCCoupling
public import CatCryptCore.Crypto.UCLoopbackObservationBridge

/-!
# A relational program logic for party programs

The relational triple `Party.Prog.RelTriple V RA p p'` relates two party programs
`p : Prog E O α` and `p' : Prog E O β` of the party language under a port coupling, the public
view `V : PubView E O`: the programs have the same shape of receives and sends, their outputs are
related by `V.out`, after a `recv` they continue at events related by `V.ev` with related
programs, their samples are coupled by an exact coupling of the sampled codes (the relational
Hoare logic `rHoare` at equal heaps), and they return values related by `RA`. The rules are the
constructors (`ret`, `recv`, `send`, `sample` for `sampleN`, `fail`), the bind rule
`RelTriple.bind`, the sampling rule `RelTriple.sampleC` on countable types, and the loop rule
`Prog.loopSys_couplingBisim`: an invariant `Inv` on the pair of loop states, holding initially and
preserved by each iteration as the return relation of the triple.

Soundness. The activations of related programs on related events are coupled into related
residual programs and related outputs (`Prog.RelTriple.stepWith_rHoare`). For the equality view
`PubView.eqView` the relation `RelTriple eqView RA` on residual programs is a coupling
bisimulation of the denotations (`Prog.toSys_couplingBisim`, `Prog.loopSys_couplingBisim`).

A coupling bisimulation gives step equivalence (`UCCoupling.CouplingBisim.stepEq`): the
probabilistic bisimulation quotient of Larsen and Skou. The states of both systems are glued
along the relation in the quotient `UCCoupling.BisimQuot` of the sum of the state spaces; an exact
coupling of two steps pushes forward to equal sub-distributions on the quotient, so the quotient
map on either side is a step map. Step-equivalent systems are equal open systems of
`loopOpenTheory`, so related programs give emulating systems in every context
(`Prog.RelTriple.emulatesΩ`, `Prog.RelTriple.emulatesObs`), and emulation of related programs is
closed under parallel composition and wiring through the laws `EmulatesΩ.par_compose` and
`EmulatesΩ.wire_compose`.

The example is a one-time-pad channel over a finite additive group: the party that receives a
message `m` and emits `m + k` for a fresh uniform key `k` emulates the ideal channel that emits a
fresh uniform ciphertext (`OTPProg.otp_emulatesΩ`), by the coupling `k ↦ m + k` of the samples.

Search words: relational program logic, party language, coupling, emulation, probabilistic
bisimulation, relational Hoare logic.

## Main definitions

* `UCCoupling.BisimQuot`, `UCCoupling.CouplingBisim.quotSys`: the bisimulation quotient of two
  systems related by a coupling bisimulation.
* `Party.Prog.RelTriple`: relational triples over party programs.
* `Party.OTPProg.otpReal`, `Party.OTPProg.otpIdeal`: the one-time-pad channel and its ideal
  functionality as loop bodies.

## Main results

* `UCCoupling.CouplingBisim.stepEq`, `UCCoupling.CouplingBisim.sysObj_eq`,
  `UCCoupling.CouplingBisim.emulatesΩ`: a coupling bisimulation gives step equivalence and
  emulation.
* `Party.Prog.RelTriple.bind`, `Party.Prog.RelTriple.sampleC`: the bind and sampling rules.
* `Party.Prog.RelTriple.stepWith_rHoare`: activations of related programs are coupled.
* `Party.Prog.toSys_couplingBisim`, `Party.Prog.loopSys_couplingBisim`: soundness for the
  equality view.
* `Party.Prog.RelTriple.emulatesΩ`, `Party.Prog.RelTriple.emulatesObs`,
  `Party.Prog.loopSys_emulatesΩ`: related programs give emulating systems.
* `Party.Prog.RelTriple.emulatesΩ_par`, `Party.Prog.RelTriple.emulatesΩ_wire`: closure under
  parallel composition and wiring.
* `Party.OTPProg.otp_emulatesΩ`: the one-time-pad channel emulates its ideal functionality.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCCoupling

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Crypto.UCTransparent
open CatCrypt.Crypto.UCLoopbackObservation CatCrypt.Crypto.UCLoopbackOpenTheory

variable {τ υ E O : Type}

/-! ## The bisimulation quotient -/

/-- The relation on the sum of two state spaces that links a state of the left system to the
states of the right system it is related to. -/
def sumRel (rel : τ → υ → Prop) : τ ⊕ υ → τ ⊕ υ → Prop
  | .inl t, .inr u => rel t u
  | _, _ => False

/-- The bisimulation quotient of the sum of two state spaces: the states glued along `rel`. -/
abbrev BisimQuot (rel : τ → υ → Prop) : Type :=
  Quotient (Relation.EqvGen.setoid (sumRel rel))

/-- The step of either system, with the new state sent to the bisimulation quotient. -/
noncomputable def sumStep (R : Sys τ E O) (I : Sys υ E O) (rel : τ → υ → Prop) :
    τ ⊕ υ → E → SPComp (BisimQuot rel × O)
  | .inl t, e => SPComp.map (fun p => (⟦.inl p.1⟧, p.2)) (R.step t e)
  | .inr u, e => SPComp.map (fun p => (⟦.inr p.1⟧, p.2)) (I.step u e)

/-- An exact coupling of two steps pushes forward to equal computations on the bisimulation
quotient. -/
theorem CouplingBisim.sumStep_rel {R : Sys τ E O} {I : Sys υ E O} {rel : τ → υ → Prop}
    (h : CouplingBisim R I rel) {t : τ} {u : υ} (htu : rel t u) (e : E) :
    sumStep R I rel (.inl t) e = sumStep R I rel (.inr u) e := by
  funext h₀
  have hc : rHoare eqPre (sumStep R I rel (.inl t) e) (sumStep R I rel (.inr u) e) eqPost := by
    simp only [sumStep, SPComp.map]
    refine rHoare_bind (h.step t u e htu) fun a b => rHoare_ret fun h₁ h₂ hp => ?_
    obtain ⟨hh, hr, ho⟩ := hp
    exact ⟨Prod.ext (Quotient.sound (Relation.EqvGen.rel _ _ hr)) ho, hh⟩
  exact liftR_eq_implies_eq (liftR_mono (fun _ _ hp => Prod.ext hp.1 hp.2) (hc h₀ h₀ rfl))

/-- The step on the sum respects the gluing. -/
theorem CouplingBisim.sumStep_eq {R : Sys τ E O} {I : Sys υ E O} {rel : τ → υ → Prop}
    (h : CouplingBisim R I rel) {x y : τ ⊕ υ} (hxy : Relation.EqvGen (sumRel rel) x y) :
    sumStep R I rel x = sumStep R I rel y := by
  induction hxy with
  | rel x y hr =>
    match x, y, hr with
    | .inl _, .inr _, hr => exact funext (h.sumStep_rel hr)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The system on the bisimulation quotient of a coupling bisimulation. -/
noncomputable def CouplingBisim.quotSys {R : Sys τ E O} {I : Sys υ E O} {rel : τ → υ → Prop}
    (h : CouplingBisim R I rel) : Sys (BisimQuot rel) E O where
  init := ⟦.inl R.init⟧
  step := Quotient.lift (sumStep R I rel) fun _ _ hxy => h.sumStep_eq hxy

/-- The quotient map is a step map from the left system to the quotient. -/
theorem CouplingBisim.stepMap_left {R : Sys τ E O} {I : Sys υ E O} {rel : τ → υ → Prop}
    (h : CouplingBisim R I rel) :
    Sys.StepMapOn R h.quotSys (fun _ => True) fun t => ⟦.inl t⟧ where
  init_inv := trivial
  init_map := rfl
  pres _ _ _ _ _ := trivial
  step _ _ _ := rfl

/-- The quotient map is a step map from the right system to the quotient. -/
theorem CouplingBisim.stepMap_right {R : Sys τ E O} {I : Sys υ E O} {rel : τ → υ → Prop}
    (h : CouplingBisim R I rel) :
    Sys.StepMapOn I h.quotSys (fun _ => True) fun u => ⟦.inr u⟧ where
  init_inv := trivial
  init_map := Quotient.sound (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ h.init))
  pres _ _ _ _ _ := trivial
  step _ _ _ := rfl

/-- **A coupling bisimulation gives step equivalence.** -/
theorem CouplingBisim.stepEq {R : Sys τ E O} {I : Sys υ E O} {rel : τ → υ → Prop}
    (h : CouplingBisim R I rel) : Sys.StepEq ⟨τ, R⟩ ⟨υ, I⟩ :=
  Relation.EqvGen.trans _ _ _ h.stepMap_left.stepEq
    (Relation.EqvGen.symm _ _ h.stepMap_right.stepEq)

/-- Systems related by a coupling bisimulation are equal open systems. -/
theorem CouplingBisim.sysObj_eq {R : Sys τ E O} {I : Sys υ E O} {rel : τ → υ → Prop}
    (h : CouplingBisim R I rel) : sysObj R = sysObj I := by
  simp only [sysObj]
  congr 1
  exact Quotient.sound (Relation.EqvGen.trans _ _ _ (h.stepMap_left.mapPorts _ _).stepEq
    (Relation.EqvGen.symm _ _ (h.stepMap_right.mapPorts _ _).stepEq))

/-- **A coupling bisimulation gives emulation.** -/
theorem CouplingBisim.emulatesΩ {R : Sys τ E O} {I : Sys υ E O} {rel : τ → υ → Prop}
    (h : CouplingBisim R I rel) : EmulatesΩ (sysObj R) (sysObj I) :=
  h.sysObj_eq ▸ EmulatesΩ.refl _

end CatCrypt.Crypto.UCCoupling

namespace CatCrypt.Crypto.Party

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Crypto.UCTransparent
open CatCrypt.Crypto.UCCoupling CatCrypt.Crypto.UCLoopbackObservation
open CatCrypt.Crypto.UCLoopbackOpenTheory CatCrypt.Crypto.OpenTheoryObs

namespace Prog

variable {E O α β γ δ σ σ' : Type}

/-! ## Relational triples -/

/-- **Relational triples over party programs.** `RelTriple V RA p p'`: the programs `p` and `p'`
have the same shape of receives and sends, emit outputs related by `V.out`, continue after a
`recv` at events related by `V.ev` with related programs, sample codes coupled exactly at equal
heaps by a relation `Φ` and continue at `Φ`-related codes with related programs, and return
values related by `RA`. -/
inductive RelTriple (V : PubView E O) (RA : α → β → Prop) : Prog E O α → Prog E O β → Prop where
  /-- Related returns. -/
  | ret {a : α} {b : β} (h : RA a b) : RelTriple V RA (.ret a) (.ret b)
  /-- Receives with related continuations at related events. -/
  | recv {k : E → Prog E O α} {k' : E → Prog E O β}
      (h : ∀ e e', V.ev e e' → RelTriple V RA (k e) (k' e')) :
      RelTriple V RA (.recv k) (.recv k')
  /-- Sends of related outputs with related continuations. -/
  | send {o o' : O} {p : Prog E O α} {p' : Prog E O β} (ho : V.out o o')
      (hp : RelTriple V RA p p') : RelTriple V RA (.send o p) (.send o' p')
  /-- Samples coupled by `Φ` with related continuations at `Φ`-related codes. -/
  | sample {μ μ' : SPComp ℕ} {k : ℕ → Prog E O α} {k' : ℕ → Prog E O β} (Φ : ℕ → ℕ → Prop)
      (hμ : rHoare eqPre μ μ' fun n h n' h' => h = h' ∧ Φ n n')
      (hk : ∀ n n', Φ n n' → RelTriple V RA (k n) (k' n')) :
      RelTriple V RA (.opN μ k) (.opN μ' k')
  /-- Failures. -/
  | fail : RelTriple V RA .fail .fail

/-- **The bind rule.** -/
theorem RelTriple.bind {V : PubView E O} {RA : α → β → Prop} {RB : γ → δ → Prop}
    {p : Prog E O α} {p' : Prog E O β} {f : α → Prog E O γ} {f' : β → Prog E O δ}
    (hp : RelTriple V RA p p') (hf : ∀ a b, RA a b → RelTriple V RB (f a) (f' b)) :
    RelTriple V RB (ProgE.bind p f) (ProgE.bind p' f') := by
  induction hp with
  | ret h => exact hf _ _ h
  | recv _ ih => exact RelTriple.recv ih
  | send ho _ ih => exact RelTriple.send ho ih
  | sample Φ hμ _ ih => exact RelTriple.sample Φ hμ ih
  | fail => exact RelTriple.fail

/-- The consequence rule on the return relation. -/
theorem RelTriple.mono {V : PubView E O} {RA RA' : α → β → Prop} {p : Prog E O α}
    {p' : Prog E O β} (hp : RelTriple V RA p p') (h : ∀ a b, RA a b → RA' a b) :
    RelTriple V RA' p p' := by
  simpa only [ProgE.bind_ret] using hp.bind (f := ProgE.ret) (f' := ProgE.ret)
    fun a b hab => RelTriple.ret (h a b hab)

/-- **The sampling rule** on countable types: samples coupled exactly at equal heaps by `Φ`, with
related continuations at `Φ`-related outcomes. -/
theorem RelTriple.sampleC {V : PubView E O} {RA : α → β → Prop} {ρ ρ' : Type} [Countable ρ]
    [Countable ρ'] {μ : SPComp ρ} {μ' : SPComp ρ'} {k : ρ → Prog E O α} {k' : ρ' → Prog E O β}
    (Φ : ρ → ρ' → Prop) (hμ : rHoare eqPre μ μ' fun b h b' h' => h = h' ∧ Φ b b')
    (hk : ∀ b b', Φ b b' → RelTriple V RA (k b) (k' b')) :
    RelTriple V RA (Prog.sample μ k) (Prog.sample μ' k') := by
  let _ := Encodable.ofCountable ρ
  let _ := Encodable.ofCountable ρ'
  refine RelTriple.sample (fun n n' => ∃ b b', Encodable.encode b = n ∧
    Encodable.encode b' = n' ∧ Φ b b') ?_ ?_
  · refine rHoare_bind hμ fun b b' => rHoare_ret fun h₁ h₂ hp => ?_
    exact ⟨hp.1, b, b', rfl, rfl, hp.2⟩
  · rintro _ _ ⟨b, b', rfl, rfl, hb⟩
    simp only [Encodable.encodek]
    exact hk b b' hb

/-- The receive operation is related to itself on related events. -/
theorem RelTriple.recvE {V : PubView E O} : RelTriple V V.ev recvE recvE :=
  RelTriple.recv fun _ _ h => RelTriple.ret h

/-- Sends of related outputs are related. -/
theorem RelTriple.sendE {V : PubView E O} {o o' : O} (ho : V.out o o') :
    RelTriple V (fun _ _ => True) (sendE o) (sendE o') :=
  RelTriple.send ho (RelTriple.ret trivial)

/-! ## Soundness: coupled activations -/

/-- The emit phases of related programs are coupled at equal heaps into related residuals and
related outputs. -/
theorem RelTriple.emitK_rHoare {V : PubView E O} {RA : α → β → Prop} {p : Prog E O α}
    {p' : Prog E O β} (h : RelTriple V RA p p') :
    rHoare eqPre (emitK (fun o r => SPComp.pure (r, o)) (fun _ => SPComp.fail) p)
      (emitK (fun o r => SPComp.pure (r, o)) (fun _ => SPComp.fail) p')
      (fun r h r' h' => h = h' ∧ RelTriple V RA r.1 r'.1 ∧ V.out r.2 r'.2) := by
  induction h with
  | ret _ => exact rHoare_fail
  | recv _ _ => exact rHoare_fail
  | send ho hp _ => exact rHoare_ret fun _ _ hh => ⟨hh, hp, ho⟩
  | sample Φ hμ _ ih =>
    rw [emitK_sampleN, emitK_sampleN]
    refine rHoare_bind hμ fun n n' h₁ h₂ hpre => ?_
    obtain ⟨rfl, hΦ⟩ := hpre
    exact ih n n' hΦ h₁ h₁ rfl
  | fail => exact rHoare_fail

/-- **Activations of related programs** on related events are coupled at equal heaps into
related residuals and related outputs, when the restarts on related returns are. -/
theorem RelTriple.stepWith_rHoare {V : PubView E O} {RA : α → β → Prop}
    {restart : α → E → SPComp (Prog E O α × O)} {restart' : β → E → SPComp (Prog E O β × O)}
    {e e' : E}
    (hr : ∀ a b, RA a b → rHoare eqPre (restart a e) (restart' b e')
      (fun r h r' h' => h = h' ∧ RelTriple V RA r.1 r'.1 ∧ V.out r.2 r'.2))
    {p : Prog E O α} {p' : Prog E O β} (h : RelTriple V RA p p') (he : V.ev e e') :
    rHoare eqPre (stepWith restart p e) (stepWith restart' p' e')
      (fun r h r' h' => h = h' ∧ RelTriple V RA r.1 r'.1 ∧ V.out r.2 r'.2) := by
  induction h with
  | ret ha => exact hr _ _ ha
  | recv hk _ => exact RelTriple.emitK_rHoare (hk e e' he)
  | send _ _ _ => exact rHoare_fail
  | sample Φ hμ _ ih =>
    rw [stepWith_def, stepWith_def, awaitK_sampleN, awaitK_sampleN]
    refine rHoare_bind hμ fun n n' h₁ h₂ hpre => ?_
    obtain ⟨rfl, hΦ⟩ := hpre
    exact ih n n' hΦ h₁ h₁ rfl
  | fail => exact rHoare_fail

/-- Activations of related programs on related events, for programs that halt on return. -/
theorem RelTriple.act_rHoare {V : PubView E O} {RA : α → β → Prop} {p : Prog E O α}
    {p' : Prog E O β} (h : RelTriple V RA p p') {e e' : E} (he : V.ev e e') :
    rHoare eqPre (act p e) (act p' e')
      (fun r h r' h' => h = h' ∧ RelTriple V RA r.1 r'.1 ∧ V.out r.2 r'.2) :=
  RelTriple.stepWith_rHoare (fun _ _ _ => rHoare_fail) h he

/-! ## Soundness: emulation -/

/-- **Soundness for programs.** For the equality view, the relational triple on residual
programs is a coupling bisimulation of the denotations. -/
theorem toSys_couplingBisim {RA : α → β → Prop} {p : Prog E O α} {p' : Prog E O β}
    (h : RelTriple PubView.eqView RA p p') :
    CouplingBisim (toSys p) (toSys p') (RelTriple PubView.eqView RA) where
  init := h
  step _ _ _ htu := RelTriple.act_rHoare htu rfl

/-- **Soundness for loops (the loop rule).** An invariant `Inv` on the pair of loop states that
holds initially and is the return relation of the triples of the iterations from related
states gives a coupling bisimulation of the loops. -/
theorem loopSys_couplingBisim {Inv : σ → σ' → Prop} (body : σ → Prog E O σ)
    (body' : σ' → Prog E O σ') {s₀ : σ} {s₀' : σ'} (h₀ : Inv s₀ s₀')
    (hb : ∀ s s', Inv s s' → RelTriple PubView.eqView Inv (body s) (body' s')) :
    CouplingBisim (loopSys body s₀) (loopSys body' s₀') (RelTriple PubView.eqView Inv) where
  init := RelTriple.ret h₀
  step _ _ _ htu := RelTriple.stepWith_rHoare
    (fun s s' hs => RelTriple.act_rHoare (hb s s' hs) rfl) htu rfl

/-- **Related programs give emulating systems.** -/
theorem RelTriple.emulatesΩ {RA : α → β → Prop} {p : Prog E O α} {p' : Prog E O β}
    (h : RelTriple PubView.eqView RA p p') : EmulatesΩ (sysObj (toSys p)) (sysObj (toSys p')) :=
  (toSys_couplingBisim h).emulatesΩ

/-- Related programs give emulating systems at distance `0` for the discrete distance on the
bit observation. -/
theorem RelTriple.emulatesObs {RA : α → β → Prop} {p : Prog E O α} {p' : Prog E O β}
    (h : RelTriple PubView.eqView RA p p') :
    EmulatesObs (ObsDist.discrete _) obsBit 0 (sysObj (toSys p)) (sysObj (toSys p')) :=
  emulatesΩ_iff_emulatesObs.mp h.emulatesΩ

/-- **Loops with related iterations give emulating systems.** -/
theorem loopSys_emulatesΩ {Inv : σ → σ' → Prop} (body : σ → Prog E O σ)
    (body' : σ' → Prog E O σ') {s₀ : σ} {s₀' : σ'} (h₀ : Inv s₀ s₀')
    (hb : ∀ s s', Inv s s' → RelTriple PubView.eqView Inv (body s) (body' s')) :
    EmulatesΩ (sysObj (loopSys body s₀)) (sysObj (loopSys body' s₀')) :=
  (loopSys_couplingBisim body body' h₀ hb).emulatesΩ

/-- Related programs denote equal open systems, so they emulate each other in every context. -/
theorem RelTriple.emulatesΩ_context {Δ : Interaction.PortBoundary} {RA : α → β → Prop}
    {p : Prog E O α} {p' : Prog E O β} (h : RelTriple PubView.eqView RA p p')
    (C : loopOpenTheory.Obj (ioBoundary E O) → loopOpenTheory.Obj Δ) :
    EmulatesΩ (C (sysObj (toSys p))) (C (sysObj (toSys p'))) :=
  (toSys_couplingBisim h).sysObj_eq ▸ EmulatesΩ.refl _

/-! ## Closure under composition -/

variable {E' O' α' β' : Type}

/-- **Parallel composition.** Two pairs of related programs give emulating parallel
compositions. -/
theorem RelTriple.emulatesΩ_par {RA : α → β → Prop} {RA' : α' → β' → Prop}
    {p : Prog E O α} {p' : Prog E O β} {q : Prog E' O' α'} {q' : Prog E' O' β'}
    (hp : RelTriple PubView.eqView RA p p') (hq : RelTriple PubView.eqView RA' q q') :
    EmulatesΩ (loopOpenTheory.par (sysObj (toSys p)) (sysObj (toSys q)))
      (loopOpenTheory.par (sysObj (toSys p')) (sysObj (toSys q'))) :=
  EmulatesΩ.par_compose hp.emulatesΩ hq.emulatesΩ

/-- **Wiring.** Two pairs of related programs, placed on the boundaries of a wiring by boundary
maps `f` and `g`, give emulating wirings. -/
theorem RelTriple.emulatesΩ_wire {Δ₁ Γ Δ₂ : Interaction.PortBoundary} {RA : α → β → Prop}
    {RA' : α' → β' → Prop} {p : Prog E O α} {p' : Prog E O β} {q : Prog E' O' α'}
    {q' : Prog E' O' β'} (f : Interaction.PortBoundary.Hom (ioBoundary E O) (Δ₁.tensor Γ))
    (g : Interaction.PortBoundary.Hom (ioBoundary E' O') (Γ.swap.tensor Δ₂))
    (hp : RelTriple PubView.eqView RA p p') (hq : RelTriple PubView.eqView RA' q q') :
    EmulatesΩ (loopOpenTheory.wire (loopOpenTheory.map f (sysObj (toSys p)))
        (loopOpenTheory.map g (sysObj (toSys q))))
      (loopOpenTheory.wire (loopOpenTheory.map f (sysObj (toSys p')))
        (loopOpenTheory.map g (sysObj (toSys q')))) :=
  EmulatesΩ.wire_compose (hp.emulatesΩ.map f) (hq.emulatesΩ.map g)

end Prog

/-! ## Example: the one-time-pad channel -/

namespace OTPProg

open Prog

variable (G : Type) [AddGroup G] [Fintype G] [Nonempty G]

/-- The one-time-pad channel: receive a message `m`, sample a uniform key `k` and emit the
ciphertext `m + k`. -/
noncomputable def otpReal (_ : Unit) : Prog G G Unit :=
  ProgE.bind ProgE.recvE fun m =>
    ProgE.bind (sampleE (SPComp.sample G)) fun k => ProgE.sendE (m + k)

/-- The ideal functionality of the channel: receive a message and emit a uniform ciphertext
independent of it. -/
noncomputable def otpIdeal (_ : Unit) : Prog G G Unit :=
  ProgE.bind ProgE.recvE fun _ =>
    ProgE.bind (sampleE (SPComp.sample G)) fun c => ProgE.sendE c

/-- An iteration of the channel is related to an iteration of the ideal functionality, by the
coupling `k ↦ m + k` of the key and the ciphertext. -/
theorem otp_relTriple (s s' : Unit) :
    RelTriple PubView.eqView (fun _ _ => True) (otpReal G s) (otpIdeal G s') := by
  refine RelTriple.bind RelTriple.recvE fun m m' hm => ?_
  refine RelTriple.bind (RA := fun k c => m + k = c)
    (RelTriple.sampleC (fun k c => m + k = c) ?_ fun _ _ hkc => RelTriple.ret hkc)
    fun _ _ hkc => RelTriple.sendE hkc
  exact rHoare_mono_post (rHoare_sample_bij G G (Equiv.addLeft m))
    fun _ _ _ _ hp => ⟨hp.1, hp.2⟩

/-- **The one-time-pad channel emulates its ideal functionality.** -/
theorem otp_emulatesΩ :
    EmulatesΩ (sysObj (loopSys (otpReal G) ())) (sysObj (loopSys (otpIdeal G) ())) :=
  loopSys_emulatesΩ (Inv := fun _ _ => True) _ _ trivial fun s s' _ => otp_relTriple G s s'

end OTPProg

end CatCrypt.Crypto.Party
