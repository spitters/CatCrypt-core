/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Party.Lifting
public import CatCryptCore.Crypto.UCCoupling
public import CatCryptCore.Crypto.Party.UnwindingTransfer

/-!
# A relator for party programs: bisimulation and identical until bad

The relator `ProgE.relBadL V RQ B RA` is a relation lifting of party programs (an instance of
`ProgE.Lifting`, indexed by the partner program as `ProgE.viewL` is) between a program over the
local signature `Op` and a program over `Op'`. It is parameterised by the public view `V`, a
relation `RQ q q' RN` on operations (the operations `q` and `q'` are coupled with the relation
`RN` on their outcomes), a predicate `B` on residual programs of the left program (the bad
event) and a relation `RA` on returns. The two programs have the same shape up to each send; at
a send, either the left residual is bad, or the outputs are related by `V.out` and the residuals
are related; after a bad residual the programs are unconstrained. The relator `ProgE.relL` is the
relator at the bad predicate that never holds; for the coupling relation `ProgE.couplingQ` of
samples and the classical signature it relates the programs that the relational triple
`Prog.RelTriple` relates.

Soundness is the generic soundness of liftings (`ProgE.PhaseLift`): the activations of related
programs through the classical handler are coupled at equal heaps so that either the left
residual is bad, or the heaps are equal, the residuals related and the outputs related
(`ProgE.relUntilBad_stepWith`).

Two rules follow, the rules CryptHOL derives from its relator `rel_gpv` by parametricity
(`exec_gpv_oracle_bisim` and `identical_until_bad`).

* Bisimulation: related programs, and loops with related iterations, denote systems related by
  a coupling bisimulation, which realize each other at distance `0`
  (`ProgE.Lifting.toSys_realizes`, `ProgE.Lifting.loopSys_realizes`).
* Identical until bad: loops whose iterations are related until bad realize each other up to the
  probability that the run against the left loop visits a bad residual program
  (`ProgE.Lifting.loopSys_realizes_upto_bad`, `ProgE.Lifting.loopSys_adv_le_prBad`). The rule
  needs the bad flag in the state of the denotation (a predicate on residual programs), and
  invariants on the residual programs of both loops from whose states the activations do not
  fail and that the activations preserve.

The system-level rule behind the second is `UCCoupling.realizes_upto_bad_rel_inv`: the
relational up-to-bad lemma `UCCoupling.realizes_upto_bad_rel` for systems that are lossless on
invariants, through the systems `UCCoupling.onInv` that take the steps of the initial state
outside the invariant.

Search words: relator, relation lifting, coupling, bisimulation, identical until bad, bad event,
up to bad, CryptHOL, party language, lossless.

## Main definitions

* `ProgE.relBadL`, `ProgE.RelUntilBad`: the relator up to the bad event.
* `ProgE.relL`, `ProgE.RelProg`: the relator.
* `ProgE.couplingQ`: exact couplings of samples as a relation on operations.
* `ProgE.relPhase`: the lifting of the phases of an activation for the relator.
* `UCCoupling.onInv`: a system with the steps outside an invariant replaced.

## Main results

* `ProgE.relUntilBad_stepWith`, `ProgE.relProg_stepWith`: coupled activations.
* `ProgE.Lifting.toSys_couplingBisim`, `ProgE.Lifting.loopSys_couplingBisim`,
  `ProgE.Lifting.toSys_realizes`, `ProgE.Lifting.loopSys_realizes`: the bisimulation rule.
* `UCCoupling.realizes_upto_bad_rel_inv`: up to bad across a relation on invariants.
* `ProgE.Lifting.loopSys_realizes_upto_bad`, `ProgE.Lifting.loopSys_adv_le_prBad`: the rule of
  identical until bad.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCCoupling

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Crypto.UCTransparent
open CatCrypt.Crypto.UCConcrete
open scoped ENNReal

variable {τ υ ζ E O : Type}

/-! ## Up to bad on invariants -/

open Classical in
/-- The system `S` with the steps from the states outside `Inv` replaced by the steps from the
initial state. -/
noncomputable def onInv (S : Sys τ E O) (Inv : τ → Prop) : Sys τ E O where
  init := S.init
  step t e := if Inv t then S.step t e else S.step S.init e

/-- The steps of `onInv S Inv` from a state satisfying `Inv` are those of `S`. -/
theorem onInv_step {S : Sys τ E O} {Inv : τ → Prop} {t : τ} (ht : Inv t) (e : E) :
    (onInv S Inv).step t e = S.step t e := by
  simp [onInv, ht]

/-- The steps of `onInv S Inv` from a state outside `Inv` are the steps from the initial
state. -/
theorem onInv_step_not {S : Sys τ E O} {Inv : τ → Prop} {t : τ} (ht : ¬ Inv t) (e : E) :
    (onInv S Inv).step t e = S.step S.init e := by
  simp [onInv, ht]

/-- From a state satisfying an invariant of `S`, the runs against `onInv S Inv` and `S` are
equal. -/
theorem loop_onInv (S : Sys τ E O) (Inv : τ → Prop)
    (hpres : ∀ t e, Inv t → ∀ q, IsOutcome (S.step t e) q → Inv q.1) (bad : τ → Bool)
    (Z : Strat ζ E O) :
    ∀ (n : ℕ) (c : ζ × τ × Bool), Inv c.2.1 → loop (onInv S Inv) bad Z n c = loop S bad Z n c := by
  intro n
  induction n with
  | zero => intro c _; rfl
  | succ n ih =>
    intro c hc
    simp only [loop, onInv_step hc]
    congr 1
    funext a
    refine bind_congr_isOutcome fun p hp => ?_
    congr 1
    funext z
    exact ih _ (hpres _ _ hc p hp)

/-- For an invariant of `S` holding initially, the bad probabilities of `onInv S Inv` and `S`
are equal. -/
theorem prBad_onInv (S : Sys τ E O) (Inv : τ → Prop) (h0 : Inv S.init)
    (hpres : ∀ t e, Inv t → ∀ q, IsOutcome (S.step t e) q → Inv q.1) (bad : τ → Bool)
    (Z : Env (Strat ζ E O) ζ) : prBad (onInv S Inv) bad Z = prBad S bad Z := by
  unfold prBad run
  rw [loop_onInv S Inv hpres bad Z.input _ _ h0]
  rfl

/-- For an invariant of `S` holding initially, `S` realizes `onInv S Inv` at distance `0`. -/
theorem realizes_onInv (S : Sys τ E O) (Inv : τ → Prop) (h0 : Inv S.init)
    (hpres : ∀ t e, Inv t → ∀ q, IsOutcome (S.step t e) q → Inv q.1) :
    Realizes S (onInv S Inv) (fun _ _ => 0) := by
  refine (realizes_zero_of_coupling (R := S) (I := onInv S Inv)
    (rel := fun t u => t = u ∧ Inv t) ⟨⟨rfl, h0⟩, ?_⟩).1
  rintro t u e ⟨rfl, ht⟩
  rw [onInv_step ht]
  refine rHoare_conseq (fun _ _ => id) (fun p h q h' hh => ?_)
    (rHoare_and_isOutcome (rHoare_refl (S.step t e)))
  obtain ⟨⟨rfl, rfl⟩, hp, -⟩ := hh
  exact ⟨rfl, ⟨rfl, hpres t e ht p hp⟩, rfl⟩

/-- **Up to bad across a relation, on invariants.** Let `InvR` and `InvI` be invariants of `R`
and `I` holding initially, from whose states the steps do not fail, and assume that from related
states satisfying the invariants where the real state is good, the steps are coupled from equal
heaps so that either the new real state is bad or the heaps and outputs are equal and the new
states related. Then `R` realizes `I` with bound the probability `prBad R bad` that the run
against `R` visits a bad state. -/
theorem realizes_upto_bad_rel_inv (R : Sys τ E O) (I : Sys υ E O) (InvR : τ → Prop)
    (InvI : υ → Prop) (rel : τ → υ → Prop) (bad : τ → Bool) (hinit : rel R.init I.init)
    (hR0 : InvR R.init) (hI0 : InvI I.init)
    (hRpres : ∀ t e, InvR t → ∀ q, IsOutcome (R.step t e) q → InvR q.1)
    (hIpres : ∀ u e, InvI u → ∀ q, IsOutcome (I.step u e) q → InvI q.1)
    (hR : ∀ t e, InvR t → SPComp.NoFail (R.step t e))
    (hI : ∀ u e, InvI u → SPComp.NoFail (I.step u e))
    (hstep : ∀ t u e, InvR t → InvI u → rel t u → bad t = false →
      rHoare eqPre (R.step t e) (I.step u e)
        fun p h q h' => bad p.1 = true ∨ stepPost rel p h q h') :
    Realizes R I (fun _ Z => prBad R bad Z) := by
  have hnf : ∀ {σ : Type} (S : Sys σ E O) (Inv : σ → Prop), Inv S.init →
      (∀ t e, Inv t → SPComp.NoFail (S.step t e)) →
      ∀ t e, SPComp.NoFail ((onInv S Inv).step t e) := by
    intro σ S Inv h0 hS t e
    by_cases ht : Inv t
    · rw [onInv_step ht]
      exact hS t e ht
    · rw [onInv_step_not ht]
      exact hS _ e h0
  have h₂ := realizes_upto_bad_rel (onInv R InvR) (onInv I InvI)
    (fun t u => rel t u ∧ InvR t ∧ InvI u) bad ⟨hinit, hR0, hI0⟩ (hnf R InvR hR0 hR)
    (hnf I InvI hI0 hI) (fun t u e hr hb => by
      obtain ⟨hr, ht, hu⟩ := hr
      rw [onInv_step ht, onInv_step hu]
      refine rHoare_conseq (fun _ _ => id) (fun p h q h' hh => ?_)
        (rHoare_and_isOutcome (hstep t u e ht hu hr hb))
      obtain ⟨hh, hp, hq⟩ := hh
      exact hh.imp_right fun ⟨e₁, e₂, e₃⟩ =>
        ⟨e₁, ⟨e₂, hRpres t e ht p hp, hIpres u e hu q hq⟩, e₃⟩)
  have h := ((realizes_onInv R InvR hR0 hRpres).trans h₂).trans
    (realizes_symm (realizes_onInv I InvI hI0 hIpres))
  intro ζ Z
  have hZ := h ζ Z
  simpa [prBad_onInv R InvR hR0 hRpres] using hZ

end CatCrypt.Crypto.UCCoupling

namespace CatCrypt.Crypto.Party

open CatCrypt.Core CatCrypt.Crypto.UCTransparent CatCrypt.Relational CatCrypt.Crypto.UCCoupling

namespace ProgE

variable {Op Op' E O α α' σ σ' : Type}

/-! ## The relator -/

/-- **The relator up to the bad event `B`**, indexed by the partner program: the partner has the
same node, with returns related by `RA`, operations related by `RQ` with continuations related
at the outcomes related by the relation `RQ` names, continuations after a receive related at
events related by `V.ev`, and at a send either a bad left residual or outputs related by `V.out`
and related residuals. -/
def relBadL (V : PubView E O) (RQ : Op → Op' → (ℕ → ℕ → Prop) → Prop)
    (B : ProgE Op E O α → Prop) (RA : α → α' → Prop) :
    Lifting Op E O α (ProgE Op' E O α') where
  ret a p' := ∃ a', p' = .ret a' ∧ RA a a'
  recv _ p' C := ∃ k', p' = .recv k' ∧ ∀ e e', V.ev e e' → C e (k' e')
  send o q p' C := ∃ o' q', p' = .send o' q' ∧ (B q ∨ V.out o o' ∧ C q')
  opN q _ p' C := ∃ q' k' RN, p' = .opN q' k' ∧ RQ q q' RN ∧ ∀ n n', RN n n' → C n (k' n')
  fail p' := p' = .fail

/-- The programs related until the bad event `B`: the judgment of `relBadL`. -/
def RelUntilBad (V : PubView E O) (RQ : Op → Op' → (ℕ → ℕ → Prop) → Prop)
    (B : ProgE Op E O α → Prop) (RA : α → α' → Prop) (p : ProgE Op E O α)
    (p' : ProgE Op' E O α') : Prop :=
  (relBadL V RQ B RA).Holds p p'

/-- **The relator**: the relator up to bad at the bad event that never holds. -/
def relL (V : PubView E O) (RQ : Op → Op' → (ℕ → ℕ → Prop) → Prop) (RA : α → α' → Prop) :
    Lifting Op E O α (ProgE Op' E O α') :=
  relBadL V RQ (fun _ => False) RA

/-- The related programs: the judgment of `relL`. -/
def RelProg (V : PubView E O) (RQ : Op → Op' → (ℕ → ℕ → Prop) → Prop) (RA : α → α' → Prop)
    (p : ProgE Op E O α) (p' : ProgE Op' E O α') : Prop :=
  (relL V RQ RA).Holds p p'

/-- Exact couplings of samples at equal heaps as a relation on operations: `q` and `q'` are
coupled from equal heaps into equal heaps and outcomes related by `RN`. -/
def couplingQ (q q' : SPComp ℕ) (RN : ℕ → ℕ → Prop) : Prop :=
  rHoare eqPre q q' fun n h n' h' => h = h' ∧ RN n n'

/-! ## Soundness for activations -/

/-- The postcondition of coupled activations up to bad: the left residual is bad, or the heaps
are equal, the residuals related until bad and the outputs related by `V.out`. -/
def relPost (V : PubView E O) (RQ : SPComp ℕ → SPComp ℕ → (ℕ → ℕ → Prop) → Prop)
    (B : Prog E O α → Prop) (RA : α → α' → Prop) : RPost (Prog E O α × O) (Prog E O α' × O) :=
  fun r h r' h' => B r.1 ∨ (h = h' ∧ RelUntilBad V RQ B RA r.1 r'.1 ∧ V.out r.2 r'.2)

/-- The lifting of the phases of activations on related events `e`, `e'` for the relator up to
bad: the phase computation is coupled at equal heaps with the phase computation of the partner
program with the postcondition `relPost`. -/
def relPhase (V : PubView E O) (RQ : SPComp ℕ → SPComp ℕ → (ℕ → ℕ → Prop) → Prop)
    (B : Prog E O α → Prop) (RA : α → α' → Prop)
    (hQ : ∀ q q' RN, RQ q q' RN → couplingQ q q' RN)
    {restart : α → E → SPComp (Prog E O α × O)} {restart' : α' → E → SPComp (Prog E O α' × O)}
    {e e' : E} (he : V.ev e e')
    (hr : ∀ a a', RA a a' → rHoare eqPre (restart a e) (restart' a' e') (relPost V RQ B RA)) :
    PhaseLift Prog.handler (relBadL V RQ B RA) e (fun o q => Prog.handler.pure (q, o))
      (fun a => restart a e) fun _ => Prog.handler.fail where
  emit p' c := rHoare eqPre c
    (Prog.emitK (fun o r => SPComp.pure (r, o)) (fun _ => SPComp.fail) p') (relPost V RQ B RA)
  await p' c := rHoare eqPre c (Prog.stepWith restart' p' e') (relPost V RQ B RA)
  emit_ret _ _ h := by
    obtain ⟨_, rfl, _⟩ := h
    exact rHoare_fail
  emit_recv _ _ h := by
    obtain ⟨_, rfl, _⟩ := h
    exact rHoare_fail
  emit_send o p _ h := by
    obtain ⟨o', q', rfl, h⟩ := h
    exact rHoare_ret fun _ _ hh => h.imp id fun h => ⟨hh, h.2, h.1⟩
  emit_opN q _ _ c h hc := by
    obtain ⟨q', k', RN, rfl, hq, h⟩ := h
    change rHoare eqPre (SPComp.bind q c) (SPComp.bind q' fun n => Prog.emitK _ _ (k' n)) _
    refine rHoare_bind (hQ q q' RN hq) fun n n' h₁ h₂ hpre => ?_
    obtain ⟨rfl, hn⟩ := hpre
    exact hc n (k' n') (h n n' hn) h₁ h₁ rfl
  emit_fail _ h := by
    subst h
    exact rHoare_fail
  await_ret a _ h := by
    obtain ⟨a', rfl, ha⟩ := h
    exact hr a a' ha
  await_recv _ _ h hk := by
    obtain ⟨k', rfl, h⟩ := h
    exact hk (k' e') (h e e' he)
  await_send _ _ _ h := by
    obtain ⟨_, _, rfl, _⟩ := h
    exact rHoare_fail
  await_opN q _ _ c h hc := by
    obtain ⟨q', k', RN, rfl, hq, h⟩ := h
    change rHoare eqPre (SPComp.bind q c)
      (SPComp.bind q' fun n => Prog.stepWith restart' (k' n) e') _
    refine rHoare_bind (hQ q q' RN hq) fun n n' h₁ h₂ hpre => ?_
    obtain ⟨rfl, hn⟩ := hpre
    exact hc n (k' n') (h n n' hn) h₁ h₁ rfl
  await_fail _ h := by
    subst h
    exact rHoare_fail

/-- **Coupled activations up to bad.** Activations with restart of programs related until bad
on related events are coupled at equal heaps so that the left residual is bad, or the heaps are
equal, the residuals related until bad and the outputs related, when the restarts on related
returns are. -/
theorem relUntilBad_stepWith {V : PubView E O}
    {RQ : SPComp ℕ → SPComp ℕ → (ℕ → ℕ → Prop) → Prop} {B : Prog E O α → Prop}
    {RA : α → α' → Prop} (hQ : ∀ q q' RN, RQ q q' RN → couplingQ q q' RN)
    {restart : α → E → SPComp (Prog E O α × O)} {restart' : α' → E → SPComp (Prog E O α' × O)}
    {e e' : E}
    (hr : ∀ a a', RA a a' → rHoare eqPre (restart a e) (restart' a' e') (relPost V RQ B RA))
    {p : Prog E O α} {p' : Prog E O α'} (h : RelUntilBad V RQ B RA p p') (he : V.ev e e') :
    rHoare eqPre (Prog.stepWith restart p e) (Prog.stepWith restart' p' e')
      (relPost V RQ B RA) :=
  (relPhase V RQ B RA hQ he hr).stepWith_sound p p' h

/-- **Coupled activations.** Activations with restart of related programs on related events are
coupled at equal heaps into related residuals and related outputs, when the restarts on related
returns are. -/
theorem relProg_stepWith {V : PubView E O}
    {RQ : SPComp ℕ → SPComp ℕ → (ℕ → ℕ → Prop) → Prop} {RA : α → α' → Prop}
    (hQ : ∀ q q' RN, RQ q q' RN → couplingQ q q' RN)
    {restart : α → E → SPComp (Prog E O α × O)} {restart' : α' → E → SPComp (Prog E O α' × O)}
    {e e' : E}
    (hr : ∀ a a', RA a a' → rHoare eqPre (restart a e) (restart' a' e')
      (fun r h r' h' => h = h' ∧ RelProg V RQ RA r.1 r'.1 ∧ V.out r.2 r'.2))
    {p : Prog E O α} {p' : Prog E O α'} (h : RelProg V RQ RA p p') (he : V.ev e e') :
    rHoare eqPre (Prog.stepWith restart p e) (Prog.stepWith restart' p' e')
      (fun r h r' h' => h = h' ∧ RelProg V RQ RA r.1 r'.1 ∧ V.out r.2 r'.2) :=
  rHoare_conseq (fun _ _ => id) (fun _ _ _ _ hh => hh.resolve_left id)
    (relUntilBad_stepWith (B := fun _ => False) hQ
      (fun a a' ha => rHoare_conseq (fun _ _ => id) (fun _ _ _ _ hh => Or.inr hh) (hr a a' ha))
      h he)

/-! ## The bisimulation rule -/

/-- **Bisimulation of programs.** For the equality view, the relator on residual programs is a
coupling bisimulation of the denotations. -/
theorem Lifting.toSys_couplingBisim {RQ : SPComp ℕ → SPComp ℕ → (ℕ → ℕ → Prop) → Prop}
    (hQ : ∀ q q' RN, RQ q q' RN → couplingQ q q' RN) {RA : α → α' → Prop} {p : Prog E O α}
    {p' : Prog E O α'} (h : RelProg PubView.eqView RQ RA p p') :
    CouplingBisim (Prog.toSys p) (Prog.toSys p') (RelProg PubView.eqView RQ RA) where
  init := h
  step _ _ _ ht := relProg_stepWith hQ (restart := fun _ _ => SPComp.fail)
    (restart' := fun _ _ => SPComp.fail) (fun _ _ _ => rHoare_fail) ht rfl

/-- **Bisimulation of loops.** For the equality view, a relation `RS` on loop states that holds
initially and is the return relation of the relator on the iterations from related states gives
a coupling bisimulation of the loops. -/
theorem Lifting.loopSys_couplingBisim {RQ : SPComp ℕ → SPComp ℕ → (ℕ → ℕ → Prop) → Prop}
    (hQ : ∀ q q' RN, RQ q q' RN → couplingQ q q' RN) {RS : σ → σ' → Prop}
    (body : σ → Prog E O σ) (body' : σ' → Prog E O σ') {s₀ : σ} {s₀' : σ'} (h₀ : RS s₀ s₀')
    (hb : ∀ s s', RS s s' → RelProg PubView.eqView RQ RS (body s) (body' s')) :
    CouplingBisim (Prog.loopSys body s₀) (Prog.loopSys body' s₀')
      (RelProg PubView.eqView RQ RS) where
  init := ⟨s₀', rfl, h₀⟩
  step _ _ _ ht := relProg_stepWith hQ (fun s s' hs => relProg_stepWith hQ
    (restart := fun _ _ => SPComp.fail) (restart' := fun _ _ => SPComp.fail)
    (fun _ _ _ => rHoare_fail) (hb s s' hs) rfl) ht rfl

/-- **The bisimulation rule for programs.** Related programs denote systems that realize each
other at distance `0`. -/
theorem Lifting.toSys_realizes {RQ : SPComp ℕ → SPComp ℕ → (ℕ → ℕ → Prop) → Prop}
    (hQ : ∀ q q' RN, RQ q q' RN → couplingQ q q' RN) {RA : α → α' → Prop} {p : Prog E O α}
    {p' : Prog E O α'} (h : RelProg PubView.eqView RQ RA p p') :
    Realizes (Prog.toSys p) (Prog.toSys p') (fun _ _ => 0) ∧
      Realizes (Prog.toSys p') (Prog.toSys p) (fun _ _ => 0) :=
  realizes_zero_of_coupling (Lifting.toSys_couplingBisim hQ h)

/-- **The bisimulation rule for loops.** Loops with iterations related from related states
denote systems that realize each other at distance `0`. -/
theorem Lifting.loopSys_realizes {RQ : SPComp ℕ → SPComp ℕ → (ℕ → ℕ → Prop) → Prop}
    (hQ : ∀ q q' RN, RQ q q' RN → couplingQ q q' RN) {RS : σ → σ' → Prop}
    (body : σ → Prog E O σ) (body' : σ' → Prog E O σ') {s₀ : σ} {s₀' : σ'} (h₀ : RS s₀ s₀')
    (hb : ∀ s s', RS s s' → RelProg PubView.eqView RQ RS (body s) (body' s')) :
    Realizes (Prog.loopSys body s₀) (Prog.loopSys body' s₀') (fun _ _ => 0) ∧
      Realizes (Prog.loopSys body' s₀') (Prog.loopSys body s₀) (fun _ _ => 0) :=
  realizes_zero_of_coupling (Lifting.loopSys_couplingBisim hQ body body' h₀ hb)

/-! ## The rule of identical until bad -/

/-- **Identical until bad for loops.** Let the iterations of two loops from states related by
`RS` be related until the bad event `bad` on residual programs of the left loop, for the
equality view, and let `InvR` and `InvI` be invariants on the residual programs of the left and
right loop that hold initially, are preserved by the activations, and from which the activations
do not fail. Then the left loop realizes the right loop with bound the probability that the run
against the left loop visits a bad residual program. -/
theorem Lifting.loopSys_realizes_upto_bad
    {RQ : SPComp ℕ → SPComp ℕ → (ℕ → ℕ → Prop) → Prop}
    (hQ : ∀ q q' RN, RQ q q' RN → couplingQ q q' RN) {RS : σ → σ' → Prop}
    (body : σ → Prog E O σ) (body' : σ' → Prog E O σ') {s₀ : σ} {s₀' : σ'} (h₀ : RS s₀ s₀')
    (bad : Prog E O σ → Bool)
    (hb : ∀ s s', RS s s' →
      RelUntilBad PubView.eqView RQ (fun p => bad p = true) RS (body s) (body' s'))
    (InvR : Prog E O σ → Prop) (InvI : Prog E O σ' → Prop) (hR0 : InvR (.ret s₀))
    (hI0 : InvI (.ret s₀'))
    (hRpres : ∀ t e, InvR t → ∀ q, IsOutcome ((Prog.loopSys body s₀).step t e) q → InvR q.1)
    (hIpres : ∀ u e, InvI u → ∀ q, IsOutcome ((Prog.loopSys body' s₀').step u e) q → InvI q.1)
    (hR : ∀ t e, InvR t → SPComp.NoFail ((Prog.loopSys body s₀).step t e))
    (hI : ∀ u e, InvI u → SPComp.NoFail ((Prog.loopSys body' s₀').step u e)) :
    Realizes (Prog.loopSys body s₀) (Prog.loopSys body' s₀')
      (fun _ Z => prBad (Prog.loopSys body s₀) bad Z) :=
  realizes_upto_bad_rel_inv _ _ InvR InvI
    (RelUntilBad PubView.eqView RQ (fun p => bad p = true) RS) bad ⟨s₀', rfl, h₀⟩ hR0 hI0
    hRpres hIpres hR hI fun _ _ _ _ _ ht _ =>
      relUntilBad_stepWith hQ (fun s s' hs => relUntilBad_stepWith hQ
        (restart := fun _ _ => SPComp.fail) (restart' := fun _ _ => SPComp.fail)
        (fun _ _ _ => rHoare_fail) (hb s s' hs) rfl) ht rfl

/-- **Identical until bad for loops, as an advantage bound.** Under the hypotheses of
`Lifting.loopSys_realizes_upto_bad`, the advantage of every environment between the two loops
is at most the probability that its run against the left loop visits a bad residual program. -/
theorem Lifting.loopSys_adv_le_prBad
    {RQ : SPComp ℕ → SPComp ℕ → (ℕ → ℕ → Prop) → Prop}
    (hQ : ∀ q q' RN, RQ q q' RN → couplingQ q q' RN) {RS : σ → σ' → Prop}
    (body : σ → Prog E O σ) (body' : σ' → Prog E O σ') {s₀ : σ} {s₀' : σ'} (h₀ : RS s₀ s₀')
    (bad : Prog E O σ → Bool)
    (hb : ∀ s s', RS s s' →
      RelUntilBad PubView.eqView RQ (fun p => bad p = true) RS (body s) (body' s'))
    (InvR : Prog E O σ → Prop) (InvI : Prog E O σ' → Prop) (hR0 : InvR (.ret s₀))
    (hI0 : InvI (.ret s₀'))
    (hRpres : ∀ t e, InvR t → ∀ q, IsOutcome ((Prog.loopSys body s₀).step t e) q → InvR q.1)
    (hIpres : ∀ u e, InvI u → ∀ q, IsOutcome ((Prog.loopSys body' s₀').step u e) q → InvI q.1)
    (hR : ∀ t e, InvR t → SPComp.NoFail ((Prog.loopSys body s₀).step t e))
    (hI : ∀ u e, InvI u → SPComp.NoFail ((Prog.loopSys body' s₀').step u e)) {ζ : Type}
    (Z : UCConcrete.Env (Strat ζ E O) ζ) :
    adv (Prog.loopSys body s₀) (Prog.loopSys body' s₀') Z ≤ prBad (Prog.loopSys body s₀) bad Z :=
  Lifting.loopSys_realizes_upto_bad hQ body body' h₀ bad hb InvR InvI hR0 hI0 hRpres hIpres hR hI
    ζ Z

end ProgE

end CatCrypt.Crypto.Party
