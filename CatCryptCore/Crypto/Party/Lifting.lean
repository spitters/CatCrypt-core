/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Party.Derived
public import CatCryptCore.Crypto.Party.LoopTimed

/-!
# Judgments on party programs as liftings of the signature

A judgment on party programs `ProgE Op E O α` is a lifting of the signature of the program
trees over an index type `G`: for each kind of node (`ret`, `recv`, `send`, `opN`, `fail`), a
condition on the node, the index and the lifted predicate of its continuations
(`ProgE.Lifting`). The judgment `ProgE.Lifting.Holds L p g` is the unique fixed point of the
lifting over the program tree, by structural recursion. The index is the unit type for a
predicate, the partner program for a relation (a relation is a predicate on the program with the
partner program as index), and the time budget for a time bound.

Soundness is one theorem for the two phases of an activation through any handler
(`ProgE.PhaseLift.emitK_sound`, `ProgE.PhaseLift.awaitK_sound`): a family of properties of the
phase computations at each index, closed under the five kinds of node, holds of the phase
computations of every program satisfying the judgment. The activation `ProgE.stepWith` is the
await phase with the output-returning send continuation (`ProgE.PhaseLift.stepWith_sound`).

The three judgments of the party language are instances.

* Port typing: `ProgE.portsL`, with `ProgE.ports_iff` to `ProgE.Ports`; the port typing of the
  denotation and of loops (`ProgE.Lifting.toSys_ports`, `ProgE.Lifting.loopSys_ports`).
* Information flow: `ProgE.viewL`, indexed by the partner program, with `ProgE.viewRel_iff` to
  `ProgE.ViewRel`; the unwinding conditions of the denotation and of loops
  (`ProgE.Lifting.toSys_unwinding`, `ProgE.Lifting.loopSys_unwinding`).
* Time bounds: `ProgE.boundL` indexed by the remaining time and `ProgE.boundSzL` by the
  remaining time and the size budget, with `ProgE.bound_iff` and `ProgE.boundSz_iff`.

Search words: party language, judgment, lifting of a signature, predicate lifting, relation
lifting, fibration, port typing, information flow, unwinding, time bound, soundness.

## Main definitions

* `ProgE.Lifting`, `ProgE.Lifting.Holds`: liftings of the signature and their judgments.
* `ProgE.PhaseLift`: a lifting of the phases of an activation through a handler.
* `ProgE.portsL`, `ProgE.viewL`, `ProgE.boundL`, `ProgE.boundSzL`: the three judgments.
* `ProgE.Ports'`, `ProgE.ViewRel'`, `ProgE.Bound'`, `ProgE.BoundSz'`,
  `ProgE.LoopBoundGraded'`: the judgments as applications of `Holds`.
* `ProgE.portsPhase`, `ProgE.viewPhase`: the liftings of the phases for port typing and
  information flow.

## Main results

* `ProgE.PhaseLift.emitK_sound`, `ProgE.PhaseLift.awaitK_sound`,
  `ProgE.PhaseLift.stepWith_sound`: soundness of a judgment for the phases of an activation.
* `ProgE.ports_iff`, `ProgE.viewRel_iff`, `ProgE.bound_iff`, `ProgE.boundSz_iff`: the instances
  are the judgments of `Derived`, `Timed` and `LoopTimed`.
* `ProgE.Bound'.stepTime_actT_le`, `ProgE.LoopBoundGraded'.timeBoundGraded_timed`: the time
  bound through `boundL` bounds the time of an activation in costed trees and of the costed
  loop simulator.
* `ProgE.ports_stepWith`, `ProgE.Lifting.toSys_ports`, `ProgE.Lifting.loopSys_ports`,
  `ProgE.viewRel_stepWith`, `ProgE.Lifting.toSys_unwinding`, `ProgE.Lifting.loopSys_unwinding`:
  the soundness theorems of port typing and information flow from the generic one.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Party

open CatCrypt.Core CatCrypt.Crypto.UCTransparent CatCrypt.Relational

namespace ProgE

variable {Op : Type} {M : Type → Type} {E O α γ G : Type}

/-! ## Liftings of the signature -/

/-- A lifting of the signature of `ProgE Op E O α` over the index type `G`: for each kind of
node, the condition on the node at an index, given the node's data, its continuations and the
lifted predicate of its continuations. -/
structure Lifting (Op E O α G : Type) where
  /-- The condition on a return. -/
  ret : α → G → Prop
  /-- The condition on a receive, given the lifted predicate of the continuation at each
  event. -/
  recv : (E → ProgE Op E O α) → G → (E → G → Prop) → Prop
  /-- The condition on a send, given the lifted predicate of the continuation. -/
  send : O → ProgE Op E O α → G → (G → Prop) → Prop
  /-- The condition on an effect operation, given the lifted predicate of the continuation at
  each outcome. -/
  opN : Op → (ℕ → ProgE Op E O α) → G → (ℕ → G → Prop) → Prop
  /-- The condition on a failure. -/
  fail : G → Prop

/-- The judgment of the lifting `L`: the fixed point of `L` over the program tree. -/
def Lifting.Holds (L : Lifting Op E O α G) : ProgE Op E O α → G → Prop
  | .ret a, g => L.ret a g
  | .recv k, g => L.recv k g fun e => L.Holds (k e)
  | .send o p, g => L.send o p g (L.Holds p)
  | .opN q k, g => L.opN q k g fun n => L.Holds (k n)
  | .fail, g => L.fail g

/-! ## Soundness for the phases of an activation -/

/-- A lifting of the phases of an activation on the event `e` through the handler `H` along the
lifting `L`, for the continuations `s` at sends, `rA` at returns in the await phase and `rE` at
returns in the emit phase: properties `emit g c` and `await g c` of phase computations at an
index, closed under the five kinds of node. -/
structure PhaseLift (H : Handler Op M) (L : Lifting Op E O α G) (e : E)
    (s : O → ProgE Op E O α → M γ) (rA rE : α → M γ) where
  /-- The property of an emit-phase computation at an index. -/
  emit : G → M γ → Prop
  /-- The property of an await-phase computation at an index. -/
  await : G → M γ → Prop
  /-- A return in the emit phase. -/
  emit_ret : ∀ a g, L.ret a g → emit g (rE a)
  /-- A receive in the emit phase fails. -/
  emit_recv : ∀ k g, L.recv k g (fun e => L.Holds (k e)) → emit g H.fail
  /-- A send in the emit phase. -/
  emit_send : ∀ o p g, L.send o p g (L.Holds p) → emit g (s o p)
  /-- An operation in the emit phase, continued by computations with the property at the
  indices of the continuations. -/
  emit_opN : ∀ q k g (c : ℕ → M γ), L.opN q k g (fun n => L.Holds (k n)) →
    (∀ n g', L.Holds (k n) g' → emit g' (c n)) → emit g (H.bind (H.run q) c)
  /-- A failure in the emit phase. -/
  emit_fail : ∀ g, L.fail g → emit g H.fail
  /-- A return in the await phase. -/
  await_ret : ∀ a g, L.ret a g → await g (rA a)
  /-- A receive in the await phase continues with the emit phase at the event `e`. -/
  await_recv : ∀ k g, L.recv k g (fun e => L.Holds (k e)) →
    (∀ g', L.Holds (k e) g' → emit g' (emitK H s rE (k e))) → await g (emitK H s rE (k e))
  /-- A send in the await phase fails. -/
  await_send : ∀ o p g, L.send o p g (L.Holds p) → await g H.fail
  /-- An operation in the await phase. -/
  await_opN : ∀ q k g (c : ℕ → M γ), L.opN q k g (fun n => L.Holds (k n)) →
    (∀ n g', L.Holds (k n) g' → await g' (c n)) → await g (H.bind (H.run q) c)
  /-- A failure in the await phase. -/
  await_fail : ∀ g, L.fail g → await g H.fail

namespace PhaseLift

variable {H : Handler Op M} {L : Lifting Op E O α G} {e : E} {s : O → ProgE Op E O α → M γ}
  {rA rE : α → M γ}

/-- **Soundness for the emit phase.** The emit phase of a program satisfying the judgment at
`g` has the emit property at `g`. -/
theorem emitK_sound (P : PhaseLift H L e s rA rE) (p : ProgE Op E O α) (g : G)
    (h : L.Holds p g) : P.emit g (emitK H s rE p) := by
  induction p generalizing g with
  | ret a => exact P.emit_ret a g h
  | recv k _ => exact P.emit_recv k g h
  | send o p _ => exact P.emit_send o p g h
  | opN q k ih => exact P.emit_opN q k g _ h fun n g' hn => ih n g' hn
  | fail => exact P.emit_fail g h

/-- **Soundness for the await phase.** The await phase of a program satisfying the judgment at
`g` has the await property at `g`. -/
theorem awaitK_sound (P : PhaseLift H L e s rA rE) (p : ProgE Op E O α) (g : G)
    (h : L.Holds p g) : P.await g (awaitK H e s rA rE p) := by
  induction p generalizing g with
  | ret a => exact P.await_ret a g h
  | recv k _ => exact P.await_recv k g h fun g' hk => P.emitK_sound (k e) g' hk
  | send o p _ => exact P.await_send o p g h
  | opN q k ih => exact P.await_opN q k g _ h fun n g' hn => ih n g' hn
  | fail => exact P.await_fail g h

end PhaseLift

/-- **Soundness for an activation.** An activation with restart of a program satisfying the
judgment at `g` has the await property at `g`. -/
theorem PhaseLift.stepWith_sound {H : Handler Op M} {L : Lifting Op E O α G} {e : E}
    {restart : α → E → M (ProgE Op E O α × O)}
    (P : PhaseLift H L e (fun o q => H.pure (q, o)) (fun a => restart a e) fun _ => H.fail)
    (p : ProgE Op E O α) (g : G) (h : L.Holds p g) : P.await g (stepWith H restart p e) :=
  P.awaitK_sound p g h

/-! ## Port typing -/

/-- The lifting of port typing: a receive accepts the events of `Pe` and fails on the others, a
send emits an output of `Po`. -/
def portsL (Pe : E → Prop) (Po : O → Prop) : Lifting Op E O α Unit where
  ret _ _ := True
  recv k _ C := ∀ e, (Pe e → C e ()) ∧ (¬ Pe e → k e = .fail)
  send o _ _ C := Po o ∧ C ()
  opN _ _ _ C := ∀ n, C n ()
  fail _ := True

/-- Port typing as the judgment of `portsL`. -/
def Ports' (Pe : E → Prop) (Po : O → Prop) (p : ProgE Op E O α) : Prop :=
  (portsL Pe Po).Holds p ()

/-- The judgment of `portsL` is port typing. -/
theorem ports_iff {Pe : E → Prop} {Po : O → Prop} (p : ProgE Op E O α) :
    Ports' Pe Po p ↔ Ports Pe Po p := by
  constructor
  · intro h
    induction p with
    | ret a => exact Ports.ret a
    | recv k ih => exact Ports.recv k (fun e he => ih e ((h e).1 he)) fun e he => (h e).2 he
    | send o p ih => exact Ports.send o p h.1 (ih h.2)
    | opN q k ih => exact Ports.opN q k fun n => ih n (h n)
    | fail => exact Ports.fail
  · intro h
    induction h with
    | ret a => trivial
    | recv k _ hrej ih => exact fun e => ⟨fun he => ih e he, hrej e⟩
    | send o p ho _ ih => exact ⟨ho, ih⟩
    | opN q k _ ih => exact ih
    | fail => trivial

/-! ## Information flow -/

/-- The lifting of information flow for the view `V`, indexed by the partner program: the
partner has the same node, with returns related by `RA`, outputs related by `V.out`, the same
operation, and continuations related at events related by `V.ev`. -/
def viewL (V : PubView E O) (RA : α → α → Prop) : Lifting Op E O α (ProgE Op E O α) where
  ret a p' := ∃ a', p' = .ret a' ∧ RA a a'
  recv _ p' C := ∃ k', p' = .recv k' ∧ ∀ e e', V.ev e e' → C e (k' e')
  send o _ p' C := ∃ o' q', p' = .send o' q' ∧ V.out o o' ∧ C q'
  opN q _ p' C := ∃ k', p' = .opN q k' ∧ ∀ n, C n (k' n)
  fail p' := p' = .fail

/-- Information flow as the judgment of `viewL`. -/
def ViewRel' (V : PubView E O) (RA : α → α → Prop) (p p' : ProgE Op E O α) : Prop :=
  (viewL V RA).Holds p p'

/-- The judgment of `viewL` is information flow. -/
theorem viewRel_iff {V : PubView E O} {RA : α → α → Prop} (p p' : ProgE Op E O α) :
    ViewRel' V RA p p' ↔ ViewRel V RA p p' := by
  constructor
  · intro h
    induction p generalizing p' with
    | ret a =>
      obtain ⟨a', rfl, h⟩ := h
      exact ViewRel.ret h
    | recv k ih =>
      obtain ⟨k', rfl, h⟩ := h
      exact ViewRel.recv fun e e' he => ih e (k' e') (h e e' he)
    | send o p ih =>
      obtain ⟨o', q', rfl, ho, h⟩ := h
      exact ViewRel.send ho (ih q' h)
    | opN q k ih =>
      obtain ⟨k', rfl, h⟩ := h
      exact ViewRel.opN q fun n => ih n (k' n) (h n)
    | fail =>
      cases (h : p' = .fail)
      exact ViewRel.fail
  · intro h
    induction h with
    | ret h => exact ⟨_, rfl, h⟩
    | recv _ ih => exact ⟨_, rfl, ih⟩
    | send ho _ ih => exact ⟨_, _, rfl, ho, ih⟩
    | opN q _ ih => exact ⟨_, rfl, ih⟩
    | fail => exact (rfl : (ProgE.fail : ProgE Op E O α) = .fail)

/-! ## Time bounds -/

/-- The lifting of the time bound at the weight `w` with the predicate `P` on returns, indexed
by the remaining time. -/
def boundL (w : Op → ℕ) (P : α → Prop) : Lifting Op E O α ℕ where
  ret a _ := P a
  recv _ t C := 1 ≤ t ∧ ∀ e, C e (t - 1)
  send _ _ t C := 1 ≤ t ∧ C (t - 1)
  opN q _ t C := w q ≤ t ∧ ∀ n, C n (t - w q)
  fail _ := True

/-- The time bound as the judgment of `boundL`. -/
def Bound' (w : Op → ℕ) (p : ProgE Op E O α) (t : ℕ) (P : α → Prop) : Prop :=
  (boundL w P).Holds p t

/-- The judgment of `boundL` is the time bound. -/
theorem bound_iff (w : Op → ℕ) (p : ProgE Op E O α) (t : ℕ) (P : α → Prop) :
    Bound' w p t P ↔ Bound w p t P := by
  induction p generalizing t with
  | ret a => exact Iff.rfl
  | recv k ih => exact and_congr_right fun _ => forall_congr' fun e => ih e _
  | send o p ih => exact and_congr_right fun _ => ih _
  | opN q k ih => exact and_congr_right fun _ => forall_congr' fun n => ih n _
  | fail => exact Iff.rfl

/-- The lifting of the size-graded time bound at the weight `w` with the size budget `sz`,
indexed by the remaining time and the budget of the current activation. -/
def boundSzL (w : Op → ℕ) (sz : E → ℕ) (P : α → Prop) : Lifting Op E O α (ℕ × ℕ) where
  ret a _ := P a
  recv _ x C := 1 ≤ x.1 ∧ ∀ e, C e (x.1 - 1, sz e)
  send _ _ x C := 1 ≤ x.1 ∧ C (x.1 - 1, 0)
  opN q _ x C := w q ≤ x.1 + x.2 ∧ ∀ n, C n (x.1 - (w q - x.2), x.2 - w q)
  fail _ := True

/-- The size-graded time bound as the judgment of `boundSzL`. -/
def BoundSz' (w : Op → ℕ) (sz : E → ℕ) (p : ProgE Op E O α) (t u : ℕ) (P : α → Prop) : Prop :=
  (boundSzL w sz P).Holds p (t, u)

/-- The judgment of `boundSzL` is the size-graded time bound. -/
theorem boundSz_iff (w : Op → ℕ) (sz : E → ℕ) (p : ProgE Op E O α) (t u : ℕ) (P : α → Prop) :
    BoundSz' w sz p t u P ↔ BoundSz w sz p t u P := by
  induction p generalizing t u with
  | ret a => exact Iff.rfl
  | recv k ih => exact and_congr_right fun _ => forall_congr' fun e => ih e _ _
  | send o p ih => exact and_congr_right fun _ => ih _ _
  | opN q k ih => exact and_congr_right fun _ => forall_congr' fun n => ih n _ _
  | fail => exact Iff.rfl

/-- The graded time bound of a loop, with the bound of the body the judgment of `boundL`. -/
def LoopBoundGraded' {σ : Type} (w : Op → ℕ) (body : σ → ProgE Op E O σ) (s₀ : σ)
    (Inv : ℕ → σ → Prop) (a b : ℕ) : Prop :=
  Inv 0 s₀ ∧ ∀ i s, Inv i s → Bound' w (body s) (a + b * i) (Inv (i + 1))

/-- The graded time bound of a loop through `boundL` is `LoopBoundGraded`. -/
theorem loopBoundGraded_iff {σ : Type} (w : Op → ℕ) (body : σ → ProgE Op E O σ) (s₀ : σ)
    (Inv : ℕ → σ → Prop) (a b : ℕ) :
    LoopBoundGraded' w body s₀ Inv a b ↔ LoopBoundGraded w body s₀ Inv a b := by
  simp only [LoopBoundGraded', LoopBoundGraded, bound_iff]

/-- **Time of an activation from the graded lifting.** When the judgment of `boundL` holds of a
costed program at the weight `weightT ι` with the time `t`, every activation of the program in
costed trees costs at most `t`. -/
theorem Bound'.stepTime_actT_le (ι : Op → ℕ × SPTree.Timed ℕ) {p : ProgE (Costed Op) E O α}
    {t : ℕ} {P : α → Prop} (h : Bound' (weightT ι) p t P) (e : E) :
    SPTree.Timed.stepTime (actT ι p e) ≤ t := by
  have := awaitT_time (R := fun _ => True) (D := 0) ι e (fun o q => (0, .ret (q, o)))
    (fun _ => (0, .fail)) (fun _ => (0, .fail))
    (fun _ _ _ _ _ => ⟨by simp only [SPTree.Timed.stepTime, SPTree.Timed.time_ret, le_refl],
      trivial⟩)
    (fun _ _ => ⟨by simp only [stepTime_fail, le_refl], trivial⟩)
    (fun _ _ => ⟨by simp only [stepTime_fail, le_refl], trivial⟩) p t le_rfl
    ((bound_iff _ p t P).1 h)
  exact this.1

/-- **Graded time certificate of the costed loop simulator from the graded lifting.** Under the
graded bound `a`, `b` of the costed body through `boundL`, the costed loop simulator has the
graded time bound `2 * a + b`, `2 * b` on the invariant `Prog.loopMulti.ActInv`. -/
theorem LoopBoundGraded'.timeBoundGraded_timed {σ A Q : Type} [Inhabited O]
    (ι : Op → ℕ × SPTree.Timed ℕ) {bodyT : σ → ProgE (Costed Op) (E ⊕ A) (Q ⊕ O) σ} {s₀ : σ}
    (n : ℕ) {Inv : ℕ → σ → Prop} {a b : ℕ}
    (h : LoopBoundGraded' (weightT ι) bodyT s₀ Inv a b) :
    (Prog.loopMulti.timed ι bodyT s₀ n).TimeBoundGraded (Prog.loopMulti.ActInv ι Inv a b)
      (2 * a + b) (2 * b) :=
  Prog.loopMulti.timeBoundGraded_timed ι bodyT s₀ n ((loopBoundGraded_iff _ _ _ _ _ _).1 h)

/-! ## Port typing of the denotation from the generic soundness -/

section PortsSound

variable {E O α σ : Type}

/-- The lifting of the phases of an activation on `e` for port typing: every outcome is a typed
residual with an output of `Po`, and, in the await phase, the event satisfies `Pe`. -/
def portsPhase (Pe : E → Prop) (Po : O → Prop) {restart : α → E → SPComp (Prog E O α × O)}
    (e : E) (hr : ∀ a q, IsOutcome (restart a e) q → Pe e ∧ Po q.2 ∧ Ports Pe Po q.1) :
    PhaseLift Prog.handler (portsL Pe Po) e (fun o q => Prog.handler.pure (q, o))
      (fun a => restart a e) fun _ => Prog.handler.fail where
  emit _ c := ∀ q, IsOutcome c q → Po q.2 ∧ Ports Pe Po q.1
  await _ c := ∀ q, IsOutcome c q → Pe e ∧ Po q.2 ∧ Ports Pe Po q.1
  emit_ret _ _ _ _ h := absurd h (Prog.not_isOutcome_fail _)
  emit_recv _ _ _ _ h := absurd h (Prog.not_isOutcome_fail _)
  emit_send o p _ h q hq := by
    obtain rfl := isOutcome_pure hq
    exact ⟨h.1, (ports_iff p).1 h.2⟩
  emit_opN _ _ _ _ h hc q hq := by
    obtain ⟨n, -, hn⟩ := isOutcome_bind hq
    exact hc n () (h n) q hn
  emit_fail _ _ _ h := absurd h (Prog.not_isOutcome_fail _)
  await_ret a _ _ q h := hr a q h
  await_recv k _ h hk q hq := by
    by_cases he : Pe e
    · exact ⟨he, hk () ((h e).1 he) q hq⟩
    · rw [(h e).2 he] at hq
      exact absurd hq (Prog.not_isOutcome_fail _)
  await_send _ _ _ _ _ h := absurd h (Prog.not_isOutcome_fail _)
  await_opN _ _ _ _ h hc q hq := by
    obtain ⟨n, -, hn⟩ := isOutcome_bind hq
    exact hc n () (h n) q hn
  await_fail _ _ _ h := absurd h (Prog.not_isOutcome_fail _)

/-- The outcomes of an activation with restart of a typed program are typed residuals with
outputs of `Po`, at events of `Pe`. -/
theorem ports_stepWith {Pe : E → Prop} {Po : O → Prop}
    {restart : α → E → SPComp (Prog E O α × O)} {e : E}
    (hr : ∀ a q, IsOutcome (restart a e) q → Pe e ∧ Po q.2 ∧ Ports Pe Po q.1)
    {p : Prog E O α} (hp : Ports Pe Po p) {q : Prog E O α × O}
    (h : IsOutcome (Prog.stepWith restart p e) q) : Pe e ∧ Po q.2 ∧ Ports Pe Po q.1 :=
  (portsPhase Pe Po e hr).stepWith_sound p () ((ports_iff p).2 hp) q h

/-- **Port typing of the denotation**, from the generic soundness. -/
theorem Lifting.toSys_ports {Pe : E → Prop} {Po : O → Prop} {p : Prog E O α}
    (hp : Ports Pe Po p) :
    Ports Pe Po (Prog.toSys p).init ∧
      ∀ t e, Ports Pe Po t → ∀ q, IsOutcome ((Prog.toSys p).step t e) q →
        Pe e ∧ Po q.2 ∧ Ports Pe Po q.1 :=
  ⟨hp, fun _ _ ht _ h => ports_stepWith (fun _ _ h => absurd h (Prog.not_isOutcome_fail _)) ht h⟩

/-- **Port typing of a loop**, from the generic soundness. -/
theorem Lifting.loopSys_ports {Pe : E → Prop} {Po : O → Prop} (body : σ → Prog E O σ) (s₀ : σ)
    (hb : ∀ s, Ports Pe Po (body s)) :
    Ports Pe Po (Prog.loopSys body s₀).init ∧
      ∀ t e, Ports Pe Po t → ∀ q, IsOutcome ((Prog.loopSys body s₀).step t e) q →
        Pe e ∧ Po q.2 ∧ Ports Pe Po q.1 :=
  ⟨Ports.ret s₀, fun _ _ ht _ h => ports_stepWith (fun s _ h => ports_stepWith
    (fun _ _ h => absurd h (Prog.not_isOutcome_fail _)) (hb s) h) ht h⟩

end PortsSound

/-! ## Opacity of the denotation from the generic soundness -/

section ViewSound

variable {E O α σ : Type}

/-- The lifting of the phases of activations on related events `e`, `e'` for information flow:
the phase computation is coupled at equal heaps with the phase computation of the partner
program into related residuals and related outputs. -/
def viewPhase (V : PubView E O) (RA : α → α → Prop)
    {restart restart' : α → E → SPComp (Prog E O α × O)} {e e' : E} (he : V.ev e e')
    (hr : ∀ a a', RA a a' → rHoare eqPre (restart a e) (restart' a' e')
      (fun r h r' h' => h = h' ∧ ViewRel V RA r.1 r'.1 ∧ V.out r.2 r'.2)) :
    PhaseLift Prog.handler (viewL V RA) e (fun o q => Prog.handler.pure (q, o))
      (fun a => restart a e) fun _ => Prog.handler.fail where
  emit p' c := rHoare eqPre c (Prog.emitK (fun o r => SPComp.pure (r, o)) (fun _ => SPComp.fail) p')
    (fun r h r' h' => h = h' ∧ ViewRel V RA r.1 r'.1 ∧ V.out r.2 r'.2)
  await p' c := rHoare eqPre c (Prog.stepWith restart' p' e')
    (fun r h r' h' => h = h' ∧ ViewRel V RA r.1 r'.1 ∧ V.out r.2 r'.2)
  emit_ret _ _ h := by
    obtain ⟨_, rfl, _⟩ := h
    exact rHoare_fail
  emit_recv _ _ h := by
    obtain ⟨_, rfl, _⟩ := h
    exact rHoare_fail
  emit_send o p _ h := by
    obtain ⟨o', q', rfl, ho, hp⟩ := h
    exact rHoare_ret fun _ _ hh => ⟨hh, (viewRel_iff p q').1 hp, ho⟩
  emit_opN q _ _ c h hc := by
    obtain ⟨k', rfl, h⟩ := h
    change rHoare eqPre (SPComp.bind q c) (SPComp.bind q fun n => Prog.emitK _ _ (k' n)) _
    refine rHoare_bind (rHoare_refl q) fun n n' h₁ h₂ hpre => ?_
    obtain ⟨rfl, rfl⟩ := hpre
    exact hc n (k' n) (h n) h₁ h₁ rfl
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
    obtain ⟨_, _, rfl, _, _⟩ := h
    exact rHoare_fail
  await_opN q _ _ c h hc := by
    obtain ⟨k', rfl, h⟩ := h
    change rHoare eqPre (SPComp.bind q c)
      (SPComp.bind q fun n => Prog.stepWith restart' (k' n) e') _
    refine rHoare_bind (rHoare_refl q) fun n n' h₁ h₂ hpre => ?_
    obtain ⟨rfl, rfl⟩ := hpre
    exact hc n (k' n) (h n) h₁ h₁ rfl
  await_fail _ h := by
    subst h
    exact rHoare_fail

/-- Activations with restart of related programs on related events are coupled at equal heaps
into related residuals and related outputs, when the restarts on related returns are. -/
theorem viewRel_stepWith {V : PubView E O} {RA : α → α → Prop}
    {restart restart' : α → E → SPComp (Prog E O α × O)} {e e' : E}
    (hr : ∀ a a', RA a a' → rHoare eqPre (restart a e) (restart' a' e')
      (fun r h r' h' => h = h' ∧ ViewRel V RA r.1 r'.1 ∧ V.out r.2 r'.2))
    {p p' : Prog E O α} (h : ViewRel V RA p p') (he : V.ev e e') :
    rHoare eqPre (Prog.stepWith restart p e) (Prog.stepWith restart' p' e')
      (fun r h r' h' => h = h' ∧ ViewRel V RA r.1 r'.1 ∧ V.out r.2 r'.2) :=
  (viewPhase V RA he hr).stepWith_sound p p' ((viewRel_iff p p').2 h)

/-- **The unwinding condition of a program**, from the generic soundness. -/
theorem Lifting.toSys_unwinding {V : PubView E O} {RA : α → α → Prop} {p : Prog E O α}
    (hp : ViewRel V RA p p) : Sys.Unwinding (Prog.toSys p) V (ViewRel V RA) :=
  ⟨hp, fun _ _ _ _ ht he => viewRel_stepWith (restart := fun _ _ => SPComp.fail)
    (restart' := fun _ _ => SPComp.fail) (fun _ _ _ => rHoare_fail) ht he⟩

/-- **The unwinding condition of a loop**, from the generic soundness. -/
theorem Lifting.loopSys_unwinding {V : PubView E O} {RA : σ → σ → Prop} (body : σ → Prog E O σ)
    (s₀ : σ) (h₀ : RA s₀ s₀) (hb : ∀ s s', RA s s' → ViewRel V RA (body s) (body s')) :
    Sys.Unwinding (Prog.loopSys body s₀) V (ViewRel V RA) :=
  ⟨ViewRel.ret h₀, fun _ _ _ _ ht he =>
    viewRel_stepWith (fun s s' hs => viewRel_stepWith (restart := fun _ _ => SPComp.fail)
      (restart' := fun _ _ => SPComp.fail) (fun _ _ _ => rHoare_fail) (hb s s' hs) he) ht he⟩

end ViewSound

end ProgE

end CatCrypt.Crypto.Party
