/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Party.Call

/-!
# Time certificates of party programs

A time certificate of a program of the party language (parties and simulators written as
`Party.ProgE` trees) is read off its tree. The costed form of a program over the effect `Op` is
a program over the effect `Costed Op`, whose operations are the operations of `Op` and the ticks
`tick c`, which charge `c` units and return the code `0`. The erasure `ProgE.erase` removes the
ticks. The costed handler `Handler.ticked` runs a tick as a return of `0`, so for a lawful
handler the activation of a costed program, its residual erased, is the activation of the
erased program (`ProgE.act_erase`), and the same holds of the step of a loop
(`ProgE.stepWith_erase`, `Prog.loopSys_step_erase`).

The cost model weighs each effect operation by a weight `w : Op → ℕ`, and each receive and each
send by one unit. `ProgE.Bound w p t P` states that every path of `p` costs at most `t` units
and that every return reached satisfies `P`; it is a predicate on the tree, so a sampling node
quantifies over all outcome codes. Bounds compose along `bind` (`ProgE.Bound.bind`), and the
bound of the unit-cost form `ProgE.costed p`, in which every operation of `p` weighs one unit,
is the bound of `p` at the unit weight (`ProgE.bound_mapOp`). The priced form
`ProgE.priced price body s` of a loop body charges the pure computation of an iteration from the
state `s` as one tick of `price s` before the unit-cost form of `body s`.

A loop whose state grows with the iterations (a lazily sampled table) has the graded bound
`ProgE.LoopBoundGraded w body s₀ Inv a b`: the initial state satisfies `Inv 0`, and the body at a
state of `Inv i` costs at most `a + b * i` and returns states of `Inv (i + 1)`, as the simulator
cost bound `MultiHybrid.Timed.TimeBoundGraded` states for multi-call simulators. The first `q`
iterations, the program `ProgE.iterate body q s₀`, then cost at most
`q * a + b * (q * (q - 1) / 2)` (`ProgE.LoopBoundGraded.iterate_time_le`). When every iteration
is one activation, the iteration index is the activation index; for a multi-call simulator an
iteration spans one or two activations of the system on the sum interface.

The X3DH simulator program `X3DHProg.simBody` is certified with the price of an iteration equal
to the length of its key-derivation table, the cost of a lookup in it: its costed form
`X3DHProg.simBodyT` erases to `simBody` and has the graded bound `7`, `1` on the invariant that
the table holds at most `i` entries after `i` iterations. The forwarding party `Prog.forward`
has the constant bound `2`.

Search words: party language, time certificate, simulator cost, graded bound, costed program,
erasure.

## Main definitions

* `Party.Costed`, `Party.Costed.weight`: effect operations with ticks, and their weight.
* `Party.Handler.ticked`: the costed handler.
* `Party.ProgE.erase`, `Party.ProgE.tick`, `Party.ProgE.costed`, `Party.ProgE.priced`: erasure
  and the costed forms.
* `Party.ProgE.Bound`: the time bound of a program, with a predicate on its returns.
* `Party.ProgE.iterate`, `Party.ProgE.LoopBoundGraded`: iterations of a loop body and the
  graded bound of a loop.
* `Party.X3DHProg.simBodyT`: the costed form of the X3DH simulator program.

## Main results

* `Party.ProgE.erase_bind`, `Party.ProgE.erase_costed`, `Party.ProgE.erase_priced`: erasure.
* `Party.ProgE.emitK_erase`, `Party.ProgE.awaitK_erase`, `Party.ProgE.stepWith_erase`,
  `Party.ProgE.act_erase`, `Party.Prog.loopSys_step_erase`: the costed handler on a costed
  program is the handler on the erased program.
* `Party.ProgE.Bound.mono`, `Party.ProgE.Bound.bind`, `Party.ProgE.bound_mapOp`.
* `Party.ProgE.LoopBoundGraded.iterate_time_le`: the time of `q` iterations.
* `Party.ProgE.priced_loopBoundGraded`: the graded bound of a priced loop body.
* `Party.X3DHProg.simBodyT_erase`, `Party.X3DHProg.simBodyT_loopBoundGraded`: the time
  certificate of the X3DH simulator program.
* `Party.Prog.forward_loopBoundGraded`: the time certificate of the forwarding party.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Party

/-- Effect operations with costs: an operation of `Op`, or a tick of `c` units. -/
inductive Costed (Op : Type) : Type where
  /-- An effect operation. -/
  | op (q : Op)
  /-- A tick of `c` units, returning the code `0`. -/
  | tick (c : ℕ)

namespace Costed

variable {Op : Type}

/-- The weight of a costed operation: one unit for an effect operation, `c` for a tick. -/
def weight : Costed Op → ℕ
  | op _ => 1
  | tick c => c

end Costed

namespace Handler

variable {Op : Type} {M : Type → Type}

/-- The costed handler: an effect operation is run by `H`, a tick returns the code `0`. -/
def ticked (H : Handler Op M) : Handler (Costed Op) M where
  pure := H.pure
  bind := H.bind
  fail := H.fail
  run
    | .op q => H.run q
    | .tick _ => H.pure 0

/-- Unfolding lemma of `ticked`: its sequencing is that of `H`. -/
@[simp] theorem ticked_bind (H : Handler Op M) {β γ : Type} (c : M β) (f : β → M γ) :
    H.ticked.bind c f = H.bind c f := rfl

/-- Unfolding lemma of `ticked`: its return is that of `H`. -/
@[simp] theorem ticked_pure (H : Handler Op M) {γ : Type} (a : γ) :
    H.ticked.pure a = H.pure a := rfl

/-- Unfolding lemma of `ticked`: its failure is that of `H`. -/
@[simp] theorem ticked_fail (H : Handler Op M) {γ : Type} :
    (H.ticked.fail : M γ) = H.fail := rfl

/-- Unfolding lemma of `ticked` at an effect operation. -/
@[simp] theorem ticked_run_op (H : Handler Op M) (q : Op) : H.ticked.run (.op q) = H.run q :=
  rfl

/-- Unfolding lemma of `ticked` at a tick. -/
@[simp] theorem ticked_run_tick (H : Handler Op M) (c : ℕ) :
    H.ticked.run (.tick c) = H.pure 0 := rfl

/-- The costed handler of a lawful handler is lawful. -/
theorem Lawful.ticked {H : Handler Op M} (hH : H.Lawful) : H.ticked.Lawful :=
  ⟨hH.pure_bind, hH.bind_assoc, hH.fail_bind⟩

end Handler

namespace ProgE

variable {Op Op' : Type} {M : Type → Type} {E O α β γ σ : Type}

/-! ## Costed programs and erasure -/

/-- The erasure of a costed program: its ticks removed. -/
def erase : ProgE (Costed Op) E O α → ProgE Op E O α
  | .ret a => .ret a
  | .recv k => .recv fun e => erase (k e)
  | .send o p => .send o (erase p)
  | .opN (.op q) k => .opN q fun n => erase (k n)
  | .opN (.tick _) k => erase (k 0)
  | .fail => .fail

/-- A tick of `c` units followed by `p`. -/
def tick (c : ℕ) (p : ProgE (Costed Op) E O α) : ProgE (Costed Op) E O α :=
  .opN (.tick c) fun _ => p

/-- The unit-cost form of a program: every operation is an effect operation of weight one. -/
abbrev costed : ProgE Op E O α → ProgE (Costed Op) E O α := mapOp Costed.op

/-- The priced form of a loop body: the iteration from `s` charges `price s` units for its pure
computation, followed by the unit-cost form of `body s`. -/
def priced (price : σ → ℕ) (body : σ → ProgE Op E O σ) (s : σ) : ProgE (Costed Op) E O σ :=
  tick (price s) (costed (body s))

/-- Erasure removes a tick. -/
@[simp] theorem erase_tick (c : ℕ) (p : ProgE (Costed Op) E O α) : erase (tick c p) = erase p :=
  rfl

/-- The erasure of the unit-cost form is the program. -/
@[simp] theorem erase_costed (p : ProgE Op E O α) : erase (costed p) = p := by
  induction p with
  | ret a => rfl
  | recv k ih => simp only [mapOp, erase, ih]
  | send o p ih => simp only [mapOp, erase, ih]
  | opN q k ih => simp only [mapOp, erase, ih]
  | fail => rfl

/-- The erasure of the priced form is the body. -/
@[simp] theorem erase_priced (price : σ → ℕ) (body : σ → ProgE Op E O σ) (s : σ) :
    erase (priced price body s) = body s := by
  simp [priced]

/-- Erasure is a monad morphism. -/
theorem erase_bind (p : ProgE (Costed Op) E O α) (f : α → ProgE (Costed Op) E O β) :
    erase (p.bind f) = (erase p).bind fun a => erase (f a) := by
  induction p with
  | ret a => rfl
  | recv k ih => simp only [bind, erase, ih]
  | send o p ih => simp only [bind, erase, ih]
  | opN q k ih =>
    cases q with
    | op q => simp only [bind, erase, ih]
    | tick c => simp only [bind, erase, ih]
  | fail => rfl

/-! ## The costed handler runs the erased program -/

/-- The emit phase of a costed program through the costed handler is the emit phase of the
erased program. -/
theorem emitK_erase (H : Handler Op M) (hH : H.Lawful) (s : O → ProgE Op E O α → M γ)
    (r : α → M γ) (p : ProgE (Costed Op) E O α) :
    emitK H.ticked (fun o q => s o (erase q)) r p = emitK H s r (erase p) := by
  induction p with
  | ret a => rfl
  | recv k ih => rfl
  | send o p ih => rfl
  | opN q k ih =>
    cases q with
    | op q => simp only [emitK, erase, Handler.ticked_bind, Handler.ticked_run_op, ih]
    | tick c =>
      simp only [emitK, erase, Handler.ticked_bind, Handler.ticked_run_tick, hH.pure_bind, ih]
  | fail => rfl

/-- The await phase of a costed program through the costed handler is the await phase of the
erased program. -/
theorem awaitK_erase (H : Handler Op M) (hH : H.Lawful) (e : E) (s : O → ProgE Op E O α → M γ)
    (rA rE : α → M γ) (p : ProgE (Costed Op) E O α) :
    awaitK H.ticked e (fun o q => s o (erase q)) rA rE p = awaitK H e s rA rE (erase p) := by
  induction p with
  | ret a => rfl
  | recv k ih => exact emitK_erase H hH s rE (k e)
  | send o p ih => rfl
  | opN q k ih =>
    cases q with
    | op q => simp only [awaitK, erase, Handler.ticked_bind, Handler.ticked_run_op, ih]
    | tick c =>
      simp only [awaitK, erase, Handler.ticked_bind, Handler.ticked_run_tick, hH.pure_bind, ih]
  | fail => rfl

/-- **Erasure of an activation with restart.** When the restarts are related by erasure, an
activation of a costed program through the costed handler, its residual erased, is the
activation of the erased program. -/
theorem stepWith_erase (H : Handler Op M) (hH : H.Lawful)
    (restart : α → E → M (ProgE (Costed Op) E O α × O))
    (restart' : α → E → M (ProgE Op E O α × O))
    (hr : ∀ a e, H.bind (restart a e) (fun x => H.pure (erase x.1, x.2)) = restart' a e)
    (p : ProgE (Costed Op) E O α) (e : E) :
    H.bind (stepWith H.ticked restart p e) (fun x => H.pure (erase x.1, x.2)) =
      stepWith H restart' (erase p) e := by
  have h := bind_awaitK H.ticked hH.ticked e (fun o q => H.ticked.pure (q, o))
    (fun a => restart a e) (fun _ => H.ticked.fail) (fun x => H.pure (erase x.1, x.2)) p
  simp only [stepWith]
  refine h.trans ?_
  simp only [Handler.ticked_bind, Handler.ticked_pure, Handler.ticked_fail, hH.pure_bind,
    hH.fail_bind, hr]
  exact awaitK_erase H hH e (fun o q => H.pure (q, o)) _ _ p

/-- **Erasure of an activation.** An activation of a costed program through the costed handler,
its residual erased, is the activation of the erased program. -/
theorem act_erase (H : Handler Op M) (hH : H.Lawful) (p : ProgE (Costed Op) E O α) (e : E) :
    H.bind (act H.ticked p e) (fun x => H.pure (erase x.1, x.2)) = act H (erase p) e :=
  stepWith_erase H hH _ _ (fun _ _ => hH.fail_bind _) p e

/-! ## Time bounds -/

/-- The time bound `t` of a program at the weight `w`, with the predicate `P` on its returns:
every path costs at most `t` units, each operation `q` weighing `w q` and each receive and send
one unit, and every return reached satisfies `P`. -/
def Bound (w : Op → ℕ) : ProgE Op E O α → ℕ → (α → Prop) → Prop
  | .ret a, _, P => P a
  | .recv k, t, P => 1 ≤ t ∧ ∀ e, Bound w (k e) (t - 1) P
  | .send _ p, t, P => 1 ≤ t ∧ Bound w p (t - 1) P
  | .opN q k, t, P => w q ≤ t ∧ ∀ n, Bound w (k n) (t - w q) P
  | .fail, _, _ => True

/-- A time bound is a time bound of every larger time and every weaker predicate. -/
theorem Bound.mono {w : Op → ℕ} {p : ProgE Op E O α} {t t' : ℕ} {P P' : α → Prop}
    (h : Bound w p t P) (ht : t ≤ t') (hP : ∀ a, P a → P' a) : Bound w p t' P' := by
  induction p generalizing t t' with
  | ret a => exact hP a h
  | recv k ih =>
    simp only [Bound] at h ⊢
    exact ⟨by omega, fun e => ih e (h.2 e) (by omega)⟩
  | send o p ih =>
    simp only [Bound] at h ⊢
    exact ⟨by omega, ih h.2 (by omega)⟩
  | opN q k ih =>
    simp only [Bound] at h ⊢
    exact ⟨by omega, fun n => ih n (h.2 n) (by omega)⟩
  | fail => trivial

/-- **Time bounds compose along `bind`.** -/
theorem Bound.bind {w : Op → ℕ} {p : ProgE Op E O α} {f : α → ProgE Op E O β} {t u : ℕ}
    {P : β → Prop} (h : Bound w p t fun a => Bound w (f a) u P) :
    Bound w (p.bind f) (t + u) P := by
  induction p generalizing t with
  | ret a => exact Bound.mono h (by omega) fun _ => id
  | recv k ih =>
    simp only [Bound, ProgE.bind] at h ⊢
    exact ⟨by omega, fun e => (ih e (h.2 e)).mono (by omega) fun _ => id⟩
  | send o p ih =>
    simp only [Bound, ProgE.bind] at h ⊢
    exact ⟨by omega, (ih h.2).mono (by omega) fun _ => id⟩
  | opN q k ih =>
    simp only [Bound, ProgE.bind] at h ⊢
    exact ⟨by omega, fun n => (ih n (h.2 n)).mono (by omega) fun _ => id⟩
  | fail => trivial

/-- The time bound of a mapped program is the time bound at the precomposed weight. -/
theorem bound_mapOp (w : Op' → ℕ) (f : Op → Op') (p : ProgE Op E O α) (t : ℕ) (P : α → Prop) :
    Bound w (mapOp f p) t P ↔ Bound (fun q => w (f q)) p t P := by
  induction p generalizing t with
  | ret a => exact Iff.rfl
  | recv k ih => simp only [mapOp, Bound, ih]
  | send o p ih => simp only [mapOp, Bound, ih]
  | opN q k ih => simp only [mapOp, Bound, ih]
  | fail => exact Iff.rfl

/-- The time bound of the unit-cost form is the time bound at the unit weight. -/
theorem bound_costed (p : ProgE Op E O α) (t : ℕ) (P : α → Prop) :
    Bound Costed.weight (costed p) t P ↔ Bound (fun _ => 1) p t P :=
  bound_mapOp _ _ p t P

/-! ## Graded bounds of loops -/

/-- The first `n` iterations of the loop body `body` from `s`. -/
def iterate (body : σ → ProgE Op E O σ) : ℕ → σ → ProgE Op E O σ
  | 0, s => .ret s
  | n + 1, s => (body s).bind (iterate body n)

/-- The graded time bound `a`, `b` of the loop of `body` from `s₀` on the invariant `Inv`,
indexed by the number of iterations: the initial state satisfies `Inv 0`, and the body at a
state of `Inv i` costs at most `a + b * i` and returns states of `Inv (i + 1)`. -/
def LoopBoundGraded (w : Op → ℕ) (body : σ → ProgE Op E O σ) (s₀ : σ) (Inv : ℕ → σ → Prop)
    (a b : ℕ) : Prop :=
  Inv 0 s₀ ∧ ∀ i s, Inv i s → Bound w (body s) (a + b * i) (Inv (i + 1))

/-- A graded bound is a graded bound of all larger constants. -/
theorem LoopBoundGraded.mono {w : Op → ℕ} {body : σ → ProgE Op E O σ} {s₀ : σ}
    {Inv : ℕ → σ → Prop} {a b a' b' : ℕ} (h : LoopBoundGraded w body s₀ Inv a b) (ha : a ≤ a')
    (hb : b ≤ b') : LoopBoundGraded w body s₀ Inv a' b' :=
  ⟨h.1, fun i s hs => (h.2 i s hs).mono
    (Nat.add_le_add ha (Nat.mul_le_mul_right i hb)) fun _ => id⟩

/-- A constant bound on an invariant is a graded bound without growth. -/
theorem LoopBoundGraded.of_bound {w : Op → ℕ} {body : σ → ProgE Op E O σ} {s₀ : σ}
    {Inv : σ → Prop} {a : ℕ} (h0 : Inv s₀) (h : ∀ s, Inv s → Bound w (body s) a Inv) :
    LoopBoundGraded w body s₀ (fun _ => Inv) a 0 :=
  ⟨h0, fun _ s hs => (h s hs).mono (by omega) fun _ => id⟩

/-- Under a graded bound, `n` iterations from a state of `Inv i` cost at most the sum of
`a + b * (i + j)` over `j < n`. -/
theorem LoopBoundGraded.iterate_le {w : Op → ℕ} {body : σ → ProgE Op E O σ} {s₀ : σ}
    {Inv : ℕ → σ → Prop} {a b : ℕ} (h : LoopBoundGraded w body s₀ Inv a b) (n : ℕ) :
    ∀ i s, Inv i s →
      Bound w (iterate body n s) (∑ j ∈ Finset.range n, (a + b * (i + j))) (Inv (i + n)) := by
  induction n with
  | zero => intro i s hs; exact hs
  | succ n ih =>
    intro i s hs
    have hsum : ∑ j ∈ Finset.range (n + 1), (a + b * (i + j)) =
        (a + b * i) + ∑ j ∈ Finset.range n, (a + b * (i + 1 + j)) := by
      rw [Finset.sum_range_succ', add_comm]
      refine congrArg₂ _ (by simp) (Finset.sum_congr rfl fun j _ => by grind)
    rw [hsum]
    refine Bound.bind ((h.2 i s hs).mono le_rfl fun s' hs' => ?_)
    have := ih (i + 1) s' hs'
    rwa [show i + 1 + n = i + (n + 1) by omega] at this

/-- **Time of `q` iterations.** Under a graded bound, the first `q` iterations from the initial
state cost at most `q * a + b * (q * (q - 1) / 2)`. -/
theorem LoopBoundGraded.iterate_time_le {w : Op → ℕ} {body : σ → ProgE Op E O σ} {s₀ : σ}
    {Inv : ℕ → σ → Prop} {a b : ℕ} (h : LoopBoundGraded w body s₀ Inv a b) (q : ℕ) :
    Bound w (iterate body q s₀) (q * a + b * (q * (q - 1) / 2)) (Inv q) := by
  have h' := h.iterate_le q 0 s₀ h.1
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
    ← Finset.mul_sum] at h'
  simpa [Finset.sum_range_id] using h'

/-- **Graded bound of a priced loop body.** If the price at a state of `Inv i` is at most
`c + b * i` and the body at a state of `Inv i` has the unit-weight bound `a` and returns states
of `Inv (i + 1)`, the priced loop has the graded bound `c + a`, `b`. -/
theorem priced_loopBoundGraded (price : σ → ℕ) (body : σ → ProgE Op E O σ) (s₀ : σ)
    (Inv : ℕ → σ → Prop) (a b c : ℕ) (h0 : Inv 0 s₀)
    (hp : ∀ i s, Inv i s → price s ≤ c + b * i)
    (hb : ∀ i s, Inv i s → Bound (fun _ => 1) (body s) a (Inv (i + 1))) :
    LoopBoundGraded Costed.weight (priced price body) s₀ Inv (c + a) b := by
  refine ⟨h0, fun i s hs => ?_⟩
  have hc := (bound_costed (body s) a (Inv (i + 1))).2 (hb i s hs)
  have hpi := hp i s hs
  simp only [priced, tick, Bound, Costed.weight]
  exact ⟨by omega, fun _ => hc.mono (by omega) fun _ => id⟩

end ProgE

/-! ## The classical language -/

namespace Prog

open CatCrypt.Core

variable {E O σ : Type}

/-- **Erasure of a loop step.** The step of a loop of a costed body through the costed
classical handler, its residual erased, is the step of the loop of the erased body. -/
theorem loopSys_step_erase (bodyT : σ → ProgE (Costed (SPComp ℕ)) E O σ) (s₀ : σ)
    (p : ProgE (Costed (SPComp ℕ)) E O σ) (e : E) :
    SPComp.bind (ProgE.stepWith handler.ticked (fun s e => ProgE.act handler.ticked (bodyT s) e)
      p e) (fun x => SPComp.pure (ProgE.erase x.1, x.2)) =
      (loopSys (fun s => ProgE.erase (bodyT s)) s₀).step (ProgE.erase p) e :=
  ProgE.stepWith_erase handler handler_lawful _ _
    (fun s e => ProgE.act_erase handler handler_lawful (bodyT s) e) p e

/-- **Time certificate of the forwarding party.** Each iteration of the forwarding party
receives and sends: the bound `2`. -/
theorem forward_loopBoundGraded (f : E → O) :
    ProgE.LoopBoundGraded Costed.weight (fun _ => ProgE.costed (forward f)) ()
      (fun _ _ => True) 2 0 :=
  ProgE.LoopBoundGraded.of_bound trivial fun _ _ => by
    simp [forward, ProgE.Bound, ProgE.recvE, ProgE.sendE, ProgE.bind, ProgE.mapOp]

end Prog

/-! ## The X3DH simulator -/

namespace X3DHProg

open CatCrypt.Crypto.AKE.X3DHSquare CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract Prog CatCrypt.Core

variable {S W K : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] (G : DHGroup S W)

/-- Unit-weight bound of a sample on a countable type. -/
theorem bound_sample {E O α β : Type} [Countable β] {μ : SPComp β}
    {k : β → Prog E O α} {t : ℕ} {P : α → Prop} (ht : 1 ≤ t)
    (h : ∀ b, ProgE.Bound (fun _ => 1) (k b) (t - 1) P) :
    ProgE.Bound (fun _ => 1) (Prog.sample μ k) t P := by
  simp only [Prog.sample, sampleN, ProgE.Bound]
  refine ⟨ht, fun n => ?_⟩
  split
  · exact h _
  · trivial

/-- Unit-weight bound of `recvO`: one unit. -/
theorem bound_recvO {E A Q O : Type} {P : E → Prop} (h : ∀ e, P e) :
    ProgE.Bound (fun _ => 1) (recvO : Prog (E ⊕ A) (Q ⊕ O) E) 1 P := by
  simp only [recvO, ProgE.Bound]
  refine ⟨le_rfl, fun x => ?_⟩
  rcases x with e | a
  · exact h e
  · trivial

omit [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- `ltP` takes one unit and keeps the key-derivation table. -/
theorem ltP_bound (s : RSt S W K) (pid : PartyId) :
    ProgE.Bound (fun _ => 1) (ltP (S := S) (W := W) (K := K) s pid) 1
      (fun r => r.2.ro = s.ro) := by
  unfold ltP
  split
  · rfl
  · apply bound_sample le_rfl
    intro _
    rfl

omit [Field S] [Fintype S] [DecidableEq W] [Inhabited K] in
/-- `roP` takes one unit and grows the table by at most one entry. -/
theorem roP_bound {D : Type} [DecidableEq D] (tb : List (D × K)) (x : D) :
    ProgE.Bound (fun _ => 1) (roP (S := S) (W := W) tb x) 1
      (fun r => r.2.length ≤ tb.length + 1) := by
  unfold roP
  split
  · simp [ProgE.Bound]
  · apply bound_sample le_rfl
    intro _
    simp [ProgE.Bound]

omit [Field S] [Fintype S] in
/-- `deliverP` takes one unit and grows the table by at most one entry. -/
theorem deliverP_bound (rs : RSt S W K) (inp : Inst → Option (Inp W)) (x : Inst) (r : Rec K)
    (ip : Inp W) :
    ProgE.Bound (fun _ => 1) (deliverP rs inp x r ip) 1
      (fun q => q.1.1.ro.length ≤ rs.ro.length + 1) := by
  unfold deliverP
  split
  · refine ProgE.Bound.bind (t := 1) (u := 0) ((roP_bound (S := S) (W := W) rs.ro ip).mono le_rfl
      fun p hp => ?_)
    simpa [ProgE.Bound, keyed] using hp
  · simp [ProgE.Bound, keyed]

/-- `simCompleteP` takes at most three units and grows the table by at most one entry. -/
theorem simCompleteP_bound (s : SimSt S W K) (x : Inst) :
    ProgE.Bound (fun _ => 1) (simCompleteP G s x) 3
      (fun q => q.1.1.ro.length ≤ s.1.ro.length + 1) := by
  unfold simCompleteP
  split
  · split
    · split
      · refine ProgE.Bound.bind (t := 1) (u := 2) ((ltP_bound _ _).mono le_rfl fun la hla => ?_)
        refine ProgE.Bound.bind (t := 1) (u := 1) ((ltP_bound _ _).mono le_rfl fun lb hlb => ?_)
        exact (deliverP_bound _ _ _ _ _).mono le_rfl fun q hq => by rw [hlb, hla] at hq; exact hq
      · simp [ProgE.Bound]
    · simp [ProgE.Bound]
  · simp [ProgE.Bound]

/-- `simSendP` takes at most three units and grows the table by at most one entry. -/
theorem simSendP_bound (s : SimSt S W K) (x : Inst) (e : W) :
    ProgE.Bound (fun _ => 1) (simSendP G s x e) 3
      (fun q => q.1.1.ro.length ≤ s.1.ro.length + 1) := by
  unfold simSendP
  split
  · split
    · refine ProgE.Bound.bind (t := 1) (u := 2) ((ltP_bound _ _).mono le_rfl fun lb hlb => ?_)
      refine ProgE.Bound.bind (t := 1) (u := 1) ((ltP_bound _ _).mono le_rfl fun la hla => ?_)
      exact (deliverP_bound _ _ _ _ _).mono le_rfl fun q hq => by rw [hla, hlb] at hq; exact hq
    · simp [ProgE.Bound]
  · simp [ProgE.Bound]

/-- `simStartP` takes at most three units and grows the table by at most one entry. -/
theorem simStartP_bound (s : SimSt S W K) (e : OEv W) :
    ProgE.Bound (fun _ => 1) (simStartP G s e) 3
      (fun q => q.1.1.ro.length ≤ s.1.ro.length + 1) := by
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) |
    (_ | _ | pid | ⟨sid, pid⟩ | pid | ⟨sid, pid⟩ | ⟨sid, pid, w⟩ | x)
  · simp only [simStartP]
    split
    · apply bound_sample (by omega)
      intro _
      simp [ProgE.Bound]
    · simp [ProgE.Bound]
  · simp [simStartP, ProgE.Bound]
  · simp [simStartP, ProgE.Bound]
  · simp [simStartP, ProgE.Bound]
  · simp only [simStartP]
    refine ProgE.Bound.bind (t := 1) (u := 2) ((ltP_bound _ _).mono le_rfl fun l hl => ?_)
    simp [ProgE.Bound, hl]
  · simp [simStartP, ProgE.Bound]
  · simp only [simStartP, simCorruptP]
    split
    · simp [ProgE.Bound]
    · refine ProgE.Bound.bind (t := 1) (u := 2) ((ltP_bound _ _).mono le_rfl fun l hl => ?_)
      simp [ProgE.Bound, hl]
  · exact simCompleteP_bound G s (sid, pid)
  · exact simSendP_bound G s (sid, pid) w
  · simp only [simStartP]
    refine ProgE.Bound.bind (t := 1) (u := 2) ((roP_bound _ _).mono le_rfl fun p hp => ?_)
    simpa [ProgE.Bound] using hp

omit [Field S] [Fintype S] [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- `simDecide` takes at most three units and keeps the table. -/
theorem simDecide_bound (q : SimSt S W K × Dec S W K) :
    ProgE.Bound (fun _ => 1) (simDecide q) 3 (fun s => s.1.ro = q.1.1.ro) := by
  unfold simDecide
  split
  · simp [call, callK, simK, outE, ProgE.Bound, ProgE.bind]
  · simp [outE, ProgE.Bound, ProgE.bind]

/-- An iteration of the X3DH simulator program takes at most seven units and grows the
key-derivation table by at most one entry. -/
theorem simBody_bound (s : SimSt S W K) :
    ProgE.Bound (fun _ => 1) (simBody G s) 7 (fun s' => s'.1.ro.length ≤ s.1.ro.length + 1) := by
  unfold simBody
  refine ProgE.Bound.bind (t := 1) (u := 6) (bound_recvO fun e => ?_)
  refine ProgE.Bound.bind (t := 3) (u := 3) ((simStartP_bound G s e).mono le_rfl fun q hq => ?_)
  exact (simDecide_bound q).mono le_rfl fun s' hs' => by rw [hs']; exact hq

/-- **The costed form of the X3DH simulator program**: an iteration from `s` charges the length
of the key-derivation table, the cost of a lookup in it, before the unit-cost form of
`simBody`. -/
noncomputable def simBodyT : SimSt S W K → ProgE (Costed (SPComp ℕ))
    (OEv W ⊕ FOut K) (FEv K ⊕ OOut S W K) (SimSt S W K) :=
  ProgE.priced (fun s => s.1.ro.length) (simBody G)

/-- The costed form of the X3DH simulator program erases to `simBody`. -/
theorem simBodyT_erase (s : SimSt S W K) : ProgE.erase (simBodyT G s) = simBody G s :=
  ProgE.erase_priced _ _ s

/-- **Time certificate of the X3DH simulator program.** After `i` iterations the key-derivation
table holds at most `i` entries, and the `i`-th iteration costs at most `7 + i`. -/
theorem simBodyT_loopBoundGraded :
    ProgE.LoopBoundGraded Costed.weight (simBodyT G)
      ((rInit, fun _ => none, .fwd) : SimSt S W K) (fun i s => s.1.ro.length ≤ i) 7 1 := by
  have h := ProgE.priced_loopBoundGraded (fun s : SimSt S W K => s.1.ro.length) (simBody G)
    ((rInit, fun _ => none, .fwd) : SimSt S W K) (fun i s => s.1.ro.length ≤ i) 7 1 0
    (by simp [rInit])
    (fun i s hs => by omega)
    (fun i s hs => (simBody_bound G s).mono le_rfl fun s' hs' => by omega)
  exact h

end X3DHProg

end CatCrypt.Crypto.Party
