/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Party.Timed
public import CatCryptCore.Crypto.Party.Protocols.QOTP

/-!
# Costed quantum simulators

A costed quantum computation on the register `R` is a quantum party program without events or
outputs whose operations are costed (`QTreeT R α`, the abbreviation of
`ProgE (Costed (SubInstrument R R ℕ)) Empty Empty α`): its operations are subinstruments on `R`
and ticks. It erases to the subinstrument `QTreeT.erase x`, which runs the operations through the
costed quantum handler, and its time is the bound `ProgE.Bound Costed.weight` of its paths: one
unit for an operation, `c` units for a tick of `c`.

A costed quantum simulator `QSim.Timed σ E O EG OG d` has a state `σ` and steps that are costed
quantum computations on the environment register `Fin d`. It erases to the simulator
`QSim.Timed.erase T` of the erased steps; `T.Erases ε S` relates it to a simulator `S` whose
steps are the erased steps with the state map `ε`. Its time bound `T.TimeBound Inv a b` bounds
each `pre` step from a state of the invariant `Inv` by `a` and each `post` step by `b`, the steps
returning states of `Inv`. `QSimQ.Timed` is the same for simulators with a private register.

The costed loop simulator `QProg.loopQSim.timed bodyT s₀` runs a costed body program: its state
is the costed residual program and a step is an activation of the residual through the tree
handler `ProgE.treeHandler`, which runs a program as a costed tree (`QProg.loopStepT`). It
erases to `QProg.loopQSim (erase ∘ bodyT) s₀`, and when each iteration of the body costs at most
`a`, each step costs at most `2 * a` (`QProg.loopQSim.timeBound_timed`).

Search words: quantum simulator, time certificate, costed simulator, running time, erasure,
quantum party program, loop simulator, cost of a twirl.

## Main definitions

* `Party.ProgE.treeHandler`, `Party.ProgE.runTree`: programs as the monad of their own trees,
  and the run of a tree without events through a handler.
* `ReactiveUC.QTreeT`, `ReactiveUC.QTreeT.erase`, `ReactiveUC.QTreeT.opE`: costed quantum
  computations, their erasure, and a costed operation.
* `ReactiveUC.QSim.Timed`, `ReactiveUC.QSim.Timed.erase`, `ReactiveUC.QSim.Timed.Erases`,
  `ReactiveUC.QSim.Timed.TimeBound`: costed quantum simulators, erasure and time bound.
* `ReactiveUC.QSimQ.Timed`: the same for simulators with a private register.
* `Party.QProg.loopStepT`: the costed step of a loop of a costed quantum party program.
* `Party.QProg.loopQSim.timed`, `Party.QProg.loopQSimQ.timed`: the costed loop simulators.

## Main results

* `Party.ProgE.runTree_awaitK`, `Party.ProgE.bound_awaitK_tree`: the run and the time of an
  activation through the tree handler.
* `Party.QProg.loopStepT_erase`, `Party.QProg.loopStepT_time`: erasure and time of the costed
  loop step.
* `Party.QProg.loopQSim.erase_timed`, `Party.QProg.loopQSim.timeBound_timed`: the costed loop
  simulator erases to the loop simulator, each step costing at most twice the bound of an
  iteration.
* `Party.QProg.loopQSimQ.erase_timed`, `Party.QProg.loopQSimQ.timeBound_timed`: the same with a
  private register.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Party

open CatCrypt.Core _root_.Quantum CatCrypt.Quantum.ReactiveUC

namespace ProgE

variable {Op : Type} {M : Type → Type} {E O E' O' α β γ : Type}

/-! ## Programs as the monad of their trees -/

/-- The tree handler: programs over `Op` as a monad, an operation run as the program that
performs it and returns its outcome. -/
def treeHandler : Handler Op (ProgE Op E' O') where
  pure a := .ret a
  bind c f := c.bind f
  fail := .fail
  run q := .opN q .ret

/-- The tree handler is lawful. -/
theorem treeHandler_lawful : (treeHandler : Handler Op (ProgE Op E' O')).Lawful where
  pure_bind _ _ := rfl
  bind_assoc c f g := bind_assoc c f g
  fail_bind _ := rfl

/-- The run of a program without events or outputs through the handler `H`. -/
def runTree (H : Handler Op M) (x : ProgE Op Empty Empty γ) : M γ :=
  emitK H (fun o _ => o.elim) H.pure x

/-- The run of a sequential composition is the sequential composition of the runs. -/
theorem runTree_bind (H : Handler Op M) (hH : H.Lawful) (x : ProgE Op Empty Empty α)
    (f : α → ProgE Op Empty Empty β) :
    runTree H (x.bind f) = H.bind (runTree H x) fun a => runTree H (f a) := by
  simp only [runTree, emitK_bind, bind_emitK H hH, hH.pure_bind]
  congr 1
  funext o
  exact o.elim

/-- The run of the emit phase through the tree handler is the emit phase through `H` of the
runs of its continuations. -/
theorem runTree_emitK (H : Handler Op M) (s : O → ProgE Op E O α → ProgE Op Empty Empty γ)
    (r : α → ProgE Op Empty Empty γ) (p : ProgE Op E O α) :
    runTree H (emitK treeHandler s r p) =
      emitK H (fun o q => runTree H (s o q)) (fun a => runTree H (r a)) p := by
  induction p with
  | ret a => rfl
  | recv k => rfl
  | send o q => rfl
  | opN q k ih => exact congrArg (H.bind (H.run q)) (funext ih)
  | fail => rfl

/-- The run of the await phase through the tree handler is the await phase through `H` of the
runs of its continuations. -/
theorem runTree_awaitK (H : Handler Op M) (e : E)
    (s : O → ProgE Op E O α → ProgE Op Empty Empty γ) (rA rE : α → ProgE Op Empty Empty γ)
    (p : ProgE Op E O α) :
    runTree H (awaitK treeHandler e s rA rE p) =
      awaitK H e (fun o q => runTree H (s o q)) (fun a => runTree H (rA a))
        (fun a => runTree H (rE a)) p := by
  induction p with
  | ret a => rfl
  | recv k => exact runTree_emitK H s rE (k e)
  | send o q => rfl
  | opN q k ih => exact congrArg (H.bind (H.run q)) (funext ih)
  | fail => rfl

/-- The run of an activation through the tree handler is the activation through `H` with the
runs of the restarts. -/
theorem runTree_stepWith (H : Handler Op M)
    (restart : α → E → ProgE Op Empty Empty (ProgE Op E O α × O)) (p : ProgE Op E O α)
    (e : E) :
    runTree H (stepWith treeHandler restart p e) =
      stepWith H (fun a e => runTree H (restart a e)) p e :=
  runTree_awaitK H e _ _ _ p

/-! ## Time of the phases through the tree handler -/

/-- **Time of the emit phase as a tree.** When `p` costs at most `t ≤ T` and returns values of
`P`, and the continuations cost at most `D` and return values of `R`, the emit phase through the
tree handler costs at most `t + D` and returns values of `R`. -/
theorem bound_emitK_tree {w : Op → ℕ} {P : α → Prop} {R : γ → Prop} {T D : ℕ}
    (s : O → ProgE Op E O α → ProgE Op E' O' γ) (r : α → ProgE Op E' O' γ)
    (hs : ∀ o q u, u ≤ T → Bound w q u P → Bound w (s o q) D R)
    (hr : ∀ a, P a → Bound w (r a) D R)
    (p : ProgE Op E O α) (t : ℕ) (ht : t ≤ T) (hp : Bound w p t P) :
    Bound w (emitK treeHandler s r p) (t + D) R := by
  induction p generalizing t with
  | ret a => exact (hr a hp).mono (by omega) fun _ => id
  | recv k => trivial
  | send o q => exact (hs o q (t - 1) (by omega) hp.2).mono (by omega) fun _ => id
  | opN q k ih =>
    simp only [emitK, treeHandler, ProgE.bind, Bound]
    refine ⟨by have := hp.1; omega, fun n => ?_⟩
    exact (ih n (t - w q) (by omega) (hp.2 n)).mono (by have := hp.1; omega) fun _ => id
  | fail => trivial

/-- **Time of the await phase as a tree.** When `p` costs at most `t ≤ T` and returns values of
`P`, and the continuations cost at most `D` and return values of `R`, the await phase through
the tree handler costs at most `t + D` and returns values of `R`. -/
theorem bound_awaitK_tree {w : Op → ℕ} {P : α → Prop} {R : γ → Prop} {T D : ℕ} (e : E)
    (s : O → ProgE Op E O α → ProgE Op E' O' γ) (rA rE : α → ProgE Op E' O' γ)
    (hs : ∀ o q u, u ≤ T → Bound w q u P → Bound w (s o q) D R)
    (hA : ∀ a, P a → Bound w (rA a) D R) (hE : ∀ a, P a → Bound w (rE a) D R)
    (p : ProgE Op E O α) (t : ℕ) (ht : t ≤ T) (hp : Bound w p t P) :
    Bound w (awaitK treeHandler e s rA rE p) (t + D) R := by
  induction p generalizing t with
  | ret a => exact (hA a hp).mono (by omega) fun _ => id
  | recv k =>
    exact (bound_emitK_tree s rE hs hE (k e) (t - 1) (by omega) (hp.2 e)).mono (by omega)
      fun _ => id
  | send o q => trivial
  | opN q k ih =>
    simp only [awaitK, treeHandler, ProgE.bind, Bound]
    refine ⟨by have := hp.1; omega, fun n => ?_⟩
    exact (ih n (t - w q) (by omega) (hp.2 n)).mono (by have := hp.1; omega) fun _ => id
  | fail => trivial

end ProgE

end CatCrypt.Crypto.Party

namespace CatCrypt.Quantum.ReactiveUC

open _root_.Quantum CatCrypt.Crypto.Party

/-! ## Costed quantum computations -/

/-- A costed quantum computation on the register `R`: a program without events or outputs
whose operations are subinstruments on `R` with outcome codes and ticks. -/
abbrev QTreeT (R : Type) [Fintype R] (α : Type) : Type :=
  ProgE (Costed (SubInstrument R R ℕ)) Empty Empty α

namespace QTreeT

variable {R : Type} [Fintype R] {α β : Type}

/-- The erasure of a costed quantum computation: the subinstrument that runs its operations,
the ticks removed. -/
noncomputable def erase (x : QTreeT R α) : SubInstrument R R α :=
  ProgE.runTree QProg.handler.ticked x

/-- The costed operation that applies the subinstrument `q` and returns its outcome. -/
noncomputable def opE [Countable β] (q : SubInstrument R R β) : QTreeT R β :=
  ProgE.costed (QProg.opE q)

/-- Unfolding lemma of `erase` at a return. -/
@[simp] theorem erase_ret (a : α) : erase (.ret a : QTreeT R α) = SubInstrument.pure a := rfl

/-- Unfolding lemma of `erase` at a failure. -/
@[simp] theorem erase_fail : erase (.fail : QTreeT R α) = SubInstrument.fail := rfl

/-- Erasure of a tick. -/
@[simp] theorem erase_tick (c : ℕ) (x : QTreeT R α) : erase (ProgE.tick c x) = erase x := by
  simp only [erase, ProgE.runTree, ProgE.tick, ProgE.emitK, Handler.ticked_bind,
    Handler.ticked_run_tick]
  exact QProg.handler_lawful.pure_bind _ _

/-- Erasure is a monad morphism. -/
theorem erase_bind (x : QTreeT R α) (f : α → QTreeT R β) :
    erase (x.bind f) = (erase x).bind fun a => erase (f a) :=
  ProgE.runTree_bind _ QProg.handler_lawful.ticked x f

/-- Erasure of a costed operation. -/
@[simp] theorem erase_opE [Countable β] (q : SubInstrument R R β) : erase (opE q) = q := by
  have h := ProgE.emitK_erase QProg.handler QProg.handler_lawful
    (fun (o : Empty) (_ : QProg R Empty Empty β) => o.elim) SubInstrument.pure
    (ProgE.costed (QProg.opE q))
  rw [ProgE.erase_costed] at h
  change ProgE.emitK _ _ _ _ = _
  refine (congrArg (fun s => ProgE.emitK QProg.handler.ticked s SubInstrument.pure
    (ProgE.costed (QProg.opE q))) (funext fun o => funext fun _ => o.elim)).trans
    (h.trans ?_)
  change QProg.emitK _ _ (QProg.op q .ret) = q
  rw [QProg.emitK_op]
  simp only [QProg.emitK_ret, SubInstrument.bind_pure]

/-- The time of a costed operation: one unit. -/
theorem bound_opE [Countable β] (q : SubInstrument R R β) :
    ProgE.Bound Costed.weight (opE q) 1 fun _ => True := by
  rw [opE, ProgE.bound_costed]
  simp only [QProg.opE, QProg.op, ProgE.Bound]
  refine ⟨le_rfl, fun n => ?_⟩
  split <;> trivial

end QTreeT

/-! ## Costed quantum simulators -/

/-- A costed quantum simulator with state `σ` between the real interface (events `E`, outputs
`O`) and the ideal interface (events `EG`, outputs `OG`): its steps are costed quantum
computations on the environment register. -/
structure QSim.Timed (σ E O EG OG : Type) (d : ℕ) where
  /-- Initial simulator state. -/
  init : σ
  /-- Costed translation of a real event. -/
  pre : σ → E → QTreeT (Fin d) (σ × EG)
  /-- Costed translation of an ideal output. -/
  post : σ → OG → QTreeT (Fin d) (σ × O)

namespace QSim.Timed

variable {σ σ' E O EG OG : Type} {d : ℕ}

/-- The erasure of a costed simulator: the simulator of the erased steps. -/
noncomputable def erase (T : QSim.Timed σ E O EG OG d) : QSim σ E O EG OG d where
  init := T.init
  pre s e := (T.pre s e).erase
  post s o := (T.post s o).erase

/-- `T.Erases ε S`: the steps of the simulator `S` are the erased steps of `T`, with the costed
state mapped to the state of `S` by `ε`. -/
def Erases (T : QSim.Timed σ' E O EG OG d) (ε : σ' → σ) (S : QSim σ E O EG OG d) : Prop :=
  ε T.init = S.init ∧
    (∀ s e, (T.erase.pre s e).bind (fun y => SubInstrument.pure (ε y.1, y.2)) = S.pre (ε s) e) ∧
    ∀ s o, (T.erase.post s o).bind (fun y => SubInstrument.pure (ε y.1, y.2)) = S.post (ε s) o

/-- A costed simulator erases to its erasure along the identity. -/
theorem erases_erase (T : QSim.Timed σ E O EG OG d) : T.Erases _root_.id T.erase :=
  ⟨rfl, fun _ _ => SubInstrument.bind_pure _, fun _ _ => SubInstrument.bind_pure _⟩

/-- The time bound of a costed simulator on the states of the invariant `Inv`: the initial
state satisfies `Inv`, and from a state of `Inv` a `pre` step costs at most `a`, a `post` step at
most `b`, both returning states of `Inv`. -/
def TimeBound (T : QSim.Timed σ E O EG OG d) (Inv : σ → Prop) (a b : ℕ) : Prop :=
  Inv T.init ∧
    (∀ s e, Inv s → ProgE.Bound Costed.weight (T.pre s e) a fun y => Inv y.1) ∧
    ∀ s o, Inv s → ProgE.Bound Costed.weight (T.post s o) b fun y => Inv y.1

/-- A time bound is a time bound of all larger times. -/
theorem TimeBound.mono {T : QSim.Timed σ E O EG OG d} {Inv : σ → Prop} {a b a' b' : ℕ}
    (h : T.TimeBound Inv a b) (ha : a ≤ a') (hb : b ≤ b') : T.TimeBound Inv a' b' :=
  ⟨h.1, fun s e hs => (h.2.1 s e hs).mono ha fun _ h => h,
    fun s o hs => (h.2.2 s o hs).mono hb fun _ h => h⟩

end QSim.Timed

/-- A costed quantum simulator with a private register `M`: its steps are costed quantum
computations on the environment register and `M`. -/
structure QSimQ.Timed (M : Type) [Fintype M] (σ E O EG OG : Type) (d : ℕ) where
  /-- Initial simulator state. -/
  init : σ
  /-- Initial basis state of the simulator register. -/
  initReg : M
  /-- Costed translation of a real event. -/
  pre : σ → E → QTreeT (Fin d × M) (σ × EG)
  /-- Costed translation of an ideal output. -/
  post : σ → OG → QTreeT (Fin d × M) (σ × O)

namespace QSimQ.Timed

variable {M : Type} [Fintype M] {σ σ' E O EG OG : Type} {d : ℕ}

/-- The erasure of a costed simulator with a private register. -/
noncomputable def erase (T : QSimQ.Timed M σ E O EG OG d) : QSimQ M σ E O EG OG d where
  init := T.init
  initReg := T.initReg
  pre s e := (T.pre s e).erase
  post s o := (T.post s o).erase

/-- `T.Erases ε S`: the steps of `S` are the erased steps of `T`, with the costed state mapped
by `ε`, from the same initial basis state of the register. -/
def Erases (T : QSimQ.Timed M σ' E O EG OG d) (ε : σ' → σ) (S : QSimQ M σ E O EG OG d) :
    Prop :=
  ε T.init = S.init ∧ T.initReg = S.initReg ∧
    (∀ s e, (T.erase.pre s e).bind (fun y => SubInstrument.pure (ε y.1, y.2)) = S.pre (ε s) e) ∧
    ∀ s o, (T.erase.post s o).bind (fun y => SubInstrument.pure (ε y.1, y.2)) = S.post (ε s) o

/-- The time bound of a costed simulator with a private register on the states of `Inv`. -/
def TimeBound (T : QSimQ.Timed M σ E O EG OG d) (Inv : σ → Prop) (a b : ℕ) : Prop :=
  Inv T.init ∧
    (∀ s e, Inv s → ProgE.Bound Costed.weight (T.pre s e) a fun y => Inv y.1) ∧
    ∀ s o, Inv s → ProgE.Bound Costed.weight (T.post s o) b fun y => Inv y.1

end QSimQ.Timed

end CatCrypt.Quantum.ReactiveUC

namespace CatCrypt.Crypto.Party

open CatCrypt.Core _root_.Quantum CatCrypt.Quantum.ReactiveUC

namespace QProg

variable {R : Type} [Fintype R] {E O EG OG σ : Type} {d : ℕ}

/-! ## The costed step of a loop -/

/-- The costed step of the loop of the costed body `bodyT`: an activation of the costed residual
program as a costed quantum computation, restarting with `bodyT s` on a return of `s`. -/
def loopStepT (bodyT : σ → ProgE (Costed (SubInstrument R R ℕ)) E O σ)
    (p : ProgE (Costed (SubInstrument R R ℕ)) E O σ) (e : E) :
    QTreeT R (ProgE (Costed (SubInstrument R R ℕ)) E O σ × O) :=
  ProgE.stepWith ProgE.treeHandler (fun s e => ProgE.act ProgE.treeHandler (bodyT s) e) p e

/-- **Erasure of the costed loop step.** The erased costed step, its residual erased, is the
step of the loop of the erased body at the erased residual. -/
theorem loopStepT_erase (bodyT : σ → ProgE (Costed (SubInstrument R R ℕ)) E O σ) (s₀ : σ)
    (p : ProgE (Costed (SubInstrument R R ℕ)) E O σ) (e : E) :
    (loopStepT bodyT p e).erase.bind (fun x => SubInstrument.pure (ProgE.erase x.1, x.2)) =
      (loopQSys (fun s => ProgE.erase (bodyT s)) s₀).step (ProgE.erase p) e := by
  have hr : ∀ s e', QProg.handler.bind
      (ProgE.runTree QProg.handler.ticked (ProgE.act ProgE.treeHandler (bodyT s) e'))
      (fun x => QProg.handler.pure (ProgE.erase x.1, x.2)) =
        ProgE.act QProg.handler (ProgE.erase (bodyT s)) e' := fun s e' => by
    rw [ProgE.act, ProgE.runTree_stepWith]
    exact ProgE.act_erase QProg.handler QProg.handler_lawful (bodyT s) e'
  have h := ProgE.stepWith_erase QProg.handler QProg.handler_lawful _ _ hr p e
  rw [← ProgE.runTree_stepWith] at h
  exact h

/-- **Time of the costed loop step.** When every iteration of the body from a state of `Inv`
costs at most `a` and returns states of `Inv`, the costed step from a residual of remaining
cost at most `a` costs at most `a + a` and returns residuals of remaining cost at most `a`. -/
theorem loopStepT_time {w : Costed (SubInstrument R R ℕ) → ℕ}
    {bodyT : σ → ProgE (Costed (SubInstrument R R ℕ)) E O σ} {Inv : σ → Prop} {a : ℕ}
    (hbody : ∀ s, Inv s → ProgE.Bound w (bodyT s) a Inv)
    (p : ProgE (Costed (SubInstrument R R ℕ)) E O σ) (hp : ProgE.Bound w p a Inv) (e : E) :
    ProgE.Bound w (loopStepT bodyT p e) (a + a) fun y => ProgE.Bound w y.1 a Inv := by
  have hs : ∀ (o : O) (q : ProgE (Costed (SubInstrument R R ℕ)) E O σ) (u : ℕ), u ≤ a →
      ProgE.Bound w q u Inv →
        ProgE.Bound w (ProgE.treeHandler.pure (q, o) :
          ProgE (Costed (SubInstrument R R ℕ)) Empty Empty _) 0
          fun y => ProgE.Bound w y.1 a Inv :=
    fun o q u hu hq => hq.mono hu fun _ => id
  have hA : ∀ s, Inv s → ProgE.Bound w
      (ProgE.act ProgE.treeHandler (bodyT s) e : QTreeT R _) (a + 0)
      fun y => ProgE.Bound w y.1 a Inv := fun s hs' =>
    ProgE.bound_awaitK_tree e (fun o q => ProgE.treeHandler.pure (q, o))
      (fun _ => ProgE.treeHandler.fail) (fun _ => ProgE.treeHandler.fail) hs
      (fun _ _ => trivial) (fun _ _ => trivial) (bodyT s) a le_rfl (hbody s hs')
  exact ProgE.bound_awaitK_tree e (fun o q => ProgE.treeHandler.pure (q, o))
    (fun s => ProgE.act ProgE.treeHandler (bodyT s) e) (fun _ => ProgE.treeHandler.fail)
    (fun o q u hu hq => (hs o q u hu hq).mono (Nat.zero_le _) fun _ h => h) hA
    (fun _ _ => trivial) p a le_rfl hp

/-- The costed step of a loop simulator: the costed loop step on an event, an output on the
side `pick` continuing with its value and an output on the other side failing. -/
def loopSimStepT {X Y Z : Type} (bodyT : σ → ProgE (Costed (SubInstrument R R ℕ)) X (Y ⊕ Z) σ)
    (p : ProgE (Costed (SubInstrument R R ℕ)) X (Y ⊕ Z) σ) (x : X) (pick : Y ⊕ Z → Option O) :
    QTreeT R (ProgE (Costed (SubInstrument R R ℕ)) X (Y ⊕ Z) σ × O) :=
  (loopStepT bodyT p x).bind fun y =>
    match pick y.2 with
    | some o => .ret (y.1, o)
    | none => .fail

/-- Erasure of the costed step of a loop simulator. -/
theorem loopSimStepT_erase {X Y Z : Type}
    (bodyT : σ → ProgE (Costed (SubInstrument R R ℕ)) X (Y ⊕ Z) σ) (s₀ : σ)
    (p : ProgE (Costed (SubInstrument R R ℕ)) X (Y ⊕ Z) σ) (x : X) (pick : Y ⊕ Z → Option O) :
    (loopSimStepT bodyT p x pick).erase.bind
        (fun y => SubInstrument.pure (ProgE.erase y.1, y.2)) =
      ((loopQSys (fun s => ProgE.erase (bodyT s)) s₀).step (ProgE.erase p) x).bind fun y =>
        match pick y.2 with
        | some o => SubInstrument.pure (y.1, o)
        | none => SubInstrument.fail := by
  rw [← loopStepT_erase bodyT s₀ p x, loopSimStepT, QTreeT.erase_bind, SubInstrument.bind_assoc,
    SubInstrument.bind_assoc]
  congr 1
  funext y
  rw [SubInstrument.pure_bind]
  cases pick y.2 <;> simp

/-- Time of the costed step of a loop simulator. -/
theorem loopSimStepT_time {X Y Z : Type} {w : Costed (SubInstrument R R ℕ) → ℕ}
    {bodyT : σ → ProgE (Costed (SubInstrument R R ℕ)) X (Y ⊕ Z) σ} {Inv : σ → Prop} {a : ℕ}
    (hbody : ∀ s, Inv s → ProgE.Bound w (bodyT s) a Inv)
    (p : ProgE (Costed (SubInstrument R R ℕ)) X (Y ⊕ Z) σ) (hp : ProgE.Bound w p a Inv) (x : X)
    (pick : Y ⊕ Z → Option O) :
    ProgE.Bound w (loopSimStepT bodyT p x pick) (2 * a) fun y => ProgE.Bound w y.1 a Inv := by
  unfold loopSimStepT
  rw [two_mul, ← Nat.add_zero (a + a)]
  refine ProgE.Bound.bind ((loopStepT_time hbody p hp x).mono le_rfl fun y hy => ?_)
  split
  · exact hy
  · trivial

/-! ## The costed loop simulators -/

/-- **The costed loop simulator.** The costed form of `loopQSim body s₀` for a costed body
`bodyT`: its state is the costed residual program, its steps are the costed loop steps. -/
def loopQSim.timed (bodyT : σ → ProgE (Costed (SubInstrument (Fin d) (Fin d) ℕ)) (E ⊕ OG)
    (EG ⊕ O) σ) (s₀ : σ) :
    QSim.Timed (ProgE (Costed (SubInstrument (Fin d) (Fin d) ℕ)) (E ⊕ OG) (EG ⊕ O) σ) E O EG OG
      d where
  init := .ret s₀
  pre t e := loopSimStepT bodyT t (.inl e) (Sum.elim some fun _ => none)
  post t o := loopSimStepT bodyT t (.inr o) (Sum.elim (fun _ => none) some)

/-- **Erasure of the costed loop simulator.** It erases, along the erasure of residual
programs, to the loop simulator of the erased body. -/
theorem loopQSim.erase_timed
    (bodyT : σ → ProgE (Costed (SubInstrument (Fin d) (Fin d) ℕ)) (E ⊕ OG) (EG ⊕ O) σ)
    (s₀ : σ) :
    (loopQSim.timed bodyT s₀).Erases ProgE.erase
      (loopQSim (fun s => ProgE.erase (bodyT s)) s₀) := by
  refine ⟨rfl, fun t e => ?_, fun t o => ?_⟩
  · refine (loopSimStepT_erase bodyT s₀ t (.inl e) _).trans ?_
    congr 1
    funext y
    rcases y with ⟨q, g | o⟩ <;> rfl
  · refine (loopSimStepT_erase bodyT s₀ t (.inr o) _).trans ?_
    congr 1
    funext y
    rcases y with ⟨q, g | o⟩ <;> rfl

/-- **Running time of the costed loop simulator.** When every iteration of the body from a
state of `Inv` costs at most `a` and returns states of `Inv`, and `s₀` satisfies `Inv`, each step
costs at most `2 * a` from a residual of remaining cost at most `a`. -/
theorem loopQSim.timeBound_timed
    {bodyT : σ → ProgE (Costed (SubInstrument (Fin d) (Fin d) ℕ)) (E ⊕ OG) (EG ⊕ O) σ}
    {s₀ : σ} {Inv : σ → Prop} {a : ℕ} (hs₀ : Inv s₀)
    (hbody : ∀ s, Inv s → ProgE.Bound Costed.weight (bodyT s) a Inv) :
    (loopQSim.timed bodyT s₀).TimeBound (fun p => ProgE.Bound Costed.weight p a Inv) (2 * a)
      (2 * a) :=
  ⟨hs₀, fun t e ht => loopSimStepT_time hbody t ht (.inl e) _,
    fun t o ht => loopSimStepT_time hbody t ht (.inr o) _⟩

section Private

variable {M : Type} [Fintype M]

/-- The costed loop simulator with a private register `M` started in the basis state `m₀`. -/
def loopQSimQ.timed
    (bodyT : σ → ProgE (Costed (SubInstrument (Fin d × M) (Fin d × M) ℕ)) (E ⊕ OG) (EG ⊕ O) σ)
    (s₀ : σ) (m₀ : M) :
    QSimQ.Timed M (ProgE (Costed (SubInstrument (Fin d × M) (Fin d × M) ℕ)) (E ⊕ OG) (EG ⊕ O) σ)
      E O EG OG d where
  init := .ret s₀
  initReg := m₀
  pre t e := loopSimStepT bodyT t (.inl e) (Sum.elim some fun _ => none)
  post t o := loopSimStepT bodyT t (.inr o) (Sum.elim (fun _ => none) some)

/-- Erasure of the costed loop simulator with a private register. -/
theorem loopQSimQ.erase_timed
    (bodyT : σ → ProgE (Costed (SubInstrument (Fin d × M) (Fin d × M) ℕ)) (E ⊕ OG) (EG ⊕ O) σ)
    (s₀ : σ) (m₀ : M) :
    (loopQSimQ.timed bodyT s₀ m₀).Erases ProgE.erase
      (loopQSimQ (fun s => ProgE.erase (bodyT s)) s₀ m₀) := by
  refine ⟨rfl, rfl, fun t e => ?_, fun t o => ?_⟩
  · refine (loopSimStepT_erase bodyT s₀ t (.inl e) _).trans ?_
    congr 1
    funext y
    rcases y with ⟨q, g | o⟩ <;> rfl
  · refine (loopSimStepT_erase bodyT s₀ t (.inr o) _).trans ?_
    congr 1
    funext y
    rcases y with ⟨q, g | o⟩ <;> rfl

/-- Running time of the costed loop simulator with a private register: each step costs at most
`2 * a` when every iteration of the body costs at most `a`. -/
theorem loopQSimQ.timeBound_timed
    {bodyT : σ → ProgE (Costed (SubInstrument (Fin d × M) (Fin d × M) ℕ)) (E ⊕ OG) (EG ⊕ O) σ}
    {s₀ : σ} {m₀ : M} {Inv : σ → Prop} {a : ℕ} (hs₀ : Inv s₀)
    (hbody : ∀ s, Inv s → ProgE.Bound Costed.weight (bodyT s) a Inv) :
    (loopQSimQ.timed bodyT s₀ m₀).TimeBound (fun p => ProgE.Bound Costed.weight p a Inv) (2 * a)
      (2 * a) :=
  ⟨hs₀, fun t e ht => loopSimStepT_time hbody t ht (.inl e) _,
    fun t o ht => loopSimStepT_time hbody t ht (.inr o) _⟩

end Private

end QProg

end CatCrypt.Crypto.Party
