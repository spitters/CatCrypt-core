/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.KEMAdvGeneral
public import CatCryptCore.Quantum.QRealizesMem

/-!
# Multi-round QROM adversaries as environments of a quantum reactive system

A general multi-round adversary `QAdvMRGen` is an environment `QStrat` over the event alphabet
`QROMEvent c` (a quantum query or a classical round with a measured message) and the output
alphabet `QROMOut a` (the end of a query or the classical answer of a round). The random oracle
and the answer function of the rounds form a quantum reactive system `QSys`. The adaptive
challenger `chal` keeps a classical state that selects the oracle of each query and the answer of
each round and that moves at every round; the fixed pair `(H, f)` of `prOutMRGen` is the
challenger `fixedSys H f` with constant state.

The adversary is flattened into a list of instructions `MRInstr`, each a local operation followed
by a query or by a classical round. The environment `progStrat l` runs the list `l`, one
instruction per activation; the operation after the last event and the final measurement are the
post-processing of `QStratAcc`, an environment with an initial state and an acceptance
measurement. `viewAcc S G` is the probability that `G` accepts against `S`.

## Main definitions

* `QROMEvent`, `QROMOut` — the events and outputs of the QROM interface
* `chal`, `fixedSys` — the classical adaptive challenger and the challenger of a fixed oracle
  and a fixed answer function
* `MRInstr`, `progStrat`, `mrInstrs`, `mrLast` — instruction lists and their environments
* `QStratAcc`, `viewAcc` — environments with an initial state and an acceptance measurement
* `QAdvMRGen.toStrat` — a general multi-round adversary as such an environment

## Main results

* `qview_fixedSys_progStrat` — the view of an instruction list against `fixedSys H f` is the
  direct run `progRun` of the list with the oracle `O_H` and the answers `f`
* `mrChainG_eq_progRun` — the multi-round chain of `QAdvMRGen` is the direct run of its
  instruction list, followed by its last local operation
* `prOutMRGen_eq_view` — the acceptance probability of `A` against `(H, f)` is its acceptance
  probability as an environment of `fixedSys H f`
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.UnitaryChannel
open _root_.Quantum CatCrypt.Quantum.ReactiveUC

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## The QROM interface -/

/-- The events of the QROM interface: a quantum query to the oracle or a classical round with
the measured message `y`. -/
inductive QROMEvent (c : ℕ) where
  /-- A quantum query on the query part of the register. -/
  | query
  /-- A classical round with message `y`. -/
  | round (y : Fin c)

/-- The outputs of the QROM interface: the end of a query or the answer `x` of a round. -/
inductive QROMOut (a : ℕ) where
  /-- The end of a query. -/
  | done
  /-- The classical answer of a round. -/
  | answer (x : Fin a)

/-! ## Challengers -/

section Sys

variable {m n w c a : ℕ} [NeZero n] {τ : Type}

/-- One activation of the classical adaptive challenger at state `t`: a query applies the
standard oracle of `orc t`; a round with message `y` answers `ans t y` and moves to
`nxt t y`. -/
def chalStep (orc : τ → Fin m → Fin n) (ans : τ → Fin c → Fin a) (nxt : τ → Fin c → τ)
    (t : τ) : QROMEvent c → CPComp (m * n * w) (τ × QROMOut a)
  | .query => CPComp.qbind (CPComp.unitary (oracleU m n w (orc t))) fun _ =>
      CPComp.qpure (t, .done)
  | .round y => CPComp.qpure (nxt t y, .answer (ans t y))

/-- The classical adaptive challenger: no private register, classical state `τ` started at
`t₀`, the oracle `orc t` at each query and the answer `ans t y` at each round, after which the
state moves to `nxt t y`. -/
def chal (t₀ : τ) (orc : τ → Fin m → Fin n) (ans : τ → Fin c → Fin a) (nxt : τ → Fin c → τ) :
    QSys Unit τ (QROMEvent c) (QROMOut a) (m * n * w) where
  init := t₀
  initReg := ()
  step t e := relabel (Equiv.prodPUnit _).symm (chalStep orc ans nxt t e)

/-- The challenger of the fixed oracle `H` and the fixed answer function `f`: the adaptive
challenger with constant state. -/
def fixedSys (H : Fin m → Fin n) (f : Fin c → Fin a) :
    QSys Unit Unit (QROMEvent c) (QROMOut a) (m * n * w) :=
  chal () (fun _ => H) (fun _ => f) (fun _ _ => ())

end Sys

/-! ## Instruction lists -/

section Prog

variable {d c a : ℕ}

/-- One instruction of a flattened multi-round adversary: a local operation followed by a
query, or a local operation followed by the classical round `R`. -/
inductive MRInstr (d c a : ℕ) where
  /-- The local operation `U`, then a query. -/
  | query (U : CPComp d Unit)
  /-- The local operation `U`, then the round `R`. -/
  | round (U : CPComp d Unit) (R : ClassicalRound d c a)

/-- The projectors of a round satisfy the completeness relation. -/
theorem ClassicalRound.P_complete (R : ClassicalRound d c a) :
    ∑ y, (R.P y)ᴴ * R.P y = 1 := by
  simp only [R.P_conjTranspose, R.P_mul_self, R.P_sum]

/-- The measurement of the message of a round. -/
def roundMeas (R : ClassicalRound d c a) : CPComp d (Fin c) :=
  CPComp.ofKraus R.P R.P_complete

/-- The choice of the next event by an instruction list: the local operation of the head
instruction, then a query, or the measurement of the message of its round. The list is kept;
`progObs` removes the head. -/
def progNext : List (MRInstr d c a) → CPComp d (List (MRInstr d c a) × QROMEvent c)
  | [] => CPComp.qpure ([], .query)
  | .query U :: l => CPComp.qbind U fun _ => CPComp.qpure (.query U :: l, .query)
  | .round U R :: l => CPComp.qbind U fun _ => CPComp.qbind (roundMeas R) fun y =>
      CPComp.qpure (.round U R :: l, .round y)

/-- The observation of an output by an instruction list: the answer unitary of the head round
on an answer, and the removal of the head instruction. -/
def progObs : List (MRInstr d c a) → QROMOut a → CPComp d (List (MRInstr d c a))
  | [], _ => CPComp.qpure []
  | .round _ R :: l, .answer x => CPComp.qbind (CPComp.unitary (R.ans x)) fun _ => CPComp.qpure l
  | _ :: l, _ => CPComp.qpure l

/-- The environment that runs the instruction list `l`, one instruction per activation. -/
def progStrat (l : List (MRInstr d c a)) :
    QStrat (List (MRInstr d c a)) (QROMEvent c) (QROMOut a) d where
  rounds := l.length
  init := l
  next := progNext
  obs := progObs

/-- The direct run of an instruction list with the oracle `O` and the answer function `f`. -/
def progRun (O : CPComp d Unit) (f : Fin c → Fin a) : List (MRInstr d c a) → CPComp d Unit
  | [] => CPComp.qpure ()
  | .query U :: l => CPComp.qbind U fun _ => CPComp.qbind O fun _ => progRun O f l
  | .round U R :: l => CPComp.qbind U fun _ => CPComp.qbind (roundMeas R) fun y =>
      CPComp.qbind (CPComp.unitary (R.ans (f y))) fun _ => progRun O f l

/-- The direct run of a concatenation is the run of the first list followed by the run of the
second. -/
theorem progRun_append (O : CPComp d Unit) (f : Fin c → Fin a) (l₁ l₂ : List (MRInstr d c a)) :
    progRun O f (l₁ ++ l₂) = CPComp.qbind (progRun O f l₁) fun _ => progRun O f l₂ := by
  induction l₁ with
  | nil => simp only [List.nil_append, progRun, CPComp.qpure_qbind]
  | cons i l ih =>
    cases i <;> simp only [List.cons_append, progRun, ih, CPComp.qbind_assoc]

/-- The instructions of a segment `U₀ ; O ; U₁ ; … ; O ; U_q`: one query instruction per
operation but the last. -/
def segInstrs : (q : ℕ) → (Fin (q + 1) → CPComp d Unit) → List (MRInstr d c a)
  | 0, _ => []
  | q + 1, U => .query (U 0) :: segInstrs q (Fin.tail U)

variable {q : ℕ}

/-- The instructions of `head ; (round ; segment)ᵏ`: the instructions of each segment, the last
operation of a segment followed by the next round. -/
def mrInstrs : (k : ℕ) → (Fin (q + 1) → CPComp d Unit) → (Fin k → Fin (q + 1) → CPComp d Unit) →
    (Fin k → ClassicalRound d c a) → List (MRInstr d c a)
  | 0, head, _, _ => segInstrs q head
  | k + 1, head, tail, R =>
    segInstrs q head ++ MRInstr.round (head (Fin.last q)) (R 0) ::
      mrInstrs k (tail 0) (Fin.tail tail) (Fin.tail R)

/-- The last local operation of `head ; (round ; segment)ᵏ`. -/
def mrLast : (k : ℕ) → (Fin (q + 1) → CPComp d Unit) → (Fin k → Fin (q + 1) → CPComp d Unit) →
    CPComp d Unit
  | 0, head, _ => head (Fin.last q)
  | k + 1, _, tail => mrLast k (tail 0) (Fin.tail tail)

end Prog

/-! ## Environments with an acceptance measurement -/

/-- An environment together with the initial state of its register and an acceptance
measurement applied to the register after the run, depending on the final environment
state. -/
structure QStratAcc (ζ E O : Type) (d : ℕ) where
  /-- The environment. -/
  strat : QStrat ζ E O d
  /-- The initial state of the register. -/
  init : DensityMatrix d
  /-- The acceptance measurement after the run. -/
  post : ζ → CPComp d Bool

/-- The probability that the environment `G` accepts against the system `S`. -/
def viewAcc {H τ ζ E O : Type} [Fintype H] [DecidableEq H] {d : ℕ} (S : QSys H τ E O d)
    (G : QStratAcc ζ E O d) : ℝ≥0∞ :=
  CPComp.prTrue (CPComp.qbind (qview S G.strat) G.post) G.init

/-! ## The view against the fixed challenger -/

section Fixed

variable {m n w c a : ℕ} [NeZero n]

/-- The run of an instruction list against the fixed challenger is its direct run, placed
beside the one-point private register. -/
theorem qloop_fixedSys (H : Fin m → Fin n) (f : Fin c → Fin a)
    (l₀ : List (MRInstr (m * n * w) c a)) :
    ∀ l : List (MRInstr (m * n * w) c a),
      qloop (fixedSys (w := w) H f) (progStrat l₀) l.length (l, ()) =
        relabel (Equiv.prodPUnit _).symm
          (CPComp.qbind (progRun (CPComp.unitary (oracleU m n w H)) f l) fun _ =>
            CPComp.qpure ([], ())) := by
  intro l
  induction l with
  | nil =>
    simp only [List.length_nil, qloop, progRun, CPComp.qpure_qbind]
    exact (relabel_pure _ _).symm
  | cons i l ih =>
    have hS : ∀ t e, (fixedSys (w := w) H f).step t e =
        relabel (Equiv.prodPUnit _).symm (chalStep (fun _ => H) (fun _ => f) (fun _ _ => ()) t e) :=
      fun _ _ => rfl
    have hn : (progStrat l₀).next = progNext := rfl
    have ho : (progStrat l₀).obs = progObs := rfl
    simp only [CPComp.qbind, CPComp.qpure, relabel_bind, relabel_pure] at ih
    cases i <;>
    simp only [List.length_cons, qloop, hS, hn, ho, progNext, progObs, chalStep, progRun, ih,
      frame_unit, CPComp.qbind, CPComp.qpure, relabel_bind, relabel_pure,
      SubInstrument.bind_assoc, SubInstrument.pure_bind]

/-- The view of an instruction list against the fixed challenger is its direct run. -/
theorem qview_fixedSys_progStrat (H : Fin m → Fin n) (f : Fin c → Fin a)
    (l : List (MRInstr (m * n * w) c a)) :
    qview (fixedSys (w := w) H f) (progStrat l) =
      CPComp.qbind (progRun (CPComp.unitary (oracleU m n w H)) f l) fun _ => CPComp.qpure [] := by
  unfold qview
  rw [show (progStrat l).rounds = l.length from rfl, show (progStrat l).init = l from rfl,
    show (fixedSys (w := w) H f).init = () from rfl,
    show (fixedSys (w := w) H f).initReg = () from rfl, qloop_fixedSys, appendBasis_unit_discard]
  simp only [CPComp.qbind, CPComp.qpure, SubInstrument.bind_assoc, SubInstrument.pure_bind]

end Fixed

/-! ## The multi-round chain as a direct run -/

section Chain

variable {d c a q : ℕ}

/-- The round measurement followed by the answer unitary of the measured message is the round
instrument with its outcome discarded. -/
theorem toQComp_roundMeas_unitary (R : ClassicalRound d c a) (f : Fin c → Fin a) :
    (CPComp.qbind (roundMeas R) fun y => CPComp.unitary (R.ans (f y))).toQComp = roundU R f := by
  refine QComp.ext_fun fun u ρ => ?_
  cases u
  rw [roundU_branch, CPComp.toQComp_qbind, qbind_branch_apply, tsum_fintype]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [roundMeas, CPComp.toQComp_ofKraus, CPComp.toQComp_unitary,
    unitaryChannel_branch_apply, QComp.ofKraus_branch, conjTranspose_mul, Matrix.mul_assoc]

/-- A segment is the direct run of its instructions followed by its last operation. -/
theorem chainG_eq_progRun (O : CPComp d Unit) (f : Fin c → Fin a) :
    ∀ (q : ℕ) (U : Fin (q + 1) → CPComp d Unit),
      chainG O.toQComp q (fun i => (U i).toQComp) =
        (CPComp.qbind (progRun O f (segInstrs (c := c) (a := a) q U)) fun _ =>
          U (Fin.last q)).toQComp := by
  intro q
  induction q with
  | zero =>
    intro U
    simp only [chainG, segInstrs, progRun, CPComp.qpure_qbind]
    rfl
  | succ q ih =>
    intro U
    have ht : (Fin.tail fun i => (U i).toQComp) = fun i => (Fin.tail U i).toQComp := rfl
    simp only [chainG, ht, ih (Fin.tail U), ← CPComp.toQComp_qbind]
    congr 1
    simp only [segInstrs, progRun, CPComp.qbind_assoc, Fin.tail, Fin.succ_last]

/-- The multi-round chain is the direct run of its instructions followed by its last
operation. -/
theorem mrChainG_eq_progRun (O : CPComp d Unit) (f : Fin c → Fin a) :
    ∀ (k : ℕ) (head : Fin (q + 1) → CPComp d Unit) (tail : Fin k → Fin (q + 1) → CPComp d Unit)
      (R : Fin k → ClassicalRound d c a),
      mrChainG O.toQComp f k q (fun i => (head i).toQComp) (fun j i => (tail j i).toQComp) R =
        (CPComp.qbind (progRun O f (mrInstrs k head tail R)) fun _ =>
          mrLast k head tail).toQComp := by
  intro k
  induction k with
  | zero =>
    intro head tail R
    exact chainG_eq_progRun O f q head
  | succ k ih =>
    intro head tail R
    have ht : (Fin.tail fun j i => (tail j i).toQComp) =
        fun j i => (Fin.tail tail j i).toQComp := rfl
    simp only [mrChainG, chainG_eq_progRun O f q head, ← toQComp_roundMeas_unitary (R 0) f, ht,
      ih (tail 0) (Fin.tail tail) (Fin.tail R), ← CPComp.toQComp_qbind]
    congr 1
    simp only [mrInstrs, mrLast, progRun_append, progRun, CPComp.qbind_assoc]

end Chain

/-! ## General multi-round adversaries as environments -/

section Adv

variable {m n w q k c a : ℕ}

/-- The final measurement of `A` as a completely positive instrument. -/
def QAdvMRGen.measureCP (A : QAdvMRGen m n w q k c a) : CPComp (m * n * w) Bool :=
  CPComp.mk' A.measure fun b => by
    cases b
    · exact isCPMap_conj (1 - A.final) _ fun _ => rfl
    · exact isCPMap_conj A.final _ fun _ => rfl

/-- The adversary `A` as an environment of the QROM interface: the instruction list of its
segments and rounds, its initial state, and as acceptance measurement its last local
operation followed by its final measurement. -/
def QAdvMRGen.toStrat (A : QAdvMRGen m n w q k c a) :
    QStratAcc (List (MRInstr (m * n * w) c a)) (QROMEvent c) (QROMOut a) (m * n * w) where
  strat := progStrat (mrInstrs k (A.seg 0) (Fin.tail A.seg) A.rounds)
  init := A.init
  post _ := CPComp.qbind (mrLast k (A.seg 0) (Fin.tail A.seg)) fun _ => A.measureCP

variable [NeZero n]

/-- **Embedding of the fixed-oracle model.** The acceptance probability of `A` with the oracle
`H` and the answer function `f` is the acceptance probability of `A` as an environment of the
fixed challenger `fixedSys H f`. -/
theorem prOutMRGen_eq_view (A : QAdvMRGen m n w q k c a) (H : Fin m → Fin n)
    (f : Fin c → Fin a) : prOutMRGen A H f = viewAcc (fixedSys H f) A.toStrat := by
  have hO : oracleQ m n w H = (CPComp.unitary (oracleU m n w H)).toQComp :=
    (CPComp.toQComp_unitary _).symm
  have hM : A.measure = A.measureCP.toQComp := (CPComp.toQComp_mk' _ _).symm
  unfold prOutMRGen viewAcc runMRGen
  rw [CPComp.prTrue_def, QAdvMRGen.toStrat, qview_fixedSys_progStrat, hO, hM,
    mrChainG_eq_progRun, ← CPComp.toQComp_qbind]
  congr 2
  simp only [CPComp.qbind_assoc, CPComp.qpure_qbind]

end Adv

end CatCrypt.Quantum.QROM
