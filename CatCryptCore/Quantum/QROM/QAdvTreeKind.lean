/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.HandlerCost
public import CatCryptCore.Quantum.QROM.MultiRound
public import CatCryptCore.Tactics.DeriveTimedStructure

/-!
# QROM circuit adversaries as tree kinds of `derive_timed`

The QROM adversaries `QAdv m n w q` (the chain `U₀ ; O ; U₁ ; ⋯ ; O ; U_q`) and
`QAdvMR m n w q k c a` (`k + 1` such segments with `k` classical rounds between them) are
registered as tree kinds of `CatCryptCore.Tactics.DeriveTimed`, so that `derive_timed`,
`derive_timed_structure` and `derive_reduction` price reductions that build circuit adversaries
and structures with circuit fields.

The costed circuit `QAdvT m n w q` is a gate set `S` with the costed circuit
`QAdv.Timed S q` of `CatCryptCore.Complexity.HandlerCost` (a word of gates for each unitary) and
the projector laws of its final projector; its erasure multiplies each word out. Its time is
the gate time of its words plus one unit per oracle call (`QAdv.Timed.time` at handler cost
`0`). The costed multi-round circuit `QAdvMRT` has a word of gates for each unitary of each
segment; its time is the gate time plus one unit per oracle call and one per classical round.

The circuit kind has the combinator `absorbOracle`, whose costed form `QAdvT.absorb` adds the
oracle unitary to the gate set as one gate of weight one, so that absorbing the oracle keeps
the time (`QAdvT.time_absorb`). A circuit given by a constant or a constructor application has
no node and is refused; in a reduction it is a binder or a field of a binder, priced by its cost
companion.

Search words: quantum circuit tree kind, costed circuit, QROM adversary, gate word, oracle
absorption, derive_timed, time certificate, quantum reduction.

## Main definitions

* `QAdvT`, `QAdvT.erase`, `QAdvT.time`, `QAdvT.StepTimeBound`, `QAdvT.absorb`
* `QAdvMRT`, `QAdvMRT.erase`, `QAdvMRT.time`, `QAdvMRT.StepTimeBound`
* `qAdvKind`, `qAdvMRKind` — the tree kinds, registered by `register_tree_kind`

## Main results

* `QAdvT.erase_absorb` — erasure commutes with oracle absorption
* `QAdvT.time_absorb` — oracle absorption keeps the time
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CatCrypt.Quantum.QROM

open CatCrypt.Complexity.HandlerCost Matrix

/-! ## Costed single-run circuits -/

/-- A costed circuit with the parameters of `QAdv m n w q`: a gate set, a word of gates for each
unitary of the chain, the initial state, and the final projector with its projector laws. -/
structure QAdvT (m n w q : ℕ) : Type 1 where
  /-- The gate set of the words. -/
  S : GateSet (m * n * w)
  /-- The words of gates, the initial state and the final projector. -/
  circ : QAdv.Timed S q
  /-- The final projector is self-adjoint. -/
  final_conjTranspose : circ.finalᴴ = circ.final
  /-- The final projector is idempotent. -/
  final_mul_self : circ.final * circ.final = circ.final

namespace QAdvT

variable {m n w q : ℕ}

/-- The circuit of a costed circuit: each word multiplied out. -/
def erase (A : QAdvT m n w q) : QAdv m n w q where
  U j := A.S.eval (A.circ.gates j)
  init := A.circ.init
  final := A.circ.final
  final_conjTranspose := A.final_conjTranspose
  final_mul_self := A.final_mul_self

/-- The time of a costed circuit: the gate time of its words plus one unit per oracle call. -/
def time (A : QAdvT m n w q) : ℕ := A.circ.time 0

/-- The step cost `c` added in front of a step-prefixed costed circuit. -/
def delay (c : ℕ) (x : ℕ × QAdvT m n w q) : ℕ × QAdvT m n w q := (c + x.1, x.2)

/-- `StepTimeBound x T`: the step cost of `x` followed by a run of its circuit takes time at
most `T`. -/
def StepTimeBound (x : ℕ × QAdvT m n w q) (T : ℕ) : Prop := x.1 + x.2.time ≤ T

/-- A step time bound holds at every larger time. -/
theorem StepTimeBound.mono {x : ℕ × QAdvT m n w q} {T T' : ℕ} (h : StepTimeBound x T)
    (hT : T ≤ T') : StepTimeBound x T' :=
  h.trans hT

/-- The gate set `S` with the unitary `u` added as one gate of weight one. -/
def withGate {d : ℕ} (S : GateSet d) (u : Matrix.unitaryGroup (Fin d) ℂ) : GateSet d where
  G := S.G ⊕ Unit
  den := Sum.elim S.den fun _ => u
  weight := Sum.elim S.weight fun _ => 1

/-- The costed form of `absorbOracle`: the oracle unitary of `G` is a gate of weight one, and
each oracle call of the chain is that gate. -/
def absorb [NeZero n] (A : QAdvT m n w q) (G : Fin m → Fin n) : QAdvT m n w 0 where
  S := withGate A.S (oracleU m n w G)
  circ :=
    { gates := fun _ => absorbWord [Sum.inr ()] q fun j => (A.circ.gates j).map Sum.inl
      init := A.circ.init
      final := A.circ.final }
  final_conjTranspose := A.final_conjTranspose
  final_mul_self := A.final_mul_self

/-- A word of `S` read in `withGate S u` multiplies out as in `S`. -/
theorem eval_map_inl {d : ℕ} (S : GateSet d) (u : Matrix.unitaryGroup (Fin d) ℂ)
    (l : List S.G) : (withGate S u).eval (l.map Sum.inl) = S.eval l := by
  simp [GateSet.eval, withGate, Function.comp_def]

/-- A word of `S` read in `withGate S u` has its cost in `S`. -/
theorem cost_map_inl {d : ℕ} (S : GateSet d) (u : Matrix.unitaryGroup (Fin d) ℂ)
    (l : List S.G) : (withGate S u).cost (l.map Sum.inl) = S.cost l := by
  simp [GateSet.cost, withGate, Function.comp_def]

/-- Erasure commutes with oracle absorption. -/
theorem erase_absorb [NeZero n] (A : QAdvT m n w q) (G : Fin m → Fin n) :
    (absorb A G).erase = absorbOracle A.erase G := by
  have h := QAdv.Timed.eval_absorbWord (S := withGate A.S (oracleU m n w G)) G [Sum.inr ()]
    (by simp [GateSet.eval, withGate]) q (fun j => (A.circ.gates j).map Sum.inl) A.erase.U
    (fun j => eval_map_inl _ _ _)
  simp only [erase, absorb, absorbOracle, h]

/-- Oracle absorption keeps the time: each oracle call becomes one gate of weight one. -/
theorem time_absorb [NeZero n] (A : QAdvT m n w q) (G : Fin m → Fin n) :
    (absorb A G).time = A.time := by
  simp only [time, QAdv.Timed.time, QAdv.Timed.gateTime, absorb]
  rw [QAdv.Timed.cost_absorbWord]
  simp [GateSet.cost, withGate]

/-- Erasure of a step-prefixed costed circuit commutes with `if`. -/
theorem erase_snd_ite (c : Prop) [Decidable c] (x y : ℕ × QAdvT m n w q) :
    (if c then x else y).2.erase = if c then x.2.erase else y.2.erase := by
  split <;> rfl

/-- Erasure of a step-prefixed costed circuit commutes with a dependent `if`. -/
theorem erase_snd_dite (c : Prop) [Decidable c] (x : c → ℕ × QAdvT m n w q)
    (y : ¬c → ℕ × QAdvT m n w q) :
    (if h : c then x h else y h).2.erase = if h : c then (x h).2.erase else (y h).2.erase := by
  split <;> rfl

/-- Erasure of a costed circuit commutes with `if`. -/
theorem erase_ite (c : Prop) [Decidable c] (x y : QAdvT m n w q) :
    (if c then x else y).erase = if c then x.erase else y.erase := by
  split <;> rfl

end QAdvT

/-! ## Costed multi-round circuits -/

/-- A costed multi-round circuit with the parameters of `QAdvMR m n w q k c a`: a gate set, a
word of gates for each unitary of each segment, the classical rounds, the initial state, and
the final projector with its projector laws. -/
structure QAdvMRT (m n w q k c a : ℕ) : Type 1 where
  /-- The gate set of the words. -/
  S : GateSet (m * n * w)
  /-- The words of gates of the unitaries of the segments. -/
  seg : Fin (k + 1) → Fin (q + 1) → List S.G
  /-- The rounds, round `j` between segments `j` and `j + 1`. -/
  rounds : Fin k → ClassicalRound (m * n * w) c a
  /-- The initial state. -/
  init : DensityMatrix (m * n * w)
  /-- The projector of the final measurement. -/
  final : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ
  /-- The final projector is self-adjoint. -/
  final_conjTranspose : finalᴴ = final
  /-- The final projector is idempotent. -/
  final_mul_self : final * final = final

namespace QAdvMRT

variable {m n w q k c a : ℕ}

/-- The multi-round circuit of a costed one: each word multiplied out. -/
def erase (A : QAdvMRT m n w q k c a) : QAdvMR m n w q k c a where
  seg i j := A.S.eval (A.seg i j)
  rounds := A.rounds
  init := A.init
  final := A.final
  final_conjTranspose := A.final_conjTranspose
  final_mul_self := A.final_mul_self

/-- The time of a costed multi-round circuit: the gate time of its words, one unit per oracle
call and one unit per classical round. -/
def time (A : QAdvMRT m n w q k c a) : ℕ :=
  (∑ i, ∑ j, A.S.cost (A.seg i j)) + (k + 1) * q + k

/-- The step cost `c'` added in front of a step-prefixed costed multi-round circuit. -/
def delay (c' : ℕ) (x : ℕ × QAdvMRT m n w q k c a) : ℕ × QAdvMRT m n w q k c a :=
  (c' + x.1, x.2)

/-- `StepTimeBound x T`: the step cost of `x` followed by a run of its circuit takes time at
most `T`. -/
def StepTimeBound (x : ℕ × QAdvMRT m n w q k c a) (T : ℕ) : Prop := x.1 + x.2.time ≤ T

/-- A step time bound holds at every larger time. -/
theorem StepTimeBound.mono {x : ℕ × QAdvMRT m n w q k c a} {T T' : ℕ}
    (h : StepTimeBound x T) (hT : T ≤ T') : StepTimeBound x T' :=
  h.trans hT

/-- Erasure of a step-prefixed costed multi-round circuit commutes with `if`. -/
theorem erase_snd_ite (p : Prop) [Decidable p] (x y : ℕ × QAdvMRT m n w q k c a) :
    (if p then x else y).2.erase = if p then x.2.erase else y.2.erase := by
  split <;> rfl

/-- Erasure of a step-prefixed costed multi-round circuit commutes with a dependent `if`. -/
theorem erase_snd_dite (p : Prop) [Decidable p] (x : p → ℕ × QAdvMRT m n w q k c a)
    (y : ¬p → ℕ × QAdvMRT m n w q k c a) :
    (if h : p then x h else y h).2.erase = if h : p then (x h).2.erase else (y h).2.erase := by
  split <;> rfl

/-- Erasure of a costed multi-round circuit commutes with `if`. -/
theorem erase_ite (p : Prop) [Decidable p] (x y : QAdvMRT m n w q k c a) :
    (if p then x else y).erase = if p then x.erase else y.erase := by
  split <;> rfl

end QAdvMRT

/-! ## The tree kinds -/

open CatCrypt.Tactics.DeriveTimed in
/-- Single-run QROM circuits `QAdv m n w q`: the combinator `absorbOracle`. -/
meta def qAdvKind : TreeKind where
  noun := "quantum circuit"
  tree := ``CatCrypt.Quantum.QROM.QAdv
  nParams := 4
  timed := ``CatCrypt.Quantum.QROM.QAdvT
  erase := ``CatCrypt.Quantum.QROM.QAdvT.erase
  delay := ``CatCrypt.Quantum.QROM.QAdvT.delay
  nodes := #[]
  combinators := #[
    ⟨``CatCrypt.Quantum.QROM.absorbOracle, ``CatCrypt.Quantum.QROM.QAdvT.absorb,
      #[.tree, .keep], false⟩]
  eraseLemmas := #[``CatCrypt.Quantum.QROM.QAdvT.delay,
    ``CatCrypt.Quantum.QROM.QAdvT.erase_absorb,
    ``CatCrypt.Quantum.QROM.QAdvT.erase_snd_ite,
    ``CatCrypt.Quantum.QROM.QAdvT.erase_snd_dite]
  hatLemmas := #[``Prod.mk.eta, ``CatCrypt.Tactics.DeriveTimed.fst_ite,
    ``CatCrypt.Tactics.DeriveTimed.snd_ite, ``CatCrypt.Tactics.DeriveTimed.ite_prod_mk,
    ``CatCrypt.Quantum.QROM.QAdvT.erase_ite]
  stepTimeBound := some ``CatCrypt.Quantum.QROM.QAdvT.StepTimeBound

open CatCrypt.Tactics.DeriveTimed in
/-- Multi-round QROM circuits `QAdvMR m n w q k c a`, without nodes or combinators: a circuit
is a binder or a field of a binder. -/
meta def qAdvMRKind : TreeKind where
  noun := "multi-round quantum circuit"
  tree := ``CatCrypt.Quantum.QROM.QAdvMR
  nParams := 7
  timed := ``CatCrypt.Quantum.QROM.QAdvMRT
  erase := ``CatCrypt.Quantum.QROM.QAdvMRT.erase
  delay := ``CatCrypt.Quantum.QROM.QAdvMRT.delay
  nodes := #[]
  combinators := #[]
  eraseLemmas := #[``CatCrypt.Quantum.QROM.QAdvMRT.delay,
    ``CatCrypt.Quantum.QROM.QAdvMRT.erase_snd_ite,
    ``CatCrypt.Quantum.QROM.QAdvMRT.erase_snd_dite]
  hatLemmas := #[``Prod.mk.eta, ``CatCrypt.Tactics.DeriveTimed.fst_ite,
    ``CatCrypt.Tactics.DeriveTimed.snd_ite, ``CatCrypt.Tactics.DeriveTimed.ite_prod_mk,
    ``CatCrypt.Quantum.QROM.QAdvMRT.erase_ite]
  stepTimeBound := some ``CatCrypt.Quantum.QROM.QAdvMRT.StepTimeBound

end CatCrypt.Quantum.QROM

end

register_tree_kind CatCrypt.Quantum.QROM.qAdvKind

register_tree_kind CatCrypt.Quantum.QROM.qAdvMRKind
