/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import CatCryptCore.XDijkstra.XPostShape
public import CatCryptCore.XDijkstra.XMvcgenReg
public import CatCryptCore.XDijkstra.GradedDo

@[expose] public section
set_option autoImplicit false

/-!
# `XCostMonad`: a cost-counting state monad observed at a graded shape

`CostM σ n α` is the type of state programs over `σ` that count ticks and whose
count is at most `n` on every run. The family is a graded monad over `(ℕ, +, 0)`:
`CostM.pure` has index `0` and `CostM.bind` adds the indices. For each index `n`
the type constructor `CostM σ n` has an `XWP` instance at the shape
`.graded ℕ (.arg σ .pure)`: the weakest precondition reads the value and the final
state of the run, and the grade of the transformer is the index `n`.

The index is a parameter of the type, not of a single `Monad` instance, because
the transformer `XPredTrans` stores one grade per program: a `Monad` instance on a
fixed type constructor has a `bind` whose continuation may choose its cost from
the value, and no grade fixed in advance bounds it. `CostM σ n` therefore has no
`Monad` instance and Lean's `do` notation is not available. The family is an
instance of `GradedMonad`, so programs are written as `gdo` blocks, or with
`CostM.bind` and `CostM.seq`.

## Main definitions

* `CostM`: the indexed family, with `CostM.run` and the invariant `CostM.cost_le`.
* `CostM.pure`, `CostM.bind`, `CostM.seq`, `CostM.tick`, `CostM.get`, `CostM.set`,
  `CostM.modify`, `CostM.relax`: the operations.
* `CostM.instGradedMonad`, `CostM.instLawfulGradedMonad`: the family as a lawful
  graded monad over `(ℕ, +, 0)`.
* `psCost`: the shape `.graded ℕ (.arg σ .pure)`.
* `costWP`, `instXWPCostM`: the observation.

## Main results

* `costWP_triple_iff`: an `XTriple` over `CostM σ n` is the Hoare triple of the run.
* `CostM.sound`: from a triple and a bound on the grade, the run returns a value
  and a state that satisfy the postcondition, with at most the bound in ticks.
* `costWP_pure`, `costWP_seq`, `costWP_bind_apply`, `costWP_bind_grade_fst`: the
  observation sends `CostM.pure` to `xpure` and `CostM.seq` to `xseq`, agrees with
  `xbind` on weakest preconditions, and sends the index of `CostM.bind` to the sum
  of the grades.
* `costWP_seq_grade_le`: the budget rule `xtriple_grade_le` for two sequenced
  programs.
* `xwp_costM`, `costWP_apply`, `costWP_grade_fst` and the `CostM.run_*` lemmas are
  in the `xspec` set, so `xmvcgen!` reduces a triple about a `CostM` program to a
  statement about states and a grade bound to an inequality between numbers.
* `CostM.gpure_eq`, `CostM.gbind_eq`, `CostM.gseq_eq`: the operations of the
  `GradedMonad` instance are `CostM.pure`, `CostM.bind` and `CostM.seq`; they are
  in the `xspec` set, so the same reduction applies to a `gdo` block.
-/

namespace CatCrypt.XDijkstra

/-- The shape of `CostM σ n`: a grade layer over `ℕ` above one state layer. -/
abbrev psCost (σ : Type) : XPostShape.{0} := .graded ℕ (.arg σ .pure)

/-- A state program over `σ` with a tick counter: `run s` is the returned value,
the final state and the number of ticks, and the number of ticks is at most the
index `n` from every initial state. -/
structure CostM (σ : Type) (n : ℕ) (α : Type) where
  /-- The run from an initial state: value and final state, paired with the number
  of ticks. -/
  run : σ → (α × σ) × ℕ
  /-- The number of ticks of every run is at most the index. -/
  cost_le : ∀ s, (run s).2 ≤ n

namespace CostM

variable {σ α β : Type} {m n : ℕ}

/-- Return a value: the state is unchanged and no tick is counted. -/
protected def pure (a : α) : CostM σ 0 α where
  run s := ((a, s), 0)
  cost_le _ := le_rfl

/-- Run `x`, then the continuation at its value from its final state. The tick
counts add, and so do the indices. -/
protected def bind (x : CostM σ m α) (f : α → CostM σ n β) : CostM σ (m + n) β where
  run s :=
    (((f (x.run s).1.1).run (x.run s).1.2).1,
      (x.run s).2 + ((f (x.run s).1.1).run (x.run s).1.2).2)
  cost_le s := Nat.add_le_add (x.cost_le s) ((f (x.run s).1.1).cost_le (x.run s).1.2)

/-- Run `x`, discard its value, then run `y`. -/
protected def seq (x : CostM σ m α) (y : CostM σ n β) : CostM σ (m + n) β :=
  x.bind fun _ => y

/-- Count `k` ticks. -/
def tick (k : ℕ) : CostM σ k Unit where
  run s := (((), s), k)
  cost_le _ := le_rfl

/-- Return the state. -/
protected def get : CostM σ 0 σ where
  run s := ((s, s), 0)
  cost_le _ := le_rfl

/-- Replace the state. -/
protected def set (s' : σ) : CostM σ 0 Unit where
  run _ := (((), s'), 0)
  cost_le _ := le_rfl

/-- Apply a function to the state. -/
protected def modify (f : σ → σ) : CostM σ 0 Unit where
  run s := (((), f s), 0)
  cost_le _ := le_rfl

/-- The same program at a larger index. -/
def relax (h : m ≤ n) (x : CostM σ m α) : CostM σ n α where
  run := x.run
  cost_le s := (x.cost_le s).trans h

/-! ### The run of each operation -/

/-- The run of `CostM.pure`. -/
@[simp, xspec] theorem run_pure (a : α) (s : σ) :
    (CostM.pure a : CostM σ 0 α).run s = ((a, s), 0) := rfl

/-- The run of `CostM.bind`. -/
@[simp, xspec] theorem run_bind (x : CostM σ m α) (f : α → CostM σ n β) (s : σ) :
    (x.bind f).run s =
      (((f (x.run s).1.1).run (x.run s).1.2).1,
        (x.run s).2 + ((f (x.run s).1.1).run (x.run s).1.2).2) := rfl

/-- The run of `CostM.seq`. -/
@[simp, xspec] theorem run_seq (x : CostM σ m α) (y : CostM σ n β) (s : σ) :
    (x.seq y).run s = ((y.run (x.run s).1.2).1, (x.run s).2 + (y.run (x.run s).1.2).2) := rfl

/-- The run of `CostM.tick`. -/
@[simp, xspec] theorem run_tick (k : ℕ) (s : σ) :
    (tick k : CostM σ k Unit).run s = (((), s), k) := rfl

/-- The run of `CostM.get`. -/
@[simp, xspec] theorem run_get (s : σ) : (CostM.get : CostM σ 0 σ).run s = ((s, s), 0) := rfl

/-- The run of `CostM.set`. -/
@[simp, xspec] theorem run_set (s' s : σ) :
    (CostM.set s' : CostM σ 0 Unit).run s = (((), s'), 0) := rfl

/-- The run of `CostM.modify`. -/
@[simp, xspec] theorem run_modify (f : σ → σ) (s : σ) :
    (CostM.modify f : CostM σ 0 Unit).run s = (((), f s), 0) := rfl

/-- The run of `CostM.relax`. -/
@[simp, xspec] theorem run_relax (h : m ≤ n) (x : CostM σ m α) (s : σ) :
    (x.relax h).run s = x.run s := rfl

/-! ### The graded-monad instance -/

/-- `CostM σ` is a graded monad over `(ℕ, +, 0)`, so a `CostM` program is written
as a `gdo` block. -/
instance instGradedMonad : GradedMonad ℕ (CostM σ) where
  gpure := CostM.pure
  gbind := CostM.bind

/-- `GradedMonad.gpure` at `CostM σ` is `CostM.pure`. -/
@[simp, xspec] theorem gpure_eq (a : α) :
    (GradedMonad.gpure a : CostM σ 0 α) = CostM.pure a := rfl

/-- `GradedMonad.gbind` at `CostM σ` is `CostM.bind`. -/
@[simp, xspec] theorem gbind_eq (x : CostM σ m α) (f : α → CostM σ n β) :
    GradedMonad.gbind x f = x.bind f := rfl

/-- `GradedMonad.gseq` at `CostM σ` is `CostM.seq`. -/
@[simp, xspec] theorem gseq_eq (x : CostM σ m α) (y : CostM σ n β) :
    GradedMonad.gseq x y = x.seq y := rfl

/-- Two programs at equal indices with the same run are heterogeneously equal. -/
theorem heq_of_run_eq (h : m = n) {x : CostM σ m α} {y : CostM σ n α}
    (hr : x.run = y.run) : HEq x y := by
  subst h
  cases x
  cases y
  cases hr
  rfl

/-- `CostM σ` satisfies the laws of a graded monad. -/
instance instLawfulGradedMonad : LawfulGradedMonad ℕ (CostM σ) where
  gpure_gbind a f := heq_of_run_eq (Nat.zero_add _) <| by
    funext s; simp
  gbind_gpure x := heq_of_run_eq (Nat.add_zero _) <| by
    funext s; simp
  gbind_assoc x f c := heq_of_run_eq (Nat.add_assoc _ _ _) <| by
    funext s; simp [Nat.add_assoc]

end CostM

/-! ## The observation at the graded shape -/

section Observation

variable {σ α β : Type} {m n : ℕ}

/-- The weakest-precondition observation of a `CostM σ n` program. The weakest
precondition at `Q` holds of an initial state when `Q` holds of the value and the
final state of the run. The grade is the index `n`, an upper bound on the tick
count of every run (`CostM.cost_le`). -/
def costWP (x : CostM σ n α) : XPredTrans (psCost σ) Prop α where
  apply Q := fun s => Q.1 (x.run s).1.1 (x.run s).1.2
  grade := (n, PUnit.unit)
  mono h := fun s => h.1 (x.run s).1.1 (x.run s).1.2

/-- `CostM σ n` observed as a transformer of grade `n` over `Prop`. -/
instance instXWPCostM : XWP (CostM σ n) (psCost σ) Prop where
  xwp := costWP

/-- The observation of a `CostM` program is `costWP`. -/
@[simp, xspec] theorem xwp_costM (x : CostM σ n α) :
    XWP.xwp (ps := psCost σ) (Ω := Prop) x = costWP x := rfl

/-- The weakest precondition of a `CostM` program evaluates the postcondition at
the value and the final state of the run. -/
@[simp, xspec] theorem costWP_apply (x : CostM σ n α) (Q : XPostCond α (psCost σ) Prop) :
    (costWP x).apply Q = fun s => Q.1 (x.run s).1.1 (x.run s).1.2 := rfl

/-- The grade of the observation of a `CostM σ n` program is `n`. -/
@[simp, xspec] theorem costWP_grade_fst (x : CostM σ n α) : (costWP x).grade.1 = n := rfl

/-! ### The observation and the graded-monad operations -/

/-- The observation of `CostM.pure` is `xpure`. -/
theorem costWP_pure (a : α) : costWP (CostM.pure a : CostM σ 0 α) = xpure a := rfl

/-- The observation of `CostM.seq` is `xseq` of the observations, grade included. -/
theorem costWP_seq (x : CostM σ m α) (y : CostM σ n β) :
    costWP (x.seq y) = xseq (costWP x) (costWP y) := rfl

/-- The weakest precondition of `CostM.bind` is that of `xbind` of the
observations. -/
theorem costWP_bind_apply (x : CostM σ m α) (f : α → CostM σ n β)
    (Q : XPostCond β (psCost σ) Prop) :
    (costWP (x.bind f)).apply Q = (xbind (costWP x) fun a => costWP (f a)).apply Q := rfl

/-- The grade of `CostM.bind` is the sum of the grade of the head and the common
grade of the continuations. `xbind` keeps the head grade only; the index of the
family supplies the second summand. -/
theorem costWP_bind_grade_fst (x : CostM σ m α) (f : α → CostM σ n β) (a : α) :
    (costWP (x.bind f)).grade.1 = (costWP x).grade.1 + (costWP (f a)).grade.1 := rfl

/-- The budget rule for two sequenced programs: `xtriple_grade_le` at the
observations. -/
theorem costWP_seq_grade_le (x : CostM σ m α) (y : CostM σ n β) {b₁ b₂ : ℕ}
    (h₁ : (costWP x).grade.1 ≤ b₁) (h₂ : (costWP y).grade.1 ≤ b₂) :
    (costWP (x.seq y)).grade.1 ≤ b₁ + b₂ :=
  costWP_seq x y ▸ xtriple_grade_le (costWP x) (costWP y) h₁ h₂

/-! ### Soundness against the run -/

/-- An `XTriple` over `CostM σ n` is the Hoare triple of the run: from every
initial state that satisfies `P`, the value and the final state satisfy `Q`. -/
theorem costWP_triple_iff (P : σ → Prop) (Q : α → σ → Prop) (x : CostM σ n α) :
    XTriple (m := CostM σ n) (ps := psCost σ) (Ω := Prop) P x (Q, PUnit.unit)
      ↔ ∀ s, P s → Q (x.run s).1.1 (x.run s).1.2 :=
  Iff.rfl

/-- Soundness of a graded triple. If `XTriple P x Q` holds and the grade of the
observation of `x` is at most `b`, then from every initial state that satisfies
`P` the run returns a value and a final state that satisfy `Q`, and counts at most
`b` ticks. -/
theorem CostM.sound (x : CostM σ n α) {P : σ → Prop} {Q : α → σ → Prop} {b : ℕ}
    (h : XTriple (m := CostM σ n) (ps := psCost σ) (Ω := Prop) P x (Q, PUnit.unit))
    (hb : (XWP.xwp (ps := psCost σ) (Ω := Prop) x).grade.1 ≤ b) (s : σ) (hs : P s) :
    Q (x.run s).1.1 (x.run s).1.2 ∧ (x.run s).2 ≤ b :=
  ⟨h s hs, (x.cost_le s).trans hb⟩

end Observation

end CatCrypt.XDijkstra
