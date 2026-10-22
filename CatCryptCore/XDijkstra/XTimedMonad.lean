/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCryptCore.Core.SPTreeTimedOps
public meta import CatCryptCore.XDijkstra.XCostMonad
public meta import CatCryptCore.Crypto.MonadCostModel
import all CatCryptCore.Core.SPTreeTimed

@[expose] public meta section
set_option autoImplicit false

/-!
# `XTimedMonad`: step-timed computation trees as a graded monad

`TimedM n α` is the type of step-prefixed computation trees `(c, t) : ℕ × SPTree.Timed α`, the
form that `derive_timed` and `derive_reduction` produce, whose time
`SPTree.Timed.stepTime (c, t) = c + t.time` is at most `n`. The family is a lawful graded monad
over `(ℕ, +, 0)`: `TimedM.pure` is the leaf `(0, ret a)` at index `0`, and `TimedM.bind` is the
costed bind `SPTree.Timed.bind` behind the step cost of the head, at the sum of the indices.
`TimedM.relax` moves a tree to a larger index.

For each index `n` the type constructor `TimedM n` has an `XWP` instance at the shape
`.graded ℕ .pure`, `timeWP`: the weakest precondition at `Q` is that `Q` holds at every leaf of
the tree, and the grade is the index `n`. The run lemmas and the operations of the
`GradedMonad` instance are in the `xspec` set, so `xmvcgen!` reduces a time bound on a `gdo`
block to an inequality between numbers, and `TimedM.sound` turns it into a bound on
`SPTree.Timed.stepTime`.

## Relation to `CostM` and to the cost classes

`TimedM` and `CostM σ n` (`XCostMonad`) are graded the same way: `CostM` bounds the
tick count of a deterministic state program on every run, `TimedM` bounds the worst-case time of
a tree over all its branches. The extensional counterpart of `TickM` (`XCostMonadModel`) is the
step-time cost of an `SPComp` arrow, `spTreeTimeCost`, the least time of a step-prefixed tree
family whose erasure compiles to the arrow. `spTreeTimeCost_le_iff` identifies the arrows of
step-time cost at most `n` with the images of the arrows into `TimedM n`.

The infimum may choose zero step costs (`SPTree.Timed.ofTree`), and a tree with zero step costs
has time equal to its query cost; conversely the query cost of the erasure is at most the time.
Hence `spTreeTimeCost = spTreeQueryCost` (`spTreeTimeCost_eq_spTreeQueryCost`), and the
`MonadCostModel` built on it (`timeCostModel`) is the query-cost model of `MonadCostModel.lean`:
`cost_pure` (zero on `pure`), `cost_bind` (subadditive under bind), `cost_mapSum` (coproduct at
most the maximum) and `cost_precomp` all hold. `cost_precomp` holds because precomposition with a
Lean function `f : α' → α` is not charged: `g ∘ f` has the witnesses of `g` reindexed along `f`,
whatever the cost of computing `f`. A time measure that charges the computation of `f` is
therefore not an arrow cost on `SPComp` of this kind; it lives on the costed trees themselves,
the grading of `TimedM`, where a step cost such as `fc a` in `SPTree.Timed.map f fc` enters the
index.

## Main definitions

* `TimedM`: the indexed family, with `TimedM.tree` and the invariant `TimedM.stepTime_le`.
* `TimedM.pure`, `TimedM.bind`, `TimedM.lift`, `TimedM.ofStep`, `TimedM.relax`,
  `TimedM.erase`: the operations.
* `TimedM.instGradedMonad`, `TimedM.instLawfulGradedMonad`: the family as a lawful graded monad.
* `SPTree.Timed.AllRet`: a predicate holds at every leaf of a tree.
* `psTimed`, `timeWP`, `instXWPTimedM`: the observation at `.graded ℕ .pure`.
* `spTreeTimeCost`, `timeCostModel`: the step-time cost of an `SPComp` arrow and its cost model.

## Main results

* `SPTree.Timed.bind_ret`, `SPTree.Timed.bind_bind`: the unit and associativity laws of the
  costed bind.
* `timeWP_triple_iff`, `TimedM.sound`: a triple holds iff the postcondition holds at every leaf;
  with a grade bound `b`, the time of the tree is at most `b`.
* `TimedM.stepTime_le_of_grade_le`: a grade bound bounds the time of the tree.
* `TimedM.tree_lift_bind`: a lifted tree followed by a continuation is the costed bind.
* `spTreeTimeCost_eq_spTreeQueryCost`, `spTreeTimeCost_le_iff`, `timeCostModel_eq`.
-/

namespace CatCrypt.Core.SPTree.Timed

variable {α β γ : Type}

/-! ## Laws of the costed bind -/

/-- Binding into leaves of step cost zero gives back the tree. -/
theorem bind_ret (t : SPTree.Timed α) : t.bind (fun a => (0, ret a)) = (0, t) := by
  induction t with
  | ret a => rfl
  | sample γ finγ neγ c k ih => simp only [bind, ih, Nat.add_zero]
  | get l c k ih => simp only [bind, ih, Nat.add_zero]
  | set l v c t ih => simp only [bind, ih, Nat.add_zero]
  | fail => rfl
  | load h₀ c t ih => simp only [bind, ih, Nat.add_zero]

/-- The costed bind after a costed bind, with the step cost of the inner result in front, is the
costed bind of the composed continuation. -/
theorem bind_bind (t : SPTree.Timed α) (f : α → ℕ × SPTree.Timed β)
    (g : β → ℕ × SPTree.Timed γ) :
    delay (t.bind f).1 ((t.bind f).2.bind g) =
      t.bind fun a => delay (f a).1 ((f a).2.bind g) := by
  induction t with
  | ret a => rfl
  | sample γ finγ neγ c k ih =>
    simp only [delay] at ih
    simp only [bind, ← ih, delay, Nat.add_assoc, Nat.add_zero]
  | get l c k ih =>
    simp only [delay] at ih
    simp only [bind, ← ih, delay, Nat.add_assoc, Nat.add_zero]
  | set l v c t ih =>
    simp only [delay] at ih
    simp only [bind, ← ih, delay, Nat.add_assoc, Nat.add_zero]
  | fail => rfl
  | load h₀ c t ih =>
    simp only [delay] at ih
    simp only [bind, ← ih, delay, Nat.add_assoc, Nat.add_zero]

/-! ## Leaves -/

/-- `Q` holds at every leaf `ret a` of the tree; `fail` has no leaf. -/
def AllRet (Q : α → Prop) : SPTree.Timed α → Prop
  | ret a => Q a
  | sample _ _ _ _ k => ∀ b, AllRet Q (k b)
  | get _ _ k => ∀ v, AllRet Q (k v)
  | set _ _ _ t => AllRet Q t
  | fail => True
  | load _ _ t => AllRet Q t

theorem allRet_mono {Q Q' : α → Prop} (h : ∀ a, Q a → Q' a) (t : SPTree.Timed α) :
    AllRet Q t → AllRet Q' t := by
  induction t with
  | ret a => exact h a
  | sample γ finγ neγ c k ih => exact fun hk b => ih b (hk b)
  | get l c k ih => exact fun hk v => ih v (hk v)
  | set l v c t ih => exact ih
  | fail => exact id
  | load h₀ c t ih => exact ih

/-- Every leaf of a costed bind satisfies `Q` iff at every leaf `a` of the tree every leaf of
the continuation at `a` satisfies `Q`. -/
theorem allRet_bind (Q : β → Prop) (t : SPTree.Timed α) (f : α → ℕ × SPTree.Timed β) :
    AllRet Q (t.bind f).2 ↔ AllRet (fun a => AllRet Q (f a).2) t := by
  induction t with
  | ret a => rfl
  | sample γ finγ neγ c k ih => simp only [bind, AllRet, ih]
  | get l c k ih => simp only [bind, AllRet, ih]
  | set l v c t ih => simp only [bind, AllRet, ih]
  | fail => simp only [bind, AllRet]
  | load h₀ c t ih => simp only [bind, AllRet, ih]

/-- The query cost of the erasure is at most the time. -/
theorem queryCost_erase_le_time (t : SPTree.Timed α) : t.erase.queryCost ≤ t.time := by
  induction t with
  | ret a => simp only [erase, SPTree.queryCost, time, le_refl]
  | sample γ finγ neγ c k ih =>
    let _ := finγ
    simp only [erase, SPTree.queryCost, time]
    exact Nat.add_le_add_left
      (Finset.sup_mono_fun fun b _ => (ih b).trans (Nat.le_add_left _ _)) 1
  | get l c k ih =>
    simp only [erase, SPTree.queryCost, time]
    exact Nat.add_le_add_left
      (Finset.sup_mono_fun fun v _ => (ih v).trans (Nat.le_add_left _ _)) 1
  | set l v c t ih =>
    simp only [erase, SPTree.queryCost, time]
    omega
  | fail => simp only [erase, SPTree.queryCost, time, le_refl]
  | load h₀ c t ih =>
    simp only [erase, SPTree.queryCost, time]
    omega

end CatCrypt.Core.SPTree.Timed

namespace CatCrypt.XDijkstra

open CatCrypt.Core

/-- A step-prefixed computation tree whose time is at most the index `n`. -/
structure TimedM (n : ℕ) (α : Type) where
  /-- The step-prefixed tree: a step cost in front of a tree with step costs. -/
  tree : ℕ × SPTree.Timed α
  /-- The time of the tree is at most the index. -/
  stepTime_le : SPTree.Timed.stepTime tree ≤ n

namespace TimedM

variable {α β : Type} {m n : ℕ}

/-- Return a value: the leaf with no step cost. -/
protected def pure (a : α) : TimedM 0 α where
  tree := (0, .ret a)
  stepTime_le := by simp [SPTree.Timed.stepTime, SPTree.Timed.time]

/-- The costed bind behind the step cost of the head; the indices add. -/
protected def bind (x : TimedM m α) (f : α → TimedM n β) : TimedM (m + n) β where
  tree := SPTree.Timed.delay x.tree.1 (x.tree.2.bind fun a => (f a).tree)
  stepTime_le := by
    have h1 := x.stepTime_le
    have h2 := SPTree.Timed.stepTime_bind_le x.tree.2 (fun a => (f a).tree) n
      fun a => (f a).stepTime_le
    rw [SPTree.Timed.stepTime_delay]
    simp only [SPTree.Timed.stepTime] at h1
    omega

/-- A tree with step costs, at its time. -/
def lift (t : SPTree.Timed α) : TimedM t.time α where
  tree := (0, t)
  stepTime_le := by simp [SPTree.Timed.stepTime]

/-- The step cost `c` in front of the tree `t`, at the index `c + t.time`. -/
def ofStep (c : ℕ) (t : SPTree.Timed α) : TimedM (c + t.time) α where
  tree := (c, t)
  stepTime_le := le_rfl

/-- The same tree at a larger index. -/
def relax (h : m ≤ n) (x : TimedM m α) : TimedM n α where
  tree := x.tree
  stepTime_le := x.stepTime_le.trans h

/-- The tree with its step costs erased. -/
def erase (x : TimedM n α) : SPTree α := x.tree.2.erase

/-! ### The tree of each operation -/

@[simp, xspec] theorem tree_pure (a : α) : (TimedM.pure a).tree = (0, .ret a) := rfl

@[simp, xspec] theorem tree_bind (x : TimedM m α) (f : α → TimedM n β) :
    (x.bind f).tree = SPTree.Timed.delay x.tree.1 (x.tree.2.bind fun a => (f a).tree) := rfl

@[simp, xspec] theorem tree_lift (t : SPTree.Timed α) : (lift t).tree = (0, t) := rfl

@[simp, xspec] theorem tree_ofStep (c : ℕ) (t : SPTree.Timed α) : (ofStep c t).tree = (c, t) :=
  rfl

@[simp, xspec] theorem tree_relax (h : m ≤ n) (x : TimedM m α) : (x.relax h).tree = x.tree := rfl

/-- A tree lifted at its time, followed by a continuation, is the costed bind of the tree. -/
@[simp, xspec] theorem tree_lift_bind (t : SPTree.Timed α) (f : α → TimedM n β) :
    ((lift t).bind f).tree = t.bind fun a => (f a).tree := by
  simp only [tree_bind, tree_lift, SPTree.Timed.delay, Nat.zero_add, Prod.mk.eta]

/-- The erasure of `TimedM.bind` is `SPTree.bind` of the erasures. -/
theorem erase_bind (x : TimedM m α) (f : α → TimedM n β) :
    (x.bind f).erase = x.erase.bind fun a => (f a).erase := by
  simp only [erase, tree_bind, SPTree.Timed.delay, SPTree.Timed.erase_bind]

/-! ### The graded-monad instance -/

instance instGradedMonad : GradedMonad ℕ TimedM where
  gpure := TimedM.pure
  gbind := TimedM.bind

@[simp, xspec] theorem gpure_eq (a : α) :
    (GradedMonad.gpure a : TimedM 0 α) = TimedM.pure a := rfl

@[simp, xspec] theorem gbind_eq (x : TimedM m α) (f : α → TimedM n β) :
    GradedMonad.gbind x f = x.bind f := rfl

/-- Two trees at equal indices with the same step-prefixed tree are heterogeneously equal. -/
theorem heq_of_tree_eq (h : m = n) {x : TimedM m α} {y : TimedM n α} (ht : x.tree = y.tree) :
    HEq x y := by
  subst h
  cases x
  cases y
  cases ht
  rfl

instance instLawfulGradedMonad : LawfulGradedMonad ℕ TimedM where
  gpure_gbind a f := heq_of_tree_eq (Nat.zero_add _) <| by
    simp only [gbind_eq, gpure_eq, tree_bind, tree_pure, SPTree.Timed.bind,
      SPTree.Timed.delay, Nat.zero_add, Prod.mk.eta]
  gbind_gpure x := heq_of_tree_eq (Nat.add_zero _) <| by
    simp only [gbind_eq, gpure_eq, tree_bind, tree_pure, SPTree.Timed.bind_ret,
      SPTree.Timed.delay, Nat.add_zero, Prod.mk.eta]
  gbind_assoc x f c := heq_of_tree_eq (Nat.add_assoc _ _ _) <| by
    simp only [gbind_eq, tree_bind]
    rw [← SPTree.Timed.bind_bind]
    simp only [SPTree.Timed.delay, Nat.add_assoc]

end TimedM

/-! ## The observation at the graded shape -/

/-- The shape of `TimedM n`: a grade layer over `ℕ` above the pure layer. -/
abbrev psTimed : XPostShape.{0} := .graded ℕ .pure

section Observation

variable {α β : Type} {m n : ℕ}

/-- The weakest-precondition observation of a `TimedM n` tree: `Q` holds at every leaf, at the
grade `n`, a bound on the time of the tree (`TimedM.stepTime_le`). -/
def timeWP (x : TimedM n α) : XPredTrans psTimed Prop α where
  apply Q := x.tree.2.AllRet Q.1
  grade := (n, PUnit.unit)
  mono h := SPTree.Timed.allRet_mono h.1 _

/-- `TimedM n` observed as a transformer of grade `n` over `Prop`. -/
instance instXWPTimedM : XWP (TimedM n) psTimed Prop where
  xwp := timeWP

@[simp, xspec] theorem xwp_timedM (x : TimedM n α) :
    XWP.xwp (ps := psTimed) (Ω := Prop) x = timeWP x := rfl

@[simp, xspec] theorem timeWP_apply (x : TimedM n α) (Q : XPostCond α psTimed Prop) :
    (timeWP x).apply Q = x.tree.2.AllRet Q.1 := rfl

@[simp, xspec] theorem timeWP_grade_fst (x : TimedM n α) : (timeWP x).grade.1 = n := rfl

/-- The weakest precondition of `TimedM.bind` is that of `xbind` of the observations. -/
theorem timeWP_bind_apply (x : TimedM m α) (f : α → TimedM n β) (Q : XPostCond β psTimed Prop) :
    (timeWP (x.bind f)).apply Q = (xbind (timeWP x) fun a => timeWP (f a)).apply Q :=
  propext (SPTree.Timed.allRet_bind Q.1 x.tree.2 fun a => (f a).tree)

/-- An `XTriple` over `TimedM n` holds iff the postcondition holds at every leaf whenever the
precondition holds. -/
theorem timeWP_triple_iff (P : Prop) (Q : α → Prop) (x : TimedM n α) :
    XTriple (m := TimedM n) (ps := psTimed) (Ω := Prop) P x (Q, PUnit.unit) ↔
      (P → x.tree.2.AllRet Q) :=
  Iff.rfl

/-- Soundness of a graded triple: with a bound `b` on the grade, the postcondition holds at every
leaf under the precondition, and the time of the tree is at most `b`. -/
theorem TimedM.sound (x : TimedM n α) {P : Prop} {Q : α → Prop} {b : ℕ}
    (h : XTriple (m := TimedM n) (ps := psTimed) (Ω := Prop) P x (Q, PUnit.unit))
    (hb : (XWP.xwp (ps := psTimed) (Ω := Prop) x).grade.1 ≤ b) (hP : P) :
    x.tree.2.AllRet Q ∧ SPTree.Timed.stepTime x.tree ≤ b :=
  ⟨h hP, x.stepTime_le.trans hb⟩

/-- A bound on the grade of the observation bounds the time of the tree. -/
theorem TimedM.stepTime_le_of_grade_le (x : TimedM n α) {b : ℕ}
    (hb : (XWP.xwp (ps := psTimed) (Ω := Prop) x).grade.1 ≤ b) :
    SPTree.Timed.stepTime x.tree ≤ b :=
  x.stepTime_le.trans hb

end Observation

/-! ## The step-time cost of an `SPComp` arrow -/

section Cost

open UCMonad
open scoped ENNReal

variable {α β : Type}

/-- The step-time cost of a Kleisli arrow into `SPComp`: the least worst-case time of a
step-prefixed tree family whose erasure compiles to it, `⊤` when there is none with a uniform
bound. -/
noncomputable def spTreeTimeCost (f : α → SPComp β) : WithTop ℕ :=
  ⨅ s : {s : α → ℕ × SPTree.Timed β // ∀ a, (s a).2.erase.compile = f a},
    ⨆ a, ((SPTree.Timed.stepTime (s.1 a) : ℕ) : ℕ∞)

/-- The step-time cost is the query cost: a tree with zero step costs has time equal to its
query cost, and the query cost of the erasure of a tree is at most its time. -/
theorem spTreeTimeCost_eq_spTreeQueryCost (f : α → SPComp β) :
    spTreeTimeCost f = spTreeQueryCost f := by
  refine le_antisymm (le_iInf fun s => ?_) (le_iInf fun s => ?_)
  · refine iInf_le_of_le ⟨fun a => (0, SPTree.Timed.ofTree (s.1 a)), fun a => ?_⟩
      (iSup_mono fun a => le_of_eq ?_)
    · rw [SPTree.Timed.erase_ofTree]
      exact s.2 a
    · simp only [SPTree.Timed.stepTime, SPTree.Timed.time_ofTree, Nat.zero_add]
      rfl
  · exact iInf_le_of_le ⟨fun a => (s.1 a).2.erase, s.2⟩ (iSup_mono fun a => Nat.cast_le.mpr
      ((SPTree.Timed.queryCost_erase_le_time _).trans (Nat.le_add_left _ _)))

/-- The arrows of step-time cost at most `n` are the erasures of the arrows into `TimedM n`. -/
theorem spTreeTimeCost_le_iff (f : α → SPComp β) (n : ℕ) :
    spTreeTimeCost f ≤ n ↔ ∃ k : α → TimedM n β, ∀ a, (k a).erase.compile = f a := by
  rw [spTreeTimeCost_eq_spTreeQueryCost, spTreeQueryCost_le_iff]
  constructor
  · rintro ⟨s, hs, hc⟩
    refine ⟨fun a => ⟨(0, SPTree.Timed.ofTree (s a)), ?_⟩, fun a => ?_⟩
    · simp only [SPTree.Timed.stepTime, SPTree.Timed.time_ofTree, Nat.zero_add]
      exact hc a
    · simp only [TimedM.erase, SPTree.Timed.erase_ofTree, hs]
  · rintro ⟨k, hk⟩
    exact ⟨fun a => (k a).erase, hk, fun a => (SPTree.Timed.queryCost_erase_le_time _).trans
      ((Nat.le_add_left _ _).trans (k a).stepTime_le)⟩

/-- The step-time cost as a `MonadCostModel` on `SPComp`. All four laws hold; it is the
query-cost model (`timeCostModel_eq`). It is a `def` because `SPComp` carries the query-cost
instance. -/
@[instance_reducible]
noncomputable def timeCostModel : MonadCostModel SPComp where
  cost := spTreeTimeCost
  cost_pure {α} := by
    rw [spTreeTimeCost_eq_spTreeQueryCost]
    exact cost_pure (T := SPComp) (α := α)
  cost_bind {α β γ} {f g} := by
    simp only [spTreeTimeCost_eq_spTreeQueryCost]
    exact cost_bind (T := SPComp) (f := f) (g := g)
  cost_mapSum {α β γ δ} {f g} := by
    simp only [spTreeTimeCost_eq_spTreeQueryCost]
    exact cost_mapSum (T := SPComp) (f := f) (g := g)
  cost_precomp {α α' β} {g} f := by
    simp only [spTreeTimeCost_eq_spTreeQueryCost]
    exact cost_precomp (T := SPComp) (g := g) f

/-- The step-time cost model is the query-cost model. -/
theorem timeCostModel_eq : timeCostModel = (inferInstance : MonadCostModel SPComp) := by
  have h : (fun {α β : Type} (f : α → SPComp β) => spTreeTimeCost f) =
      fun {α β : Type} (f : α → SPComp β) => spTreeQueryCost f := by
    funext α β f
    exact spTreeTimeCost_eq_spTreeQueryCost f
  unfold timeCostModel
  generalize hB : (inferInstance : MonadCostModel SPComp) = B
  cases B with
  | mk cost _ _ _ _ =>
    have hc : @cost = fun {α β : Type} (f : α → SPComp β) => spTreeQueryCost f := by
      exact (congrArg (fun M => @MonadCostModel.cost SPComp _ _ M) hB).symm
    subst hc
    simp only [h]

/-- An arrow has step-time cost at most `n` in `timeCostModel` iff it is the erasure of an arrow
into `TimedM n`. -/
theorem costBounded_timeCostModel_iff (f : α → SPComp β) (n : ℕ) :
    @costBounded SPComp _ _ timeCostModel n α β f ↔
      ∃ k : α → TimedM n β, ∀ a, (k a).erase.compile = f a :=
  spTreeTimeCost_le_iff f n

end Cost

end CatCrypt.XDijkstra
