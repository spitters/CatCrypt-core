/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.DNCert

/-!
# Time and query counts of oracle programs as one vector charge

The tick tree `OracleProg.Timed.toFreeMT p` of a costed oracle program carries two resources:
the clock, charged `tickCost` at each position, and the queries, charged `cost i` at a query
`i` and nothing elsewhere. The vector charge `useCharge cost` counts both, the queries at
`false` and the ticks at `true`, the two positions of `Container.clockPos`. A use bound of the
tick tree at the vector `budget q T` is the pair of the time bound `T` and the query bound `q`
(`useBound_iff_timeBound_and_queryCostLe`), so that the two budgets of a program travel as one
hypothesis.

Replacing the queries of a program by handler programs (`Timed.bindQueries`,
`Timed.collectLog`) is, at the level of charge folds, the interpretation of the tick tree by a
free handler (`bqHandler`, `clHandler`): the fold of the costed combinator is the fold of
`FreeM.liftM` (an equation for `bindQueries`, a bound for `collectLog`, whose record append is
charged after the rest of the program and is charged before it by the handler). The use bound
of the composite is then the composition rule `Container.useBound_liftM` at `{query, tick}`,
which at constant use counts is `Container.Clocked.comp`: a program of time `T` with `q`
queries, each handled by a program of time `t` with `q'` queries, has time `T + q * t` and
`q * q'` queries. The query count of the composite comes out of the same step as its time.

The query bound of an erased oracle program is a charge fold of its free tree
(`OracleProg.toFreeM`), the analogue for oracle programs of
`OracleAdv.isQueryBoundBy_iff_wpFold_charge`.

## Main definitions

* `OracleProg.EPos`, `OracleProg.ESig`, `OracleProg.toFreeM` — the free tree of an erased
  oracle program
* `OracleProg.queryCharge` — the weight `cost i` at a query, `0` elsewhere
* `OracleProg.useCharge` — the vector charge `{query, tick}` of a tick tree
* `OracleProg.budget` — the vector of `q` queries and `T` ticks
* `OracleProg.Timed.bqHandler`, `OracleProg.Timed.clHandler` — the free handlers of
  `bindQueries` and `collectLog`

## Main results

* `OracleProg.queryCostLe_iff_wpFold_charge` — `QueryCostLe` is a charge fold bound of the free
  tree of the program
* `OracleProg.Timed.queryCostLe_erase_iff_wpFold_charge` — the same over the tick tree
* `OracleProg.Timed.useBound_iff_timeBound_and_queryCostLe`,
  `OracleProg.Timed.useBound_step_iff` — a use bound at `budget q T` is a time bound and a query
  bound
* `OracleProg.Timed.wpFold_stepToFreeMT_bindQueries`,
  `OracleProg.Timed.wpFold_stepToFreeMT_collectLog_le` — the costed combinators are
  interpretations of the tick tree, on charge folds
* `OracleProg.Timed.useBound_bindQueries`, `OracleProg.Timed.useBound_collectLog` — the
  composition rule at `{query, tick}` for general vectors
* `OracleProg.Timed.stepTimeBound_bindQueries_queryCostLe`,
  `OracleProg.Timed.stepTimeBound_collectLog_queryCostLe` — time `T + q * t` (resp.
  `T + q * (t + 2 * ℓ + 1)`) and `q * q'` queries, by `Container.useBound_liftM_clocked`
* `OracleProg.Timed.timeBound_bindQueries`, `OracleProg.Timed.timeBound_collectLog` — the time
  components, without a query bound on the handler
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Core CatCrypt.Container PFunctor PFunctor.FreeM
open scoped BigOperators

namespace CatCrypt.Crypto

namespace OracleProg

variable {I O I' O' α : Type}

/-! ## The free tree of an erased oracle program -/

/-- The positions of the free tree of an erased oracle program: a query on `i`, or the
computation `c`. -/
inductive EPos (I : Type) : Type 1 where
  /-- Query the oracle on `i`. -/
  | query (i : I)
  /-- Run the computation `c`. -/
  | lift (β : Type) (c : SPComp β)

/-- The directions at a position of `ESig I O`: an answer in `O` or a result in `β`. -/
abbrev EPos.dir (O : Type) {I : Type} : EPos I → Type
  | .query _ => O
  | .lift β _ => β

/-- The polynomial functor of erased oracle programs. -/
abbrev ESig (I O : Type) : PFunctor.{1, 0} := ⟨EPos I, EPos.dir O⟩

/-- The weight `cost i` at a query, `0` at a computation. -/
def EPos.cost (cost : I → ℕ) : EPos I → ℕ
  | .query i => cost i
  | .lift _ _ => 0

/-- The erased oracle program as a tree of `ESig I O`. -/
def toFreeM : OracleProg I O α → FreeM (ESig I O) α
  | .pure a => .pure a
  | .query i k => .liftBind (P := ESig I O) (.query i) fun o => toFreeM (k o)
  | .lift (β := β) c k => .liftBind (P := ESig I O) (.lift β c) fun b => toFreeM (k b)

/-- `QueryCostLe` is the subtractive roll bound of the free tree with charge `EPos.cost`. -/
theorem queryCostLe_iff_isRollBound (cost : I → ℕ) (p : OracleProg I O α) (n : ℕ) :
    QueryCostLe cost p n ↔
      (toFreeM p).IsRollBound n (fun a b => EPos.cost cost a ≤ b)
        (fun a b => b - EPos.cost cost a) := by
  induction p generalizing n with
  | pure a => exact Iff.rfl
  | query i k ih =>
    simp only [QueryCostLe, toFreeM, FreeM.isRollBound_liftBind_iff, EPos.cost, ih]
  | lift c k ih =>
    simp only [QueryCostLe, toFreeM, FreeM.isRollBound_liftBind_iff, EPos.cost, ih,
      Nat.zero_le, Nat.sub_zero, true_and]

/-- **The query bound of an oracle program is a charge fold.** `QueryCostLe cost p n` is the
bound `n` on the worst-case charge fold of the free tree of `p`, charging `cost i` at a query `i`
and `0` at a computation. -/
theorem queryCostLe_iff_wpFold_charge (cost : I → ℕ) (p : OracleProg I O α) (n : ℕ) :
    QueryCostLe cost p n ↔
      wpFold (OpSpec.charge fun a => ((EPos.cost cost a : ℕ) : ℕ∞)) (toFreeM p)
        (fun _ => 0) ≤ n := by
  rw [queryCostLe_iff_isRollBound, FreeM.isRollBound_iff_wpFold_charge]

/-! ## The vector charge of a tick tree -/

/-- The query charge of a position of the tick tree: `cost i` at a query `i`, `0` at a
computation node and at a tick. -/
def queryCharge (cost : I → ℕ) : (SigT I O).A → ℕ
  | .inl (.query i) => cost i
  | .inl (.lift _ _) => 0
  | .inr _ => 0

/-- The vector charge of a tick tree at `{query, tick}`: the query charge at `false`, the tick
charge `tickCost` at `true`. -/
noncomputable def useCharge (cost : I → ℕ) : (SigT I O).A → Bool → ℕ∞
  | a, false => queryCharge cost a
  | a, true => tickCost a

/-- The vector of `q` queries and `T` ticks. -/
def budget (q T : ℕ∞) : Bool → ℕ∞
  | false => q
  | true => T

@[simp] theorem budget_false (q T : ℕ∞) : budget q T false = q := rfl

@[simp] theorem budget_true (q T : ℕ∞) : budget q T true = T := rfl

@[simp] theorem useCharge_false (cost : I → ℕ) (a : (SigT I O).A) :
    useCharge cost a false = queryCharge cost a := rfl

@[simp] theorem useCharge_true (cost : I → ℕ) (a : (SigT I O).A) :
    useCharge cost a true = tickCost a := rfl

/-- The use vector of a costed function with constant use counts `q` and cost `T` is
`budget q T`. -/
theorem Clocked.useVec_const (q T : ℕ) :
    (⟨fun _ => (), fun _ => q, fun _ => T⟩ : Clocked Unit Unit).useVec () = budget q T := by
  funext b
  cases b <;> rfl

namespace Timed

/-- The query bound of an erased costed program is the charge fold of its tick tree at the query
charge. -/
theorem queryCostLe_erase_iff_isRollBound (cost : I → ℕ) (p : Timed I O α) (n : ℕ) :
    QueryCostLe cost p.erase n ↔
      (toFreeMT p).IsRollBound n (fun a b => queryCharge cost a ≤ b)
        (fun a b => b - queryCharge cost a) := by
  induction p generalizing n with
  | pure a => exact Iff.rfl
  | query i c k ih =>
    simp only [erase, QueryCostLe, toFreeMT, FreeM.isRollBound_liftBind_iff, queryCharge, ih,
      Nat.zero_le, Nat.sub_zero, true_and]
    exact and_congr Iff.rfl (forall_congr' fun _ => ⟨fun h _ => h, fun h => h PUnit.unit⟩)
  | lift β t c k ih =>
    simp only [erase, QueryCostLe, toFreeMT, FreeM.isRollBound_liftBind_iff, queryCharge, ih,
      Nat.zero_le, Nat.sub_zero, true_and]
    exact forall_congr' fun _ => ⟨fun h _ => h, fun h => h PUnit.unit⟩

/-- **The query bound over the tick tree.** `QueryCostLe cost p.erase n` is the bound `n` on the
worst-case charge fold of the tick tree of `p` at the query charge. -/
theorem queryCostLe_erase_iff_wpFold_charge (cost : I → ℕ) (p : Timed I O α) (n : ℕ) :
    QueryCostLe cost p.erase n ↔
      wpFold (OpSpec.charge fun a => ((queryCharge cost a : ℕ) : ℕ∞)) (toFreeMT p)
        (fun _ => 0) ≤ n := by
  rw [queryCostLe_erase_iff_isRollBound, FreeM.isRollBound_iff_wpFold_charge]

/-- **Time and queries as one use bound.** The tick tree of `p` has use bound `budget q T` at the
vector charge `useCharge cost` if and only if `p` takes time at most `T` and its queries cost at
most `q`. -/
theorem useBound_iff_timeBound_and_queryCostLe (cost : I → ℕ) (p : Timed I O α) (q T : ℕ) :
    UseBound (useCharge cost) (fun _ _ => True) (toFreeMT p) (budget q T) ↔
      p.TimeBound T ∧ QueryCostLe cost p.erase q := by
  rw [useBound_iff, Bool.forall_bool, timeBound_iff_wpFold_charge,
    queryCostLe_erase_iff_wpFold_charge, ← OpSpec.chargeUnder_true,
    ← OpSpec.chargeUnder_true]
  exact and_comm

/-- **Time and queries of a step-prefixed program as one use bound.** -/
theorem useBound_step_iff (cost : I → ℕ) (x : ℕ × Timed I O α) (q T : ℕ) :
    UseBound (useCharge cost) (fun _ _ => True) (stepToFreeMT x) (budget q T) ↔
      StepTimeBound x T ∧ QueryCostLe cost x.2.erase q := by
  rw [useBound_iff, Bool.forall_bool, stepTimeBound_iff_wpFold_chargeUnder,
    queryCostLe_erase_iff_wpFold_charge, ← OpSpec.chargeUnder_true]
  refine and_comm.trans (and_congr Iff.rfl ?_)
  simp only [useCharge_false, budget_false, stepToFreeMT]
  rw [wpFold_chargeUnder_liftBind_const _ _ _ (b := PUnit.unit) trivial]
  simp [queryCharge]

/-! ## The handlers of `bindQueries` and `collectLog` -/

section Handlers

variable {Q R L : Type}

/-- A charge on the tick positions that is additive in the number of ticks. -/
def TickAdditive (c : (SigT I O).A → ℕ∞) : Prop :=
  c (.inr 0) = 0 ∧ ∀ m n, c (.inr (m + n)) = c (.inr m) + c (.inr n)

theorem tickAdditive_tickCost : TickAdditive (I := I) (O := O) fun a => ((tickCost a : ℕ) : ℕ∞) :=
  ⟨by simp [tickCost], fun m n => by simp [tickCost]⟩

theorem tickAdditive_queryCharge (cost : I → ℕ) :
    TickAdditive (I := I) (O := O) fun a => ((queryCharge cost a : ℕ) : ℕ∞) :=
  ⟨by simp [queryCharge], fun m n => by simp [queryCharge]⟩

/-- The charge fold of a step-prefixed tick tree is the charge of its leading tick plus the fold
of its program. -/
theorem wpFold_stepToFreeMT_eq (c : (SigT I O).A → ℕ∞) (x : ℕ × Timed I O α) (post : α → ℕ∞) :
    wpFold (OpSpec.chargeUnder c fun _ _ => True) (stepToFreeMT x) post =
      c (.inr x.1) + wpFold (OpSpec.chargeUnder c fun _ _ => True) (toFreeMT x.2) post :=
  wpFold_chargeUnder_liftBind_const c _ (.inr x.1) (b := PUnit.unit) trivial _ post

/-- The charge reading at a tick: its charge plus the continuation at the single answer. -/
theorem chargeUnder_tick {I O : Type} (c : (SigT I O).A → ℕ∞) (n : ℕ)
    (k : (SigT I O).B (.inr n) → ℕ∞) :
    OpSpec.chargeUnder c (fun _ _ => True) (.inr n) k = c (.inr n) + k PUnit.unit := by
  rw [OpSpec.chargeUnder_apply]
  exact congrArg (c (.inr n) + ·)
    (le_antisymm (iSup₂_le fun b _ => by cases b; exact le_rfl) (le_iSup₂_of_le PUnit.unit
      trivial le_rfl))

/-- The charge reading at a computation or query position with every answer allowed. -/
theorem chargeUnder_inl {I O : Type} (c : (SigT I O).A → ℕ∞) (a : (Sig I O).A)
    (k : (SigT I O).B (.inl a) → ℕ∞) :
    OpSpec.chargeUnder c (fun _ _ => True) (.inl a) k = c (.inl a) + ⨆ b, k b := by
  rw [OpSpec.chargeUnder_apply]
  simp only [iSup_true]

/-- The charge fold of the tick tree of a query node. -/
theorem wpFold_toFreeMT_query (c : (SigT I O).A → ℕ∞) (i : I) (c' : O → ℕ)
    (k : O → Timed I O α) (post : α → ℕ∞) :
    wpFold (OpSpec.chargeUnder c fun _ _ => True) (toFreeMT (query i c' k)) post =
      c (.inl (.query i)) + ⨆ o, (c (.inr (c' o)) +
        wpFold (OpSpec.chargeUnder c fun _ _ => True) (toFreeMT (k o)) post) := by
  rw [toFreeMT, FreeM.wpFold_liftBind, chargeUnder_inl]
  exact congrArg _ (iSup_congr fun _ => chargeUnder_tick c _ _)

/-- The charge fold of the tick tree of a computation node. -/
theorem wpFold_toFreeMT_lift (c : (SigT I O).A → ℕ∞) (β : Type) (t : SPTree.Timed β)
    (c' : β → ℕ) (k : β → Timed I O α) (post : α → ℕ∞) :
    wpFold (OpSpec.chargeUnder c fun _ _ => True) (toFreeMT (lift β t c' k)) post =
      c (.inl (.lift β t)) + ⨆ b, (c (.inr (c' b)) +
        wpFold (OpSpec.chargeUnder c fun _ _ => True) (toFreeMT (k b)) post) := by
  rw [toFreeMT, FreeM.wpFold_liftBind, chargeUnder_inl]
  exact congrArg _ (iSup_congr fun _ => chargeUnder_tick c _ _)

/-- The pulled-back fold of the tick tree of a query node, for a handler keeping the ticks. -/
theorem wpFold_pullback_toFreeMT_query (c : (SigT I' O').A → ℕ∞)
    (H : (a : (SigT I O).A) → FreeM (SigT I' O') ((SigT I O).B a))
    (hH : ∀ n, H (.inr n) = FreeM.lift (P := SigT I' O') (.inr n)) (i : I) (c' : O → ℕ)
    (k : O → Timed I O α) (post : α → ℕ∞) :
    wpFold ((OpSpec.chargeUnder c fun _ _ => True).pullback H) (toFreeMT (query i c' k)) post =
      wpFold (OpSpec.chargeUnder c fun _ _ => True) (H (.inl (.query i))) fun o =>
        c (.inr (c' o)) +
          wpFold ((OpSpec.chargeUnder c fun _ _ => True).pullback H) (toFreeMT (k o)) post := by
  rw [toFreeMT, FreeM.wpFold_liftBind]
  simp only [OpSpec.pullback, FreeM.wpFold_liftBind, hH, FreeM.wpFold_lift]
  exact congrArg _ (funext fun _ => chargeUnder_tick c _ _)

/-- The pulled-back fold of the tick tree of a computation node, for a handler keeping the
computation nodes and the ticks. -/
theorem wpFold_pullback_toFreeMT_lift (c : (SigT I' O').A → ℕ∞)
    (H : (a : (SigT I O).A) → FreeM (SigT I' O') ((SigT I O).B a))
    (hH : ∀ n, H (.inr n) = FreeM.lift (P := SigT I' O') (.inr n)) (β : Type)
    (t : SPTree.Timed β)
    (hL : H (.inl (.lift β t)) = FreeM.lift (P := SigT I' O') (.inl (.lift β t)))
    (c' : β → ℕ) (k : β → Timed I O α) (post : α → ℕ∞) :
    wpFold ((OpSpec.chargeUnder c fun _ _ => True).pullback H) (toFreeMT (lift β t c' k)) post =
      c (.inl (.lift β t)) + ⨆ b, (c (.inr (c' b)) +
        wpFold ((OpSpec.chargeUnder c fun _ _ => True).pullback H) (toFreeMT (k b)) post) := by
  rw [toFreeMT, FreeM.wpFold_liftBind]
  simp only [OpSpec.pullback, FreeM.wpFold_liftBind, hH, hL, FreeM.wpFold_lift]
  exact (chargeUnder_inl c _ _).trans (congrArg _ (iSup_congr fun _ => chargeUnder_tick c _ _))

/-- The bind clause of the tick tree at a tick-additive charge. -/
theorem wpFold_stepToFreeMT_bind_of_tickAdditive {β : Type} {c : (SigT I O).A → ℕ∞}
    (hc : TickAdditive c) (p : Timed I O α) (f : α → ℕ × Timed I O β) (post : β → ℕ∞) :
    wpFold (OpSpec.chargeUnder c fun _ _ => True) (stepToFreeMT (p.bind f)) post =
      wpFold (OpSpec.chargeUnder c fun _ _ => True) (toFreeMT p)
        (fun a => wpFold (OpSpec.chargeUnder c fun _ _ => True) (stepToFreeMT (f a)) post) := by
  have htick : ∀ {γ : Type} (n : ℕ) (y : FreeM (SigT I O) γ) (q : γ → ℕ∞),
      wpFold (OpSpec.chargeUnder c fun _ _ => True)
        (FreeM.liftBind (P := SigT I O) (.inr n) fun _ => y) q =
      c (.inr n) + wpFold (OpSpec.chargeUnder c fun _ _ => True) y q :=
    fun n y q => wpFold_chargeUnder_liftBind_const c _ (.inr n) (b := PUnit.unit) trivial y q
  induction p with
  | pure a => rfl
  | query i c' k ih =>
    rw [wpFold_stepToFreeMT_eq]
    simp only [bind, toFreeMT, FreeM.wpFold_liftBind, OpSpec.chargeUnder_apply, htick, hc.1,
      zero_add]
    refine congrArg _ (iSup_congr fun b => iSup_congr fun _ => ?_)
    rw [← ih b, wpFold_stepToFreeMT_eq, hc.2, add_assoc]
  | lift γ t c' k ih =>
    rw [wpFold_stepToFreeMT_eq]
    simp only [bind, toFreeMT, FreeM.wpFold_liftBind, OpSpec.chargeUnder_apply, htick, hc.1,
      zero_add]
    refine congrArg _ (iSup_congr fun b => iSup_congr fun _ => ?_)
    rw [← ih b, wpFold_stepToFreeMT_eq, hc.2, add_assoc]

/-- The free handler of `bindQueries h`: a query `i` is the step-prefixed tick tree of `h i`, a
computation node and a tick are kept. -/
def bqHandler (h : I → ℕ × Timed I' O' O) :
    (a : (SigT I O).A) → FreeM (SigT I' O') ((SigT I O).B a)
  | .inl (.query i) => stepToFreeMT (h i)
  | .inl (.lift β t) => FreeM.lift (P := SigT I' O') (.inl (.lift β t))
  | .inr n => FreeM.lift (P := SigT I' O') (.inr n)

/-- **`bindQueries` is an interpretation of the tick tree.** At a tick-additive charge, the
charge fold of the costed `bindQueries h p` is the fold of the tick tree of `p` interpreted by
`bqHandler h`. -/
theorem wpFold_stepToFreeMT_bindQueries {c : (SigT I' O').A → ℕ∞} (hc : TickAdditive c)
    (h : I → ℕ × Timed I' O' O) (p : Timed I O α) (post : α → ℕ∞) :
    wpFold (OpSpec.chargeUnder c fun _ _ => True) (stepToFreeMT (bindQueries h p)) post =
      wpFold (OpSpec.chargeUnder c fun _ _ => True) ((toFreeMT p).liftM (bqHandler h)) post := by
  rw [FreeM.wpFold_liftM]
  induction p with
  | pure a =>
    rw [bindQueries, wpFold_stepToFreeMT_eq, hc.1, zero_add]
    rfl
  | query i c' k ih =>
    rw [wpFold_pullback_toFreeMT_query c (bqHandler h) (fun _ => rfl), bindQueries, delay,
      wpFold_stepToFreeMT_eq, hc.2, add_assoc, ← wpFold_stepToFreeMT_eq c ((h i).2.bind _),
      wpFold_stepToFreeMT_bind_of_tickAdditive hc, ← wpFold_stepToFreeMT_eq c (h i)]
    refine congrArg _ (funext fun o => ?_)
    rw [delay, wpFold_stepToFreeMT_eq, hc.2, add_assoc, ← wpFold_stepToFreeMT_eq, ih o]
  | lift γ t c' k ih =>
    rw [wpFold_pullback_toFreeMT_lift c (bqHandler h) (fun _ => rfl) γ t rfl, bindQueries,
      wpFold_stepToFreeMT_eq, hc.1, zero_add, wpFold_toFreeMT_lift]
    refine congrArg _ (iSup_congr fun b => ?_)
    rw [hc.2, add_assoc, ← wpFold_stepToFreeMT_eq, ih b]

/-- A constant added to the postcondition of a charge fold is at most the constant added to the
fold: the constant is not charged on a branch with no answer. -/
theorem wpFold_chargeUnder_const_add_le {P : PFunctor.{1, 0}} {X : Type} (c : P.A → ℕ∞)
    (allows : (a : P.A) → P.B a → Prop) (x : FreeM P X) (k : ℕ∞) (post : X → ℕ∞) :
    wpFold (OpSpec.chargeUnder c allows) x (fun r => k + post r) ≤
      k + wpFold (OpSpec.chargeUnder c allows) x post := by
  induction x with
  | pure r => exact le_rfl
  | lift_bind a r ih =>
    change c a + ⨆ b, ⨆ (_ : allows a b), wpFold (OpSpec.chargeUnder c allows) (r b) _ ≤
      k + (c a + ⨆ b, ⨆ (_ : allows a b), wpFold (OpSpec.chargeUnder c allows) (r b) post)
    rw [add_left_comm]
    refine add_le_add le_rfl (iSup₂_le fun b hb => (ih b).trans (add_le_add le_rfl ?_))
    exact le_iSup₂_of_le (f := fun b (_ : allows a b) =>
      wpFold (OpSpec.chargeUnder c allows) (r b) post) b hb le_rfl

/-- The charge reading under allowed answers is monotone in the continuation. -/
theorem chargeUnder_monotone {P : PFunctor.{1, 0}} (c : P.A → ℕ∞)
    (allows : (a : P.A) → P.B a → Prop) : (OpSpec.chargeUnder c allows).Monotone := by
  intro a k k' hk
  rw [OpSpec.chargeUnder_apply, OpSpec.chargeUnder_apply]
  exact add_le_add le_rfl (iSup₂_mono fun b _ => hk b)

/-- The free handler of `collectLog h`: a query `x` is the step-prefixed tick tree of `h x`
followed by the tick `2 * l + 1` of appending its records of length `l`, returning the answer;
a computation node and a tick are kept. -/
def clHandler (h : Q → ℕ × Timed I O (R × List L)) :
    (a : (SigT Q R).A) → FreeM (SigT I O) ((SigT Q R).B a)
  | .inl (.query x) => (stepToFreeMT (h x)).bind fun rl =>
      FreeM.liftBind (P := SigT I O) (.inr (2 * rl.2.length + 1)) fun _ => .pure rl.1
  | .inl (.lift β t) => FreeM.lift (P := SigT I O) (.inl (.lift β t))
  | .inr n => FreeM.lift (P := SigT I O) (.inr n)

/-- **`collectLog` is bounded by an interpretation of the tick tree.** At a tick-additive
charge, the charge fold of the costed `collectLog h p`, at a postcondition of the result, is at
most the fold of the tick tree of `p` interpreted by `clHandler h`. The handler charges the
record append before the rest of the program, `collectLog` after it. -/
theorem wpFold_stepToFreeMT_collectLog_le {c : (SigT I O).A → ℕ∞} (hc : TickAdditive c)
    (h : Q → ℕ × Timed I O (R × List L)) (p : Timed Q R α) (post : α → ℕ∞) :
    wpFold (OpSpec.chargeUnder c fun _ _ => True) (stepToFreeMT (collectLog h p))
        (fun al => post al.1) ≤
      wpFold (OpSpec.chargeUnder c fun _ _ => True) ((toFreeMT p).liftM (clHandler h)) post := by
  rw [FreeM.wpFold_liftM]
  induction p generalizing post with
  | pure a =>
    rw [collectLog, wpFold_stepToFreeMT_eq, hc.1, zero_add]
    exact le_rfl
  | query x c' k ih =>
    rw [wpFold_pullback_toFreeMT_query c (clHandler h) (fun _ => rfl), collectLog, delay,
      wpFold_stepToFreeMT_eq, hc.2, add_assoc, ← wpFold_stepToFreeMT_eq c ((h x).2.bind _),
      wpFold_stepToFreeMT_bind_of_tickAdditive hc, ← wpFold_stepToFreeMT_eq c (h x)]
    simp only [clHandler, FreeM.wpFold_bind', FreeM.wpFold_liftBind]
    refine FreeM.wpFold_mono (chargeUnder_monotone _ _) _ fun rl => ?_
    rw [delay, wpFold_stepToFreeMT_eq, hc.2, add_assoc, delay, hc.2, add_assoc,
      ← wpFold_stepToFreeMT_eq c ((collectLog h (k rl.1)).2.bind _),
      wpFold_stepToFreeMT_bind_of_tickAdditive hc]
    simp only [wpFold_stepToFreeMT_eq, toFreeMT]
    rw [← wpFold_stepToFreeMT_eq c (collectLog h (k rl.1))]
    refine le_of_le_of_eq ?_ (chargeUnder_tick c _ _).symm
    change c (.inr (c' rl.1)) + wpFold (OpSpec.chargeUnder c fun _ _ => True)
        (stepToFreeMT (collectLog h (k rl.1)))
        (fun a => c (.inr (2 * rl.2.length + 1)) + post a.1) ≤
      c (.inr (2 * rl.2.length + 1)) + (c (.inr (c' rl.1)) +
        wpFold ((OpSpec.chargeUnder c fun _ _ => True).pullback (clHandler h)) (toFreeMT (k rl.1))
          post)
    rw [add_left_comm (c (.inr (2 * rl.2.length + 1)))]
    refine add_le_add le_rfl ((ih rl.1 fun a => c (.inr (2 * rl.2.length + 1)) + post a).trans ?_)
    rw [← FreeM.wpFold_liftM, ← FreeM.wpFold_liftM]
    exact wpFold_chargeUnder_const_add_le _ _ _ _ _
  | lift γ t c' k ih =>
    rw [wpFold_pullback_toFreeMT_lift c (clHandler h) (fun _ => rfl) γ t rfl, collectLog,
      wpFold_stepToFreeMT_eq, hc.1, zero_add, wpFold_toFreeMT_lift]
    refine add_le_add le_rfl (iSup_mono fun b => ?_)
    rw [hc.2, add_assoc, ← wpFold_stepToFreeMT_eq]
    exact add_le_add le_rfl (ih b post)

/-! ## The composition rule at `{query, tick}` -/

/-- Each component of the vector charge is tick-additive. -/
theorem tickAdditive_useCharge (cost : I → ℕ) (j : Bool) :
    TickAdditive (I := I) (O := O) fun a => useCharge cost a j := by
  cases j
  · exact tickAdditive_queryCharge cost
  · exact tickAdditive_tickCost

/-- The demand of one call of a query handler of use vector `d`: a query demands `d`, a tick
demands one tick. At `d = f.useVec a` this is `Clocked.callDemand f a`. -/
def queryDemand (d : Bool → ℕ∞) : Bool → Bool → ℕ∞
  | false => d
  | true => Pi.single true 1

theorem queryDemand_useVec {X Y : Type} (f : Clocked X Y) (a : X) :
    queryDemand (f.useVec a) = f.callDemand a := by
  funext j
  cases j <;> rfl

/-- The tick tree of one operation has its charge as use bound. -/
theorem useBound_lift {P : PFunctor.{1, 0}} {ι : Type} (c : P.A → ι → ℕ∞) (a : P.A) :
    UseBound c (fun _ _ => True) (FreeM.lift (P := P) a) (c a) := by
  rw [UseBound, FreeM.wpFold_lift, OpSpec.chargeUnder_apply]
  simp only [iSup_true]
  have h0 : (⨆ _ : P.B a, (0 : ι → ℕ∞)) = 0 :=
    le_antisymm (iSup_le fun _ => le_rfl) (Pi.le_def.2 fun _ => zero_le)
  rw [h0, add_zero]

/-- The use bound of a handler that keeps a computation node or a tick: the demand of that
position. -/
theorem useBound_keep (cost' : I' → ℕ) (d : Bool → ℕ∞) (a : (SigT I O).A)
    (a' : (SigT I' O').A) (ha : ∀ j, useCharge cost' a' j = useCharge (fun _ => 1) a j)
    (hq : useCharge (fun _ => 1) a false = 0) :
    UseBound (useCharge cost') (fun _ _ => True) (FreeM.lift (P := SigT I' O') a')
      (∑ j, useCharge (fun _ => 1) a j • queryDemand d j) := by
  refine (useBound_lift _ a').mono fun j => ?_
  rw [ha j]
  cases j <;> simp [queryDemand, hq]

/-- The use bound of each call of `bqHandler h`, from a use bound `d` of each handler program. -/
theorem useBound_bqHandler (cost' : I' → ℕ) {h : I → ℕ × Timed I' O' O} {d : Bool → ℕ∞}
    (hh : ∀ i, UseBound (useCharge cost') (fun _ _ => True) (stepToFreeMT (h i)) d)
    (a : (SigT I O).A) :
    UseBound (useCharge cost') (fun _ _ => True) (bqHandler h a)
      (∑ j, useCharge (fun _ => 1) a j • queryDemand d j) := by
  rcases a with (i | ⟨β, t⟩) | n
  · refine (hh i).mono fun j => ?_
    cases j <;> simp [queryDemand, queryCharge, tickCost]
  · exact useBound_keep cost' d _ _ (fun j => by cases j <;> rfl) rfl
  · exact useBound_keep cost' d _ _ (fun j => by cases j <;> rfl) rfl

/-- **Use bound of `bindQueries`, the composition rule at `{query, tick}`.** If the tick tree of
`p` has use bound `u` (queries at `false`, ticks at `true`) and each handler program has use
bound `d`, then `bindQueries h p` has use bound `∑ j, u j • queryDemand d j`: queries
`u false * d false`, time `u false * d true + u true`. -/
theorem useBound_bindQueries (cost' : I' → ℕ) {h : I → ℕ × Timed I' O' O} {p : Timed I O α}
    {u d : Bool → ℕ∞}
    (hp : UseBound (useCharge (fun _ => 1)) (fun _ _ => True) (toFreeMT p) u)
    (hh : ∀ i, UseBound (useCharge cost') (fun _ _ => True) (stepToFreeMT (h i)) d) :
    UseBound (useCharge cost') (fun _ _ => True) (stepToFreeMT (bindQueries h p))
      (∑ j, u j • queryDemand d j) := by
  have hl := useBound_liftM hp (useBound_bqHandler cost' hh)
    (fun _ => FreeM.wpFold_demonicUnder_true _ _)
  rw [useBound_iff] at hl ⊢
  intro j
  rw [wpFold_stepToFreeMT_bindQueries (tickAdditive_useCharge cost' j)]
  exact hl j

/-- **Time and queries of `bindQueries` (Diller–Nahm composition).** A program of time `T` with
at most `q` queries, each replaced by a handler program of time `t` with queries of cost at most
`q'`, runs in time `T + q * t` and its queries cost at most `q * q'`: the use vector of
`Clocked.comp` at uses `q`, `q'` and costs `T`, `t`. -/
theorem stepTimeBound_bindQueries_queryCostLe (cost' : I' → ℕ) {h : I → ℕ × Timed I' O' O}
    {t q' : ℕ} (hh : ∀ i, StepTimeBound (h i) t ∧ QueryCostLe cost' (h i).2.erase q')
    {p : Timed I O α} {T q : ℕ} (hp : p.TimeBound T) (hq : QueryCostLe (fun _ => 1) p.erase q) :
    StepTimeBound (bindQueries h p) (T + q * t) ∧
      QueryCostLe cost' (bindQueries h p).2.erase (q * q') := by
  let g : Clocked Unit Unit := ⟨fun _ => (), fun _ => q, fun _ => T⟩
  let f : Clocked Unit Unit := ⟨fun _ => (), fun _ => q', fun _ => t⟩
  have hx : UseBound (useCharge (fun _ => 1)) (fun _ _ => True) (toFreeMT p)
      (g.useVec (f.fn ())) := by
    rw [Clocked.useVec_const]
    exact (useBound_iff_timeBound_and_queryCostLe _ p q T).2 ⟨hp, hq⟩
  have hl := useBound_liftM_clocked g f () hx (fun a => by
    rw [← queryDemand_useVec, Clocked.useVec_const]
    exact useBound_bqHandler cost' (fun i => (useBound_step_iff _ _ q' t).2 (hh i)) a)
    (fun _ => FreeM.wpFold_demonicUnder_true _ _)
  have hc : (Clocked.comp g f).useVec () = budget ((q * q' : ℕ) : ℕ∞) ((T + q * t : ℕ) : ℕ∞) := by
    funext j
    cases j <;> rfl
  rw [hc] at hl
  refine (useBound_step_iff cost' _ _ _).1 ?_
  rw [useBound_iff] at hl ⊢
  intro j
  rw [wpFold_stepToFreeMT_bindQueries (tickAdditive_useCharge cost' j)]
  exact hl j

/-- The use bound `budget ⊤ T` of a step-prefixed program is its time bound `T`. -/
theorem useBound_top_of_stepTimeBound (cost : I → ℕ) {x : ℕ × Timed I O α} {T : ℕ}
    (hx : StepTimeBound x T) :
    UseBound (useCharge cost) (fun _ _ => True) (stepToFreeMT x) (budget ⊤ T) := by
  rw [useBound_iff, Bool.forall_bool]
  exact ⟨le_top, (stepTimeBound_iff_wpFold_chargeUnder x T).1 hx⟩

/-- The time component of a use bound of a step-prefixed program. -/
theorem stepTimeBound_of_useBound_true (cost : I → ℕ) {x : ℕ × Timed I O α} {u : Bool → ℕ∞}
    {T : ℕ} (hx : UseBound (useCharge cost) (fun _ _ => True) (stepToFreeMT x) u)
    (hT : u true ≤ T) : StepTimeBound x T :=
  (stepTimeBound_iff_wpFold_chargeUnder x T).2 (((useBound_iff _ _ _ _).1 hx true).trans hT)

/-- **Time of replacing queries by handler programs.** A program of time `T` with at most `q`
queries, each replaced by a handler program of time at most `t`, runs in time `T + q * t`: the
time component of `useBound_bindQueries`, with no bound on the queries of the handler. -/
theorem timeBound_bindQueries {h : I → ℕ × Timed I' O' O} {t : ℕ}
    (hh : ∀ i, StepTimeBound (h i) t) {p : Timed I O α} {T q : ℕ} (hp : p.TimeBound T)
    (hq : QueryCostLe (fun _ => 1) p.erase q) :
    StepTimeBound (bindQueries h p) (T + q * t) := by
  have hu := useBound_bindQueries (fun _ => 0)
    ((useBound_iff_timeBound_and_queryCostLe _ p q T).2 ⟨hp, hq⟩)
    (fun i => useBound_top_of_stepTimeBound _ (hh i))
  refine stepTimeBound_of_useBound_true _ hu (le_of_eq ?_)
  simp [queryDemand]

/-- The use bound of each call of `clHandler h`, from a use bound `d` of each handler program
whose records have length at most `ℓ`: the handler adds the tick `2 * ℓ + 1` of the append. -/
theorem useBound_clHandler (cost : I → ℕ) {h : Q → ℕ × Timed I O (R × List L)}
    {d : Bool → ℕ∞} {ℓ : ℕ}
    (hh : ∀ x, UseBound (useCharge cost) (fun _ _ => True) (stepToFreeMT (h x)) d)
    (hl : ∀ x, (h x).2.AllRet fun rl => rl.2.length ≤ ℓ) (a : (SigT Q R).A) :
    UseBound (useCharge cost) (fun _ _ => True) (clHandler h a)
      (∑ j, useCharge (fun _ => 1) a j • queryDemand (d + budget 0 (2 * ℓ + 1 : ℕ)) j) := by
  rcases a with (x | ⟨β, t⟩) | n
  · rw [useBound_iff]
    intro j
    have hdem : wpFold (OpSpec.demonicUnder fun _ _ => True) (stepToFreeMT (h x))
        fun rl => rl.2.length ≤ ℓ :=
      fun _ _ => (allRet_iff_wpFold_demonicUnder _ _).1 (hl x)
    simp only [clHandler, FreeM.wpFold_bind']
    have hstep : ∀ rl : R × List L,
        wpFold (OpSpec.chargeUnder (fun a => useCharge cost a j) fun _ _ => True)
          (FreeM.liftBind (P := SigT I O) (.inr (2 * rl.2.length + 1)) fun _ =>
            (FreeM.pure rl.1 : FreeM (SigT I O) R)) (fun _ => 0) =
          useCharge cost (.inr (2 * rl.2.length + 1)) j + 0 :=
      fun rl => wpFold_chargeUnder_liftBind_const _ _ _ (b := PUnit.unit) trivial _ _
    refine (FreeM.wpFold_mono (chargeUnder_monotone _ _) _ fun rl => (hstep rl).le).trans ?_
    refine (wpFold_chargeUnder_le_add_of_demonicUnder _ _ hdem
      (k := useCharge (O := O) cost (.inr (2 * ℓ + 1)) j) fun rl hrl => ?_).trans ?_
    · cases j
      · simp [queryCharge]
      · simp [tickCost]
        omega
    · have := (useBound_iff _ _ _ _).1 (hh x) j
      refine (add_le_add this le_rfl).trans ?_
      cases j <;> simp [queryDemand, queryCharge, tickCost]
  · exact useBound_keep cost _ _ _ (fun j => by cases j <;> rfl) rfl
  · exact useBound_keep cost _ _ _ (fun j => by cases j <;> rfl) rfl

/-- **Use bound of `collectLog`, the composition rule at `{query, tick}`.** If the tick tree of
`p` has use bound `u` and each handler program has use bound `d` and records of length at most
`ℓ`, then `collectLog h p` has use bound `∑ j, u j • queryDemand (d + budget 0 (2 * ℓ + 1)) j`.
-/
theorem useBound_collectLog (cost : I → ℕ) {h : Q → ℕ × Timed I O (R × List L)}
    {p : Timed Q R α} {u d : Bool → ℕ∞} {ℓ : ℕ}
    (hp : UseBound (useCharge (fun _ => 1)) (fun _ _ => True) (toFreeMT p) u)
    (hh : ∀ x, UseBound (useCharge cost) (fun _ _ => True) (stepToFreeMT (h x)) d)
    (hl : ∀ x, (h x).2.AllRet fun rl => rl.2.length ≤ ℓ) :
    UseBound (useCharge cost) (fun _ _ => True) (stepToFreeMT (collectLog h p))
      (∑ j, u j • queryDemand (d + budget 0 (2 * ℓ + 1 : ℕ)) j) := by
  have hm := useBound_liftM hp (useBound_clHandler cost hh hl)
    (fun _ => FreeM.wpFold_demonicUnder_true _ _)
  rw [useBound_iff] at hm ⊢
  intro j
  exact (wpFold_stepToFreeMT_collectLog_le (tickAdditive_useCharge cost j) h p fun _ => 0).trans
    (hm j)

/-- **Time and queries of `collectLog` (Diller–Nahm composition).** A program of time `T` with
at most `q` queries, each replaced by a handler program of time `t` with queries of cost at most
`q'` and records of length at most `ℓ`, runs in time `T + q * (t + 2 * ℓ + 1)` and its queries
cost at most `q * q'`: the use vector of `Clocked.comp` at uses `q`, `q'` and costs `T`,
`t + 2 * ℓ + 1`. -/
theorem stepTimeBound_collectLog_queryCostLe (cost : I → ℕ)
    {h : Q → ℕ × Timed I O (R × List L)} {t q' ℓ : ℕ}
    (hh : ∀ x, StepTimeBound (h x) t ∧ QueryCostLe cost (h x).2.erase q')
    (hl : ∀ x, (h x).2.AllRet fun rl => rl.2.length ≤ ℓ)
    {p : Timed Q R α} {T q : ℕ} (hp : p.TimeBound T) (hq : QueryCostLe (fun _ => 1) p.erase q) :
    StepTimeBound (collectLog h p) (T + q * (t + 2 * ℓ + 1)) ∧
      QueryCostLe cost (collectLog h p).2.erase (q * q') := by
  let g : Clocked Unit Unit := ⟨fun _ => (), fun _ => q, fun _ => T⟩
  let f : Clocked Unit Unit := ⟨fun _ => (), fun _ => q', fun _ => t + 2 * ℓ + 1⟩
  have hx : UseBound (useCharge (fun _ => 1)) (fun _ _ => True) (toFreeMT p)
      (g.useVec (f.fn ())) := by
    rw [Clocked.useVec_const]
    exact (useBound_iff_timeBound_and_queryCostLe _ p q T).2 ⟨hp, hq⟩
  have hd : budget (q' : ℕ∞) (t : ℕ∞) + budget 0 ((2 * ℓ + 1 : ℕ) : ℕ∞) = f.useVec () := by
    funext j
    cases j
    · simp [Clocked.useVec, f]
    · simp [Clocked.useVec, f, add_assoc]
  have hl' := useBound_liftM_clocked g f () hx (fun a => by
    rw [← queryDemand_useVec, ← hd]
    exact useBound_clHandler cost (fun x => (useBound_step_iff _ _ q' t).2 (hh x)) hl a)
    (fun _ => FreeM.wpFold_demonicUnder_true _ _)
  have hc : (Clocked.comp g f).useVec () =
      budget ((q * q' : ℕ) : ℕ∞) ((T + q * (t + 2 * ℓ + 1) : ℕ) : ℕ∞) := by
    funext j
    cases j <;> rfl
  rw [hc] at hl'
  refine (useBound_step_iff cost _ _ _).1 ?_
  rw [useBound_iff] at hl' ⊢
  intro j
  exact (wpFold_stepToFreeMT_collectLog_le (tickAdditive_useCharge cost j) h p fun _ => 0).trans
    (hl' j)

/-- **Time of collecting the records of handler programs.** A program of time `T` with at most
`q` queries, each replaced by a handler program of time at most `t` whose records have length
at most `ℓ`, runs in time `T + q * (t + 2 * ℓ + 1)`: the time component of
`useBound_collectLog`, with no bound on the queries of the handler. -/
theorem timeBound_collectLog {h : Q → ℕ × Timed I O (R × List L)} {t ℓ : ℕ}
    (hh : ∀ x, StepTimeBound (h x) t) (hl : ∀ x, (h x).2.AllRet fun rl => rl.2.length ≤ ℓ)
    {p : Timed Q R α} {T q : ℕ} (hp : p.TimeBound T)
    (hq : QueryCostLe (fun _ => 1) p.erase q) :
    StepTimeBound (collectLog h p) (T + q * (t + 2 * ℓ + 1)) := by
  have hu := useBound_collectLog (fun _ => 0)
    ((useBound_iff_timeBound_and_queryCostLe _ p q T).2 ⟨hp, hq⟩)
    (fun x => useBound_top_of_stepTimeBound _ (hh x)) hl
  refine stepTimeBound_of_useBound_true _ hu (le_of_eq ?_)
  simp [queryDemand]
  ring

end Handlers

end Timed

end OracleProg

end CatCrypt.Crypto
