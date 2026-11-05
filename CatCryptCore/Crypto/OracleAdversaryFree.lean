/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleAdversaryTimed
public import CatCryptCore.Crypto.OracleForkingLemma
public import PolyFun.PFunctor.Free.WP.Charge
public import CatCryptCore.ForMathlib.PFunctorChargeUnder
public import CatCryptCore.Tactics.DeriveTimed

/-!
# Oracle adversaries as free monads of a polynomial functor

`OracleAdv D R α` is the free monad `PFunctor.FreeM (AdvSig D R) α` of the polynomial
functor `AdvSig D R`, whose positions are the sampling nodes `rand β p` (directions `β`) and
the queries `query d` (directions `R`).

* `OracleAdv.equivFreeM` — the equivalence `OracleAdv D R α ≃ FreeM (AdvSig D R) α`
* `OracleAdv.run_eq_liftM` — `run O` is `FreeM.liftM` into `StateT S PMF`
* `OracleAdv.toFreeM_mapQuery` — `mapQuery c` is `FreeM.mapLens` along `AdvSig.queryLens c`
* `OracleAdv.isQueryBoundBy_iff_isRollBound`, `OracleAdv.isQueryBound_iff_isRollBound`,
  `OracleAdv.isQueryBound₂_iff_isRollBound` — the query bounds are roll bounds
* `OracleAdv.Timed.timeBound_iff_isRollBound`, `OracleAdv.Timed.timeBound_iff_wpFold_charge` —
  the time bound of a costed adversary is the subtractive roll bound, equivalently the charge
  fold bound, on the tree with a `tick (c x)` node after every direction `x`
* `OracleAdv.Timed.stepTimeBound_iff_wpFold_chargeUnder` — `StepTimeBound` is the bound on the
  charge fold of the step-prefixed tick tree `OracleAdv.Timed.stepToFreeMT`
* `OracleAdv.Timed.wpFold_stepToFreeMT_bind` — the charge fold of a costed bind is the charge
  fold of the bind of the tick trees
* `OracleAdv.Timed.allRet_iff_wpFold_demonicUnder` — `AllRet` is the demonic fold of the tick
  tree
-/

@[expose] public section

namespace CatCrypt.Crypto

open PFunctor

/-- The positions of `AdvSig D R`: sample from `p : PMF β`, or query the oracle at `d`. -/
inductive AdvPos (D : Type) : Type 1 where
  /-- Sample from `p`. -/
  | rand (β : Type) (p : PMF β)
  /-- Query the oracle at `d`. -/
  | query (d : D)

/-- The directions at a position of `AdvSig D R`: a sample in `β` or an answer in `R`. -/
abbrev AdvPos.dir (R : Type) {D : Type} : AdvPos D → Type
  | .rand β _ => β
  | .query _ => R

/-- The polynomial functor of oracle adversaries: positions `AdvPos D`, directions
`AdvPos.dir R`. -/
abbrev AdvSig (D R : Type) : PFunctor.{1, 0} := ⟨AdvPos D, AdvPos.dir R⟩

namespace AdvSig

variable {D D₀ R : Type}

/-- The lens that renames each query `d` to `c d` and fixes the sampling positions. -/
def queryLens (c : D → D₀) : Lens (AdvSig D R) (AdvSig D₀ R) where
  toFunA
    | .rand β p => .rand β p
    | .query d => .query (c d)
  toFunB
    | .rand _ _ => id
    | .query _ => id

/-- The query cost of a position: `0` at a sampling node, `cost d` at a query `d`. -/
def posCost (cost : D → ℕ) : AdvPos D → ℕ
  | .rand _ _ => 0
  | .query d => cost d

/-- The budget check of a two-kind query bound: a query in `D₁` needs a positive first
component, a query in `D₂` a positive second component. -/
def canRoll₂ {D₁ D₂ : Type} : AdvPos (D₁ ⊕ D₂) → ℕ × ℕ → Prop
  | .rand _ _, _ => True
  | .query (.inl _), b => 0 < b.1
  | .query (.inr _), b => 0 < b.2

/-- The budget update of a two-kind query bound: decrement the component of the query's kind. -/
def cost₂ {D₁ D₂ : Type} : AdvPos (D₁ ⊕ D₂) → ℕ × ℕ → ℕ × ℕ
  | .rand _ _, b => b
  | .query (.inl _), b => (b.1 - 1, b.2)
  | .query (.inr _), b => (b.1, b.2 - 1)

end AdvSig

namespace OracleAdv

variable {D R α : Type}

/-- The adversary `A` as a tree of the free monad of `AdvSig D R`. -/
def toFreeM : OracleAdv D R α → FreeM (AdvSig D R) α
  | ret a => .pure a
  | rand p k => .liftBind (.rand _ p) fun b => toFreeM (k b)
  | query d k => .liftBind (.query d) fun r => toFreeM (k r)

/-- The oracle adversary of a tree of the free monad of `AdvSig D R`. -/
def ofFreeM : FreeM (AdvSig D R) α → OracleAdv D R α
  | .pure a => ret a
  | .liftBind (.rand _ p) k => rand p fun b => ofFreeM (k b)
  | .liftBind (.query d) k => query d fun r => ofFreeM (k r)

@[simp] theorem ofFreeM_toFreeM (A : OracleAdv D R α) : ofFreeM (toFreeM A) = A := by
  induction A with
  | ret a => rfl
  | rand p k ih => simp only [toFreeM, ofFreeM, ih]
  | query d k ih => simp only [toFreeM, ofFreeM, ih]

@[simp] theorem toFreeM_ofFreeM : ∀ x : FreeM (AdvSig D R) α, toFreeM (ofFreeM x) = x
  | .pure a => rfl
  | .liftBind (.rand _ p) k => by
    simp only [ofFreeM, toFreeM, toFreeM_ofFreeM]
  | .liftBind (.query d) k => by
    simp only [ofFreeM, toFreeM, toFreeM_ofFreeM]

/-- Oracle adversaries are the trees of the free monad of `AdvSig D R`. -/
def equivFreeM : OracleAdv D R α ≃ FreeM (AdvSig D R) α where
  toFun := toFreeM
  invFun := ofFreeM
  left_inv := ofFreeM_toFreeM
  right_inv := toFreeM_ofFreeM

/-! ## Running -/

/-- The handler of `AdvSig D R` in `StateT S PMF`: a sampling node samples, a query asks
the stateful oracle `O`. -/
noncomputable def runHandler {S : Type} (O : S → D → PMF (R × S)) :
    (a : AdvPos D) → StateT S PMF (AdvPos.dir R a)
  | .rand _ p => fun s => p.bind fun b => PMF.pure (b, s)
  | .query d => fun s => O s d

/-- Running `A` against `O` is interpreting its tree in `StateT S PMF` by `runHandler O`. -/
theorem run_eq_liftM {S : Type} (O : S → D → PMF (R × S)) (A : OracleAdv D R α) (s : S) :
    run O A s = FreeM.liftM (P := AdvSig D R) (runHandler O) (toFreeM A) s := by
  induction A generalizing s with
  | ret a => rfl
  | rand p k ih =>
    simp only [run_rand, toFreeM, FreeM.liftM, runHandler, ih]
    change _ = StateT.run (_ >>= _) s
    rw [StateT.run_bind]
    change _ = PMF.bind (PMF.bind p _) _
    simp only [PMF.bind_bind, PMF.pure_bind]
    rfl
  | query d k ih =>
    simp only [run_query, toFreeM, FreeM.liftM, runHandler, ih]
    change _ = StateT.run (_ >>= _) s
    rw [StateT.run_bind]
    rfl

/-! ## Renaming queries -/

/-- Renaming the queries of `A` by `c` is transporting its tree along `AdvSig.queryLens c`. -/
theorem toFreeM_mapQuery {D₀ : Type} (c : D → D₀) (A : OracleAdv D R α) :
    toFreeM (mapQuery c A) = (toFreeM A).mapLens (AdvSig.queryLens c) := by
  induction A with
  | ret a => rfl
  | rand p k ih => simp only [mapQuery, toFreeM, FreeM.mapLens_liftBind, ih]; rfl
  | query d k ih => simp only [mapQuery, toFreeM, FreeM.mapLens_liftBind, ih]; rfl

/-! ## Query bounds as roll bounds -/

/-- The weighted query bound is the subtractive roll bound with cost `0` at sampling nodes
and `cost d` at a query `d`. -/
theorem isQueryBoundBy_iff_isRollBound (cost : D → ℕ) (A : OracleAdv D R α) (n : ℕ) :
    A.IsQueryBoundBy cost n ↔
      (toFreeM A).IsRollBound n (fun a b => AdvSig.posCost cost a ≤ b)
        (fun a b => b - AdvSig.posCost cost a) := by
  induction A generalizing n with
  | ret a => exact Iff.rfl
  | rand p k ih =>
    simp only [IsQueryBoundBy, toFreeM, FreeM.isRollBound_liftBind_iff, AdvSig.posCost,
      Nat.zero_le, Nat.sub_zero, true_and, ih]
  | query d k ih =>
    simp only [IsQueryBoundBy, toFreeM, FreeM.isRollBound_liftBind_iff, AdvSig.posCost, ih]

/-- The query bound is the weighted roll bound with cost `1` at queries and `0` at sampling
nodes. -/
theorem isQueryBound_iff_isRollBound (A : OracleAdv D R α) (q : ℕ) :
    A.IsQueryBound q ↔
      (toFreeM A).IsRollBound q (fun a b => AdvSig.posCost (fun _ => 1) a ≤ b)
        (fun a b => b - AdvSig.posCost (fun _ => 1) a) := by
  induction A generalizing q with
  | ret a => exact Iff.rfl
  | rand p k ih =>
    simp only [IsQueryBound, toFreeM, FreeM.isRollBound_liftBind_iff, AdvSig.posCost,
      Nat.zero_le, Nat.sub_zero, true_and, ih]
  | query d k ih =>
    cases q with
    | zero => simp [IsQueryBound, toFreeM, AdvSig.posCost]
    | succ q => simp [IsQueryBound, toFreeM, AdvSig.posCost, ih]

/-- The two-kind query bound is the roll bound with budget `ℕ × ℕ` that decrements the
component of each query's kind. -/
theorem isQueryBound₂_iff_isRollBound {D₁ D₂ : Type} (A : OracleAdv (D₁ ⊕ D₂) R α)
    (h q : ℕ) :
    OracleForking.IsQueryBound₂ A h q ↔
      (toFreeM A).IsRollBound (h, q) AdvSig.canRoll₂ AdvSig.cost₂ := by
  induction A generalizing h q with
  | ret a => exact Iff.rfl
  | rand p k ih =>
    simp only [OracleForking.IsQueryBound₂, toFreeM, FreeM.isRollBound_liftBind_iff,
      AdvSig.canRoll₂, AdvSig.cost₂, true_and, ih]
  | query d k ih =>
    rcases d with d | d
    · cases h with
      | zero => simp [OracleForking.IsQueryBound₂, toFreeM, AdvSig.canRoll₂]
      | succ h => simp [OracleForking.IsQueryBound₂, toFreeM, AdvSig.canRoll₂, AdvSig.cost₂, ih]
    · cases q with
      | zero => simp [OracleForking.IsQueryBound₂, toFreeM, AdvSig.canRoll₂]
      | succ q => simp [OracleForking.IsQueryBound₂, toFreeM, AdvSig.canRoll₂, AdvSig.cost₂, ih]

/-! ## Costed adversaries -/

namespace Timed

/-- The tick polynomial: a position `n : ℕ` charges `n` units and has one direction. -/
abbrev TickSig : PFunctor.{0, 0} := ⟨ℕ, fun _ => PUnit⟩

/-- The polynomial functor of costed oracle adversaries: `AdvSig D R` with tick positions. -/
abbrev AdvSigT (D R : Type) : PFunctor.{1, 0} := AdvSig D R + TickSig

/-- The charge of a position of `AdvSigT D R`: one unit at a node of `AdvSig D R`, `n` at
`tick n`. -/
def tickCost : (AdvSigT D R).A → ℕ
  | .inl _ => 1
  | .inr n => n

/-- The costed adversary `A` as a tree of `AdvSigT D R`: each direction `x` of a node with
step cost `c` is followed by the tick `c x`. -/
def toFreeMT : Timed D R α → FreeM (AdvSigT D R) α
  | ret a => .pure a
  | rand p c k => .liftBind (P := AdvSigT D R) (.inl (.rand _ p)) fun b =>
      .liftBind (P := AdvSigT D R) (.inr (c b)) fun _ => toFreeMT (k b)
  | query d c k => .liftBind (P := AdvSigT D R) (.inl (.query d)) fun r =>
      .liftBind (P := AdvSigT D R) (.inr (c r)) fun _ => toFreeMT (k r)

/-- The time bound of a costed adversary is the subtractive roll bound with charge
`tickCost` on its tick tree. -/
theorem timeBound_iff_isRollBound (A : Timed D R α) (n : ℕ) :
    A.TimeBound n ↔
      (toFreeMT A).IsRollBound n (fun a b => tickCost a ≤ b) (fun a b => b - tickCost a) := by
  induction A generalizing n with
  | ret a => exact Iff.rfl
  | rand p c k ih =>
    simp only [TimeBound, toFreeMT, FreeM.isRollBound_liftBind_iff, tickCost, ih]
    simp_all
  | query d c k ih =>
    simp only [TimeBound, toFreeMT, FreeM.isRollBound_liftBind_iff, tickCost, ih]
    simp_all

/-- The time bound of a costed adversary is the bound `n` on the worst-case charge fold of its
tick tree. -/
theorem timeBound_iff_wpFold_charge (A : Timed D R α) (n : ℕ) :
    A.TimeBound n ↔
      FreeM.wpFold (OpSpec.charge fun a => ((tickCost a : ℕ) : ℕ∞)) (toFreeMT A)
        (fun _ => 0) ≤ n := by
  rw [timeBound_iff_isRollBound, FreeM.isRollBound_iff_wpFold_charge]

/-- The charge fold of the tick tree with every answer allowed: `TimeBound` quantifies over
every sample and every oracle answer. -/
theorem timeBound_iff_wpFold_chargeUnder (A : Timed D R α) (n : ℕ) :
    A.TimeBound n ↔
      FreeM.wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) fun _ _ => True)
        (toFreeMT A) (fun _ => 0) ≤ n := by
  rw [OpSpec.chargeUnder_true, timeBound_iff_wpFold_charge]

/-! ## Step-prefixed adversaries, sequencing and leaves -/

/-- The step-prefixed costed adversary `(c, A)` as a tree of `AdvSigT D R`: the tick `c`
followed by the tick tree of `A`. -/
def stepToFreeMT (x : ℕ × Timed D R α) : FreeM (AdvSigT D R) α :=
  .liftBind (P := AdvSigT D R) (.inr x.1) fun _ => toFreeMT x.2

/-- The charge fold of a step-prefixed tree, with every tick answer allowed, is its step cost
plus the charge fold of its tree. -/
theorem wpFold_chargeUnder_stepToFreeMT
    (allows : (a : (AdvSigT D R).A) → (AdvSigT D R).B a → Prop)
    (hA : ∀ n, allows (.inr n) PUnit.unit) (x : ℕ × Timed D R α) (post : α → ℕ∞) :
    FreeM.wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows)
        (stepToFreeMT x) post =
      x.1 + FreeM.wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows)
        (toFreeMT x.2) post :=
  FreeM.wpFold_chargeUnder_liftBind_const _ allows _ (hA x.1) _ post

/-- `StepTimeBound x n` is the bound `n` on the charge fold of the step-prefixed tick tree of
`x`, with every answer allowed. -/
theorem stepTimeBound_iff_wpFold_chargeUnder (x : ℕ × Timed D R α) (n : ℕ) :
    StepTimeBound x n ↔
      FreeM.wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) fun _ _ => True)
        (stepToFreeMT x) (fun _ => 0) ≤ n := by
  rw [StepTimeBound, stepToFreeMT, FreeM.wpFold_chargeUnder_liftBind_le_iff,
    timeBound_iff_wpFold_chargeUnder]
  exact and_congr_right fun _ => ⟨fun h _ _ => h, fun h => h PUnit.unit trivial⟩

/-- The bind clause of the tick tree: the charge fold of a costed bind is the charge fold of the
FreeM bind of the tick tree with the step-prefixed tick trees of the continuation, for every
`allows` admitting the tick answers. The costed bind merges the tick `c b` of an edge with the
step cost of the continuation, so this is an equation of folds, not of trees. -/
theorem wpFold_stepToFreeMT_bind {β : Type}
    (allows : (a : (AdvSigT D R).A) → (AdvSigT D R).B a → Prop)
    (hA : ∀ n, allows (.inr n) PUnit.unit) (A : Timed D R α) (f : α → ℕ × Timed D R β)
    (post : β → ℕ∞) :
    FreeM.wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows)
        (stepToFreeMT (A.bind f)) post =
      FreeM.wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows)
        ((toFreeMT A).bind (stepToFreeMT ∘ f)) post := by
  have hstep : ∀ y : ℕ × Timed D R β,
      FreeM.wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows)
        (stepToFreeMT y) post =
      y.1 + FreeM.wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows)
        (toFreeMT y.2) post :=
    fun y => wpFold_chargeUnder_stepToFreeMT allows hA y post
  have htick : ∀ {γ : Type} (n : ℕ) (y : FreeM (AdvSigT D R) γ) (q : γ → ℕ∞),
      FreeM.wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows)
        (FreeM.liftBind (P := AdvSigT D R) (.inr n) fun _ => y) q =
      n + FreeM.wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows) y q :=
    fun n y q => FreeM.wpFold_chargeUnder_liftBind_const _ allows (.inr n) (hA n) y q
  rw [FreeM.wpFold_bind']
  induction A with
  | ret a => rfl
  | rand p c k ih =>
    rw [hstep]
    simp only [bind, toFreeMT, FreeM.wpFold_liftBind, OpSpec.chargeUnder_apply, htick,
      Nat.cast_zero, zero_add]
    refine congrArg _ (iSup_congr fun b => iSup_congr fun _ => ?_)
    rw [← ih b, hstep, Nat.cast_add, add_assoc]
  | query d c k ih =>
    rw [hstep]
    simp only [bind, toFreeMT, FreeM.wpFold_liftBind, OpSpec.chargeUnder_apply, htick,
      Nat.cast_zero, zero_add]
    refine congrArg _ (iSup_congr fun b => iSup_congr fun _ => ?_)
    rw [← ih b, hstep, Nat.cast_add, add_assoc]

/-- `AllRet Q A` is the demonic fold of `Q` over the tick tree of `A` with every answer
allowed: `AllRet` quantifies over every sample and every oracle answer. -/
theorem allRet_iff_wpFold_demonicUnder (Q : α → Prop) (A : Timed D R α) :
    AllRet Q A ↔ FreeM.wpFold (OpSpec.demonicUnder fun _ _ => True) (toFreeMT A) Q := by
  induction A with
  | ret a => exact Iff.rfl
  | rand p c k ih =>
    exact ⟨fun h b _ _ _ => (ih b).1 (h b), fun h b => (ih b).2 (h b trivial PUnit.unit trivial)⟩
  | query d c k ih =>
    exact ⟨fun h b _ _ _ => (ih b).1 (h b), fun h b => (ih b).2 (h b trivial PUnit.unit trivial)⟩

end Timed

end OracleAdv

end CatCrypt.Crypto
