/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signatures.OracleProgTimed
public import CatCryptCore.Core.SPTreeTimedFree
public import CatCryptCore.ForMathlib.PFunctorChargeUnder

/-!
# Costed oracle programs as free monads with a tick operation

`OracleProg.Timed I O α` translates to the free monad `PFunctor.FreeM (OracleProg.SigT I O) α`
of the polynomial functor `SigT I O = Sig I O + SPTree.TickSig`. The positions of `Sig I O` are
the queries `query i` (directions `O`) and the computation nodes `lift β t` (directions `β`);
the tick positions `tick n` of `SPTree.TickSig` charge `n` units and have one direction. The
translation `OracleProg.Timed.toFreeMT` follows each direction `x` of a node with step cost `c`
by the tick `c x`, so that every step cost is charged on the edge it labels.

## Main definitions

* `OracleProg.Pos`, `OracleProg.Sig`, `OracleProg.SigT` — the positions, the signature and the
  ticked signature
* `OracleProg.tickCost` — one unit at a query, `SPTree.Timed.time t` at `lift β t`, `n` at
  `tick n`
* `OracleProg.Timed.toFreeMT` — the tick tree of a costed program
* `OracleProg.Timed.stepToFreeMT` — the tick tree of a step-prefixed costed program

## Main results

* `OracleProg.Timed.timeBound_iff_isRollBound` — `TimeBound` is the subtractive roll bound with
  charge `tickCost` on the tick tree
* `OracleProg.Timed.timeBound_iff_wpFold_charge` — `TimeBound` is the bound on the worst-case
  charge fold of the tick tree
* `OracleProg.Timed.stepTimeBound_iff_isRollBound`,
  `OracleProg.Timed.stepTimeBound_iff_wpFold_charge` — the same for `StepTimeBound`
* `OracleProg.Timed.stepTimeBound_iff_wpFold_chargeUnder` — the same over the charge reading
  with every answer allowed
* `OracleProg.Timed.wpFold_stepToFreeMT_bind` — the charge fold of a costed bind is the charge
  fold of the bind of the tick trees
* `OracleProg.Timed.allRet_iff_wpFold_demonicUnder` — `AllRet` is the demonic fold of the tick
  tree
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Core PFunctor

namespace CatCrypt.Crypto

namespace OracleProg

/-- The positions of `OracleProg.Sig I O`: a query on `i`, or the costed computation tree `t`. -/
inductive Pos (I : Type) : Type 1 where
  /-- Query the oracle on `i`. -/
  | query (i : I)
  /-- Run the costed computation tree `t`. -/
  | lift (β : Type) (t : SPTree.Timed β)

/-- The directions at a position of `OracleProg.Sig I O`: an answer in `O` or a result in `β`. -/
abbrev Pos.dir (O : Type) {I : Type} : Pos I → Type
  | .query _ => O
  | .lift β _ => β

/-- The polynomial functor of costed oracle programs without step costs: positions `Pos I`,
directions `Pos.dir O`. -/
abbrev Sig (I O : Type) : PFunctor.{1, 0} := ⟨Pos I, Pos.dir O⟩

/-- The polynomial functor of costed oracle programs: `Sig I O` with tick positions. -/
abbrev SigT (I O : Type) : PFunctor.{1, 0} := Sig I O + SPTree.TickSig

variable {I O α : Type}

/-- The charge of a position of `SigT I O`: one unit at a query, the time of `t` at `lift β t`,
and `n` at `tick n`. -/
noncomputable def tickCost : (SigT I O).A → ℕ
  | .inl (.query _) => 1
  | .inl (.lift _ t) => t.time
  | .inr n => n

namespace Timed

/-- The costed program `p` as a tree of `SigT I O`: each direction `x` of a node with step cost
`c` is followed by the tick `c x`. -/
def toFreeMT : Timed I O α → FreeM (SigT I O) α
  | pure a => .pure a
  | query i c k => .liftBind (P := SigT I O) (.inl (.query i)) fun o =>
      .liftBind (P := SigT I O) (.inr (c o)) fun _ => toFreeMT (k o)
  | lift β t c k => .liftBind (P := SigT I O) (.inl (.lift β t)) fun b =>
      .liftBind (P := SigT I O) (.inr (c b)) fun _ => toFreeMT (k b)

/-- The step-prefixed program `(c, p)` as a tree of `SigT I O`: the tick `c` followed by the
tick tree of `p`. -/
def stepToFreeMT (x : ℕ × Timed I O α) : FreeM (SigT I O) α :=
  .liftBind (P := SigT I O) (.inr x.1) fun _ => toFreeMT x.2

/-- The time bound of a costed program is the subtractive roll bound with charge `tickCost` on
its tick tree. -/
theorem timeBound_iff_isRollBound (p : Timed I O α) (n : ℕ) :
    p.TimeBound n ↔
      (toFreeMT p).IsRollBound n (fun a b => tickCost a ≤ b) (fun a b => b - tickCost a) := by
  induction p generalizing n with
  | pure a => exact Iff.rfl
  | query i c k ih =>
    simp only [TimeBound, toFreeMT, FreeM.isRollBound_liftBind_iff, tickCost, ih]
    simp_all
  | lift β t c k ih =>
    simp only [TimeBound, toFreeMT, FreeM.isRollBound_liftBind_iff, tickCost, ih]
    simp_all

/-- The time bound of a costed program is the bound `n` on the worst-case charge fold of its
tick tree. -/
theorem timeBound_iff_wpFold_charge (p : Timed I O α) (n : ℕ) :
    p.TimeBound n ↔
      FreeM.wpFold (OpSpec.charge fun a => ((tickCost a : ℕ) : ℕ∞)) (toFreeMT p)
        (fun _ => 0) ≤ n := by
  rw [timeBound_iff_isRollBound, FreeM.isRollBound_iff_wpFold_charge]

/-- The time bound of a step-prefixed program is the subtractive roll bound with charge
`tickCost` on its tick tree. -/
theorem stepTimeBound_iff_isRollBound (x : ℕ × Timed I O α) (n : ℕ) :
    StepTimeBound x n ↔
      (stepToFreeMT x).IsRollBound n (fun a b => tickCost a ≤ b)
        (fun a b => b - tickCost a) := by
  simp only [StepTimeBound, stepToFreeMT, FreeM.isRollBound_liftBind_iff,
    timeBound_iff_isRollBound]
  exact and_congr Iff.rfl ⟨fun h _ => h, fun h => h PUnit.unit⟩

/-- The time bound of a step-prefixed program is the bound `n` on the worst-case charge fold of
its tick tree. -/
theorem stepTimeBound_iff_wpFold_charge (x : ℕ × Timed I O α) (n : ℕ) :
    StepTimeBound x n ↔
      FreeM.wpFold (OpSpec.charge fun a => ((tickCost a : ℕ) : ℕ∞)) (stepToFreeMT x)
        (fun _ => 0) ≤ n := by
  rw [stepTimeBound_iff_isRollBound, FreeM.isRollBound_iff_wpFold_charge]

/-- The time bound of a step-prefixed program is the bound `n` on the charge fold of its tick
tree with every answer allowed: `TimeBound` quantifies over every answer and every result. -/
theorem stepTimeBound_iff_wpFold_chargeUnder (x : ℕ × Timed I O α) (n : ℕ) :
    StepTimeBound x n ↔
      FreeM.wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) fun _ _ => True)
        (stepToFreeMT x) (fun _ => 0) ≤ n := by
  rw [OpSpec.chargeUnder_true, stepTimeBound_iff_wpFold_charge]

/-- The charge fold of a step-prefixed program, with every tick answer allowed, is its step
cost plus the charge fold of its program. -/
theorem wpFold_chargeUnder_stepToFreeMT
    (allows : (a : (SigT I O).A) → (SigT I O).B a → Prop)
    (hA : ∀ n, allows (.inr n) PUnit.unit) (x : ℕ × Timed I O α) (post : α → ℕ∞) :
    FreeM.wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows)
        (stepToFreeMT x) post =
      x.1 + FreeM.wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows)
          (toFreeMT x.2) post :=
  FreeM.wpFold_chargeUnder_liftBind_const _ allows _ (hA x.1) _ post

/-- The bind clause of the tick tree: the charge fold of a costed bind is the charge fold of the
FreeM bind of the tick tree with the step-prefixed tick trees of the continuation, for every
`allows` admitting the tick answers. The costed bind merges the tick `c b` of an edge with the
step cost of the continuation, so this is an equation of folds, not of trees. -/
theorem wpFold_stepToFreeMT_bind {β : Type}
    (allows : (a : (SigT I O).A) → (SigT I O).B a → Prop)
    (hA : ∀ n, allows (.inr n) PUnit.unit) (p : Timed I O α) (f : α → ℕ × Timed I O β)
    (post : β → ℕ∞) :
    FreeM.wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows)
        (stepToFreeMT (p.bind f)) post =
      FreeM.wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows)
          ((toFreeMT p).bind (stepToFreeMT ∘ f)) post := by
  have hstep : ∀ y : ℕ × Timed I O β,
      FreeM.wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows)
          (stepToFreeMT y) post =
        y.1 + FreeM.wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows)
            (toFreeMT y.2) post :=
    fun y => wpFold_chargeUnder_stepToFreeMT allows hA y post
  have htick : ∀ {γ : Type} (n : ℕ) (y : FreeM (SigT I O) γ) (q : γ → ℕ∞),
      FreeM.wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows)
        (FreeM.liftBind (P := SigT I O) (.inr n) fun _ => y) q =
      n + FreeM.wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows) y q :=
    fun n y q => FreeM.wpFold_chargeUnder_liftBind_const _ allows (.inr n) (hA n) y q
  rw [FreeM.wpFold_bind']
  induction p with
  | pure a => rfl
  | query i c k ih =>
    rw [hstep]
    simp only [bind, toFreeMT, FreeM.wpFold_liftBind, OpSpec.chargeUnder_apply, htick,
      Nat.cast_zero, zero_add]
    refine congrArg _ (iSup_congr fun b => iSup_congr fun _ => ?_)
    rw [← ih b, hstep, Nat.cast_add, add_assoc]
  | lift γ t c k ih =>
    rw [hstep]
    simp only [bind, toFreeMT, FreeM.wpFold_liftBind, OpSpec.chargeUnder_apply, htick,
      Nat.cast_zero, zero_add]
    refine congrArg _ (iSup_congr fun b => iSup_congr fun _ => ?_)
    rw [← ih b, hstep, Nat.cast_add, add_assoc]

/-- `AllRet Q p` is the demonic fold of `Q` over the tick tree of `p` with every answer
allowed: `AllRet` quantifies over every answer and every result. -/
theorem allRet_iff_wpFold_demonicUnder (Q : α → Prop) (p : Timed I O α) :
    AllRet Q p ↔ FreeM.wpFold (OpSpec.demonicUnder fun _ _ => True) (toFreeMT p) Q := by
  induction p with
  | pure a => exact Iff.rfl
  | query i c k ih =>
    exact ⟨fun h b _ _ _ => (ih b).1 (h b), fun h b => (ih b).2 (h b trivial PUnit.unit trivial)⟩
  | lift γ t c k ih =>
    exact ⟨fun h b _ _ _ => (ih b).1 (h b), fun h b => (ih b).2 (h b trivial PUnit.unit trivial)⟩

end Timed

end OracleProg

end CatCrypt.Crypto
