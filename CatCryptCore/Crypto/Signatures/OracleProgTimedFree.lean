/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signatures.OracleProgTimed
public import CatCryptCore.Core.SPTreeTimedFree

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

end Timed

end OracleProg

end CatCrypt.Crypto
