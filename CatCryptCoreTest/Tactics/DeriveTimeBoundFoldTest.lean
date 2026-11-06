/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Crypto.Signatures.OracleProgTimedFree

/-!
# Tests of the fold rule of `derive_time_bound`

Fresh programs of the kinds `SPTree.Timed`, `OracleAdv.Timed` and `OracleProg.Timed` and two
programs written directly in a free monad, bounded by the fold rule: by `derive_time_bound`
for a costed oracle adversary and a costed oracle program, by the standalone tactic `time_fold`
on the time-bound goals of the registered kinds and on charge-fold goals.

* `spRed`: sample a bit, on heads run a binder tree `A` at it and bind into a continuation
  charging a cost companion; `spSupp`: a `sampleDist` node whose continuation is an
  `if h : b ∈ μ.support` with a costly else-branch, bounded by the cheap branch;
* `oaRed.timed`: a query, then a bind into a binder adversary;
* `opRed.timed`: the lift of a fresh costed `SPTree`, a query, a bind into a binder program
  and an `if`;
* `coinWork`, `thenWork`: programs written in `FreeM` with symbolic bounds;
* negative: a bound one below the computed one is refused, and a charge that depends on a
  sampled value through an unregistered function is refused with the charge named.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimeBoundFoldTest

open CatCrypt.Core CatCrypt.Crypto CatCrypt.Prob PFunctor PFunctor.FreeM

/-! ## Programs written in a free monad -/

/-- The operations of a toy signature: a coin flip and a step of work of a given size. -/
inductive Op where
  /-- Flip a coin. -/
  | flip
  /-- Work for `n` units. -/
  | work (n : ℕ)

/-- The answers of an operation: a bit for a flip, nothing for work. -/
abbrev Op.dir : Op → Type
  | .flip => Bool
  | .work _ => PUnit

/-- The toy signature. -/
abbrev Sig : PFunctor.{0, 0} := ⟨Op, Op.dir⟩

/-- The charge of an operation: one unit for a flip, `n` for work of size `n`. -/
def opCharge : Op → ℕ
  | .flip => 1
  | .work n => n

/-- Flip a coin, and on heads work for `n` units. -/
def coinWork (n : ℕ) : FreeM Sig Bool :=
  .liftBind (P := Sig) .flip fun b =>
    if b then .liftBind (P := Sig) (.work n) fun _ => .pure true else .pure false

example (n : ℕ) :
    wpFold (OpSpec.charge fun a => (opCharge a : ℕ∞)) (coinWork n) (fun _ => 0) ≤
      ((n + 1 : ℕ) : ℕ∞) := by
  time_fold

/-- Run `coinWork n`, then a binder program `q` on its result, then `m` units of work. -/
def thenWork (n m : ℕ) (q : Bool → FreeM Sig ℕ) : FreeM Sig ℕ :=
  (coinWork n).bind fun b => (q b).bind fun k => .liftBind (P := Sig) (.work m) fun _ => .pure k

example (n m T : ℕ) (q : Bool → FreeM Sig ℕ)
    (hq : ∀ b, wpFold (OpSpec.charge fun a => (opCharge a : ℕ∞)) (q b) (fun _ => 0) ≤ T) :
    wpFold (OpSpec.charge fun a => (opCharge a : ℕ∞)) (thenWork n m q) (fun _ => 0) ≤
      ((n + m + T + 1 : ℕ) : ℕ∞) := by
  time_fold

/-! ## Costed `SPTree`s -/

/-- Sample a bit; on heads run the binder tree `A` at it and charge `gCost` at its result. -/
noncomputable def spRed (A : Bool → SPTree.Timed ℕ) (gCost : ℕ → ℕ) : SPTree.Timed ℕ :=
  .sample Bool inferInstance ⟨true⟩
    (fun b => (if b then (A b).bind fun n => (gCost n, .ret n) else (0, .ret 0)).1)
    fun b => (if b then (A b).bind fun n => (gCost n, .ret n) else (0, .ret 0)).2

example (A : Bool → SPTree.Timed ℕ) (gCost : ℕ → ℕ) {T t : ℕ} (hA : ∀ b, (A b).TimeBound T)
    (hg : ∀ n, gCost n ≤ t) : (spRed A gCost).TimeBound (T + t + 1) := by
  time_fold

open Classical in
/-- Sample from `μ`; inside the support return, outside it run a costly sample. -/
noncomputable def spSupp (μ : SDistr Bool) (n : ℕ) : SPTree.Timed Bool :=
  .sampleDist Bool μ (fun _ => 0) fun b =>
    if _h : b ∈ μ.support then .ret b else .sample Bool inferInstance ⟨true⟩ (fun _ => n) .ret

example (μ : SDistr Bool) (n : ℕ) : (spSupp μ n).TimeBound 1 := by
  time_fold

/-! ## Costed oracle adversaries -/

/-- The name of the costed oracle adversary `oaRed.timed`. -/
def oaRed : Unit := ()

/-- Query `x`, charging `aCost` at the answer, then run the binder adversary `A` and return the
conjunction of its bit with the answer. -/
def oaRed.timed (A : ℕ → OracleAdv.Timed ℕ Bool Bool) (aCost : Bool → ℕ) (x : ℕ) :
    ℕ × OracleAdv.Timed ℕ Bool Bool :=
  (2, .query x (fun r => aCost r + ((A x).bind fun b => (1, .ret (b && r))).1)
    fun r => ((A x).bind fun b => (1, .ret (b && r))).2)

derive_time_bound oaRed

example (A : ℕ → OracleAdv.Timed ℕ Bool Bool) (aCost : Bool → ℕ) (x : ℕ) {T t : ℕ}
    (hA : ∀ a, (A a).TimeBound T) (ha : ∀ r, aCost r ≤ t) :
    OracleAdv.Timed.StepTimeBound (oaRed.timed A aCost x) (T + t + 4) :=
  (oaRed.timeBound_timed A aCost x hA ha).mono (by omega)

/-! ## Costed oracle programs -/

/-- The name of the costed oracle program `opRed.timed`. -/
def opRed : Unit := ()

/-- Run a fresh costed sample of a bit, query `x`, and on a positive answer run the binder
program `A` at the bit, charging three units at its result. -/
noncomputable def opRed.timed (A : Bool → OracleProg.Timed ℕ Bool Bool) (x : ℕ) :
    ℕ × OracleProg.Timed ℕ Bool Bool :=
  (1, .lift Bool (.sample Bool inferInstance ⟨true⟩ (fun _ => 2) .ret) (fun _ => 1) fun b =>
    .query x (fun o => (if o then (A b).bind fun c => (3, .pure c) else (0, .pure false)).1)
      fun o => (if o then (A b).bind fun c => (3, .pure c) else (0, .pure false)).2)

derive_time_bound opRed

example (A : Bool → OracleProg.Timed ℕ Bool Bool) (x : ℕ) {T : ℕ}
    (hA : ∀ b, (A b).TimeBound T) :
    OracleProg.Timed.StepTimeBound (opRed.timed A x) (T + 9) :=
  (opRed.timeBound_timed A x hA).mono (by omega)

/-! ## Refusals -/

/-- A bound one below the computed bound is refused. -/
example : True := by
  fail_if_success
    have : ∀ n : ℕ, wpFold (OpSpec.charge fun a => (opCharge a : ℕ∞)) (coinWork n)
        (fun _ => 0) ≤ ((n : ℕ) : ℕ∞) := fun n => by time_fold
  trivial

/-- A charge outside the registered costs: the weight of a sampled bit through a function the
rule does not read. -/
def bitWeight : Bool → ℕ
  | true => 7
  | false => 0

/-- Sample a bit and charge its weight. -/
noncomputable def spWeighted : SPTree.Timed Bool :=
  .sample Bool inferInstance ⟨true⟩ bitWeight .ret

/--
error: no bound of the charge
  bitWeight b
-/
#guard_msgs (substring := true) in
example : spWeighted.TimeBound 8 := by
  time_fold

end CatCrypt.Tactics.DeriveTimeBoundFoldTest
