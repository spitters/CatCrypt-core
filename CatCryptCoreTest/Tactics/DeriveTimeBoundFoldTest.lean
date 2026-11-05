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
for a costed oracle adversary, by the standalone tactic `time_fold` on the time-bound goals of
the registered kinds and on charge-fold goals.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimeBoundFoldTest

open CatCrypt.Core PFunctor PFunctor.FreeM

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

end CatCrypt.Tactics.DeriveTimeBoundFoldTest
