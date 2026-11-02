/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.OracleProfile
import CatCryptCore.Tactics.QueryFold

/-!
# Tests of the fold of `query_bound`

Bounds of trees, of known adversaries, of simulations, of renamings and of branches; a defined
charge and a defined branch condition listed as laws; a bound with the attribute `@[query_fold]`,
which `query_bound only` leaves out; a two-kind hypothesis; and a projection of a defined structure.
-/

set_option autoImplicit false

namespace CatCrypt.Tactics.QueryFoldTest

open CatCrypt.Crypto OracleAdv

variable {D D' R R' α β : Type}

example (c : D → ℕ) (d : D) (h : c d ≤ 1) :
    (OracleAdv.query d fun r => OracleAdv.ret r : OracleAdv D R R).IsQueryBoundBy c 1 := by
  query_bound

example (d : D) :
    (OracleAdv.bind (OracleAdv.query d fun r => OracleAdv.ret r)
      (fun _ => OracleAdv.query d fun r => OracleAdv.ret r) : OracleAdv D R R).IsQueryBound 2 := by
  query_bound

example (A : OracleAdv D R α) (f : α → OracleAdv D R β) (hA : A.IsQueryBound 2)
    (hf : ∀ a, (f a).IsQueryBound 3) : (A.bind f).IsQueryBound 5 := by
  query_bound

example (S : Type) (impl : S → D → OracleAdv D' R' (R × S)) (c : D → ℕ) (A : OracleAdv D R α)
    (n : ℕ) (hA : A.IsQueryBoundBy c n) (h : ∀ s d, (impl s d).IsQueryBound (c d)) (s : S) :
    (simulate impl A s).IsQueryBound n := by
  query_bound

example (S : Type) (impl : S → D → OracleAdv D' R' (R × S)) (A : OracleAdv D R α)
    (q : ℕ) (hA : A.IsQueryBound q) (h : ∀ s d, (impl s d).IsQueryBound 2) (s : S) :
    (simulate impl A s).IsQueryBound (q * 2) := by
  query_bound

example (g : D → D') (c : D' → ℕ) (hc : ∀ d, c (g d) ≤ 1) (A : OracleAdv D R α) (q : ℕ)
    (hA : A.IsQueryBound q) : (mapQuery g A).IsQueryBoundBy c q := by
  query_bound

example (d : D) (b : Bool) (A : OracleAdv D R α) (hA : A.IsQueryBound 1) :
    (if b then A else OracleAdv.query d fun _ => A).IsQueryBound 2 := by
  query_bound

/-- A defined charge with a case split. -/
def boolCharge : Bool → ℕ
  | true => 1
  | false => 0

example (b : Bool) :
    (OracleAdv.query b fun r => OracleAdv.ret r : OracleAdv Bool R R).IsQueryBoundBy
      boolCharge 1 := by
  query_bound [boolCharge]

/-- A defined branch condition. -/
def SmallQ (n : ℕ) : Prop := n ≤ 1

example (n : ℕ) [Decidable (SmallQ n)] (a : α) (A : ℕ → OracleAdv D R α)
    (hA : ∀ m, (A m).IsQueryBound m) :
    (if SmallQ n then A n else OracleAdv.ret a).IsQueryBound 1 := by
  query_bound [SmallQ]

/-- A total count with a pointwise bound of the charge gives a product budget. -/
@[query_fold] theorem isQueryBoundBy_mul_of_le {c : D → ℕ} {N q : ℕ} {A : OracleAdv D R α}
    (hc : ∀ d, c d ≤ N) (hA : A.IsQueryBound q) : A.IsQueryBoundBy c (q * N) := by
  have := (hA.isQueryBoundBy_one.mul_left N).of_cost_le (cost' := c) (by simpa using hc)
  simpa [Nat.mul_comm] using this

example {c : D → ℕ} {N q : ℕ} {A : OracleAdv D R α} (hc : ∀ d, c d ≤ N)
    (hA : A.IsQueryBound q) : A.IsQueryBoundBy c (q * N + 1) := by
  query_bound

/-- `only` leaves out the theorems with the attribute, and a listed name adds one. -/
example {c : D → ℕ} {N q : ℕ} {A : OracleAdv D R α} (hc : ∀ d, c d ≤ N)
    (hA : A.IsQueryBound q) : A.IsQueryBoundBy c (q * N + 1) := by
  fail_if_success query_bound only
  query_bound only [isQueryBoundBy_mul_of_le]

/-- A two-kind hypothesis gives the count of each summand and their sum. -/
example {D₁ D₂ : Type} {A : OracleAdv (D₁ ⊕ D₂) R α} {a b : ℕ}
    (hA : OracleForking.IsQueryBound₂ A a b) :
    A.IsQueryBoundBy chargeInr b ∧ A.IsQueryBound (a + b) := by
  exact ⟨by query_bound, by query_bound⟩

/-- An adversary with a field bound, and a defined instance of it. -/
structure CountedRun (D R α : Type) (q : ℕ) where
  /-- The run. -/
  run : ℕ → OracleAdv D R α
  /-- The bound of the run. -/
  bound : ∀ n, (run n).IsQueryBound q

/-- The run of `countedRet` asks no query. -/
def countedRet (a : α) : CountedRun D R α 0 where
  run _ := OracleAdv.ret a
  bound _ := trivial

example {q : ℕ} (B : CountedRun D R α q) (n : ℕ) : (B.run n).IsQueryBound (q + 1) := by
  query_bound

example (a : α) (n : ℕ) :
    ((countedRet (D := D) (R := R) a).run n).IsQueryBoundBy (fun _ => 1) 0 := by
  query_bound

end CatCrypt.Tactics.QueryFoldTest
