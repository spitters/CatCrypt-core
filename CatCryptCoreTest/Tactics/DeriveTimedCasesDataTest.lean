/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimed

/-!
# Tests for tree-valued case analyses by a recursor on data (rule (o) of `derive_timed`)

* `relabel`: a recursion over an oracle-tree binder whose match on the query has a nested
  constructor pattern (`.query (.inl x) k`), which the equation compiler compiles to the case
  analysis `Sum.casesOn` of the query inside the alternative of the tree node. Its costed form is
  the same case analysis over the costed trees of the alternatives, behind one unit plus the cost
  of the query (pinned by `relabel_timed_inl`, `relabel_timed_inr`).
* `pick`: a tree written with the case analysis `Cmd.casesOn` of a command; the same case analysis in the
  costed tree, at one unit plus the cost of the argument (`pick_timed`).

## Main results

* `relabel.erase_timed`, `pick.erase_timed` — the erasure theorems, proved by the command
-/

public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimedCasesDataTest

open CatCrypt.Crypto

/-- A relabelling of the queries of an adversary: a query `inl x` is forwarded as `x + 1`, a
query `inr b` is answered by `b` without a query. -/
def relabel : OracleAdv (ℕ ⊕ Bool) Bool Bool → OracleAdv ℕ Bool Bool
  | .ret b => .ret b
  | .rand p k => .rand p fun x => relabel (k x)
  | .query (.inl x) k => .query (x + 1) fun r => relabel (k r)
  | .query (.inr b) k => relabel (k b)

derive_timed relabel

/-- At a query `inl x`: the unit of the case analysis of the tree and the unit of the case
analysis of the query in front, the forwarded query node, and each answer charged the step cost
of the source node and the costed recursive call. -/
theorem relabel_timed_inl (x : ℕ) (c : Bool → ℕ)
    (k : Bool → OracleAdv.Timed (ℕ ⊕ Bool) Bool Bool) :
    relabel.timed (.query (.inl x) c k) = OracleAdv.Timed.delay 2
      (1, .query (x + 1) (fun r => 2 + c r + (relabel.timed (k r)).1)
        fun r => (relabel.timed (k r)).2) := by
  rw [relabel.timed]

/-- At a query `inr b`: the two units, the step cost of the source node, then the costed
recursive call at the answer `b`. -/
theorem relabel_timed_inr (b : Bool) (c : Bool → ℕ)
    (k : Bool → OracleAdv.Timed (ℕ ⊕ Bool) Bool Bool) :
    relabel.timed (.query (.inr b) c k) =
      OracleAdv.Timed.delay 2 (OracleAdv.Timed.delay (2 + c b) (relabel.timed (k b))) := by
  rw [relabel.timed]

/-- Commands. -/
inductive Cmd where
  | stop
  | go (n : ℕ)
  | flip (b : Bool)

/-- A tree that branches on a command by its case analysis. -/
def pick (m : Cmd) : OracleAdv ℕ Bool Bool :=
  Cmd.casesOn (motive := fun _ => OracleAdv ℕ Bool Bool) m (.ret false)
    (fun n => .query (n + 1) .ret) fun b => .ret b

derive_timed pick

/-- The case analysis of the command in the costed tree, behind one unit. -/
theorem pick_timed (m : Cmd) : pick.timed m = OracleAdv.Timed.delay 1
    (Cmd.casesOn (motive := fun _ => ℕ × OracleAdv.Timed ℕ Bool Bool) m (0, .ret false)
      (fun n => (1, .query (n + 1) (fun _ => 0) .ret)) fun b => (0, .ret b)) := rfl

end CatCrypt.Tactics.DeriveTimedCasesDataTest
