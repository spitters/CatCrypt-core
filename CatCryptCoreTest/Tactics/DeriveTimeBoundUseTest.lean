/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signatures.OracleProgUseBound
public import CatCryptCore.Tactics.DeriveTimeBound

/-!
# Tests of the vector charge of oracle programs in the fold rule

Fresh costed oracle programs, none taken from a protocol: a program with two queries, a binder
program whose queries are answered by a handler program (`bindQueries`), and a binder program
whose queries are answered by a handler with records (`collectLog`), followed by a continuation
whose cost is the length of the collected records. `derive_time_bound +queries` states the
query count beside the time, from one use bound on each binder program.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimeBoundUseTest

open CatCrypt.Core CatCrypt.Crypto CatCrypt.Container OracleProg

/-- The name of `twoQ.timed`. -/
def twoQ : Unit := ()

/-- Two queries, on `x` and on the answer plus one, at step costs `1` and `2`, behind one unit:
time `1 + 1 + 1 + 1 + 2 = 6`, two queries. -/
def twoQ.timed (x : ℕ) : ℕ × Timed ℕ ℕ ℕ :=
  (1, .query x (fun _ => 1) fun o => .query (o + 1) (fun _ => 2) fun o' => .pure (o + o'))

derive_time_bound +queries twoQ

example (x : ℕ) :
    Timed.StepTimeBound (twoQ.timed x) 6 ∧ QueryCostLe (fun _ => 1) (twoQ.timed x).2.erase 2 :=
  twoQ.timeBound_timed x

/-- A handler program: one unit, then one query on `0`, answering whether the answer is zero. -/
def hdl (i : Bool) : ℕ × Timed ℕ ℕ Bool :=
  (1, .query (if i then 0 else 1) (fun _ => 0) fun o => .pure (decide (o = 0)))

/-- The name of `bq.timed`. -/
def bq : Unit := ()

/-- The binder program `A x` with its queries answered by `hdl`, behind one unit and followed by
a step of one unit. -/
def bq.timed (A : ℕ → Timed Bool Bool ℕ) (x : ℕ) : ℕ × Timed ℕ ℕ ℕ :=
  Timed.delay (1 + (Timed.bindQueries hdl (A x)).1)
    ((Timed.bindQueries hdl (A x)).2.bind fun o => (1, .pure o))

derive_time_bound bq

/-- The query count of `bq` is the query count of `A` times the one query of the handler. -/
example (A : ℕ → Timed Bool Bool ℕ) (x : ℕ) {q T : ℕ}
    (hA : ∀ x, UseBound (useCharge fun _ => 1) (fun _ _ => True) (Timed.toFreeMT (A x))
      (budget q T)) :
    Timed.StepTimeBound (bq.timed A x) (T + q * 2 + 2) ∧
      QueryCostLe (fun _ => 1) (bq.timed A x).2.erase q := by
  obtain ⟨h1, h2⟩ := bq.timeBound_timed A x hA
  exact ⟨h1.mono (by omega), by simpa using h2⟩

/-- A handler program with records: one query on `i`, at step cost `1`, and the record
`[i, i]`. -/
def hrec (i : ℕ) : ℕ × Timed ℕ ℕ (ℕ × List ℕ) :=
  (0, .query i (fun _ => 1) fun o => .pure (o, [i, i]))

/-- The name of `cl.timed`. -/
def cl : Unit := ()

/-- The binder program `A x` with its queries answered by `hrec`, followed by a step whose cost
is the length of the collected records. -/
def cl.timed (A : ℕ → Timed ℕ ℕ ℕ) (x : ℕ) : ℕ × Timed ℕ ℕ ℕ :=
  Timed.delay (1 + (Timed.collectLog hrec (A x)).1)
    ((Timed.collectLog hrec (A x)).2.bind fun al => (al.2.length, .pure al.1))

derive_time_bound +queries cl

/-- The records have length at most `2 q` (the leaf-length rule on `hrec` and the invariant of
`collectLog`), so the continuation costs at most `2 q`. -/
example (A : ℕ → Timed ℕ ℕ ℕ) (x : ℕ) {q T : ℕ}
    (hA : ∀ x, UseBound (useCharge fun _ => 1) (fun _ _ => True) (Timed.toFreeMT (A x))
      (budget q T)) :
    Timed.StepTimeBound (cl.timed A x) (T + q * 7 + 2 * q + 1) ∧
      QueryCostLe (fun _ => 1) (cl.timed A x).2.erase q := by
  obtain ⟨h1, h2⟩ := cl.timeBound_timed A x hA
  exact ⟨h1.mono (by omega), by simpa using h2⟩

end CatCrypt.Tactics.DeriveTimeBoundUseTest
