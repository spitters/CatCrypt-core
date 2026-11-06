/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signatures.OracleProgUseBound
public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.StdCosts

/-!
# Tests of time bounds through length hypotheses

Fresh costed oracle programs, none taken from a protocol. A binder program has its queries
answered by a handler with records (`collectLog`), and the continuation reads the collected log
through lists computed from it: a search over a flat map of the log, a search whose test is a
membership test in a map of that flat map, and a filter of the log followed by its length. The
law of `collectLog` bounds the length of the log at the continuation, and the bounds of the
continuation go through that hypothesis and the length bounds of the derived lists.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimeBoundLenHypTest

open CatCrypt.Core CatCrypt.Crypto CatCrypt.Container OracleProg

/-- A record: a marked value or nothing. -/
inductive Ev where
  /-- A marked value. -/
  | mark (n : ℕ)
  /-- Nothing. -/
  | skip

/-- The pairs of a record: one for a mark, none otherwise. -/
def Ev.pairs : Ev → List (ℕ × ℕ)
  | .mark n => [(n, n + 1)]
  | _ => []

/-- Whether a record is a mark. -/
def Ev.isMark : Ev → Bool
  | .mark _ => true
  | .skip => false

/-- A handler program with records: one query on `i`, at step cost `1`, and one record. -/
def hrec (i : ℕ) : ℕ × Timed ℕ ℕ (ℕ × List Ev) :=
  (0, .query i (fun _ => 1) fun o => .pure (o, [if o = 0 then .skip else .mark o]))

/-- The name of `srch.timed`. -/
def srch : Unit := ()

/-- The binder program `A x` with its queries answered by `hrec`, followed by a search of the
pairs of the log for a pair whose first component is `x`. -/
noncomputable def srch.timed (A : ℕ → Timed ℕ ℕ ℕ) (x : ℕ) : ℕ × Timed ℕ ℕ ℕ :=
  Timed.delay (1 + (Timed.collectLog hrec (A x)).1)
    ((Timed.collectLog hrec (A x)).2.bind fun al =>
      (List.find?.timedCost (fun s => s.1 == x) (fun _ => 1) (al.2.flatMap Ev.pairs) +
        (List.flatten.timedCost (al.2.map Ev.pairs) +
          List.map.timedCost Ev.pairs (fun _ => 2) al.2), .pure al.1))

derive_time_bound +queries srch

/-- The log has length at most `q` (one record per query), so its pairs number at most `q`
(each record has at most one), and the search, the flattening and the map each cost a linear
function of `q`. -/
example (A : ℕ → Timed ℕ ℕ ℕ) (x : ℕ) {q T : ℕ}
    (hA : ∀ x, UseBound (useCharge fun _ => 1) (fun _ _ => True) (Timed.toFreeMT (A x))
      (budget q T)) :
    Timed.StepTimeBound (srch.timed A x) (T + 21 * q + 4) ∧
      QueryCostLe (fun _ => 1) (srch.timed A x).2.erase q := by
  obtain ⟨h1, h2⟩ := srch.timeBound_timed A x hA
  exact ⟨h1.mono (by omega), by simpa using h2⟩

/-- The name of `memb.timed`. -/
def memb : Unit := ()

/-- As `srch`, with a test that checks membership of the second component among the first
components of the pairs of the log. -/
noncomputable def memb.timed (A : ℕ → Timed ℕ ℕ ℕ) (x : ℕ) : ℕ × Timed ℕ ℕ ℕ :=
  Timed.delay (1 + (Timed.collectLog hrec (A x)).1)
    ((Timed.collectLog hrec (A x)).2.bind fun al =>
      (List.find?.timedCost (fun s => ((al.2.flatMap Ev.pairs).map Prod.fst).contains s.2)
        (fun s => 1 + List.elem.timedCost s.2 ((al.2.flatMap Ev.pairs).map Prod.fst))
        (al.2.flatMap Ev.pairs), .pure al.1))

derive_time_bound +queries memb

/-- Each of the at most `q` tests is a membership test among at most `q` first components, so
the search costs a quadratic function of `q`. -/
example (A : ℕ → Timed ℕ ℕ ℕ) (x : ℕ) {q T : ℕ}
    (hA : ∀ x, UseBound (useCharge fun _ => 1) (fun _ _ => True) (Timed.toFreeMT (A x))
      (budget q T)) :
    Timed.StepTimeBound (memb.timed A x) (T + 4 * q * q + 11 * q + 2) ∧
      QueryCostLe (fun _ => 1) (memb.timed A x).2.erase q := by
  obtain ⟨h1, h2⟩ := memb.timeBound_timed A x hA
  exact ⟨h1.mono (le_of_eq (by ring)), by simpa using h2⟩

/-- The name of `filt.timed`. -/
def filt : Unit := ()

/-- As `srch`, followed by the marks of the log and their number. -/
noncomputable def filt.timed (A : ℕ → Timed ℕ ℕ ℕ) (x : ℕ) : ℕ × Timed ℕ ℕ ℕ :=
  Timed.delay (1 + (Timed.collectLog hrec (A x)).1)
    ((Timed.collectLog hrec (A x)).2.bind fun al =>
      (List.filter.timedCost Ev.isMark (fun _ => 1) al.2 +
        List.length.timedCost (al.2.filter Ev.isMark), .pure (al.2.filter Ev.isMark).length))

derive_time_bound +queries filt

/-- The marks of the log are at most as many as its records, so the filter and the length of
its result cost a linear function of `q`. -/
example (A : ℕ → Timed ℕ ℕ ℕ) (x : ℕ) {q T : ℕ}
    (hA : ∀ x, UseBound (useCharge fun _ => 1) (fun _ _ => True) (Timed.toFreeMT (A x))
      (budget q T)) :
    Timed.StepTimeBound (filt.timed A x) (T + 13 * q + 3) ∧
      QueryCostLe (fun _ => 1) (filt.timed A x).2.erase q := by
  obtain ⟨h1, h2⟩ := filt.timeBound_timed A x hA
  exact ⟨h1.mono (by omega), by simpa using h2⟩

/-- The length of a list defined by cases, each case a literal, is bounded by the longest
literal. -/
example : ∀ e, (Ev.pairs e).length ≤ 1 := by
  intro e; cases e <;> simp [Ev.pairs]

end CatCrypt.Tactics.DeriveTimeBoundLenHypTest
