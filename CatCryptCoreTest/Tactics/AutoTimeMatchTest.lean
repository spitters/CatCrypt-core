/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoTime
public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.DeriveReduction

/-!
# Tests of `time_bound` on a nested match in a step cost

A decision on an event whose tick reads a command of a structure state: a `match` on the event
whose tick alternative is a `match` with seven alternatives on the command of the popped
state, with further matches and `if`s inside the alternatives. The bound of
`derive_time_bound` is the same nested match over the bounds of the alternatives
(`matchBound`); `time_bound` compares the two matches alternative by alternative.

## Main results

* `startRed.tree.timeBound_timed` — emitted by `derive_time_bound`
* an `example` of the same statement closed by `time_bound`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.AutoTimeMatchTest

open CatCrypt.Core

/-- A command. -/
inductive Cmd where
  | skip
  | letAt (x : ℕ)
  | comm (x : ℕ)
  | ite (x : ℕ) (b : Bool)
  | output (h : ℕ)
  | input (h : ℕ)
  | relabel (p : ℕ) (kd : Bool)

/-- An event. -/
inductive Ev where
  | inp (h v : ℕ)
  | adv (p v : ℕ)
  | tick

/-- A state. -/
structure St where
  /-- Input queues. -/
  iq : ℕ → List ℕ
  /-- Adversary queues. -/
  aq : ℕ → List ℕ
  /-- A buffer. -/
  buf : List ℕ
  /-- The current command. -/
  cur : Cmd

/-- The state past a finished command. -/
def pop (s : St) : St :=
  match s.cur with
  | .skip => { s with cur := .letAt 0 }
  | _ => s

/-- A tick: the step of the command of the popped state. -/
def tick (s : St) : St × List ℕ :=
  let c := pop s
  match c.cur with
  | .skip => (c, c.buf ++ c.buf)
  | .letAt x => ({ c with buf := c.buf ++ [x] ++ c.iq x ++ c.aq x }, c.iq x ++ c.aq x)
  | .comm x => ({ c with buf := c.aq x ++ c.buf }, c.iq x ++ c.buf ++ c.aq x)
  | .ite x b => if b then (c, c.iq x ++ c.aq x ++ c.buf) else (c, c.aq x ++ c.iq x)
  | .output h => ({ c with buf := c.buf ++ c.aq h }, match c.buf.head? with
      | some w => w :: c.aq h ++ c.iq h
      | none => c.iq h ++ c.buf)
  | .input h => match c.iq h with
      | [] => (c, c.aq h ++ c.buf)
      | v :: vs => ({ c with buf := vs ++ c.buf }, c.aq h ++ [v] ++ c.iq v)
  | .relabel p kd => if kd then (c, c.aq p ++ c.iq p) else match c.aq p with
      | [] => (c, c.buf ++ c.iq p)
      | w :: ws => ({ c with buf := ws ++ c.buf }, ws ++ c.iq w ++ c.aq w)

/-- The decision on an event, returning the state. -/
def dec (s : St) : Ev → St × List ℕ
  | .inp h v => ({ s with buf := s.buf ++ s.iq h }, [v])
  | .adv p v => ({ s with buf := s.buf ++ [p] ++ [v] }, [])
  | .tick => tick s

/-- The decision as a computation. -/
noncomputable def startRed (s : St) (e : Ev) : SPComp (St × List ℕ) :=
  SPComp.pure (dec s e)

derive_reduction startRed

derive_time_bound startRed.tree

/-- The time theorem of `startRed`, closed by `time_bound`. -/
example : type_of% @startRed.tree.timeBound_timed := by
  time_bound

end CatCrypt.Tactics.AutoTimeMatchTest

end
