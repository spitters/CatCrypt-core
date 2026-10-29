/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound

/-!
# Tests of case-split bounds of matches under `derive_time_bound`

Two reductions whose step costs contain a `match` with an alternative whose cost mentions its
pattern variables: `decRed` (the cost of `q h ++ [v]` in the alternative `inp h v`) and
`resumeRed` (a match on a field of a state, nested over the match of `decRed`). Their time
theorems are bounded by the same matches with each alternative replaced by its bound.

## Main results

* `decRed.tree.timeBound_timed` and `resumeRed.tree.timeBound_timed`, emitted by the command
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimeBoundMatchTest

open CatCrypt.Core

/-- An event: an input `v` for the queue `h`, or a tick. -/
inductive Ev where
  | inp (h : ℕ) (v : ℕ)
  | tick

/-- The queue `h` of `q` with the input `v` appended, on an input; empty on a tick. -/
def dec (q : ℕ → List ℕ) : Ev → List ℕ
  | .inp h v => q h ++ [v]
  | .tick => []

/-- The adversary called at the decision on `e`. -/
noncomputable def decRed (q : ℕ → List ℕ) (e : Ev) (A : List ℕ → SPComp Bool) :
    SPComp Bool :=
  A (dec q e)

derive_reduction decRed

derive_time_bound decRed.tree

/-- The time theorem of `decRed` bounds the decision by cases on the event: the length of the
queue `h` on an input `inp h v`, nothing on a tick. -/
example (q : ℕ → List ℕ) (qCost : ℕ → ℕ) (e : Ev) (A : List ℕ → SPTree.Timed Bool)
    (ACost : List ℕ → ℕ) {t T c : ℕ} (hq : ∀ a, qCost a ≤ t) (hA : ∀ a, (A a).time ≤ T)
    (hAc : ∀ a, ACost a ≤ c) :
    SPTree.Timed.stepTime (decRed.tree.timed q qCost e A ACost) ≤
      (c + match e with
        | Ev.inp h _ => 1 + (2 * (q h).length + 1 + (1 + t))
        | Ev.tick => 0) + T + 3 :=
  decRed.tree.timeBound_timed q qCost e A ACost hq hA hAc

/-- The work left in a state. -/
inductive Pend where
  | idle
  | evt (e : Ev)
  | bind (x : ℕ) (w : Option ℕ)

/-- A state: queues, a buffer and the work left. -/
structure St where
  /-- The queues. -/
  iq : ℕ → List ℕ
  /-- The buffer. -/
  buf : List ℕ
  /-- The work left. -/
  pend : Pend

/-- The answer `ans` received in the state `s`: a match on the work left, then on the waiting
event. -/
def resume (s : St) (ans : List ℕ) : List ℕ :=
  match s.pend with
  | .evt e => dec s.iq e ++ ans
  | .bind x w => if x = 0 then s.buf ++ ans else (w.getD x) :: s.iq x
  | .idle => s.buf

/-- The adversary called at the answer received in a state. -/
noncomputable def resumeRed (s : St) (ans : List ℕ) (A : List ℕ → SPComp Bool) :
    SPComp Bool :=
  A (resume s ans)

derive_reduction resumeRed

derive_time_bound resumeRed.tree

end CatCrypt.Tactics.DeriveTimeBoundMatchTest
