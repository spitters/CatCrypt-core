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

`fireRed` matches a structure answer whose operator alternative folds over the gates of the
operator: the closed form of the fold keeps their length, which the `@[length_bound]` theorem
`gatesOf_length_le` bounds, so the time theorem has one bound for every answer.

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

/-- A gate: a literal, or an operator `o` with an offset `z`. -/
inductive Gate where
  | lit (n : ℕ)
  | op (z : ℕ) (o : ℕ)

/-- An answer: a gate and a tag. -/
structure Ans where
  /-- The gate. -/
  gate : Gate
  /-- The tag. -/
  tag : ℕ

/-- The gates of the operator `o`: one or two. -/
def gatesOf (o : ℕ) : List ℕ := if o < 2 then [o] else [o, o]

derive_cost gatesOf

/-- Building the gates of an operator costs at most one unit. -/
theorem gatesOf.timedCost_le (o : ℕ) : gatesOf.timedCost o ≤ 1 := by
  unfold gatesOf.timedCost; grind

/-- An operator has at most two gates. -/
@[length_bound] theorem gatesOf_length_le (o : ℕ) : (gatesOf o).length ≤ 2 := by
  unfold gatesOf; split <;> simp

/-- The value of an answer: the literal, or a fold over the gates of the operator that adds the
offset and the gate at each position to the tag. -/
def fire (a : Ans) : ℕ :=
  match a.gate, a.tag with
  | .lit n, _ => n
  | .op z o, t =>
    let g := gatesOf o
    Fin.foldr g.length (fun j acc => acc + z + g.getD j.val 0) t

/-- The adversary called at the value of the answer. -/
noncomputable def fireRed (a : Ans) (A : ℕ → SPComp Bool) : SPComp Bool :=
  A (fire a)

derive_reduction fireRed

-- the closed form of the fold, free of the offset `z`, keeps the length of the gates of `o`;
-- `@[length_bound]` on `gatesOf_length_le` bounds it, so the bound is free of the answer
derive_time_bound fireRed.tree

/-- The time theorem of `fireRed` bounds its step time by one bound for every answer. -/
example (A : ℕ → SPTree.Timed Bool) (ACost : ℕ → ℕ) {T c : ℕ}
    (hA : ∀ x, (A x).time ≤ T) (hc : ∀ x, ACost x ≤ c) :
    ∃ E, ∀ a, SPTree.Timed.stepTime (fireRed.tree.timed a A ACost) ≤ E :=
  ⟨_, fun a => fireRed.tree.timeBound_timed a A ACost hA hc⟩

end CatCrypt.Tactics.DeriveTimeBoundMatchTest
