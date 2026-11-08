/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.DeriveTimeBound.Basic
public import CatCryptCore.Tactics.DeriveTimeRec

/-!
# Tests for certified callees of `derive_reduction`

A computation certified by `derive_reduction` is called through its tree, its costed form and
its time theorem, and is not unfolded in its callers.

* `once`, a non-recursive computation that calls its adversary once, is certified by
  `derive_reduction once`; `twice` calls it two times. The tree `twice.tree` calls `once.tree`,
  the costed form `twice.tree.timed` calls `once.tree.timed`, neither mentions the adversary
  call of the body of `once`, and the time theorem of `twice` is stated with two bounds of
  `once` (`twice.tree.timeBound_timed`).
* `each` runs the certified helper `step` over a list by a recursive loop `loop`, whose
  argument is the call of `step`: the tree of `each` passes the tree of `step` to the tree of
  the loop, and its costed form passes `step.tree.timed`, so that the time of `each` follows
  from the time theorems of `loop` (`derive_time_rec`, linear in the length of the list per
  element) and of `step`. `List.mapM` itself, a loop generic in its monad and universe, is
  not reflected by `derive_reduction` and is not a registered loop combinator.
* `twiceU` calls `onceU`, which has the body of `once` and is not certified: its call is
  unfolded, and the tree of `twiceU` calls the adversary directly.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveReductionCertifiedTest

open Lean Meta CatCrypt.Core

/-- Whether the value of the definition `d` mentions the constant `c`. -/
def mentions (d c : Name) : MetaM Bool := do
  let some (.defnInfo v) := (← getEnv).find? d | throwError "no definition `{d}`"
  return v.value.getUsedConstants.contains c

/-! ### T1: a certified helper called twice -/

/-- One call of the adversary on `x`, negated. -/
noncomputable def once (A : Bool → SPComp Bool) (x : Bool) : SPComp Bool := do
  let b ← A x
  return !b

derive_reduction once

derive_time_bound once.tree

/-- Two calls of the certified helper `once`. -/
noncomputable def twice (A : Bool → SPComp Bool) : SPComp Bool := do
  let y ← once A true
  once A y

derive_reduction twice

derive_time_bound twice.tree

run_meta do
  unless CatCrypt.Tactics.DeriveTimed.isCertified (← getEnv) ``once do
    throwError "`once` is not certified"
  unless ← mentions ``twice.tree ``once.tree do throwError "`twice.tree` does not call `once.tree`"
  unless ← mentions ``twice.tree.timed ``once.tree.timed do
    throwError "`twice.tree.timed` does not call `once.tree.timed`"
  if (← mentions ``twice.tree ``once) || (← mentions ``twice.tree ``not) ||
      (← mentions ``twice.tree ``Bool.not) then
    throwError "`twice.tree` has the body of `once` inlined"

/-- The time of `twice` is two bounds of `once`, at the cost companion `1 + ACost` that the
call passes, plus two units of its own. -/
example (A : Bool → SPTree.Timed Bool) (ACost : Bool → ℕ) {T t : ℕ} (hA : ∀ a, (A a).time ≤ T)
    (hc : ∀ a, ACost a ≤ t) :
    SPTree.Timed.stepTime (twice.tree.timed A ACost) ≤ 2 * ((t + 1) + T + 3) + 2 := by
  have := twice.tree.timeBound_timed A ACost hA hc
  omega

/-! ### T2: a certified helper as the argument of a loop -/

/-- One sample and one call of the adversary on it, paired with the input. -/
noncomputable def step (A : Bool → SPComp ℕ) (n : ℕ) : SPComp ℕ := do
  let b ← SPComp.sample Bool
  let k ← A b
  return n + k

derive_reduction step

derive_time_bound step.tree


/-- The run of `f` over a list, collecting the results. -/
noncomputable def loop (f : ℕ → SPComp ℕ) : List ℕ → SPComp (List ℕ)
  | [] => SPComp.pure []
  | a :: as => (f a).bind fun y => (loop f as).bind fun ys => SPComp.pure (y :: ys)

derive_reduction loop

/-- The helper `step` run over the list `l` by `loop`. -/
noncomputable def each (A : Bool → SPComp ℕ) (l : List ℕ) : SPComp (List ℕ) :=
  loop (fun n => step A n) l

derive_reduction each

run_meta do
  unless ← mentions ``each.tree ``step.tree do throwError "`each.tree` does not call `step.tree`"
  unless ← mentions ``each.tree ``loop.tree do throwError "`each.tree` does not call `loop.tree`"
  if ← mentions ``each.tree ``SPTree.sample then
    throwError "`each.tree` has the body of `step` inlined"

derive_time_rec loop.tree using fun (l : List ℕ) T_f t_fCost =>
  (T_f + t_fCost + 4 + l.length) * l.length + 1

/-- The time of `each` from the certificates of `loop` and `step`: the costed form of `each`
passes the costed tree of `step` and its step cost to the costed form of `loop`. -/
example (A : Bool → SPTree.Timed ℕ) (ACost : Bool → ℕ) (l : List ℕ) {T t : ℕ}
    (hA : ∀ a, (A a).time ≤ T) (hc : ∀ a, ACost a ≤ t) :
    SPTree.Timed.stepTime (each.tree.timed A ACost l) ≤
      1 + ((t + 1 + 2 * T + 4) + (1 + (t + 1 + 2 * T + 4)) + 4 + l.length) * l.length + 1 := by
  have hs := fun n => step.tree.timeBound_timed (fun a => A a) (fun a => 1 + ACost a) n hA
    (fun a => Nat.add_le_add_left (hc a) 1)
  have := loop.tree.timeBound_timed
    (fun n => (step.tree.timed (fun a => A a) (fun a => 1 + ACost a) n).2)
    (fun n => 1 + (step.tree.timed (fun a => A a) (fun a => 1 + ACost a) n).1) l
    (T_f := t + 1 + 2 * T + 4) (t_fCost := 1 + (t + 1 + 2 * T + 4))
    (fun n => by have := hs n; simp only [SPTree.Timed.stepTime] at this ⊢; omega)
    (fun n => by have := hs n; simp only [SPTree.Timed.stepTime] at this ⊢; omega)
  simp only [each.tree.timed, SPTree.Timed.stepTime_delay]
  omega

/-! ### T3: an uncertified helper is unfolded -/

/-- The body of `once`, not certified. -/
noncomputable def onceU (A : Bool → SPComp Bool) (x : Bool) : SPComp Bool := do
  let b ← A x
  return !b

/-- Two calls of the uncertified helper `onceU`. -/
noncomputable def twiceU (A : Bool → SPComp Bool) : SPComp Bool := do
  let y ← onceU A true
  onceU A y

derive_reduction twiceU

run_meta do
  if CatCrypt.Tactics.DeriveTimed.isCertified (← getEnv) ``onceU then
    throwError "`onceU` is certified"
  if (← getEnv).contains (``onceU ++ `tree) then throwError "`onceU.tree` was derived"
  if ← mentions ``twiceU.tree ``onceU then throwError "`twiceU.tree` calls `onceU`"
  unless (← mentions ``twiceU.tree ``not) || (← mentions ``twiceU.tree ``Bool.not) do
    throwError "`twiceU.tree` does not have the body of `onceU` inlined"

end CatCrypt.Tactics.DeriveReductionCertifiedTest
