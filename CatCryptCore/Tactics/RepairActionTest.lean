/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Lean
public meta import CatCryptCore.Tactics.RepairAction
public import CatCryptCore.Tactics.AutoDispatch
public meta import CatCryptCore.Tactics.AutoDispatch

/-!
# Leaves for the grind repair code action

Seven tactic leaves on which the code action of `CatCryptCore.Tactics.RepairAction` is
requested at the leaf's line. Each declaration is wrapped in `#guard_msgs (drop all)`, so
that the failing tactics and the open goals elaborate without diagnostics.

| leaf | goal | arm expected to close |
|---|---|---|
| `skip` | `a < b + 1` from `a ≤ b` | `grind` |
| `exact rfl` | `(xs ++ []).length = xs.length` | `grind` |
| `simp only [triple]` | `triple n = 3 * n` | `grind [triple]` |
| `skip` | `a * b = a + b` (false) | none |
| `simp [sumTo]` | `2 * sumTo n = n * (n + 1)` (needs induction) | none |
| `exact hp` | `p ∧ q` | `grind` |
| `skip` inside `have` | `a + 1 < c` | `grind` |

Game-shaped leaves on which the tactic `repair_dispatch_probe` of this file runs
`RepairAction.repairGoal` (the arms `grind`, `grind [names]` and `catcrypt_auto?`),
requires the closing arm's text to start with the given prefix, and closes the goal with
that text; and a goal on which no arm closes, where the arms stop within the given time.

| leaf | goal | closing arm |
|---|---|---|
| side condition | `IsPure flipNeg` | `(unfold flipNeg; simp only [...]; aesop ...)` |
| side condition | `IsPure` of a `do` block | `(simp only [...]; aesop ...)` |
| relational | `rHoare eqPre (bind (pure a) negStep) (negStep a) eqPost` | `aesop ...` |
| advantage sum | sum of two `AdvantageA` hops `≤ ε₁ + ε₂` | `sum_atoms_le` |
| game equality | `gameL = gameR` (samples swapped) | `(unfold gameL; …; bind_swap_nf)` |
| none | `2 * sumTo n = n * (n + 1)` | no arm, within 1000 ms |
-/

set_option autoImplicit false

namespace CatCryptCore.RepairActionTest

/-- Three times `n`, as an opaque definition. -/
def triple (n : Nat) : Nat := n + n + n

/-- The sum `0 + 1 + ⋯ + n`. -/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

#guard_msgs (drop all) in
example (a b : Nat) (h : a ≤ b) : a < b + 1 := by
  skip

#guard_msgs (drop all) in
example (xs : List Nat) : (xs ++ []).length = xs.length := by
  exact rfl

#guard_msgs (drop all) in
example (n : Nat) : triple n = 3 * n := by
  simp only [triple]

#guard_msgs (drop all) in
example (a b : Nat) : a * b = a + b := by
  skip

#guard_msgs (drop all) in
example (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  simp [sumTo]

#guard_msgs (drop all) in
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  exact hp

#guard_msgs (drop all) in
example (a b c : Nat) (h1 : a < b) (h2 : b < c) : a < c := by
  have h : a + 1 < c := by
    skip
  omega

/-! ## The arm `catcrypt_auto?` -/

public meta section

open Lean Elab Meta CatCryptCore.RepairAction

/-- One entry per arm: its text, time and outcome. -/
def report (rs : Array ArmResult) : String :=
  "; ".intercalate (rs.map fun r =>
    s!"{r.text}: {r.ms} ms, {if r.closed then "closed" else r.msg}").toList

/-- `repairGoal` on the main goal, the arms reported as information with their total time. -/
def probeArms (stx : Syntax) : Tactic.TacticM (Array ArmResult × Nat) := do
  let g ← Tactic.getMainGoal
  let some r := stx.getRange? | throwError "repair_dispatch_probe: no source range"
  let rs ← g.withContext (repairGoal g .missing r (← Term.getDeclName?))
  let total := rs.foldl (· + ·.ms) 0
  logInfo m!"repair arms ({total} ms): {report rs}"
  return (rs, total)

/-- `repair_dispatch_probe closes "p"` requires that `repairGoal` closes the main goal by an
arm whose text starts with `p`, then closes the goal with that text. It reports the arms
with their times. -/
syntax (name := probeCloses) "repair_dispatch_probe" " closes " str : tactic

/-- `repair_dispatch_probe fails_within n` requires that no arm of `repairGoal` closes the
main goal and that the arms take under `n` milliseconds in all; the goal is unchanged. It
reports the arms with their times. -/
syntax (name := probeFails) "repair_dispatch_probe" " fails_within " num : tactic

@[tactic probeCloses, inherit_doc probeCloses]
def evalProbeCloses : Tactic.Tactic := fun stx => do
  let p := stx[2].isStrLit?.getD ""
  let (rs, _) ← probeArms stx
  let some c := rs.find? (·.closed)
    | throwError "repair_dispatch_probe: no arm closes the goal: {report rs}"
  unless c.text.startsWith p do
    throwError "repair_dispatch_probe: the closing arm is {c.text}, expected {p}"
  let .ok tac := Parser.runParserCategory (← getEnv) `tactic c.text
    | throwError "repair_dispatch_probe: the closing text does not parse: {c.text}"
  Tactic.evalTactic tac

@[tactic probeFails, inherit_doc probeFails]
def evalProbeFails : Tactic.Tactic := fun stx => do
  let n := stx[2].isNatLit?.getD 0
  let (rs, total) ← probeArms stx
  if let some c := rs.find? (·.closed) then
    throwError "repair_dispatch_probe: the arm {c.text} closes the goal"
  unless total < n do
    throwError "repair_dispatch_probe: the arms take {total} ms, not under {n} ms"

end

section Dispatch

open CatCrypt.Core CatCrypt.Relational CatCrypt.Crypto
open scoped ENNReal

/-- A fair coin, negated. -/
noncomputable def flipNeg : SPComp Bool := do
  let a ← SPComp.sample Bool
  pure (!a)

/-- Negation as a program. -/
noncomputable def negStep (b : Bool) : SPComp Bool := SPComp.pure (!b)

/-- Two coins sampled in one order. -/
noncomputable def gameL : SPComp Bool := do
  let a ← SPComp.sample Bool
  let b ← SPComp.sample Bool
  pure (a && !b)

/-- The coins of `gameL` sampled in the other order. -/
noncomputable def gameR : SPComp Bool := do
  let b ← SPComp.sample Bool
  let a ← SPComp.sample Bool
  pure (a && !b)

#guard_msgs (drop info) in
example : SPComp.IsPure flipNeg := by
  repair_dispatch_probe closes "(unfold"

#guard_msgs (drop info) in
example : SPComp.IsPure (do
    let a ← SPComp.sample Bool
    let b ← SPComp.sample Bool
    pure (a && b) : SPComp Bool) := by
  repair_dispatch_probe closes "(simp only"

#guard_msgs (drop info) in
example (a : Bool) :
    rHoare eqPre (SPComp.bind (SPComp.pure a) negStep) (negStep a) eqPost := by
  repair_dispatch_probe closes "aesop"

#guard_msgs (drop info) in
example (A : Bool → SPComp Bool) (ε₁ ε₂ : ℝ≥0∞)
    (h₁ : AdvantageA gameL flipNeg A ≤ ε₁) (h₂ : AdvantageA flipNeg gameR A ≤ ε₂) :
    AdvantageA gameL flipNeg A + AdvantageA flipNeg gameR A ≤ ε₁ + ε₂ := by
  repair_dispatch_probe closes "sum_atoms_le"

set_option repairAction.dispatchMillis 3000 in
#guard_msgs (drop info) in
example : gameL = gameR := by
  repair_dispatch_probe closes "(unfold"

set_option linter.unusedTactic false in
#guard_msgs (drop info) in
example (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  repair_dispatch_probe fails_within 1000
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumTo]; grind

end Dispatch

end CatCryptCore.RepairActionTest
