/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Tactics.ClassicalCostAudit
public import CatCryptCore.Tactics.StdCosts
public import CatCryptCore.Tactics.StdCostsPoly
import CatCryptCore.Core.SPTree

/-!
# Tests for the refusal of classical decisions by `derive_timed` (rule (n))

A decision by a classical `Decidable` instance has no running time and is refused, with a
message that names the declaration, the condition, the classical instance and the fix: in an
`if` and in a `decide`, inside a computable instance (a conjunction with a classical
component), as a decision procedure evaluated as data, and as the decision instance passed to a
registered primitive (`Finset.filter`). The same programs with a computable decision procedure
(an instance binder, or the instance of the concrete type) derive without a message, and the
decision is priced by the cost of its condition. Decisions of Boolean conditions built with
`||`, `&&` and `!`, which Lean 4.35 marks `noncomputable` and compiles through `@[csimp]`
replacements, are computable. A polynomial term, whose Mathlib representation `Finsupp.single`
decides its support classically, is priced by the registered cost of `Finsupp.single`
(`CatCryptCore.Tactics.StdCostsPoly`). A data term computed by `Exists.choose` is warned about
and then refused, since `Classical.choice` has no cost. `#classical_cost_audit` finds no classical
decision in the derived costed forms.
-/

@[expose] public section

open CatCrypt.Core

namespace CatCryptCoreTest.DeriveClassicalFlag

/-! ## Refused: decisions by a classical instance -/

/-- `a` when `p a` holds, decided by the classical instance, otherwise `b`. -/
noncomputable def classicalPick (p : ℕ → Prop) (a b : ℕ) : SPTree ℕ :=
  open Classical in if p a then .ret a else .ret b

/--
error: derive_timed: `CatCryptCoreTest.DeriveClassicalFlag.classicalPick` decides `p a` by the
classical instance `Classical.propDecidable (p a)`, which has no running time (rule (n)); decide
it by a computable instance: a `[Decidable _]`, `[DecidablePred _]` or `[DecidableEq _]` binder,
or a computable instance at the concrete type
-/
#guard_msgs (whitespace := lax) in
derive_timed classicalPick

/-- The truth value of `p a`, decided by the classical instance. -/
noncomputable def classicalTest (p : ℕ → Prop) (a : ℕ) : SPTree Bool :=
  open Classical in .ret (decide (p a))

/--
error: derive_timed: `CatCryptCoreTest.DeriveClassicalFlag.classicalTest` decides `p a` by the
classical instance `Classical.propDecidable (p a)`, which has no running time (rule (n)); decide
it by a computable instance: a `[Decidable _]`, `[DecidablePred _]` or `[DecidableEq _]` binder,
or a computable instance at the concrete type
-/
#guard_msgs (whitespace := lax) in
derive_timed classicalTest

/-- An equality of values of a type without decidable equality, decided classically. -/
noncomputable def classicalEq {α : Type} (x y : α) : SPTree Bool :=
  open Classical in if x = y then .ret true else .ret false

/--
error: derive_timed: `CatCryptCoreTest.DeriveClassicalFlag.classicalEq` decides `x = y` by the
classical instance `Classical.propDecidable (x = y)`, which has no running time (rule (n));
decide it by a computable instance: a `[Decidable _]`, `[DecidablePred _]` or `[DecidableEq _]`
binder, or a computable instance at the concrete type
-/
#guard_msgs (whitespace := lax) in
derive_timed classicalEq

/-- A conjunction whose first component is decided classically and whose second is decided by
the equality of `ℕ`: the instance `instDecidableAnd` is computable, its first argument is not. -/
noncomputable def classicalAnd (p : ℕ → Prop) (a : ℕ) : SPTree ℕ :=
  open Classical in if p a ∧ a = 3 then .ret a else .ret 0

/--
error: derive_timed: `CatCryptCoreTest.DeriveClassicalFlag.classicalAnd` decides `p a ∧ a = 3`
by the classical instance `Classical.propDecidable (p a)` (in the instance
`instDecidableAnd`), which has no running time (rule (n)); decide it by a computable instance: a
`[Decidable _]`, `[DecidablePred _]` or `[DecidableEq _]` binder, or a computable instance at
the concrete type
-/
#guard_msgs (whitespace := lax) in
derive_timed classicalAnd

/-- A classical decision procedure evaluated as data: the discriminant of a match. -/
noncomputable def classicalMatch {α : Type} (x y : α) : SPTree ℕ :=
  match Classical.decEq α x y with
  | .isTrue _ => .ret 1
  | .isFalse _ => .ret 0

/--
error: derive_timed: `CatCryptCoreTest.DeriveClassicalFlag.classicalMatch` decides `x = y` by the
classical instance `Classical.decEq α x y`, which has no running time (rule (n)); decide it by a
computable instance: a `[Decidable _]`, `[DecidablePred _]` or `[DecidableEq _]` binder, or a
computable instance at the concrete type
-/
#guard_msgs (whitespace := lax) in
derive_timed classicalMatch

/-- The number of elements of `s` that satisfy `p`, the predicate decided classically by
`Finset.filter`, a registered primitive (rule (i)). -/
noncomputable def classicalFilter (p : ℕ → Prop) (s : Finset ℕ) : SPTree ℕ :=
  open Classical in .ret (s.filter p).card

/--
error: derive_timed: `CatCryptCoreTest.DeriveClassicalFlag.classicalFilter` passes to
`Finset.filter` the decision procedure of `DecidablePred p` by the classical instance
`fun a ↦ Classical.propDecidable (p a)`, which has no running time (rule (n)); decide it by a
computable instance: a `[Decidable _]`, `[DecidablePred _]` or `[DecidableEq _]` binder, or a
computable instance at the concrete type
-/
#guard_msgs (whitespace := lax) in
derive_timed classicalFilter

/-! ## Derived: the same programs with a computable decision procedure -/

/-- `classicalPick` with the decision instance as a binder. -/
def decPick (p : ℕ → Prop) [DecidablePred p] (a b : ℕ) : SPTree ℕ :=
  if p a then .ret a else .ret b

#guard_msgs in
derive_timed decPick

/-- The decision costs one unit and the cost of its condition; the instance binder is supplied
by the caller. -/
example (p : ℕ → Prop) [DecidablePred p] (a b : ℕ) :
    decPick.timed p a b =
      SPTree.Timed.delay 1 (if p a then (0, .ret a) else (0, .ret b)) := rfl

/-- `classicalEq` with an instance binder of decidable equality. -/
def decEqTest {α : Type} [DecidableEq α] (x y : α) : SPTree Bool :=
  if x = y then .ret true else .ret false

#guard_msgs in
derive_timed decEqTest

/-- `classicalAnd` at the decidable predicate binder: both components are computable. -/
def decAnd (p : ℕ → Prop) [DecidablePred p] (a : ℕ) : SPTree ℕ :=
  if p a ∧ a = 3 then .ret a else .ret 0

#guard_msgs in
derive_timed decAnd

/-- `classicalMatch` at the decidable equality of `ℕ`, a computable instance at the concrete
type. -/
def natMatch (x y : ℕ) : SPTree ℕ :=
  match decEq x y with
  | .isTrue _ => .ret 1
  | .isFalse _ => .ret 0

#guard_msgs in
derive_timed natMatch

/-- `classicalFilter` with the decision instance of the predicate as a binder. -/
def decFilter (p : ℕ → Prop) [DecidablePred p] (s : Finset ℕ) : SPTree ℕ :=
  .ret (s.filter p).card

#guard_msgs in
derive_timed decFilter

/-- `a` when `a = 3`, decided by the computable equality of `ℕ`, otherwise `b`. -/
def natPick (a b : ℕ) : SPTree ℕ := if a = 3 then .ret a else .ret b

#guard_msgs in
derive_timed natPick

/-! ## Derived: Boolean conditions

The conditions `b || c`, `b && !c` are decided by `instDecidableEqBool`, a computable instance;
`Bool.or`, `Bool.and` and `Bool.not` are compiled through their `@[csimp]` replacements, and the
cost of the condition charges their evaluation. -/

/-- A test of a status table: `p` is registered and corrupt, as the corruption tests of a
party step. -/
def statusTest (reg : ℕ → Option ℕ) (corrupt : ℕ → Bool) (p : ℕ) : SPTree ℕ :=
  if (reg p).isSome && corrupt p then .ret 1 else if !corrupt p then .ret 2 else .ret 0

#guard_msgs in
derive_timed statusTest

/-- Each decision is charged: the units of the `if` and the evaluation of its condition, with
the companions of the tables `reg` and `corrupt`. -/
example (reg : ℕ → Option ℕ) (regCost : ℕ → ℕ) (corrupt : ℕ → Bool) (corruptCost : ℕ → ℕ)
    (p : ℕ) :
    statusTest.timed reg regCost corrupt corruptCost p =
      SPTree.Timed.delay (2 + (1 + (1 + regCost p + 1) + (1 + corruptCost p + 1)))
        (if ((reg p).isSome && corrupt p) = true then (0, .ret 1)
        else SPTree.Timed.delay (2 + (1 + corruptCost p + 1))
          (if (!corrupt p) = true then (0, .ret 2) else (0, .ret 0))) := rfl

/-- A Boolean condition with `||` on a stuck flag and an optional value. -/
def stuckTest (stuck : ℕ → Bool) (inj : ℕ → Option ℕ) (p : ℕ) : SPTree ℕ :=
  if stuck p || (inj p).isSome then .ret 0 else .ret p

#guard_msgs in
derive_timed stuckTest

/-! ## A library definition that decides classically: polynomial terms

`Polynomial.C a` and `Polynomial.X` unfold to `Finsupp.single`, whose support Mathlib computes by
deciding `a = 0` with `Classical.decEq`; `Finsupp.single` is a registered primitive of
`StdCostsPoly`, so the derivation does not reach that decision. -/

/-- The polynomial of the base-`p` digits of `a`, the decoding of a sampled index. -/
noncomputable def digitsPoly (p : ℕ) [Fact (Nat.Prime p)] : ℕ → ℕ → Polynomial (ZMod p)
  | 0, _ => 0
  | t + 1, a => Polynomial.C (a : ZMod p) + Polynomial.X * digitsPoly p t (a / p)

/-- The tree returning the decoded polynomial. -/
noncomputable def digitsTree (p : ℕ) [Fact (Nat.Prime p)] (t a : ℕ) :
    SPTree (Polynomial (ZMod p)) :=
  .ret (digitsPoly p t a)

#guard_msgs in
derive_timed digitsTree

/-- A level of the decoding writes two terms, `C a` and `X`, at the registered cost of
`Finsupp.single`. -/
example (p : ℕ) [Fact (Nat.Prime p)] (t a : ℕ) :
    digitsPoly.timedCost p (t + 1) a =
      1 + (1 + (7 + Finsupp.single.timedCost ℕ (ZMod p) 0 (a : ZMod p) +
        (1 + (5 + Finsupp.single.timedCost ℕ (ZMod p) 1 1 +
          (1 + (digitsPoly.timedCost p t (a / p) + 1)))))) :=
  digitsPoly.timedCost.eq_2 p a t

/-! ## Choice in data -/

/-- A witness of `2 < n`, chosen. -/
noncomputable def chosenRet (h : ∃ n : ℕ, 2 < n) : SPTree ℕ := .ret h.choose

/--
warning: derive_timed: `CatCryptCoreTest.DeriveClassicalFlag.chosenRet` computes `h.choose` by
Classical.choice; it has no running time
---
error: derive_timed: needs a registered primitive: `Classical.choice` has no definition to price
and no registered cost `Classical.choice.timedCost`
-/
#guard_msgs (whitespace := lax) in
derive_timed chosenRet

/-! ## The audit of the costed forms -/

/--
info: classical_cost_audit: 0 of 10 costed forms and costs
-/
#guard_msgs (whitespace := lax) in
#classical_cost_audit CatCryptCoreTest.DeriveClassicalFlag

end CatCryptCoreTest.DeriveClassicalFlag

end
