/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Tactics.ClassicalCostAudit
import CatCryptCore.Core.SPTree

/-!
# Tests for the classical-decision warning of `derive_timed`

A decision by a classical `Decidable` instance is derived with a warning naming the declaration.
A data term computed by `Exists.choose` is warned about and then refused, since `Classical.choice`
has no cost. A decision by a computable instance derives without a message.
`#classical_cost_audit` reports the classical decisions in the costed forms.
-/

@[expose] public section

open CatCrypt.Core

namespace CatCryptCoreTest.DeriveClassicalFlag

/-- `a` when `p a` holds, decided by the classical instance, otherwise `b`. -/
noncomputable def classicalPick (p : ℕ → Prop) (a b : ℕ) : SPTree ℕ :=
  open Classical in if p a then .ret a else .ret b

/--
warning: derive_timed: `CatCryptCoreTest.DeriveClassicalFlag.classicalPick` decides `p a` by a
classical instance (`Classical.propDecidable (p a)`); its time bound does not charge this
decision
-/
#guard_msgs (whitespace := lax) in
derive_timed classicalPick

/-- The truth value of `p a`, decided by the classical instance. -/
noncomputable def classicalTest (p : ℕ → Prop) (a : ℕ) : SPTree Bool :=
  open Classical in .ret (decide (p a))

/--
warning: derive_timed: `CatCryptCoreTest.DeriveClassicalFlag.classicalTest` decides `p a` by a
classical instance (`Classical.propDecidable (p a)`); its time bound does not charge this
decision
-/
#guard_msgs (whitespace := lax) in
derive_timed classicalTest

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

/-- `a` when `a = 3`, decided by the computable equality of `ℕ`, otherwise `b`. -/
def natPick (a b : ℕ) : SPTree ℕ := if a = 3 then .ret a else .ret b

#guard_msgs in
derive_timed natPick

/--
info: classical_cost_audit: 2 of 3 costed forms and costs
CatCryptCoreTest.DeriveClassicalFlag.classicalPick.timed: decides `p a` by a classical instance
  (`Classical.propDecidable (p a)`)
CatCryptCoreTest.DeriveClassicalFlag.classicalTest.timed: decides `p a` by a classical instance
  (`Classical.propDecidable (p a)`)
-/
#guard_msgs (whitespace := lax) in
#classical_cost_audit CatCryptCoreTest.DeriveClassicalFlag

end CatCryptCoreTest.DeriveClassicalFlag

end
