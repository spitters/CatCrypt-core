/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.CsimpAudit

/-!
# Tests for `#csimp_audit`

Four csimp theorems on toy definitions: one proved without axioms, one proved with
`Classical.choice`, one depending on a declared axiom and one with an unproved proof. The audit
passes the first two, warns on the third and reports the fourth as an error.
-/

public section

namespace CsimpAuditTest

/-- Specification of the clean replacement. -/
def specA (n : Nat) : Nat := n + 0

/-- Implementation of the clean replacement. -/
def implA (n : Nat) : Nat := n

/-- A csimp theorem proved without axioms. -/
@[csimp] theorem specA_csimp : @specA = @implA := by
  funext n
  simp [specA, implA]

/-- A `noncomputable` specification decided classically. -/
noncomputable def specC (n : Nat) : Bool := by
  classical
  exact decide (n = 0)

/-- Implementation of `specC`. -/
def implC (n : Nat) : Bool := n == 0

/-- A csimp theorem whose proof uses `Classical.choice`. -/
@[csimp] theorem specC_csimp : @specC = @implC := by
  funext n
  simp only [specC, implC]
  grind

/-- Specification of the replacement proved from a declared axiom. -/
def specD (n : Nat) : Nat := n * 1

/-- Implementation of `specD`. -/
def implD (n : Nat) : Nat := n

/-- An axiom outside the standard three. -/
axiom testAxiom : ∀ n : Nat, n * 1 = n

/-- A csimp theorem depending on `testAxiom`. -/
@[csimp] theorem specD_csimp : @specD = @implD := by
  funext n
  exact testAxiom n

/-- Specification of the unproved replacement. -/
def specB (n : Nat) : Nat := n + 1

/-- Implementation of `specB`, unequal to it. -/
def implB (n : Nat) : Nat := n

/-- warning: declaration uses `sorry` -/
#guard_msgs in
/-- A csimp theorem without a proof. -/
@[csimp] theorem specB_csimp : @specB = @implB := by
  sorry

/-- info: csimp audit: 1 theorems, 0 reported -/
#guard_msgs in
#csimp_audit CsimpAuditTest.specA_csimp

/-- info: csimp audit: 1 theorems, 0 reported -/
#guard_msgs in
#csimp_audit CsimpAuditTest.specC_csimp

/--
warning: csimp theorem `CsimpAuditTest.specD_csimp` (`CsimpAuditTest.specD` compiled as `CsimpAuditTest.implD`) depends on [CsimpAuditTest.testAxiom], outside [propext, Classical.choice, Quot.sound]
---
info: csimp audit: 1 theorems, 1 reported
-/
#guard_msgs in
#csimp_audit CsimpAuditTest.specD_csimp

/--
error: csimp theorem `CsimpAuditTest.specB_csimp` (`CsimpAuditTest.specB` compiled as `CsimpAuditTest.implB`) depends on [sorryAx]; its replacement runs in compiled code without a proof
---
info: csimp audit: 1 theorems, 1 reported
-/
#guard_msgs in
#csimp_audit CsimpAuditTest.specB_csimp

/--
error: csimp theorem `CsimpAuditTest.specB_csimp` (`CsimpAuditTest.specB` compiled as `CsimpAuditTest.implB`) depends on [sorryAx]; its replacement runs in compiled code without a proof
---
warning: csimp theorem `CsimpAuditTest.specD_csimp` (`CsimpAuditTest.specD` compiled as `CsimpAuditTest.implD`) depends on [CsimpAuditTest.testAxiom], outside [propext, Classical.choice, Quot.sound]
---
info: csimp audit: 4 theorems, 2 reported
-/
#guard_msgs in
#csimp_audit CsimpAuditTest

/-- error: no csimp theorem is named `CsimpAuditTest.implA` or lies in that namespace -/
#guard_msgs in
#csimp_audit CsimpAuditTest.implA

end CsimpAuditTest

end
