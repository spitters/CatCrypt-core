/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Lean
public meta import CatCryptCore.Tactics.RepairAction

/-!
# Availability of the constants of a repair proof

Tests of the availability rule of the kernel check of `CatCryptCore.Tactics.RepairAction`
(`RepairAction.unavailableConst?`), over four fresh theorems of this file: `availEarly`,
a lemma with an unproved body `availUnproved`, the enclosing declaration `availEnclosing`, and
`availLate`, declared in that order.

* With `availEnclosing` as the enclosing declaration, a proof citing `availEarly` is accepted,
  and proofs citing `availEnclosing`, `availLate` or `availUnproved` are rejected.
* With an enclosing declaration that has no range, the bound is the position of the leaf: at
  the start of `availEnclosing`, `availEarly` is accepted and `availLate` is rejected.
* `kernelCheck` gives the reason `uses availLate, not available here`, and the arm
  `exact availLate` (`runArm`) fails with that reason, final.
-/

set_option autoImplicit false

namespace CatCryptCore.RepairActionAvailTest

/-- A theorem declared before `availEnclosing`. -/
theorem availEarly : True := trivial

#guard_msgs (drop warning) in
/-- A lemma with an unproved body, declared before `availEnclosing`. -/
theorem availUnproved : True := by sorry

/-- The enclosing declaration of the leaves of the tests. -/
theorem availEnclosing : True := trivial

/-- A theorem declared after `availEnclosing`. -/
theorem availLate : True := trivial

open Lean Meta CatCryptCore.RepairAction

run_meta do
  let enc := ``availEnclosing
  let ty := mkConst ``True
  let expect (declName? : Option Name) (c : Name) (want : Option Name) : MetaM Unit := do
    let got ← unavailableConst? declName? ty (mkConst c)
    unless got == want do
      throwError "unavailableConst? {declName?} {c}: got {got}, expected {want}"
  expect (some enc) ``availEarly none
  expect (some enc) ``availEnclosing (some ``availEnclosing)
  expect (some enc) ``availLate (some ``availLate)
  expect (some enc) ``availUnproved (some ``availUnproved)
  -- an enclosing declaration with no range: the bound is the leaf, at `availEnclosing`
  let some rs ← findDeclarationRanges? enc | throwError "availEnclosing has no range"
  let b := (← getFileMap).ofPosition rs.range.pos
  let leaf : Syntax.Range := ⟨b, b⟩
  let noRange := enc ++ `noRange
  withLeafPos leaf do
    expect (some noRange) ``availEarly none
    expect (some noRange) ``availLate (some ``availLate)
  -- the kernel check and an arm
  let g := (← mkFreshExprMVar ty).mvarId!
  let m ← kernelCheck g (mkConst ``availLate) 100000 (some enc)
  unless m == some (unavailableMsg ``availLate) do
    throwError "kernelCheck: got {m}"
  let r ← runArm g "exact availLate" "exact" 100000 2000 (some enc)
  unless !r.closed && r.final && isUnavailableMsg r.msg do
    throwError "runArm: closed {r.closed}, final {r.final}, {r.msg}"

end CatCryptCore.RepairActionAvailTest
