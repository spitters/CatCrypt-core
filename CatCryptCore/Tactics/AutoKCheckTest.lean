/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoDispatchCore
public meta import CatCryptCore.Tactics.AutoDispatchCore
public import Mathlib.Algebra.Field.ZMod

/-!
# Tests for the kernel check of the arms of `catcrypt_auto`

A goal on which `grind +suggestions` closes the goal in the elaborator with a proof term
that the kernel rejects (`eq_false_of_decide (eagerReduce _)` at a numeral equation in
`ZMod 2`, the failure of `ka_real_eq` in Examples/DiffieHellman.lean and of
`elgamal_real₀_eq`, `elgamal_real₁_eq` in Examples/ElGamal.lean): the dispatcher rejects
that arm and closes the goal by the next one. The arms of the shape `other` of
`CatCryptCore.Tactics.AutoBase` and the goals of `CatCryptCore.Tactics.AutoDispatchTest`
over them follow.
-/

set_option autoImplicit false

namespace CatCrypt.Tactics.AutoKCheckTest

/-- A proposition that `grind` does not unfold. -/
public def Good (n : Nat) : Prop := n = n

/-- An equation of natural numbers that `grind` does not unfold. -/
public def Bad (a b : Nat) : Prop := a = b

public section

catcrypt_auto_shape "kernel check test" direct priority 200 :=
  app CatCrypt.Tactics.AutoKCheckTest.Good

catcrypt_auto_arm "kernel check test" order 10 := "grind +suggestions"
catcrypt_auto_arm "kernel check test" order 20 := "exact rfl"

catcrypt_auto_shape "kernel check only grind" direct priority 200 :=
  app CatCrypt.Tactics.AutoKCheckTest.Bad

catcrypt_auto_arm "kernel check only grind" order 10 := "grind +suggestions"

catcrypt_auto_arm "*" order 10 := "exact %TERM"
catcrypt_auto_arm "other" order 20 := "%SIMP_ALL"
catcrypt_auto_arm "other" order 30 := "grind%GRIND"
catcrypt_auto_arm "premises" order 10 := "solve_by_elim%PREMISES"

end

/-! ## The kernel check -/

-- `grind +suggestions` closes the goal with a term the kernel rejects; the dispatcher
-- suggests the next arm.
/--
info: Try this:
  [apply] exact rfl
-/
#guard_msgs (substring := true) in
example (x : ZMod 2) (_h : x = 2) : Good 3 := by
  catcrypt_auto?

-- With no other arm, the false goal `Bad 0 1` stays open and the failure reports the
-- kernel's rejection.
/--
on the goal as stated: goal shape kernel check only grind; every arm failed:
  grind +suggestions: the kernel rejects the proof term
-/
#guard_msgs (substring := true) in
example (x : ZMod 2) (_h : x = 2) : Bad 0 1 := by
  catcrypt_auto?

/-! ## Goals of `CatCryptCore.Tactics.AutoDispatchTest` over the arms of `other` -/

/-- A goal of no registered shape. -/
example (n : ℕ) (h : n = 3) : n + 1 = 4 := by
  catcrypt_auto

/-- `simp_all` rewrites `f n` to `f (n + 1)` without end and reaches the
recursion limit; the runtime exception is caught and `grind` closes the goal. -/
example (f : ℕ → ℕ) (_h : ∀ n, f n = f (n + 1)) (h₇ : f 0 = 7) : f 0 = 7 := by
  catcrypt_auto

-- The literal disequality of Examples/Cryptobox/PKEY.lean:472, without prefix.
/--
info: Try this:
  [apply] simp_all
-/
#guard_msgs (substring := true) in
example : (101 : ℕ) ≠ 103 := by
  catcrypt_auto?

end CatCrypt.Tactics.AutoKCheckTest
