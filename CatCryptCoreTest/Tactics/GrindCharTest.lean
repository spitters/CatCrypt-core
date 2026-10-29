/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import Mathlib.Data.ZMod.Basic
import CatCryptCore.Tactics.GrindChar

/-!
# Tests of `grind_char_numeral`

Each field below is `ZMod q` for a named modulus `q`: a `def`, a `def` marked
`@[irreducible]`, a power expression and an `irreducible_def`. A `grind` goal that needs
reduction modulo `q` fails before `grind_char_numeral` and closes after it.
-/

set_option autoImplicit false

namespace CatCrypt.Tactic.GrindCharTest

/-- The BabyBear prime as a named constant. -/
def babyP : ℕ := 2013265921

/-- `ZMod babyP`. -/
abbrev BB := ZMod babyP

/-- The BabyBear prime as an `irreducible_def`. -/
irreducible_def irrP : ℕ := 2 ^ 31 - 2 ^ 27 + 1

/-- `ZMod irrP`. -/
abbrev IB := ZMod irrP

/-- The prime `2 ^ 255 - 19` as a named constant. -/
def bigP : ℕ := 2 ^ 255 - 19

/-- `ZMod bigP`. -/
abbrev F25519 := ZMod bigP

/-- The ML-KEM modulus as an irreducible `def`. -/
@[irreducible] def kyberQ : ℕ := 3329

/-- `ZMod kyberQ`. -/
abbrev KQ := ZMod kyberQ

example : True := by
  fail_if_success (have : (2013265921 : BB) = 0 := by grind)
  trivial

example : True := by
  fail_if_success (have : ∀ x : IB, x * 2013265922 = x := by grind)
  trivial

grind_char_numeral BB

/-- error: grind_char_numeral: the characteristic irrP is not a numeral; add `using` h -/
#guard_msgs in
grind_char_numeral IB

grind_char_numeral IB using irrP_def

grind_char_numeral F25519

grind_char_numeral KQ

example : (2013265921 : BB) = 0 := by grind

example (x : BB) : x * 2013265922 = x := by grind

example (x y : BB) (h : x = y + 1) : x * 2013265920 = -y - 1 := by grind

example : (2013265921 : IB) = 0 := by grind

example (x : IB) : x * 2013265922 = x := by grind

example (x : F25519) : x * (2 ^ 255 - 18) = x := by grind

example (x : KQ) : x * 3330 = x := by grind

end CatCrypt.Tactic.GrindCharTest
