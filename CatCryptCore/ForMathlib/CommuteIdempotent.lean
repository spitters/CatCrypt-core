/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Tactic.Module
public import Mathlib.Analysis.Complex.Basic

/-!
# Commuting idempotents in a complex algebra

For commuting idempotents `p`, `q` of a `ℂ`-algebra, the element `a = p + 2 q` satisfies the
polynomial identity `3 p = 10 a - 9 a² + 2 a³`, by expanding with `p² = p`, `q² = q` and
`p q = q p`.

## Main results

* `three_smul_eq_of_commute_idem` — `3 p = 10 a - 9 a² + 2 a³` for `a = p + 2 q`.

Search words: commuting idempotents, commuting projections, polynomial in a sum of projections,
simultaneous diagonalisation.
-/

@[expose] public section

set_option autoImplicit false

/-- For commuting idempotents `p`, `q` of a `ℂ`-algebra and `a = p + 2 q`,
`3 p = 10 a - 9 a² + 2 a³`. -/
theorem three_smul_eq_of_commute_idem {R : Type*} [Ring R] [Algebra ℂ R] {p q : R}
    (hp : p * p = p) (hq : q * q = q) (hpq : Commute p q) :
    (3 : ℂ) • p = ((10 : ℂ) • (p + (2 : ℂ) • q))
      - ((9 : ℂ) • ((p + (2 : ℂ) • q) * (p + (2 : ℂ) • q)))
      + ((2 : ℂ) • ((p + (2 : ℂ) • q) * (p + (2 : ℂ) • q) * (p + (2 : ℂ) • q))) := by
  have hqp : q * p = p * q := hpq.eq.symm
  have h3 : p * q * p = p * q := by rw [mul_assoc, hqp, ← mul_assoc, hp]
  have h4 : p * q * q = p * q := by rw [mul_assoc, hq]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hp, hq, hqp, h3, h4]
  module
