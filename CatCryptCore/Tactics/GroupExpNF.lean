/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Tactic.Ring
public meta import Mathlib.Tactic.Ring
public import CatCryptCore.Core.Code
public meta import CatCryptCore.Core.Code
public import CatCryptCore.Tactics.BindAlign
public meta import CatCryptCore.Tactics.BindAlign

/-!
# `group_exp_nf` — game equalities up to the algebra of group exponentiation

The tactic proves equalities of `SPComp` programs whose bind layers align one by one and
whose layers differ by the algebra of exponentiation in a group: `(g ^ a) ^ b` against
`g ^ (a * b)`, `g ^ a * g ^ b` against `g ^ (a + b)`, `(g ^ a)⁻¹` against `g ^ (-a)`, with
exponents bound earlier in the chain.

## Why the existing tactics stall on this class

* `bind_align` peels the matching layers by congruence and closes a leaf only by `rfl`. A
  leaf such as `D (g ^ a) ((g ^ a) ^ b) = D (g ^ a) (g ^ (a * b))` is an identity of the
  group and of the exponent ring, not a definitional equality, so it stays open.
* `catcrypt_grind`, `bind_vcgen` and `bind_swap_nf` do not unfold the definitions that
  hide the exponentiations (a game, a key generation, a Diffie–Hellman operation), and
  stall on the folded goal.
* `grind` instantiates an exponent law such as `(x ^ a) ^ b = x ^ (a * b)` by e-matching,
  but does not use an equality of the exponent ring (`a * (b * c) = c * a * b`) to merge
  the two powers by congruence; an equality of two powers whose exponents agree only as
  polynomials stays open. Over an exponent ring `ZMod p` with `p` a variable, its ring
  solver may produce a proof with `eq_false_of_decide` on a numeral equation
  (`decide (3 = 0)` in `ZMod p`) that the kernel cannot evaluate and rejects.

## The procedure

`group_exp_nf [r₁, …, rₙ]` runs:

1. *Unfolding.* `simp only` with the rules `rᵢ` and the monad laws `SPComp.monad_bind_eq`,
   `SPComp.monad_pure_eq`, `SPComp.bind_assoc`, `SPComp.pure_bind`: a rule that names a
   definition unfolds it, a theorem (possibly with `←`, possibly applied to hypotheses)
   rewrites by it.
2. *Normalisation of the group expressions* (`group_exp_norm [r₁, …, rₙ]`), on the whole
   goal, under the binders: `simp only` folds the group expressions into powers of their
   bases by the laws below and the rules `rᵢ`, then `ring_nf` brings every exponent to the
   normal form of commutative (semi)ring polynomials, and the two steps repeat until
   neither changes the goal.
3. *Alignment.* `bind_align` peels the bind layers (and the applications) that agree on
   both sides.
4. *Leaves.* Each remaining goal is normalised again by step 2; the procedure fails when a
   goal remains.

The built-in laws are, in a monoid with `ℕ` exponents, `(x ^ m) ^ n = x ^ (m * n)`,
`x ^ m * x ^ n = x ^ (m + n)` (also with `x` for `x ^ 1`, and under a left factor), and the
unit laws; in a group, `ℕ` exponents are cast to `ℤ` and `x⁻¹ = x ^ (-1)`, with the same
laws for `ℤ` exponents. Products are associated to the left. Another exponentiation (by
`ZMod q`, by the elements of a field) is handled by its laws given as rules, oriented to
fold: `pw (pw x a) b = pw x (a * b)`, `pw x a * pw x b = pw x (a + b)`,
`(pw x a)⁻¹ = pw x (-a)`; the definitions that compute an exponentiation of the goal (a
Diffie–Hellman operation through a discrete logarithm) are named among the rules, together
with the facts that evaluate them (such as `dlog (g ^ a) = a`).

## Decided fragment

Call a term of a group (or monoid) type a *single-base word* when it is built from one base
`x` by products, inverses, `1` and exponentiation by exponents that are polynomials over
atoms of a commutative (semi)ring (`ℕ`, `ℤ`, or the ring of an exponentiation whose fold
laws are given). Every single-base word normalises to `x ^ E` (or `x`, or `1`) with `E` in
`ring_nf` normal form, and two words over the same base are equal in every group exactly
when their exponents are equal polynomials. For the exponentiations given by rules the
fold of a product of powers covers two adjacent factors.

The procedure closes an equality of two `SPComp` programs when, after unfolding, the two
sides are bind chains with the same computations in the same order whose corresponding
positions are either syntactically equal after normalisation or single-base words over the
same base; it is complete for this fragment when the continuations (distinguishers,
adversaries) are abstract, since then the two sides are equal for all continuations exactly
when the arguments at each position are. Outside it the procedure fails:

* bindings in different orders (use `bind_swap_nf`);
* products of powers of several bases that must commute to cancel (`x ^ a * y * x ^ (-a)`);
  the procedure does not use commutativity of the group;
* exponent identities that hold only modulo the order of the group, when the
  exponentiation is not given by laws over `ZMod q` (`x ^ q = 1`).
-/

public section

namespace CatCrypt.Tactic.GroupExpNF

section Laws

variable {M : Type*} [Monoid M] {G : Type*} [Group G]

/-- Two powers of the same base under a left factor merge. -/
theorem mul_pow_mul_pow (a b : M) (m n : ℕ) : a * b ^ m * b ^ n = a * b ^ (m + n) := by
  rw [mul_assoc, ← pow_add]

/-- A power followed by its base, under a left factor, merges. -/
theorem mul_pow_mul_self (a b : M) (m : ℕ) : a * b ^ m * b = a * b ^ (m + 1) := by
  rw [mul_assoc, ← pow_succ]

/-- A base followed by its power, under a left factor, merges. -/
theorem mul_self_mul_pow (a b : M) (m : ℕ) : a * b * b ^ m = a * b ^ (1 + m) := by
  rw [mul_assoc, ← pow_succ', add_comm]

/-- A base twice, under a left factor, is its square. -/
theorem mul_self_mul_self (a b : M) : a * b * b = a * b ^ 2 := by
  rw [mul_assoc, ← sq]

/-- A natural power in a group is the integer power of the cast exponent. -/
theorem pow_eq_zpow_natCast (a : G) (n : ℕ) : a ^ n = a ^ (n : ℤ) :=
  (zpow_natCast a n).symm

/-- An inverse in a group is the power `-1`. -/
theorem inv_eq_zpow_neg_one (a : G) : a⁻¹ = a ^ (-1 : ℤ) :=
  (zpow_neg_one a).symm

/-- Integer powers of powers multiply their exponents. -/
theorem zpow_zpow (a : G) (m n : ℤ) : (a ^ m) ^ n = a ^ (m * n) :=
  (zpow_mul a m n).symm

/-- Two integer powers of the same base merge. -/
theorem zpow_mul_zpow (a : G) (m n : ℤ) : a ^ m * a ^ n = a ^ (m + n) :=
  (zpow_add a m n).symm

/-- A base followed by its integer power merges. -/
theorem self_mul_zpow (a : G) (n : ℤ) : a * a ^ n = a ^ (1 + n) :=
  (zpow_one_add a n).symm

/-- An integer power followed by its base merges. -/
theorem zpow_mul_self (a : G) (n : ℤ) : a ^ n * a = a ^ (n + 1) :=
  (zpow_add_one a n).symm

/-- Two integer powers of the same base under a left factor merge. -/
theorem mul_zpow_mul_zpow (a b : G) (m n : ℤ) : a * b ^ m * b ^ n = a * b ^ (m + n) := by
  rw [mul_assoc, ← zpow_add]

/-- An integer power followed by its base, under a left factor, merges. -/
theorem mul_zpow_mul_self (a b : G) (m : ℤ) : a * b ^ m * b = a * b ^ (m + 1) := by
  rw [mul_assoc, ← zpow_add_one]

/-- A base followed by its integer power, under a left factor, merges. -/
theorem mul_self_mul_zpow (a b : G) (m : ℤ) : a * b * b ^ m = a * b ^ (1 + m) := by
  rw [mul_assoc, ← zpow_one_add]

end Laws

end CatCrypt.Tactic.GroupExpNF

meta section

namespace CatCrypt.Tactic

open Lean Elab Tactic

/-- The built-in fold laws of `group_exp_norm`. -/
def groupExpNFLaws : MacroM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) := do
  return #[
    ← `(Lean.Parser.Tactic.simpLemma| ← pow_mul),
    ← `(Lean.Parser.Tactic.simpLemma| ← pow_add),
    ← `(Lean.Parser.Tactic.simpLemma| ← pow_succ),
    ← `(Lean.Parser.Tactic.simpLemma| ← pow_succ'),
    ← `(Lean.Parser.Tactic.simpLemma| ← sq),
    ← `(Lean.Parser.Tactic.simpLemma| pow_one),
    ← `(Lean.Parser.Tactic.simpLemma| pow_zero),
    ← `(Lean.Parser.Tactic.simpLemma| one_pow),
    ← `(Lean.Parser.Tactic.simpLemma| mul_one),
    ← `(Lean.Parser.Tactic.simpLemma| one_mul),
    ← `(Lean.Parser.Tactic.simpLemma| inv_one),
    ← `(Lean.Parser.Tactic.simpLemma| ← mul_assoc),
    ← `(Lean.Parser.Tactic.simpLemma| GroupExpNF.mul_pow_mul_pow),
    ← `(Lean.Parser.Tactic.simpLemma| GroupExpNF.mul_pow_mul_self),
    ← `(Lean.Parser.Tactic.simpLemma| GroupExpNF.mul_self_mul_pow),
    ← `(Lean.Parser.Tactic.simpLemma| GroupExpNF.mul_self_mul_self),
    ← `(Lean.Parser.Tactic.simpLemma| GroupExpNF.pow_eq_zpow_natCast),
    ← `(Lean.Parser.Tactic.simpLemma| GroupExpNF.inv_eq_zpow_neg_one),
    ← `(Lean.Parser.Tactic.simpLemma| GroupExpNF.zpow_zpow),
    ← `(Lean.Parser.Tactic.simpLemma| GroupExpNF.zpow_mul_zpow),
    ← `(Lean.Parser.Tactic.simpLemma| GroupExpNF.self_mul_zpow),
    ← `(Lean.Parser.Tactic.simpLemma| GroupExpNF.zpow_mul_self),
    ← `(Lean.Parser.Tactic.simpLemma| GroupExpNF.mul_zpow_mul_zpow),
    ← `(Lean.Parser.Tactic.simpLemma| GroupExpNF.mul_zpow_mul_self),
    ← `(Lean.Parser.Tactic.simpLemma| GroupExpNF.mul_self_mul_zpow),
    ← `(Lean.Parser.Tactic.simpLemma| zpow_zero),
    ← `(Lean.Parser.Tactic.simpLemma| zpow_one),
    ← `(Lean.Parser.Tactic.simpLemma| one_zpow),
    ← `(Lean.Parser.Tactic.simpLemma| Nat.cast_add),
    ← `(Lean.Parser.Tactic.simpLemma| Nat.cast_mul),
    ← `(Lean.Parser.Tactic.simpLemma| Nat.cast_one),
    ← `(Lean.Parser.Tactic.simpLemma| Nat.cast_zero),
    ← `(Lean.Parser.Tactic.simpLemma| Nat.cast_ofNat)]

/-- Normalise the group expressions of the goal: fold them into powers of their bases by the
built-in laws and the given rules (`simp only`), bring the exponents to `ring_nf` normal
form, and repeat until the goal no longer changes. Never fails. -/
syntax (name := groupExpNorm) "group_exp_norm" (" [" Lean.Parser.Tactic.simpLemma,* "]")? :
  tactic

macro_rules
  | `(tactic| group_exp_norm $[[$rs,*]]?) => do
    let rs : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := (rs.map (·.getElems)).getD #[]
    let ls := rs ++ (← groupExpNFLaws)
    `(tactic| repeat fail_if_no_progress
        ((simp -decide -failIfUnchanged only [$ls,*]) <;> ring_nf (ifUnchanged := .silent)))

/-- Prove an equality of `SPComp` programs whose bind layers align and whose layers differ
by the algebra of group exponentiation: unfold the rules `rᵢ` and the monad laws, normalise
the group expressions (`group_exp_norm`), peel the aligned layers (`bind_align`) and close
each leaf by normalising it again. Fails when a goal remains. See the module docstring for
the decided fragment. -/
syntax (name := groupExpNF) "group_exp_nf" (" [" Lean.Parser.Tactic.simpLemma,* "]")? :
  tactic

macro_rules
  | `(tactic| group_exp_nf $[[$rs,*]]?) => do
    let rs : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := (rs.map (·.getElems)).getD #[]
    let unfold := rs ++ #[
      ← `(Lean.Parser.Tactic.simpLemma| CatCrypt.Core.SPComp.monad_bind_eq),
      ← `(Lean.Parser.Tactic.simpLemma| CatCrypt.Core.SPComp.monad_pure_eq),
      ← `(Lean.Parser.Tactic.simpLemma| CatCrypt.Core.SPComp.bind_assoc),
      ← `(Lean.Parser.Tactic.simpLemma| CatCrypt.Core.SPComp.pure_bind)]
    `(tactic| (
        simp -decide -failIfUnchanged only [$unfold,*]
        group_exp_norm [$rs,*]
        bind_align
        all_goals group_exp_norm [$rs,*]
        all_goals fail "group_exp_nf: a leaf is not closed by the normal form of the group \
          expressions"))

end CatCrypt.Tactic
