/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Nat.Bits

/-!
# Montgomery Ladder Algebraic Correctness

Proves that the Montgomery double-and-add ladder, viewed as an iterated
group operation on an abstract abelian group `G`, computes `n · P` for
a scalar `n` processed bit-by-bit from MSB to LSB.

## Scope

This is the **algebraic** correctness of the ladder. It does not depend on:
- Any specific field (would specialise to `𝔽_{2²⁵⁵-19}` for Curve25519).
- Any specific curve (would specialise to Curve25519's Montgomery form).
- The x-only formulas (`dadd`, `xdbl`) — at this level we use the full
  group operation. The x-only ladder uses the same invariant; showing
  that the x-only formulas agree with the full group's x-coordinate is
  a separate algebraic lemma (a well-known 2-page argument, deferred).

## What is proved

For any abelian group `G`, any element `P : G`, and any natural number
`n` with `n.size` bits, starting from the state `(0 · P, 1 · P)` and
iterating the ladder step over the bits of `n` from MSB to LSB, the
final state `(R₀, R₁)` satisfies `R₀ = n · P` and `R₁ = (n + 1) · P`.

This is the **invariant-based** correctness argument: standard folklore
dating to Montgomery's 1987 paper, formalised here as a pure induction
on bit length.

## What is NOT proved (see `docs/jasmin-lean.md`)

- **Field-op correctness.** The x-only differential-addition formula
  `dadd(x₀, x₁, x_P) = x(R₀ + R₁)` when `x_P = x(R₁ - R₀)`: this is the
  algebraic identity that makes the x-only ladder work. Proving it
  requires the full Montgomery-form group law (a case analysis and
  polynomial identity over the base field). Fiat-crypto proves it in
  Rocq; porting ~3–4 weeks.
- **Connection to Jasmin sem.** Axiom-level trust edge; see
  `rustExecSoundInJasmin` and the plan doc.

## References

- Montgomery, "Speeding the Pollard and Elliptic Curve Methods of
  Factorization", Math. Comp. 1987.
- Bernstein, "Curve25519: new Diffie-Hellman speed records", PKC 2006.
- Costello & Smith, "Montgomery curves and the Montgomery ladder",
  IACR eprint 2017/212, §4.
-/

namespace CatCrypt.Crypto.ECC

open AddCommGroup

variable {G : Type*} [AddCommGroup G]

/-! ## Ladder step -/

/-- One step of the Montgomery ladder, operating on a pair of group
    elements. The state `(R₀, R₁)` is intended to maintain the invariant
    `R₀ = a · P`, `R₁ = (a + 1) · P` for some running `a`; a single step
    with bit `b` updates `a` to `2 a + (if b then 1 else 0)`. -/
def ladderStep (acc : G × G) (b : Bool) : G × G :=
  let (R₀, R₁) := acc
  -- Both branches: one element is doubled, the other is the sum.
  -- Which is which depends on the bit.
  if b then (R₀ + R₁, R₁ + R₁) else (R₀ + R₀, R₀ + R₁)

/-- Running the ladder on a list of bits (head = MSB processed first). -/
def ladderFold (P : G) : List Bool → G × G
  | []      => (0, P)
  | b :: bs => ladderStep (ladderFold P bs) b

/-! ## Key invariant -/

/-- The invariant predicate: `(R₀, R₁) = (a · P, (a + 1) · P)`. -/
def LadderInv (P : G) (a : ℕ) (st : G × G) : Prop :=
  st.1 = a • P ∧ st.2 = (a + 1) • P

/-- Initial state `(0, P)` satisfies the invariant with `a = 0`. -/
lemma ladderInv_init (P : G) : LadderInv P 0 (0, P) := by
  refine ⟨?_, ?_⟩
  · show (0 : G) = (0 : ℕ) • P; simp
  · show P = (0 + 1 : ℕ) • P
    simp [one_nsmul]

/-- Core step lemma: if `(R₀, R₁)` satisfies the invariant at scalar `a`,
    then `ladderStep (R₀, R₁) b` satisfies the invariant at scalar
    `2 a + (if b then 1 else 0)`. -/
lemma ladderStep_inv (P : G) (a : ℕ) (st : G × G) (b : Bool)
    (h : LadderInv P a st) :
    LadderInv P (2 * a + (if b then 1 else 0)) (ladderStep st b) := by
  obtain ⟨h₀, h₁⟩ := h
  -- Unpack the pair so `st.1`, `st.2` reduce.
  have hR₀ : st.1 = a • P := h₀
  have hR₁ : st.2 = (a + 1) • P := h₁
  -- Unfold ladderStep + the if-branch explicitly based on b.
  simp only [LadderInv, ladderStep]
  cases b
  · -- b = false: ladderStep st false = (st.1 + st.1, st.1 + st.2)
    refine ⟨?_, ?_⟩
    · -- (st.1 + st.1) = (2 * a + 0) • P
      show st.1 + st.1 = _
      rw [hR₀, ← add_nsmul]
      congr 1; simp; omega
    · -- (st.1 + st.2) = ((2 * a + 0) + 1) • P
      show st.1 + st.2 = _
      rw [hR₀, hR₁, ← add_nsmul]
      congr 1; simp; omega
  · -- b = true: ladderStep st true = (st.1 + st.2, st.2 + st.2)
    refine ⟨?_, ?_⟩
    · -- (st.1 + st.2) = (2 * a + 1) • P
      show st.1 + st.2 = _
      rw [hR₀, hR₁, ← add_nsmul]
      congr 1; simp; omega
    · -- (st.2 + st.2) = ((2 * a + 1) + 1) • P
      show st.2 + st.2 = _
      rw [hR₁, ← add_nsmul]
      congr 1; simp; omega

/-! ## Scalar reconstruction from bits -/

/-- Compute the natural number represented by a list of bits, MSB first.
    `bitsToNat [b₂, b₁, b₀] = 4 b₂ + 2 b₁ + b₀` etc. -/
def bitsToNat : List Bool → ℕ
  | []      => 0
  | b :: bs => 2 * bitsToNat bs + (if b then 1 else 0)

/-! ## Main correctness theorem -/

/-- **Montgomery ladder correctness (algebraic).**
    Running `ladderFold P` on a list of bits (MSB first) produces a state
    `(n · P, (n + 1) · P)` where `n = bitsToNat bits`. -/
theorem ladderFold_correct (P : G) (bits : List Bool) :
    LadderInv P (bitsToNat bits) (ladderFold P bits) := by
  induction bits with
  | nil =>
    show LadderInv P 0 (0, P)
    exact ladderInv_init P
  | cons b bs ih =>
    show LadderInv P (bitsToNat (b :: bs)) (ladderFold P (b :: bs))
    simp only [bitsToNat, ladderFold]
    exact ladderStep_inv P (bitsToNat bs) (ladderFold P bs) b ih

/-- **Corollary — scalar multiplication via ladder.**
    The first component of `ladderFold P bits` equals
    `(bitsToNat bits) • P`. This is what the Montgomery ladder is
    supposed to compute. -/
theorem ladderFold_fst_eq_nsmul (P : G) (bits : List Bool) :
    (ladderFold P bits).1 = (bitsToNat bits) • P :=
  (ladderFold_correct P bits).1

end CatCrypt.Crypto.ECC
