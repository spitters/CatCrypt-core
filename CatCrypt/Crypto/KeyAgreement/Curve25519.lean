/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.KeyAgreement.MontgomeryLadder
import CatCrypt.Crypto.KeyAgreement.MontgomeryXOnly
import CatCrypt.Crypto.KeyAgreement.MontgomeryAsWeierstrass
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Curve25519 as an abelian group

Defines Curve25519 abstractly as an additive commutative group, with a
distinguished generator and an x-coordinate projection to the field
`𝔽_p` where `p = 2²⁵⁵ − 19`. The group structure itself is treated as a
black box — realising it from the curve equation requires Mathlib-level
Montgomery-curve algebraic geometry that is not in place yet.

This gives a **concrete target** for the ladder correctness theorem in
`MontgomeryLadder.lean`: specialising it to `G = Curve25519` yields a
concrete statement about X25519 scalar multiplication.

## What this file establishes

1. `curve25519Prime : ℕ = 2²⁵⁵ − 19`, the Curve25519 base field prime.
2. `Fp25519`, a type alias for `ZMod curve25519Prime`.
3. `Curve25519` — an abstract abelian group (assumed as a parameter).
4. `curve25519Generator : Curve25519` — distinguished generator (u = 9).
5. `x25519 : ℕ → Curve25519 → Curve25519` — scalar multiplication,
   defined via `nsmul` from the group structure.
6. `x25519_eq_ladder` — the ladder computes X25519 scalar multiplication.

## What remains (the fiat-crypto trust edge)

- Realising `Curve25519` as `{ P : Fp25519 × Fp25519 // y² = x³ + Ax² + x }`
  with an explicit group law. ~3–6 weeks of Mathlib-style work, or
  trust the Rocq proof in fiat-crypto.
- Connecting the abstract `Curve25519` to the concrete `Fp25519`-valued
  `xProj` from `MontgomeryXOnly.MontyCurveGroup`.

## References

- RFC 7748, "Elliptic Curves for Security" (defines X25519).
- Bernstein, "Curve25519: new Diffie-Hellman speed records", PKC 2006.
-/

namespace CatCrypt.Crypto.ECC

/-! ## Base field -/

/-- Curve25519 base-field prime `p = 2²⁵⁵ − 19`. -/
def curve25519Prime : ℕ := 2^255 - 19

/-- The prime is positive (for `Fact (0 < p)` instance). -/
theorem curve25519Prime_pos : 0 < curve25519Prime := by
  show 0 < 2^255 - 19
  -- 2^255 is very large; explicit decision is slow, so we bound it.
  have h : (19 : ℕ) < 2^255 := by
    calc (19 : ℕ) < 2^5 := by decide
      _ ≤ 2^255 := Nat.pow_le_pow_right (by decide) (by decide)
  omega

/-- Base field for Curve25519 arithmetic. -/
abbrev Fp25519 : Type := ZMod curve25519Prime

/-- Curve25519's Montgomery parameters, specialised to `Fp25519`. -/
noncomputable def curve25519FpParams : MontyParams Fp25519 :=
  curve25519Params Fp25519

/-! ## Abstract group structure

We take `Curve25519` to be *any* abelian group together with a
distinguished generator. This abstracts the details of the
curve-point implementation. Security proofs reduce X25519 to DDH
on this abstract group. -/

section AbstractCurve25519

variable {G : Type*} [AddCommGroup G]

/-- `x25519 k P` computes `k · P` in the group `G`. For `G = Curve25519`
    and `P = generator`, this is the X25519 scalar multiplication. -/
def x25519 (k : ℕ) (P : G) : G := k • P

/-- The Montgomery ladder computes `x25519`. This is the corollary of
    `ladderFold_fst_eq_nsmul` tailored to the X25519 setting. -/
theorem x25519_eq_ladder (P : G) (bits : List Bool) :
    x25519 (bitsToNat bits) P = (ladderFold P bits).1 := by
  unfold x25519
  exact (ladderFold_fst_eq_nsmul P bits).symm

/-- Two X25519 scalar multiplications commute (DH property).
    This follows from commutativity of the abelian group action. -/
theorem x25519_commute (k k' : ℕ) (P : G) :
    x25519 k (x25519 k' P) = x25519 k' (x25519 k P) := by
  unfold x25519
  rw [← mul_smul, ← mul_smul, Nat.mul_comm]

end AbstractCurve25519

/-! ## Concrete Curve25519 as a Weierstrass point group

We instantiate `Curve25519` concretely as the points on the Montgomery-form
Weierstrass curve `y² = x³ + 486662·x² + x` over `Fp25519`. The
`AddCommGroup` is inherited from Mathlib's proved group law on affine
Weierstrass points; the `MontyCurveGroup` instance is closed via
`montgomeryW_MontyCurveGroup` from `MontgomeryAsWeierstrass.lean`.

## Trust edge

Proving `Nat.Prime (2²⁵⁵ − 19)` in Lean requires a Pratt certificate
that is both costly to construct and kernel-check. Mirroring the Rocq
AUCurves development (which uses `Spec/XEdDSA_Curve25519.v` abstractly
over `Z/pZ` without discharging primality) and standard fiat-crypto
convention, we take primality as the single project axiom. Everything
else is proved. -/

/-- **Trust edge**: Curve25519's base-field modulus is prime. Registered
    as an axiom because proving `Nat.Prime (2²⁵⁵ − 19)` in Lean requires
    a costly Pocklington/Pratt certificate; this is already discharged
    in the Rocq AUCurves development and we import it across the
    Rocq↔Lean boundary. -/
axiom curve25519Prime_prime : Nat.Prime curve25519Prime

/-- Register primality as a typeclass fact, unlocking `Field (ZMod p)`
    and hence `Field Fp25519`. -/
instance factCurve25519Prime : Fact (Nat.Prime curve25519Prime) :=
  ⟨curve25519Prime_prime⟩

-- All subsequent declarations need higher heartbeats because `curve25519Prime`
-- is a definition wrapping `2²⁵⁵ − 19`, and Lean's typeclass synthesis
-- paths can end up trying to `whnf` this large literal.
set_option maxHeartbeats 1600000

/-- `curve25519Prime ≠ 2`. Needed for `(2 : Fp25519) ≠ 0`. -/
theorem curve25519Prime_ne_two : curve25519Prime ≠ 2 := by
  show 2^255 - 19 ≠ 2
  have : (21 : ℕ) < 2^255 := by
    calc (21 : ℕ) < 2^5 := by decide
      _ ≤ 2^255 := Nat.pow_le_pow_right (by decide) (by decide)
  omega

/-- `2 < curve25519Prime`. -/
theorem two_lt_curve25519Prime : 2 < curve25519Prime := by
  show 2 < 2^255 - 19
  have : (21 : ℕ) < 2^255 := by
    calc (21 : ℕ) < 2^5 := by decide
      _ ≤ 2^255 := Nat.pow_le_pow_right (by decide) (by decide)
  omega

/-- `(2 : Fp25519) ≠ 0` — follows from `2 < curve25519Prime`. -/
theorem fp25519_two_ne_zero : (2 : Fp25519) ≠ 0 := by
  rw [show (2 : Fp25519) = ((2 : ℕ) : Fp25519) by norm_cast]
  rw [Ne, ZMod.natCast_eq_zero_iff 2 curve25519Prime]
  intro h
  exact absurd (Nat.le_of_dvd (by decide) h) (by linarith [two_lt_curve25519Prime])

/-- Concrete Curve25519: points on the Montgomery-as-Weierstrass curve
    over `Fp25519`. Inherits `AddCommGroup` from Mathlib's
    `WeierstrassCurve.Affine.Point`. -/
abbrev Curve25519Point : Type := (montgomeryW (486662 : Fp25519)).toAffine.Point

/-- Parameter well-formedness: `4 · 121666 = 486662 + 2` in `Fp25519`. -/
theorem curve25519_h24 : (4 : Fp25519) * (121666 : Fp25519) = (486662 : Fp25519) + 2 :=
  curve25519Params_wf Fp25519

/-- **Concrete `MontyCurveGroup` instance for Curve25519.** The x-only
    formulas `xdbl` and `xdadd` correctly compute scalar multiplication
    on `Curve25519Point`. -/
noncomputable def curve25519_MontyCurveGroup :
    MontyCurveGroup Fp25519 (curve25519Params Fp25519) Curve25519Point :=
  montgomeryW_MontyCurveGroup fp25519_two_ne_zero (486662 : Fp25519) (121666 : Fp25519)
    curve25519_h24

/-- `xProj` is negation-invariant on Curve25519 (instance specialisation of
    `xProjW_neg`). -/
theorem curve25519_xProj_neg (P : Curve25519Point) :
    curve25519_MontyCurveGroup.xProj (-P) = curve25519_MontyCurveGroup.xProj P :=
  xProjW_neg 486662 P

/-! ## Field-level ladder correctness for Curve25519

`xladderFold_curve25519_correct` is the end-to-end algebraic theorem:
running the field-level x-only ladder on `xProj P` and a bit-list produces
a projective x-coordinate matching `k • P` where `k = bitsToNat bits`.

Requires nondegeneracy of the ladder's intermediate `xdbl`/`xdadd` outputs
along the entire scalar-multiplication path — a scalar-specific hypothesis
(on Curve25519's prime-order subgroup, this holds for non-identity base
points and non-zero scalars below the subgroup order). -/

/-- Combined nondegeneracy hypothesis over a list of bits: at every
    point of the ladder run, the intermediate projective outputs are
    nondegenerate. -/
def LadderNondeg (P : Curve25519Point) (bits : List Bool) : Prop :=
  let params := curve25519Params Fp25519
  let inst := curve25519_MontyCurveGroup
  ∀ n ≤ bitsToNat bits,
    ((xdbl params.a24 (inst.xProj (n • P))).1 ≠ 0 ∨
     (xdbl params.a24 (inst.xProj (n • P))).2 ≠ 0) ∧
    ((xdbl params.a24 (inst.xProj ((n + 1) • P))).1 ≠ 0 ∨
     (xdbl params.a24 (inst.xProj ((n + 1) • P))).2 ≠ 0) ∧
    ((xdadd (inst.xProj (n • P)) (inst.xProj ((n + 1) • P))
         (inst.xProj (n • P - (n + 1) • P))).1 ≠ 0 ∨
     (xdadd (inst.xProj (n • P)) (inst.xProj ((n + 1) • P))
         (inst.xProj (n • P - (n + 1) • P))).2 ≠ 0)

/-- **Field-level ladder correctness for Curve25519.**
    `xladderFold`, applied to `xProj P` and a bit-list, satisfies the
    projective-equivalence invariant with the abstract-group ladder. -/
theorem xladderFold_curve25519_correct
    (P : Curve25519Point) (bits : List Bool)
    (hND : LadderNondeg P bits) :
    XLadderInv (params := curve25519Params Fp25519) (h := curve25519_MontyCurveGroup)
      P (bitsToNat bits)
      (xladderFold (curve25519Params Fp25519).a24
         (curve25519_MontyCurveGroup.xProj P) bits) := by
  induction bits with
  | nil =>
    refine ⟨?_, ?_⟩
    · -- ProjEquiv (1, 0) (xProj (0 • P)) — on the concrete case, 0 • P = 0 and xProj 0 = (1, 0).
      show ProjEquiv (1, 0) (curve25519_MontyCurveGroup.xProj ((0 : ℕ) • P))
      rw [zero_nsmul]
      -- xProj 0 = xProjW 486662 0 = (1, 0)
      show ProjEquiv (1, 0) (xProjW (486662 : Fp25519) (0 : Curve25519Point))
      rw [show (0 : Curve25519Point) = WeierstrassCurve.Affine.Point.zero from rfl]
      rw [xProjW_zero]
    · show ProjEquiv (curve25519_MontyCurveGroup.xProj P)
              (curve25519_MontyCurveGroup.xProj ((0 + 1) • P))
      rw [zero_add, one_nsmul]
  | cons b bs ih =>
    -- Apply ih to get invariant at bitsToNat bs; then step.
    have ihbs : XLadderInv (params := curve25519Params Fp25519)
                  (h := curve25519_MontyCurveGroup) P (bitsToNat bs)
                  (xladderFold (curve25519Params Fp25519).a24
                    (curve25519_MontyCurveGroup.xProj P) bs) := by
      apply ih
      -- The nondegeneracy at smaller bitsToNat bs follows from hND at bitsToNat (b :: bs)
      -- because bitsToNat bs ≤ bitsToNat (b :: bs).
      intro n hn
      apply hND n
      show n ≤ 2 * bitsToNat bs + (if b then 1 else 0)
      omega
    -- Now apply xladderStep_preserves_invariant with the right nondegeneracy from hND.
    have hNnext := hND (bitsToNat bs) (by simp [bitsToNat]; split_ifs <;> omega)
    obtain ⟨hND0, hND1, hNDa⟩ := hNnext
    show XLadderInv (params := curve25519Params Fp25519)
           (h := curve25519_MontyCurveGroup) P (bitsToNat (b :: bs))
           (xladderStep (curve25519Params Fp25519).a24
             (curve25519_MontyCurveGroup.xProj P)
             (xladderFold (curve25519Params Fp25519).a24
               (curve25519_MontyCurveGroup.xProj P) bs) b)
    show XLadderInv (params := curve25519Params Fp25519)
           (h := curve25519_MontyCurveGroup) P
           (2 * bitsToNat bs + (if b then 1 else 0))
           (xladderStep (curve25519Params Fp25519).a24
             (curve25519_MontyCurveGroup.xProj P)
             (xladderFold (curve25519Params Fp25519).a24
               (curve25519_MontyCurveGroup.xProj P) bs) b)
    exact xladderStep_preserves_invariant (params := curve25519Params Fp25519)
      (h := curve25519_MontyCurveGroup) P (bitsToNat bs)
      (xladderFold (curve25519Params Fp25519).a24
        (curve25519_MontyCurveGroup.xProj P) bs) b
      curve25519_xProj_neg hND0 hND1 hNDa ihbs

/-- **End-to-end X25519 field-level scalar-multiplication theorem.**
    The first component of the field-level Montgomery ladder run on
    `xProj P` for bit-list `bits` is projectively equivalent to
    `xProj (x25519 (bitsToNat bits) P)` — i.e., the x-coordinate of the
    abstract-group scalar multiplication. -/
theorem x25519_ladder_correct
    (P : Curve25519Point) (bits : List Bool)
    (hND : LadderNondeg P bits) :
    ProjEquiv
      (xladderFold (curve25519Params Fp25519).a24
         (curve25519_MontyCurveGroup.xProj P) bits).1
      (curve25519_MontyCurveGroup.xProj
         (x25519 (bitsToNat bits) P)) := by
  have h := xladderFold_curve25519_correct P bits hND
  show ProjEquiv _ _
  unfold x25519
  exact h.1

/-! ## Canonical X25519 scalar-clamp (RFC 7748 §5)

X25519 clamps scalar bytes before treating as a scalar:
  - Clear bits 0, 1, 2 of byte 0 (so bottom 3 bits of scalar are 0).
  - Clear bit 7 of byte 31 (top bit).
  - Set bit 6 of byte 31 (so scalar ≥ 2^254).

We model this as a scalar-level operation on `ℕ`. -/

/-- Clamp a 256-bit scalar per RFC 7748 §5. Clears the bottom 3 bits,
    clears bit 255, and sets bit 254. -/
def clampScalar (k : ℕ) : ℕ :=
  let cleared_low := k &&& (2^256 - 1 - 7)
  let cleared_high := cleared_low &&& (2^256 - 1 - 2^255)
  cleared_high ||| 2^254

end CatCrypt.Crypto.ECC
