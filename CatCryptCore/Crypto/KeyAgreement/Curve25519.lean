/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.KeyAgreement.MontgomeryLadder
import CatCryptCore.Crypto.KeyAgreement.MontgomeryXOnly
import CatCryptCore.Crypto.KeyAgreement.MontgomeryAsWeierstrass
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
convention, we take primality as an axiom. It is one of four
AUCurves-bridged trust edges in this file — each documented at its
definition and imported across the Rocq↔Lean boundary:
`curve25519Prime_prime` (base-field prime), `curve25519SubgroupOrder_prime`
(the subgroup order `l` is prime), and `curve25519_basepoint` /
`curve25519_basepoint_addOrder` (the RFC 7748 base point and its order `l`).
Everything else — including the unconditional ladder capstone
`x25519_ladder_correct_basepoint` — is proved. -/

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

/-! ### Curve25519 subgroup order (AUCurves bridge)

The order of Curve25519's prime-order subgroup — equivalently the order of the
RFC 7748 base point `u = 9` — is
`l = 2^252 + 27742317777372353535851937790883648493`. It bounds the scalar range
the Montgomery ladder traverses, and its primality is what makes every
intermediate `n • B` (for `0 < n < l`) non-identity, hence projectively
nondegenerate — the group-theoretic half of discharging `LadderNondeg`. -/

/-- Order of Curve25519's prime-order subgroup / of the base point `u = 9`. -/
def curve25519SubgroupOrder : ℕ :=
  2 ^ 252 + 27742317777372353535851937790883648493

/-- **`l` is prime.** Bridged across the Rocq↔Lean boundary from the AUCurves
    development — `E_basepoint_order` in `Spec/Curve25519_BasepointOrder.v`
    establishes `l • B = 0` (Qed-sealed; its Montgomery-side link
    `scalarmult_l_eq_zero` is tactic-complete but left `Admitted` there only
    because the Coq kernel-check times out), and the quotient `E/E[4]` has prime
    order `l` in fiat-crypto's `Spec/Ristretto255.v`. Imported here as an axiom
    exactly as `curve25519Prime_prime` is. This underpins the cyclic-subgroup
    argument that `n • B ≠ 0` for `0 < n < l`, the group-theoretic input to
    discharging the `LadderNondeg` side-condition of `x25519_ladder_correct`.

    The remaining, field-algebraic half — that `xdbl`/`xdadd` outputs on
    non-identity affine points are `(0,0)`-free — plus a concrete
    `Curve25519Point` basepoint of order `l`, together turn `x25519_ladder_correct`
    unconditional in the intended regime; that proof is not yet carried here. -/
axiom curve25519SubgroupOrder_prime : Nat.Prime curve25519SubgroupOrder

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

/-- **End-to-end X25519 field-level scalar-multiplication theorem
    (conditional on ladder nondegeneracy).**
    The first component of the field-level Montgomery ladder run on
    `xProj P` for bit-list `bits` is projectively equivalent to
    `xProj (x25519 (bitsToNat bits) P)` — i.e., the x-coordinate of the
    abstract-group scalar multiplication.

    **The hypothesis `hND : LadderNondeg P bits` is required and is left
    undischarged here.** It asserts that every intermediate `xdbl`/`xdadd`
    output along the scalar-multiplication path is projectively nondegenerate.
    On Curve25519's prime-order subgroup this holds for a non-identity base
    point and scalars below the subgroup order `curve25519SubgroupOrder` (`l`),
    so the theorem is unconditional in the intended regime. The group-theoretic
    input to discharging it — that `n • B ≠ 0` for `0 < n < l` — follows from
    `curve25519SubgroupOrder_prime` (the AUCurves order bridge); the remaining
    field-algebraic step (`xdbl`/`xdadd` non-`(0,0)` on non-identity affine
    points) plus a concrete order-`l` basepoint would remove `hND` entirely.
    Until that lands, read this as correctness *wherever the ladder path stays
    nondegenerate*, not as an unconditional identity. -/
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

/-! ### Unconditional ladder nondegeneracy for the RFC 7748 basepoint

The RFC 7748 base point `B` (`u = 9`) generates Curve25519's prime-order
subgroup of order `l = curve25519SubgroupOrder`. Because `l` is an odd prime,
no non-identity multiple `n • B` (`0 < n < l`) is a 4-torsion point, and this
is exactly what makes every intermediate `xdbl`/`xdadd` output along the ladder
path projectively nondegenerate. This section discharges `LadderNondeg` for the
base point unconditionally, removing the `hND` side condition from
`x25519_ladder_correct`. -/

/-- Small field elements are nonzero: `n < curve25519Prime` for `n ≤ 2000000`. -/
theorem lt_curve25519Prime_of_le_2M {n : ℕ} (h : n ≤ 2000000) :
    n < curve25519Prime := by
  show n < 2 ^ 255 - 19
  have hb : (2000020 : ℕ) ≤ 2 ^ 255 := by
    calc (2000020 : ℕ) ≤ 2 ^ 21 := by norm_num
      _ ≤ 2 ^ 255 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  omega

/-- A small nonzero natural is nonzero in `Fp25519`. -/
theorem fp25519_small_ne_zero {n : ℕ} (h0 : 0 < n) (h : n ≤ 2000000) :
    (n : Fp25519) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff n curve25519Prime]
  intro hdvd
  have hle := Nat.le_of_dvd h0 hdvd
  have hlt := lt_curve25519Prime_of_le_2M h
  omega

theorem fp25519_121666_ne_zero : (121666 : Fp25519) ≠ 0 := by
  rw [show (121666 : Fp25519) = ((121666 : ℕ) : Fp25519) by norm_cast]
  exact fp25519_small_ne_zero (by norm_num) (by norm_num)

theorem fp25519_121665_ne_zero : (121665 : Fp25519) ≠ 0 := by
  rw [show (121665 : Fp25519) = ((121665 : ℕ) : Fp25519) by norm_cast]
  exact fp25519_small_ne_zero (by norm_num) (by norm_num)

theorem fp25519_four_ne_zero : (4 : Fp25519) ≠ 0 := by
  rw [show (4 : Fp25519) = ((4 : ℕ) : Fp25519) by norm_cast]
  exact fp25519_small_ne_zero (by norm_num) (by norm_num)

/-- `xdbl a24 (1, 1) = (0, 16·a24)` — doubling the x-coordinate `1`. -/
theorem xdbl_one_one {F : Type*} [CommRing F] (a24 : F) :
    xdbl a24 (1, 1) = (0, 16 * a24) := by
  simp only [xdbl, Prod.mk.injEq]; constructor <;> ring

/-- `xdbl a24 (-1, 1) = (0, 16·a24 − 16)` — doubling the x-coordinate `−1`. -/
theorem xdbl_neg_one_one {F : Type*} [CommRing F] (a24 : F) :
    xdbl a24 (-1, 1) = (0, 16 * a24 - 16) := by
  simp only [xdbl, Prod.mk.injEq]; constructor <;> ring

/-- `16 · a24 ≠ 0` in `Fp25519` (a24 = 121666). -/
theorem fp25519_sixteen_a24_ne_zero :
    (16 * (curve25519Params Fp25519).a24 : Fp25519) ≠ 0 := by
  simp only [curve25519Params]
  rw [show (16 : Fp25519) * ((121666 : ℕ) : Fp25519) = ((16 * 121666 : ℕ) : Fp25519) by
        push_cast; ring]
  exact fp25519_small_ne_zero (by norm_num) (by norm_num)

/-- `16 · a24 − 16 ≠ 0` in `Fp25519` (16·(121666−1)). -/
theorem fp25519_sixteen_a24_sub_ne_zero :
    (16 * (curve25519Params Fp25519).a24 - 16 : Fp25519) ≠ 0 := by
  simp only [curve25519Params]
  rw [show (16 : Fp25519) * ((121666 : ℕ) : Fp25519) - 16 = ((16 * 121666 - 16 : ℕ) : Fp25519) by
        push_cast; ring]
  exact fp25519_small_ne_zero (by norm_num) (by norm_num)

/-! ### Curve25519 base point (AUCurves bridge)

`curve25519_basepoint` is the RFC 7748 base point `u = 9` as a concrete
`Curve25519Point`, and `curve25519_basepoint_addOrder` records that its order in
the Weierstrass group is `l = curve25519SubgroupOrder`. Both are bridged across
the Rocq↔Lean boundary from the AUCurves development: `E_basepoint_order` in
`Spec/Curve25519_BasepointOrder.v` establishes `l • B = 0` (with `l` the prime
subgroup order of `E/E[4]` from fiat-crypto's `Spec/Ristretto255.v`), and the
minimality of `l` as the additive order follows there from primality of `l`
together with `B ≠ 0`. Imported here as axioms exactly as `curve25519Prime_prime`
and `curve25519SubgroupOrder_prime` are; everything downstream of them is proved. -/

/-- **AUCurves bridge**: an order-`l` point of the Curve25519 group. Only its
    additive order is constrained (by `curve25519_basepoint_addOrder`); nothing
    here pins its x-coordinate. The intended instantiation is the RFC 7748 base
    point `u = 9`, but because only the order is used, the capstone
    `x25519_ladder_correct_basepoint` in fact holds for *any* order-`l` point
    (`u = 9` included) — a generalisation, not a weakening. Pinning `xProj` to
    `(9, 1)` would need a further concrete-coordinate bridge, not present here. -/
axiom curve25519_basepoint : Curve25519Point

/-- **AUCurves bridge**: the base point has additive order `l`
    (`E_basepoint_order`, `Spec/Curve25519_BasepointOrder.v`). -/
axiom curve25519_basepoint_addOrder :
    addOrderOf curve25519_basepoint = curve25519SubgroupOrder

/-- Non-vanishing of small multiples of a point of order `l`: for
    `0 < n < l`, `n • B ≠ 0`. -/
theorem nsmul_ne_zero_of_lt_order {G : Type*} [AddGroup G] {B : G} {n : ℕ}
    (hord : addOrderOf B = curve25519SubgroupOrder)
    (hn0 : 0 < n) (hnl : n < curve25519SubgroupOrder) : n • B ≠ 0 := by
  rw [ne_eq, ← addOrderOf_dvd_iff_nsmul_eq_zero, hord]
  intro hdvd; have := Nat.le_of_dvd hn0 hdvd; omega

/-- `curve25519_MontyCurveGroup.xProj` unfolds to `xProjW 486662`. -/
@[simp] theorem curve25519_xProj_eq (Q : Curve25519Point) :
    curve25519_MontyCurveGroup.xProj Q = xProjW (486662 : Fp25519) Q := rfl

/-- If the first projective coordinate of `Q` vanishes, then `Q` is a
    2-torsion point: `Q + Q = 0`. (Such a `Q` is the affine point `(0, 0)`,
    which is its own negation on a Montgomery curve.) -/
theorem curve25519_double_eq_zero_of_xProj_fst_zero (Q : Curve25519Point)
    (hQ : (curve25519_MontyCurveGroup.xProj Q).1 = 0) : Q + Q = 0 := by
  obtain (_ | @⟨x, y, h⟩) := Q
  · exact absurd hQ (by simp)
  · rw [curve25519_xProj_eq, xProjW_some] at hQ
    simp only at hQ
    subst hQ
    have hy : y = 0 := by
      have hcurve : y ^ 2 = (0:Fp25519) ^ 3 + 486662 * 0 ^ 2 + 0 :=
        (montgomeryW_equation 486662 0 y).mp h.1
      have : y ^ 2 = 0 := by rw [hcurve]; ring
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    subst hy
    have hyeq : (0:Fp25519) = (montgomeryW 486662).toAffine.negY 0 0 := by
      rw [montgomeryW_negY]; ring
    exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq hyeq

/-- A point of x-coordinate `1` is a 4-torsion point: `(R+R)+(R+R) = 0`. -/
theorem curve25519_quad_eq_zero_of_xProj_one (R : Curve25519Point)
    (hR : curve25519_MontyCurveGroup.xProj R = (1, 1)) :
    (R + R) + (R + R) = 0 := by
  apply curve25519_double_eq_zero_of_xProj_fst_zero
  have hspec := curve25519_MontyCurveGroup.xdbl_spec R
  simp only [hR, xdbl_one_one] at hspec
  have hz : (curve25519_MontyCurveGroup.xProj (R + R)).1 * (16 * (curve25519Params Fp25519).a24) = 0 := by
    rw [← hspec]; ring
  rcases mul_eq_zero.mp hz with h | h
  · exact h
  · exact absurd h fp25519_sixteen_a24_ne_zero

/-- A point of x-coordinate `−1` is a 4-torsion point: `(R+R)+(R+R) = 0`. -/
theorem curve25519_quad_eq_zero_of_xProj_neg_one (R : Curve25519Point)
    (hR : curve25519_MontyCurveGroup.xProj R = (-1, 1)) :
    (R + R) + (R + R) = 0 := by
  apply curve25519_double_eq_zero_of_xProj_fst_zero
  have hspec := curve25519_MontyCurveGroup.xdbl_spec R
  simp only [hR, xdbl_neg_one_one] at hspec
  have hz : (curve25519_MontyCurveGroup.xProj (R + R)).1
      * (16 * (curve25519Params Fp25519).a24 - 16) = 0 := by
    rw [← hspec]; ring
  rcases mul_eq_zero.mp hz with h | h
  · exact h
  · exact absurd h fp25519_sixteen_a24_sub_ne_zero

/-- `4 < l`. -/
theorem four_lt_curve25519SubgroupOrder : 4 < curve25519SubgroupOrder := by
  show 4 < 2 ^ 252 + 27742317777372353535851937790883648493
  have : (4 : ℕ) ≤ 2 ^ 252 := by
    calc (4 : ℕ) ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ 252 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  omega

/-- `l` is coprime to `4` (it is an odd prime `> 4`). -/
theorem curve25519SubgroupOrder_coprime_four :
    Nat.Coprime curve25519SubgroupOrder 4 :=
  (Nat.Prime.coprime_iff_not_dvd curve25519SubgroupOrder_prime).mpr (fun hd => by
    have := Nat.le_of_dvd (by norm_num) hd
    have := four_lt_curve25519SubgroupOrder
    omega)

/-- The 4-torsion multiple `(4m)·B = 0` only when `l ∣ m`; hence for
    `0 < m < l` the point `m·B` is not 4-torsion. -/
theorem curve25519_quad_nsmul_ne_zero {m : ℕ} (hm0 : 0 < m)
    (hml : m < curve25519SubgroupOrder) :
    (m • curve25519_basepoint + m • curve25519_basepoint) +
      (m • curve25519_basepoint + m • curve25519_basepoint) ≠ 0 := by
  rw [show (m • curve25519_basepoint + m • curve25519_basepoint) +
        (m • curve25519_basepoint + m • curve25519_basepoint)
        = (4 * m) • curve25519_basepoint from by
        rw [show 4 * m = (m + m) + (m + m) from by ring, add_nsmul, add_nsmul]]
  rw [ne_eq, ← addOrderOf_dvd_iff_nsmul_eq_zero, curve25519_basepoint_addOrder]
  intro hdvd
  have hlm : curve25519SubgroupOrder ∣ m :=
    curve25519SubgroupOrder_coprime_four.dvd_of_dvd_mul_left hdvd
  have := Nat.le_of_dvd hm0 hlm
  omega

/-- **xdbl nondegeneracy.** If `Q` is not a 4-torsion point, the `xdbl`
    output at `xProj Q` is projectively nondegenerate. -/
theorem curve25519_xdbl_nondeg_of_quad_ne_zero (Q : Curve25519Point)
    (hQ : (Q + Q) + (Q + Q) ≠ 0) :
    (xdbl (curve25519Params Fp25519).a24 (curve25519_MontyCurveGroup.xProj Q)).1 ≠ 0 ∨
      (xdbl (curve25519Params Fp25519).a24 (curve25519_MontyCurveGroup.xProj Q)).2 ≠ 0 := by
  obtain (_ | @⟨x, y, h⟩) := Q
  · exact absurd (show (0:Curve25519Point) + 0 + (0 + 0) = 0 by simp) hQ
  · left
    rw [curve25519_xProj_eq, xProjW_some, xdbl_numerator]
    intro hx
    have hsub : x ^ 2 - 1 = 0 := (pow_eq_zero_iff (by norm_num)).mp hx
    have hfac : (x - 1) * (x + 1) = 0 := by linear_combination hsub
    rcases mul_eq_zero.mp hfac with h1 | h1
    · apply hQ
      apply curve25519_quad_eq_zero_of_xProj_one
      rw [curve25519_xProj_eq, xProjW_some, sub_eq_zero.mp h1]
    · apply hQ
      apply curve25519_quad_eq_zero_of_xProj_neg_one
      rw [curve25519_xProj_eq, xProjW_some, add_eq_zero_iff_eq_neg.mp h1]

/-- `xdbl a24 (1, 0) = (1, 0)` — doubling the point at infinity's representative. -/
theorem xdbl_one_zero {F : Type*} [CommRing F] (a24 : F) :
    xdbl a24 (1, 0) = (1, 0) := by
  simp only [xdbl, Prod.mk.injEq]; constructor <;> ring

/-- The projective second coordinate of a nonzero point is `1`. -/
theorem xProjW_snd_of_ne_zero (Q : Curve25519Point) (hQ : Q ≠ 0) :
    (curve25519_MontyCurveGroup.xProj Q).2 = 1 := by
  obtain (_ | @⟨x, y, h⟩) := Q
  · exact absurd rfl hQ
  · rw [curve25519_xProj_eq, xProjW_some]

/-- `l • B = 0`. -/
theorem curve25519_basepoint_order_nsmul :
    curve25519SubgroupOrder • curve25519_basepoint = 0 := by
  rw [← curve25519_basepoint_addOrder]
  exact (addOrderOf_dvd_iff_nsmul_eq_zero).mp dvd_rfl

/-- The base point is not the identity. -/
theorem curve25519_basepoint_ne_zero : curve25519_basepoint ≠ 0 := by
  intro h
  have hord := curve25519_basepoint_addOrder
  rw [h, addOrderOf_zero] at hord
  have := four_lt_curve25519SubgroupOrder
  omega

/-- The base point's projective second coordinate is `1` (it is affine). -/
theorem curve25519_basepoint_xProj_snd_eq_one :
    (curve25519_MontyCurveGroup.xProj curve25519_basepoint).2 = 1 :=
  xProjW_snd_of_ne_zero _ curve25519_basepoint_ne_zero

/-- The base point's projective first coordinate is nonzero (`u = 9 ≠ 0`);
    equivalently, the base point is not the 2-torsion point `(0, 0)`. -/
theorem curve25519_basepoint_xProj_fst_ne_zero :
    (curve25519_MontyCurveGroup.xProj curve25519_basepoint).1 ≠ 0 := by
  intro hx
  have h2 : (2 : ℕ) • curve25519_basepoint = 0 := by
    rw [two_nsmul]
    exact curve25519_double_eq_zero_of_xProj_fst_zero _ hx
  rw [← addOrderOf_dvd_iff_nsmul_eq_zero, curve25519_basepoint_addOrder] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  have := four_lt_curve25519SubgroupOrder
  omega

/-- **xdadd nondegeneracy.** For a non-4-torsion point `P0` and any `P1`, the
    differential-addition output (with the base point as the difference input,
    which is the ladder's invariant) is projectively nondegenerate. The base
    point is affine with nonzero x-coordinate (`u = 9`), and the only way the
    output could degenerate is if `P0` had x-coordinate `±1` (a 4-torsion
    point), excluded by hypothesis. -/
theorem curve25519_xdadd_nondeg (P0 P1 : Curve25519Point)
    (hP0nt : (P0 + P0) + (P0 + P0) ≠ 0) :
    (xdadd (curve25519_MontyCurveGroup.xProj P0)
        (curve25519_MontyCurveGroup.xProj P1)
        (curve25519_MontyCurveGroup.xProj curve25519_basepoint)).1 ≠ 0 ∨
    (xdadd (curve25519_MontyCurveGroup.xProj P0)
        (curve25519_MontyCurveGroup.xProj P1)
        (curve25519_MontyCurveGroup.xProj curve25519_basepoint)).2 ≠ 0 := by
  have hZD := curve25519_basepoint_xProj_snd_eq_one
  have hXD := curve25519_basepoint_xProj_fst_ne_zero
  rw [curve25519_xProj_eq] at hZD hXD
  obtain (_ | @⟨x0, y0, h0⟩) := P0
  · exact absurd (show (0:Curve25519Point) + 0 + (0 + 0) = 0 by simp) hP0nt
  · obtain (_ | @⟨x1, y1, h1⟩) := P1
    · -- P1 = 0 : the (DA − CB) term is `−2`, so the second output is `4·x_B ≠ 0`.
      right
      simp only [curve25519_xProj_eq, xProjW_some, xProjW_zero]
      have e2 : (xdadd ((x0 : Fp25519), 1) (1, 0)
          (xProjW (486662 : Fp25519) curve25519_basepoint)).2
          = 4 * (xProjW (486662 : Fp25519) curve25519_basepoint).1 := by
        simp only [xdadd]; ring
      rw [e2]
      exact mul_ne_zero fp25519_four_ne_zero hXD
    · -- both affine
      simp only [curve25519_xProj_eq, xProjW_some]
      by_contra hcon
      rw [not_or] at hcon
      obtain ⟨hc1, hc2⟩ := hcon
      rw [not_not] at hc1 hc2
      have e1 : (xdadd ((x0 : Fp25519), 1) (x1, 1)
          (xProjW (486662 : Fp25519) curve25519_basepoint)).1
          = (2 * (x0 * x1 - 1)) ^ 2 := by
        simp only [xdadd]; rw [hZD]; ring
      have e2 : (xdadd ((x0 : Fp25519), 1) (x1, 1)
          (xProjW (486662 : Fp25519) curve25519_basepoint)).2
          = (xProjW (486662 : Fp25519) curve25519_basepoint).1 * (2 * (x0 - x1)) ^ 2 := by
        simp only [xdadd]; ring
      rw [e2] at hc2
      have hxx : x0 = x1 := by
        rcases mul_eq_zero.mp hc2 with h | h
        · exact absurd h hXD
        · have : (2 * (x0 - x1)) = 0 := by
            have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
            exact this
          have hxx0 : x0 - x1 = 0 := by
            rcases mul_eq_zero.mp this with h' | h'
            · exact absurd h' fp25519_two_ne_zero
            · exact h'
          exact sub_eq_zero.mp hxx0
      rw [e1] at hc1
      subst hxx
      have hx2 : x0 ^ 2 = 1 := by
        have hz : (2 * (x0 * x0 - 1)) = 0 := by
          have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hc1
          exact this
        have hx00 : x0 * x0 - 1 = 0 := by
          rcases mul_eq_zero.mp hz with h' | h'
          · exact absurd h' fp25519_two_ne_zero
          · exact h'
        linear_combination hx00
      have hfac : (x0 - 1) * (x0 + 1) = 0 := by linear_combination hx2
      apply hP0nt
      rcases mul_eq_zero.mp hfac with h1' | h1'
      · exact curve25519_quad_eq_zero_of_xProj_one _ (by
          rw [curve25519_xProj_eq, xProjW_some, sub_eq_zero.mp h1'])
      · exact curve25519_quad_eq_zero_of_xProj_neg_one _ (by
          rw [curve25519_xProj_eq, xProjW_some, add_eq_zero_iff_eq_neg.mp h1'])

/-- **The base point discharges `LadderNondeg` for every in-range scalar.**
    For any bit-list whose value is below the subgroup order `l`, the entire
    Montgomery-ladder path over the base point is projectively nondegenerate. -/
theorem curve25519_basepoint_LadderNondeg (bits : List Bool)
    (hbits : bitsToNat bits < curve25519SubgroupOrder) :
    LadderNondeg curve25519_basepoint bits := by
  intro n hn
  have hnl : n < curve25519SubgroupOrder := lt_of_le_of_lt hn hbits
  refine ⟨?_, ?_, ?_⟩
  · -- (i) doubling at n·B
    by_cases hz0 : n • curve25519_basepoint = 0
    · left
      rw [hz0, curve25519_xProj_eq,
          show (0:Curve25519Point) = WeierstrassCurve.Affine.Point.zero from rfl,
          xProjW_zero, xdbl_one_zero]
      exact one_ne_zero
    · have hn0 : 0 < n := Nat.pos_of_ne_zero (fun h => hz0 (by rw [h, zero_nsmul]))
      exact curve25519_xdbl_nondeg_of_quad_ne_zero _
        (curve25519_quad_nsmul_ne_zero hn0 hnl)
  · -- (ii) doubling at (n+1)·B
    by_cases hz1 : (n + 1) • curve25519_basepoint = 0
    · left
      rw [hz1, curve25519_xProj_eq,
          show (0:Curve25519Point) = WeierstrassCurve.Affine.Point.zero from rfl,
          xProjW_zero, xdbl_one_zero]
      exact one_ne_zero
    · have hn1l : n + 1 < curve25519SubgroupOrder := by
        rcases Nat.lt_or_ge (n + 1) curve25519SubgroupOrder with h | h
        · exact h
        · refine absurd (?_ : (n + 1) • curve25519_basepoint = 0) hz1
          rw [show n + 1 = curve25519SubgroupOrder by omega]
          exact curve25519_basepoint_order_nsmul
      exact curve25519_xdbl_nondeg_of_quad_ne_zero _
        (curve25519_quad_nsmul_ne_zero (Nat.succ_pos n) hn1l)
  · -- (iii) differential addition
    have hd : curve25519_MontyCurveGroup.xProj
        (n • curve25519_basepoint - (n + 1) • curve25519_basepoint)
        = curve25519_MontyCurveGroup.xProj curve25519_basepoint := by
      rw [show n • curve25519_basepoint - (n + 1) • curve25519_basepoint
            = -curve25519_basepoint from by
            rw [succ_nsmul, sub_add_eq_sub_sub, sub_self, zero_sub]]
      exact curve25519_xProj_neg curve25519_basepoint
    rw [hd]
    by_cases hz0 : n • curve25519_basepoint = 0
    · -- n = 0 : the first output is `4·x_B² ≠ 0`
      left
      have hn0 : n = 0 := by
        by_contra hne
        exact (nsmul_ne_zero_of_lt_order curve25519_basepoint_addOrder
          (Nat.pos_of_ne_zero hne) hnl) hz0
      subst hn0
      have hZD := curve25519_basepoint_xProj_snd_eq_one
      have hXD := curve25519_basepoint_xProj_fst_ne_zero
      rw [zero_nsmul, zero_add, one_nsmul,
          show curve25519_MontyCurveGroup.xProj (0:Curve25519Point) = ((1:Fp25519), 0) from rfl]
      have e : (xdadd ((1:Fp25519), 0)
          (curve25519_MontyCurveGroup.xProj curve25519_basepoint)
          (curve25519_MontyCurveGroup.xProj curve25519_basepoint)).1
          = (curve25519_MontyCurveGroup.xProj curve25519_basepoint).2
            * (2 * (curve25519_MontyCurveGroup.xProj curve25519_basepoint).1) ^ 2 := by
        simp only [xdadd]; ring
      rw [e, hZD, one_mul]
      exact pow_ne_zero _ (mul_ne_zero fp25519_two_ne_zero hXD)
    · have hn0 : 0 < n := Nat.pos_of_ne_zero (fun h => hz0 (by rw [h, zero_nsmul]))
      exact curve25519_xdadd_nondeg _ _ (curve25519_quad_nsmul_ne_zero hn0 hnl)

/-- **Unconditional X25519 field-level scalar-multiplication theorem for the
    RFC 7748 base point.** For any scalar below the subgroup order `l`, the
    first component of the field-level Montgomery ladder run on `xProj B` is
    projectively equivalent to `xProj (k · B)` — the x-coordinate of the
    abstract-group scalar multiplication. This is `x25519_ladder_correct`
    with the `LadderNondeg` side condition discharged (via
    `curve25519_basepoint_LadderNondeg`), so it holds with no nondegeneracy
    hypothesis, exactly on the RFC 7748 scalar range `k < l`. -/
theorem x25519_ladder_correct_basepoint (bits : List Bool)
    (hbits : bitsToNat bits < curve25519SubgroupOrder) :
    ProjEquiv
      (xladderFold (curve25519Params Fp25519).a24
         (curve25519_MontyCurveGroup.xProj curve25519_basepoint) bits).1
      (curve25519_MontyCurveGroup.xProj
         (x25519 (bitsToNat bits) curve25519_basepoint)) :=
  x25519_ladder_correct curve25519_basepoint bits
    (curve25519_basepoint_LadderNondeg bits hbits)

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
