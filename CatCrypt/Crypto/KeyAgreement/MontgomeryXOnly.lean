/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import CatCrypt.Crypto.KeyAgreement.MontgomeryLadder

/-!
# Montgomery curve x-only formulas (Costello–Smith §4)

For a Montgomery curve

  E : B y² = x³ + A x² + x

over a field `F`, the x-only differential-addition and doubling
formulas operate on projective pairs `(X, Z)` representing the
x-coordinate `X/Z`. The formulas use only field operations (no y).

## What this file provides

1. The formulas `xdbl`, `xdadd` over any commutative ring `F`.
2. Basic algebraic properties of the formulas (projective invariance,
   commutativity of `xdbl`'s output shape, etc.).
3. **`MontyParams` structure** capturing the curve parameters `(A, B, p)`.
4. **The Costello–Smith §4 key identities** stated as a hypothesis class
   `MontyCurveGroup`, which axiomatises the correspondence between the
   x-only formulas and scalar multiplication on the abstract group.

   - `xdbl_eq`: `xdbl(X/Z) = x(2 · P)` when `x(P) = X/Z`
   - `xdadd_eq`: `xdadd(x(P), x(Q), x(P-Q)) = x(P + Q)`

## Why this is a hypothesis, not a theorem (yet)

Proving `xdbl_eq` and `xdadd_eq` from first principles requires
- The Montgomery-form group law in affine coordinates (~2 pages of
  polynomial algebra).
- A birational map to Weierstrass form (or a direct point-addition
  formula).
- Case analysis for the point at infinity / doubling singularities.

This is the classical **Costello–Smith §4** algebra. It's a page of
polynomial manipulation, doable in Lean in a few dozen lines once
the affine-coordinate group law is set up, but the group law itself
requires a Montgomery-curve structure in Mathlib that does not yet
exist (Mathlib has `WeierstrassCurve` but not `MontgomeryCurve`).

For now we axiomatise the correspondence and connect it to the ladder
correctness proof in `MontgomeryLadder.lean`.

## References

- Costello, Smith, "Montgomery curves and the Montgomery ladder",
  IACR eprint 2017/212, §4 (equations 8, 9, 12, 13).
- Bernstein, "Curve25519: new Diffie-Hellman speed records", PKC 2006.
-/

namespace CatCrypt.Crypto.ECC

variable {F : Type*} [CommRing F]

/-! ## x-only formulas as pure field computation -/

/-- Projective x-only doubling (Costello–Smith eq. 12). Given `(X, Z)` with
    `X/Z = x(P)`, returns `(X', Z')` with `X'/Z' = x(2 · P)`. Formula:

      X' = (X + Z)² · (X − Z)²
      Z' = 4·X·Z · ((X − Z)² + ((A + 2)/4) · 4·X·Z)

    We use the equivalent form with a single curve-parameter `a24 = (A+2)/4`. -/
def xdbl (a24 : F) (XZ : F × F) : F × F :=
  let (X, Z) := XZ
  let a := X + Z
  let b := X - Z
  let aa := a * a
  let bb := b * b
  let c := aa - bb          -- 4XZ
  let X' := aa * bb
  let Z' := c * (bb + a24 * c)
  (X', Z')

/-- Projective x-only differential addition (Costello–Smith eq. 13).
    Given `(XP, ZP)` for P, `(XQ, ZQ)` for Q, and `(XD, ZD)` for P−Q,
    returns the projective x-coordinate of `P + Q`. Formula:

      DA = (XP − ZP)(XQ + ZQ)
      CB = (XP + ZP)(XQ − ZQ)
      X' = ZD · (DA + CB)²
      Z' = XD · (DA − CB)² -/
def xdadd (PZ QZ DZ : F × F) : F × F :=
  let (XP, ZP) := PZ
  let (XQ, ZQ) := QZ
  let (XD, ZD) := DZ
  let DA := (XP - ZP) * (XQ + ZQ)
  let CB := (XP + ZP) * (XQ - ZQ)
  let X' := ZD * (DA + CB) ^ 2
  let Z' := XD * (DA - CB) ^ 2
  (X', Z')

/-! ## Algebraic properties -/

/-- `xdadd` is symmetric in its first two arguments up to the sign of the
    "DA − CB" term, which is squared, so full symmetry holds. -/
theorem xdadd_symm (PZ QZ DZ : F × F) :
    xdadd PZ QZ DZ = xdadd QZ PZ DZ := by
  simp only [xdadd]
  -- Expand the let-bindings and reassemble.
  obtain ⟨XP, ZP⟩ := PZ
  obtain ⟨XQ, ZQ⟩ := QZ
  obtain ⟨XD, ZD⟩ := DZ
  -- Swapping P and Q negates DA-CB and negates DA+CB modulo signs; both
  -- squared, so outputs are equal.
  congr 1 <;> ring

/-- If `Z = 0`, the projective point `(X, 0)` represents the point at
    infinity. Doubling the point at infinity gives the point at infinity. -/
theorem xdbl_infinity (a24 : F) (X : F) : xdbl a24 (X, 0) = (X^4, 0) := by
  simp only [xdbl]; ring_nf

/-! ## Curve parameters -/

/-- A Montgomery curve parameter triple `(A, p)` over a field `F`, plus
    the common derived constant `a24 = (A + 2) / 4`. Kept as an
    independent field to avoid division in the representation. -/
structure MontyParams (F : Type*) [CommRing F] where
  /-- Curve equation: `y² = x³ + A x² + x`. -/
  A : F
  /-- The derived constant `(A + 2) / 4` used in `xdbl`. The invariant
      `4 * a24 = A + 2` is part of the well-formedness hypothesis. -/
  a24 : F

/-- Curve25519 parameters: `A = 486662`, `a24 = 121666 = (486662 + 2)/4`.

    Note: some implementations use the constant `121665 = (A − 2)/4` with a
    different doubling-formula variant. Here we use the `(A + 2)/4` variant
    corresponding to Costello–Smith eq. 12. -/
def curve25519Params (F : Type*) [CommRing F] : MontyParams F :=
  { A := (486662 : ℕ), a24 := (121666 : ℕ) }

/-- Well-formedness: `4 * a24 = A + 2`. Verifies for Curve25519 over any
    field where the characteristic doesn't divide the value. -/
theorem curve25519Params_wf (F : Type*) [CommRing F] :
    (4 : F) * (curve25519Params F).a24 = (curve25519Params F).A + 2 := by
  simp only [curve25519Params]
  push_cast; ring

/-! ## Costello–Smith §4 — polynomial identities

The identities below are the algebraic content of Costello–Smith §4.
Each is a pure field identity, provable by the `ring` tactic. They
state that the x-only projective formulas compute the same values as
the affine slope-based formulas evaluated under the Montgomery curve
equation `y² = x³ + A x² + x`.

Once a Montgomery-curve group structure is in place (with affine
point addition), these identities are the core algebraic fact needed
to prove `MontyCurveGroup.xdbl_spec` and `xdadd_spec`. -/

/-- **xdbl polynomial identity** (Costello–Smith §4, doubling).
    The projective x-coordinate numerator `xdbl.1` at input `(x, 1)`
    equals `(x² − 1)²`, matching the affine formula
    `x(2P) = λ² − A − 2x` with `λ = (3x² + 2Ax + 1) / (2y)`.

    Specifically, over any commutative ring, the identity
    `(3x² + 2Ax + 1)² − 4(A + 2x)(x³ + Ax² + x) = (x² − 1)²`
    holds. This is the numerator identity that falls out of clearing
    the common denominator `4(x³ + Ax² + x) = 4y²` from the affine
    expression for `x(2P)`. -/
theorem xdbl_affine_numerator_identity (A x : F) :
    (3 * x^2 + 2 * A * x + 1)^2 - 4 * (A + 2 * x) * (x^3 + A * x^2 + x)
      = (x^2 - 1)^2 := by
  ring

/-- The xdbl numerator matches `(x² − 1)²` — direct from the formula. -/
theorem xdbl_numerator (a24 x : F) :
    (xdbl a24 (x, 1)).1 = (x^2 - 1)^2 := by
  simp only [xdbl]; ring

/-- The xdbl denominator, in the `a24 = (A + 2) / 4` convention, matches
    `4x · (x² + A x + 1)` under the constraint `4 a24 = A + 2`. -/
theorem xdbl_denominator (A a24 x : F) (h : 4 * a24 = A + 2) :
    (xdbl a24 (x, 1)).2 = 4 * x * (x^2 + A * x + 1) := by
  simp only [xdbl]
  linear_combination (4 * x^2 : F) * h

/-- **xdadd polynomial identity** (Costello–Smith §4, differential
    addition). Given points P, Q with x-coordinates `xP`, `xQ` and
    their difference `P − Q` with x-coordinate `xD`, the projective
    output of `xdadd` has numerator `((xP − 1)(xQ + 1) + (xP + 1)(xQ − 1))² = (2(xP xQ − 1))²`
    and denominator `xD · ((xP − 1)(xQ + 1) − (xP + 1)(xQ − 1))² = xD · (2(xQ − xP))²`
    when `Z` coordinates are all normalised to 1. -/
theorem xdadd_affine_num_simpl (xP xQ : F) :
    ((xP - 1) * (xQ + 1) + (xP + 1) * (xQ - 1))^2 = (2 * (xP * xQ - 1))^2 := by
  ring

theorem xdadd_affine_den_simpl (xP xQ : F) :
    ((xP - 1) * (xQ + 1) - (xP + 1) * (xQ - 1))^2 = (2 * (xQ - xP))^2 := by
  ring

/-- The xdadd output with `Z = 1` for all three projective inputs simplifies
    to `(2(xP xQ − 1))² · 1` and `xD · (2(xQ − xP))²` — the classical form. -/
theorem xdadd_normalised (xP xQ xD : F) :
    xdadd (xP, 1) (xQ, 1) (xD, 1) =
      ((2 * (xP * xQ - 1))^2, xD * (2 * (xQ - xP))^2) := by
  simp only [xdadd]
  refine Prod.ext ?_ ?_
  · show 1 * ((xP - 1) * (xQ + 1) + (xP + 1) * (xQ - 1))^2 = (2 * (xP * xQ - 1))^2
    ring
  · show xD * ((xP - 1) * (xQ + 1) - (xP + 1) * (xQ - 1))^2 = xD * (2 * (xQ - xP))^2
    ring

/-! ## Costello–Smith §4 correspondence (hypothesised group form) -/

/-- A Montgomery curve with a distinguished abelian group of points and
    an x-coordinate map. The key hypotheses encode Costello–Smith §4 §4.

    `xdbl_spec` and `xdadd_spec` state that the x-only formulas agree with
    scalar multiplication (equivalently: group addition) on the abstract
    group. Proving these from the affine Montgomery curve group law is
    the remaining work; see the header. -/
class MontyCurveGroup (F : Type*) [CommRing F] (params : MontyParams F)
    (G : Type*) [AddCommGroup G] where
  /-- Project a curve point to its projective x-coordinate `(X, Z)`. -/
  xProj : G → F × F
  /-- `xdbl` computes the x-coordinate of doubling, up to projective
      equivalence (both outputs represent the same `X/Z`). -/
  xdbl_spec : ∀ (P : G),
    let (Xd, Zd) := xdbl params.a24 (xProj P)
    let (X2, Z2) := xProj (P + P)
    Xd * Z2 = X2 * Zd
  /-- `xdadd` computes the x-coordinate of addition, up to projective
      equivalence, given the difference as auxiliary input. -/
  xdadd_spec : ∀ (P Q : G),
    let (Xs, Zs) := xdadd (xProj P) (xProj Q) (xProj (P - Q))
    let (Xa, Za) := xProj (P + Q)
    Xs * Za = Xa * Zs

/-! ## Field-level x-only ladder

The ladder below is the actual program a Jasmin (or bedrock2, or Rust)
implementation runs: pure field operations on projective pairs `(X, Z)`,
no points, no y-coordinates, no group law. Connect it to the
abstract-group ladder via `MontyCurveGroup` using `ProjEquiv`. -/

/-- Projective equivalence on `F × F`: `(X₁, Z₁) ∼ (X₂, Z₂)` iff their
    x-coordinates agree (`X₁/Z₁ = X₂/Z₂` in the field of fractions). -/
def ProjEquiv (p q : F × F) : Prop :=
  p.1 * q.2 = q.1 * p.2

@[refl] lemma ProjEquiv.refl (p : F × F) : ProjEquiv p p := by
  unfold ProjEquiv; ring

lemma ProjEquiv.symm {p q : F × F} (h : ProjEquiv p q) : ProjEquiv q p := by
  unfold ProjEquiv at h ⊢; linear_combination -h

/-- One step of the field-level x-only ladder. Takes the projective
    x-coordinate of the base point `xP` (as the invariant difference) and
    the current `(R₀_proj, R₁_proj)` state, steps on bit `b` via `xdbl`
    and `xdadd`. -/
def xladderStep (a24 : F) (xP : F × F) (acc : (F × F) × (F × F)) (b : Bool) :
    (F × F) × (F × F) :=
  let (R₀, R₁) := acc
  if b then (xdadd R₀ R₁ xP, xdbl a24 R₁)
       else (xdbl a24 R₀, xdadd R₀ R₁ xP)

/-- Run the field-level ladder over a list of bits (MSB first) starting
    from projective `(1, 0)` (infinity) and `xP` (the base point). -/
def xladderFold (a24 : F) (xP : F × F) : List Bool → (F × F) × (F × F)
  | []      => ((1, 0), xP)
  | b :: bs => xladderStep a24 xP (xladderFold a24 xP bs) b

/-- `xdbl` respects projective equivalence: if two projective inputs
    represent the same x-coordinate, their `xdbl` outputs do too.
    Both numerator and denominator of `xdbl` are homogeneous polynomials
    of degree 4 in `(X, Z)`, so scaling both coordinates by a common
    factor scales the output uniformly — `ProjEquiv` is preserved. -/
theorem xdbl_projEquiv (a24 : F) {p q : F × F} (h : ProjEquiv p q) :
    ProjEquiv (xdbl a24 p) (xdbl a24 q) := by
  obtain ⟨X₁, Z₁⟩ := p
  obtain ⟨X₂, Z₂⟩ := q
  unfold ProjEquiv xdbl at *
  simp only at h ⊢
  linear_combination (4 * (X₁*X₂ - Z₁*Z₂)
      * ((X₁-Z₁)^2 * (X₂-Z₂)^2
         + 16*a24 * (X₂*Z₂*(X₁-Z₁)^2 + X₁*Z₁*(X₂+Z₂)^2))
    + 48*a24*(Z₁^2*Z₂^2 - X₁^2*X₂^2)*(X₁*Z₂ + X₂*Z₁)) * h

/-- `xdadd` respects projective equivalence in all three arguments.
    Key algebraic fact: `DA + CB = 2(XPXQ − ZPZQ)` and
    `DA − CB = 2(XPZQ − XQZP)`, and each of these is homogeneous of
    degree 1 in each of `(XP, ZP)` and `(XQ, ZQ)`. The `ZD`/`XD`
    factors cancel under `ProjEquiv (d, d')`. -/
theorem xdadd_projEquiv {p p' q q' d d' : F × F}
    (hp : ProjEquiv p p') (hq : ProjEquiv q q') (hd : ProjEquiv d d') :
    ProjEquiv (xdadd p q d) (xdadd p' q' d') := by
  obtain ⟨X₁, Z₁⟩ := p
  obtain ⟨X₂, Z₂⟩ := q
  obtain ⟨XD, ZD⟩ := d
  obtain ⟨X₁', Z₁'⟩ := p'
  obtain ⟨X₂', Z₂'⟩ := q'
  obtain ⟨XD', ZD'⟩ := d'
  unfold ProjEquiv xdadd at *
  simp only at hp hq hd ⊢
  linear_combination
    16 * ZD * XD' * (Z₂*Z₂' - X₂*X₂')
      * ((X₁*X₂ - Z₁*Z₂)*(X₁'*Z₂' - X₂'*Z₁')
         + (X₁'*X₂' - Z₁'*Z₂')*(X₁*Z₂ - X₂*Z₁)) * hp
    + 16 * ZD * XD' * (X₁*X₁' - Z₁*Z₁')
        * ((X₁*X₂ - Z₁*Z₂)*(X₁'*Z₂' - X₂'*Z₁')
           + (X₁'*X₂' - Z₁'*Z₂')*(X₁*Z₂ - X₂*Z₁)) * hq
    + (-16) * (X₁'*X₂' - Z₁'*Z₂')^2 * (X₁*Z₂ - X₂*Z₁)^2 * hd

/-! ## Field-level ladder correctness

Combines `MontyCurveGroup.{xdbl_spec, xdadd_spec}` with the invariant
`(R₀, R₁) ∼ (xProj (n·P), xProj ((n+1)·P))` from
`MontgomeryLadder.ladderFold_correct`, where `∼` is projective equivalence. -/

/-- The field-level ladder invariant: the state `(R₀, R₁)` projectively
    represents `(n · P, (n + 1) · P)` for some running scalar `n`. -/
def XLadderInv {F : Type*} [CommRing F] {params : MontyParams F}
    {G : Type*} [AddCommGroup G] [h : MontyCurveGroup F params G]
    (P : G) (n : ℕ) (st : (F × F) × (F × F)) : Prop :=
  ProjEquiv st.1 (h.xProj (n • P)) ∧ ProjEquiv st.2 (h.xProj ((n + 1) • P))

/-- **Restricted `ProjEquiv` transitivity over an integral domain.**
    `ProjEquiv` is transitive when the middle term is nondegenerate
    (not both coordinates zero). Over a `CommRing` that isn't an
    integral domain, transitivity can fail; we specialise to the
    `Field` case (integral domain) and require nondegeneracy explicitly. -/
theorem ProjEquiv.trans {F : Type*} [Field F] {p q r : F × F}
    (hpq : ProjEquiv p q) (hqr : ProjEquiv q r)
    (hq : q.1 ≠ 0 ∨ q.2 ≠ 0) : ProjEquiv p r := by
  unfold ProjEquiv at *
  rcases hq with hq1 | hq2
  · -- q.1 ≠ 0
    rcases eq_or_ne q.2 0 with hq2 | hq2
    · -- q.2 = 0: then from hpq: p.1 * 0 = q.1 * p.2, so p.2 = 0 (since q.1 ≠ 0).
      -- From hqr: q.1 * r.2 = r.1 * 0 = 0, so r.2 = 0.
      rw [hq2, mul_zero] at hpq
      rw [hq2, mul_zero] at hqr
      have hp2 : p.2 = 0 := (mul_eq_zero.mp hpq.symm).resolve_left hq1
      have hr2 : r.2 = 0 := (mul_eq_zero.mp hqr).resolve_left hq1
      rw [hp2, hr2, mul_zero, mul_zero]
    · -- q.2 ≠ 0
      grind
  · -- q.2 ≠ 0 directly
    grind

/-- **Doubling step preserves ProjEquiv**, given the intermediate
    `xdbl (xProj (n·P))` is nondegenerate (Z ≠ 0). This is the
    composition of `xdbl_projEquiv`, `xdbl_spec`, and `ProjEquiv.trans`. -/
theorem ProjEquiv_xdbl_of_inv {F : Type*} [Field F] {params : MontyParams F}
    {G : Type*} [AddCommGroup G] [h : MontyCurveGroup F params G]
    (P : G) (n : ℕ) {r : F × F}
    (hr : ProjEquiv r (h.xProj (n • P)))
    (hND : (xdbl params.a24 (h.xProj (n • P))).1 ≠ 0 ∨
           (xdbl params.a24 (h.xProj (n • P))).2 ≠ 0) :
    ProjEquiv (xdbl params.a24 r) (h.xProj (n • P + n • P)) :=
  ProjEquiv.trans (xdbl_projEquiv params.a24 hr) (h.xdbl_spec (n • P)) hND

/-- **Differential-addition step preserves ProjEquiv**, given the
    intermediate `xdadd` output is nondegenerate, and that `xProj` is
    negation-invariant (`xProj (-X) = xProj X`). -/
theorem ProjEquiv_xdadd_of_inv {F : Type*} [Field F] {params : MontyParams F}
    {G : Type*} [AddCommGroup G] [h : MontyCurveGroup F params G]
    (P Q D : G) {r s d : F × F}
    (hr : ProjEquiv r (h.xProj P))
    (hs : ProjEquiv s (h.xProj Q))
    (hd : ProjEquiv d (h.xProj D))
    (hDeq : h.xProj D = h.xProj (P - Q))
    (hND : (xdadd (h.xProj P) (h.xProj Q) (h.xProj (P - Q))).1 ≠ 0 ∨
           (xdadd (h.xProj P) (h.xProj Q) (h.xProj (P - Q))).2 ≠ 0) :
    ProjEquiv (xdadd r s d) (h.xProj (P + Q)) := by
  rw [hDeq] at hd
  exact ProjEquiv.trans (xdadd_projEquiv hr hs hd) (h.xdadd_spec P Q) hND

/-- **Field-level ladder step preserves the invariant.**

    For bit `b`, scalar `n` advances to `2n + (if b then 1 else 0)`.

    Requires:
    - `Field F` (for `ProjEquiv` transitivity);
    - `hNeg`: `xProj` is negation-invariant (holds on `montgomeryW`
      via `xProjW_neg`);
    - `hND0/hND1`: nondegeneracy of the two intermediate outputs
      (`xdbl (xProj (n·P))` and `xdadd (xProj (n·P)) (xProj ((n+1)·P))
      (xProj (-P))`). -/
theorem xladderStep_preserves_invariant
    {F : Type*} [Field F] {params : MontyParams F}
    {G : Type*} [AddCommGroup G] [h : MontyCurveGroup F params G]
    (P : G) (n : ℕ) (st : (F × F) × (F × F)) (b : Bool)
    (hNeg : ∀ X : G, h.xProj (-X) = h.xProj X)
    (hND0 : (xdbl params.a24 (h.xProj (n • P))).1 ≠ 0 ∨
            (xdbl params.a24 (h.xProj (n • P))).2 ≠ 0)
    (hND1 : (xdbl params.a24 (h.xProj ((n + 1) • P))).1 ≠ 0 ∨
            (xdbl params.a24 (h.xProj ((n + 1) • P))).2 ≠ 0)
    (hNDa : (xdadd (h.xProj (n • P)) (h.xProj ((n + 1) • P))
              (h.xProj (n • P - (n + 1) • P))).1 ≠ 0 ∨
            (xdadd (h.xProj (n • P)) (h.xProj ((n + 1) • P))
              (h.xProj (n • P - (n + 1) • P))).2 ≠ 0)
    (hInv : XLadderInv (params := params) P n st) :
    XLadderInv (params := params) P (2 * n + (if b then 1 else 0))
      (xladderStep params.a24 (h.xProj P) st b) := by
  obtain ⟨hR₀, hR₁⟩ := hInv
  -- Key identity: n•P - (n+1)•P = -P, so xProj of it = xProj(-P) = xProj(P) by hNeg.
  have hDiff : n • P - (n + 1) • P = -P := by
    rw [succ_nsmul, sub_add_eq_sub_sub, sub_self, zero_sub]
  have hProjP : h.xProj (n • P - (n + 1) • P) = h.xProj P := by
    rw [hDiff, hNeg]
  -- The "difference" projection equivalence used for both xdadd calls.
  have hDiffEq : ProjEquiv (h.xProj P) (h.xProj (n • P - (n + 1) • P)) := by
    rw [hProjP]
  cases b
  · -- b = false
    refine ⟨?_, ?_⟩
    · -- xdbl st.1 ∼ xProj ((2n + 0) • P)
      show ProjEquiv (xdbl params.a24 st.1) (h.xProj ((2 * n + 0) • P))
      have heq : (2 * n + 0) • P = n • P + n • P := by
        rw [Nat.add_zero, two_mul, add_nsmul]
      rw [heq]
      exact ProjEquiv_xdbl_of_inv P n hR₀ hND0
    · -- xdadd st.1 st.2 (xProj P) ∼ xProj ((2n + 0 + 1) • P)
      show ProjEquiv (xdadd st.1 st.2 (h.xProj P))
              (h.xProj ((2 * n + 0 + 1) • P))
      have heq : (2 * n + 0 + 1) • P = n • P + (n + 1) • P := by
        rw [Nat.add_zero, show 2 * n + 1 = n + (n + 1) from by omega, add_nsmul]
      rw [heq]
      exact ProjEquiv_xdadd_of_inv (n • P) ((n + 1) • P) (n • P - (n + 1) • P)
        hR₀ hR₁ hDiffEq rfl hNDa
  · -- b = true
    refine ⟨?_, ?_⟩
    · -- xdadd st.1 st.2 (xProj P) ∼ xProj ((2n + 1) • P)
      show ProjEquiv (xdadd st.1 st.2 (h.xProj P))
              (h.xProj ((2 * n + 1) • P))
      have heq : (2 * n + 1) • P = n • P + (n + 1) • P := by
        rw [show 2 * n + 1 = n + (n + 1) from by omega, add_nsmul]
      rw [heq]
      exact ProjEquiv_xdadd_of_inv (n • P) ((n + 1) • P) (n • P - (n + 1) • P)
        hR₀ hR₁ hDiffEq rfl hNDa
    · -- xdbl st.2 ∼ xProj ((2n + 1 + 1) • P)
      show ProjEquiv (xdbl params.a24 st.2) (h.xProj ((2 * n + 1 + 1) • P))
      have heq : (2 * n + 1 + 1) • P = (n + 1) • P + (n + 1) • P := by
        rw [show 2 * n + 1 + 1 = (n + 1) + (n + 1) from by omega, add_nsmul]
      rw [heq]
      exact ProjEquiv_xdbl_of_inv P (n + 1) hR₁ hND1

end CatCrypt.Crypto.ECC
