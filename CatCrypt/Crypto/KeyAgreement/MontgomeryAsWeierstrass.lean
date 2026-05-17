/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import CatCrypt.Crypto.KeyAgreement.MontgomeryXOnly

/-!
# Montgomery curve as a Weierstrass curve (Option B)

The Montgomery equation `y² = x³ + A x² + x` (with `B = 1`) is literally
a Weierstrass equation with `a₁ = 0, a₂ = A, a₃ = 0, a₄ = 1, a₆ = 0`.
We instantiate `Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass`
directly and reuse its proved `AddCommGroup` structure on affine points.

This closes the full `MontyCurveGroup` specification without needing a
separate Montgomery-form group-law port:

- **Definition** `montgomeryW A : WeierstrassCurve F` — trivial
- **Group instance** `(montgomeryW A).toAffine.Point` — free from Mathlib
- **xProjW** — projective x-coordinate map (zero ↦ (1, 0); affine (x, _) ↦ (x, 1))
- **`xdbl_spec_W`** — x-only doubling formula matches `P + P`'s x-coord,
  covering the point at infinity, 2-torsion, and generic cases
- **`xdadd_spec_W`** — x-only differential addition matches `P + Q`'s x-coord,
  covering `P = 0`, `Q = 0`, `P = ±Q`, and generic cases (`xp ≠ xq`)
- **`montgomeryW_MontyCurveGroup`** — packages the above into a
  `MontyCurveGroup` instance, modulo the hypotheses `2 ≠ 0` and
  `4 · a24 = A + 2`.

The proof reduces everything to two polynomial identities over the
base field (`xdbl_affine_numerator_identity` and `xdadd_affine_identity`),
both of which are provable by `linear_combination` using only the two
curve equations for `P, Q`.

## References

- Costello, Smith, "Montgomery curves and the Montgomery ladder",
  IACR eprint 2017/212, §4.
- Mathlib, `AlgebraicGeometry/EllipticCurve/Affine/Formula.lean`.
-/

namespace CatCrypt.Crypto.ECC

open WeierstrassCurve

variable {F : Type*} [Field F]

/-! ## Montgomery curve as a Weierstrass curve -/

/-- The Montgomery equation `y² = x³ + A x² + x` expressed as a
    Weierstrass curve with `(a₁, a₂, a₃, a₄, a₆) = (0, A, 0, 1, 0)`. -/
def montgomeryW (A : F) : WeierstrassCurve F where
  a₁ := 0
  a₂ := A
  a₃ := 0
  a₄ := 1
  a₆ := 0

@[simp] lemma montgomeryW_a₁ (A : F) : (montgomeryW A).a₁ = 0 := rfl
@[simp] lemma montgomeryW_a₂ (A : F) : (montgomeryW A).a₂ = A := rfl
@[simp] lemma montgomeryW_a₃ (A : F) : (montgomeryW A).a₃ = 0 := rfl
@[simp] lemma montgomeryW_a₄ (A : F) : (montgomeryW A).a₄ = 1 := rfl
@[simp] lemma montgomeryW_a₆ (A : F) : (montgomeryW A).a₆ = 0 := rfl

/-- Curve equation check: `y² = x³ + A x² + x` iff the Weierstrass equation
    holds for `(x, y)` on `montgomeryW A`. -/
theorem montgomeryW_equation (A x y : F) :
    (montgomeryW A).toAffine.Equation x y ↔ y^2 = x^3 + A * x^2 + x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [montgomeryW_a₁, montgomeryW_a₂, montgomeryW_a₃, montgomeryW_a₄,
             montgomeryW_a₆, zero_mul, add_zero]
  rw [show (1 : F) * x = x from one_mul _]

/-! ## Affine-doubling x-coordinate matches xdbl ratio -/

/-- The affine slope for doubling a Montgomery point:
    `ℓ = (3x² + 2Ax + 1) / (2y)`. This is Mathlib's `slope` specialised to
    the doubling case (`x₁ = x₂`, `y₁ = y₂`) on `montgomeryW A`. -/
def montyDoublingSlope (A x y : F) : F :=
  (3 * x^2 + 2 * A * x + 1) / (2 * y)

/-- The x-coordinate of `2P` via the affine formula, specialised to
    `montgomeryW A`. Mathlib's `addX x x ℓ = ℓ² + a₁·ℓ − a₂ − 2x`, which
    for Montgomery (a₁=0, a₂=A) reduces to `ℓ² − A − 2x`. -/
def montyDoublingX (A x ℓ : F) : F :=
  ℓ^2 - A - 2 * x

/-- **Core identity — affine doubling x-coord matches xdbl's ratio.**

    Given a point `(x, y)` on Montgomery `y² = x³ + A x² + x` with `y ≠ 0`
    (not a 2-torsion point), and `4 · a24 = A + 2`, the affine-formula
    x-coordinate of `2 · (x, y)` equals the projective ratio `X' / Z'` of
    `xdbl a24 (x, 1)`, expressed as `X' = montyDoublingX · Z'`. -/
theorem xdbl_matches_affine_doubling
    (A a24 x y : F)
    (hCurve : y^2 = x^3 + A * x^2 + x)
    (hy : 2 * y ≠ 0)
    (h24 : 4 * a24 = A + 2) :
    montyDoublingX A x (montyDoublingSlope A x y) * (xdbl a24 (x, 1)).2
      = (xdbl a24 (x, 1)).1 := by
  rw [xdbl_numerator, xdbl_denominator A a24 x h24]
  -- Goal: montyDoublingX A x (montyDoublingSlope A x y) * (4·x·(x²+A·x+1)) = (x²-1)²
  simp only [montyDoublingX, montyDoublingSlope]
  -- Let δ = (3x² + 2Ax + 1)². Then LHS = (δ/(4y²) - A - 2x) · (4x(x² + A·x + 1)).
  -- Using 4y² = 4(x³ + A·x² + x) = 4x(x² + A·x + 1):
  --   (δ/(4y²)) · 4x(x²+A·x+1) = δ
  --   (A + 2x) · 4x(x²+A·x+1) = (A + 2x) · 4(x³ + A·x² + x)
  -- Hence LHS = δ - 4(A+2x)(x³+A·x²+x) = (x²-1)² by xdbl_affine_numerator_identity.
  have h4y2 : (2 * y)^2 = 4 * x * (x^2 + A * x + 1) := by
    calc (2 * y)^2 = 4 * y^2 := by ring
      _ = 4 * (x^3 + A * x^2 + x) := by rw [hCurve]
      _ = 4 * x * (x^2 + A * x + 1) := by ring
  have h4y2_ne : (2 * y)^2 ≠ 0 := pow_ne_zero _ hy
  have hX_ne : 4 * x * (x^2 + A * x + 1) ≠ 0 := h4y2 ▸ h4y2_ne
  have hδ : (3 * x^2 + 2 * A * x + 1)^2 - 4 * (A + 2 * x) * (x^3 + A * x^2 + x)
              = (x^2 - 1)^2 := xdbl_affine_numerator_identity A x
  -- Expand slope², rewrite (2y)² = 4x(x²+Ax+1), then cancel the division
  -- with the outer multiplication to reduce to the polynomial identity hδ.
  rw [div_pow, h4y2, sub_sub, sub_mul, div_mul_cancel₀ _ hX_ne]
  linear_combination hδ

/-! ## Projective x-coordinate map and MontyCurveGroup specs -/

/-- Projective x-coordinate of a Weierstrass affine point on the Montgomery
    curve. The point at infinity projects to `(1, 0)` (representing the
    "point at infinity" in the projective line); a finite affine point
    `(x, y)` projects to `(x, 1)`. -/
def xProjW (A : F) : (montgomeryW A).toAffine.Point → F × F
  | .zero => (1, 0)
  | @WeierstrassCurve.Affine.Point.some _ _ _ x _ _ => (x, 1)

@[simp] lemma xProjW_zero (A : F) :
    xProjW A (WeierstrassCurve.Affine.Point.zero) = (1, 0) := rfl

@[simp] lemma xProjW_some (A : F) {x y : F}
    (h : (montgomeryW A).toAffine.Nonsingular x y) :
    xProjW A (.some x y h) = (x, 1) := rfl

/-- **`xProjW` is negation-invariant.** The x-coordinate of `-P` equals
    that of `P`, since Montgomery negation only flips `y`. -/
@[simp] theorem xProjW_neg (A : F) (P : (montgomeryW A).toAffine.Point) :
    xProjW A (-P) = xProjW A P := by
  obtain (_ | @⟨x, y, h⟩) := P
  · rfl
  · rw [WeierstrassCurve.Affine.Point.neg_some]; rfl

/-- The Mathlib `negY` for Montgomery is `-y` (since `a₁ = a₃ = 0`). -/
@[simp] lemma montgomeryW_negY (A x y : F) :
    (montgomeryW A).toAffine.negY x y = -y := by
  simp [WeierstrassCurve.Affine.negY]

/-- The Mathlib doubling slope on Montgomery is `(3x² + 2Ax + 1) / (2y)`. -/
lemma montgomeryW_slope_double [DecidableEq F] (A x y : F) (hy : y ≠ -y) :
    (montgomeryW A).toAffine.slope x x y y = montyDoublingSlope A x y := by
  have hy' : y ≠ (montgomeryW A).toAffine.negY x y := by rwa [montgomeryW_negY]
  rw [WeierstrassCurve.Affine.slope, if_pos rfl, if_neg hy']
  simp only [montgomeryW_negY, montgomeryW_a₁, montgomeryW_a₂, montgomeryW_a₄,
             montyDoublingSlope]
  ring_nf

/-- The Mathlib `addX` on doubling reduces to `montyDoublingX`. -/
lemma montgomeryW_addX_double (A x ℓ : F) :
    (montgomeryW A).toAffine.addX x x ℓ = montyDoublingX A x ℓ := by
  simp only [WeierstrassCurve.Affine.addX, montgomeryW_a₁, montgomeryW_a₂,
             montyDoublingX]
  ring

/-- **`xdbl_spec` on `(montgomeryW A).toAffine.Point`.** The x-only doubling
    formula `xdbl` computes the projective x-coordinate of `P + P` for any
    point `P` on the Montgomery curve as a Weierstrass curve. -/
theorem xdbl_spec_W [DecidableEq F] (h2 : (2 : F) ≠ 0) (A a24 : F)
    (h24 : 4 * a24 = A + 2)
    (P : (montgomeryW A).toAffine.Point) :
    (xdbl a24 (xProjW A P)).1 * (xProjW A (P + P)).2
      = (xProjW A (P + P)).1 * (xdbl a24 (xProjW A P)).2 := by
  obtain (_ | @⟨x, y, h⟩) := P
  · -- P = zero: xProjW = (1, 0), P + P = zero, xdbl a24 (1, 0) = (1, 0).
    show (xdbl a24 (1, 0)).1 * 0 = 1 * (xdbl a24 (1, 0)).2
    simp [xdbl]
  · -- P = some h with coordinates (x, y)
    by_cases hy_eq : y = (montgomeryW A).toAffine.negY x y
    · -- 2-torsion case: P + P = 0, so xProjW (P + P) = (1, 0) and we need
      -- (xdbl.2) = 0. Curve equation + y = -y in char ≠ 2 gives y = 0,
      -- hence 4x(x²+Ax+1) = 4y² = 0.
      rw [WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy_eq]
      rw [montgomeryW_negY] at hy_eq
      have h2y : 2 * y = 0 := by grind
      have hy_zero : y = 0 := (mul_eq_zero.mp h2y).resolve_left h2
      have hCurve : y^2 = x^3 + A * x^2 + x := (montgomeryW_equation A x y).mp h.1
      have hx_factor : (4 : F) * x * (x^2 + A * x + 1) = 0 := by
        have hy2_zero : y^2 = 0 := by rw [hy_zero]; ring
        linear_combination -4 * hCurve + 4 * hy2_zero
      show (xdbl a24 (x, 1)).1 * (xProjW A (0 : _)).2
             = (xProjW A (0 : _)).1 * (xdbl a24 (x, 1)).2
      rw [show (0 : (montgomeryW A).toAffine.Point) =
              WeierstrassCurve.Affine.Point.zero from rfl, xProjW_zero]
      rw [xdbl_denominator A a24 x h24, hx_factor]
      ring
    · -- Non-2-torsion: P + P = some (addX x x slope) (addY ...).
      rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy_eq]
      rw [montgomeryW_negY] at hy_eq
      have hCurve : y^2 = x^3 + A * x^2 + x := (montgomeryW_equation A x y).mp h.1
      have h2y : 2 * y ≠ 0 := by
        intro h0
        apply hy_eq
        linear_combination h0
      simp only [xProjW_some, montgomeryW_addX_double,
                 montgomeryW_slope_double A x y hy_eq]
      rw [mul_one]
      exact (xdbl_matches_affine_doubling A a24 x y hCurve h2y h24).symm

/-! ## xdadd correspondence -/

/-- **Core polynomial identity for differential addition** (Costello–Smith §4).

    Given two points `(xp, yp)` and `(xq, yq)` on the Montgomery curve
    `y² = x³ + A x² + x`, the product of the affine "plus" and "minus"
    x-numerators equals `(xp · xq − 1)² · (xq − xp)²`. Proof is purely
    polynomial, using only the two curve equations. -/
theorem xdadd_affine_identity (A xp yp xq yq : F)
    (hp : yp^2 = xp^3 + A * xp^2 + xp)
    (hq : yq^2 = xq^3 + A * xq^2 + xq) :
    ((yq - yp)^2 - (A + xp + xq) * (xq - xp)^2) *
        ((yq + yp)^2 - (A + xp + xq) * (xq - xp)^2)
      = (xp * xq - 1)^2 * (xq - xp)^2 := by
  linear_combination
    (yp^2 + (xp^3 + A*xp^2 + xp) - 2*yq^2 - 2*(A + xp + xq)*(xq - xp)^2) * hp
    + (yq^2 + (xq^3 + A*xq^2 + xq) - 2*(xp^3 + A*xp^2 + xp)
        - 2*(A + xp + xq)*(xq - xp)^2) * hq

/-- **Differential-addition x-coordinate identity.** Combines the two
    affine secant x-coordinates (for `P+Q` and `P-Q`) into the product
    form `(xp · xq − 1)²`. This is the form needed by `xdadd_spec_W`. -/
theorem xdadd_affine_prod (A xp yp xq yq : F)
    (hp : yp^2 = xp^3 + A * xp^2 + xp)
    (hq : yq^2 = xq^3 + A * xq^2 + xq)
    (hxne : xq - xp ≠ 0) :
    ((yq - yp)^2 / (xq - xp)^2 - A - xp - xq)
        * ((yq + yp)^2 / (xq - xp)^2 - A - xp - xq)
        * (xq - xp)^2
      = (xp * xq - 1)^2 := by
  have hx2ne : (xq - xp)^2 ≠ 0 := pow_ne_zero _ hxne
  field_simp
  linear_combination xdadd_affine_identity A xp yp xq yq hp hq

/-- Mathlib's secant slope specialised to Montgomery with `x₁ ≠ x₂`. -/
lemma montgomeryW_slope_secant [DecidableEq F] (A x₁ x₂ y₁ y₂ : F) (hx : x₁ ≠ x₂) :
    (montgomeryW A).toAffine.slope x₁ x₂ y₁ y₂ = (y₁ - y₂) / (x₁ - x₂) := by
  simp only [WeierstrassCurve.Affine.slope, if_neg hx]

/-- Mathlib's affine `addX` specialised to Montgomery. -/
lemma montgomeryW_addX (A x₁ x₂ ℓ : F) :
    (montgomeryW A).toAffine.addX x₁ x₂ ℓ = ℓ^2 - A - x₁ - x₂ := by
  simp only [WeierstrassCurve.Affine.addX, montgomeryW_a₁, montgomeryW_a₂]
  ring

/-- **`xdadd_spec` on `(montgomeryW A).toAffine.Point`.** The x-only
    differential-addition formula `xdadd` computes the projective
    x-coordinate of `P + Q`, given the difference `P - Q`. Covers
    all cases including `P = 0`, `Q = 0`, `P = ±Q`, and generic. -/
theorem xdadd_spec_W [DecidableEq F] (h2 : (2 : F) ≠ 0) (A : F)
    (P Q : (montgomeryW A).toAffine.Point) :
    (xdadd (xProjW A P) (xProjW A Q) (xProjW A (P - Q))).1 * (xProjW A (P + Q)).2
      = (xProjW A (P + Q)).1
          * (xdadd (xProjW A P) (xProjW A Q) (xProjW A (P - Q))).2 := by
  obtain (_ | @⟨xp, yp, hP⟩) := P
  · -- P = zero: P + Q = Q, P - Q = -Q
    obtain (_ | @⟨xq, yq, hQ⟩) := Q
    · -- Q = zero
      simp [xProjW, xdadd]
    · -- Q = some; P + Q = Q, P - Q = -Q
      rw [show (WeierstrassCurve.Affine.Point.zero : (montgomeryW A).toAffine.Point)
              + WeierstrassCurve.Affine.Point.some xq yq hQ =
            WeierstrassCurve.Affine.Point.some xq yq hQ from zero_add _,
          show (WeierstrassCurve.Affine.Point.zero : (montgomeryW A).toAffine.Point)
              - WeierstrassCurve.Affine.Point.some xq yq hQ =
            -WeierstrassCurve.Affine.Point.some xq yq hQ from zero_sub _,
          WeierstrassCurve.Affine.Point.neg_some]
      simp only [xProjW_some, xProjW_zero, xdadd, montgomeryW_negY]
      ring
  · -- P = some hP
    obtain (_ | @⟨xq, yq, hQ⟩) := Q
    · -- Q = zero
      rw [show WeierstrassCurve.Affine.Point.some xp yp hP +
            (WeierstrassCurve.Affine.Point.zero : (montgomeryW A).toAffine.Point) =
            WeierstrassCurve.Affine.Point.some xp yp hP from add_zero _,
          show WeierstrassCurve.Affine.Point.some xp yp hP -
            (WeierstrassCurve.Affine.Point.zero : (montgomeryW A).toAffine.Point) =
            WeierstrassCurve.Affine.Point.some xp yp hP from sub_zero _]
      simp only [xProjW_some, xProjW_zero, xdadd]
      ring
    · -- Both P, Q nonzero. Case on xp = xq.
      by_cases hx : xp = xq
      · -- xp = xq
        subst hx
        -- xdadd (xp, 1) (xp, 1) XD: DA = CB, so DA - CB = 0, so xdadd.2 = 0 regardless of XD.
        have hxd2 : ∀ (xd : F × F), (xdadd (xp, 1) (xp, 1) xd).2 = 0 := by
          intro xd; obtain ⟨xD, ZD⟩ := xd; simp only [xdadd]; ring
        simp only [xProjW_some, hxd2, mul_zero]
        by_cases hy : yp = -yq
        · -- P = -Q: P + Q = 0, xProjW(P+Q) = (1, 0), Za = 0.
          have h_eqNeg : WeierstrassCurve.Affine.Point.some xp yp hP +
              WeierstrassCurve.Affine.Point.some xp yq hQ = 0 := by
            apply WeierstrassCurve.Affine.Point.add_of_Y_eq rfl
            rw [montgomeryW_negY]; exact hy
          rw [h_eqNeg,
              show ((0 : (montgomeryW A).toAffine.Point))
                     = WeierstrassCurve.Affine.Point.zero from rfl,
              xProjW_zero]
          ring
        · -- yp ≠ -yq: yp = yq from curve equation, so P = Q, P - Q = 0,
          --   and xProjW(P - Q) = (1, 0), ZD = 0, so xdadd.1 = 0.
          have hy' : yp = yq := by
            have hyp_sq : yp^2 = xp^3 + A * xp^2 + xp :=
              (montgomeryW_equation A xp yp).mp hP.1
            have hyq_sq : yq^2 = xp^3 + A * xp^2 + xp :=
              (montgomeryW_equation A xp yq).mp hQ.1
            have hsq : (yp - yq) * (yp + yq) = 0 := by
              linear_combination hyp_sq - hyq_sq
            rcases mul_eq_zero.mp hsq with h | h
            · exact sub_eq_zero.mp h
            · exfalso; apply hy; linear_combination h
          subst hy'
          have h_sub : WeierstrassCurve.Affine.Point.some xp yp hP -
              WeierstrassCurve.Affine.Point.some xp yp hQ = 0 := by
            rw [show hQ = hP from Subsingleton.elim _ _, sub_self]
          have h_XProjSub :
              xProjW A (WeierstrassCurve.Affine.Point.some xp yp hP -
                  WeierstrassCurve.Affine.Point.some xp yp hQ) = (1, 0) := by
            rw [h_sub,
                show ((0 : (montgomeryW A).toAffine.Point))
                       = WeierstrassCurve.Affine.Point.zero from rfl,
                xProjW_zero]
          rw [h_XProjSub]
          have hxd1 : (xdadd (xp, 1) (xp, 1) (1, 0)).1 = 0 := by
            simp only [xdadd]; ring
          rw [hxd1, zero_mul]
      · -- xp ≠ xq: generic case
        have hxne : xp ≠ xq := hx
        have hxne' : xq - xp ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
        have hpmq_ne : xp - xq ≠ 0 := sub_ne_zero.mpr hxne
        rw [WeierstrassCurve.Affine.Point.add_of_X_ne hxne, sub_eq_add_neg,
            WeierstrassCurve.Affine.Point.neg_some,
            WeierstrassCurve.Affine.Point.add_of_X_ne hxne]
        simp only [xProjW_some, montgomeryW_addX]
        rw [montgomeryW_slope_secant A xp xq yp yq hxne, montgomeryW_negY,
            montgomeryW_slope_secant A xp xq yp (-yq) hxne]
        rw [xdadd_normalised, mul_one]
        have hCurveP : yp^2 = xp^3 + A * xp^2 + xp :=
          (montgomeryW_equation A xp yp).mp hP.1
        have hCurveQ : yq^2 = xq^3 + A * xq^2 + xq :=
          (montgomeryW_equation A xq yq).mp hQ.1
        -- Goal is now in clean form; use xdadd_affine_identity after clearing denoms.
        have hxp_sq_ne : (xp - xq)^2 ≠ 0 := pow_ne_zero _ hpmq_ne
        have hxq_sq_ne : (xq - xp)^2 ≠ 0 := pow_ne_zero _ hxne'
        field_simp
        linear_combination
          -(xq - xp)^2 * xdadd_affine_identity A xp yp xq yq hCurveP hCurveQ

/-! ## MontyCurveGroup instance for WeierstrassCurve.Affine.Point -/

/-- **Main packaging.** The Weierstrass-curve group on `(montgomeryW A).toAffine.Point`,
    together with the x-coordinate map `xProjW A`, satisfies the
    `MontyCurveGroup` specification for the Montgomery x-only formulas.

    Hypotheses are `h2 : (2 : F) ≠ 0` (excludes char-2 fields, where Montgomery
    form is degenerate) and `h24 : 4 * a24 = A + 2` (definition of `a24`). -/
def montgomeryW_MontyCurveGroup [DecidableEq F] (h2 : (2 : F) ≠ 0)
    (A a24 : F) (h24 : 4 * a24 = A + 2) :
    MontyCurveGroup F ⟨A, a24⟩ ((montgomeryW A).toAffine.Point) where
  xProj := xProjW A
  xdbl_spec := xdbl_spec_W h2 A a24 h24
  xdadd_spec := xdadd_spec_W h2 A

end CatCrypt.Crypto.ECC
