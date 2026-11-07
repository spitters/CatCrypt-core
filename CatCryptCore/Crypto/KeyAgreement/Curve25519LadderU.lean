/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.KeyAgreement.Curve25519Subgroup
public import CatCryptCore.Crypto.KeyAgreement.X25519Spec
public import CatCryptCore.ForMathlib.UInt8Bytes

/-!
# The x-only ladder computes the u-coordinate of every multiple

For every point `P` of Curve25519 and every list of bits, the field-level x-only ladder
`xladderFold a24 (uCoord P, 1) bits` ends in a first component `(X, Z)` with
`X * Z⁻¹ = uCoord (bitsToNat bits • P)`. No hypothesis on the order of `P` or on the size of
the scalar enters. As a consequence, the X25519 function `Spec.x25519_spec` of RFC 7748
computes clamped scalar multiplication on u-coordinates.

## Nondegeneracy

`LadderNondeg P bits` holds for every `P` with `uCoord P ≠ 0` and every list of bits
(`curve25519_LadderNondeg`). `xdbl` is nondegenerate at the projective x-coordinate of every
point (`curve25519_xdbl_nondeg`). The differential addition of the ladder is nondegenerate at
every scalar `n` (`curve25519_xdadd_ladder_nondeg`): a degenerate output forces
`uCoord (n • P) = uCoord ((n + 1) • P) = ±1`, hence `(2n + 1) • P = 0` and `(4n) • P = 0`,
and `2n + 1` is coprime to `4n`.

## The invariant read off

`ProjMul p q` states that `p` is a nonzero multiple of `q`. Both `xdbl` and `xdadd` are
homogeneous, so the ladder state is a nonzero multiple of the projective x-coordinates of
`(n • P, (n + 1) • P)` (`xladderFold_projMul`), which determines `X * Z⁻¹`. At `uCoord P = 0`
every ladder component has `X * Z = 0`, and every multiple of `P` has u-coordinate `0`.

## Main results

* `curve25519_LadderNondeg` — ladder nondegeneracy at every point with `uCoord P ≠ 0`
* `xladderFold_uCoord` — the ladder computes `uCoord (bitsToNat bits • P)` for every `P`
* `bitsToNat_scalarBits` — the ladder bits of `sk` represent `clampScalar (natOfLeBytes sk)`
* `x25519_spec_uCoord` — `x25519_spec sk` maps the encoding of `uCoord P` to the encoding of
  `uCoord (clampScalar (natOfLeBytes sk) • P)`, for every point `P`
* `x25519_spec_encU`, `x25519_base_spec_encU` — the same on the subgroup `G25519 B`, and the
  base-point function at a point `B` with `uCoord B = 9`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.ECC

open CatCrypt.Crypto.KeyAgreement.X25519

/-! ## Projective x-coordinates of points -/

/-- The projective x-coordinate of every point is nondegenerate. -/
theorem curve25519_xProj_nondeg (Q : Curve25519Point) :
    (curve25519_MontyCurveGroup.xProj Q).1 ≠ 0 ∨ (curve25519_MontyCurveGroup.xProj Q).2 ≠ 0 := by
  obtain (_ | ⟨x, y, h⟩) := Q
  · left
    rw [curve25519_xProj_eq, xProjW_zero]
    exact one_ne_zero
  · right
    rw [curve25519_xProj_eq, xProjW_some]
    exact one_ne_zero

/-- The projective x-coordinate of a point other than the identity is `(uCoord P, 1)`. -/
theorem xProj_eq_uCoord {P : Curve25519Point} (hP : P ≠ 0) :
    curve25519_MontyCurveGroup.xProj P = (uCoord P, 1) := by
  obtain (_ | ⟨x, y, h⟩) := P
  · exact absurd rfl hP
  · simp [uCoord, curve25519_xProj_eq, xProjW_some]

/-- A point with nonzero u-coordinate is not the identity. -/
theorem ne_zero_of_uCoord_ne_zero {P : Curve25519Point} (hu : uCoord P ≠ 0) : P ≠ 0 := by
  rintro rfl
  exact hu uCoord_zero

/-- Two points other than the identity with the same u-coordinate are equal or opposite. -/
theorem eq_or_eq_neg_of_uCoord_eq_of_ne_zero {P Q : Curve25519Point} (hP : P ≠ 0)
    (hQ : Q ≠ 0) (h : uCoord P = uCoord Q) : P = Q ∨ P = -Q := by
  obtain (_ | ⟨x, y, hxy⟩) := P
  · exact absurd rfl hP
  obtain (_ | ⟨x', y', hxy'⟩) := Q
  · exact absurd rfl hQ
  simp only [uCoord, curve25519_xProj_eq, xProjW_some, inv_one, mul_one] at h
  rcases WeierstrassCurve.Affine.Y_eq_of_X_eq hxy.1 hxy'.1 h with hy | hy
  · left; subst h; subst hy; rfl
  · right
    rw [WeierstrassCurve.Affine.Point.neg_some]
    simp only [h, hy]

/-- Every multiple of a point with u-coordinate `0` has u-coordinate `0`: such a point is the
identity or the point `(0, 0)` of order two. -/
theorem uCoord_nsmul_of_uCoord_eq_zero {P : Curve25519Point} (hu : uCoord P = 0) (n : ℕ) :
    uCoord (n • P) = 0 := by
  have h2 : P + P = 0 := by
    obtain (_ | ⟨x, y, h⟩) := P
    · rfl
    · apply curve25519_double_eq_zero_of_xProj_fst_zero
      simpa [uCoord, curve25519_xProj_eq, xProjW_some] using hu
  have key : ∀ m : ℕ, m • P = 0 ∨ m • P = P := by
    intro m
    induction m with
    | zero => exact Or.inl (zero_nsmul P)
    | succ m ih =>
        rw [succ_nsmul]
        rcases ih with h | h
        · right; rw [h, zero_add]
        · left; rw [h, h2]
  rcases key n with h | h
  · rw [h, uCoord_zero]
  · rw [h, hu]

/-! ## Nondegeneracy of the ladder -/

/-- **`xdbl` is nondegenerate at every point.** At `(x, 1)` the first output `(x² − 1)²`
vanishes only at `x = ±1`, where the second output is `16 · a24` or `16 · a24 − 16`. -/
theorem curve25519_xdbl_nondeg (Q : Curve25519Point) :
    (xdbl (curve25519Params Fp25519).a24 (curve25519_MontyCurveGroup.xProj Q)).1 ≠ 0 ∨
      (xdbl (curve25519Params Fp25519).a24 (curve25519_MontyCurveGroup.xProj Q)).2 ≠ 0 := by
  obtain (_ | ⟨x, y, h⟩) := Q
  · left
    rw [curve25519_xProj_eq, xProjW_zero, xdbl_one_zero]
    exact one_ne_zero
  · rw [curve25519_xProj_eq, xProjW_some]
    by_cases hx : (xdbl (curve25519Params Fp25519).a24 (x, 1)).1 = 0
    · right
      rw [xdbl_numerator] at hx
      have hsub : x ^ 2 - 1 = 0 := (pow_eq_zero_iff (by norm_num)).mp hx
      have hfac : (x - 1) * (x + 1) = 0 := by linear_combination hsub
      rcases mul_eq_zero.mp hfac with h1 | h1
      · rw [sub_eq_zero.mp h1, xdbl_one_one]
        exact fp25519_sixteen_a24_ne_zero
      · rw [add_eq_zero_iff_eq_neg.mp h1, xdbl_neg_one_one]
        exact fp25519_sixteen_a24_sub_ne_zero
    · exact Or.inl hx

/-- **The differential addition of the ladder is nondegenerate at every scalar**, for a
difference `P` with `uCoord P ≠ 0`. -/
theorem curve25519_xdadd_ladder_nondeg (P : Curve25519Point) (hu : uCoord P ≠ 0) (n : ℕ) :
    (xdadd (curve25519_MontyCurveGroup.xProj (n • P))
        (curve25519_MontyCurveGroup.xProj ((n + 1) • P))
        (curve25519_MontyCurveGroup.xProj P)).1 ≠ 0 ∨
    (xdadd (curve25519_MontyCurveGroup.xProj (n • P))
        (curve25519_MontyCurveGroup.xProj ((n + 1) • P))
        (curve25519_MontyCurveGroup.xProj P)).2 ≠ 0 := by
  have hP := ne_zero_of_uCoord_ne_zero hu
  have hxP := xProj_eq_uCoord hP
  have hsucc : (n + 1) • P = n • P + P := succ_nsmul P n
  have h2u : (2 * uCoord P) ^ 2 ≠ 0 := pow_ne_zero _ (mul_ne_zero fp25519_two_ne_zero hu)
  by_cases h0 : n • P = 0
  · left
    rw [hsucc, h0, zero_add, hxP, curve25519_xProj_eq,
      show (0 : Curve25519Point) = .zero from rfl, xProjW_zero]
    simp only [xdadd]
    convert h2u using 1
    ring
  by_cases h1 : (n + 1) • P = 0
  · left
    have hneg : n • P = -P := eq_neg_of_add_eq_zero_left (hsucc ▸ h1)
    rw [h1, hneg, curve25519_xProj_neg, hxP, curve25519_xProj_eq,
      show (0 : Curve25519Point) = .zero from rfl, xProjW_zero]
    simp only [xdadd]
    convert h2u using 1
    ring
  rw [xProj_eq_uCoord h0, xProj_eq_uCoord h1, hxP]
  set x0 := uCoord (n • P) with hx0
  set x1 := uCoord ((n + 1) • P) with hx1
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨hc1, hc2⟩ := hcon
  have e1 : (xdadd (x0, 1) (x1, 1) (uCoord P, 1)).1 = (2 * (x0 * x1 - 1)) ^ 2 := by
    simp only [xdadd]; ring
  have e2 : (xdadd (x0, 1) (x1, 1) (uCoord P, 1)).2 = uCoord P * (2 * (x0 - x1)) ^ 2 := by
    simp only [xdadd]; ring
  rw [e1] at hc1
  rw [e2] at hc2
  have hx01 : x0 = x1 := by
    rcases mul_eq_zero.mp hc2 with h | h
    · exact absurd h hu
    · rcases mul_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h) with h' | h'
      · exact absurd h' fp25519_two_ne_zero
      · exact sub_eq_zero.mp h'
  have hsq : (x0 - 1) * (x0 + 1) = 0 := by
    rcases mul_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hc1) with h' | h'
    · exact absurd h' fp25519_two_ne_zero
    · rw [← hx01] at h'; linear_combination h'
  -- `n • P` has u-coordinate `±1`, so it is a 4-torsion point.
  have h4 : (4 * n) • P = 0 := by
    rw [show 4 * n = (n + n) + (n + n) by ring, add_nsmul, add_nsmul]
    rcases mul_eq_zero.mp hsq with h' | h'
    · exact curve25519_quad_eq_zero_of_xProj_one _ (by
        rw [xProj_eq_uCoord h0, ← hx0, sub_eq_zero.mp h'])
    · exact curve25519_quad_eq_zero_of_xProj_neg_one _ (by
        rw [xProj_eq_uCoord h0, ← hx0, add_eq_zero_iff_eq_neg.mp h'])
  -- Equal u-coordinates: `(n + 1) • P = ± n • P`.
  have h2n1 : (2 * n + 1) • P = 0 := by
    rcases eq_or_eq_neg_of_uCoord_eq_of_ne_zero h1 h0 hx01.symm with h' | h'
    · exact absurd (by rw [hsucc] at h'; simpa using h') hP
    · rw [show 2 * n + 1 = (n + 1) + n by ring, add_nsmul, h', neg_add_cancel]
  apply hP
  have hd1 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h2n1
  have hd2 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h4
  -- `2n + 1` is odd and coprime to `n`, hence to `4n`.
  have hcop : Nat.Coprime (2 * n + 1) (4 * n) := by
    have hodd : Nat.Coprime (2 * n + 1) 2 := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      omega
    have h4 : Nat.Coprime (2 * n + 1) 4 := by simpa using Nat.Coprime.pow_right 2 hodd
    exact Nat.Coprime.mul_right h4
      ((Nat.coprime_mul_right_add_left 1 n 2).mpr (Nat.coprime_one_left n))
  have hd := Nat.dvd_gcd hd1 hd2
  rw [Nat.Coprime.gcd_eq_one hcop] at hd
  exact AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)

/-- **Ladder nondegeneracy at every point with nonzero u-coordinate**, for every list of
bits: the scalar range is not restricted. -/
theorem curve25519_LadderNondeg (P : Curve25519Point) (hu : uCoord P ≠ 0)
    (bits : List Bool) : LadderNondeg P bits := by
  intro n _
  have hd : curve25519_MontyCurveGroup.xProj (n • P - (n + 1) • P)
      = curve25519_MontyCurveGroup.xProj P := by
    rw [show n • P - (n + 1) • P = -P by rw [succ_nsmul, sub_add_eq_sub_sub, sub_self, zero_sub]]
    exact curve25519_xProj_neg P
  refine ⟨curve25519_xdbl_nondeg _, curve25519_xdbl_nondeg _, ?_⟩
  rw [hd]
  exact curve25519_xdadd_ladder_nondeg P hu n

/-! ## Nonzero multiples of projective pairs -/

section ProjMul

variable {F : Type*} [Field F]

/-- `p` is a nonzero multiple of `q`. -/
def ProjMul (p q : F × F) : Prop :=
  ∃ c : F, c ≠ 0 ∧ p = (c * q.1, c * q.2)

theorem ProjMul.refl (p : F × F) : ProjMul p p :=
  ⟨1, one_ne_zero, by simp⟩

theorem ProjMul.trans {p q r : F × F} (hpq : ProjMul p q) (hqr : ProjMul q r) :
    ProjMul p r := by
  obtain ⟨c, hc, rfl⟩ := hpq
  obtain ⟨d, hd, rfl⟩ := hqr
  exact ⟨c * d, mul_ne_zero hc hd, by simp only [mul_assoc]⟩

/-- Projectively equivalent nondegenerate pairs are nonzero multiples of each other. -/
theorem ProjMul.of_projEquiv {p q : F × F} (h : ProjEquiv p q) (hp : p.1 ≠ 0 ∨ p.2 ≠ 0)
    (hq : q.1 ≠ 0 ∨ q.2 ≠ 0) : ProjMul p q := by
  unfold ProjEquiv at h
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  simp only at h hp hq ⊢
  by_cases hq2 : q2 = 0
  · subst hq2
    have hq1 : q1 ≠ 0 := hq.resolve_right (by simp)
    have hp2 : p2 = 0 := by
      rw [mul_zero] at h
      exact (mul_eq_zero.mp h.symm).resolve_left hq1
    subst hp2
    have hp1 : p1 ≠ 0 := hp.resolve_right (by simp)
    exact ⟨p1 * q1⁻¹, mul_ne_zero hp1 (inv_ne_zero hq1), by
      refine Prod.ext ?_ ?_ <;> simp [hq1]⟩
  · have hp2 : p2 ≠ 0 := by
      rintro rfl
      rw [mul_zero] at h
      exact hp.resolve_right (by simp) ((mul_eq_zero.mp h).resolve_right hq2)
    refine ⟨p2 * q2⁻¹, mul_ne_zero hp2 (inv_ne_zero hq2), Prod.ext ?_ ?_⟩
    · simp only
      field_simp
      linear_combination h
    · simp [hq2]

/-- A nonzero multiple has the same ratio `X * Z⁻¹`. -/
theorem ProjMul.ratio_eq {p q : F × F} (h : ProjMul p q) : p.1 * p.2⁻¹ = q.1 * q.2⁻¹ := by
  obtain ⟨c, hc, rfl⟩ := h
  simp only
  rw [mul_inv, mul_mul_mul_comm, mul_inv_cancel₀ hc, one_mul]

/-- `xdbl` is homogeneous of degree `4`. -/
theorem xdbl_projMul (a24 : F) {p q : F × F} (h : ProjMul p q) :
    ProjMul (xdbl a24 p) (xdbl a24 q) := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨c ^ 4, pow_ne_zero _ hc, ?_⟩
  simp only [xdbl]
  refine Prod.ext ?_ ?_ <;> simp only <;> ring

/-- `xdadd` is homogeneous of degree `2` in each of its first two arguments. -/
theorem xdadd_projMul {p p' q q' : F × F} (d : F × F) (hp : ProjMul p p') (hq : ProjMul q q') :
    ProjMul (xdadd p q d) (xdadd p' q' d) := by
  obtain ⟨c, hc, rfl⟩ := hp
  obtain ⟨c', hc', rfl⟩ := hq
  refine ⟨(c * c') ^ 2, pow_ne_zero _ (mul_ne_zero hc hc'), ?_⟩
  simp only [xdadd]
  refine Prod.ext ?_ ?_ <;> simp only <;> ring

end ProjMul

/-! ## The ladder invariant up to nonzero multiples -/

/-- The ladder state is a nonzero multiple of the projective x-coordinates of
`(n • P, (n + 1) • P)`. -/
def XLadderInvM (P : Curve25519Point) (n : ℕ) (st : (Fp25519 × Fp25519) × (Fp25519 × Fp25519)) :
    Prop :=
  ProjMul st.1 (curve25519_MontyCurveGroup.xProj (n • P)) ∧
    ProjMul st.2 (curve25519_MontyCurveGroup.xProj ((n + 1) • P))

/-- `xdbl` of a nonzero multiple of `xProj Q` is a nonzero multiple of `xProj (Q + Q)`. -/
theorem projMul_xdbl_xProj {r : Fp25519 × Fp25519} {Q : Curve25519Point}
    (hr : ProjMul r (curve25519_MontyCurveGroup.xProj Q)) :
    ProjMul (xdbl (curve25519Params Fp25519).a24 r) (curve25519_MontyCurveGroup.xProj (Q + Q)) :=
  (xdbl_projMul _ hr).trans (ProjMul.of_projEquiv (curve25519_MontyCurveGroup.xdbl_spec Q)
    (curve25519_xdbl_nondeg Q) (curve25519_xProj_nondeg _))

/-- The differential addition step of the ladder at the difference `P`. -/
theorem projMul_xdadd_xProj (P : Curve25519Point) (hu : uCoord P ≠ 0) (n : ℕ)
    {r s : Fp25519 × Fp25519} (hr : ProjMul r (curve25519_MontyCurveGroup.xProj (n • P)))
    (hs : ProjMul s (curve25519_MontyCurveGroup.xProj ((n + 1) • P))) :
    ProjMul (xdadd r s (curve25519_MontyCurveGroup.xProj P))
      (curve25519_MontyCurveGroup.xProj (n • P + (n + 1) • P)) := by
  have hd : curve25519_MontyCurveGroup.xProj (n • P - (n + 1) • P)
      = curve25519_MontyCurveGroup.xProj P := by
    rw [show n • P - (n + 1) • P = -P by rw [succ_nsmul, sub_add_eq_sub_sub, sub_self, zero_sub]]
    exact curve25519_xProj_neg P
  have hspec := curve25519_MontyCurveGroup.xdadd_spec (n • P) ((n + 1) • P)
  rw [hd] at hspec
  exact (xdadd_projMul _ hr hs).trans (ProjMul.of_projEquiv hspec
    (curve25519_xdadd_ladder_nondeg P hu n) (curve25519_xProj_nondeg _))

/-- **One ladder step preserves the invariant up to nonzero multiples.** -/
theorem xladderStep_invM (P : Curve25519Point) (hu : uCoord P ≠ 0) (n : ℕ)
    (st : (Fp25519 × Fp25519) × (Fp25519 × Fp25519)) (b : Bool) (h : XLadderInvM P n st) :
    XLadderInvM P (2 * n + (if b then 1 else 0))
      (xladderStep (curve25519Params Fp25519).a24 (curve25519_MontyCurveGroup.xProj P) st b) := by
  obtain ⟨h0, h1⟩ := h
  have hadd := projMul_xdadd_xProj P hu n h0 h1
  cases b
  · refine ⟨?_, ?_⟩
    · show ProjMul (xdbl _ st.1) (curve25519_MontyCurveGroup.xProj ((2 * n + 0) • P))
      rw [show (2 * n + 0) • P = n • P + n • P by rw [Nat.add_zero, two_mul, add_nsmul]]
      exact projMul_xdbl_xProj h0
    · show ProjMul (xdadd st.1 st.2 _) (curve25519_MontyCurveGroup.xProj ((2 * n + 0 + 1) • P))
      rw [show (2 * n + 0 + 1) • P = n • P + (n + 1) • P by
        rw [Nat.add_zero, show 2 * n + 1 = n + (n + 1) by omega, add_nsmul]]
      exact hadd
  · refine ⟨?_, ?_⟩
    · show ProjMul (xdadd st.1 st.2 _) (curve25519_MontyCurveGroup.xProj ((2 * n + 1) • P))
      rw [show (2 * n + 1) • P = n • P + (n + 1) • P by
        rw [show 2 * n + 1 = n + (n + 1) by omega, add_nsmul]]
      exact hadd
    · show ProjMul (xdbl _ st.2) (curve25519_MontyCurveGroup.xProj ((2 * n + 1 + 1) • P))
      rw [show (2 * n + 1 + 1) • P = (n + 1) • P + (n + 1) • P by
        rw [show 2 * n + 1 + 1 = (n + 1) + (n + 1) by omega, add_nsmul]]
      exact projMul_xdbl_xProj h1

/-- **The ladder state is a nonzero multiple of the projective x-coordinates** of
`(k • P, (k + 1) • P)`, `k = bitsToNat bits`, for every `P` with `uCoord P ≠ 0`. -/
theorem xladderFold_projMul (P : Curve25519Point) (hu : uCoord P ≠ 0) (bits : List Bool) :
    XLadderInvM P (bitsToNat bits)
      (xladderFold (curve25519Params Fp25519).a24 (curve25519_MontyCurveGroup.xProj P) bits) := by
  induction bits with
  | nil =>
      refine ⟨?_, ?_⟩
      · show ProjMul (1, 0) (curve25519_MontyCurveGroup.xProj (0 • P))
        rw [zero_nsmul, curve25519_xProj_eq, show (0 : Curve25519Point) = .zero from rfl,
          xProjW_zero]
        exact ProjMul.refl _
      · show ProjMul _ (curve25519_MontyCurveGroup.xProj ((0 + 1) • P))
        rw [zero_add, one_nsmul]
        exact ProjMul.refl _
  | cons b bs ih => exact xladderStep_invM P hu (bitsToNat bs) _ b ih

/-! ## The ladder at the difference `(0, 1)` -/

/-- With the difference `(0, 1)`, every component `(X, Z)` of the ladder has `X * Z = 0`. -/
theorem xladderFold_zero_one (a24 : Fp25519) (bits : List Bool) :
    (xladderFold a24 (0, 1) bits).1.1 * (xladderFold a24 (0, 1) bits).1.2 = 0 ∧
      (xladderFold a24 (0, 1) bits).2.1 * (xladderFold a24 (0, 1) bits).2.2 = 0 := by
  have hdbl : ∀ r : Fp25519 × Fp25519, r.1 * r.2 = 0 →
      (xdbl a24 r).1 * (xdbl a24 r).2 = 0 := by
    rintro ⟨X, Z⟩ h
    have e : (xdbl a24 (X, Z)).1 * (xdbl a24 (X, Z)).2 =
        (X * Z) * (4 * ((X + Z) ^ 2 * (X - Z) ^ 2) * ((X - Z) * (X - Z) +
          a24 * ((X + Z) * (X + Z) - (X - Z) * (X - Z)))) := by
      simp only [xdbl]; ring
    rw [e, show X * Z = 0 from h, zero_mul]
  have hadd : ∀ r s : Fp25519 × Fp25519, (xdadd r s (0, 1)).1 * (xdadd r s (0, 1)).2 = 0 := by
    intro r s
    simp only [xdadd, zero_mul, mul_zero]
  induction bits with
  | nil => simp [xladderFold]
  | cons b bs ih =>
      obtain ⟨h1, h2⟩ := ih
      cases b
      · exact ⟨hdbl _ h1, hadd _ _⟩
      · exact ⟨hadd _ _, hdbl _ h2⟩

/-! ## The ladder computes the u-coordinate -/

/-- **The x-only ladder computes the u-coordinate of every multiple.** For every point `P` and
every list of bits, the first component `(X, Z)` of `xladderFold a24 (uCoord P, 1) bits` has
`X * Z⁻¹ = uCoord (bitsToNat bits • P)`. -/
theorem xladderFold_uCoord (P : Curve25519Point) (bits : List Bool) :
    (xladderFold (curve25519Params Fp25519).a24 (uCoord P, 1) bits).1.1 *
        (xladderFold (curve25519Params Fp25519).a24 (uCoord P, 1) bits).1.2⁻¹ =
      uCoord (bitsToNat bits • P) := by
  by_cases hu : uCoord P = 0
  · rw [uCoord_nsmul_of_uCoord_eq_zero hu, hu]
    rcases mul_eq_zero.mp (xladderFold_zero_one (curve25519Params Fp25519).a24 bits).1
      with h | h <;> simp [h]
  · rw [← xProj_eq_uCoord (ne_zero_of_uCoord_ne_zero hu)]
    exact (xladderFold_projMul P hu bits).1.ratio_eq

/-! ## Codecs and clamping -/

/-- The byte decoding of the specification is `natOfLeBytes`. -/
theorem bytesToNat_eq_natOfLeBytes (b : Vector UInt8 32) :
    Spec.bytesToNat b = natOfLeBytes b := by
  rw [Spec.bytesToNat, natOfLeBytes, Fin.sum_univ_def, List.sum_eq_foldl, List.foldl_map]
  congr 1
  funext acc i
  rw [pow_mul]
  rfl

/-- The byte encoding of the specification is `leBytesOfNat`. -/
theorem natToBytes_eq_leBytesOfNat (n : ℕ) : Spec.natToBytes n = leBytesOfNat n := by
  unfold Spec.natToBytes leBytesOfNat
  congr 1
  funext i
  rw [pow_mul]
  apply UInt8.toNat_inj.mp
  simp

/-- The u-coordinate encoding of the specification is `leBytesOfNat` of the canonical
representative. -/
theorem encodeUCoord_eq (u : Fp25519) : Spec.encodeUCoord u = leBytesOfNat u.val :=
  natToBytes_eq_leBytesOfNat u.val

/-- Decoding the bytes of a number below `2 ^ 255` gives the number: the mask of bit 255 is
inert. -/
theorem decodeUCoord_leBytesOfNat {n : ℕ} (hn : n < 2 ^ 255) :
    Spec.decodeUCoord (leBytesOfNat n) = (n : Fp25519) := by
  have h31 : (leBytesOfNat n)[31] &&& (127 : UInt8) = (leBytesOfNat n)[31] := by
    have hlt : n / 256 ^ 31 < 128 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      calc n < 2 ^ 255 := hn
        _ = 128 * 256 ^ 31 := by norm_num
    simp only [leBytesOfNat, Vector.getElem_ofFn]
    exact UInt8.ofNat_and_127_of_lt hlt
  have hm : (Vector.ofFn fun i : Fin 32 =>
      if i = ⟨31, by omega⟩ then (leBytesOfNat n)[31] &&& (127 : UInt8)
      else (leBytesOfNat n)[i.val]) = leBytesOfNat n := by
    ext i hi
    simp only [Vector.getElem_ofFn]
    split_ifs with h
    · rw [h31]; simp only [Fin.ext_iff] at h; subst h; rfl
    · rfl
  unfold Spec.decodeUCoord
  dsimp only
  rw [hm, bytesToNat_eq_natOfLeBytes, natOfLeBytes_leBytesOfNat,
    Nat.mod_eq_of_lt (lt_trans hn (by norm_num))]

/-- The canonical representative of a field element is below `2 ^ 255`. -/
theorem fp25519_val_lt (u : Fp25519) : u.val < 2 ^ 255 :=
  lt_of_lt_of_le (ZMod.val_lt u) (show curve25519Prime ≤ 2 ^ 255 from Nat.sub_le _ _)

/-- Decoding the encoding of a field element gives the element. -/
theorem decodeUCoord_leBytesOfNat_val (u : Fp25519) :
    Spec.decodeUCoord (leBytesOfNat u.val) = u := by
  rw [decodeUCoord_leBytesOfNat (fp25519_val_lt u), ZMod.natCast_zmod_val]

/-- `natOfLeBytes` split at the first and the last byte. -/
theorem natOfLeBytes_split (v : Vector UInt8 32) :
    natOfLeBytes v = v[0].toNat + 256 * (∑ i : Fin 30, v[i.val + 1].toNat * 256 ^ i.val) +
      256 ^ 31 * v[31].toNat := by
  rw [natOfLeBytes, Fin.sum_univ_succ, Fin.sum_univ_castSucc, Finset.mul_sum]
  simp only [Fin.getElem_fin, Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last,
    pow_zero, mul_one]
  rw [add_assoc]
  refine congrArg (_ + ·) (congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_) ?_) <;> ring

/-- The byte clamp of the specification is `clampScalar` on numbers. -/
theorem natOfLeBytes_clamp (sk : Vector UInt8 32) :
    natOfLeBytes (Spec.clamp sk) = clampScalar (natOfLeBytes sk) := by
  have hmid : ∀ i : Fin 30, (Spec.clamp sk)[i.val + 1] = sk[i.val + 1] := by
    intro i
    simp only [Spec.clamp, Vector.getElem_ofFn, Fin.mk.injEq,
      show (i : ℕ) + 1 ≠ 0 by omega, show (i : ℕ) + 1 ≠ 31 by omega, ↓reduceIte]
  have h0 : ((Spec.clamp sk)[0]).toNat = 8 * (sk[0].toNat / 8) := by
    simp only [Spec.clamp, Vector.getElem_ofFn, ↓reduceIte]
    exact UInt8.toNat_and_248 _
  have h31 : ((Spec.clamp sk)[31]).toNat = 64 + sk[31].toNat % 64 := by
    simp only [Spec.clamp, Vector.getElem_ofFn, Fin.mk.injEq, show (31 : ℕ) ≠ 0 by omega,
      ↓reduceIte]
    exact UInt8.toNat_and_127_or_64 _
  have ha : sk[0].toNat < 256 := UInt8.toNat_lt _
  have hc : sk[31].toNat < 256 := UInt8.toNat_lt _
  rw [clampScalar_eq _ (natOfLeBytes_lt sk), natOfLeBytes_split (Spec.clamp sk),
    natOfLeBytes_split sk, h0, h31]
  simp only [hmid]
  generalize hMdef : (∑ i : Fin 30, sk[i.val + 1].toNat * 256 ^ i.val) = M
  generalize sk[0].toNat = a at ha ⊢
  generalize sk[31].toNat = c at hc ⊢
  have hM : M < 2 ^ 240 := hMdef ▸ lt_of_lt_of_eq (Fin.sum_toNat_mul_256_pow_lt _) (by norm_num)
  omega

/-- **The ladder bits of `sk` represent the clamped scalar** `clampScalar (natOfLeBytes sk)`. -/
theorem bitsToNat_scalarBits (sk : Vector UInt8 32) :
    bitsToNat (Spec.scalarBits sk) = clampScalar (natOfLeBytes sk) := by
  rw [Spec.scalarBits, Spec.bitsToNat_reverse_bitsOfMSB, bytesToNat_eq_natOfLeBytes,
    natOfLeBytes_clamp, Nat.mod_eq_of_lt (clampScalar_bounds _).2]

/-! ## The X25519 function computes clamped scalar multiplication -/

/-- **The X25519 function computes clamped scalar multiplication on u-coordinates**, for every
point `P` of Curve25519 and every 32-byte key `sk`. -/
theorem x25519_spec_uCoord (sk : Vector UInt8 32) (P : Curve25519Point) :
    Spec.x25519_spec sk (leBytesOfNat (uCoord P).val) =
      leBytesOfNat (uCoord (clampScalar (natOfLeBytes sk) • P)).val := by
  rw [Spec.x25519_spec, Spec.a24, curve25519FpParams, decodeUCoord_leBytesOfNat_val,
    encodeUCoord_eq, ← bitsToNat_scalarBits]
  exact congrArg (fun u : Fp25519 => leBytesOfNat u.val) (xladderFold_uCoord P _)

/-- **The X25519 function on the subgroup generated by `B`**: on the encoding of a point `T`
of `G25519 B`, the function with the key `sk` returns the encoding of the clamped multiple of
`T`. -/
theorem x25519_spec_encU {B : Curve25519Point} (sk : Vector UInt8 32) (T : G25519 B) :
    Spec.x25519_spec sk (encU T) = encU (clampScalar (natOfLeBytes sk) • T) := by
  rw [encU, encU, AddSubgroup.coe_nsmul]
  exact x25519_spec_uCoord sk T

/-- **The base-point function of the specification** at a point `B` with `uCoord B = 9`
returns the encoding of the clamped multiple of `B`. -/
theorem x25519_base_spec_encU {B : Curve25519Point} (hB : uCoord B = 9)
    (sk : Vector UInt8 32) :
    Spec.x25519_base_spec sk =
      encU (clampScalar (natOfLeBytes sk) • (⟨B, AddSubgroup.mem_zmultiples B⟩ : G25519 B)) := by
  have h9 : Spec.natToBytes 9 = encU (⟨B, AddSubgroup.mem_zmultiples B⟩ : G25519 B) := by
    rw [natToBytes_eq_leBytesOfNat, encU, hB]
    rfl
  rw [Spec.x25519_base_spec, h9, x25519_spec_encU]

end CatCrypt.Crypto.ECC
