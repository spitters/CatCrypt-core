/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.KeyAgreement.Curve25519LadderU

/-!
# The base point `u = 9` of Curve25519 and its order

`B9` is the point `(9, v₉)` of Curve25519 with the v-coordinate
`v₉ = 14781619447589544791020593568409986887264606134616475288964881837755586237401` of
RFC 7748 §4.1. Its additive order is the prime `ℓ = curve25519SubgroupOrder`.

The order is computed with the x-only ladder. The ladder over the 253 bits of `ℓ`, started at
the projective x-coordinate `(9, 1)` of `B9`, ends in a first component with `Z = 0`; this is a
kernel computation of 253 ladder steps over `Fp25519` (`B9_ladder_snd`). By
`xladderFold_projMul` that component is a nonzero multiple of the projective x-coordinate of
`ℓ • B9`, so the second coordinate of the latter vanishes and `ℓ • B9` is the identity.

## Main definitions

* `B9v`, `B9` — the v-coordinate and the point

## Main results

* `B9_nonsingular` — `(9, v₉)` is a nonsingular point of the curve
* `uCoord_B9` — `uCoord B9 = 9`
* `B9_order_nsmul`, `B9_addOrder` — `ℓ • B9 = 0` and `addOrderOf B9 = ℓ`
* `x25519_base_spec_B9` — the base-point function of the X25519 specification is clamped scalar
  multiplication of `B9`
* `curve25519_basepoint_addOrder` — `addOrderOf curve25519_basepoint = ℓ`, for the point
  `curve25519_basepoint`, which is `B9`
* `curve25519_basepoint_LadderNondeg` — ladder nondegeneracy below `ℓ`
* `x25519_ladder_correct_basepoint` — correctness of the ladder at the base point below `ℓ`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.ECC

open CatCrypt.Crypto.KeyAgreement.X25519

/-- The v-coordinate of the base point `u = 9` (RFC 7748 §4.1). -/
def B9v : Fp25519 :=
  14781619447589544791020593568409986887264606134616475288964881837755586237401

/-- `(9, v₉)` satisfies `v₉² = 9³ + 486662 · 9² + 9` and `2 · v₉ ≠ 0`. -/
theorem B9_nonsingular : (montgomeryW (486662 : Fp25519)).toAffine.Nonsingular 9 B9v := by
  rw [WeierstrassCurve.Affine.nonsingular_iff', montgomeryW_equation]
  simp only [montgomeryW_a₁, montgomeryW_a₃, zero_mul, add_zero]
  refine ⟨by decide +kernel, Or.inr (by decide +kernel)⟩

/-- **The base point `u = 9` of Curve25519** (RFC 7748 §4.1). -/
def B9 : Curve25519Point := .some 9 B9v B9_nonsingular

theorem B9_ne_zero : B9 ≠ 0 := by
  intro h
  cases h

theorem uCoord_B9 : uCoord B9 = 9 := by
  simp [B9, uCoord, curve25519_xProj_eq, xProjW_some]

/-- The 253 bits of `ℓ`, least significant first, represent `ℓ`. -/
theorem bitsToNat_bitsOfMSB_subgroupOrder :
    bitsToNat (Spec.bitsOfMSB 253 curve25519SubgroupOrder).reverse = curve25519SubgroupOrder := by
  rw [Spec.bitsToNat_reverse_bitsOfMSB, Nat.mod_eq_of_lt]
  rw [curve25519SubgroupOrder_eq]
  norm_num

/-- **The ladder over the bits of `ℓ` at `(9, 1)` ends with `Z = 0`**, a kernel computation of
253 ladder steps over `Fp25519`. -/
theorem B9_ladder_snd :
    (xladderFold (curve25519Params Fp25519).a24 ((9 : Fp25519), 1)
      (Spec.bitsOfMSB 253 curve25519SubgroupOrder).reverse).1.2 = 0 := by
  decide +kernel

/-- **`ℓ • B9 = 0`.** -/
theorem B9_order_nsmul : curve25519SubgroupOrder • B9 = 0 := by
  have hu : uCoord B9 ≠ 0 := by
    rw [uCoord_B9, show (9 : Fp25519) = ((9 : ℕ) : Fp25519) by norm_cast]
    exact fp25519_small_ne_zero (by norm_num) (by norm_num)
  have h := (xladderFold_projMul B9 hu (Spec.bitsOfMSB 253 curve25519SubgroupOrder).reverse).1
  rw [xProj_eq_uCoord B9_ne_zero, uCoord_B9, bitsToNat_bitsOfMSB_subgroupOrder] at h
  obtain ⟨c, hc, hst⟩ := h
  have hz := congrArg Prod.snd hst
  rw [B9_ladder_snd] at hz
  by_contra hne
  rw [xProj_eq_uCoord hne, mul_one] at hz
  exact hc hz.symm

/-- **The base point has order `ℓ`.** -/
theorem B9_addOrder : addOrderOf B9 = curve25519SubgroupOrder :=
  addOrderOf_eq_prime B9_order_nsmul B9_ne_zero

instance factB9AddOrder : Fact (addOrderOf B9 = curve25519SubgroupOrder) :=
  ⟨B9_addOrder⟩

/-- **The base-point function of the X25519 specification** is clamped scalar multiplication of
`B9`: it returns the encoding of `clampScalar (natOfLeBytes sk) • B9`. -/
theorem x25519_base_spec_B9 (sk : Vector UInt8 32) :
    Spec.x25519_base_spec sk =
      encU (clampScalar (natOfLeBytes sk) • (⟨B9, AddSubgroup.mem_zmultiples B9⟩ : G25519 B9)) :=
  x25519_base_spec_encU uCoord_B9 sk

/-! ## The ladder at the base point -/

/-- **The base point of Curve25519**: the point `B9` with `u = 9` (RFC 7748 §4.1). -/
abbrev curve25519_basepoint : Curve25519Point := B9

/-- `l • B = 0` for the base point. -/
theorem curve25519_basepoint_order_nsmul :
    curve25519SubgroupOrder • curve25519_basepoint = 0 :=
  B9_order_nsmul

/-- The base point is not the identity. -/
theorem curve25519_basepoint_ne_zero : curve25519_basepoint ≠ 0 :=
  B9_ne_zero

/-- The base point has additive order exactly `l`. -/
theorem curve25519_basepoint_addOrder :
    addOrderOf curve25519_basepoint = curve25519SubgroupOrder :=
  B9_addOrder

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

end CatCrypt.Crypto.ECC
