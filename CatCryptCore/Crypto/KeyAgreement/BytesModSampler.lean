/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.KeyAgreement.Curve25519Subgroup
public import CatCryptCore.Crypto.MLKEM.XOFMatrix
public import CatCryptCore.Crypto.Ristretto255.FinGroup

/-!
# A uniform 32-byte string reduced modulo `q`

`bytesModLaw q` is the law of the little-endian value of a uniform 32-byte string, reduced
modulo `q`. When `2^256 ≤ k · q`, every residue has at most `k` preimages, so the uniform
distribution on `ZMod q` is at least `(1 - β)` times `bytesModLaw q` pointwise as soon as
`(1 - β) · k · q ≤ 2^256`, and the two are at total variation distance at most `β`.

At the order `ℓ = 2^252 + δ₀` of the ristretto255 group, `k = 16` and `β = δ₀ / ℓ`, which is
at most `2^-127`.

## Main definitions

* `bytesModLaw q` — the law of `natOfLeBytes v mod q` for uniform `v : Vector UInt8 32`
* `δR255` — `δ₀ / ℓ` with `δ₀ = ℓ - 2^252`
* `bytesModLCert` — the sampler certificate of `bytesModLaw ℓ` against uniform, bound `δR255`

## Main results

* `sampleFrom_bytesModLaw_bind` — a draw from `bytesModLaw q` is a uniform byte string
  followed by its value modulo `q`
* `card_bytesMod_fiber_le` — a residue has at most `k` preimages when `2^256 ≤ k · q`
* `tvDist_bytesModLaw_le` — `tvDist (bytesModLaw q) uniform ≤ β` for
  `(1 - β) · k · q ≤ 2^256`
* `tvDist_bytesModL_le` — `tvDist (bytesModLaw ℓ) uniform ≤ δR255`
* `δR255_le` — `δR255 ≤ 2^-127`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.ECC

open CatCrypt.Core CatCrypt.Prob CatCrypt.NonUniform CatCrypt.Crypto
open CatCrypt.Crypto.Ristretto255 (curve25519_l)
open scoped ENNReal

variable (q : ℕ)

/-- The law of the little-endian value of a uniform 32-byte string, modulo `q`. -/
noncomputable def bytesModLaw : SDistr (ZMod q) :=
  (SDistr.uniform (Vector UInt8 32)).bind fun v => SDistr.pure (natOfLeBytes v : ZMod q)

/-- A draw from `bytesModLaw q` is a uniform byte string followed by its value modulo `q`. -/
theorem sampleFrom_bytesModLaw_bind {β : Type} (k : ZMod q → SPComp β) :
    (sampleFrom (bytesModLaw q)).bind k =
      (SPComp.sample (Vector UInt8 32)).bind fun v => k (natOfLeBytes v : ZMod q) :=
  sampleFrom_uniform_map_bind _ k

/-- `bytesModLaw q` does not fail. -/
theorem mass_bytesModLaw : SDistr.mass (bytesModLaw q) = 1 :=
  mass_bind_of_mass_one SDistr.mass_uniform fun _ => SDistr.mass_pure _

/-- `bytesModLaw q` gives no mass to failure. -/
theorem bytesModLaw_apply_none : bytesModLaw q none = 0 := by
  have h := mass_bytesModLaw q
  unfold SDistr.mass at h
  by_contra hne
  exact absurd h (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hne).ne

variable [NeZero q]

/-- When `2^256 ≤ k · q`, a residue modulo `q` is the value of at most `k` byte strings. -/
theorem card_bytesMod_fiber_le (k : ℕ) (hk : 2 ^ 256 ≤ k * q) (y : ZMod q) :
    (Finset.univ.filter fun v : Vector UInt8 32 => (natOfLeBytes v : ZMod q) = y).card ≤ k := by
  have hq : 0 < q := NeZero.pos q
  let g : {v : Vector UInt8 32 // (natOfLeBytes v : ZMod q) = y} → Fin k := fun v =>
    ⟨natOfLeBytes v.1 / q, (Nat.div_lt_iff_lt_mul hq).2 ((natOfLeBytes_lt v.1).trans_le hk)⟩
  have hg : Function.Injective g := by
    rintro ⟨v, hv⟩ ⟨v', hv'⟩ h
    have hd : natOfLeBytes v / q = natOfLeBytes v' / q := congrArg Fin.val h
    have hm : natOfLeBytes v % q = natOfLeBytes v' % q :=
      (ZMod.natCast_eq_natCast_iff' _ _ _).1 (hv.trans hv'.symm)
    have he : natOfLeBytes v = natOfLeBytes v' := by
      rw [← Nat.div_add_mod (natOfLeBytes v) q, ← Nat.div_add_mod (natOfLeBytes v') q, hd, hm]
    apply Subtype.ext
    refine bytesEquiv.injective (Fin.ext ?_)
    rw [bytesEquiv_val, bytesEquiv_val, he]
  rw [← Fintype.card_subtype]
  exact (Fintype.card_le_of_injective g hg).trans_eq (Fintype.card_fin _)

/-- When `2^256 ≤ k · q`, each residue has mass at most `k / 2^256`. -/
theorem bytesModLaw_apply_le (k : ℕ) (hk : 2 ^ 256 ≤ k * q) (y : ZMod q) :
    bytesModLaw q (some y) ≤ k * ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  rw [bytesModLaw, SDistr.uniform_bind_pure_apply, card_bytes]
  have h := card_bytesMod_fiber_le q k hk y
  calc _ ≤ (k : ℝ≥0∞) * ((2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹ := by gcongr
    _ = _ := by norm_num

/-- **Reducing a uniform 32-byte string modulo `q`**: for `2^256 ≤ k · q` and
`(1 - β) · k · q ≤ 2^256`, the law is at total variation distance at most `β` from the uniform
distribution on `ZMod q`. -/
theorem tvDist_bytesModLaw_le (k : ℕ) (β : ℝ≥0∞) (hk : 2 ^ 256 ≤ k * q)
    (hβ : (1 - β) * k * q ≤ 2 ^ 256) :
    tvDist (bytesModLaw q) (SDistr.uniform (ZMod q)) ≤ β := by
  have hN : ((2 : ℝ≥0∞) ^ 256) ≠ 0 := by positivity
  have hN' : ((2 : ℝ≥0∞) ^ 256) ≠ ⊤ := by simp
  have hmin : ∀ x, (1 - β) * bytesModLaw q x ≤ SDistr.uniform (ZMod q) x := by
    rintro (_ | y)
    · rw [bytesModLaw_apply_none, mul_zero]
      exact zero_le
    · rw [SDistr.uniform_apply_some, ZMod.card]
      calc (1 - β) * bytesModLaw q (some y) ≤ (1 - β) * (k * ((2 : ℝ≥0∞) ^ 256)⁻¹) := by
            gcongr
            exact bytesModLaw_apply_le q k hk y
        _ ≤ (q : ℝ≥0∞)⁻¹ := by
            rw [ENNReal.le_inv_iff_mul_le]
            calc (1 - β) * (k * ((2 : ℝ≥0∞) ^ 256)⁻¹) * q
                = (1 - β) * k * q * ((2 : ℝ≥0∞) ^ 256)⁻¹ := by ring
              _ ≤ 2 ^ 256 * ((2 : ℝ≥0∞) ^ 256)⁻¹ := by gcongr
              _ = 1 := ENNReal.mul_inv_cancel hN hN'
  refine iSup₂_le fun f hf => ?_
  have h := MLKEM.XOFMatrix.tsum_le_add_of_minorant (SDistr.uniform (ZMod q)) (bytesModLaw q) β
    hmin f hf
  exact sup_le (tsub_le_iff_left.mpr h.2) (tsub_le_iff_left.mpr h.1)

/-! ## The order of the ristretto255 group -/

/-- `δ₀ / ℓ`, with `δ₀ = ℓ - 2^252` and `ℓ` the order of the ristretto255 group. -/
noncomputable def δR255 : ℝ≥0∞ := ((curve25519_l - 2 ^ 252 : ℕ) : ℝ≥0∞) / curve25519_l

/-- **A uniform 32-byte string modulo `ℓ`** is at total variation distance at most `δ₀ / ℓ`
from uniform on `ZMod ℓ`. -/
theorem tvDist_bytesModL_le :
    tvDist (bytesModLaw curve25519_l) (SDistr.uniform (ZMod curve25519_l)) ≤ δR255 := by
  have hℓ : curve25519_l = 2 ^ 252 + 27742317777372353535851937790883648493 := rfl
  refine tvDist_bytesModLaw_le curve25519_l 16 δR255 (by rw [hℓ]; norm_num) ?_
  have hℓ0 : (curve25519_l : ℝ≥0∞) ≠ 0 := by simp [hℓ]
  have hℓt : (curve25519_l : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsub : (1 - δR255) * curve25519_l = (2 ^ 252 : ℕ) := by
    rw [ENNReal.sub_mul (fun _ _ => hℓt), one_mul, δR255,
      ENNReal.div_mul_cancel hℓ0 hℓt, ← ENNReal.natCast_sub, Nat.sub_sub_self (by rw [hℓ]; omega)]
  calc (1 - δR255) * (16 : ℕ) * curve25519_l = 16 * ((1 - δR255) * curve25519_l) := by
        push_cast; ring
    _ ≤ 2 ^ 256 := by rw [hsub]; norm_num

/-- `δR255 ≤ 2^-127`. -/
theorem δR255_le : δR255 ≤ (2 ^ 127 : ℝ≥0∞)⁻¹ := by
  have hℓ : curve25519_l = 2 ^ 252 + 27742317777372353535851937790883648493 := rfl
  have hδ : curve25519_l - 2 ^ 252 = 27742317777372353535851937790883648493 := by
    rw [hℓ]; omega
  have h0 : ((curve25519_l - 2 ^ 252 : ℕ) : ℝ≥0∞) ≠ 0 := by rw [hδ]; norm_num
  calc δR255 ≤ ((curve25519_l - 2 ^ 252 : ℕ) : ℝ≥0∞) /
        (((curve25519_l - 2 ^ 252) * 2 ^ 127 : ℕ)) := by
        unfold δR255
        gcongr
        rw [hδ, hℓ]
        norm_num
    _ = (2 ^ 127 : ℝ≥0∞)⁻¹ := by
        rw [Nat.cast_mul, ← mul_one ((curve25519_l - 2 ^ 252 : ℕ) : ℝ≥0∞), mul_assoc,
          ENNReal.mul_div_mul_left _ _ h0 (ENNReal.natCast_ne_top _), one_mul, one_div]
        norm_num

/-- **The sampler certificate of a uniform 32-byte string modulo `ℓ`**: the law
`bytesModLaw ℓ` against the uniform distribution on `ZMod ℓ`, with bound `δR255`. -/
noncomputable def bytesModLCert : SamplerCert (ZMod curve25519_l) where
  μ := bytesModLaw curve25519_l
  ν := SDistr.uniform _
  δ := δR255
  mass_μ := mass_bytesModLaw _
  mass_ν := SDistr.mass_uniform
  tv_le := tvDist_bytesModL_le

end CatCrypt.Crypto.ECC
