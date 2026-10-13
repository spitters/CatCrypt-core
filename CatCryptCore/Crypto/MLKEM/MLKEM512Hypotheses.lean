/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.FIPS203QROMQuantumMLWE
public import CatCryptCore.Crypto.MLKEM.SamplerCbd

/-!
# The coin and spreadness hypotheses at ML-KEM-512

The coin hypothesis of `FIPS203QROMQuantumMLWE.mlkem512_qindcca_qmlwe_coll` and
`(15/16)^512`-spreadness hold at `CompressedPKE.mlkem512CompressedScheme`.

## Main definitions

* `zeroSeed` — the all-zero PRF output blocks of one encryption
* `UAdmissible pk c r e₁` — `Compress_{10} (Aᵀ r + e₁)` equals the `u`-component of `c`

## Main results

* `samplePoly_zero` — the FIPS 203 centered-binomial sampler maps the all-zero block
  to the zero polynomial
* `mlkem512_hcoin` — under every key pair, every message decrypts correctly when
  encrypted with `zeroSeed`
* `enc_eq`, `dec_eq` — encryption and decryption of the scheme with the record
  fields unfolded
* `compress10_ne_add_four` — `Compress_{10}` separates every two residues at
  distance `4` in `Z_q`
* `card_window_filter_le`, `card_e1_filter_le`, `card_uAdmissible_le` — the counts
  of admissible windows, `e₁` blocks and encryption seeds
* `mlkem512_isSpread` — the scheme is `(15/16)^512`-spread

## Proof of spreadness

`mlkem512_isSpread` uses the `u`-component of the ciphertext alone: for fixed
`r` and `e₂`, each of the 512 coefficients of `e₁` is read from its own 4-bit
window of the PRF block (`SamplerCbd.windowMap_bijective`), and of the 16 windows
at least one, the window of value `2` or the window of value `-2`, leaves the
prescribed `Compress_{10}` value (`compress10_ne_add_four`,
`card_uAdmissible_le`). The collision term of the ML-KEM-512 theorems is the
coin-collision weight bound of `CollisionSpreadBound`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal

noncomputable section

namespace CatCrypt.Crypto.MLKEM.MLKEM512Hypotheses

open MLKEM512Instance
open CompressedPKE (MLKEM512CT mlkem512Compress mlkem512Decompress mlkem512CompressedScheme)
open MLWE_PKE_Basic (PK)

/-! ## The all-zero seed -/

/-- The centered-binomial sampler maps the all-zero PRF block to the zero
polynomial. -/
theorem samplePoly_zero (η : ℕ) : samplePoly η (fun _ => 0) = 0 := by
  rw [SamplerCbd.samplePoly_eq]
  funext i
  have hb : ∀ k, SamplerCbd.bitB (List.replicate (64 * η) (0 : UInt8)) k = false := by
    intro k
    simp only [SamplerCbd.bitB, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> simp
  simp [SamplerCbd.windowMap, SamplerCbd.windowOf, SamplerCbd.windowVal, SamplerCbd.countOnes,
    hb, Util.Zq3329.fromInt]

/-- The all-zero PRF output blocks of one ML-KEM-512 encryption. -/
def zeroSeed : PrfVecBlock 3 × PrfVecBlock 2 × PrfBlock 2 :=
  (fun _ _ => 0, fun _ _ => 0, fun _ => 0)

/-- The centered-binomial sampler maps all-zero blocks to the zero vector. -/
theorem sampleVec_zero (η : ℕ) : sampleVec η (fun _ _ => 0) = 0 := by
  funext i
  exact samplePoly_zero η

/-- Multiplication by the zero polynomial in `Rq` is zero. -/
theorem ringMul_zero (a : Rq) : ringMul a 0 = 0 := by
  funext k
  simp [ringMul, CatCrypt.Crypto.Optimizer.Lattice.SignedNegacyclicConv.signedNegaConv]

/-- `Compress₁ ∘ Decompress_4 ∘ Compress_4 ∘ Decompress₁` is the identity on bits. -/
theorem compress1_roundtrip4 (b : Bool) :
    compress1 (Compress.decompress_d 4 (Compress.compress_d 4 (decompress1 b))) = b := by
  cases b <;> decide

/-- Encryption in `mlkem512CompressedScheme`, with the record fields unfolded. -/
theorem enc_eq (pk : Mat × Vec) (m : Msg) (sd : PrfVecBlock 3 × PrfVecBlock 2 × PrfBlock 2) :
    mlkem512CompressedScheme.enc pk m sd =
      mlkem512Compress
        (vecAdd (matVecMul (matTranspose pk.1) (sampleVec 3 sd.1)) (sampleVec 2 sd.2.1),
          ringAdd (ringAdd (vecDot pk.2 (sampleVec 3 sd.1)) (samplePoly 2 sd.2.2))
            (msgEncode m)) :=
  congrArg mlkem512Compress rfl

/-- Decryption in the uncompressed base scheme at `mlkem512Params`, with the record
fields unfolded. -/
theorem base_dec_eq (sk : Vec) (x : Vec × Rq) :
    (MLWE_PKE_Scheme.toScheme mlkem512Params).dec sk x =
      some (msgDecode (ringSub x.2 (vecDot sk x.1))) := by
  have h1 : mlkem512Params.m_decode = msgDecode := rfl
  have h2 : mlkem512Params.ring_sub = ringSub := rfl
  have h3 : mlkem512Params.vec_dot = vecDot := rfl
  show some (mlkem512Params.m_decode (mlkem512Params.ring_sub x.2 (mlkem512Params.vec_dot sk x.1)))
    = _
  rw [h1, h2, h3]
  rfl

/-- Decryption in `mlkem512CompressedScheme`, with the record fields unfolded. -/
theorem dec_eq (sk : Vec) (c : MLKEM512CT) :
    mlkem512CompressedScheme.dec sk c =
      some (msgDecode (ringSub (mlkem512Decompress c).2 (vecDot sk (mlkem512Decompress c).1))) :=
  (CompressedPKE.mlkem512Compressed_dec sk c).trans (base_dec_eq sk _)

/-! ## The coin hypothesis -/

/-- Under every key pair, encryption of `m` with the all-zero seed decrypts to `m`:
with `r = e₁ = e₂ = 0` the ciphertext is `(Compress_{10} 0, Compress_4 (Encode m))`,
and `Compress₁ ∘ Decompress_4 ∘ Compress_4 ∘ Decompress₁` is the identity. -/
theorem mlkem512_hcoin : ∀ pk sk, mlkem512CompressedScheme.keygen (pk, sk) ≠ 0 → ∀ m, ∃ ρ,
    mlkem512CompressedScheme.dec sk (mlkem512CompressedScheme.enc pk m ρ) = some m := by
  intro (pk : Mat × Vec) (sk : Vec) _ (m : Msg)
  refine ⟨zeroSeed, ?_⟩
  refine (dec_eq sk _).trans ?_
  rw [enc_eq pk m zeroSeed]
  simp only [zeroSeed, sampleVec_zero, samplePoly_zero]
  have hdot : ∀ v : Vec, vecDot v 0 = 0 := by
    intro v
    simp [vecDot, ringMul_zero]
  have hu : vecAdd (matVecMul (matTranspose pk.1) 0) 0 = 0 := by
    funext j
    simp [vecAdd, matVecMul, ringMul_zero]
  have hv : ringAdd (ringAdd (vecDot pk.2 0) 0) (msgEncode m) = msgEncode m := by
    simp [ringAdd, hdot pk.2]
  have h0 : Compress.decompress_d 10 (Compress.compress_d 10 0) = 0 := by decide
  have hz : ∀ x : Rq,
      (mlkem512Decompress (mlkem512Compress ((0 : Vec), x))).1 = (0 : Vec) := by
    intro x
    funext j i
    simp only [mlkem512Decompress, mlkem512Compress, CompressedPKE.decompressCT,
      CompressedPKE.compressCT, CompressedPKE.decompressPoly, CompressedPKE.compressPoly,
      Pi.zero_apply]
    exact h0
  have hmsg : msgDecode (ringSub
      (mlkem512Decompress (mlkem512Compress ((0 : Vec), msgEncode m))).2 (0 : Rq)) = m := by
    funext i
    simp only [msgDecode, ringSub, mlkem512Decompress, mlkem512Compress,
      CompressedPKE.decompressCT, CompressedPKE.compressCT, CompressedPKE.decompressPoly,
      CompressedPKE.compressPoly, sub_zero, msgEncode]
    exact compress1_roundtrip4 (m i)
  rw [hu, hv, hz, hdot, hmsg]
  rfl

/-! ## Spreadness -/

/-- The integer form of `compress10_ne_add_four`: for `a < 3329`, the rounded
`1024 · a / 3329` and the rounded `1024 · ((a + 4) mod 3329) / 3329` differ
modulo `1024`. -/
theorem compress10_nat_ne (a : ℕ) (ha : a < 3329) :
    (1024 * a + 1664) / 3329 % 1024 ≠ (1024 * ((a + 4) % 3329) + 1664) / 3329 % 1024 := by
  rcases Nat.lt_or_ge (a + 4) 3329 with h | h
  · rw [Nat.mod_eq_of_lt h]
    have e1 := Nat.div_add_mod (1024 * a + 1664) 3329
    have e2 := Nat.mod_lt (1024 * a + 1664) (show 3329 > 0 by norm_num)
    have e3 := Nat.div_add_mod (1024 * (a + 4) + 1664) 3329
    have e4 := Nat.mod_lt (1024 * (a + 4) + 1664) (show 3329 > 0 by norm_num)
    generalize (1024 * a + 1664) / 3329 = n₁ at *
    generalize (1024 * (a + 4) + 1664) / 3329 = n₂ at *
    generalize (1024 * a + 1664) % 3329 = r₁ at *
    generalize (1024 * (a + 4) + 1664) % 3329 = r₂ at *
    have hlt : n₁ < n₂ := by omega
    have hle : n₂ ≤ n₁ + 2 := by omega
    intro heq
    have hd : 1024 ∣ n₂ - n₁ := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq heq.symm)
    have := Nat.le_of_dvd (by omega) hd
    omega
  · interval_cases a <;> norm_num

/-- `Compress_{10}` separates every two residues at distance `4` in `Z_q`: a
`Compress_{10}` bucket has width at most `4` because `4 · 1024 > 3329`. -/
theorem compress10_ne_add_four (z : ZMod Compress.q) :
    Compress.compress_d 10 z ≠ Compress.compress_d 10 (z + 4) := by
  have hz : z.val < 3329 := ZMod.val_lt z
  have h4 : (z + 4).val = (z.val + 4) % 3329 := by
    rw [ZMod.val_add]
    rfl
  unfold Compress.compress_d
  rw [h4, Ne, ZMod.natCast_eq_natCast_iff']
  norm_num
  exact compress10_nat_ne _ hz

/-- Of the 16 bit windows of one `η = 2` coefficient, at most 15 give a coefficient
`e` with `Compress_{10} (x + e) = y`: the windows of value `2` and `-2` land at
distance `4`, which `Compress_{10}` separates. -/
theorem card_window_filter_le (x : ZMod Compress.q) (y : ZMod (2 ^ 10)) :
    (Finset.univ.filter (fun w : SamplerCbd.Win 2 =>
      Compress.compress_d 10 (x + Util.Zq3329.fromInt (SamplerCbd.windowVal w)) = y)).card
        ≤ 15 := by
  classical
  by_contra hS
  push Not at hS
  set S := Finset.univ.filter (fun w : SamplerCbd.Win 2 =>
    Compress.compress_d 10 (x + Util.Zq3329.fromInt (SamplerCbd.windowVal w)) = y)
  have hcard : Fintype.card (SamplerCbd.Win 2) = 16 := by
    simp [SamplerCbd.Win]
  have huniv : S = Finset.univ :=
    Finset.eq_univ_of_card S (le_antisymm (Finset.card_le_univ S) (by omega))
  have hp : ((fun _ => true, fun _ => false) : SamplerCbd.Win 2) ∈ S := huniv ▸ Finset.mem_univ _
  have hm : ((fun _ => false, fun _ => true) : SamplerCbd.Win 2) ∈ S := huniv ▸ Finset.mem_univ _
  simp only [S, SamplerCbd.windowVal, SamplerCbd.countOnes] at hp hm
  norm_num [Util.Zq3329.fromInt] at hp hm
  apply compress10_ne_add_four (x - 2)
  rw [show x - 2 + 4 = x + 2 by ring, ← sub_eq_add_neg] at *
  rw [hp, hm]

/-- For a fixed vector `U`, at most `15^512` of the `16^512` PRF blocks of `e₁` give
`Compress_{10} (U + e₁) = c₁`: each of the 512 coefficients of `e₁` is read from its
own bit window, and at most 15 of its 16 windows are admissible. -/
theorem card_e1_filter_le (U : Vec) (c₁ : Fin 2 → Fin 256 → ZMod (2 ^ 10)) :
    (Finset.univ.filter (fun e : PrfVecBlock 2 => ∀ j i,
      Compress.compress_d 10 (U j i + sampleVec 2 e j i) = c₁ j i)).card ≤ 15 ^ 512 := by
  classical
  let φ : PrfBlock 2 ≃ (Fin 256 → SamplerCbd.Win 2) :=
    Equiv.ofBijective _ (SamplerCbd.windowMap_bijective 2 (by norm_num))
  let Φ : PrfVecBlock 2 ≃ (Fin 2 → Fin 256 → SamplerCbd.Win 2) := Equiv.piCongrRight fun _ => φ
  let T : Fin 2 → Fin 256 → Finset (SamplerCbd.Win 2) := fun j i =>
    Finset.univ.filter (fun w : SamplerCbd.Win 2 =>
      Compress.compress_d 10 (U j i + Util.Zq3329.fromInt (SamplerCbd.windowVal w)) = c₁ j i)
  have hset : Finset.univ.filter (fun e : PrfVecBlock 2 => ∀ j i,
      Compress.compress_d 10 (U j i + sampleVec 2 e j i) = c₁ j i) =
      (Fintype.piFinset fun j => Fintype.piFinset fun i => T j i).map Φ.symm.toEmbedding := by
    ext e
    rw [Finset.mem_map_equiv, Equiv.symm_symm]
    simp [Fintype.mem_piFinset, T, Φ, φ, sampleVec, SamplerCbd.samplePoly_eq]
  rw [hset, Finset.card_map, Fintype.card_piFinset]
  calc ∏ j, (Fintype.piFinset fun i => T j i).card
      ≤ ∏ _j : Fin 2, 15 ^ 256 := by
        refine Finset.prod_le_prod' fun j _ => ?_
        rw [Fintype.card_piFinset]
        calc ∏ i, (T j i).card ≤ ∏ _i : Fin 256, 15 :=
              Finset.prod_le_prod' fun i _ => card_window_filter_le _ _
          _ = 15 ^ 256 := by simp
    _ = 15 ^ 512 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]

/-- The `u`-component condition on the PRF blocks `r`, `e₁` of an encryption of any
message under `pk` to `c`: `Compress_{10} (Aᵀ r + e₁) = c.1`. -/
def UAdmissible (pk : Mat × Vec) (c : MLKEM512CT) (r : PrfVecBlock 3) (e : PrfVecBlock 2) :
    Prop :=
  ∀ j i, Compress.compress_d 10
    (matVecMul (matTranspose pk.1) (sampleVec 3 r) j i + sampleVec 2 e j i) = c.1 j i

/-- An encryption of `m` under `pk` to `c` has `UAdmissible` PRF blocks. -/
theorem uAdmissible_of_enc (pk : Mat × Vec) (m : Msg) (c : MLKEM512CT)
    (sd : PrfVecBlock 3 × PrfVecBlock 2 × PrfBlock 2)
    (h : mlkem512CompressedScheme.enc pk m sd = c) : UAdmissible pk c sd.1 sd.2.1 := by
  intro j i
  rw [← h, enc_eq]
  simp only [mlkem512Compress, CompressedPKE.compressCT, CompressedPKE.compressPoly, vecAdd,
    Pi.add_apply]
  rfl

set_option linter.constructorNameAsVariable false in
open scoped Classical in
/-- For fixed `r`, at most `15^512` PRF blocks `e₁` are `UAdmissible`. -/
theorem card_uAdmissible_e1_le (pk : Mat × Vec) (c : MLKEM512CT) (r : PrfVecBlock 3) :
    (Finset.univ.filter (UAdmissible pk c r)).card ≤ 15 ^ 512 := by
  refine le_trans (Finset.card_le_card ?_)
    (card_e1_filter_le (matVecMul (matTranspose pk.1) (sampleVec 3 r)) c.1)
  intro e he
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  exact he

set_option linter.constructorNameAsVariable false in
open scoped Classical in
/-- At most `|PRF blocks of r| · 15^512 · |PRF blocks of e₂|` encryption seeds have
`UAdmissible` blocks. -/
theorem card_uAdmissible_le (pk : Mat × Vec) (c : MLKEM512CT) :
    (Finset.univ.filter (fun sd : PrfVecBlock 3 × PrfVecBlock 2 × PrfBlock 2 =>
      UAdmissible pk c sd.1 sd.2.1)).card ≤
      Fintype.card (PrfVecBlock 3) * (15 ^ 512 * Fintype.card (PrfBlock 2)) := by
  set S := Finset.univ.filter (fun sd : PrfVecBlock 3 × PrfVecBlock 2 × PrfBlock 2 =>
    UAdmissible pk c sd.1 sd.2.1)
  have hfib : ∀ a ∈ S.image (fun sd => (sd.1, sd.2.2)),
      (S.filter fun sd => (sd.1, sd.2.2) = a).card ≤ 15 ^ 512 := by
    intro a _
    refine le_trans (Finset.card_le_card_of_injOn (fun sd => sd.2.1) ?_ ?_)
      (card_uAdmissible_e1_le pk c a.1)
    · intro sd hsd
      simp only [S, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] at hsd ⊢
      rw [← hsd.2]
      exact hsd.1
    · intro sd hsd sd' hsd' h
      simp only [S, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] at hsd hsd'
      have h1 := congrArg Prod.fst (hsd.2.trans hsd'.2.symm)
      have h2 := congrArg Prod.snd (hsd.2.trans hsd'.2.symm)
      exact Prod.ext h1 (Prod.ext h h2)
  have himg : (S.image (fun sd => (sd.1, sd.2.2))).card ≤
      Fintype.card (PrfVecBlock 3 × PrfBlock 2) :=
    Finset.card_le_univ _
  calc S.card ≤ 15 ^ 512 * (S.image (fun sd => (sd.1, sd.2.2))).card :=
        Finset.card_le_mul_card_image S _ hfib
    _ ≤ 15 ^ 512 * Fintype.card (PrfVecBlock 3 × PrfBlock 2) := Nat.mul_le_mul_left _ himg
    _ = 15 ^ 512 * (Fintype.card (PrfVecBlock 3) * Fintype.card (PrfBlock 2)) := by
        rw [Fintype.card_prod]
    _ = Fintype.card (PrfVecBlock 3) * (15 ^ 512 * Fintype.card (PrfBlock 2)) :=
        Nat.mul_left_comm _ _ _

/-- The encryption seed space has `|PRF blocks of r| · 16^512 · |PRF blocks of e₂|`
elements. -/
theorem card_seed :
    Fintype.card mlkem512Params.Seed =
      Fintype.card (PrfVecBlock 3) * (16 ^ 512 * Fintype.card (PrfBlock 2)) := by
  have h1 : Fintype.card mlkem512Params.Seed =
      Fintype.card (PrfVecBlock 3 × PrfVecBlock 2 × PrfBlock 2) :=
    Fintype.card_congr (Equiv.refl _)
  have h2 : Fintype.card (PrfVecBlock 2) = 16 ^ 512 := by
    have hw : Fintype.card (SamplerCbd.Win 2) = 16 := by simp [SamplerCbd.Win]
    rw [show Fintype.card (PrfVecBlock 2) = Fintype.card (PrfBlock 2) ^ 2 by
      simp [PrfVecBlock], SamplerCbd.card_window_eq, Fintype.card_fun, hw, Fintype.card_fin,
      ← pow_mul]
  rw [h1, Fintype.card_prod, Fintype.card_prod, h2]

set_option linter.constructorNameAsVariable false in
open scoped Classical in
/-- **`mlkem512CompressedScheme` is `(15/16)^512`-spread.** For every public key,
message and ciphertext, a uniform encryption seed encrypts the message to the
ciphertext with probability at most `(15/16)^512`: the `u`-component alone fixes
`Compress_{10}` of each of the 512 coefficients of `Aᵀ r + e₁`, and for fixed `r`
each coefficient of `e₁` is read from its own 4-bit window, at most 15 of whose 16
values are admissible (`card_window_filter_le`). -/
theorem mlkem512_isSpread : mlkem512CompressedScheme.IsSpread ((15 / 16) ^ 512) := by
  intro ks _ m c
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  have ha : Fintype.card ↑{r | mlkem512CompressedScheme.enc ks.1 m r = c} ≤
      Fintype.card (PrfVecBlock 3) * (15 ^ 512 * Fintype.card (PrfBlock 2)) := by
    refine le_trans ?_ (card_uAdmissible_le ks.1 c)
    rw [← Fintype.card_subtype]
    exact Fintype.card_le_of_injective
      (fun x => ⟨x.1, uAdmissible_of_enc ks.1 m c x.1 x.2⟩)
      (fun x y h => Subtype.ext (Subtype.mk.inj h))
  rw [card_seed]
  generalize Fintype.card ↑{r | mlkem512CompressedScheme.enc ks.1 m r = c} = a at ha ⊢
  generalize Fintype.card (PrfVecBlock 3) = A at ha ⊢
  generalize Fintype.card (PrfBlock 2) = B at ha ⊢
  apply ENNReal.div_le_of_le_mul
  calc (a : ℝ≥0∞) ≤ ((A * (15 ^ 512 * B) : ℕ) : ℝ≥0∞) := by exact_mod_cast ha
    _ = (15 / 16) ^ 512 * ((A * (16 ^ 512 * B) : ℕ) : ℝ≥0∞) := by
        simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        rw [show ((15 : ℝ≥0∞) / 16) ^ 512 * (A * (16 ^ 512 * B)) =
            A * ((15 / 16 * 16) ^ 512 * B) by rw [mul_pow]; ac_rfl,
          ENNReal.div_mul_cancel (by norm_num) (by simp)]

end CatCrypt.Crypto.MLKEM.MLKEM512Hypotheses

end

end
