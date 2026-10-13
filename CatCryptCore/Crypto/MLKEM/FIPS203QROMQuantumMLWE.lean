/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.KEMAdvNormalFormMR
public import CatCryptCore.Quantum.QROM.QMLWEAux

/-!
# ML-KEM-512 in the QROM under quantum module-LWE with oracle access

The quantum IND-CCA advantage of the FIPS 203 KEM over the ML-KEM-512 K-PKE with
compressed ciphertexts, against every quantum adversary with `k` decapsulation
rounds, is bounded by quantum module-LWE advantages of reductions that keep the
adversary's oracle calls. The one-wayness link of the coin hop is
`prFindCoin_le_qOwcpaAux`; one-wayness is reduced to IND-CPA with oracle access by
`qOwcpaAux_le_qIndcpaAux`, and IND-CPA to module-LWE by `qIndcpaAux_le_qMLWE`.

## Main definitions

* `qMLWEBound hpk eG eJ eKR eC eKa A b` — the two module-LWE and two extended
  module-LWE advantages with oracle access of `qRedEnc` and `qRedExt` applied to
  `indRed eG (owRedQuery A b)`, plus `|M|⁻¹` and the decryption error `corrErr`

## Main results

* `qINDCCA_le_qOwcpaAux_numeric_coll` — for a scheme `P`,
  `qINDCCA_le_find_numeric_coll` with each one-wayness term the winning
  probability of `owRedQuery A b` in `qOwcpaAux`, under a bound
  `collWeight P ≤ ε` on the key-averaged coin-collision weight of
  `Quantum/QROM/CollisionWeight.lean`
* `qOwcpaAux_owRedQuery_le_qMLWEBound` — that winning probability is at most
  `qMLWEBound` at ML-KEM-512
* `mlkem512_qindcca_qmlwe_coll` — the bound for every KEM adversary `A`, with
  each one-wayness term `qMLWEBound` at the normal form `nfKEM A` and each `δ*`
  replaced by `Λ`

## Scope

The reductions are `owRedQuery` (the adversary's circuit up to a uniformly drawn
query index, with its oracle calls kept), `indRed` (two classical message draws
and one projector) and `qRedEnc`, `qRedExt` (one encryption or compression, then
one run); none of them draws an oracle table or computes a distribution. The
assumption is module-LWE against quantum distinguishers with independent
auxiliary random oracles. `Λ`, `ε` and `hcoin` are hypotheses; no value for them
is derived here; `MLKEM512Hypotheses` and `MLKEM512FailureBound` discharge them at
ML-KEM-512, and `PolyOracle` simulates the auxiliary oracles by random
low-degree polynomials to reach quantum module-LWE and extended module-LWE
without oracle access.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.QROM
open CatCrypt.Crypto.PKE.Games (Scheme)

noncomputable section

namespace CatCrypt.Crypto.MLKEM.FIPS203QROMQuantumMLWE

/-! ## The coin hop with the one-wayness game with oracle access -/

section Numeric

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z] [Fintype K]
  [Nonempty K] [Fintype R] [Nonempty R] [Fintype C] [DecidableEq C] [DecidableEq Hash]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

variable [NeZero n] [NeZero c] [NeZero (m₁ + m₂)]

open scoped Classical in
/-- The quantum IND-CCA advantage through the coin hop with every correctness
term numeric in `Λ` and each one-wayness term the winning probability of
`owRedQuery A b` in `qOwcpaAux`: with `q' = flatQ q k q`,
`q'' = flatQ (q + 4) k q`, `Λ = E λ` and `ε` a bound on the coin-collision
weight `collWeight P`,

`Adv ≤ 4 √(4 q'² (Adv_OWaux(B_true) + δ*)) + (8 q' Λ^(1/2) + (Λ + ε) + 8 q' Λ^(1/2))
  + 4 √(4 q'² (Adv_OWaux(B_false) + δ*))
  + 2 (8 q' / √|Z| + 8 q'' Λ^(1/2) + Λ + 8 q' Λ^(1/2))`. -/
theorem qINDCCA_le_qOwcpaAux_numeric_coll [NeZero (flatQ q k q)]
    (A : KEMQAdv m₁ m₂ n w q k c a PK C K)
    (hcoin : ∀ pk sk, P.keygen (pk, sk) ≠ 0 → ∀ m, ∃ ρ, P.dec sk (P.enc pk m ρ) = some m)
    (lam : PK × SK → ℝ≥0∞)
    (hlam : ∀ pk sk, P.keygen (pk, sk) ≠ 0 → ∀ x,
      ((badVals (kemBad P hpk eG eKR pk sk) x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam (pk, sk))
    (ε : ℝ≥0∞) (hcoll : collWeight P ≤ ε)
    (w₀ : ℕ) (hw : 2 * w = w₀ * ancDim (m₁ + m₂) n c)
    (Ans : PK → C → K → Fin a → Equiv.Perm ((Fin (m₁ + m₂) × Fin n) × Fin w₀))
    (hseg : ∀ pk cs κ j i, ((castMR hw (A.run pk cs κ)).seg j i : Matrix _ _ ℂ) *
        cleanProjM (m₁ + m₂) n w₀ c =
      cleanProjM (m₁ + m₂) n w₀ c * ((castMR hw (A.run pk cs κ)).seg j i : Matrix _ _ ℂ))
    (hrounds : ∀ pk cs κ j,
      (castMR hw (A.run pk cs κ)).rounds j = permRound (m₁ + m₂) n w₀ c (Ans pk cs κ))
    (hinit : ∀ pk cs κ,
      SupportedOn (cleanProjM (m₁ + m₂) n w₀ c) (castMR hw (A.run pk cs κ)).init.val) :
    qINDCCAAdvantage P hpk eG eJ eKR eC eKa A ≤
      (4 * ((flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) *
          (qOwcpaAux P hpk eG eJ eKR eC eKa (owRedQuery A true) +
            ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
              (if i.2.2.1 ∈ kemGood P hpk eG eKR i then 0 else 1)))) ^ (1 / 2 : ℝ) +
        (8 * (flatQ q k q : ℝ≥0∞) *
            (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ) +
          (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1 + ε) +
          8 * (flatQ q k q : ℝ≥0∞) *
            (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ)) +
        4 * ((flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) *
          (qOwcpaAux P hpk eG eJ eKR eC eKa (owRedQuery A false) +
            ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
              (if i.2.2.1 ∈ kemGood P hpk eG eKR i then 0 else 1)))) ^ (1 / 2 : ℝ)) +
      2 * (8 * (flatQ q k q : ℝ≥0∞) * ((Fintype.card Z : ℝ≥0∞)⁻¹) ^ (1 / 2 : ℝ) +
        (8 * (flatQ (q + 4) k q : ℝ≥0∞) *
            (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ) +
          ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1 +
          8 * (flatQ q k q : ℝ≥0∞) *
            (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ))) :=
  qINDCCA_le_find_numeric_coll P hpk eG eJ eKR eC eKa A hcoin lam hlam ε hcoll
    (fun b => qOwcpaAux P hpk eG eJ eKR eC eKa (owRedQuery A b))
    (prFindCoin_le_qOwcpaAux P hpk eG eJ eKR eC eKa A) w₀ hw Ans hseg hrounds hinit

end Numeric

/-! ## The bound at ML-KEM-512 -/

section MLKEM512

open MLKEM512Instance (mlkem512Params)
open CompressedPKE (MLKEM512CT mlkem512Compress mlkem512CompressedScheme)
open MLWE_PKE_Basic (PK)

variable {m₁ m₂ n w q k c a : ℕ} {K Hash Z : Type} [Fintype Z] [Nonempty Z] [DecidableEq Z]
  [Fintype K] [Nonempty K] [DecidableEq Hash]
  (hpk : PK mlkem512Params.toBasic → Hash) (eG : (mlkem512Params.PT × Hash) ≃ Fin m₁)
  (eJ : (Z × MLKEM512CT) ≃ Fin m₂) (eKR : (K × mlkem512Params.Seed) ≃ Fin n)
  (eC : MLKEM512CT ≃ Fin c) (eKa : K ≃ Fin a)

variable [NeZero n] [NeZero c]

/-- The module-LWE bound on the one-wayness term of `A` at challenge bit `b`: the
two module-LWE and two extended module-LWE advantages with oracle access of
`qRedEnc` and `qRedExt` applied to `indRed eG (owRedQuery A b)`, plus `|M|⁻¹` and
the decryption error of the scheme. -/
def qMLWEBound (A : KEMQAdv m₁ m₂ n w q k c a (PK mlkem512Params.toBasic) MLKEM512CT K)
    (b : Bool) : ℝ≥0∞ :=
  qMLWEAux mlkem512Params.toBasic mlkem512CompressedScheme hpk eG eJ eKR eC eKa
      (qRedEnc mlkem512CompressedScheme (indRed eG (owRedQuery A b)) true) +
    qMLWEExtAux mlkem512Params.toBasic mlkem512CompressedScheme hpk eG eJ eKR eC eKa
      (qRedExt mlkem512Params.toBasic mlkem512Compress (indRed eG (owRedQuery A b)) true) +
    qMLWEExtAux mlkem512Params.toBasic mlkem512CompressedScheme hpk eG eJ eKR eC eKa
      (qRedExt mlkem512Params.toBasic mlkem512Compress (indRed eG (owRedQuery A b)) false) +
    qMLWEAux mlkem512Params.toBasic mlkem512CompressedScheme hpk eG eJ eKR eC eKa
      (qRedEnc mlkem512CompressedScheme (indRed eG (owRedQuery A b)) false) +
    (Fintype.card mlkem512Params.PT : ℝ≥0∞)⁻¹ + corrErr mlkem512CompressedScheme

/-- The winning probability of `owRedQuery A b` in the one-wayness game with
oracle access is at most `qMLWEBound`. -/
theorem qOwcpaAux_owRedQuery_le_qMLWEBound [NeZero (flatQ q k q)]
    (A : KEMQAdv m₁ m₂ n w q k c a (PK mlkem512Params.toBasic) MLKEM512CT K) (b : Bool) :
    qOwcpaAux mlkem512CompressedScheme hpk eG eJ eKR eC eKa (owRedQuery A b) ≤
      qMLWEBound hpk eG eJ eKR eC eKa A b := by
  refine (qOwcpaAux_le_qIndcpaAux mlkem512CompressedScheme hpk eG eJ eKR eC eKa
    (owRedQuery A b)).trans ?_
  unfold qMLWEBound
  gcongr
  exact qIndcpaAux_le_qMLWE hpk eG eJ eKR eC eKa _

variable [NeZero a] [NeZero (flatQ q k q)] [NeZero (m₁ + m₂)]

open scoped Classical in
/-- **The FIPS 203 KEM over the ML-KEM-512 K-PKE against every quantum adversary
with `k` decapsulation rounds, under quantum module-LWE with oracle access.** With
`q' = flatQ q k q`, `q'' = flatQ (q + 4) k q`, `λ (pk, sk)` a bound on the
decryption-failure fraction of every message under the key pair, `Λ = E λ` and
`ε` a bound on the coin-collision weight `collWeight mlkem512CompressedScheme`,
the advantage is at most the bound of `qINDCCA_le_qOwcpaAux_numeric_coll` at the
normal form `nfKEM A`, with each `δ*` replaced by `Λ` and each one-wayness term
by `qMLWEBound` at `nfKEM A`: module-LWE advantages of `qRedEnc` and `qRedExt`
applied to `indRed eG (owRedQuery (nfKEM A) b)`, plus `|M|⁻¹` and the decryption
error. -/
theorem mlkem512_qindcca_qmlwe_coll
    (A : KEMQAdv m₁ m₂ n w q k c a (PK mlkem512Params.toBasic) MLKEM512CT K)
    (ε : ℝ≥0∞) (hcoll : collWeight mlkem512CompressedScheme ≤ ε)
    (hcoin : ∀ pk sk, mlkem512CompressedScheme.keygen (pk, sk) ≠ 0 → ∀ m, ∃ ρ,
      mlkem512CompressedScheme.dec sk (mlkem512CompressedScheme.enc pk m ρ) = some m)
    (lam : PK mlkem512Params.toBasic × MLWE_PKE_Basic.SK mlkem512Params.toBasic → ℝ≥0∞)
    (hlam : ∀ pk sk, mlkem512CompressedScheme.keygen (pk, sk) ≠ 0 → ∀ x,
      ((badVals (kemBad mlkem512CompressedScheme hpk eG eKR pk sk) x).card : ℝ≥0∞) /
        (n : ℝ≥0∞) ≤ lam (pk, sk)) :
    qINDCCAAdvantage mlkem512CompressedScheme hpk eG eJ eKR eC eKa A ≤
      (4 * ((flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) *
          (qMLWEBound hpk eG eJ eKR eC eKa (nfKEM A) true +
            ∑ i : KEMInput (PK mlkem512Params.toBasic) (MLWE_PKE_Basic.SK mlkem512Params.toBasic)
              Z mlkem512Params.PT K m₁ m₂ n, kemSample mlkem512CompressedScheme i * lam i.1))) ^
            (1 / 2 : ℝ) +
        (8 * (flatQ q k q : ℝ≥0∞) *
            (∑ i : KEMInput (PK mlkem512Params.toBasic) (MLWE_PKE_Basic.SK mlkem512Params.toBasic)
              Z mlkem512Params.PT K m₁ m₂ n, kemSample mlkem512CompressedScheme i * lam i.1) ^
              (1 / 2 : ℝ) +
          (∑ i : KEMInput (PK mlkem512Params.toBasic) (MLWE_PKE_Basic.SK mlkem512Params.toBasic)
              Z mlkem512Params.PT K m₁ m₂ n, kemSample mlkem512CompressedScheme i * lam i.1 +
            ε) +
          8 * (flatQ q k q : ℝ≥0∞) *
            (∑ i : KEMInput (PK mlkem512Params.toBasic) (MLWE_PKE_Basic.SK mlkem512Params.toBasic)
              Z mlkem512Params.PT K m₁ m₂ n, kemSample mlkem512CompressedScheme i * lam i.1) ^
              (1 / 2 : ℝ)) +
        4 * ((flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) *
          (qMLWEBound hpk eG eJ eKR eC eKa (nfKEM A) false +
            ∑ i : KEMInput (PK mlkem512Params.toBasic) (MLWE_PKE_Basic.SK mlkem512Params.toBasic)
              Z mlkem512Params.PT K m₁ m₂ n, kemSample mlkem512CompressedScheme i * lam i.1))) ^
            (1 / 2 : ℝ)) +
      2 * (8 * (flatQ q k q : ℝ≥0∞) * ((Fintype.card Z : ℝ≥0∞)⁻¹) ^ (1 / 2 : ℝ) +
        (8 * (flatQ (q + 4) k q : ℝ≥0∞) *
            (∑ i : KEMInput (PK mlkem512Params.toBasic) (MLWE_PKE_Basic.SK mlkem512Params.toBasic)
              Z mlkem512Params.PT K m₁ m₂ n, kemSample mlkem512CompressedScheme i * lam i.1) ^
              (1 / 2 : ℝ) +
          ∑ i : KEMInput (PK mlkem512Params.toBasic) (MLWE_PKE_Basic.SK mlkem512Params.toBasic)
              Z mlkem512Params.PT K m₁ m₂ n, kemSample mlkem512CompressedScheme i * lam i.1 +
          8 * (flatQ q k q : ℝ≥0∞) *
            (∑ i : KEMInput (PK mlkem512Params.toBasic) (MLWE_PKE_Basic.SK mlkem512Params.toBasic)
              Z mlkem512Params.PT K m₁ m₂ n, kemSample mlkem512CompressedScheme i * lam i.1) ^
              (1 / 2 : ℝ))) := by
  rw [← qINDCCAAdvantage_nfKEM]
  refine (qINDCCA_le_qOwcpaAux_numeric_coll mlkem512CompressedScheme hpk eG eJ eKR eC eKa
    (nfKEM A) hcoin lam hlam ε hcoll (2 * (w * nfX c a k)) (nfKEM_hw w c a k (m₁ + m₂))
    (fun _ _ _ => nfAns (m₁ + m₂) n c a k w) (nfKEM_hseg A) (nfKEM_hrounds A)
    (nfKEM_hinit A)).trans ?_
  have hΛ := deltaStar_le_Lambda mlkem512CompressedScheme hpk eG eKR (Z := Z) (m₂ := m₂) lam hlam
  have hT := qOwcpaAux_owRedQuery_le_qMLWEBound hpk eG eJ eKR eC eKa (nfKEM A) true
  have hF := qOwcpaAux_owRedQuery_le_qMLWEBound hpk eG eJ eKR eC eKa (nfKEM A) false
  gcongr

end MLKEM512

end CatCrypt.Crypto.MLKEM.FIPS203QROMQuantumMLWE

end

end
