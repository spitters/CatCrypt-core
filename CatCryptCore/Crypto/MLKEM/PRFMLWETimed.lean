/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.PRFMLWE
public import CatCryptCore.Quantum.QROM.AdversariesTimed
public import CatCryptCore.Tactics.DeriveReduction

/-!
# Time certificates of the module-LWE hops of `PRFMLWE`

The costed forms `qRedEncF.tree.timed` and `qRedExtF.tree.timed` of the two hops from an
IND-CPA adversary with the PRF-extended oracle (`QIndAuxPrfAdv`) to standard quantum
module-LWE distinguishers, derived by `derive_reduction`, with their erasure theorems
`qRedEncF.erase_timed` and `qRedExtF.erase_timed`. The costed mirror `QIndAuxPrfAdv.Timed` of
the adversary structure is derived by `derive_timed_structure`.

Each hop computes the challenge ciphertext and runs the circuit of the adversary with its oracle
absorbed (`absorbOracle`, costed `QAdvT.absorb`): each of the `Q` oracle calls becomes one gate
of weight one, so the time of the absorbed circuit is the time of the adversary, which counts
its gates and its `Q` calls (`QAdvT.time_absorb`). The time of a hop is that time plus the cost
of the encryption (for `qRedExtF`, of the compression, the ring addition and the message
encoding), of the message choice and a constant. The tables `ΦG`, `ΦJ`, `ΦH`, `ΦT`, `ΦF` and
the oracle `auxOracleF` enter only through the absorbed oracle gate and are not charged.

`derive_time_bound` does not apply: it bounds costed trees of the kinds `SPTree` and
`OracleAdv`, and the result of these hops is a step-prefixed costed circuit `ℕ × QAdvT`. The
time theorems are proved from the costed forms by `QAdvT.time_absorb` and `grind`.

## Main results

* `qRedEncF.timeBound` — an adversary of time `T` (gates and oracle calls) gives a distinguisher
  of time `T + F + Va + Mv + Mt + 4 * Ss + 2 * Ra + Vd + En + Ms + 21`, in the bounds of the
  costs of the compression and the operations of the scheme (the short sampler is evaluated
  four times by the encryption)
* `qRedExtF.timeBound` — an adversary of time `T` gives a distinguisher of time
  `T + F + Ra + En + Ms + 7`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLKEM.PRFMLWE

open CatCrypt.Quantum.QROM

derive_timed_structure CatCrypt.Crypto.MLKEM.PRFAuxHop.QIndAuxPrfAdv

derive_reduction qRedEncF

derive_reduction qRedExtF

open CatCrypt.Crypto.MLKEM.PRFAuxHop (QIndAuxPrfAdv) in
/-- **Time of `qRedEncF`.** If every circuit of the costed adversary, with the cost of computing
it, runs within `T`, then every circuit of the first hop runs within
`T + Fc + Va + Mv + Mt + 4 * Ss + 2 * Ra + Vd + En + Ms + 21`, where `Fc` bounds the
compression, `Va`, `Mv`, `Mt`, `Ss`, `Ra`, `Vd`, `En` the operations of the scheme used by the
encryption, and `Ms` the message choice. -/
theorem qRedEncF.timeBound {Sd Nc SK C KS K Hash Z Φ ι : Type} {m₁ m₂ m₃ n W Q : ℕ}
    [Fintype Φ] [Nonempty Φ] [Fintype Sd] [Nonempty Sd] [DecidableEq Z] [DecidableEq Hash]
    [NeZero n] (P : MLWE_PKE_Scheme.Params) (f : MLWE_PKE_Basic.CT P.toBasic → C)
    (fCost : MLWE_PKE_Basic.CT P.toBasic → ℕ) (g : C → MLWE_PKE_Basic.CT P.toBasic)
    (gCost : C → ℕ) (eD : Sd × Nc ≃ Fin m₃) (kg : Φ → KS → MLWE_PKE_Basic.PK P.toBasic × SK)
    (kgCost : Φ → KS → ℕ) (enc : MLWE_PKE_Basic.PK P.toBasic → P.PT → (Nc → Fin n) → C)
    (encCost : MLWE_PKE_Basic.PK P.toBasic → P.PT → (Nc → Fin n) → ℕ)
    (dec : SK → C → Option P.PT) (decCost : SK → C → ℕ) (eK : (Nc → Fin n) → KS)
    (eKCost : (Nc → Fin n) → ℕ) (hpk : MLWE_PKE_Basic.PK P.toBasic → Hash)
    (hpkCost : MLWE_PKE_Basic.PK P.toBasic → ℕ) (eG : P.PT × Hash ≃ Fin m₁)
    (eJ : Z × C ≃ Fin m₂) (eKR : K × Sd ≃ Fin n) {ΩG ΩJ ΩH ΩT ΩF : Type}
    (ΦG : ΩG → Fin m₁ → Fin n) (ΦGCost : ΩG → Fin m₁ → ℕ) (ΦJ : ΩJ → Fin m₂ → Fin n)
    (ΦJCost : ΩJ → Fin m₂ → ℕ) (ΦH : ΩH → C → K) (ΦHCost : ΩH → C → ℕ)
    (ΦT : ΩT → C → Fin n) (ΦTCost : ΩT → C → ℕ) (ΦF : ΩF → Fin m₃ → Fin n)
    (ΦFCost : ΩF → Fin m₃ → ℕ)
    (B : QIndAuxPrfAdv ι m₁ m₂ m₃ n W Q (MLWE_PKE_Basic.PK P.toBasic) C K P.PT) (b : Bool)
    (prog : MLWE_PKE_Basic.PK P.toBasic → C → (C → K) → ι → QAdvT (m₁ + m₂ + m₃) n W Q)
    (progCost : MLWE_PKE_Basic.PK P.toBasic → C → (C → K) → ι → ℕ)
    (vec_addCost : P.Vec → P.Vec → ℕ) (mat_vec_mulCost : P.Mat → P.Vec → ℕ)
    (mat_transposeCost : P.Mat → ℕ) (sampleShortCost : P.Seed → ℕ)
    (ring_addCost : P.R → P.R → ℕ) (vec_dotCost : P.Vec → P.Vec → ℕ)
    (m_encodeCost : P.PT → ℕ) (msgsCost : MLWE_PKE_Basic.PK P.toBasic → ι → ℕ)
    (T Fc Va Mv Mt Ss Ra Vd En Ms : ℕ)
    (hT : ∀ pk c h i, QAdvT.StepTimeBound (progCost pk c h i, prog pk c h i) T)
    (hF : ∀ u, fCost u ≤ Fc) (hVa : ∀ u v, vec_addCost u v ≤ Va)
    (hMv : ∀ u v, mat_vec_mulCost u v ≤ Mv) (hMt : ∀ u, mat_transposeCost u ≤ Mt)
    (hSs : ∀ u, sampleShortCost u ≤ Ss) (hRa : ∀ u v, ring_addCost u v ≤ Ra)
    (hVd : ∀ u v, vec_dotCost u v ≤ Vd) (hEn : ∀ u, m_encodeCost u ≤ En)
    (hMs : ∀ pk i, msgsCost pk i ≤ Ms) (pk : MLWE_PKE_Basic.PK P.toBasic)
    (s : ι × P.Seed × Z × ΩG × ΩJ × ΩH × ΩT × ΩF) :
    QAdvT.StepTimeBound (qRedEncF.tree.timed P f fCost g gCost eD kg kgCost enc encCost dec
      decCost eK eKCost hpk hpkCost eG eJ eKR ΦG ΦGCost ΦJ ΦJCost ΦH ΦHCost ΦT ΦTCost ΦF ΦFCost B b
      pk s prog progCost vec_addCost mat_vec_mulCost mat_transposeCost sampleShortCost ring_addCost
      vec_dotCost m_encodeCost msgsCost)
      (T + Fc + Va + Mv + Mt + 4 * Ss + 2 * Ra + Vd + En + Ms + 21) := by
  simp only [QAdvT.StepTimeBound] at hT ⊢
  simp only [qRedEncF.tree.timed, QAdvT.time_absorb]
  grind

open CatCrypt.Crypto.MLKEM.PRFAuxHop (QIndAuxPrfAdv) in
/-- **Time of `qRedExtF`.** If every circuit of the costed adversary, with the cost of computing
it, runs within `T`, and the compression, the ring addition, the message encoding and the
message choice cost at most `Fc`, `Ra`, `En` and `Ms`, then every circuit of the second hop runs
within `T + Fc + Ra + En + Ms + 7`. -/
theorem qRedExtF.timeBound {Sd Nc SK C KS K Hash Z Φ ι : Type} {m₁ m₂ m₃ n W Q : ℕ}
    [Fintype Φ] [Nonempty Φ] [Fintype Sd] [Nonempty Sd] [DecidableEq Z] [DecidableEq Hash]
    [NeZero n] (P : MLWE_PKE_Scheme.Params) (f : MLWE_PKE_Basic.CT P.toBasic → C)
    (fCost : MLWE_PKE_Basic.CT P.toBasic → ℕ) (eD : Sd × Nc ≃ Fin m₃)
    (kg : Φ → KS → MLWE_PKE_Basic.PK P.toBasic × SK) (kgCost : Φ → KS → ℕ)
    (enc : MLWE_PKE_Basic.PK P.toBasic → P.PT → (Nc → Fin n) → C)
    (encCost : MLWE_PKE_Basic.PK P.toBasic → P.PT → (Nc → Fin n) → ℕ)
    (dec : SK → C → Option P.PT) (decCost : SK → C → ℕ) (eK : (Nc → Fin n) → KS)
    (eKCost : (Nc → Fin n) → ℕ) (hpk : MLWE_PKE_Basic.PK P.toBasic → Hash)
    (hpkCost : MLWE_PKE_Basic.PK P.toBasic → ℕ) (eG : P.PT × Hash ≃ Fin m₁)
    (eJ : Z × C ≃ Fin m₂) (eKR : K × Sd ≃ Fin n) {ΩG ΩJ ΩH ΩT ΩF : Type}
    (ΦG : ΩG → Fin m₁ → Fin n) (ΦGCost : ΩG → Fin m₁ → ℕ) (ΦJ : ΩJ → Fin m₂ → Fin n)
    (ΦJCost : ΩJ → Fin m₂ → ℕ) (ΦH : ΩH → C → K) (ΦHCost : ΩH → C → ℕ)
    (ΦT : ΩT → C → Fin n) (ΦTCost : ΩT → C → ℕ) (ΦF : ΩF → Fin m₃ → Fin n)
    (ΦFCost : ΩF → Fin m₃ → ℕ)
    (B : QIndAuxPrfAdv ι m₁ m₂ m₃ n W Q (MLWE_PKE_Basic.PK P.toBasic) C K P.PT) (b : Bool)
    (prog : MLWE_PKE_Basic.PK P.toBasic → C → (C → K) → ι → QAdvT (m₁ + m₂ + m₃) n W Q)
    (progCost : MLWE_PKE_Basic.PK P.toBasic → C → (C → K) → ι → ℕ)
    (ring_addCost : P.R → P.R → ℕ) (m_encodeCost : P.PT → ℕ)
    (msgsCost : MLWE_PKE_Basic.PK P.toBasic → ι → ℕ) (T Fc Ra En Ms : ℕ)
    (hT : ∀ pk c h i, QAdvT.StepTimeBound (progCost pk c h i, prog pk c h i) T)
    (hF : ∀ u, fCost u ≤ Fc) (hRa : ∀ u v, ring_addCost u v ≤ Ra)
    (hEn : ∀ u, m_encodeCost u ≤ En) (hMs : ∀ pk i, msgsCost pk i ≤ Ms)
    (x : P.Mat × P.Vec × P.Vec × P.R) (s : ι × Z × ΩG × ΩJ × ΩH × ΩT × ΩF) :
    QAdvT.StepTimeBound (qRedExtF.tree.timed P f fCost eD kg kgCost enc encCost dec decCost eK
      eKCost hpk hpkCost eG eJ eKR ΦG ΦGCost ΦJ ΦJCost ΦH ΦHCost ΦT ΦTCost ΦF ΦFCost B b x s prog
      progCost ring_addCost m_encodeCost msgsCost) (T + Fc + Ra + En + Ms + 7) := by
  simp only [QAdvT.StepTimeBound] at hT ⊢
  simp only [qRedExtF.tree.timed, QAdvT.time_absorb]
  grind

end CatCrypt.Crypto.MLKEM.PRFMLWE
