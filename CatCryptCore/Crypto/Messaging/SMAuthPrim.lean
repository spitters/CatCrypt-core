/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SMAuthFSInt

/-!
# Authenticity of the ACD construction from its primitives

The authenticity advantage of an adversary asking at most `N` queries against the ACD secure
messaging scheme with decryption `acdAuthSM C R G D` is bounded by advantages of explicit
reductions in the games of its primitives: the corruption bound of `acdAuthSM_authAdvantage_le`
(CKA corruption, PRF-PRNG and FS-AEAD with corruption), and, for each epoch `k < N`, the CKA
corruption advantage of `smAuthCKARed`, the PRF-PRNG advantage of `smAuthRootRed` and the
FS-AEAD integrity advantage of `smAuthFSRed` of `acdAuthSM_truncGame_le_fsint`.

## Main results

* `acdAuthSM_intAdvantage_le_prim` — the integrity advantage as a sum over the epochs of
  primitive advantages
* `acdAuthSM_authAdvantage_le_prim` — the authenticity advantage bounded by primitive
  advantages only
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open scoped ENNReal

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [DecidableEq W] [DecidableEq Ct] [Fintype RK] [Nonempty RK] [Fintype Key]
  [Nonempty Key] [Fintype Sa] [Nonempty Sa] [DecidableEq RK] [DecidableEq Key]

/-- **Integrity of the ACD construction from its primitives.** Under the hypotheses of
`acdAuthSM_truncGame_le_fsint`, for an adversary asking at most `N` queries, the integrity
advantage against `acdAuthSM C R G D` is at most the sum over the epochs `k < N` of the CKA
corruption advantage of `smAuthCKARed`, the PRF-PRNG advantage of `smAuthRootRed` and the FS-AEAD
integrity advantage of `smAuthFSRed` at the epoch `k`. -/
theorem acdAuthSM_intAdvantage_le_prim (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (hS : CKACoins.Sound C) {J : Sc → Sc → Prop} (hJ : CKACorrect C J)
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (hJi : ∀ i ∈ initP.support, J i.2.1 i.2.2) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS)
    (hPCS : 1 ≤ ΔPCS) (N : ℕ) (A : SMAuthAdv Msg W Ct (SMPartySt Sc RK Sa))
    (hA : ∀ t pub, (A.play t pub).IsQueryBound N) :
    (acdAuthSM C R G D).intAdvantage ΔFS ΔPCS A ≤
      ∑ k ∈ Finset.range N,
        (CKA_Corrupt_Advantage C ΔFS ΔPCS (smAuthCKARed R G D ΔFS ΔPCS k A) +
          PRFPRNG_Advantage R (smAuthRootRed C R G D ΔFS ΔPCS k initP A) +
          FSAEAD_Int_Advantage G D (smAuthFSRed C R G D ΔFS ΔPCS k initP A)) := by
  refine ((acdAuthSM C R G D).intAdvantage_le_sum ΔFS ΔPCS N A hA).trans ?_
  refine Finset.sum_le_sum fun k _ => ?_
  refine ((acdAuthSM C R G D).epochIntAdvantage_le_bad ΔFS ΔPCS k A).trans ?_
  rw [← smAuthTruncGame_eq]
  exact acdAuthSM_truncGame_le_fsint C hS hJ initP hinit hJi R G D hFS hPCS k A

/-- **Authenticity of the ACD construction from its primitives.** For a CKA correct along `J`
with a sound explicit-randomness sending algorithm, an initialisation that is the lift of
`initP` with initial states related by `J`, `2 ≤ ΔFS` and `1 ≤ ΔPCS`, the authenticity advantage
of an adversary `A` asking at most `N` queries against `acdAuthSM C R G D` is at most the sum over
the epochs `k < N` of the CKA corruption advantage of `smAuthCKARed`, the PRF-PRNG advantage of
`smAuthRootRed` and the FS-AEAD integrity advantage of `smAuthFSRed` at the epoch `k`, plus the
CKA corruption advantages of `smcCKARed`, the PRF-PRNG advantages of `smcRootRed` and the FS-AEAD
advantage with corruption of `smcFSRed` at `smAuthRed ΔFS ΔPCS A`. -/
theorem acdAuthSM_authAdvantage_le_prim (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (hS : CKACoins.Sound C) {J : Sc → Sc → Prop} (hJ : CKACorrect C J)
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (hJi : ∀ i ∈ initP.support, J i.2.1 i.2.2) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS)
    (hPCS : 1 ≤ ΔPCS) (N : ℕ) (A : SMAuthAdv Msg W Ct (SMPartySt Sc RK Sa))
    (hA : ∀ t pub, (A.play t pub).IsQueryBound N) :
    (acdAuthSM C R G D).authAdvantage ΔFS ΔPCS A ≤
      ∑ k ∈ Finset.range N,
          (CKA_Corrupt_Advantage C ΔFS ΔPCS (smAuthCKARed R G D ΔFS ΔPCS k A) +
            PRFPRNG_Advantage R (smAuthRootRed C R G D ΔFS ΔPCS k initP A) +
            FSAEAD_Int_Advantage G D (smAuthFSRed C R G D ΔFS ΔPCS k initP A)) +
        (∑ b : Bool, CKA_Corrupt_Advantage C ΔFS ΔPCS
            (smcCKARed R G D b (smAuthRed ΔFS ΔPCS A).toSM) +
          ∑ b : Bool, PRFPRNG_Advantage R
            (smcRootRed C R G D ΔFS ΔPCS b initP (smAuthRed ΔFS ΔPCS A).toSM) +
          FSAEAD_Corrupt_Advantage G D
            (smcFSRed C R G D ΔFS ΔPCS initP (smAuthRed ΔFS ΔPCS A).toSM)) :=
  (acdAuthSM_authAdvantage_le C hS hJ initP hinit hJi R G D hFS hPCS A).trans
    (add_le_add_left
      (acdAuthSM_intAdvantage_le_prim C hS hJ initP hinit hJi R G D hFS hPCS N A hA) _)

end CatCrypt.Crypto.Messaging
