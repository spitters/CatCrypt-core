/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SMAuthFSInt
public import CatCryptCore.Crypto.Messaging.FSAEADInt

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
* `smAuthFSTree_isQueryBoundBy`, `smAuthFSRed_isQueryBoundBy` — the FS-AEAD integrity reduction
  decrypts at positions below `M` only when the adversary delivers at positions below `M` only
  (`smAuthFar`)
* `acdAuthSM_authAdvantage_le_aead` — the authenticity advantage bounded by CKA, PRF-PRNG,
  single-step PRG and AEAD advantages and the confidentiality terms
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

/-- The cost of a query of the authenticity game that delivers at a position from `M` on: `1`
for such a delivery, `0` otherwise. An adversary bounded by `0` in this cost delivers at
positions below `M` only. -/
def smAuthFar (M : ℕ) : SMAuthQuery W Ct → ℕ
  | .deliver _ j _ _ => if M ≤ j then 1 else 0
  | .sm _ => 0

omit [DecidableEq W] [DecidableEq Ct] [DecidableEq RK] [DecidableEq Key] [Fintype RK]
  [Fintype Key] [Fintype Sa] [SampleableType Ct] [Nonempty RK] [Nonempty Key] [Nonempty Sa] in
/-- A query of the corruption game in the simulator of the integrity hop asks no decryption. -/
theorem smAuthFSImplAt_isQueryBoundBy (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) (rkS : RK) (x : FSSim Sc Msg RK Sa) (q : SMQuery W) (M : ℕ) :
    (smAuthFSImplAt C R G D ΔFS ΔPCS t k rkS x q).IsQueryBoundBy
      (fsIntFar (W := W) (Ct := Ct) M) 0 := by
  have hc : ∀ q : FSQuery W, fsIntFar (Ct := Ct) M (fsIntQ q) = 0 := fun q => by
    cases q <;> rfl
  cases q with
  | chall p m =>
    change (smAuthFSChall G D t x p m).IsQueryBoundBy _ 0
    unfold smAuthFSChall
    split
    · exact OracleAdv.isQueryBoundBy_mapQueryAnswer_zero _ _ hc _
    · split
      · split <;> trivial
      · trivial
  | _ => exact OracleAdv.isQueryBoundBy_mapQueryAnswer_zero _ _ hc _

omit [DecidableEq RK] [DecidableEq Key] [Fintype RK] [Fintype Key] [Fintype Sa]
  [SampleableType Ct] [Nonempty RK] [Nonempty Key] [Nonempty Sa] in
/-- A query `d` of the authenticity game in the simulator of the integrity hop asks decryptions
at positions from `M` on of total cost at most `smAuthFar M d`. -/
theorem smAuthFSImpl_isQueryBoundBy (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) (rkS : RK) (σ : (FSSim Sc Msg RK Sa × SMAuthAux W Ct) × Bool)
    (d : SMAuthQuery W Ct) (M : ℕ) :
    (smAuthFSImpl C R G D ΔFS ΔPCS t k rkS σ d).IsQueryBoundBy (fsIntFar M) (smAuthFar M d) := by
  unfold smAuthFSImpl
  split
  · cases d with
    | sm q =>
      simp only [smAuthFSStep]
      simpa using OracleAdv.isQueryBoundBy_bind
        (smAuthFSImplAt_isQueryBoundBy C R G D ΔFS ΔPCS t k rkS σ.1.1 q M)
        (fun y => by split <;> trivial)
    | deliver p j ad c =>
      simp only [smAuthFSStep]
      split
      · exact ⟨by simp [fsIntFar, smAuthFar], fun _ => trivial⟩
      · trivial
  · trivial

omit [DecidableEq RK] [DecidableEq Key] [Fintype Key] [Fintype Sa] [SampleableType Ct]
  [Nonempty Key] [Nonempty Sa] in
/-- **Decryption positions of the FS-AEAD integrity reduction.** When every interaction `play t
pub` delivers at positions below `M` only, the tree `smAuthFSTree` decrypts at positions below
`M` only. -/
theorem smAuthFSTree_isQueryBoundBy (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS k : ℕ) (initP : PMF (Msg × Sc × Sc)) (tStar : PMF ℕ)
    (play : ℕ → Msg → OracleAdv (SMAuthQuery W Ct) (SMAuthAns Msg Ct (SMPartySt Sc RK Sa) W) Bool)
    (M : ℕ) (hplay : ∀ t pub, (play t pub).IsQueryBoundBy (smAuthFar M) 0) :
    (smAuthFSTree C R G D ΔFS ΔPCS k initP tStar play).IsQueryBoundBy (fsIntFar M) 0 := by
  unfold smAuthFSTree
  intro t i rk rkS
  simpa using OracleAdv.isQueryBoundBy_bind (b := 0) (f := fun r => OracleAdv.ret r.2.2)
    (OracleAdv.isQueryBoundBy_simulate _ (smAuthFar M) _
      (fun σ d => smAuthFSImpl_isQueryBoundBy C R G D ΔFS ΔPCS t k rkS σ d M) (hplay t i.1) _)
    (fun _ => trivial)

omit [DecidableEq RK] [DecidableEq Key] [Fintype Key] [Fintype Sa] [SampleableType Ct]
  [Nonempty Key] [Nonempty Sa] in
/-- The FS-AEAD integrity reduction `smAuthFSRed` of an adversary that delivers at positions
below `M` only decrypts at positions below `M` only. -/
theorem smAuthFSRed_isQueryBoundBy (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS k : ℕ) (initP : PMF (Msg × Sc × Sc)) (A : SMAuthAdv Msg W Ct (SMPartySt Sc RK Sa))
    (M : ℕ) (hM : ∀ t pub, (A.play t pub).IsQueryBoundBy (smAuthFar M) 0) :
    (smAuthFSRed C R G D ΔFS ΔPCS k initP A).IsQueryBoundBy (fsIntFar M) 0 :=
  smAuthFSTree_isQueryBoundBy C R G D ΔFS ΔPCS k initP A.tStar A.play M hM

/-- **Authenticity of the ACD construction from CKA, PRF-PRNG, PRG and AEAD security.** Under
the hypotheses of `acdAuthSM_authAdvantage_le_prim`, for an adversary `A` asking at most `N`
queries and delivering at positions below `M` only, the authenticity advantage against
`acdAuthSM C R G D` is at most the sum over the epochs `k < N` of the CKA corruption advantage of
`smAuthCKARed`, the PRF-PRNG advantage of `smAuthRootRed`, the PRG advantages of the FS-PRG
reductions `fsprgRed G M i` for `i < M` and the AEAD advantages of `fsIntRed G D M j` for
`j < M` at the FS-AEAD integrity reduction `smAuthFSRed` of the epoch `k`, plus the
confidentiality terms of `acdAuthSM_authAdvantage_le_prim`. -/
theorem acdAuthSM_authAdvantage_le_aead (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (hS : CKACoins.Sound C) {J : Sc → Sc → Prop} (hJ : CKACorrect C J)
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (hJi : ∀ i ∈ initP.support, J i.2.1 i.2.2) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS)
    (hPCS : 1 ≤ ΔPCS) (N M : ℕ) (A : SMAuthAdv Msg W Ct (SMPartySt Sc RK Sa))
    (hA : ∀ t pub, (A.play t pub).IsQueryBound N)
    (hM : ∀ t pub, (A.play t pub).IsQueryBoundBy (smAuthFar M) 0) :
    (acdAuthSM C R G D).authAdvantage ΔFS ΔPCS A ≤
      ∑ k ∈ Finset.range N,
          (CKA_Corrupt_Advantage C ΔFS ΔPCS (smAuthCKARed R G D ΔFS ΔPCS k A) +
            PRFPRNG_Advantage R (smAuthRootRed C R G D ΔFS ΔPCS k initP A) +
            (∑ i ∈ Finset.range M, PRG_Advantage G
                (fsprgRed G M i (fsIntPost G D (smAuthFSRed C R G D ΔFS ΔPCS k initP A))) +
              ∑ j ∈ Finset.range M, AEAD_CCA_Advantage D
                (fsIntRed G D M j (smAuthFSRed C R G D ΔFS ΔPCS k initP A)))) +
        (∑ b : Bool, CKA_Corrupt_Advantage C ΔFS ΔPCS
            (smcCKARed R G D b (smAuthRed ΔFS ΔPCS A).toSM) +
          ∑ b : Bool, PRFPRNG_Advantage R
            (smcRootRed C R G D ΔFS ΔPCS b initP (smAuthRed ΔFS ΔPCS A).toSM) +
          FSAEAD_Corrupt_Advantage G D
            (smcFSRed C R G D ΔFS ΔPCS initP (smAuthRed ΔFS ΔPCS A).toSM)) := by
  refine (acdAuthSM_authAdvantage_le_prim C hS hJ initP hinit hJi R G D hFS hPCS N A hA).trans ?_
  gcongr with k hk
  exact fsaead_int_advantage_le_prg G D M _
    (smAuthFSRed_isQueryBoundBy C R G D ΔFS ΔPCS k initP A M hM)

end CatCrypt.Crypto.Messaging
