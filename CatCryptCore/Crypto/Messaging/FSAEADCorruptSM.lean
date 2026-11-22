/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.FSAEADCorrupt
public import CatCryptCore.Crypto.Messaging.SMScheme

/-!
# Secure messaging with state corruption from PRG and AEAD security

The FS-AEAD reduction `smcFSRed` of `sm_corrupt_advantage_le` forwards each encryption and
challenge query of the secure-messaging adversary as one encryption or challenge query of the
FS-AEAD game and asks nothing else, so an adversary with at most `q` queries gives an FS-AEAD
adversary of cost at most `q` under `fsCost` (`smcFSRed_isQueryBoundBy`). With
`fsaead_corrupt_advantage_le` the FS-AEAD term of `sm_corrupt_advantage_le` becomes PRG and
AEAD advantages of explicit reductions.

## Main results

* `smcFSRed_isQueryBoundBy` — the cost bound of the FS-AEAD reduction
* `sm_corrupt_advantage_le_prim` — secure messaging with state corruption from CKA, PRF-PRNG,
  PRG and AEAD security
* `acdSMAD_corruptAdvantage_le_prim` — the same bound for the ACD construction with associated
  data of the AEAD in `AD`
* `fsCorrAEADRed_isQueryBound` — the AEAD reduction of an FS-AEAD adversary of cost at most `q`
  asks at most `q` queries

## References

* J. Alwen, S. Coretti, Y. Dodis, *The Double Ratchet: Security Notions, Proofs, and
  Modularization for the Signal Protocol*, EUROCRYPT 2019, §4.3 and §5
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open scoped ENNReal

section QueryBound

variable {Sc Msg Key Rand RK Sa W Ct AD : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  {Kt : Type} [SampleableType Kt]

omit [SampleableType Kt] in
/-- Each query of the secure-messaging game in the simulator of the FS-AEAD reduction asks at
most one query of cost `1` of the FS-AEAD game. -/
theorem smFSImplOf_isQueryBoundBy (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct AD Kt)
    (ΔFS ΔPCS t : ℕ) (rkS : RK) (x : FSSim Sc Msg RK Sa) (d : SMQuery W AD) :
    (smFSImplOf C R G D ΔFS ΔPCS t rkS x d).IsQueryBoundBy fsCost 1 := by
  cases d <;> query_bound [smFSImplOf, smFSRatchet, smFSRecv, smFSSend, smFSChall, smFSCorr,
    fsCost]

omit [SampleableType Kt] in
/-- **The cost bound of the FS-AEAD reduction.** If every interaction of `A` asks at most `q`
queries, the FS-AEAD reduction `smcFSRed` has cost at most `q` under `fsCost`. -/
theorem smcFSRed_isQueryBoundBy [Fintype RK] [Nonempty RK] (C : CKADef Sc Msg Key)
    [CKACoins C Rand] (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa))
    (D : AEADDef W Ct AD Kt) (ΔFS ΔPCS : ℕ) (initP : PMF (Msg × Sc × Sc))
    (A : SMCorruptAdv Sc Msg RK Sa W Ct AD) (q : ℕ)
    (hA : ∀ t m, (A.play t m).IsQueryBound q) :
    (smcFSRed C R G D ΔFS ΔPCS initP A).IsQueryBoundBy fsCost q := by
  unfold smcFSRed smFSTreeOf
  intro t i rk rkS
  simpa using OracleAdv.isQueryBoundBy_bind (b := 0) (f := fun r => OracleAdv.ret r.1)
    (OracleAdv.isQueryBoundBy_simulate _ (fun _ => 1) _
      (fun x d => smFSImplOf_isQueryBoundBy C R G D ΔFS ΔPCS t rkS x d)
      (hA t i.1).isQueryBoundBy_one _) (fun _ => trivial)

end QueryBound

section Prim

variable {Sc Msg Key Rand RK Sa W Ct AD : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [Fintype RK] [Nonempty RK] [Fintype Key] [Nonempty Key] [Fintype Sa]
  [Nonempty Sa] [DecidableEq RK] [DecidableEq Key] [DecidableEq AD] {Kt : Type} [SampleableType Kt]

/-- **Secure messaging with state corruption from CKA, PRF-PRNG, PRG and AEAD security.** Under
the hypotheses of `sm_corrupt_advantage_le`, for an adversary `A` whose interactions ask at most
`q` queries, the advantage against the double ratchet is at most the CKA and PRF-PRNG terms of
`sm_corrupt_advantage_le`, the PRG advantages of `fsCorrPRGRed G D b i` for the positions
`i < q` and both challenge bits `b`, and the AEAD advantage of `fsCorrAEADRed G D`, both at the
FS-AEAD reduction `smcFSRed C R G D ΔFS ΔPCS initP A`. -/
theorem sm_corrupt_advantage_le_prim (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (hS : CKACoins.Sound C) (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct AD Kt)
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS) (A : SMCorruptAdv Sc Msg RK Sa W Ct AD)
    (q : ℕ) (hA : ∀ t m, (A.play t m).IsQueryBound q) :
    SM_Corrupt_Advantage C R G D ΔFS ΔPCS A ≤
      ∑ b : Bool, CKA_Corrupt_Advantage C ΔFS ΔPCS (smcCKARed R G D b A) +
        ∑ b : Bool, PRFPRNG_Advantage R (smcRootRed C R G D ΔFS ΔPCS b initP A) +
        (∑ i ∈ Finset.range q,
            PRG_Advantage G (fsCorrPRGRed G D false i (smcFSRed C R G D ΔFS ΔPCS initP A)) +
          ∑ i ∈ Finset.range q,
            PRG_Advantage G (fsCorrPRGRed G D true i (smcFSRed C R G D ΔFS ΔPCS initP A)) +
          AEAD_CCA_Advantage D (fsCorrAEADRed G D (smcFSRed C R G D ΔFS ΔPCS initP A))) := by
  refine (sm_corrupt_advantage_le C hS initP hinit R G D hFS hPCS A).trans ?_
  gcongr
  exact fsaead_corrupt_advantage_le G D q _ (smcFSRed_isQueryBoundBy C R G D ΔFS ΔPCS initP A q hA)

/-- **The ACD construction with associated data in `AD` from CKA, PRF-PRNG, PRG and AEAD
security.** Under the hypotheses of `acdSMAD_corruptAdvantage_le`, for an adversary `A` whose
interactions ask at most `q` queries, the FS-AEAD term of `acdSMAD_corruptAdvantage_le` is
replaced by the PRG and AEAD terms of `fsaead_corrupt_advantage_le` at the FS-AEAD reduction of
the relabelled adversary `A.toSMAD f`. -/
theorem acdSMAD_corruptAdvantage_le_prim (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (hS : CKACoins.Sound C) {J : Sc → Sc → Prop} (hJ : CKACorrect C J)
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (hJi : ∀ i ∈ initP.support, J i.2.1 i.2.2) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct AD Kt) (f : W → AD) {ΔFS ΔPCS : ℕ}
    (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS) (A : SMSchemeAdv Msg W Ct (SMPartySt Sc RK Sa)) (q : ℕ)
    (hA : ∀ t T, (A.play t T).IsQueryBound q) :
    (acdSMAD C R G D fun _ => f).corruptAdvantage ΔFS ΔPCS A ≤
      ∑ b : Bool, CKA_Corrupt_Advantage C ΔFS ΔPCS (smcCKARed R G D b (A.toSMAD f)) +
        ∑ b : Bool, PRFPRNG_Advantage R (smcRootRed C R G D ΔFS ΔPCS b initP (A.toSMAD f)) +
        (∑ i ∈ Finset.range q, PRG_Advantage G
            (fsCorrPRGRed G D false i (smcFSRed C R G D ΔFS ΔPCS initP (A.toSMAD f))) +
          ∑ i ∈ Finset.range q, PRG_Advantage G
            (fsCorrPRGRed G D true i (smcFSRed C R G D ΔFS ΔPCS initP (A.toSMAD f))) +
          AEAD_CCA_Advantage D
            (fsCorrAEADRed G D (smcFSRed C R G D ΔFS ΔPCS initP (A.toSMAD f)))) := by
  refine (acdSMAD_corruptAdvantage_le C hS hJ initP hinit hJi R G D f hFS hPCS A).trans ?_
  gcongr
  exact fsaead_corrupt_advantage_le G D q _ (smcFSRed_isQueryBoundBy C R G D ΔFS ΔPCS initP _ q
    (SMSchemeAdv.toSMAD_play_isQueryBound f hA))

end Prim

section AEADRed

variable {Sa W Ct AD : Type} [SampleableType W] [Fintype Sa] [Nonempty Sa] {Kt : Type}
  [SampleableType Kt]

/-- **The query bound of the AEAD reduction of the FS-AEAD game.** For an adversary of cost at
most `q` under `fsCost`, the AEAD reduction `fsCorrAEADRed G D B` asks at most `q` queries. -/
theorem fsCorrAEADRed_isQueryBound (G : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct AD Kt)
    (B : OracleAdv (FSQuery W AD) (FSAns Sa Ct) Bool) (q : ℕ) (hB : B.IsQueryBoundBy fsCost q) :
    (fsCorrAEADRed G D B).IsQueryBound q := by
  have himpl : ∀ h d, (fsCorrAEADImpl G D h d).IsQueryBound (fsCost d) := by
    intro h d
    cases d <;> query_bound [fsCorrAEADImpl, fsCost]
  unfold fsCorrAEADRed
  simpa using OracleAdv.isQueryBound_bind (n := 0) (f := fun x => OracleAdv.ret x.1)
    (OracleAdv.isQueryBound_simulate _ fsCost himpl hB fsLzInit) (fun _ => trivial)

end AEADRed

end CatCrypt.Crypto.Messaging
