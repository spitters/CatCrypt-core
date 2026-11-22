/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.FSAEADCorruptSM
public import CatCryptCore.Crypto.Messaging.TripleRatchetDeployed

/-!
# The deployed Triple Ratchet from its primitives

The bound `tripleRatchetDeployed_idAdvantage_le_fs` on the immediate-decryption advantage
against the deployed Triple Ratchet has an FS-AEAD term with corruption at the message AEAD
`deployedAEAD D₀ F E`. For an adversary with at most `q` queries, `fsaead_corrupt_advantage_le`
replaces it by PRG advantages and the AEAD advantage of `fsCorrAEADRed` against the message
AEAD, and `deployedAEAD_advantage_le` replaces the latter by the left dual-PRF advantage of the
mixing `F` and the AEAD advantages of `D₀` at the salts asked. The AEAD reduction asks at most
`q` queries, so its relabelled adversary asks at most `q` distinct salts
(`OracleAdv.indexBound_of_isQueryBound`).

## Main results

* `OracleAdv.indexBound_of_isQueryBound` — an adversary with at most `q` queries asks at most
  `q` indices beyond `G`
* `tripleRatchetDeployedRed_toSMAD_play_isQueryBound` — the reduction of the deployed Triple
  Ratchet keeps the query bound of the adversary
* `tripleRatchetDeployed_idAdvantage_le_prim` — the immediate-decryption advantage against the
  deployed Triple Ratchet from the integrity advantage of the ACD construction, CKA, PRF-PRNG,
  PRG, dual-PRF and AEAD security and the two wrong-salt events of the sidecar

## References

* Y. Dodis, D. Jost, S. Katsumata, T. Prest, R. Schmidt, *Triple Ratchet: A Bandwidth Efficient
  Hybrid-Secure Signal Protocol*, ePrint 2025/078.
* J. Alwen, S. Coretti, Y. Dodis, *The Double Ratchet: Security Notions, Proofs, and
  Modularization for the Signal Protocol*, EUROCRYPT 2019.
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open scoped ENNReal

/-- An adversary with at most `q` queries asks at most `q` indices beyond `G`. -/
theorem OracleAdv.indexBound_of_isQueryBound {N D R α : Type} [DecidableEq N] (ι : D → N)
    {A : OracleAdv D R α} {q : ℕ} (hA : A.IsQueryBound q) (G : Finset N) :
    A.IndexBound ι G (G.card + q) := by
  induction A generalizing q G with
  | ret a => trivial
  | rand p k ih => exact fun b => ih b (hA b) G
  | query d k ih =>
    cases q with
    | zero => exact hA.elim
    | succ q =>
      have hc := Finset.card_insert_le (ι d) G
      exact ⟨by omega, fun r => (ih r (hA r) (insert (ι d) G)).mono le_rfl (by omega)⟩

section Deployed

variable {Sc Msg Key Rand RK Sa W Ct PSt PHdr S : Type} [Fintype Rand] [Nonempty Rand]
  [SampleableType W] [SampleableType Ct] [Fintype RK] [Nonempty RK] [Inhabited Msg]
  [DecidableEq Msg] [DecidableEq W] [DecidableEq Ct] [DecidableEq PHdr]

omit [Fintype Rand] [Nonempty Rand] [DecidableEq PHdr] in
/-- **The query bound of the reduction of the deployed Triple Ratchet.** If every interaction of
`A` asks at most `q` queries, so does every interaction of the relabelled reduction
`(tripleRatchetDeployedRed … A).toSMAD dec`. -/
theorem tripleRatchetDeployedRed_toSMAD_play_isQueryBound (C : CKADef Sc Msg Key)
    [CKACoins C Rand] (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D₀ : AEADDef W Ct ((PHdr × W) × ACDHdr Msg)) (F : W → S → W)
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored : ℕ)
    (P : SidecarDef PSt PHdr S) (E : SidecarPack PHdr S W) (ΔFS ΔPCS : ℕ)
    (A : SMIDAdv (Msg × ℕ) W (ACDHdr Msg × PHdr) Ct (ACDIDLeak Sc RK Sa Msg W × PSt)) (q : ℕ)
    (hA : ∀ t pub, (A.play t pub).IsQueryBound q) (t : ℕ) (pub : Msg) :
    (((tripleRatchetDeployedRed C R G D₀ F dec enc maxSkip maxStored P E ΔFS ΔPCS A).toSMAD
      (Sc := Sc) dec).play t pub).IsQueryBound q := by
  refine SMSchemeAdv.toSMAD_play_isQueryBound dec (fun t pub => ?_) t pub
  have hside : ∀ t pub, ((sidecarRed P E A).play t pub).IsQueryBound q := by
    intro t pub
    simpa [sidecarRed] using
      OracleAdv.isQueryBound_bind (n := 0) (f := fun x => OracleAdv.ret x.1)
      (OracleAdv.isQueryBound_simulate_mul (c := 1)
        (fun ys d => by cases d <;> query_bound [sidecarImpl]) (hA t pub) _)
      (fun _ => trivial)
  simpa [tripleRatchetDeployedRed, smIDRed] using
    OracleAdv.isQueryBound_bind (n := 0) (f := fun x => OracleAdv.ret x.1)
    (OracleAdv.isQueryBound_simulate_mul (c := 1)
      (fun σ d => by cases d <;> query_bound [smIDImpl]) (hside t _) _)
    (fun _ => trivial)

/-- **The deployed Triple Ratchet from CKA, PRF-PRNG, PRG, dual-PRF and AEAD security.** Under
the hypotheses of `tripleRatchetDeployed_idAdvantage_le_fs`, for an injective decoding
`E.unpack` and an adversary `A` whose interactions ask at most `q` queries, the
immediate-decryption advantage against the deployed Triple Ratchet is at most the integrity
advantage of the ACD construction with headers, the CKA and PRF-PRNG terms of
`tripleRatchetDeployed_idAdvantage_le_fs`, the PRG advantages of `fsCorrPRGRed` at the positions
`i < q`, the left dual-PRF advantage of `F` at `saltedPRFRed` and the AEAD advantages of `D₀` at
`saltedAEADRed j` for `j < q`, and the two wrong-salt events of the sidecar. The reductions of
the last three groups are applied to the FS-AEAD reduction `smcFSRed` of the relabelled
reduction `(tripleRatchetDeployedRed … A).toSMAD dec`, through the AEAD reduction
`fsCorrAEADRed` and the relabelling `aeadAdvMapAD (deployedAD E)`. The injective packing
`SidecarPack` into a finite word type forces a single salt and a single sidecar header, so the
statement applies only to runs with a constant salt. -/
theorem tripleRatchetDeployed_idAdvantage_le_prim [Fintype Key] [Nonempty Key] [Fintype Sa]
    [Nonempty Sa] [DecidableEq RK] [DecidableEq Key] [DecidableEq S] (C : CKADef Sc Msg Key)
    [CKACoins C Rand] (hS : CKACoins.Sound C) {J : Sc → Sc → Prop} (hJ : CKACorrect C J)
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (hJi : ∀ i ∈ initP.support, J i.2.1 i.2.2)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D₀ : AEADDef W Ct ((PHdr × W) × ACDHdr Msg)) (F : W → S → W)
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored : ℕ)
    (P : SidecarDef PSt PHdr S) (E : SidecarPack PHdr S W) (hE : Function.Injective E.unpack)
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS)
    (A : SMIDAdv (Msg × ℕ) W (ACDHdr Msg × PHdr) Ct (ACDIDLeak Sc RK Sa Msg W × PSt)) (q : ℕ)
    (hA : ∀ t pub, (A.play t pub).IsQueryBound q) :
    (tripleRatchetDeployed C R G D₀ F dec enc maxSkip maxStored P E).idAdvantage ΔFS ΔPCS A ≤
      (acdIDSM C R G (deployedAEAD D₀ F E) dec enc maxSkip maxStored).intAdvantage ΔFS ΔPCS
          (sidecarRed P E A) +
        (∑ b : Bool, CKA_Corrupt_Advantage C ΔFS ΔPCS (smcCKARed R G (deployedAEAD D₀ F E) b
            ((tripleRatchetDeployedRed C R G D₀ F dec enc maxSkip maxStored P E ΔFS ΔPCS
              A).toSMAD dec)) +
          ∑ b : Bool, PRFPRNG_Advantage R (smcRootRed C R G (deployedAEAD D₀ F E) ΔFS ΔPCS b
            initP ((tripleRatchetDeployedRed C R G D₀ F dec enc maxSkip maxStored P E ΔFS ΔPCS
              A).toSMAD dec)) +
          (∑ i ∈ Finset.range q, PRG_Advantage G (fsCorrPRGRed G (deployedAEAD D₀ F E) false i
              (smcFSRed C R G (deployedAEAD D₀ F E) ΔFS ΔPCS initP
                ((tripleRatchetDeployedRed C R G D₀ F dec enc maxSkip maxStored P E ΔFS ΔPCS
                  A).toSMAD dec))) +
            ∑ i ∈ Finset.range q, PRG_Advantage G (fsCorrPRGRed G (deployedAEAD D₀ F E) true i
              (smcFSRed C R G (deployedAEAD D₀ F E) ΔFS ΔPCS initP
                ((tripleRatchetDeployedRed C R G D₀ F dec enc maxSkip maxStored P E ΔFS ΔPCS
                  A).toSMAD dec))) +
            (DualPRF_Left_Advantage F (saltedPRFRed D₀ (aeadAdvMapAD (deployedAD E)
                (fsCorrAEADRed G (deployedAEAD D₀ F E)
                  (smcFSRed C R G (deployedAEAD D₀ F E) ΔFS ΔPCS initP
                    ((tripleRatchetDeployedRed C R G D₀ F dec enc maxSkip maxStored P E ΔFS
                      ΔPCS A).toSMAD dec))))) +
              ∑ j ∈ Finset.range q, AEAD_CCA_Advantage D₀ (saltedAEADRed D₀
                (aeadAdvMapAD (deployedAD E) (fsCorrAEADRed G (deployedAEAD D₀ F E)
                  (smcFSRed C R G (deployedAEAD D₀ F E) ΔFS ΔPCS initP
                    ((tripleRatchetDeployedRed C R G D₀ F dec enc maxSkip maxStored P E ΔFS
                      ΔPCS A).toSMAD dec)))) j)))) +
        prTrue (sidecarBadGame (acdIDSM C R G (deployedAEAD D₀ F E) dec enc maxSkip maxStored)
          P E ΔFS ΔPCS false (fun _ => false) A) Heap.empty +
        prTrue (sidecarBadGame (acdIDSM C R G (deployedAEAD D₀ F E) dec enc maxSkip maxStored)
          P E ΔFS ΔPCS true (fun _ => true) A) Heap.empty := by
  have hB := smcFSRed_isQueryBoundBy C R G (deployedAEAD D₀ F E) ΔFS ΔPCS initP _ q
    (tripleRatchetDeployedRed_toSMAD_play_isQueryBound C R G D₀ F dec enc maxSkip maxStored P E
      ΔFS ΔPCS A q hA)
  have hX := fsCorrAEADRed_isQueryBound G (deployedAEAD D₀ F E) _ q hB
  have hI : (aeadAdvMapAD (deployedAD E) (fsCorrAEADRed G (deployedAEAD D₀ F E)
      (smcFSRed C R G (deployedAEAD D₀ F E) ΔFS ΔPCS initP
        ((tripleRatchetDeployedRed C R G D₀ F dec enc maxSkip maxStored P E ΔFS ΔPCS
          A).toSMAD dec)))).IndexBound querySalt ∅ q := by
    simpa [aeadAdvMapAD] using OracleAdv.indexBound_of_isQueryBound querySalt
      (OracleAdv.isQueryBound_mapQueryAnswer _ _ hX) ∅
  refine (tripleRatchetDeployed_idAdvantage_le_fs C hS hJ initP hinit hJi R G D₀ F dec enc
    maxSkip maxStored P E hFS hPCS A).trans ?_
  gcongr
  refine (fsaead_corrupt_advantage_le G _ q _ hB).trans ?_
  gcongr
  exact deployedAEAD_advantage_le D₀ F E hE _ q hI

end Deployed

end CatCrypt.Crypto.Messaging
