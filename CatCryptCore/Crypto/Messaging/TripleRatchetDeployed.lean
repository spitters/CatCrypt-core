/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SMIDSidecar
public import CatCryptCore.Crypto.Messaging.SMIDACD
public import CatCryptCore.Crypto.Messaging.SaltedAEAD

/-!
# The deployed Triple Ratchet with per-message key mixing

The deployed Signal Triple Ratchet runs the post-quantum ratchet SPQR beside the Double Ratchet
and encrypts each message under `mk = KDF_HYBRID(ec_mk, pq_mk)`: the message key `ec_mk` of the
Double Ratchet mixed with the message key `pq_mk` of SPQR. This is the per-message step
`K_aead ← KDF3(K^C_aead, K^Q_aead)` of the Triple Ratchet of Dodis, Jost, Katsumata, Prest and
Schmidt (ePrint 2025/078).

`tripleRatchetDeployed` is the sidecar scheme `smidSidecar M P E` (`SMIDSidecar.lean`) over the
ACD construction with headers `M = acdIDSM C R G D dec enc maxSkip maxStored` (`SMIDACD.lean`),
for an arbitrary sidecar `P : SidecarDef` in place of SPQR. The AEAD of `M` is
`deployedAEAD D₀ F E = aeadComapAD (saltedAEAD D₀ F) (deployedAD E)`: the associated data of a
message is a word that `E.unpack` decodes into the sidecar header, the salt and the associated
data of the message, and the AEAD encrypts under `F mk s` with the salt `s` read from it
(`SaltedAEAD.lean`). With `F` the mixing of `KDF_HYBRID` and `s = pq_mk`, a message is
encrypted under `KDF_HYBRID(ec_mk, pq_mk)`. The receiver's sidecar advances only after the
message authenticates (commit after authentication), which is the order modelled by
`smidSidecar` and is not confirmed against libsignal.

## Main definitions

* `deployedAD`, `deployedAEAD`: the message AEAD of the deployed Triple Ratchet.
* `tripleRatchetDeployed`: the deployed Triple Ratchet over a sidecar `P`.
* `tripleRatchetDeployedRed`: the reduction to the corruption game of the ACD construction.

## Main results

* `deployedAEAD_advantage_le`: the advantage against the message AEAD is at most the left
  dual-PRF advantage of `F` and the per-salt AEAD advantages of `D₀`, for an injective
  decoding `E.unpack`.
* `tripleRatchetDeployed_idAdvantage_le`: the immediate-decryption advantage against the
  deployed Triple Ratchet is at most the integrity advantage of the ACD construction with
  headers, the corruption advantage of the ACD construction at `tripleRatchetDeployedRed`, and
  the two wrong-salt events of the sidecar.
* `tripleRatchetDeployed_idAdvantage_le_fs`: the same bound with the corruption term replaced by
  the CKA, PRF-PRNG and FS-AEAD corruption advantages of `acdSMAD_corruptAdvantage_le` at the
  message AEAD with associated data `W × ACDHdr Msg`.

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

/-! ## The message AEAD -/

section AEAD

variable {PHdr S W Ct Msg : Type}

/-- The associated data of the message AEAD read as salted associated data: the salt decoded
from the word, and the sidecar header, the associated data of the message and the header of the
ACD construction. -/
def deployedAD (E : SidecarPack PHdr S W) (x : W × ACDHdr Msg) :
    S × ((PHdr × W) × ACDHdr Msg) :=
  ((E.unpack x.1).2.1, (((E.unpack x.1).1, (E.unpack x.1).2.2), x.2))

/-- The relabelling `deployedAD E` is injective for an injective decoding. -/
theorem deployedAD_injective (E : SidecarPack PHdr S W) (hE : Function.Injective E.unpack) :
    Function.Injective (deployedAD (Msg := Msg) E) := by
  rintro ⟨w, h⟩ ⟨w', h'⟩ heq
  simp only [deployedAD, Prod.mk.injEq] at heq
  obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := heq
  have hu : E.unpack w = E.unpack w' := Prod.ext h2 (Prod.ext h1 h3)
  rw [hE hu, h4]

variable [SampleableType W]

/-- **The message AEAD of the deployed Triple Ratchet**: `D₀` under the key `F mk s`, with the
salt `s` decoded from the associated data by `E`. -/
def deployedAEAD (D₀ : AEADDef W Ct ((PHdr × W) × ACDHdr Msg)) (F : W → S → W)
    (E : SidecarPack PHdr S W) : AEADDef W Ct (W × ACDHdr Msg) :=
  aeadComapAD (saltedAEAD D₀ F) (deployedAD E)

variable [SampleableType Ct] [DecidableEq S] [DecidableEq PHdr] [DecidableEq W]
  [DecidableEq Msg]

/-- **The message AEAD of the deployed Triple Ratchet.** For an injective decoding `E.unpack`
and every adversary `A` whose relabelled adversary asks at no more than `u` distinct salts, the
advantage against `deployedAEAD D₀ F E` is at most the left dual-PRF advantage of `F` against
`saltedPRFRed` and the sum over `j < u` of the AEAD advantages of `D₀` against
`saltedAEADRed`, both at the relabelled adversary `aeadAdvMapAD (deployedAD E) A`. -/
theorem deployedAEAD_advantage_le (D₀ : AEADDef W Ct ((PHdr × W) × ACDHdr Msg))
    (F : W → S → W) (E : SidecarPack PHdr S W) (hE : Function.Injective E.unpack)
    (A : AEAD_CCA_Adversary W Ct (W × ACDHdr Msg)) (u : ℕ)
    (hA : (aeadAdvMapAD (deployedAD E) A).IndexBound querySalt ∅ u) :
    AEAD_CCA_Advantage (deployedAEAD D₀ F E) A ≤
      DualPRF_Left_Advantage F (saltedPRFRed D₀ (aeadAdvMapAD (deployedAD E) A)) +
        ∑ j ∈ Finset.range u,
          AEAD_CCA_Advantage D₀ (saltedAEADRed D₀ (aeadAdvMapAD (deployedAD E) A) j) := by
  rw [deployedAEAD, AEAD_CCA_Advantage_comapAD _ _ (deployedAD_injective E hE)]
  exact saltedAEAD_advantage_le D₀ F _ u hA

end AEAD

/-! ## The deployed Triple Ratchet -/

section Deployed

variable {Sc Msg Key Rand RK Sa W Ct PSt PHdr S : Type} [Fintype Rand] [Nonempty Rand]
  [SampleableType W] [SampleableType Ct] [Fintype RK] [Nonempty RK] [Inhabited Msg]
  [DecidableEq Msg]

/-- **The deployed Triple Ratchet** (DJKPS, ePrint 2025/078, with per-message mixing
`mk = KDF_HYBRID(ec_mk, pq_mk)`): the ACD construction with headers over the CKA `C`, with the
message AEAD `deployedAEAD D₀ F E`, run with the sidecar `P` mixed into every message key. The
receiver's sidecar commits only after a successful decryption. -/
noncomputable def tripleRatchetDeployed (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D₀ : AEADDef W Ct ((PHdr × W) × ACDHdr Msg)) (F : W → S → W)
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored : ℕ)
    (P : SidecarDef PSt PHdr S) (E : SidecarPack PHdr S W) :
    SMIDScheme (ACDIDSt Sc RK Sa Msg W × PSt) (Msg × ℕ) Rand W Ct
      (ACDIDLeak Sc RK Sa Msg W × PSt) (ACDHdr Msg × PHdr) (W × S) :=
  smidSidecar (acdIDSM C R G (deployedAEAD D₀ F E) dec enc maxSkip maxStored) P E

variable [DecidableEq W] [DecidableEq Ct] [DecidableEq PHdr]

/-- **Reduction** from the deployed Triple Ratchet to the corruption game of the ACD
construction: the sidecar reduction `sidecarRed P E A` followed by the reduction `smIDRed` of
the ACD construction with headers. -/
noncomputable def tripleRatchetDeployedRed (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D₀ : AEADDef W Ct ((PHdr × W) × ACDHdr Msg)) (F : W → S → W)
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored : ℕ)
    (P : SidecarDef PSt PHdr S) (E : SidecarPack PHdr S W) (ΔFS ΔPCS : ℕ)
    (A : SMIDAdv (Msg × ℕ) W (ACDHdr Msg × PHdr) Ct (ACDIDLeak Sc RK Sa Msg W × PSt)) :=
  smIDRed (acdIDSM C R G (deployedAEAD D₀ F E) dec enc maxSkip maxStored)
    (acdIDView G maxSkip maxStored enc) ΔFS ΔPCS (sidecarRed P E A)

/-- **The deployed Triple Ratchet against every sidecar.** For every sidecar `P` and every
adversary `A`, the immediate-decryption advantage against `tripleRatchetDeployed` is at most the
integrity advantage of the ACD construction with headers against `sidecarRed P E A`, the
corruption advantage of the ACD construction against `tripleRatchetDeployedRed`, and the
probabilities of a wrong salt in the real game and in the game with a uniform challenge and
decryption from the log. -/
theorem tripleRatchetDeployed_idAdvantage_le (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D₀ : AEADDef W Ct ((PHdr × W) × ACDHdr Msg)) (F : W → S → W)
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored : ℕ)
    (P : SidecarDef PSt PHdr S) (E : SidecarPack PHdr S W) (ΔFS ΔPCS : ℕ)
    (A : SMIDAdv (Msg × ℕ) W (ACDHdr Msg × PHdr) Ct (ACDIDLeak Sc RK Sa Msg W × PSt)) :
    (tripleRatchetDeployed C R G D₀ F dec enc maxSkip maxStored P E).idAdvantage ΔFS ΔPCS A ≤
      (acdIDSM C R G (deployedAEAD D₀ F E) dec enc maxSkip maxStored).intAdvantage ΔFS ΔPCS
          (sidecarRed P E A) +
        (acdIDBase C R G (deployedAEAD D₀ F E) dec).corruptAdvantage ΔFS ΔPCS
          (tripleRatchetDeployedRed C R G D₀ F dec enc maxSkip maxStored P E ΔFS ΔPCS A) +
        prTrue (sidecarBadGame (acdIDSM C R G (deployedAEAD D₀ F E) dec enc maxSkip maxStored)
          P E ΔFS ΔPCS false (fun _ => false) A) Heap.empty +
        prTrue (sidecarBadGame (acdIDSM C R G (deployedAEAD D₀ F E) dec enc maxSkip maxStored)
          P E ΔFS ΔPCS true (fun _ => true) A) Heap.empty := by
  refine (SMIDScheme.idAdvantage_sidecar_le _ P E ΔFS ΔPCS A).trans ?_
  gcongr
  exact acdIDSM_idAdvantage_le C R G _ dec enc maxSkip maxStored ΔFS ΔPCS _

/-- **The deployed Triple Ratchet from CKA, PRF-PRNG and FS-AEAD security.** For a CKA correct
along `J` with a sound explicit-randomness sending algorithm, an initialisation that is the lift
of `initP` with initial states related by `J`, and `2 ≤ ΔFS`, `1 ≤ ΔPCS`, the corruption term
of `tripleRatchetDeployed_idAdvantage_le` is bounded by `acdSMAD_corruptAdvantage_le` at the
decoding `dec` of the associated data: the CKA corruption advantages, the PRF-PRNG advantages
of `R`, and the FS-AEAD advantage with corruption of `G` and the message AEAD
`deployedAEAD D₀ F E`, whose associated data are `W × ACDHdr Msg`, each at an explicit
reduction of `tripleRatchetDeployedRed … A` relabelled by `toSMAD dec`. -/
theorem tripleRatchetDeployed_idAdvantage_le_fs [Fintype Key] [Nonempty Key] [Fintype Sa]
    [Nonempty Sa] [DecidableEq RK] [DecidableEq Key] (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (hS : CKACoins.Sound C) {J : Sc → Sc → Prop} (hJ : CKACorrect C J)
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (hJi : ∀ i ∈ initP.support, J i.2.1 i.2.2)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D₀ : AEADDef W Ct ((PHdr × W) × ACDHdr Msg)) (F : W → S → W)
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored : ℕ)
    (P : SidecarDef PSt PHdr S) (E : SidecarPack PHdr S W) {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS)
    (hPCS : 1 ≤ ΔPCS)
    (A : SMIDAdv (Msg × ℕ) W (ACDHdr Msg × PHdr) Ct (ACDIDLeak Sc RK Sa Msg W × PSt)) :
    (tripleRatchetDeployed C R G D₀ F dec enc maxSkip maxStored P E).idAdvantage ΔFS ΔPCS A ≤
      (acdIDSM C R G (deployedAEAD D₀ F E) dec enc maxSkip maxStored).intAdvantage ΔFS ΔPCS
          (sidecarRed P E A) +
        (∑ b : Bool, CKA_Corrupt_Advantage C ΔFS ΔPCS (smcCKARed R G (deployedAEAD D₀ F E) b
            ((tripleRatchetDeployedRed C R G D₀ F dec enc maxSkip maxStored P E ΔFS ΔPCS
              A).toSMAD dec)) +
          ∑ b : Bool, PRFPRNG_Advantage R (smcRootRed C R G (deployedAEAD D₀ F E) ΔFS ΔPCS b
            initP ((tripleRatchetDeployedRed C R G D₀ F dec enc maxSkip maxStored P E ΔFS ΔPCS
              A).toSMAD dec)) +
          FSAEAD_Corrupt_Advantage G (deployedAEAD D₀ F E)
            (smcFSRed C R G (deployedAEAD D₀ F E) ΔFS ΔPCS initP
              ((tripleRatchetDeployedRed C R G D₀ F dec enc maxSkip maxStored P E ΔFS ΔPCS
                A).toSMAD dec))) +
        prTrue (sidecarBadGame (acdIDSM C R G (deployedAEAD D₀ F E) dec enc maxSkip maxStored)
          P E ΔFS ΔPCS false (fun _ => false) A) Heap.empty +
        prTrue (sidecarBadGame (acdIDSM C R G (deployedAEAD D₀ F E) dec enc maxSkip maxStored)
          P E ΔFS ΔPCS true (fun _ => true) A) Heap.empty := by
  refine (tripleRatchetDeployed_idAdvantage_le C R G D₀ F dec enc maxSkip maxStored P E ΔFS
    ΔPCS A).trans ?_
  gcongr
  exact acdSMAD_corruptAdvantage_le C hS hJ initP hinit hJi R G (deployedAEAD D₀ F E) dec hFS
    hPCS _

end Deployed

end CatCrypt.Crypto.Messaging
