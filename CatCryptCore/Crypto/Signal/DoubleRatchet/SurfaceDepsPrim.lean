/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.FSAEADCorruptSM
public import CatCryptCore.Crypto.Signal.DoubleRatchet.SurfaceDeps

/-!
# The extracted Signal double ratchet with state corruption from PRG and AEAD security

The corruption bound `signalDR_extracted_corrupt_advantage_le` of the extracted double ratchet
has an FS-AEAD term of the libcrux symmetric ratchet at the reduction `smcFSRed`. For an
adversary whose interactions ask at most `q` queries, `fsaead_corrupt_advantage_le` bounds that
term by the PRG advantages of the chain PRG `Signal.FSAEAD.toPRG libcrux_fsaeadConfig` at the
hybrid reductions `fsCorrPRGRed` for the positions `i < q` and the AEAD advantage of
`Signal.FSAEAD.toAEAD libcrux_fsaeadConfig` at `fsCorrAEADRed`.

## Main results

* `signalDR_extracted_corrupt_advantage_le_of_hom_prim` — the bound at an X25519 function `sm`
  under `X25519HomOf sm bp B`
* `signalDR_extracted_corrupt_advantage_le_prim` — the bound for libcrux X25519 under
  `X25519Hom B`

## References

* J. Alwen, S. Coretti, Y. Dodis, *The Double Ratchet: Security Notions, Proofs, and
  Modularization for the Signal Protocol*, EUROCRYPT 2019, §4.3 and §5
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Signal.DoubleRatchet.SurfaceDeps

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open CatCrypt.Examples.SymmRatchet
open CatCrypt.Crypto.Messaging CatCrypt.Crypto.Signal.DoubleRatchet_CKA
open CatCryptCore.Examples.CyclicGroupDDH
open CatCrypt.Crypto.Libcrux.ConcreteInstances
open CatCrypt.Crypto.Libcrux.Extraction.Libcrux_specs
open CatCrypt.Hax.ReprBridge
open CatCrypt.Crypto.ECC CatCrypt.Crypto.Libcrux.Bridge_X25519Group
open ExtractedCorrespondence ExtractedScheme
open scoped ENNReal

variable (B : Curve25519Point) [Fact (addOrderOf B = curve25519SubgroupOrder)]

open CatCrypt.Crypto.KeyAgreement.X25519 in
/-- **The extracted Signal double ratchet with state corruption from DDH, PRF-PRNG, PRG and AEAD
security, at an X25519 function.** Under the hypotheses of
`signalDR_extracted_corrupt_advantage_le_of_hom`, for an adversary `A` whose interactions ask at
most `q` queries, the advantage in the corruption game over `signalDRSMOf B sm` is at most the
DDH and PRF-PRNG terms of that theorem, the PRG advantages of the libcrux chain PRG at
`fsCorrPRGRed` for the positions `i < q` and both challenge bits, and the AEAD advantage of the
libcrux AEAD at `fsCorrAEADRed`, all at the FS-AEAD reduction `smcFSRed` of the encoded and
relabelled adversary. -/
theorem signalDR_extracted_corrupt_advantage_le_of_hom_prim
    {sm : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32}
    {bp : Vector UInt8 32 → Vector UInt8 32} (hH : X25519HomOf sm bp B) {ΔFS ΔPCS : ℕ}
    (hFS : 2 ≤ ΔFS) (hPCS : 2 ≤ ΔPCS)
    (A : SMSchemeAdv (Array Int) (Vector UInt8 32) (Array Int) DrLeak) (q : ℕ)
    (hA : ∀ t T, (A.play t T).IsQueryBound q) :
    (signalDRSMOf B sm).corruptAdvantage ΔFS ΔPCS A ≤
      ∑ b : Bool, (DDH_Advantage (G25519 B) (ckaCorruptDDHRedOf (G := G25519 B) signedE ΔFS ΔPCS
          (smcCKARed (hkdfRoot (libcruxRootKdf encU)) (Signal.FSAEAD.toPRG libcrux_fsaeadConfig)
            (Signal.FSAEAD.toAEAD libcrux_fsaeadConfig) b
            (A.comap (vecToArrayInt ∘ encU) vecToArrayInt (signalDRLibcruxLeak B)).toSM)) +
          4 * Δ25519) +
        ∑ b : Bool, PRFPRNG_Advantage (hkdfRoot (libcruxRootKdf encU))
          (smcRootRed (dhCKAOf (G25519 B) signedE) (hkdfRoot (libcruxRootKdf encU))
            (Signal.FSAEAD.toPRG libcrux_fsaeadConfig) (Signal.FSAEAD.toAEAD libcrux_fsaeadConfig)
            ΔFS ΔPCS b (dhInitPOf (G25519 B) signedE)
            (A.comap (vecToArrayInt ∘ encU) vecToArrayInt (signalDRLibcruxLeak B)).toSM) +
        (∑ i ∈ Finset.range q, PRG_Advantage (Signal.FSAEAD.toPRG libcrux_fsaeadConfig)
            (fsCorrPRGRed (Signal.FSAEAD.toPRG libcrux_fsaeadConfig)
              (Signal.FSAEAD.toAEAD libcrux_fsaeadConfig) false i
              (smcFSRed (dhCKAOf (G25519 B) signedE) (hkdfRoot (libcruxRootKdf encU))
                (Signal.FSAEAD.toPRG libcrux_fsaeadConfig)
                (Signal.FSAEAD.toAEAD libcrux_fsaeadConfig) ΔFS ΔPCS
                (dhInitPOf (G25519 B) signedE)
                (A.comap (vecToArrayInt ∘ encU) vecToArrayInt (signalDRLibcruxLeak B)).toSM)) +
          ∑ i ∈ Finset.range q, PRG_Advantage (Signal.FSAEAD.toPRG libcrux_fsaeadConfig)
            (fsCorrPRGRed (Signal.FSAEAD.toPRG libcrux_fsaeadConfig)
              (Signal.FSAEAD.toAEAD libcrux_fsaeadConfig) true i
              (smcFSRed (dhCKAOf (G25519 B) signedE) (hkdfRoot (libcruxRootKdf encU))
                (Signal.FSAEAD.toPRG libcrux_fsaeadConfig)
                (Signal.FSAEAD.toAEAD libcrux_fsaeadConfig) ΔFS ΔPCS
                (dhInitPOf (G25519 B) signedE)
                (A.comap (vecToArrayInt ∘ encU) vecToArrayInt (signalDRLibcruxLeak B)).toSM)) +
          AEAD_CCA_Advantage (Signal.FSAEAD.toAEAD libcrux_fsaeadConfig)
            (fsCorrAEADRed (Signal.FSAEAD.toPRG libcrux_fsaeadConfig)
              (Signal.FSAEAD.toAEAD libcrux_fsaeadConfig)
              (smcFSRed (dhCKAOf (G25519 B) signedE) (hkdfRoot (libcruxRootKdf encU))
                (Signal.FSAEAD.toPRG libcrux_fsaeadConfig)
                (Signal.FSAEAD.toAEAD libcrux_fsaeadConfig) ΔFS ΔPCS
                (dhInitPOf (G25519 B) signedE)
                (A.comap (vecToArrayInt ∘ encU) vecToArrayInt
                  (signalDRLibcruxLeak B)).toSM))) := by
  refine (signalDR_extracted_corrupt_advantage_le_of_hom B hH hFS hPCS A).trans ?_
  gcongr
  exact fsaead_corrupt_advantage_le _ _ q _ (smcFSRed_isQueryBoundBy _ _ _ _ _ _ _ _ q
    (SMSchemeAdv.toSM_play_isQueryBound (SMSchemeAdv.comap_play_isQueryBound hA)))

/-- **The extracted Signal double ratchet with state corruption from DDH, PRF-PRNG, PRG and AEAD
security.** Under `X25519Hom B`, with `2 ≤ ΔFS`, `2 ≤ ΔPCS`, for an adversary `A` whose
interactions ask at most `q` queries, the advantage in the corruption game over
`signalDRLibcruxSM B` is at most the bound of `signalDR_extracted_corrupt_advantage_le_of_hom_prim`.
The theorem is `signalDR_extracted_corrupt_advantage_le_of_hom_prim` at `X25519Hom B`. -/
theorem signalDR_extracted_corrupt_advantage_le_prim (hH : X25519Hom B) {ΔFS ΔPCS : ℕ}
    (hFS : 2 ≤ ΔFS) (hPCS : 2 ≤ ΔPCS)
    (A : SMSchemeAdv (Array Int) (Vector UInt8 32) (Array Int) DrLeak) (q : ℕ)
    (hA : ∀ t T, (A.play t T).IsQueryBound q) :
    (signalDRLibcruxSM B).corruptAdvantage ΔFS ΔPCS A ≤
      ∑ b : Bool, (DDH_Advantage (G25519 B) (ckaCorruptDDHRedOf (G := G25519 B) signedE ΔFS ΔPCS
          (smcCKARed (hkdfRoot (libcruxRootKdf encU)) (Signal.FSAEAD.toPRG libcrux_fsaeadConfig)
            (Signal.FSAEAD.toAEAD libcrux_fsaeadConfig) b
            (A.comap (vecToArrayInt ∘ encU) vecToArrayInt (signalDRLibcruxLeak B)).toSM)) +
          4 * Δ25519) +
        ∑ b : Bool, PRFPRNG_Advantage (hkdfRoot (libcruxRootKdf encU))
          (smcRootRed (dhCKAOf (G25519 B) signedE) (hkdfRoot (libcruxRootKdf encU))
            (Signal.FSAEAD.toPRG libcrux_fsaeadConfig) (Signal.FSAEAD.toAEAD libcrux_fsaeadConfig)
            ΔFS ΔPCS b (dhInitPOf (G25519 B) signedE)
            (A.comap (vecToArrayInt ∘ encU) vecToArrayInt (signalDRLibcruxLeak B)).toSM) +
        (∑ i ∈ Finset.range q, PRG_Advantage (Signal.FSAEAD.toPRG libcrux_fsaeadConfig)
            (fsCorrPRGRed (Signal.FSAEAD.toPRG libcrux_fsaeadConfig)
              (Signal.FSAEAD.toAEAD libcrux_fsaeadConfig) false i
              (smcFSRed (dhCKAOf (G25519 B) signedE) (hkdfRoot (libcruxRootKdf encU))
                (Signal.FSAEAD.toPRG libcrux_fsaeadConfig)
                (Signal.FSAEAD.toAEAD libcrux_fsaeadConfig) ΔFS ΔPCS
                (dhInitPOf (G25519 B) signedE)
                (A.comap (vecToArrayInt ∘ encU) vecToArrayInt (signalDRLibcruxLeak B)).toSM)) +
          ∑ i ∈ Finset.range q, PRG_Advantage (Signal.FSAEAD.toPRG libcrux_fsaeadConfig)
            (fsCorrPRGRed (Signal.FSAEAD.toPRG libcrux_fsaeadConfig)
              (Signal.FSAEAD.toAEAD libcrux_fsaeadConfig) true i
              (smcFSRed (dhCKAOf (G25519 B) signedE) (hkdfRoot (libcruxRootKdf encU))
                (Signal.FSAEAD.toPRG libcrux_fsaeadConfig)
                (Signal.FSAEAD.toAEAD libcrux_fsaeadConfig) ΔFS ΔPCS
                (dhInitPOf (G25519 B) signedE)
                (A.comap (vecToArrayInt ∘ encU) vecToArrayInt (signalDRLibcruxLeak B)).toSM)) +
          AEAD_CCA_Advantage (Signal.FSAEAD.toAEAD libcrux_fsaeadConfig)
            (fsCorrAEADRed (Signal.FSAEAD.toPRG libcrux_fsaeadConfig)
              (Signal.FSAEAD.toAEAD libcrux_fsaeadConfig)
              (smcFSRed (dhCKAOf (G25519 B) signedE) (hkdfRoot (libcruxRootKdf encU))
                (Signal.FSAEAD.toPRG libcrux_fsaeadConfig)
                (Signal.FSAEAD.toAEAD libcrux_fsaeadConfig) ΔFS ΔPCS
                (dhInitPOf (G25519 B) signedE)
                (A.comap (vecToArrayInt ∘ encU) vecToArrayInt (signalDRLibcruxLeak B)).toSM))) :=
  signalDR_extracted_corrupt_advantage_le_of_hom_prim B hH hFS hPCS A q hA

end CatCrypt.Crypto.Signal.DoubleRatchet.SurfaceDeps
