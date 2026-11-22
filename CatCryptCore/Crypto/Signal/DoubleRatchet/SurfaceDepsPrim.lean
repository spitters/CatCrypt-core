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

The corruption bound of `drExtractedSM`, the store-free abstraction of the extracted double
ratchet whose corruptions return the key material `drExpose`, over the ACD construction with
headers consists of DDH terms, PRF-PRNG terms of the HKDF root step `signalDRRoot B`, the PRG
advantages of the chain PRG `signalDRPRG` at the hybrid reductions `fsCorrPRGRed` for the
positions `i < q` and the AEAD advantage of the libcrux AEAD `signalDRAEAD B` at
`fsCorrAEADRed`, all at the reductions of the header wrapper adversary `toHdr (drHdrAD id)` of
the encoded and relabelled adversary. The theorems of this file state that bound at an X25519
function and at the libcrux X25519.

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
/-- **The store-free abstraction of the extracted Signal double ratchet with corruption of its key
material, from DDH, PRF-PRNG, PRG and AEAD security, at an X25519 function.** Under
`X25519HomOf sm bp B`, with `2 ≤ ΔFS` and `2 ≤ ΔPCS`,
for an adversary `A` whose interactions ask at most `q` queries, the advantage in the corruption
game over `signalDRSMOf B sm` is at most the DDH advantages in `G25519 B` of
`ckaCorruptDDHRedOf signedE ΔFS ΔPCS` plus `4 Δ25519`, the PRF-PRNG advantages of
`signalDRRoot B`, the PRG advantages of the chain PRG `signalDRPRG` at `fsCorrPRGRed` for the
positions `i < q` and both challenge bits, and the AEAD advantage of `signalDRAEAD B` at
`fsCorrAEADRed`, all at the reductions of the header wrapper adversary `toHdr (drHdrAD id)` of the
encoded and relabelled adversary. The theorem is
`signalDR_extracted_corrupt_advantage_le_of_hom`. -/
theorem signalDR_extracted_corrupt_advantage_le_of_hom_prim
    {sm : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32}
    {bp : Vector UInt8 32 → Vector UInt8 32} (hH : X25519HomOf sm bp B) {ΔFS ΔPCS : ℕ}
    (hFS : 2 ≤ ΔFS) (hPCS : 2 ≤ ΔPCS)
    (A : SMSchemeAdv (Array Int) (Vector UInt8 32) (Array Int) DrLeak) (q : ℕ)
    (hA : ∀ t T, (A.play t T).IsQueryBound q) :
    (signalDRSMOf B sm).corruptAdvantage ΔFS ΔPCS A ≤
      ∑ b : Bool, (DDH_Advantage (G25519 B) (ckaCorruptDDHRedOf (G := G25519 B) signedE ΔFS ΔPCS
          (smcCKARed (signalDRRoot B) (signalDRPRG) (signalDRAEAD B) b
            ((A.comap (vecToArrayInt ∘ encU) vecToArrayInt (signalDRLibcruxLeak B)).toHdr
              (drHdrAD id)))) + 4 * Δ25519) +
        ∑ b : Bool, PRFPRNG_Advantage (signalDRRoot B)
          (smcRootRed (dhCKAOf (G25519 B) signedE) (signalDRRoot B) (signalDRPRG)
            (signalDRAEAD B) ΔFS ΔPCS b (dhInitPOf (G25519 B) signedE)
            ((A.comap (vecToArrayInt ∘ encU) vecToArrayInt (signalDRLibcruxLeak B)).toHdr
              (drHdrAD id))) +
        (∑ i ∈ Finset.range q, PRG_Advantage (signalDRPRG) (fsCorrPRGRed (signalDRPRG)
            (signalDRAEAD B) false i (smcFSRed (dhCKAOf (G25519 B) signedE) (signalDRRoot B)
              (signalDRPRG) (signalDRAEAD B) ΔFS ΔPCS (dhInitPOf (G25519 B) signedE)
              ((A.comap (vecToArrayInt ∘ encU) vecToArrayInt (signalDRLibcruxLeak B)).toHdr
                (drHdrAD id)))) +
          ∑ i ∈ Finset.range q, PRG_Advantage (signalDRPRG) (fsCorrPRGRed (signalDRPRG)
            (signalDRAEAD B) true i (smcFSRed (dhCKAOf (G25519 B) signedE) (signalDRRoot B)
              (signalDRPRG) (signalDRAEAD B) ΔFS ΔPCS (dhInitPOf (G25519 B) signedE)
              ((A.comap (vecToArrayInt ∘ encU) vecToArrayInt (signalDRLibcruxLeak B)).toHdr
                (drHdrAD id)))) +
          AEAD_CCA_Advantage (signalDRAEAD B)
            (fsCorrAEADRed (signalDRPRG) (signalDRAEAD B)
              (smcFSRed (dhCKAOf (G25519 B) signedE) (signalDRRoot B) (signalDRPRG)
                (signalDRAEAD B) ΔFS ΔPCS (dhInitPOf (G25519 B) signedE)
                ((A.comap (vecToArrayInt ∘ encU) vecToArrayInt (signalDRLibcruxLeak B)).toHdr
                  (drHdrAD id))))) :=
  signalDR_extracted_corrupt_advantage_le_of_hom B hH hFS hPCS A q hA

/-- **The store-free abstraction of the extracted Signal double ratchet with corruption of its key
material, from DDH, PRF-PRNG, PRG and AEAD security.** Under `X25519Hom B`, with `2 ≤ ΔFS`,
`2 ≤ ΔPCS`, for an adversary `A` whose
interactions ask at most `q` queries, the advantage in the corruption game over
`signalDRLibcruxSM B` is at most the bound of `signalDR_extracted_corrupt_advantage_le_of_hom_prim`.
The theorem is `signalDR_extracted_corrupt_advantage_le_of_hom_prim` at `X25519Hom B`. -/
theorem signalDR_extracted_corrupt_advantage_le_prim (hH : X25519Hom B) {ΔFS ΔPCS : ℕ}
    (hFS : 2 ≤ ΔFS) (hPCS : 2 ≤ ΔPCS)
    (A : SMSchemeAdv (Array Int) (Vector UInt8 32) (Array Int) DrLeak) (q : ℕ)
    (hA : ∀ t T, (A.play t T).IsQueryBound q) :
    (signalDRLibcruxSM B).corruptAdvantage ΔFS ΔPCS A ≤
      ∑ b : Bool, (DDH_Advantage (G25519 B) (ckaCorruptDDHRedOf (G := G25519 B) signedE ΔFS ΔPCS
          (smcCKARed (signalDRRoot B) (signalDRPRG) (signalDRAEAD B) b
            ((A.comap (vecToArrayInt ∘ encU) vecToArrayInt (signalDRLibcruxLeak B)).toHdr
              (drHdrAD id)))) + 4 * Δ25519) +
        ∑ b : Bool, PRFPRNG_Advantage (signalDRRoot B)
          (smcRootRed (dhCKAOf (G25519 B) signedE) (signalDRRoot B) (signalDRPRG)
            (signalDRAEAD B) ΔFS ΔPCS b (dhInitPOf (G25519 B) signedE)
            ((A.comap (vecToArrayInt ∘ encU) vecToArrayInt (signalDRLibcruxLeak B)).toHdr
              (drHdrAD id))) +
        (∑ i ∈ Finset.range q, PRG_Advantage (signalDRPRG) (fsCorrPRGRed (signalDRPRG)
            (signalDRAEAD B) false i (smcFSRed (dhCKAOf (G25519 B) signedE) (signalDRRoot B)
              (signalDRPRG) (signalDRAEAD B) ΔFS ΔPCS (dhInitPOf (G25519 B) signedE)
              ((A.comap (vecToArrayInt ∘ encU) vecToArrayInt (signalDRLibcruxLeak B)).toHdr
                (drHdrAD id)))) +
          ∑ i ∈ Finset.range q, PRG_Advantage (signalDRPRG) (fsCorrPRGRed (signalDRPRG)
            (signalDRAEAD B) true i (smcFSRed (dhCKAOf (G25519 B) signedE) (signalDRRoot B)
              (signalDRPRG) (signalDRAEAD B) ΔFS ΔPCS (dhInitPOf (G25519 B) signedE)
              ((A.comap (vecToArrayInt ∘ encU) vecToArrayInt (signalDRLibcruxLeak B)).toHdr
                (drHdrAD id)))) +
          AEAD_CCA_Advantage (signalDRAEAD B)
            (fsCorrAEADRed (signalDRPRG) (signalDRAEAD B)
              (smcFSRed (dhCKAOf (G25519 B) signedE) (signalDRRoot B) (signalDRPRG)
                (signalDRAEAD B) ΔFS ΔPCS (dhInitPOf (G25519 B) signedE)
                ((A.comap (vecToArrayInt ∘ encU) vecToArrayInt (signalDRLibcruxLeak B)).toHdr
                  (drHdrAD id))))) :=
  signalDR_extracted_corrupt_advantage_le_of_hom_prim B hH hFS hPCS A q hA

end CatCrypt.Crypto.Signal.DoubleRatchet.SurfaceDeps
