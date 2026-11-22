/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signal.DoubleRatchet.ExtractedScheme
public import CatCryptCore.Crypto.Messaging.SMMultiChallenge

/-!
# The extracted double ratchet in the multi-challenge corruption game

The multi-challenge corruption game `smMultiGame` of
`CatCryptCore.Crypto.Messaging.SMMultiChallenge` is stated over the record `SMScheme`, and its
bound transfers along a simulation of schemes (`SMScheme.Sim.multiAdvantage_le`). The extracted
double ratchet `drExtractedSM` simulates the ACD construction with headers
`acdHdrSM (dhCKAOf G decE) R F D (drHdrAD adOf)` under `DrHom` (`drExtracted_sim`). Composing
the two with the bound `acdHdrSM_corruptAdvantage_le_prim` gives the bound of the extracted
ratchet in the multi-challenge game with at most `n` challenges: the sum over the `n` hybrids of
the CKA corruption, PRF-PRNG, PRG and AEAD terms at the reductions of `SMCorrupt` and
`FSAEADCorruptSM`, applied to the wrapper adversary of the hybrid reduction `A.hyb` with the
answers encoded and relabelled. The hybrid reduction asks at most one query for each query of
`A` (`SMSchemeAdv.hyb_play_isQueryBound`), so it keeps the query bound `q` of `A`.

`drExtractedSM` is the store-free abstraction of the ratchet (`ExtractedScheme`): the corruptions
of the game return the key material `drExpose`.

The theorem allows `ΔPCS = 1`. Its CKA term is bounded by DDH for `2 ≤ ΔPCS`
(`dhCKAOf_corrupt_advantage_le`); at `ΔPCS = 1` a corruption may return the exponent that
determines the challenge key.

## Main results

* `drExtracted_multiAdvantage_le`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.DoubleRatchet.ExtractedScheme

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Messaging
open CatCrypt.Crypto.Assumptions CatCryptCore.Examples.CyclicGroupDDH
open CatCrypt.Crypto.Signal.DoubleRatchet.ExtractedCorrespondence
open Doubleratchet
open scoped ENNReal

variable (Dp : Type) [Inhabited Dp] [DoubleRatchetDeps Dp]
  {RK Sa W Ct Sk A : Type} [SampleableType W] {G : Type} [CG : CyclicGroup G]
  [Fintype RK] [Nonempty RK] [Fintype Sk] [Nonempty Sk] [SampleableType Ct]
  [Fintype Sa] [Nonempty Sa] [DecidableEq RK] [Fintype G] [Nonempty G] [DecidableEq G]
  [DecidableEq A]
  {R : PRGDef (RK × G) (RK × Sa)} {F : PRGDef Sa (W × Sa)}
  {D : AEADDef W Ct (A × ((G × ℕ) × ℕ))} {ptLen : Int} {encR : RK → Array Int}
  {encG : G → Array Int} {encSk : Sk → Array Int} {decE : Sk → CG.Exp} {encS : Sa → Array Int}
  {encW : W → Array Int} {encPt : W → Array Int} {encC : Ct → Array Int}
  {encAD : A → Array Int} {adOf : W → A}

/-- **The store-free abstraction `drExtractedSM` with many challenges**, for corruptions that
return the key material `drExpose`. Under `DrHom`, with `2 ≤ ΔFS` and
`1 ≤ ΔPCS`, for an adversary `A` whose interactions ask at most `q` queries, the advantage in the
multi-challenge corruption game over `drExtractedSM` with at most `n` challenges is at most the
sum over the hybrids `i < n` of the terms of `drExtracted_corruptAdvantage_le` at the hybrid
reduction `A.hyb _ n i`: the CKA corruption advantages of `smcCKARed`, the PRF-PRNG advantages
of the root KDF `R` at `smcRootRed`, the PRG advantages of `F` at `fsCorrPRGRed` and the AEAD
advantage of `D` at `fsCorrAEADRed`, for the CKA `dhCKAOf G decE` and the wrapper adversary
`toHdr (drHdrAD adOf)` of the hybrid reduction with the answers encoded and relabelled. -/
theorem drExtracted_multiAdvantage_le
    (h : DrHom Dp G R F D ptLen encR encG encSk decE encS encW encPt encC encAD (drEncH encG))
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS) (n : ℕ)
    (A : SMSchemeAdv (Array Int) W (Array Int) DrLeak) (q : ℕ)
    (hA : ∀ t T, (A.play t T).IsQueryBound q) :
    (drExtractedSM Dp RK ptLen encR encG encSk decE encPt encC encAD adOf).multiAdvantage
        ΔFS ΔPCS n A ≤
      ∑ i ∈ Finset.range n,
        (∑ b : Bool, CKA_Corrupt_Advantage (dhCKAOf G decE) ΔFS ΔPCS (smcCKARed R F D b
            (((A.hyb (drExtractedSM Dp RK ptLen encR encG encSk decE encPt encC encAD adOf)
              n i).comap encG encC (drEncLeak encR encG encSk decE encS)).toHdr
                (drHdrAD adOf))) +
          ∑ b : Bool, PRFPRNG_Advantage R (smcRootRed (dhCKAOf G decE) R F D ΔFS ΔPCS b
            (dhInitPOf G decE)
            (((A.hyb (drExtractedSM Dp RK ptLen encR encG encSk decE encPt encC encAD adOf)
              n i).comap encG encC (drEncLeak encR encG encSk decE encS)).toHdr
                (drHdrAD adOf))) +
          (∑ j ∈ Finset.range q, PRG_Advantage F (fsCorrPRGRed F D false j
              (smcFSRed (dhCKAOf G decE) R F D ΔFS ΔPCS (dhInitPOf G decE)
                (((A.hyb (drExtractedSM Dp RK ptLen encR encG encSk decE encPt encC encAD
                  adOf) n i).comap encG encC (drEncLeak encR encG encSk decE encS)).toHdr
                    (drHdrAD adOf)))) +
            ∑ j ∈ Finset.range q, PRG_Advantage F (fsCorrPRGRed F D true j
              (smcFSRed (dhCKAOf G decE) R F D ΔFS ΔPCS (dhInitPOf G decE)
                (((A.hyb (drExtractedSM Dp RK ptLen encR encG encSk decE encPt encC encAD
                  adOf) n i).comap encG encC (drEncLeak encR encG encSk decE encS)).toHdr
                    (drHdrAD adOf)))) +
            AEAD_CCA_Advantage D (fsCorrAEADRed F D
              (smcFSRed (dhCKAOf G decE) R F D ΔFS ΔPCS (dhInitPOf G decE)
                (((A.hyb (drExtractedSM Dp RK ptLen encR encG encSk decE encPt encC encAD
                  adOf) n i).comap encG encC (drEncLeak encR encG encSk decE encS)).toHdr
                    (drHdrAD adOf)))))) := by
  refine ((drExtracted_sim Dp h).multiAdvantage_le ΔFS ΔPCS n A).trans
    (Finset.sum_le_sum fun i _ => ?_)
  exact acdHdrSM_corruptAdvantage_le_prim (dhCKAOf G decE) (dhCKAOfCoins_sound G decE)
    (dhCKAOf_correct G decE) (dhInitPOf G decE) (dhCKAOf_init_eq G decE) (dhInitPOf_rel G decE)
    R F D (drHdrAD adOf) hFS hPCS _ q
    (SMSchemeAdv.comap_play_isQueryBound (SMSchemeAdv.hyb_play_isQueryBound _ n i hA))

end CatCrypt.Crypto.Signal.DoubleRatchet.ExtractedScheme
