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
double ratchet `drExtractedSM` simulates the ACD construction `acdSM (dhCKAOf G decE) R F D`
under `DrHom` (`drExtracted_sim`). Composing the two with the corruption bound
`acdSM_corruptAdvantage_le` of the ACD construction gives the bound of the extracted ratchet in
the multi-challenge game with at most `n` challenges: the sum over the `n` hybrids of the CKA
corruption, PRF-PRNG and FS-AEAD terms at the reductions of `SMCorrupt`, applied to the hybrid
reduction `A.hyb` with the answers encoded and relabelled.

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

variable [inst : DoubleratchetDeps]

variable {RK Sa W Ct Sk : Type} [SampleableType W] {G : Type} [CG : CyclicGroup G]
  [Fintype RK] [Nonempty RK] [Fintype Sk] [Nonempty Sk] [SampleableType Ct]
  [Fintype Sa] [Nonempty Sa] [DecidableEq RK] [DecidableEq G]
  {R : PRGDef (RK × G) (RK × Sa)} {F : PRGDef Sa (W × Sa)} {D : AEADDef W Ct}
  {ptLen : Int} {encR : RK → Array Int} {encG : G → Array Int} {encSk : Sk → Array Int}
  {decE : Sk → CG.Exp} {encS : Sa → Array Int} {encW : W → Array Int} {encC : Ct → Array Int}

/-- **The extracted double ratchet with many challenges.** Under `DrHom`, with `2 ≤ ΔFS` and
`1 ≤ ΔPCS`, the advantage of every adversary `A` in the multi-challenge corruption game over
`drExtractedSM` with at most `n` challenges is at most the sum over the hybrids `i < n` of the
CKA corruption advantages of `smcCKARed`, the PRF-PRNG advantages of the root KDF `R` at
`smcRootRed` and the FS-AEAD advantage at `smcFSRed`, for the CKA `dhCKAOf G decE` and the
hybrid reduction `A.hyb _ n i` with the answers encoded and relabelled. -/
theorem drExtracted_multiAdvantage_le
    (h : DrHom G R F D ptLen encR encG encSk decE encS encW encC)
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS) (n : ℕ)
    (A : SMSchemeAdv (Array Int) W (Array Int) DrLeak) :
    (drExtractedSM RK ptLen encR encG encSk decE encW encC).multiAdvantage ΔFS ΔPCS n A ≤
      ∑ i ∈ Finset.range n,
        (∑ b : Bool, CKA_Corrupt_Advantage (dhCKAOf G decE) ΔFS ΔPCS
            (smcCKARed R F D b ((A.hyb (drExtractedSM RK ptLen encR encG encSk decE encW encC)
              n i).comap encG encC (drEncLeak encR encG encSk decE encS)).toSM) +
          ∑ b : Bool, PRFPRNG_Advantage R (smcRootRed (dhCKAOf G decE) R F D ΔFS ΔPCS b
            (dhInitPOf G decE) ((A.hyb (drExtractedSM RK ptLen encR encG encSk decE encW encC)
              n i).comap encG encC (drEncLeak encR encG encSk decE encS)).toSM) +
          FSAEAD_Corrupt_Advantage F D (smcFSRed (dhCKAOf G decE) R F D ΔFS ΔPCS
            (dhInitPOf G decE) ((A.hyb (drExtractedSM RK ptLen encR encG encSk decE encW encC)
              n i).comap encG encC (drEncLeak encR encG encSk decE encS)).toSM)) := by
  refine ((drExtracted_sim h).multiAdvantage_le ΔFS ΔPCS n A).trans
    (Finset.sum_le_sum fun i _ => ?_)
  exact acdSM_corruptAdvantage_le (dhCKAOf G decE) (dhCKAOfCoins_sound G decE)
    (dhCKAOf_correct G decE) (dhInitPOf G decE) (dhCKAOf_init_eq G decE) (dhInitPOf_rel G decE)
    R F D hFS hPCS _

end CatCrypt.Crypto.Signal.DoubleRatchet.ExtractedScheme
