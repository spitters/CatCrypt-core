/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signal.DoubleRatchet.ExtractedScheme
public import CatCryptCore.Crypto.Messaging.SMHdrAdaptive

/-!
# The extracted double ratchet against passive adversaries

A passive adversary of the games over a secure-messaging scheme asks no corruption query: every
query of its tree lies in `smNoCorrupt`. The oracles `smSchemeOracle` and `smSchemeAdOracle`
read the delays `ΔFS`, `ΔPCS` only when they answer a corruption query, so the games against a
passive adversary do not depend on the delays (`smCorruptGame_passive`,
`smAdaptiveGame_passive`). The bounds of the store-free abstraction `drExtractedSM` of the
extracted double ratchet in the corruption game (`drExtracted_corruptAdvantage_le`) and in the
game with an adaptive challenge epoch (`drExtracted_adaptiveAdvantage_le`) therefore hold at a
passive adversary for all delays, with the terms taken at `ΔFS = ΔPCS = 2`.

The passive notion of this module is the game with an adaptive challenge epoch at an adversary
without corruption queries. The adversary chooses the challenge epoch and the messages during
the run, with associated data built by the scheme from the state (the header of the crate holds
the fresh ratchet public value).

The CKA terms of the bounds are corruption-game advantages of the Diffie–Hellman CKA
`dhCKAOf G decE`. At the delays `2`, `2` the theorem `dhCKAOf_corrupt_advantage_eq_advAt` of
`CatCryptCore.Crypto.Messaging.CKACorrupt` makes each of them the advantage of the DDH reduction
`ckaCorruptDDHRedOf decE 2 2` against the DDH games over the law of `decE` at a uniform key:
the DDH advantage itself when that law is uniform (`_of_uniform`), and at most the DDH
advantage plus `4 c.δ` for a sampler certificate `c` (`dhCKAOf_corrupt_advantage_le`). These
are the counterparts of the DDH terms of `sm_dh_advantage_le`.

The independence of the games from the delays is stated over any scheme in
`CatCryptCore.Crypto.Messaging.SMHdrAdaptive`.

## Main results

* `drExtracted_passive_adaptiveAdvantage_eq` — the game of the extracted ratchet against a
  passive adversary is `sm_adaptive_game` at the wrapper adversary
* `drExtracted_passive_adaptiveAdvantage_le`,
  `drExtracted_passive_adaptiveAdvantage_le_of_uniform` — the adaptive bound, with CKA terms and
  with DDH terms
* `drExtracted_passive_corruptAdvantage_le` — the bound of the corruption game with DDH terms
  plus `4 c.δ` for each bit
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.DoubleRatchet.ExtractedScheme

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Messaging
open CatCrypt.Crypto.Assumptions CatCryptCore.Examples.CyclicGroupDDH
open CatCrypt.Crypto.Signal.DoubleRatchet.ExtractedCorrespondence
open Doubleratchet
open scoped ENNReal

section Passive

variable (Dp : Type) [Inhabited Dp] [DoubleRatchetDeps Dp]
  {RK Sa W Ct Sk A : Type} [SampleableType W] {G : Type} [CG : CyclicGroup G]
  [Fintype RK] [Nonempty RK] [Fintype Sk] [Nonempty Sk] [SampleableType Ct]
  [Fintype Sa] [Nonempty Sa] [DecidableEq RK] [Fintype G] [Nonempty G] [DecidableEq G]
  {R : PRGDef (RK × G) (RK × Sa)} {F : PRGDef Sa (W × Sa)}
  {D : AEADDef W Ct (A × ((G × ℕ) × ℕ))} {ptLen : Int} {encR : RK → Array Int}
  {encG : G → Array Int} {encSk : Sk → Array Int} {decE : Sk → CG.Exp} {encS : Sa → Array Int}
  {encW : W → Array Int} {encPt : W → Array Int} {encC : Ct → Array Int}
  {encAD : A → Array Int} {adOf : W → A}

omit [Fintype Sa] [Nonempty Sa] [DecidableEq RK] [Fintype G] [Nonempty G] [DecidableEq G] in
/-- **The extracted double ratchet against a passive adversary is the ACD game.** Under
`DrHom`, for every adversary `B` without corruption queries and all delays, the advantage of
`B` in the game over the store-free abstraction `drExtractedSM` with an adaptive challenge epoch
is the advantage in `sm_adaptive_game (dhCKAOf G decE) R F D` at the delays `2`, `2` of the
wrapper adversary `smHdrAdaptive (drHdrAD adOf)` of `B` with the answers encoded. -/
theorem drExtracted_passive_adaptiveAdvantage_eq
    (h : DrHom Dp G R F D ptLen encR encG encSk decE encS encW encPt encC encAD (drEncH encG))
    (ΔFS ΔPCS : ℕ)
    (B : Array Int → OracleAdv (SMQuery W) (SMSchemeAns (Array Int) (Array Int) DrLeak) Bool)
    (hB : ∀ T, (B T).MayOnlyCall smNoCorrupt) :
    (drExtractedSM Dp RK ptLen encR encG encSk decE encPt encC encAD adOf).adaptiveAdvantage
        ΔFS ΔPCS B =
      SM_Adaptive_Advantage (dhCKAOf G decE) R F D 2 2 (smHdrAdaptive (drHdrAD adOf)
        fun T => (B (encG T)).mapQueryAnswer id
          (SMSchemeAns.map encG encC (drEncLeak encR encG encSk decE encS))) := by
  rw [SMScheme.adaptiveAdvantage_passive _ ΔFS ΔPCS 2 2 B hB,
    (drExtracted_sim Dp h).adaptiveAdvantage_eq,
    acdHdrSM_adaptiveAdvantage_eq (dhCKAOf G decE) (dhCKAOf_correct G decE) (dhInitPOf G decE)
      (dhCKAOf_init_eq G decE) (dhInitPOf_rel G decE)]

/-- **Confidentiality of the extracted double ratchet against passive adversaries.** Under
`DrHom`, for every adversary `B` without corruption queries and all delays, the advantage of `B`
in the game over the store-free abstraction `drExtractedSM` with an adaptive challenge epoch is
at most the bound of `drExtracted_adaptiveAdvantage_le` at the delays `2`, `2`. -/
theorem drExtracted_passive_adaptiveAdvantage_le
    (h : DrHom Dp G R F D ptLen encR encG encSk decE encS encW encPt encC encAD (drEncH encG))
    (ΔFS ΔPCS : ℕ)
    (B : Array Int → OracleAdv (SMQuery W) (SMSchemeAns (Array Int) (Array Int) DrLeak) Bool)
    (hB : ∀ T, (B T).MayOnlyCall smNoCorrupt) :
    (drExtractedSM Dp RK ptLen encR encG encSk decE encPt encC encAD adOf).adaptiveAdvantage
        ΔFS ΔPCS B ≤
      ∑' e, (∑ b : Bool, CKA_Corrupt_Advantage (dhCKAOf G decE) 2 2
            (smcCKARed R F D b (smGuessAdv 2 2 (smHdrAdaptive (drHdrAD adOf)
              fun T => (B (encG T)).mapQueryAnswer id
                (SMSchemeAns.map encG encC (drEncLeak encR encG encSk decE encS))) e)) +
        ∑ b : Bool, PRFPRNG_Advantage R (smcRootRed (dhCKAOf G decE) R F D 2 2 b
          (dhInitPOf G decE) (smGuessAdv 2 2 (smHdrAdaptive (drHdrAD adOf)
            fun T => (B (encG T)).mapQueryAnswer id
              (SMSchemeAns.map encG encC (drEncLeak encR encG encSk decE encS))) e)) +
        FSAEAD_Corrupt_Advantage F D (smcFSRed (dhCKAOf G decE) R F D 2 2
          (dhInitPOf G decE) (smGuessAdv 2 2 (smHdrAdaptive (drHdrAD adOf)
            fun T => (B (encG T)).mapQueryAnswer id
              (SMSchemeAns.map encG encC (drEncLeak encR encG encSk decE encS))) e))) := by
  rw [SMScheme.adaptiveAdvantage_passive _ ΔFS ΔPCS 2 2 B hB]
  exact drExtracted_adaptiveAdvantage_le Dp h le_rfl (by norm_num) B

/-- **Confidentiality of the extracted double ratchet against passive adversaries at uniform
exponents.** Under `DrHom`, when the exponent of a uniform secret key is uniform, for every
adversary `B` without corruption queries and all delays, the advantage of `B` in the game over
the store-free abstraction `drExtractedSM` with an adaptive challenge epoch is at most the bound of
`drExtracted_passive_adaptiveAdvantage_le` with each CKA term replaced by the DDH advantage of
the reduction `ckaCorruptDDHRedOf decE 2 2`. -/
theorem drExtracted_passive_adaptiveAdvantage_le_of_uniform
    (h : DrHom Dp G R F D ptLen encR encG encSk decE encS encW encPt encC encAD (drEncH encG))
    (hU : ((SDistr.uniform Sk).bind fun s => SDistr.pure (decE s)) = SDistr.uniform CG.Exp)
    (ΔFS ΔPCS : ℕ)
    (B : Array Int → OracleAdv (SMQuery W) (SMSchemeAns (Array Int) (Array Int) DrLeak) Bool)
    (hB : ∀ T, (B T).MayOnlyCall smNoCorrupt) :
    (drExtractedSM Dp RK ptLen encR encG encSk decE encPt encC encAD adOf).adaptiveAdvantage
        ΔFS ΔPCS B ≤
      ∑' e, (∑ b : Bool, DDH_Advantage G (ckaCorruptDDHRedOf (G := G) decE 2 2
            (smcCKARed R F D b (smGuessAdv 2 2 (smHdrAdaptive (drHdrAD adOf)
              fun T => (B (encG T)).mapQueryAnswer id
                (SMSchemeAns.map encG encC (drEncLeak encR encG encSk decE encS))) e))) +
        ∑ b : Bool, PRFPRNG_Advantage R (smcRootRed (dhCKAOf G decE) R F D 2 2 b
          (dhInitPOf G decE) (smGuessAdv 2 2 (smHdrAdaptive (drHdrAD adOf)
            fun T => (B (encG T)).mapQueryAnswer id
              (SMSchemeAns.map encG encC (drEncLeak encR encG encSk decE encS))) e)) +
        FSAEAD_Corrupt_Advantage F D (smcFSRed (dhCKAOf G decE) R F D 2 2
          (dhInitPOf G decE) (smGuessAdv 2 2 (smHdrAdaptive (drHdrAD adOf)
            fun T => (B (encG T)).mapQueryAnswer id
              (SMSchemeAns.map encG encC (drEncLeak encR encG encSk decE encS))) e))) := by
  obtain rfl : ‹Fintype G› = CG.finG := Subsingleton.elim _ _
  have hcka : ∀ C, CKA_Corrupt_Advantage (dhCKAOf G decE) 2 2 C =
      DDH_Advantage G (ckaCorruptDDHRedOf (G := G) decE 2 2 C) := fun C =>
    (dhCKAOf_corrupt_advantage_eq_advAt decE le_rfl le_rfl C).trans
      (by rw [hU, ddhSampledUnif_advAt_uniform])
  refine (drExtracted_passive_adaptiveAdvantage_le Dp h ΔFS ΔPCS B hB).trans (le_of_eq ?_)
  simp only [hcka]

/-- **Confidentiality of the extracted double ratchet against passive adversaries, from DDH.**
Under `DrHom`, for a certificate `c` from the image `c.μ` of the uniform sampler on `Sk` under
`decE` to the uniform exponent sampler `c.ν`, for every adversary `B` without corruption queries
whose interactions ask at most `q` queries, and all delays, the advantage of `B` in the
corruption game over the store-free abstraction `drExtractedSM` is at most the bound of
`drExtracted_corruptAdvantage_le` at the delays `2`, `2` with each CKA term replaced by the DDH
advantage of the reduction `ckaCorruptDDHRedOf decE 2 2` plus `4 c.δ`. -/
theorem drExtracted_passive_corruptAdvantage_le [DecidableEq A]
    (h : DrHom Dp G R F D ptLen encR encG encSk decE encS encW encPt encC encAD (drEncH encG))
    (c : SamplerCert CG.Exp)
    (hμ : c.μ = (SDistr.uniform Sk).bind fun s => SDistr.pure (decE s))
    (hν : c.ν = SDistr.uniform CG.Exp) (ΔFS ΔPCS : ℕ)
    (B : SMSchemeAdv (Array Int) W (Array Int) DrLeak) (q : ℕ)
    (hq : ∀ t T, (B.play t T).IsQueryBound q)
    (hB : ∀ t T, (B.play t T).MayOnlyCall smNoCorrupt) :
    (drExtractedSM Dp RK ptLen encR encG encSk decE encPt encC encAD adOf).corruptAdvantage
        ΔFS ΔPCS B ≤
      ∑ b : Bool, (DDH_Advantage G (ckaCorruptDDHRedOf (G := G) decE 2 2 (smcCKARed R F D b
          ((B.comap encG encC (drEncLeak encR encG encSk decE encS)).toHdr (drHdrAD adOf)))) +
          4 * c.δ) +
        ∑ b : Bool, PRFPRNG_Advantage R (smcRootRed (dhCKAOf G decE) R F D 2 2 b
          (dhInitPOf G decE)
          ((B.comap encG encC (drEncLeak encR encG encSk decE encS)).toHdr (drHdrAD adOf))) +
        (∑ i ∈ Finset.range q, PRG_Advantage F (fsCorrPRGRed F D false i
            (smcFSRed (dhCKAOf G decE) R F D 2 2 (dhInitPOf G decE)
              ((B.comap encG encC (drEncLeak encR encG encSk decE encS)).toHdr
                (drHdrAD adOf)))) +
          ∑ i ∈ Finset.range q, PRG_Advantage F (fsCorrPRGRed F D true i
            (smcFSRed (dhCKAOf G decE) R F D 2 2 (dhInitPOf G decE)
              ((B.comap encG encC (drEncLeak encR encG encSk decE encS)).toHdr
                (drHdrAD adOf)))) +
          AEAD_CCA_Advantage D (fsCorrAEADRed F D
            (smcFSRed (dhCKAOf G decE) R F D 2 2 (dhInitPOf G decE)
              ((B.comap encG encC (drEncLeak encR encG encSk decE encS)).toHdr
                (drHdrAD adOf))))) := by
  obtain rfl : ‹Fintype G› = CG.finG := Subsingleton.elim _ _
  rw [SMScheme.corruptAdvantage_passive _ ΔFS ΔPCS 2 2 B hB]
  refine (drExtracted_corruptAdvantage_le Dp h le_rfl (by norm_num) B q hq).trans ?_
  gcongr with b
  exact dhCKAOf_corrupt_advantage_le decE c hμ hν le_rfl le_rfl _

end Passive

end CatCrypt.Crypto.Signal.DoubleRatchet.ExtractedScheme
