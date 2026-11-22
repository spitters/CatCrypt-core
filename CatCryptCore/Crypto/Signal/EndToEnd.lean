/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SignalStackSM
public import CatCryptCore.Crypto.AKE.X3DH.ExtractedGame
public import CatCryptCore.Crypto.Signal.SessionExtracted
public import CatCryptCore.Crypto.Messaging.SignalStackSMPrekey

/-!
# The Signal stack over the extracted ratchet and the model X3DH

The theorem `signal_extracted_e2e` about the Signal stack of the model X3DH and the haxpipeT
extraction of `doubleratchet-hax`, and about the extraction of `x3dh-hax`, assembled from the
theorems of the scheme records by instantiation. Its hypotheses are the hom records of the two
extractions at shared
encodings of group elements (`encG`) and of session and root keys (`encR`), `X3dhSquareHom` and
`DrHom` (at the header encoding `drEncH encG`), and the left-inverse facts of the encodings
`encG` and `encR` that the game over the extracted X3DH functions decodes with. These hypotheses
exclude X25519, where `encG` is the u-coordinate: it identifies `T` and `-T` (`encU_eq_iff`), so
it has no left inverse, and no clamped scalar has the neutral element as public key, which the
field `dh_pub` of `X3dhSquareHom` requires at the scalar `0`. The theorem is the conjunction of
three statements: the bound is in the first, for the model X3DH with the key derivation a random
function, and the second is an equality of the extracted X3DH with the model at a fixed key
derivation.

* **The stack over the extracted ratchet.** The stack of `SignalStackSM`, X3DH followed by the
  ratchet layer over `drExtractedSM`, the store-free abstraction of the extracted double ratchet
  whose corruptions return the key material `drExpose`, keyed by the session key of
  X3DH through `drExtractedIni`, realizes the secure-messaging functionality `F_SM` behind the
  X3DH simulator `scSim GX`. The bound `signalExtractedBound` is the gap Diffie–Hellman bound of
  X3DH, the CKA corruption, PRF-PRNG and FS-AEAD advantages of the reductions of `SMCorrupt` at
  the wrapper adversaries `toHdr (drHdrAD adOf)` of the reductions `smHopRed` of the stack with
  the answers encoded, and the probabilities that a key is read twice
  (`signal_stack_realizes_FSM` at `drExtractedSM`, then `drExtracted_corruptAdvantage_le_fsaead`).
  The AEAD of the model has the associated data `drHdrAD adOf`: the associated data of the key
  agreement and the message header. The key derivation of X3DH in the stack is the lazily
  sampled random function `lazyKDF`. The probability that a key is read twice is `1` when the
  environment always makes both partners of an unexposed session read their key, and the bound
  is then at least `1`. The CKA term is bounded by DDH for `2 ≤ ΔPCS`
  (`dhCKAOf_corrupt_advantage_le`); the statement allows `ΔPCS = 1`, where a corruption may
  return the exponent that determines the challenge key.
* **The extracted X3DH.** The system of the game over the extracted X3DH functions is the real
  system `x3dhRealOfK (fixedKDF H) (x3dhAlg GX)` of the square model with the key derivation the
  fixed function `H` (`extSys_eq`).
* **The session link.** The session that the extracted initiator computes, `X3dh.initiate` and
  then `Uninitialized_establish_alice` on its key, is at step `0` with the state of the epoch
  opening `ratchet` of the extracted scheme from the initial state `drInitState` whose root key
  is the encoding of the X3DH key `H (aliceInp …)` of the square model and whose remote public
  value is the encoded signed prekey (`initiate_square_enc`, `signal_session_extracted_drOpen`).
  The keyed initialisation `drExtractedIni k` of the stack starts both parties in `drInitState`
  at the root key `encR k`.

## Main definitions

* `drExtractedIni` — the keyed initialisation of the extracted double ratchet.
* `signalExtractedBound` — the bound of the Signal stack over the extracted ratchet.

## Main results

* `drExtractedSM_init_eq` — the initialisation of `drExtractedSM` is `drExtractedIni` at a
  uniform root key.
* `drExtracted_corruptAdvantage_le_fsaead` — the corruption bound of the extracted ratchet with
  the FS-AEAD advantage of `smcFSRed`.
* `signal_stack_realizes_FSM_extracted` — the Signal stack over the extracted ratchet realizes
  `F_SM`.
* `signal_extracted_e2e` — the conjunction of the three statements.
* `smMulti_sim_step`, `smSessView_sim` — session views transfer along a simulation of schemes.
* `signal_stack_realizes_FSM_acdHdr_prekey` — the Signal stack with the signed prekey over the
  gated ACD construction with headers realizes `F_SMK`.
* `signal_extracted_e2e_prekey` — the same conjunction with the signed prekey and the
  responder's state, with the bound `signalExtractedBoundPair` at the encoded schedule
  `drSchPair`, under the same hypotheses on the encodings.
-/

@[expose] public section

set_option autoImplicit false

/-! ## Lemmas for the scheme module -/

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
  {R : PRGDef (RK × G) (RK × Sa)} {F : PRGDef Sa (W × Sa)}
  {D : AEADDef W Ct (A × ((G × ℕ) × ℕ))} {ptLen : Int} {encR : RK → Array Int}
  {encG : G → Array Int} {encSk : Sk → Array Int} {decE : Sk → CG.Exp} {encS : Sa → Array Int}
  {encW : W → Array Int} {encPt : W → Array Int} {encC : Ct → Array Int}
  {encAD : A → Array Int} {adOf : W → A}

/-- **Forward secrecy and post-compromise security of the store-free abstraction `drExtractedSM`,
with the FS-AEAD term**, for corruptions that return the key material `drExpose`. Under `DrHom`,
with `2 ≤ ΔFS` and `1 ≤ ΔPCS`, the advantage in the corruption
game over `drExtractedSM` is at most the CKA corruption advantages of `smcCKARed`, the PRF-PRNG
advantages of the root KDF `R` at `smcRootRed` and the FS-AEAD advantage with corruption of `F`,
`D` at `smcFSRed`, for the CKA `dhCKAOf G decE` and the wrapper adversary `toHdr (drHdrAD adOf)`
of `A` with the answers encoded and relabelled. -/
theorem drExtracted_corruptAdvantage_le_fsaead
    (h : DrHom Dp G R F D ptLen encR encG encSk decE encS encW encPt encC encAD (drEncH encG))
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS)
    (B : SMSchemeAdv (Array Int) W (Array Int) DrLeak) :
    (drExtractedSM Dp RK ptLen encR encG encSk decE encPt encC encAD adOf).corruptAdvantage
        ΔFS ΔPCS B ≤
      ∑ b : Bool, CKA_Corrupt_Advantage (dhCKAOf G decE) ΔFS ΔPCS (smcCKARed R F D b
          ((B.comap encG encC (drEncLeak encR encG encSk decE encS)).toHdr (drHdrAD adOf))) +
        ∑ b : Bool, PRFPRNG_Advantage R (smcRootRed (dhCKAOf G decE) R F D ΔFS ΔPCS b
          (dhInitPOf G decE)
          ((B.comap encG encC (drEncLeak encR encG encSk decE encS)).toHdr (drHdrAD adOf))) +
        FSAEAD_Corrupt_Advantage F D (smcFSRed (dhCKAOf G decE) R F D ΔFS ΔPCS
          (dhInitPOf G decE)
          ((B.comap encG encC (drEncLeak encR encG encSk decE encS)).toHdr (drHdrAD adOf))) := by
  rw [drExtracted_corruptAdvantage_eq Dp h]
  exact sm_corrupt_advantage_le (dhCKAOf G decE) (dhCKAOfCoins_sound G decE) (dhInitPOf G decE)
    (dhCKAOf_init_eq G decE) R F D hFS hPCS _

end CatCrypt.Crypto.Signal.DoubleRatchet.ExtractedScheme

/-! ## Lemmas for the prekey stack module: the ACD construction with headers -/

namespace CatCrypt.Crypto.Messaging.SignalStackSMPrekey

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Messaging
open CatCrypt.Crypto.Assumptions CatCrypt.Crypto.PRPPRF CatCryptCore.Examples.CyclicGroupDDH
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.AKE.X3DHSquare CatCrypt.Crypto.AKE.X3DHSquareGDH
open CatCrypt.Crypto.AKE.X3DHSquarePrekey CatCrypt.Crypto.Messaging.SignalStackSM
open CatCrypt.Crypto.Messaging.SignalStack CatCrypt.Crypto.Messaging.SignalStackUC
open CatCrypt.Crypto.PAKE.CPaceSquare (PureNF pureNF_sample pureNF_pure)
open CatCrypt.Crypto.PAKE.DHExtract
open scoped ENNReal

section ACDHdr

variable {S W : Type} [Field S] [Fintype S] [SampleableType W] (GX : DHGroup S W)
  {Gc : Type} [CG : CyclicGroup Gc] [DecidableEq Gc] {Sk : Type} [Fintype Sk] [Nonempty Sk]
  [Inhabited Sk] {RK Sa Wd Ct AD V : Type} [SampleableType Wd] [SampleableType Ct] [Fintype RK]
  [Nonempty RK] [Inhabited RK] [DecidableEq RK] [Fintype Sa] [Nonempty Sa]

/-- **The efficient layer of the gated ACD ratchet with headers at the signed-prekey pair**: at
the key `k` and the public value `w` of the prekey, the real session view of the gated ACD
construction with headers over `dhCKAPre decE (encW w)`, with the corruption answers read through
`SMHdrSt.mapCk dhPreOpen`. It reads the prekey only through its public value. -/
noncomputable def smPreViewHdr (decE : Sk → CG.Exp) (encW : W → Gc)
    (R : PRGDef (RK × Gc) (RK × Sa)) (F : PRGDef Sa (Wd × Sa)) (D : AEADDef Wd Ct AD)
    (hdrAD : Wd → (Gc × ℕ) × ℕ → AD)
    (Sch : Gc → OracleAdv (SMQuery Wd)
      (SMSchemeAns Gc Ct (Option (SMHdrSt (Gc × Sk) RK Sa Gc))) V)
    (t n ΔFS ΔPCS : ℕ) (p : RK × W) : SPComp V :=
  smSessView (acdHdrSM (dhCKAPre decE (encW p.2)) R F D hdrAD).gateB
    (gateIni (acdHdrIni (Sa := Sa) (dhCKAPre decE (encW p.2))))
    (fun T => (Sch T).mapQueryAnswer id
      (SMSchemeAns.map id id (Option.map (SMHdrSt.mapCk dhPreOpen))))
    t n ΔFS ΔPCS (fun _ => false) p.1

omit [SampleableType W] [DecidableEq Gc] [Inhabited RK] [DecidableEq RK] [Fintype Sa]
  [Nonempty Sa] in
/-- The efficient layer with headers never fails. -/
theorem smPreViewHdr_noFail (decE : Sk → CG.Exp) (encW : W → Gc)
    (R : PRGDef (RK × Gc) (RK × Sa)) (F : PRGDef Sa (Wd × Sa)) (D : AEADDef Wd Ct AD)
    (hdrAD : Wd → (Gc × ℕ) × ℕ → AD)
    (Sch : Gc → OracleAdv (SMQuery Wd)
      (SMSchemeAns Gc Ct (Option (SMHdrSt (Gc × Sk) RK Sa Gc))) V)
    (t n ΔFS ΔPCS : ℕ) (p : RK × W) :
    SPComp.NoFail (smPreViewHdr decE encW R F D hdrAD Sch t n ΔFS ΔPCS p) := by
  have hC : PureNF (dhCKAPre decE (encW p.2)).init := by
    simp only [dhCKAPre]
    exact PureNF.bind (pureNF_sample Sk) fun _ => pureNF_pure _
  exact (smSessView_pureNF (fun _ => (hC.bind fun _ => pureNF_pure _).bind
    fun _ => pureNF_pure _) _ t n ΔFS ΔPCS _ p.1).2

/-- **The bound of the ACD ratchet at the signed-prekey pair** of `x₀` at an adversary `A` of
`sm_corrupt_game` with associated data in `AD`: the right-hand side of
`sm_dh_corrupt_advantage_le_pair`. -/
noncomputable def smPairBoundAD (decE : Sk → CG.Exp) (c : SamplerCert CG.Exp)
    (R : PRGDef (RK × Gc) (RK × Sa)) (F : PRGDef Sa (Wd × Sa)) (D : AEADDef Wd Ct AD)
    (ΔFS ΔPCS : ℕ) (x₀ : Sk) (A : SMCorruptAdv (Gc × Sk) Gc RK Sa Wd Ct AD) : ℝ≥0∞ :=
  (∑ b : Bool, PRFPRNG_Advantage R
      (smcRootRedFirst (dhCKAOf Gc decE) R F D ΔFS ΔPCS b (dhPairInit decE x₀) A.first) +
    FSAEAD_Corrupt_Advantage F D
      (smcFSRed (dhCKAOf Gc decE) R F D ΔFS ΔPCS (PMF.pure (dhPairInit decE x₀)) A.first)) +
  (∑ b : Bool, DDH_Advantage Gc
      (ckaCorruptDDHRedAt decE x₀ ΔFS ΔPCS (smcCKARed (Rand := Sk) R F D b A.later)) +
    8 * c.δ +
    ∑ b : Bool, PRFPRNG_Advantage R
      (smcRootRed (dhCKAOf Gc decE) R F D ΔFS ΔPCS b (PMF.pure (dhPairInit decE x₀)) A.later) +
    FSAEAD_Corrupt_Advantage F D
      (smcFSRed (dhCKAOf Gc decE) R F D ΔFS ΔPCS (PMF.pure (dhPairInit decE x₀)) A.later))

omit [Inhabited RK] in
/-- **The corruption advantage of the gated ACD ratchet with headers at the signed-prekey
pair**: the advantage of `A` is at most `smPairBoundAD` at the wrapper adversary
`A.gateB.toHdr hdrAD`. -/
theorem gateB_acdHdr_corruptAdvantage_le_pair (decE : Sk → CG.Exp) (c : SamplerCert CG.Exp)
    (hμ : c.μ = (SDistr.uniform Sk).bind fun x => SDistr.pure (decE x))
    (hν : c.ν = SDistr.uniform CG.Exp) (R : PRGDef (RK × Gc) (RK × Sa))
    (F : PRGDef Sa (Wd × Sa)) (D : AEADDef Wd Ct AD) (hdrAD : Wd → (Gc × ℕ) × ℕ → AD)
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 2 ≤ ΔPCS) (x₀ : Sk)
    (A : SMSchemeAdv Gc Wd Ct (Option (SMHdrSt (Gc × Sk) RK Sa Gc))) :
    (acdHdrSM ((dhCKAOf Gc decE).atInit (dhPairInit decE x₀)) R F D hdrAD).gateB.corruptAdvantage
        ΔFS ΔPCS A ≤
      smPairBoundAD decE c R F D ΔFS ΔPCS x₀ (A.gateB.toHdr hdrAD) := by
  have hg : (acdHdrSM ((dhCKAOf Gc decE).atInit (dhPairInit decE x₀)) R F D
      hdrAD).gateB.corruptAdvantage ΔFS ΔPCS A =
      (acdHdrSM ((dhCKAOf Gc decE).atInit (dhPairInit decE x₀)) R F D hdrAD).corruptAdvantage
        ΔFS ΔPCS A.gateB := by
    simp only [SMScheme.corruptAdvantage, smSchemeGame_gateB]
  rw [hg]
  exact acdHdrSM_dh_corruptAdvantage_le_pair decE c hμ hν R F D hdrAD hFS hPCS x₀ _

variable [Inhabited S]

/-- **The Signal stack over the gated ACD ratchet with headers at the signed-prekey pair
realizes secure messaging with corruption** (genuine UC): `signal_stack_realizes_FSM_prekey` at
the schemes `(acdHdrSM ((dhCKAOf Gc decE).atInit (dhPairInit decE (ι x₀))) R F D hdrAD).gateB`,
keyed by the root key through `gateIni (acdHdrIni …)`, for a map `ι` of the X3DH prekey secret to
the secret key of the ratchet and a map `encW` of the X3DH public values to the ratchet group
with `g ^ decE (ι x) = encW (GX.pub x)`.

*Ideal functionality.* `F_SMK` at these schemes: completed sessions have the ideal view of the
gated ratchet with headers at the prekey pair of their datum.

*Real world.* X3DH with the datum followed by the ratchet layer whose first epoch starts from the
prekey pair of the responder.

*Simulator.* `chanSim (simProtPair GX) x3dhFwd`.

*Bound.* `fsmBoundPair` with the efficient layer `smPreViewHdr` (`smSessView_pair_eq_pre_hdr`)
and, at each datum `x₀`, the bound `smPairBoundAD` at `ι x₀` and the wrapper adversary
`A.gateB.toHdr hdrAD`: PRF-PRNG, FS-AEAD and DDH advantages of explicit reductions and `8 c.δ`,
for `2 ≤ ΔFS` and `2 ≤ ΔPCS`. -/
theorem signal_stack_realizes_FSM_acdHdr_prekey (P : Finset PartyId) (decE : Sk → CG.Exp)
    (c : SamplerCert CG.Exp)
    (hμ : c.μ = (SDistr.uniform Sk).bind fun x => SDistr.pure (decE x))
    (hν : c.ν = SDistr.uniform CG.Exp) (ι : S → Sk) (encW : W → Gc)
    (hpub : ∀ x, CG.pow (decE (ι x)) = encW (GX.pub x)) (R : PRGDef (RK × Gc) (RK × Sa))
    (F : PRGDef Sa (Wd × Sa)) (D : AEADDef Wd Ct AD) (hdrAD : Wd → (Gc × ℕ) × ℕ → AD)
    (Sch : Gc → OracleAdv (SMQuery Wd)
      (SMSchemeAns Gc Ct (Option (SMHdrSt (Gc × Sk) RK Sa Gc))) V)
    {t n ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 2 ≤ ΔPCS) :
    RealizesSim ((x3dhRealPair (K := RK) GX).seq (smCorruptLayerK
        (fun x₀ => (acdHdrSM ((dhCKAOf Gc decE).atInit (dhPairInit decE (ι x₀))) R F D
          hdrAD).gateB)
        (fun k x₀ => gateIni (acdHdrIni (Sa := Sa)
          ((dhCKAOf Gc decE).atInit (dhPairInit decE (ι x₀))))  k)
        Sch t n ΔFS ΔPCS))
      (F_SMK (fun x₀ => (acdHdrSM ((dhCKAOf Gc decE).atInit (dhPairInit decE (ι x₀))) R F D
          hdrAD).gateB)
        (fun k x₀ => gateIni (acdHdrIni (Sa := Sa)
          ((dhCKAOf Gc decE).atInit (dhPairInit decE (ι x₀)))) k)
        Sch t n ΔFS ΔPCS)
      (chanSim (simProtPair (K := RK) GX) x3dhFwd)
      (fsmBoundPair GX P
        (fun x₀ => (acdHdrSM ((dhCKAOf Gc decE).atInit (dhPairInit decE (ι x₀))) R F D
          hdrAD).gateB)
        (fun k x₀ => gateIni (acdHdrIni (Sa := Sa)
          ((dhCKAOf Gc decE).atInit (dhPairInit decE (ι x₀)))) k)
        (fun x₀ A => smPairBoundAD decE c R F D ΔFS ΔPCS (ι x₀) (A.gateB.toHdr hdrAD))
        Sch t n ΔFS ΔPCS (smPreViewHdr decE encW R F D hdrAD Sch t n ΔFS ΔPCS)
        (smPreViewHdr_noFail decE encW R F D hdrAD Sch t n ΔFS ΔPCS)) := by
  have hM : ∀ x₀ : S,
      (acdHdrSM ((dhCKAOf Gc decE).atInit (dhPairInit decE (ι x₀))) R F D hdrAD).gateB.init =
        SPComp.bind (SPComp.sample RK) fun k => gateIni (acdHdrIni (Sa := Sa)
          ((dhCKAOf Gc decE).atInit (dhPairInit decE (ι x₀)))) k := by
    intro x₀
    simp only [SMScheme.gateB, acdHdrSM, gateIni, acdHdrIni, CKADef.atInit, SPComp.pure_bind,
      SPComp.bind_assoc]
  have hini : ∀ (k : RK) (x₀ : S), PureNF (gateIni (acdHdrIni (Sa := Sa)
      ((dhCKAOf Gc decE).atInit (dhPairInit decE (ι x₀)))) k) :=
    fun _ _ => ((pureNF_pure _).bind fun _ => pureNF_pure _).bind fun _ => pureNF_pure _
  have hL : ∀ k x₀, smRealViewK
      (fun x₀ => (acdHdrSM ((dhCKAOf Gc decE).atInit (dhPairInit decE (ι x₀))) R F D
        hdrAD).gateB)
      (fun k x₀ => gateIni (acdHdrIni (Sa := Sa)
        ((dhCKAOf Gc decE).atInit (dhPairInit decE (ι x₀)))) k)
      Sch t n ΔFS ΔPCS (k, x₀) =
        smPreViewHdr decE encW R F D hdrAD Sch t n ΔFS ΔPCS (k, GX.pub x₀) := by
    intro k x₀
    rw [smRealViewK, smRealView, smPreViewHdr, ← hpub]
    exact smSessView_pair_eq_pre_hdr decE R F D hdrAD Sch t n ΔFS ΔPCS _ (ι x₀) k
  intro ζ Z
  exact (signal_stack_realizes_FSM_prekey GX P _ _ hM hini Sch t n ΔFS ΔPCS _
    (smPreViewHdr_noFail decE encW R F D hdrAD Sch t n ΔFS ΔPCS) hL ζ Z).trans
    (fsmBoundPair_mono GX P _ _ (fun x₀ A => gateB_acdHdr_corruptAdvantage_le_pair decE c hμ hν
      R F D hdrAD hFS hPCS (ι x₀) A) Sch t n ΔFS ΔPCS _ _ ζ Z)

end ACDHdr

end CatCrypt.Crypto.Messaging.SignalStackSMPrekey

namespace CatCrypt.Crypto.Signal.EndToEnd

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Messaging
open CatCrypt.Crypto.Assumptions CatCryptCore.Examples.CyclicGroupDDH
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract (DHGroup)
open CatCrypt.Crypto.PAKE.CPaceSquare (PureNF pureNF_pure pureNF_sample)
open CatCrypt.Crypto.AKE.X3DHSquare CatCrypt.Crypto.AKE.X3DHSquareGDH
open CatCrypt.Crypto.AKE.X3DH.SquareCorrespondence CatCrypt.Crypto.AKE.X3DH.ExtractedGame
open CatCrypt.Crypto.Messaging.SignalStack CatCrypt.Crypto.Messaging.SignalStackUC
open CatCrypt.Crypto.Messaging.SignalStackSM
open CatCrypt.Crypto.Signal.DoubleRatchet.ExtractedCorrespondence
open CatCrypt.Crypto.Signal.DoubleRatchet.ExtractedScheme
open CatCrypt.Crypto.Signal.SessionExtracted
open scoped ENNReal

/-! ## The keyed initialisation of the extracted ratchet -/

section Ini

variable {RK Wd Ct Sk Ad : Type} {G : Type} [CG : CyclicGroup G] [Fintype RK] [Nonempty RK]
  [Fintype Sk] [Nonempty Sk] [SampleableType Ct]

/-- **The keyed initialisation of the extracted double ratchet** at the root key `rk`: a uniform
secret key `x₀` of `Sk`, and both parties in the state `drInitState` with the encoded root key,
the key pair `(x₀, g ^ decE x₀)` and the remote public value `g ^ decE x₀`. -/
noncomputable def drExtractedIni (encR : RK → Array Int) (encG : G → Array Int)
    (encSk : Sk → Array Int) (decE : Sk → CG.Exp) (rk : RK) :
    SPComp (Array Int × Doubleratchet.RatchetState_T × Doubleratchet.RatchetState_T) :=
  SPComp.bind (SPComp.sample Sk) fun x =>
    SPComp.pure (encG (CG.pow (decE x)),
      drInitState (encR rk) (encSk x) (encG (CG.pow (decE x))) (encG (CG.pow (decE x))),
      drInitState (encR rk) (encSk x) (encG (CG.pow (decE x))) (encG (CG.pow (decE x))))

omit [Fintype RK] [Nonempty RK] [SampleableType Ct] in
/-- The keyed initialisation neither touches the heap nor fails. -/
theorem drExtractedIni_pureNF (encR : RK → Array Int) (encG : G → Array Int)
    (encSk : Sk → Array Int) (decE : Sk → CG.Exp) (rk : RK) :
    PureNF (drExtractedIni encR encG encSk decE rk) :=
  (pureNF_sample Sk).bind fun _ => pureNF_pure _

/-- The initialisation of `drExtractedSM` is its keyed initialisation at a uniform root key. -/
theorem drExtractedSM_init_eq (Dp : Type) [Inhabited Dp] [Doubleratchet.DoubleRatchetDeps Dp]
    (ptLen : Int) (encR : RK → Array Int) (encG : G → Array Int)
    (encSk : Sk → Array Int) (decE : Sk → CG.Exp) (encPt : Wd → Array Int)
    (encC : Ct → Array Int) (encAD : Ad → Array Int) (adOf : Wd → Ad) :
    (drExtractedSM Dp RK ptLen encR encG encSk decE encPt encC encAD adOf).init =
      SPComp.bind (SPComp.sample RK) (drExtractedIni encR encG encSk decE) := by
  simp only [drExtractedSM]
  exact SPComp.isPure_bind_comm_left _ _ _ (pureNF_sample Sk).1

end Ini

/-! ## The Signal stack over the extracted ratchet -/

section Stack

variable (Dp : Type) [Inhabited Dp] [Doubleratchet.DoubleRatchetDeps Dp]
  {S RK Sa Wd Ct Sk Ad G V : Type} [Field S] [Fintype S] [Nonempty S] [SampleableType G]
  [CG : CyclicGroup G] [Fintype RK] [Nonempty RK] [Inhabited RK] [DecidableEq RK]
  [Fintype Sa] [Nonempty Sa] [SampleableType Wd] [Fintype Sk] [Nonempty Sk] [SampleableType Ct]

/-- **The bound of the Signal stack over the extracted ratchet** at an environment `Z`: the gap
Diffie–Hellman bound of X3DH at the environment reduced through the ratchet layer, and, at the
environment `Z'` reduced through the simulator, over the keys `i` below the number of
activations of `Z'`, the sum over the `n` challenges `j` of the CKA corruption advantages of
`smcCKARed`, the PRF-PRNG advantages of the root KDF `R` at `smcRootRed` and the FS-AEAD
advantage of `F`, `D` at `smcFSRed`, at the wrapper adversary `toHdr (drHdrAD adOf)` of the
reduction `smHopRed i j Z'` with the answers encoded by `encG`, `encC` and `drEncLeak`, and the
probability that the key `i` is read twice. -/
noncomputable def signalExtractedBound (GX : DHGroup S G) (P : Finset PartyId)
    (R : PRGDef (RK × G) (RK × Sa)) (F : PRGDef Sa (Wd × Sa))
    (D : AEADDef Wd Ct (Ad × ((G × ℕ) × ℕ))) (ptLen : Int)
    (encR : RK → Array Int) (encG : G → Array Int) (encSk : Sk → Array Int) (decE : Sk → CG.Exp)
    (encS : Sa → Array Int) (encPt : Wd → Array Int) (encC : Ct → Array Int)
    (encAD : Ad → Array Int) (adOf : Wd → Ad)
    (Sch : Array Int →
      OracleAdv (SMQuery Wd) (SMSchemeAns (Array Int) (Array Int) DrLeak) V)
    (t n ΔFS ΔPCS : ℕ) (ζ : Type) (Z : Env (Strat ζ (OEv G) (HOut V ⊕ ROut S G RK)) ζ) :
    ℝ≥0∞ :=
  gdhBound GX P ((OProt.oracle (Q := OEv G) (A := OOut S G RK)).reduction
      ((Hybrid.seqCtxR (E := OEv G)
        (smCorruptLayer (drExtractedSM Dp RK ptLen encR encG encSk decE encPt encC encAD adOf)
          (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS)
        (keyLayer_noFail fun k => (smSessView_pureNF
          (drExtractedIni_pureNF encR encG encSk decE) Sch t n ΔFS ΔPCS _ k).2)).reduceEnv Z)) +
    ∑ i ∈ Finset.range ((simSC (V := V) GX).reduceEnv (.inr .idle) Z).input.rounds,
      ((∑ j ∈ Finset.range n,
          (∑ b : Bool, CKA_Corrupt_Advantage (dhCKAOf G decE) ΔFS ΔPCS
              (smcCKARed R F D b (((smHopRed (drExtractedSM Dp RK ptLen encR encG encSk decE
                encPt encC encAD adOf) (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS i
                j ((simSC GX).reduceEnv (.inr .idle) Z)).comap encG encC
                (drEncLeak encR encG encSk decE encS)).toHdr (drHdrAD adOf))) +
            ∑ b : Bool, PRFPRNG_Advantage R (smcRootRed (dhCKAOf G decE) R F D ΔFS ΔPCS b
              (dhInitPOf G decE) (((smHopRed (drExtractedSM Dp RK ptLen encR encG encSk decE
                encPt encC encAD adOf) (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS i
                j ((simSC GX).reduceEnv (.inr .idle) Z)).comap encG encC
                (drEncLeak encR encG encSk decE encS)).toHdr (drHdrAD adOf))) +
            FSAEAD_Corrupt_Advantage F D (smcFSRed (dhCKAOf G decE) R F D ΔFS ΔPCS
              (dhInitPOf G decE) (((smHopRed (drExtractedSM Dp RK ptLen encR encG encSk decE
                encPt encC encAD adOf) (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS i
                j ((simSC GX).reduceEnv (.inr .idle) Z)).comap encG encC
                (drEncLeak encR encG encSk decE encS)).toHdr (drHdrAD adOf))))) +
        prBad (hyb (smRealView (drExtractedSM Dp RK ptLen encR encG encSk decE encPt encC encAD
              adOf) (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS)
          (smIdealView (drExtractedSM Dp RK ptLen encR encG encSk decE encPt encC encAD adOf)
            (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS) i)
          (reuse i) ((simSC GX).reduceEnv (.inr .idle) Z))

variable {R : PRGDef (RK × G) (RK × Sa)} {F : PRGDef Sa (Wd × Sa)}
  {D : AEADDef Wd Ct (Ad × ((G × ℕ) × ℕ))} {ptLen : Int} {encR : RK → Array Int}
  {encG : G → Array Int} {encSk : Sk → Array Int} {decE : Sk → CG.Exp} {encS : Sa → Array Int}
  {encW : Wd → Array Int} {encPt : Wd → Array Int} {encC : Ct → Array Int}
  {encAD : Ad → Array Int} {adOf : Wd → Ad}

omit [Nonempty S] in
/-- **The Signal stack over the store-free abstraction of the extracted double ratchet realizes
secure messaging with corruption of the key material `drExpose`** (genuine UC).

*Ideal functionality.* `F_SM (drExtractedSM …) (drExtractedIni …) Sch t n ΔFS ΔPCS`: the
multi-session functionality over `F_AKE` whose completed sessions have the ideal view of the
schedule `Sch` over the extracted scheme (ideal ciphertexts for the challenge messages of the
honest epoch `t`, the key material `drExpose` leaked in the corruption windows of `ΔFS` and `ΔPCS`
under
a fresh root key), whose exposed sessions have the real view under the adversary key, and whose
adversary port is that of `F_AKE`.

*Real world.* The real X3DH protocol `x3dhReal GX` with the key derivation a lazily sampled
random function, followed by the ratchet layer over the extracted scheme `drExtractedSM`, which
starts both parties at `drInitState` with the session key of every `getKey` answer as root key
and runs the schedule against the oracles of the extracted state functions.

*Simulator.* `scSim GX`, the X3DH simulator over `F_SC`.

*Bound.* Under `DrHom` at the header encoding `drEncH encG`, with `2 ≤ ΔFS` and `1 ≤ ΔPCS`, for
every finite set of parties `P` and every environment `Z`, the distance is at most
`signalExtractedBound`: the gap Diffie–Hellman bound of X3DH and, over the keys of the run and
the challenges `j < n`, the CKA corruption, PRF-PRNG and FS-AEAD advantages of explicit
reductions of the header wrapper adversaries, and the probability that a key is read twice, which
is `1` when both partners of an unexposed session always read their key. The CKA term is bounded
by DDH for `2 ≤ ΔPCS`. -/
theorem signal_stack_realizes_FSM_extracted (GX : DHGroup S G) (P : Finset PartyId)
    (hD : DrHom Dp G R F D ptLen encR encG encSk decE encS encW encPt encC encAD (drEncH encG))
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS)
    (Sch : Array Int →
      OracleAdv (SMQuery Wd) (SMSchemeAns (Array Int) (Array Int) DrLeak) V) (t n : ℕ) :
    RealizesSim ((x3dhReal (K := RK) GX).seq
        (smCorruptLayer (drExtractedSM Dp RK ptLen encR encG encSk decE encPt encC encAD adOf)
          (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS))
      (F_SM (drExtractedSM Dp RK ptLen encR encG encSk decE encPt encC encAD adOf)
        (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS) (scSim GX)
      (signalExtractedBound Dp GX P R F D ptLen encR encG encSk decE encS encPt encC encAD adOf
        Sch t n ΔFS ΔPCS) := by
  intro ζ Z
  refine (signal_stack_realizes_FSM GX P
    (drExtractedSM Dp RK ptLen encR encG encSk decE encPt encC encAD adOf)
    (drExtractedIni encR encG encSk decE) (drExtractedSM_init_eq Dp ptLen encR encG encSk decE
      encPt encC encAD adOf) (drExtractedIni_pureNF encR encG encSk decE) Sch t n ΔFS ΔPCS ζ
      Z).trans ?_
  simp only [fsmBound, signalExtractedBound]
  exact add_le_add le_rfl (Finset.sum_le_sum fun i _ => add_le_add_left
    (Finset.sum_le_sum fun j _ => drExtracted_corruptAdvantage_le_fsaead Dp hD hFS hPCS _) _)

/-- **The Signal stack over the extracted ratchet and the model X3DH, the extracted X3DH, and the
session link.** Under the hom records `X3dhSquareHom` of `x3dh-hax` and `DrHom` of
`doubleratchet-hax` (at the header encoding `drEncH encG`) at shared encodings `encG` of group
elements and `encR` of session and root keys, with `decG`, `decR` left inverses of `encG`,
`encR` (which excludes X25519, whose u-coordinate identifies `T` and `-T`), and with `2 ≤ ΔFS`
and `1 ≤ ΔPCS`, the conjunction of three statements, of which the first has a bound:

1. *The stack over the extracted ratchet* (genuine UC). The ideal functionality is
   `F_SM (drExtractedSM …) (drExtractedIni …) Sch t n ΔFS ΔPCS`, the functionality over `F_AKE`
   with the ideal views of the schedule `Sch` over the extracted scheme in the corruption windows
   of `ΔFS` and `ΔPCS`; the real world is X3DH over `GX` with the key derivation a lazily
   sampled random function, followed by the ratchet layer over the extracted scheme keyed by the
   X3DH session key; the simulator is `scSim GX`; the bound is `signalExtractedBound`, the gap
   Diffie–Hellman bound of X3DH plus the CKA corruption, PRF-PRNG and FS-AEAD advantages of
   explicit reductions and the probabilities that a key is read twice, which are `1` in sum when
   both partners of an unexposed session always read their key
   (`signal_stack_realizes_FSM_extracted`). The CKA term is bounded by DDH for `2 ≤ ΔPCS`.
2. *The extracted X3DH.* The system of the game `extGame` over the extracted X3DH functions is
   the real system `x3dhRealOfK (fixedKDF H) (x3dhAlg GX)` of the square model with the key
   derivation the fixed function `H` (`extSys_eq`).
3. *The session link.* For the initiator `a` of the session `sid` with the peer `b`, the
   encoded secrets `ik`, `ek`, a bundle of the encoded public keys `IKB`, `SPKB`, `OPKB` and the
   new ratchet secret key `y`, the session that `Uninitialized_establish_alice` computes on the
   key of `X3dh.initiate` is at step `0` with the state of the epoch opening `ratchet` at `y` of
   the extracted scheme from the initial state `drInitState` whose root key is the encoding of
   the X3DH key `H (aliceInp GX sid a b ik ek IKB SPKB OPKB)` of the square model and whose
   remote public value is the encoded signed prekey `encG SPKB`, for any key pair `(sk₀, pk₀)` of
   the initial state. -/
theorem signal_extracted_e2e [X3dh.X3dhDeps] {Gh : Type} [Inhabited Gh]
    [Doubleratchet.DoubleRatchetGhost Gh] (GX : DHGroup S G) (P : Finset PartyId)
    {encCtx : SessionId × PartyId × PartyId → Array Int} {encX : S → Array Int}
    {H : Inp G → RK} {decG : Array Int → G} {decR : Array Int → RK}
    (hX : X3dhSquareHom GX encCtx encX encG encR H)
    (hD : DrHom Dp G R F D ptLen encR encG encSk decE encS encW encPt encC encAD (drEncH encG))
    (hG : ∀ Y, decG (encG Y) = Y) (hR : ∀ k, decR (encR k) = k)
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS)
    (Sch : Array Int →
      OracleAdv (SMQuery Wd) (SMSchemeAns (Array Int) (Array Int) DrLeak) V) (t n : ℕ) :
    RealizesSim ((x3dhReal (K := RK) GX).seq
        (smCorruptLayer (drExtractedSM Dp RK ptLen encR encG encSk decE encPt encC encAD adOf)
          (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS))
      (F_SM (drExtractedSM Dp RK ptLen encR encG encSk decE encPt encC encAD adOf)
        (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS) (scSim GX)
      (signalExtractedBound Dp GX P R F D ptLen encR encG encSk decE encS encPt encC encAD adOf
        Sch t n ΔFS ΔPCS) ∧
    (OProt.oracle (Q := HEv ⊕ RAEv G) (A := HOut RK ⊕ ROut S G RK)).sys
        (extGame encCtx encX encG decG decR) = x3dhRealOfK (fixedKDF H) (x3dhAlg GX) ∧
    ∀ (u : Doubleratchet.Uninitialized_T) (g : Gh) (sid : SessionId) (a b : PartyId)
      (ik ek : S) (IKB SPKB OPKB : G) (sig : Array Int) (y : Sk) (sk₀ pk₀ : Array Int),
      (X3dh.initiate (encCtx (sid, a, b)) (encX ik) (encX ek)
          (encG IKB, encG SPKB, encG OPKB, sig) true).map
          (fun o => (Doubleratchet.Uninitialized_establish_alice (D := Dp) u g o.1 (encG SPKB)
            (encSk y) (encG (CG.pow (decE y)))).1) =
        some (Doubleratchet.Session
          ((drExtractedSM Dp RK ptLen encR encG encSk decE encPt encC encAD adOf).ratchet
            (drInitState (encR (H (aliceInp GX sid a b ik ek IKB SPKB OPKB))) sk₀ pk₀
              (encG SPKB)) y).1 0) := by
  refine ⟨signal_stack_realizes_FSM_extracted Dp GX P hD hFS hPCS Sch t n, extSys_eq hX hG hR, ?_⟩
  intro u g sid a b ik ek IKB SPKB OPKB sig y sk₀ pk₀
  rw [initiate_square_eq_some hX, Option.map_some,
    signal_session_extracted_drOpen u g _ _ _ _ _ _ sk₀ pk₀ _, initiate_square_enc hX]
  rfl

end Stack

/-! ## Session views along a simulation of schemes -/

section SessView

variable {St St' Pub Pub' Rand W Ct Ct' Leak Leak' K V : Type} [Fintype Rand] [Nonempty Rand]
  {M' : SMScheme St' Pub' Rand W Ct' Leak'} {M : SMScheme St Pub Rand W Ct Leak}
  {ρ : St' → St → Prop} {encP : Pub → Pub'} {encC : Ct → Ct'} {encL : Leak → Leak'}
  {encI : St → St'}

/-- **The oracles of the multi-challenge game of simulating schemes are coupled.** From related
game states with the same number of answered challenges, each call of the oracle over `M'` is
coupled with the call over `M` along the same relation, with the answers of `M` encoded. -/
theorem smMulti_sim_step (h : M'.Sim M ρ encP encC encL encI) (ΔFS ΔPCS t n : ℕ)
    (mode : ℕ → Bool) (x' : SMSchemeSt St' Pub' × ℕ) (x : SMSchemeSt St Pub × ℕ)
    (hx : SMSchemeSt.Related ρ encP x'.1 x.1 ∧ x'.2 = x.2) (q : SMQuery W) :
    ∃ ν : PMF ((SMSchemeAns Pub Ct Leak × (SMSchemeSt St Pub × ℕ)) × (SMSchemeSt St' Pub' × ℕ)),
      ν.map Prod.fst = smMultiOracle M ΔFS ΔPCS t n mode x q ∧
      ν.map (fun z => (SMSchemeAns.map encP encC encL z.1.1, z.2)) =
        smMultiOracle M' ΔFS ΔPCS t n mode x' q ∧
      ∀ z ∈ ν.support, SMSchemeSt.Related ρ encP z.2.1 z.1.2.1 ∧ z.2.2 = z.1.2.2 := by
  rcases x' with ⟨s', c⟩
  rcases x with ⟨s, c₀⟩
  obtain ⟨hs, hc⟩ := hx
  dsimp only at hs hc
  subst c₀
  have hpair : SMSchemeSt.Related ρ encP (s', c).1 (s, c).1 ∧ (s', c).2 = (s, c).2 := ⟨hs, rfl⟩
  have lift : ∀ q : SMQuery W, ∃ ν : PMF ((SMSchemeAns Pub Ct Leak × (SMSchemeSt St Pub × ℕ)) ×
      (SMSchemeSt St' Pub' × ℕ)),
      ν.map Prod.fst = (smSchemeOracle M ΔFS ΔPCS t false s q).map (fun y => (y.1, (y.2, c))) ∧
      ν.map (fun z => (SMSchemeAns.map encP encC encL z.1.1, z.2)) =
        (smSchemeOracle M' ΔFS ΔPCS t false s' q).map (fun y => (y.1, (y.2, c))) ∧
      ∀ z ∈ ν.support, SMSchemeSt.Related ρ encP z.2.1 z.1.2.1 ∧ z.2.2 = z.1.2.2 := by
    intro q
    obtain ⟨ν, h1, h2, h3⟩ := smScheme_sim_step h ΔFS ΔPCS t false s' s hs q
    refine ⟨ν.map fun z => ((z.1.1, (z.1.2, c)), (z.2, c)), ?_, ?_, ?_⟩
    · rw [← h1, PMF.map_comp, PMF.map_comp]
      rfl
    · rw [← h2, PMF.map_comp, PMF.map_comp]
      rfl
    · intro z hz
      rw [PMF.support_map] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact ⟨h3 w hw, rfl⟩
  cases q with
  | ratchet p => exact lift _
  | recv p => exact lift _
  | send p m => exact lift _
  | corrupt p => exact lift _
  | chall p m =>
    simp only [smMultiOracle, hs.t]
    by_cases hcnd : c < n ∧ ckaSender (s.ck.t p) = p ∧ s.ck.t p = t
    · simp only [eq_true hcnd, ↓reduceIte]
      have hr := h.send _ _ m (hs.st p)
      cases h1 : M'.send (s'.ck.st p) m <;> cases h2 : M.send (s.ck.st p) m <;>
        rw [h1, h2] at hr <;> cases hr
      · exact coupling_pure _
          (fun (x' : SMSchemeSt St' Pub' × ℕ) (x : SMSchemeSt St Pub × ℕ) =>
            SMSchemeSt.Related ρ encP x'.1 x.1 ∧ x'.2 = x.2) _ _ _ hpair
      · rename_i y' y hy
        dsimp only
        have hμ : (if mode c then M'.idealCt else PMF.pure y'.2) =
            (if mode c then M.idealCt else PMF.pure y.2).map encC := by
          split_ifs
          · exact h.idealCt
          · rw [hy.2, PMF.pure_map]
        rw [hμ, PMF.bind_map, hs.done]
        exact coupling_bind (SMSchemeAns.map encP encC encL)
          (fun (x' : SMSchemeSt St' Pub' × ℕ) (x : SMSchemeSt St Pub × ℕ) =>
            SMSchemeSt.Related ρ encP x'.1 x.1 ∧ x'.2 = x.2) _
          (fun d => (SMSchemeAns.ct d, (s.upd p y.1 s.done, c + 1)))
          (fun _ => (s'.upd p y'.1 s.done, c + 1)) fun _ => ⟨hs.upd p hy.1 _, rfl⟩
    · simp only [eq_false hcnd, ↓reduceIte]
      exact coupling_pure _
        (fun (x' : SMSchemeSt St' Pub' × ℕ) (x : SMSchemeSt St Pub × ℕ) =>
          SMSchemeSt.Related ρ encP x'.1 x.1 ∧ x'.2 = x.2) _ _ _ hpair

/-- **Session views transfer along a simulation.** If `M'` simulates `M` and the keyed
initialisation `ini'` is the encoding of `ini`, the session view over `M'` under the schedule
`Sch` is the session view over `M` under `Sch` with the public values, ciphertexts and corruption
answers encoded. -/
theorem smSessView_sim (h : M'.Sim M ρ encP encC encL encI)
    (ini' : K → SPComp (Pub' × St' × St')) (ini : K → SPComp (Pub × St × St))
    (hini : ∀ k, ini' k =
      SPComp.bind (ini k) fun i => SPComp.pure (encP i.1, encI i.2.1, encI i.2.2))
    (Sch : Pub' → OracleAdv (SMQuery W) (SMSchemeAns Pub' Ct' Leak') V) (t n ΔFS ΔPCS : ℕ)
    (mode : ℕ → Bool) (k : K) :
    smSessView M' ini' Sch t n ΔFS ΔPCS mode k =
      smSessView M ini (fun T => (Sch (encP T)).mapQueryAnswer id
        (SMSchemeAns.map encP encC encL)) t n ΔFS ΔPCS mode k := by
  simp only [smSessView, hini, SPComp.bind_assoc, SPComp.pure_bind]
  refine congrArg _ (funext fun i => congrArg _ ?_)
  exact OracleAdv.run_map_fst_mapQueryAnswer_of_coupling _ _ _
    (fun x' x => SMSchemeSt.Related ρ encP x'.1 x.1 ∧ x'.2 = x.2)
    (fun x' x d hx => smMulti_sim_step h ΔFS ΔPCS t n mode x' x hx d) _ _ _
    ⟨SMSchemeSt.related_init h.init_rel i, rfl⟩

end SessView

/-! ## The Signal stack with the signed prekey over the extracted ratchet -/

section Pair

open CatCrypt.Crypto.AKE.X3DHSquarePrekey CatCrypt.Crypto.Messaging.SignalStackSMPrekey

variable (Dp : Type) [Inhabited Dp] [Doubleratchet.DoubleRatchetDeps Dp]
  {S RK Sa Wd Ct Sk Ad G V : Type} [Field S] [Fintype S] [Inhabited S] [SampleableType G]
  [CG : CyclicGroup G] [Fintype RK] [Nonempty RK] [Inhabited RK]
  [DecidableEq RK] [Fintype Sa] [Nonempty Sa] [SampleableType Wd] [Fintype Sk] [Nonempty Sk]
  [Inhabited Sk] [SampleableType Ct]

/-- **The prekey secret of X3DH and the secret key of the ratchet are one value** at the
encodings: for every X3DH secret `s`, the ratchet secret key `ι s` has the encoding `encX s` of
`s` and the public value `GX.pub s` of `s`. It is a fact about the encodings of the two
extractions. -/
structure SpkCompat (GX : DHGroup S G) (ι : S → Sk) (encX : S → Array Int)
    (encSk : Sk → Array Int) (decE : Sk → CG.Exp) : Prop where
  /-- The encodings of the two secrets agree. -/
  enc : ∀ s, encSk (ι s) = encX s
  /-- The public values of the two secrets agree. -/
  pub : ∀ s, CG.pow (decE (ι s)) = GX.pub s

/-- The schedule `Sch` against the gated extracted scheme as a schedule against the gated ACD
construction with headers: the public value and the answers encoded by `encG`, `encC` and
`drEncLeak` under `some`. -/
def drSchPair (encR : RK → Array Int) (encG : G → Array Int) (encSk : Sk → Array Int)
    (decE : Sk → CG.Exp) (encS : Sa → Array Int) (encC : Ct → Array Int)
    (Sch : Array Int →
      OracleAdv (SMQuery Wd) (SMSchemeAns (Array Int) (Array Int) (Option DrLeak)) V)
    (T : G) :
    OracleAdv (SMQuery Wd) (SMSchemeAns G Ct (Option (SMHdrSt (G × Sk) RK Sa G))) V :=
  (Sch (encG T)).mapQueryAnswer id
    (SMSchemeAns.map encG encC (Option.map (drEncLeak encR encG encSk decE encS)))

/-- **The bound of the Signal stack with the signed prekey over the extracted ratchet**: the
bound `fsmBoundPair` of `signal_stack_realizes_FSM_acdHdr_prekey` at the schedule
`drSchPair … Sch` and the associated data `drHdrAD adOf`. It is the gap Diffie–Hellman bound of
the X3DH square with the datum at the environment reduced through `smPreViewHdr`, and per key of
the run the expectation over the chosen datum `x₀` of `smPairBoundAD` at `ι x₀` (PRF-PRNG,
FS-AEAD and DDH advantages of explicit reductions and `8 c.δ`) at the header wrappers of the
hybrid adversaries, and the probability that a key is read twice. -/
noncomputable def signalExtractedBoundPair (GX : DHGroup S G) (P : Finset PartyId)
    (decE : Sk → CG.Exp) (c : SamplerCert CG.Exp) (ι : S → Sk)
    (R : PRGDef (RK × G) (RK × Sa)) (F : PRGDef Sa (Wd × Sa))
    (D : AEADDef Wd Ct (Ad × ((G × ℕ) × ℕ))) (adOf : Wd → Ad)
    (encR : RK → Array Int) (encG : G → Array Int) (encSk : Sk → Array Int)
    (encS : Sa → Array Int) (encC : Ct → Array Int)
    (Sch : Array Int →
      OracleAdv (SMQuery Wd) (SMSchemeAns (Array Int) (Array Int) (Option DrLeak)) V)
    (t n ΔFS ΔPCS : ℕ) (ζ : Type) (Z : Env (Strat ζ (OEv G) (HOut V ⊕ ROut S G RK)) ζ) :
    ℝ≥0∞ :=
  fsmBoundPair GX P
    (fun x₀ => (acdHdrSM ((dhCKAOf G decE).atInit (dhPairInit decE (ι x₀))) R F D
      (drHdrAD adOf)).gateB)
    (fun k x₀ => gateIni (acdHdrIni (Sa := Sa)
      ((dhCKAOf G decE).atInit (dhPairInit decE (ι x₀)))) k)
    (fun x₀ A => smPairBoundAD decE c R F D ΔFS ΔPCS (ι x₀) (A.gateB.toHdr (drHdrAD adOf)))
    (drSchPair encR encG encSk decE encS encC Sch) t n ΔFS ΔPCS
    (smPreViewHdr decE id R F D (drHdrAD adOf) (drSchPair encR encG encSk decE encS encC Sch)
      t n ΔFS ΔPCS)
    (smPreViewHdr_noFail decE id R F D (drHdrAD adOf)
      (drSchPair encR encG encSk decE encS encC Sch) t n ΔFS ΔPCS) ζ Z

variable {R : PRGDef (RK × G) (RK × Sa)} {F : PRGDef Sa (Wd × Sa)}
  {D : AEADDef Wd Ct (Ad × ((G × ℕ) × ℕ))} {ptLen : Int} {encR : RK → Array Int}
  {encG : G → Array Int} {encSk : Sk → Array Int} {decE : Sk → CG.Exp} {encS : Sa → Array Int}
  {encW : Wd → Array Int} {encPt : Wd → Array Int} {encC : Ct → Array Int}
  {encAD : Ad → Array Int} {adOf : Wd → Ad}

omit [SampleableType G] [Fintype RK] [Nonempty RK] [Inhabited RK]
  [DecidableEq RK] [Fintype Sa] [Nonempty Sa] in
/-- The keyed initialisation of the gated extracted ratchet at the pair of `y` is the encoding
of that of the gated ACD construction with headers. -/
theorem gateIni_drExtractedIniPair (y : Sk) (k : RK) :
    gateIni (fun rk => drExtractedIniPair encR encG encSk decE rk y) k =
      SPComp.bind (gateIni (acdHdrIni (Sa := Sa) ((dhCKAOf G decE).atInit (dhPairInit decE y)))
          k)
        fun i => SPComp.pure (encG i.1, (drEncInit encR encG encSk decE encS i.2.1.1, i.2.1.2),
          (drEncInit encR encG encSk decE encS i.2.2.1, i.2.2.2)) := by
  simp only [gateIni, acdHdrIni, CKADef.atInit, drExtractedIniPair, SPComp.pure_bind]
  rfl

omit [Field S] [Fintype S] [Inhabited S] [SampleableType G] [Inhabited RK] [DecidableEq RK]
  [Fintype Sa] [Nonempty Sa] in
/-- The real views of the extracted stack with the datum are those of the gated ACD
construction with headers under the encoded schedule. -/
theorem smRealViewK_drExtractedPair
    (hD : DrHom Dp G R F D ptLen encR encG encSk decE encS encW encPt encC encAD (drEncH encG))
    (ι : S → Sk)
    (Sch : Array Int →
      OracleAdv (SMQuery Wd) (SMSchemeAns (Array Int) (Array Int) (Option DrLeak)) V)
    (t n ΔFS ΔPCS : ℕ) (p : RK × S) :
    smRealViewK (fun s => (drExtractedSMPair Dp RK ptLen encR encG encSk decE encPt encC encAD
          adOf (ι s)).gateB)
        (fun k s => gateIni (fun rk => drExtractedIniPair encR encG encSk decE rk (ι s)) k)
        Sch t n ΔFS ΔPCS p =
      smRealViewK
        (fun x₀ => (acdHdrSM ((dhCKAOf G decE).atInit (dhPairInit decE (ι x₀))) R F D
          (drHdrAD adOf)).gateB)
        (fun k x₀ => gateIni (acdHdrIni (Sa := Sa)
          ((dhCKAOf G decE).atInit (dhPairInit decE (ι x₀)))) k)
        (drSchPair encR encG encSk decE encS encC Sch) t n ΔFS ΔPCS p :=
  smSessView_sim (drExtracted_sim_pair Dp hD (ι p.2)) _ _
    (fun k => gateIni_drExtractedIniPair _ k) Sch t n ΔFS ΔPCS _ p.1

omit [Field S] [Fintype S] [Inhabited S] [SampleableType G] [Inhabited RK] [DecidableEq RK]
  [Fintype Sa] [Nonempty Sa] in
/-- The ideal views of the extracted stack with the datum are those of the gated ACD
construction with headers under the encoded schedule. -/
theorem smIdealViewK_drExtractedPair
    (hD : DrHom Dp G R F D ptLen encR encG encSk decE encS encW encPt encC encAD (drEncH encG))
    (ι : S → Sk)
    (Sch : Array Int →
      OracleAdv (SMQuery Wd) (SMSchemeAns (Array Int) (Array Int) (Option DrLeak)) V)
    (t n ΔFS ΔPCS : ℕ) (x₀ : S) :
    smIdealViewK (fun s => (drExtractedSMPair Dp RK ptLen encR encG encSk decE encPt encC encAD
          adOf (ι s)).gateB)
        (fun k s => gateIni (fun rk => drExtractedIniPair encR encG encSk decE rk (ι s)) k)
        Sch t n ΔFS ΔPCS x₀ =
      smIdealViewK
        (fun x₀ => (acdHdrSM ((dhCKAOf G decE).atInit (dhPairInit decE (ι x₀))) R F D
          (drHdrAD adOf)).gateB)
        (fun k x₀ => gateIni (acdHdrIni (Sa := Sa)
          ((dhCKAOf G decE).atInit (dhPairInit decE (ι x₀)))) k)
        (drSchPair encR encG encSk decE encS encC Sch) t n ΔFS ΔPCS x₀ := by
  simp only [smIdealViewK, smIdealView]
  exact congrArg _ (funext fun k => smSessView_sim (drExtracted_sim_pair Dp hD (ι x₀)) _ _
    (fun k => gateIni_drExtractedIniPair _ k) Sch t n ΔFS ΔPCS _ k)

/-- **The Signal stack with the signed prekey over the extracted ratchet and the model X3DH, the
extracted X3DH, and the states of both parties.** Under the hom records `X3dhSquareHom` of
`x3dh-hax` and `DrHom` of `doubleratchet-hax` (at the header encoding `drEncH encG`) at shared
encodings `encG` of group elements and `encR` of session and root keys, with `decG`, `decR` left
inverses of `encG`, `encR` (which excludes X25519, whose u-coordinate identifies `T` and `-T`),
the compatibility `SpkCompat` of the X3DH prekey secret and the ratchet secret key along `ι`, a
sampler certificate `c` of the exponents, and `2 ≤ ΔFS`, `2 ≤ ΔPCS`, the conjunction of four
statements, of which the first has a bound:

1. *The stack with the prekey over the gated extracted ratchet* (genuine UC). The ideal
   functionality is `F_SMK` at the schemes `(drExtractedSMPair … (ι x₀)).gateB` keyed through
   `drExtractedIniPair`: the functionality over `F_AKEK` with the prekey datum whose completed
   sessions have the ideal view of the schedule `Sch` over the gated extracted scheme at the
   signed-prekey pair of their datum. The real world is X3DH with the datum `x3dhRealPair GX`
   followed by the ratchet layer over the gated extracted scheme, whose initiator starts with the
   responder's signed prekey as remote public value and whose responder starts with the signed
   prekey pair. The simulator is `chanSim (simProtPair GX) x3dhFwd`. The bound is
   `signalExtractedBoundPair`, the bound of `signal_stack_realizes_FSM_acdHdr_prekey` at the
   encoded schedule. It contains the probability that a key is read twice, which is `1` when
   both partners of an unexposed session always read their key.
2. *The extracted X3DH.* The system of `extGame` is `x3dhRealOfK (fixedKDF H) (x3dhAlg GX)`
   (`extSys_eq`).
3. *The initiator's session.* The session of `Uninitialized_establish_alice` on the key of
   `X3dh.initiate` is at step `0` with the state of the epoch opening `ratchet` from
   `drInitState` at the encoded X3DH key and the encoded signed prekey, as in
   `signal_extracted_e2e`.
4. *The responder's state.* The state of `ratchet_init_bob` on the key of `X3dh.respond` with
   the signed-prekey secret `s` and the key pair `(encX s, encG (GX.pub s))`, with its remote
   public value set to `encG (GX.pub s)`, is the responder state `drPairBob` of
   `drExtractedIniPair` at the root key `H (bobInp …)` and `y = ι s`. -/
theorem signal_extracted_e2e_prekey [X3dh.X3dhDeps] {Gh : Type} [Inhabited Gh]
    [Doubleratchet.DoubleRatchetGhost Gh] (GX : DHGroup S G) (P : Finset PartyId)
    {encCtx : SessionId × PartyId × PartyId → Array Int} {encX : S → Array Int}
    {H : Inp G → RK} {decG : Array Int → G} {decR : Array Int → RK}
    (hX : X3dhSquareHom GX encCtx encX encG encR H)
    (hD : DrHom Dp G R F D ptLen encR encG encSk decE encS encW encPt encC encAD (drEncH encG))
    (hG : ∀ Y, decG (encG Y) = Y) (hR : ∀ k, decR (encR k) = k)
    (ι : S → Sk) (hι : SpkCompat GX ι encX encSk decE) (c : SamplerCert CG.Exp)
    (hμ : c.μ = (SDistr.uniform Sk).bind fun x => SDistr.pure (decE x))
    (hν : c.ν = SDistr.uniform CG.Exp)
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 2 ≤ ΔPCS)
    (Sch : Array Int →
      OracleAdv (SMQuery Wd) (SMSchemeAns (Array Int) (Array Int) (Option DrLeak)) V)
    (t n : ℕ) :
    RealizesSim ((x3dhRealPair (K := RK) GX).seq (smCorruptLayerK
        (fun s => (drExtractedSMPair Dp RK ptLen encR encG encSk decE encPt encC encAD adOf
          (ι s)).gateB)
        (fun k s => gateIni (fun rk => drExtractedIniPair encR encG encSk decE rk (ι s)) k)
        Sch t n ΔFS ΔPCS))
      (F_SMK (fun s => (drExtractedSMPair Dp RK ptLen encR encG encSk decE encPt encC encAD adOf
          (ι s)).gateB)
        (fun k s => gateIni (fun rk => drExtractedIniPair encR encG encSk decE rk (ι s)) k)
        Sch t n ΔFS ΔPCS)
      (chanSim (simProtPair (K := RK) GX) x3dhFwd)
      (signalExtractedBoundPair GX P decE c ι R F D adOf encR encG encSk encS encC Sch t n ΔFS
        ΔPCS) ∧
    (OProt.oracle (Q := HEv ⊕ RAEv G) (A := HOut RK ⊕ ROut S G RK)).sys
        (extGame encCtx encX encG decG decR) = x3dhRealOfK (fixedKDF H) (x3dhAlg GX) ∧
    (∀ (u : Doubleratchet.Uninitialized_T) (g : Gh) (sid : SessionId) (a b : PartyId)
      (ik ek : S) (IKB SPKB OPKB : G) (sig : Array Int) (y : Sk) (sk₀ pk₀ : Array Int),
      (X3dh.initiate (encCtx (sid, a, b)) (encX ik) (encX ek)
          (encG IKB, encG SPKB, encG OPKB, sig) true).map
          (fun o => (Doubleratchet.Uninitialized_establish_alice (D := Dp) u g o.1 (encG SPKB)
            (encSk y) (encG (CG.pow (decE y)))).1) =
        some (Doubleratchet.Session
          ((drExtractedSM Dp RK ptLen encR encG encSk decE encPt encC encAD adOf).ratchet
            (drInitState (encR (H (aliceInp GX sid a b ik ek IKB SPKB OPKB))) sk₀ pk₀
              (encG SPKB)) y).1 0)) ∧
    ∀ (sid : SessionId) (a b : PartyId) (ik s opk : S) (IKA E : G) (opk_id : Array Int),
      (X3dh.respond (encCtx (sid, a, b)) (encX ik) (encX s) (encX opk)
          (encG IKA, encG E, opk_id) true).map
          (fun k => let x := Doubleratchet.ratchet_init_bob k (encX s) (encG (GX.pub s))
            (x.1, x.2.1, some (encG (GX.pub s)), x.2.2.2)) =
        some (drPairBob encR encG encSk decE (H (bobInp GX sid a b IKA E ik s opk)) (ι s)) := by
  refine ⟨?_, extSys_eq hX hG hR, ?_, ?_⟩
  · have hL : smCorruptLayerK (R := ROut S G RK)
        (fun s => (drExtractedSMPair Dp RK ptLen encR encG encSk decE encPt encC encAD adOf
          (ι s)).gateB)
        (fun k s => gateIni (fun rk => drExtractedIniPair encR encG encSk decE rk (ι s)) k)
        Sch t n ΔFS ΔPCS =
        smCorruptLayerK
          (fun x₀ => (acdHdrSM ((dhCKAOf G decE).atInit (dhPairInit decE (ι x₀))) R F D
            (drHdrAD adOf)).gateB)
          (fun k x₀ => gateIni (acdHdrIni (Sa := Sa)
            ((dhCKAOf G decE).atInit (dhPairInit decE (ι x₀)))) k)
          (drSchPair encR encG encSk decE encS encC Sch) t n ΔFS ΔPCS := by
      simp only [smCorruptLayerK]
      exact congrArg _ (funext fun p => smRealViewK_drExtractedPair Dp hD ι Sch t n ΔFS ΔPCS p)
    have hF : F_SMK
        (fun s => (drExtractedSMPair Dp RK ptLen encR encG encSk decE encPt encC encAD adOf
          (ι s)).gateB)
        (fun k s => gateIni (fun rk => drExtractedIniPair encR encG encSk decE rk (ι s)) k)
        Sch t n ΔFS ΔPCS =
        F_SMK
          (fun x₀ => (acdHdrSM ((dhCKAOf G decE).atInit (dhPairInit decE (ι x₀))) R F D
            (drHdrAD adOf)).gateB)
          (fun k x₀ => gateIni (acdHdrIni (Sa := Sa)
            ((dhCKAOf G decE).atInit (dhPairInit decE (ι x₀)))) k)
          (drSchPair encR encG encSk decE encS encC Sch) t n ΔFS ΔPCS := by
      simp only [F_SMK]
      rw [funext fun p => smRealViewK_drExtractedPair (adOf := adOf) Dp hD ι Sch t n ΔFS ΔPCS p,
        funext fun x₀ => smIdealViewK_drExtractedPair (adOf := adOf) Dp hD ι Sch t n ΔFS ΔPCS
          x₀]
    have key := signal_stack_realizes_FSM_acdHdr_prekey (t := t) (n := n) (RK := RK) (Sa := Sa)
      (V := V) GX P decE c hμ hν ι id (fun x => hι.pub x) R F D (drHdrAD adOf)
      (drSchPair encR encG encSk decE encS encC Sch) hFS hPCS
    rw [hL, hF]
    exact key
  · intro u g sid a b ik ek IKB SPKB OPKB sig y sk₀ pk₀
    rw [initiate_square_eq_some hX, Option.map_some,
      signal_session_extracted_drOpen u g _ _ _ _ _ _ sk₀ pk₀ _, initiate_square_enc hX]
    rfl
  · intro sid a b ik s opk IKA E opk_id
    rw [respond_square_eq_some hX, Option.map_some, respond_square_enc hX]
    simp only [drPairBob, drInitState, Doubleratchet.ratchet_init_bob, hι.enc, hι.pub]
    rfl

end Pair

end CatCrypt.Crypto.Signal.EndToEnd
