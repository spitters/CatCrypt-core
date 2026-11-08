/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SignalStackSM
public import CatCryptCore.Crypto.AKE.X3DH.ExtractedGame
public import CatCryptCore.Crypto.Signal.SessionExtracted

/-!
# Signal over the extracted code, end to end

The end-to-end statement `signal_extracted_e2e` for the Signal stack over the haxpipeT
extractions of `x3dh-hax` and `doubleratchet-hax`, assembled from the theorems of the scheme
records by instantiation. Its hypotheses are the hom records of the two extractions at shared
encodings of group elements (`encG`) and of session and root keys (`encR`), `X3dhSquareHom` and
`DrHom`, and the left-inverse facts of the encodings `encG` and `encR` that the game over the
extracted X3DH functions decodes with. It is the conjunction of three statements.

* **The stack over the extracted ratchet.** The stack of `SignalStackSM`, X3DH followed by the
  ratchet layer over the extracted double ratchet `drExtractedSM` keyed by the session key of
  X3DH through `drExtractedIni`, realizes the secure-messaging functionality `F_SM` behind the
  X3DH simulator `scSim GX`. The bound `signalExtractedBound` is the gap Diffie–Hellman bound of
  X3DH, the CKA corruption, PRF-PRNG and FS-AEAD advantages of the reductions of `SMCorrupt` at
  the reductions `smHopRed` of the stack with the answers encoded, and the probabilities that a
  key is read twice (`signal_stack_realizes_FSM` at `drExtractedSM`, then
  `drExtracted_corruptAdvantage_le`). The key derivation of X3DH in the stack is the lazily
  sampled random function `lazyKDF`.
* **The extracted X3DH.** The system of the game over the extracted X3DH functions is the real
  system `x3dhRealOfK (fixedKDF H) (x3dhAlg GX)` of the square model with the key derivation the
  fixed function `H` (`extSys_eq`).
* **The session link.** The session that the extracted initiator computes, `X3dh.initiate` and
  then `Uninitialized_establish` on its key, is the epoch opening `ratchet` of the extracted
  scheme from the initial session `drInitSession` whose root key is the encoding of the X3DH key
  `H (aliceInp …)` of the square model and whose remote public value is the encoded signed
  prekey (`initiate_square_enc`, `signal_session_extracted_drOpen`). The keyed initialisation
  `drExtractedIni k` of the stack starts both parties in `drInitSession` at the root key
  `encR k`.

## Main definitions

* `drExtractedIni` — the keyed initialisation of the extracted double ratchet.
* `signalExtractedBound` — the bound of the Signal stack over the extracted ratchet.

## Main results

* `drExtractedSM_init_eq` — the initialisation of `drExtractedSM` is `drExtractedIni` at a
  uniform root key.
* `signal_stack_realizes_FSM_extracted` — the Signal stack over the extracted ratchet realizes
  `F_SM`.
* `signal_extracted_e2e` — the end-to-end statement.
-/

@[expose] public section

set_option autoImplicit false

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

variable [Doubleratchet.DoubleratchetDeps]

/-! ## The keyed initialisation of the extracted ratchet -/

section Ini

variable {RK Wd Ct Sk : Type} {G : Type} [CG : CyclicGroup G] [Fintype RK] [Nonempty RK]
  [Fintype Sk] [Nonempty Sk] [SampleableType Ct]

/-- **The keyed initialisation of the extracted double ratchet** at the root key `rk`: a uniform
secret key `x₀` of `Sk`, and both parties in the session `drInitSession` with the encoded root
key, no chain keys, the key pair `(x₀, g ^ decE x₀)` and the remote public value
`g ^ decE x₀`. -/
noncomputable def drExtractedIni (encR : RK → Array Int) (encG : G → Array Int)
    (encSk : Sk → Array Int) (decE : Sk → CG.Exp) (rk : RK) :
    SPComp (Array Int × Doubleratchet.Session_T × Doubleratchet.Session_T) :=
  SPComp.bind (SPComp.sample Sk) fun x =>
    SPComp.pure (encG (CG.pow (decE x)),
      drInitSession (encR rk) (encSk x) (encG (CG.pow (decE x))) (encG (CG.pow (decE x))),
      drInitSession (encR rk) (encSk x) (encG (CG.pow (decE x))) (encG (CG.pow (decE x))))

omit [Doubleratchet.DoubleratchetDeps] [Fintype RK] [Nonempty RK] in
/-- The keyed initialisation neither touches the heap nor fails. -/
theorem drExtractedIni_pureNF (encR : RK → Array Int) (encG : G → Array Int)
    (encSk : Sk → Array Int) (decE : Sk → CG.Exp) (rk : RK) :
    PureNF (drExtractedIni encR encG encSk decE rk) :=
  (pureNF_sample Sk).bind fun _ => pureNF_pure _

/-- The initialisation of `drExtractedSM` is its keyed initialisation at a uniform root key. -/
theorem drExtractedSM_init_eq (ptLen : Int) (encR : RK → Array Int) (encG : G → Array Int)
    (encSk : Sk → Array Int) (decE : Sk → CG.Exp) (encW : Wd → Array Int)
    (encC : Ct → Array Int) :
    (drExtractedSM RK ptLen encR encG encSk decE encW encC).init =
      SPComp.bind (SPComp.sample RK) (drExtractedIni encR encG encSk decE) := by
  simp only [drExtractedSM]
  exact SPComp.isPure_bind_comm_left _ _ _ (pureNF_sample Sk).1

end Ini

/-! ## The Signal stack over the extracted ratchet -/

section Stack

variable {S RK Sa Wd Ct Sk G V : Type} [Field S] [Fintype S] [Nonempty S] [SampleableType G]
  [CG : CyclicGroup G] [Fintype RK] [Nonempty RK] [Inhabited RK] [DecidableEq RK]
  [Fintype Sa] [Nonempty Sa] [SampleableType Wd] [Fintype Sk] [Nonempty Sk] [SampleableType Ct]

/-- **The bound of the Signal stack over the extracted ratchet** at an environment `Z`: the gap
Diffie–Hellman bound of X3DH at the environment reduced through the ratchet layer, and, at the
environment `Z'` reduced through the simulator, over the keys `i` below the number of
activations of `Z'`, the sum over the `n` challenges `j` of the CKA corruption advantages of
`smcCKARed`, the PRF-PRNG advantages of the root KDF `R` at `smcRootRed` and the FS-AEAD
advantage of `F`, `D` at `smcFSRed`, at the reduction `smHopRed i j Z'` with the answers
encoded by `encG`, `encC` and `drEncLeak`, and the probability that the key `i` is read
twice. -/
noncomputable def signalExtractedBound (GX : DHGroup S G) (P : Finset PartyId)
    (R : PRGDef (RK × G) (RK × Sa)) (F : PRGDef Sa (Wd × Sa)) (D : AEADDef Wd Ct) (ptLen : Int)
    (encR : RK → Array Int) (encG : G → Array Int) (encSk : Sk → Array Int) (decE : Sk → CG.Exp)
    (encS : Sa → Array Int) (encW : Wd → Array Int) (encC : Ct → Array Int)
    (Sch : Array Int →
      OracleAdv (SMQuery Wd) (SMSchemeAns (Array Int) (Array Int) DrLeak) V)
    (t n ΔFS ΔPCS : ℕ) (ζ : Type) (Z : Env (Strat ζ (OEv G) (HOut V ⊕ ROut S G RK)) ζ) :
    ℝ≥0∞ :=
  gdhBound GX P ((OProt.oracle (Q := OEv G) (A := OOut S G RK)).reduction
      ((Hybrid.seqCtxR (E := OEv G)
        (smCorruptLayer (drExtractedSM RK ptLen encR encG encSk decE encW encC)
          (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS)
        (keyLayer_noFail fun k => (smSessView_pureNF
          (drExtractedIni_pureNF encR encG encSk decE) Sch t n ΔFS ΔPCS _ k).2)).reduceEnv Z)) +
    ∑ i ∈ Finset.range ((simSC (V := V) GX).reduceEnv (.inr .idle) Z).input.rounds,
      ((∑ j ∈ Finset.range n,
          (∑ b : Bool, CKA_Corrupt_Advantage (dhCKAOf G decE) ΔFS ΔPCS
              (smcCKARed R F D b ((smHopRed (drExtractedSM RK ptLen encR encG encSk decE encW
                encC) (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS i j
                ((simSC GX).reduceEnv (.inr .idle) Z)).comap encG encC
                (drEncLeak encR encG encSk decE encS)).toSM) +
            ∑ b : Bool, PRFPRNG_Advantage R (smcRootRed (dhCKAOf G decE) R F D ΔFS ΔPCS b
              (dhInitPOf G decE) ((smHopRed (drExtractedSM RK ptLen encR encG encSk decE encW
                encC) (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS i j
                ((simSC GX).reduceEnv (.inr .idle) Z)).comap encG encC
                (drEncLeak encR encG encSk decE encS)).toSM) +
            FSAEAD_Corrupt_Advantage F D (smcFSRed (dhCKAOf G decE) R F D ΔFS ΔPCS
              (dhInitPOf G decE) ((smHopRed (drExtractedSM RK ptLen encR encG encSk decE encW
                encC) (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS i j
                ((simSC GX).reduceEnv (.inr .idle) Z)).comap encG encC
                (drEncLeak encR encG encSk decE encS)).toSM))) +
        prBad (hyb (smRealView (drExtractedSM RK ptLen encR encG encSk decE encW encC)
            (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS)
          (smIdealView (drExtractedSM RK ptLen encR encG encSk decE encW encC)
            (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS) i)
          (reuse i) ((simSC GX).reduceEnv (.inr .idle) Z))

variable {R : PRGDef (RK × G) (RK × Sa)} {F : PRGDef Sa (Wd × Sa)} {D : AEADDef Wd Ct}
  {ptLen : Int} {encR : RK → Array Int} {encG : G → Array Int} {encSk : Sk → Array Int}
  {decE : Sk → CG.Exp} {encS : Sa → Array Int} {encW : Wd → Array Int} {encC : Ct → Array Int}

omit [Nonempty S] in
/-- **The Signal stack over the extracted double ratchet realizes secure messaging with
corruption** (genuine UC).

*Ideal functionality.* `F_SM (drExtractedSM …) (drExtractedIni …) Sch t n ΔFS ΔPCS`: the
multi-session secure channel of `F_AKE` whose completed sessions have the ideal view of the
schedule `Sch` over the extracted scheme (ideal ciphertexts for the challenge messages of the
honest epoch `t`, the session states leaked in the corruption windows of `ΔFS` and `ΔPCS` under
a fresh root key), whose exposed sessions have the real view under the adversary key, and whose
adversary port is that of `F_AKE`.

*Real world.* The real X3DH protocol `x3dhReal GX` with the key derivation a lazily sampled
random function, followed by the ratchet layer over the extracted scheme `drExtractedSM`, which
starts both parties at `drInitSession` with the session key of every `getKey` answer as root key
and runs the schedule against the oracles of the extracted session functions.

*Simulator.* `scSim GX`, the X3DH simulator over `F_SC`.

*Bound.* Under `DrHom`, with `2 ≤ ΔFS` and `1 ≤ ΔPCS`, for every finite set of parties `P` and
every environment `Z`, the distance is at most `signalExtractedBound`: the gap Diffie–Hellman
bound of X3DH and, over the keys of the run and the challenges `j < n`, the CKA corruption,
PRF-PRNG and FS-AEAD advantages of explicit reductions, and the probability that a key is read
twice. -/
theorem signal_stack_realizes_FSM_extracted (GX : DHGroup S G) (P : Finset PartyId)
    (hD : DrHom G R F D ptLen encR encG encSk decE encS encW encC)
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS)
    (Sch : Array Int →
      OracleAdv (SMQuery Wd) (SMSchemeAns (Array Int) (Array Int) DrLeak) V) (t n : ℕ) :
    RealizesSim ((x3dhReal (K := RK) GX).seq
        (smCorruptLayer (drExtractedSM RK ptLen encR encG encSk decE encW encC)
          (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS))
      (F_SM (drExtractedSM RK ptLen encR encG encSk decE encW encC)
        (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS) (scSim GX)
      (signalExtractedBound GX P R F D ptLen encR encG encSk decE encS encW encC Sch t n ΔFS
        ΔPCS) := by
  intro ζ Z
  refine (signal_stack_realizes_FSM GX P (drExtractedSM RK ptLen encR encG encSk decE encW encC)
    (drExtractedIni encR encG encSk decE) (drExtractedSM_init_eq ptLen encR encG encSk decE encW
      encC) (drExtractedIni_pureNF encR encG encSk decE) Sch t n ΔFS ΔPCS ζ Z).trans ?_
  simp only [fsmBound, signalExtractedBound]
  exact add_le_add le_rfl (Finset.sum_le_sum fun i _ => add_le_add_left
    (Finset.sum_le_sum fun j _ => drExtracted_corruptAdvantage_le hD hFS hPCS _) _)

/-- **Signal over the extracted code, end to end.** Under the hom records `X3dhSquareHom` of
`x3dh-hax` and `DrHom` of `doubleratchet-hax` at shared encodings `encG` of group elements and
`encR` of session and root keys, with `decG`, `decR` left inverses of `encG`, `encR`, and with
`2 ≤ ΔFS` and `1 ≤ ΔPCS`:

1. *The stack over the extracted ratchet* (genuine UC). The ideal functionality is
   `F_SM (drExtractedSM …) (drExtractedIni …) Sch t n ΔFS ΔPCS`, the secure channel of `F_AKE`
   with the ideal views of the schedule `Sch` over the extracted scheme in the corruption windows
   of `ΔFS` and `ΔPCS`; the real world is X3DH over `GX` with the key derivation a lazily
   sampled random function, followed by the ratchet layer over the extracted scheme keyed by the
   X3DH session key; the simulator is `scSim GX`; the bound is `signalExtractedBound`, the gap
   Diffie–Hellman bound of X3DH plus the CKA corruption, PRF-PRNG and FS-AEAD advantages of
   explicit reductions and the probabilities that a key is read twice
   (`signal_stack_realizes_FSM_extracted`).
2. *The extracted X3DH.* The system of the game `extGame` over the extracted X3DH functions is
   the real system `x3dhRealOfK (fixedKDF H) (x3dhAlg GX)` of the square model with the key
   derivation the fixed function `H` (`extSys_eq`).
3. *The session link.* For the initiator `a` of the session `sid` with the peer `b`, the
   encoded secrets `ik`, `ek`, a bundle of the encoded public keys `IKB`, `SPKB`, `OPKB` and the
   new ratchet secret key `y`, the session that `Uninitialized_establish` computes on the key of
   `X3dh.initiate` is the epoch opening `ratchet` at `y` of the extracted scheme from the initial
   session `drInitSession` whose root key is the encoding of the X3DH key
   `H (aliceInp GX sid a b ik ek IKB SPKB OPKB)` of the square model and whose remote public
   value is the encoded signed prekey `encG SPKB`, for any key pair `(sk₀, pk₀)` of the initial
   session. -/
theorem signal_extracted_e2e [X3dh.X3dhDeps] (GX : DHGroup S G) (P : Finset PartyId)
    {encCtx : SessionId × PartyId × PartyId → Array Int} {encX : S → Array Int}
    {H : Inp G → RK} {decG : Array Int → G} {decR : Array Int → RK}
    (hX : X3dhSquareHom GX encCtx encX encG encR H)
    (hD : DrHom G R F D ptLen encR encG encSk decE encS encW encC)
    (hG : ∀ Y, decG (encG Y) = Y) (hR : ∀ k, decR (encR k) = k)
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS)
    (Sch : Array Int →
      OracleAdv (SMQuery Wd) (SMSchemeAns (Array Int) (Array Int) DrLeak) V) (t n : ℕ) :
    RealizesSim ((x3dhReal (K := RK) GX).seq
        (smCorruptLayer (drExtractedSM RK ptLen encR encG encSk decE encW encC)
          (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS))
      (F_SM (drExtractedSM RK ptLen encR encG encSk decE encW encC)
        (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS) (scSim GX)
      (signalExtractedBound GX P R F D ptLen encR encG encSk decE encS encW encC Sch t n ΔFS
        ΔPCS) ∧
    (OProt.oracle (Q := HEv ⊕ RAEv G) (A := HOut RK ⊕ ROut S G RK)).sys
        (extGame H encCtx encX encG decG decR) = x3dhRealOfK (fixedKDF H) (x3dhAlg GX) ∧
    ∀ (u : Doubleratchet.Uninitialized_T) (g : Array Int) (sid : SessionId) (a b : PartyId)
      (ik ek : S) (IKB SPKB OPKB : G) (sig : Array Int) (y : Sk) (sk₀ pk₀ : Array Int),
      (X3dh.initiate (encCtx (sid, a, b)) (encX ik) (encX ek)
          (encG IKB, encG SPKB, encG OPKB, sig) true).map
          (fun o => (Doubleratchet.Uninitialized_establish u g o.1 (encSk y)
            (encG (CG.pow (decE y))) (encG SPKB)).1) =
        some ((drExtractedSM RK ptLen encR encG encSk decE encW encC).ratchet
          (drInitSession (encR (H (aliceInp GX sid a b ik ek IKB SPKB OPKB))) sk₀ pk₀
            (encG SPKB)) y).1 := by
  refine ⟨signal_stack_realizes_FSM_extracted GX P hD hFS hPCS Sch t n, extSys_eq hX hG hR, ?_⟩
  intro u g sid a b ik ek IKB SPKB OPKB sig y sk₀ pk₀
  rw [initiate_square_eq_some hX, Option.map_some,
    signal_session_extracted_drOpen u g _ _ _ _ _ _ sk₀ pk₀ _, initiate_square_enc hX]
  rfl

end Stack

end CatCrypt.Crypto.Signal.EndToEnd
