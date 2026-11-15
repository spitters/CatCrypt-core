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

`signal_extracted_e2e_prekey` is the end-to-end statement with the signed prekey (genuine UC).

* *Ideal functionality.* `F_SMK` at the gated extracted ratchet at the signed-prekey pair
  (`drExtractedSMPair`, `drExtractedIniPair`): the secure channel of `F_AKEK` with the prekey
  datum, whose completed sessions have the ideal view at the pair of their datum.
* *Real world.* X3DH with the datum `x3dhRealPair GX`, followed by the ratchet layer over the
  gated extracted scheme; the initiator starts with the responder's signed prekey as remote
  public value, the responder with the signed-prekey pair.
* *Simulator.* `chanSim (simProtPair GX) x3dhFwd`.
* *Bound.* `signalExtractedBoundPair`, the bound of `signal_stack_realizes_FSM_acd_prekey` at
  the schedule with the answers encoded (`drSchPair`): the session views of the extracted stack
  are those of the gated ACD construction (`smSessView_sim` along `drExtracted_sim_pair`).

Its further conjuncts are `extSys_eq`, the initiator's session as in `signal_extracted_e2e`, and
the responder's session: `ratchet_init_responder` on the key of `X3dh.respond` with the
signed-prekey secret `s` is `drPairBob` at `ι s`, under `SpkCompat`, which states that the X3DH
prekey secret and the ratchet secret key agree at the encodings.

## Main definitions

* `drExtractedIni` — the keyed initialisation of the extracted double ratchet.
* `signalExtractedBound` — the bound of the Signal stack over the extracted ratchet.
* `SpkCompat`, `drSchPair`, `signalExtractedBoundPair` — the compatibility of the prekey
  secrets, the encoded schedule and the bound of the stack with the signed prekey.

## Main results

* `drExtractedSM_init_eq` — the initialisation of `drExtractedSM` is `drExtractedIni` at a
  uniform root key.
* `signal_stack_realizes_FSM_extracted` — the Signal stack over the extracted ratchet realizes
  `F_SM`.
* `signal_extracted_e2e` — the end-to-end statement.
* `smMulti_sim_step`, `smSessView_sim` — session views transfer along a simulation of schemes.
* `signal_extracted_e2e_prekey` — the end-to-end statement with the signed prekey.
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

omit [Fintype RK] [Nonempty RK] in
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
        (extGame encCtx encX encG decG decR) = x3dhRealOfK (fixedKDF H) (x3dhAlg GX) ∧
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

/-! ## Session views along a simulation of schemes -/

section SessView

variable {St St' Pub Pub' Rand W Ct Ct' Leak Leak' K V : Type} [Fintype Rand] [Nonempty Rand]
  {M' : SMScheme St' Pub' Rand W Ct' Leak'} {M : SMScheme St Pub Rand W Ct Leak}
  {ρ : St' → St → Prop} {encP : Pub → Pub'} {encC : Ct → Ct'} {encL : Leak → Leak'}
  {encI : St → St'}

omit [Doubleratchet.DoubleratchetDeps] in
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

omit [Doubleratchet.DoubleratchetDeps] in
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

/-! ## The Signal stack with the signed prekey over the extracted code -/

section Pair

open CatCrypt.Crypto.AKE.X3DHSquarePrekey CatCrypt.Crypto.Messaging.SignalStackSMPrekey

variable {S RK Sa Wd Ct Sk G V : Type} [Field S] [Fintype S] [Inhabited S] [SampleableType G]
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
construction: the public value and the answers encoded by `encG`, `encC` and `drEncLeak`
under `some`. -/
def drSchPair (encR : RK → Array Int) (encG : G → Array Int) (encSk : Sk → Array Int)
    (decE : Sk → CG.Exp) (encS : Sa → Array Int) (encC : Ct → Array Int)
    (Sch : Array Int →
      OracleAdv (SMQuery Wd) (SMSchemeAns (Array Int) (Array Int) (Option DrLeak)) V)
    (T : G) :
    OracleAdv (SMQuery Wd) (SMSchemeAns G Ct (Option (SMPartySt (G × Sk) RK Sa))) V :=
  (Sch (encG T)).mapQueryAnswer id
    (SMSchemeAns.map encG encC (Option.map (drEncLeak encR encG encSk decE encS)))

/-- **The bound of the Signal stack with the signed prekey over the extracted ratchet**: the
bound `fsmBoundPair` of `signal_stack_realizes_FSM_acd_prekey` at the schedule `drSchPair …
Sch`. It is the gap Diffie–Hellman bound of the X3DH square with the datum at the environment
reduced through `smPreView`, and per key of the run the expectation over the chosen datum `x₀`
of `smPairBound` at `ι x₀` (PRF-PRNG, FS-AEAD and DDH advantages of explicit reductions and
`8 c.δ`) at the hybrid adversaries, and the probability that a key is read twice. -/
noncomputable def signalExtractedBoundPair (GX : DHGroup S G) (P : Finset PartyId)
    (decE : Sk → CG.Exp) (c : SamplerCert CG.Exp) (ι : S → Sk)
    (R : PRGDef (RK × G) (RK × Sa)) (F : PRGDef Sa (Wd × Sa)) (D : AEADDef Wd Ct)
    (encR : RK → Array Int) (encG : G → Array Int) (encSk : Sk → Array Int)
    (encS : Sa → Array Int) (encC : Ct → Array Int)
    (Sch : Array Int →
      OracleAdv (SMQuery Wd) (SMSchemeAns (Array Int) (Array Int) (Option DrLeak)) V)
    (t n ΔFS ΔPCS : ℕ) (ζ : Type) (Z : Env (Strat ζ (OEv G) (HOut V ⊕ ROut S G RK)) ζ) :
    ℝ≥0∞ :=
  fsmBoundPair GX P
    (fun x₀ => (acdSM ((dhCKAOf G decE).atInit (dhPairInit decE (ι x₀))) R F D).gateB)
    (fun k x₀ => gateIni (acdIniPair (Sa := Sa) (dhCKAOf G decE) (dhPairInit decE (ι x₀))) k)
    (fun x₀ A => smPairBound decE c R F D ΔFS ΔPCS (ι x₀) A.gateB.toSM)
    (drSchPair encR encG encSk decE encS encC Sch) t n ΔFS ΔPCS
    (smPreView decE id R F D (drSchPair encR encG encSk decE encS encC Sch) t n ΔFS ΔPCS)
    (smPreView_noFail decE id R F D (drSchPair encR encG encSk decE encS encC Sch) t n ΔFS
      ΔPCS) ζ Z

variable {R : PRGDef (RK × G) (RK × Sa)} {F : PRGDef Sa (Wd × Sa)} {D : AEADDef Wd Ct}
  {ptLen : Int} {encR : RK → Array Int} {encG : G → Array Int} {encSk : Sk → Array Int}
  {decE : Sk → CG.Exp} {encS : Sa → Array Int} {encW : Wd → Array Int} {encC : Ct → Array Int}

omit [Field S] [Fintype S] [Inhabited S] [SampleableType G] [Fintype RK] [Nonempty RK]
  [Inhabited RK] [DecidableEq RK] [Fintype Sa] [Nonempty Sa] in
/-- The keyed initialisation of the gated extracted ratchet at the pair of `y` is the encoding
of that of the gated ACD construction. -/
theorem gateIni_drExtractedIniPair (y : Sk) (k : RK) :
    gateIni (fun rk => drExtractedIniPair encR encG encSk decE rk y) k =
      SPComp.bind (gateIni (acdIniPair (Sa := Sa) (dhCKAOf G decE) (dhPairInit decE y)) k)
        fun i => SPComp.pure (encG i.1, (drEncInit encR encG encSk decE encS i.2.1.1, i.2.1.2),
          (drEncInit encR encG encSk decE encS i.2.2.1, i.2.2.2)) := by
  simp only [gateIni, acdIniPair, acdIni, CKADef.atInit, drExtractedIniPair, SPComp.pure_bind]
  rfl

omit [Field S] [Fintype S] [Inhabited S] [SampleableType G] [Inhabited RK] [DecidableEq RK]
  [Fintype Sa] [Nonempty Sa] in
/-- The real views of the extracted stack with the datum are those of the gated ACD
construction under the encoded schedule. -/
theorem smRealViewK_drExtractedPair (hD : DrHom G R F D ptLen encR encG encSk decE encS encW encC)
    (ι : S → Sk)
    (Sch : Array Int →
      OracleAdv (SMQuery Wd) (SMSchemeAns (Array Int) (Array Int) (Option DrLeak)) V)
    (t n ΔFS ΔPCS : ℕ) (p : RK × S) :
    smRealViewK (fun s => (drExtractedSMPair RK ptLen encR encG encSk decE encW encC (ι s)).gateB)
        (fun k s => gateIni (fun rk => drExtractedIniPair encR encG encSk decE rk (ι s)) k)
        Sch t n ΔFS ΔPCS p =
      smRealViewK
        (fun x₀ => (acdSM ((dhCKAOf G decE).atInit (dhPairInit decE (ι x₀))) R F D).gateB)
        (fun k x₀ => gateIni (acdIniPair (Sa := Sa) (dhCKAOf G decE) (dhPairInit decE (ι x₀))) k)
        (drSchPair encR encG encSk decE encS encC Sch) t n ΔFS ΔPCS p :=
  smSessView_sim (drExtracted_sim_pair hD (ι p.2)) _ _ (fun k => gateIni_drExtractedIniPair _ k)
    Sch t n ΔFS ΔPCS _ p.1

omit [Field S] [Fintype S] [Inhabited S] [SampleableType G] [Inhabited RK] [DecidableEq RK]
  [Fintype Sa] [Nonempty Sa] in
/-- The ideal views of the extracted stack with the datum are those of the gated ACD
construction under the encoded schedule. -/
theorem smIdealViewK_drExtractedPair
    (hD : DrHom G R F D ptLen encR encG encSk decE encS encW encC) (ι : S → Sk)
    (Sch : Array Int →
      OracleAdv (SMQuery Wd) (SMSchemeAns (Array Int) (Array Int) (Option DrLeak)) V)
    (t n ΔFS ΔPCS : ℕ) (x₀ : S) :
    smIdealViewK (fun s => (drExtractedSMPair RK ptLen encR encG encSk decE encW encC (ι s)).gateB)
        (fun k s => gateIni (fun rk => drExtractedIniPair encR encG encSk decE rk (ι s)) k)
        Sch t n ΔFS ΔPCS x₀ =
      smIdealViewK
        (fun x₀ => (acdSM ((dhCKAOf G decE).atInit (dhPairInit decE (ι x₀))) R F D).gateB)
        (fun k x₀ => gateIni (acdIniPair (Sa := Sa) (dhCKAOf G decE) (dhPairInit decE (ι x₀))) k)
        (drSchPair encR encG encSk decE encS encC Sch) t n ΔFS ΔPCS x₀ := by
  simp only [smIdealViewK, smIdealView]
  exact congrArg _ (funext fun k => smSessView_sim (drExtracted_sim_pair hD (ι x₀)) _ _
    (fun k => gateIni_drExtractedIniPair _ k) Sch t n ΔFS ΔPCS _ k)

/-- **Signal with the signed prekey over the extracted code, end to end.** Under the hom records
`X3dhSquareHom` of `x3dh-hax` and `DrHom` of `doubleratchet-hax` at shared encodings `encG` of
group elements and `encR` of session and root keys, with `decG`, `decR` left inverses of `encG`,
`encR`, the compatibility `SpkCompat` of the X3DH prekey secret and the ratchet secret key along
`ι`, a sampler certificate `c` of the exponents, and `2 ≤ ΔFS`, `2 ≤ ΔPCS`:

1. *The stack with the prekey over the gated extracted ratchet* (genuine UC). The ideal
   functionality is `F_SMK` at the schemes `(drExtractedSMPair … (ι x₀)).gateB` keyed through
   `drExtractedIniPair`: the secure channel of `F_AKEK` with the prekey datum whose completed
   sessions have the ideal view of the schedule `Sch` over the gated extracted scheme at the
   signed-prekey pair of their datum. The real world is X3DH with the datum `x3dhRealPair GX`
   followed by the ratchet layer over the gated extracted scheme, whose initiator starts with the
   responder's signed prekey as remote public value and whose responder starts with the signed
   prekey pair. The simulator is `chanSim (simProtPair GX) x3dhFwd`. The bound is
   `signalExtractedBoundPair`, the bound of `signal_stack_realizes_FSM_acd_prekey` at the
   encoded schedule.
2. *The extracted X3DH.* The system of `extGame` is `x3dhRealOfK (fixedKDF H) (x3dhAlg GX)`
   (`extSys_eq`).
3. *The initiator's session.* The session of `Uninitialized_establish` on the key of
   `X3dh.initiate` is the epoch opening `ratchet` from `drInitSession` at the encoded X3DH key
   and the encoded signed prekey, as in `signal_extracted_e2e`.
4. *The responder's session.* The session of `ratchet_init_responder` on the key of
   `X3dh.respond` with the signed-prekey secret `s`, the key pair `(encX s, encG (GX.pub s))` and
   the remote public value `encG (GX.pub s)` is the responder state `drPairBob` of
   `drExtractedIniPair` at the root key `H (bobInp …)` and `y = ι s`. -/
theorem signal_extracted_e2e_prekey [X3dh.X3dhDeps] (GX : DHGroup S G) (P : Finset PartyId)
    {encCtx : SessionId × PartyId × PartyId → Array Int} {encX : S → Array Int}
    {H : Inp G → RK} {decG : Array Int → G} {decR : Array Int → RK}
    (hX : X3dhSquareHom GX encCtx encX encG encR H)
    (hD : DrHom G R F D ptLen encR encG encSk decE encS encW encC)
    (hG : ∀ Y, decG (encG Y) = Y) (hR : ∀ k, decR (encR k) = k)
    (ι : S → Sk) (hι : SpkCompat GX ι encX encSk decE) (c : SamplerCert CG.Exp)
    (hμ : c.μ = (SDistr.uniform Sk).bind fun x => SDistr.pure (decE x))
    (hν : c.ν = SDistr.uniform CG.Exp)
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 2 ≤ ΔPCS)
    (Sch : Array Int →
      OracleAdv (SMQuery Wd) (SMSchemeAns (Array Int) (Array Int) (Option DrLeak)) V)
    (t n : ℕ) :
    RealizesSim ((x3dhRealPair (K := RK) GX).seq (smCorruptLayerK
        (fun s => (drExtractedSMPair RK ptLen encR encG encSk decE encW encC (ι s)).gateB)
        (fun k s => gateIni (fun rk => drExtractedIniPair encR encG encSk decE rk (ι s)) k)
        Sch t n ΔFS ΔPCS))
      (F_SMK (fun s => (drExtractedSMPair RK ptLen encR encG encSk decE encW encC (ι s)).gateB)
        (fun k s => gateIni (fun rk => drExtractedIniPair encR encG encSk decE rk (ι s)) k)
        Sch t n ΔFS ΔPCS)
      (chanSim (simProtPair (K := RK) GX) x3dhFwd)
      (signalExtractedBoundPair GX P decE c ι R F D encR encG encSk encS encC Sch t n ΔFS
        ΔPCS) ∧
    (OProt.oracle (Q := HEv ⊕ RAEv G) (A := HOut RK ⊕ ROut S G RK)).sys
        (extGame encCtx encX encG decG decR) = x3dhRealOfK (fixedKDF H) (x3dhAlg GX) ∧
    (∀ (u : Doubleratchet.Uninitialized_T) (g : Array Int) (sid : SessionId) (a b : PartyId)
      (ik ek : S) (IKB SPKB OPKB : G) (sig : Array Int) (y : Sk) (sk₀ pk₀ : Array Int),
      (X3dh.initiate (encCtx (sid, a, b)) (encX ik) (encX ek)
          (encG IKB, encG SPKB, encG OPKB, sig) true).map
          (fun o => (Doubleratchet.Uninitialized_establish u g o.1 (encSk y)
            (encG (CG.pow (decE y))) (encG SPKB)).1) =
        some ((drExtractedSM RK ptLen encR encG encSk decE encW encC).ratchet
          (drInitSession (encR (H (aliceInp GX sid a b ik ek IKB SPKB OPKB))) sk₀ pk₀
            (encG SPKB)) y).1) ∧
    ∀ (sid : SessionId) (a b : PartyId) (ik s opk : S) (IKA E : G) (opk_id : Array Int),
      (X3dh.respond (encCtx (sid, a, b)) (encX ik) (encX s) (encX opk)
          (encG IKA, encG E, opk_id) true).map
          (fun k => Doubleratchet.ratchet_init_responder k (encX s) (encG (GX.pub s))
            (encG (GX.pub s))) =
        some (drPairBob encR encG encSk decE (H (bobInp GX sid a b IKA E ik s opk)) (ι s)) := by
  refine ⟨?_, extSys_eq hX hG hR, ?_, ?_⟩
  · have hL : smCorruptLayerK (R := ROut S G RK)
        (fun s => (drExtractedSMPair RK ptLen encR encG encSk decE encW encC (ι s)).gateB)
        (fun k s => gateIni (fun rk => drExtractedIniPair encR encG encSk decE rk (ι s)) k)
        Sch t n ΔFS ΔPCS =
        smCorruptLayerK
          (fun x₀ => (acdSM ((dhCKAOf G decE).atInit (dhPairInit decE (ι x₀))) R F D).gateB)
          (fun k x₀ => gateIni (acdIniPair (Sa := Sa) (dhCKAOf G decE)
            (dhPairInit decE (ι x₀))) k)
          (drSchPair encR encG encSk decE encS encC Sch) t n ΔFS ΔPCS := by
      simp only [smCorruptLayerK]
      exact congrArg _ (funext fun p => smRealViewK_drExtractedPair hD ι Sch t n ΔFS ΔPCS p)
    have hF : F_SMK
        (fun s => (drExtractedSMPair RK ptLen encR encG encSk decE encW encC (ι s)).gateB)
        (fun k s => gateIni (fun rk => drExtractedIniPair encR encG encSk decE rk (ι s)) k)
        Sch t n ΔFS ΔPCS =
        F_SMK
          (fun x₀ => (acdSM ((dhCKAOf G decE).atInit (dhPairInit decE (ι x₀))) R F D).gateB)
          (fun k x₀ => gateIni (acdIniPair (Sa := Sa) (dhCKAOf G decE)
            (dhPairInit decE (ι x₀))) k)
          (drSchPair encR encG encSk decE encS encC Sch) t n ΔFS ΔPCS := by
      simp only [F_SMK]
      rw [funext fun p => smRealViewK_drExtractedPair hD ι Sch t n ΔFS ΔPCS p,
        funext fun x₀ => smIdealViewK_drExtractedPair hD ι Sch t n ΔFS ΔPCS x₀]
    have key := signal_stack_realizes_FSM_acd_prekey (t := t) (n := n) (RK := RK) (Sa := Sa)
      (V := V) GX P decE c hμ hν ι id (fun x => hι.pub x) R F D
      (drSchPair encR encG encSk decE encS encC Sch) hFS hPCS
    rw [hL, hF]
    exact key
  · intro u g sid a b ik ek IKB SPKB OPKB sig y sk₀ pk₀
    rw [initiate_square_eq_some hX, Option.map_some,
      signal_session_extracted_drOpen u g _ _ _ _ _ _ sk₀ pk₀ _, initiate_square_enc hX]
    rfl
  · intro sid a b ik s opk IKA E opk_id
    rw [respond_square_eq_some hX, Option.map_some, respond_square_enc hX]
    simp only [drPairBob, drInitSession, hι.enc, hι.pub]

end Pair

end CatCrypt.Crypto.Signal.EndToEnd
