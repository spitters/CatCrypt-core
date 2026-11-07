/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signal.DoubleRatchet.ExtractedCorrespondence
public import CatCryptCore.Crypto.Messaging.SMScheme

/-!
# The extracted double ratchet as a secure-messaging scheme

The session functions of the haxpipeT extraction of `doubleratchet-hax` as an instance
`drExtractedSM` of the secure-messaging record `SMScheme`, and its simulation of the ACD
construction `acdSM (dhCKAOf G decE) R F D` under `DrHom` (`drExtracted_sim`). Through the
transfer lemmas of `CatCryptCore.Crypto.Messaging.SMScheme`, the corruption game and the game
with an adaptive challenge epoch over the extracted scheme are those over the ACD construction
with the answers encoded, and the bounds of `CatCryptCore.Crypto.Messaging.SMCorrupt` (forward
secrecy and post-compromise security with the delays `ΔFS`, `ΔPCS`) hold at the relabelled
adversary (`drExtracted_corruptAdvantage_le`, `drExtracted_adaptiveAdvantage_le`). The only
statement about the extracted code is the simulation; the game theorems are its instances.

## The scheme

A party state is a `Session_T` of the crate. The record of ACD separates the receipt of the
peer's public value from the opening of the next epoch, so that a corruption may come between
them; the crate performs both in one call, `Session_dh_ratchet`. Its two halves are
`sessionRecvStep` (the root step `kdf_rk` at the root key on `dh my_sk T`, which gives the next
root key and the receiving chain key; the remote public key becomes `T`) and
`sessionRatchetStep` (the root step on `dh sk remote_pk` for the new key pair `(sk, pk)`, which
gives the next root key and the sending chain key), and `Session_dh_ratchet` is the second
after the first (`Session_dh_ratchet_eq`). The first epoch of the initiator is opened by
`Uninitialized_establish`, the transition of the crate from `Uninitialized` to `Session`: on the
root key, the new key pair and the remote public value it computes the same root step and holds
its chain key as the sending chain key and no receiving chain key. The scheme `drExtractedSM`:

* `init` — a uniform secret key `x₀` of `Sk` and a uniform root key; both parties start in the
  session `drInitSession` with the encoded root key, no chain keys, the key pair
  `(x₀, g ^ decE x₀)` and the remote public value `g ^ decE x₀`, as in the CKA initialisation
  of ACD;
* `ratchet` — `drOpen` with the fresh key pair `(y, g ^ decE y)` of the secret key `y`, and the
  public value `g ^ decE y`: a session without a receiving chain key has received no epoch of
  the peer, and `drOpen` opens its epoch by `Uninitialized_establish` on its root key and its
  remote public value; a session with a receiving chain key opens it by `sessionRatchetStep`.
  In the games the first case is the first epoch of the initiator: every later epoch is opened
  after the receipt of an epoch of the peer (`CKAGameSt.canSend`);
* `recv` — `sessionRecvStep`;
* `send` — `Session_send` under the ghost hooks `keyGhost`, which hand out the message key, and
  `aead_encrypt` of the plaintext with the associated data of the message under that key;
  `Session_send` refuses on a session without a sending chain key, and so does the scheme;
* `expose` — the key material of the session: the root key, the chain keys (`none` for an
  absent chain), the key pair and the remote public value (`drExpose`); the counters `send_n`,
  `recv_n` and `step`, which the transcript of the queries determines, are not part of it;
* `idealCt` — the encoding of a uniform model ciphertext.

## The simulation

`drRel` relates a session to a party state of the ACD construction: the root key, the chain
keys (`none` for an absent chain), the secret key, its public value and the remote public value
are the encodings of the components. Under `DrHom`, `drExtracted_sim` proves that
`drExtractedSM` simulates `acdSM (dhCKAOf G decE) R F D` along `drRel`, with public values
encoded by `encG`, ciphertexts by `encC`, corruption answers by `drEncLeak` and initial states
by `drEncInit`. The CKA of the model is `dhCKAOf G decE`, the Diffie–Hellman CKA whose secret
keys are the uniform elements of `Sk` with exponents `decE`: the extracted secret keys are drawn
from `Sk` and revealed by a corruption, so the model draws and reveals the same keys.

## Main definitions

* `sessionRecvStep`, `sessionRatchetStep` — the halves of `Session_dh_ratchet`
* `drOpen` — opening an epoch: `Uninitialized_establish` without a receiving chain,
  `sessionRatchetStep` otherwise
* `drInitSession`, `drExpose`, `drExtractedSM` — the extracted scheme
* `drRel`, `drEncLeak`, `drEncInit` — the encodings of the simulation

## Main results

* `Session_dh_ratchet_eq` — the Diffie–Hellman ratchet of the crate in terms of the halves
* `drExtracted_sim` — the extracted scheme simulates the ACD construction
* `drExtracted_corruptAdvantage_eq`, `drExtracted_adaptiveAdvantage_eq` — the games of the
  extracted scheme are those of the ACD construction at the encoded adversary
* `drExtracted_corruptAdvantage_le`, `drExtracted_adaptiveAdvantage_le` — the bounds of
  `sm_corrupt_advantage_le` and `sm_adaptive_corrupt_advantage_le` at
  `dhCKAOf G decE`, the root KDF `R`, the generator `F` and the AEAD `D`
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

/-! ## The halves of the Diffie–Hellman ratchet of the crate -/

/-- The receiving half of `Session_dh_ratchet`: the root step at the root key on
`dh my_sk T` gives the next root key and the receiving chain key, and `T` becomes the remote
public value. -/
def sessionRecvStep (x : Session_T) (T : Array Int) : Session_T :=
  Session (kdf_rk («Session.root_key» x) (dh («Session.my_sk» x) T)).1 («Session.send_ck» x)
    (some (kdf_rk («Session.root_key» x) (dh («Session.my_sk» x) T)).2) («Session.send_n» x)
    («Session.recv_n» x) («Session.my_sk» x) («Session.my_pk» x) T («.step» x)

/-- The sending half of `Session_dh_ratchet` with the new key pair `(sk, pk)`: the root step on
`dh sk remote_pk` gives the next root key and the sending chain key. -/
def sessionRatchetStep (x : Session_T) (sk pk : Array Int) : Session_T :=
  Session (kdf_rk («Session.root_key» x) (dh sk («Session.remote_pk» x))).1
    (some (kdf_rk («Session.root_key» x) (dh sk («Session.remote_pk» x))).2)
    («Session.recv_ck» x) 0 0 sk pk («Session.remote_pk» x) (Hax.add («.step» x) 1)

/-- **The Diffie–Hellman ratchet of the crate is its receiving half followed by its sending
half.** -/
theorem Session_dh_ratchet_eq (x : Session_T) (g T sk pk : Array Int) :
    Session_dh_ratchet x g T sk pk =
      (sessionRatchetStep (sessionRecvStep x T) sk pk, event g 2 (Hax.add («.step» x) 1)) := by
  obtain ⟨a, b, c, d, e, f, i, j, k⟩ := x
  rfl

/-- **Opening an epoch** with the new key pair `(sk, pk)`. A session without a receiving chain
key has received no epoch of the peer: it opens the epoch by `Uninitialized_establish` on its
root key, the new key pair and its remote public value. A session with a receiving chain key
opens it by the sending half `sessionRatchetStep` of `Session_dh_ratchet`. -/
def drOpen (x : Session_T) (sk pk : Array Int) : Session_T :=
  match «Session.recv_ck» x with
  | none =>
    (Uninitialized_establish Uninitialized #[] («Session.root_key» x) sk pk
      («Session.remote_pk» x)).1
  | some _ => sessionRatchetStep x sk pk

/-! ## The scheme -/

/-- The initial session of a party: the root key `rk`, no chain keys, the key pair `(sk, pk)`
and the remote public value `rpk`. -/
def drInitSession (rk sk pk rpk : Array Int) : Session_T := Session rk none none 0 0 sk pk rpk 0

/-- The corruption answers of the extracted scheme: root key, sending and receiving chain
keys (`none` for an absent chain), secret key, public key and remote public value. -/
abbrev DrLeak :=
  Array Int × Option (Array Int) × Option (Array Int) × Array Int × Array Int × Array Int

/-- The key material of a session. -/
def drExpose (x : Session_T) : DrLeak :=
  («Session.root_key» x, «Session.send_ck» x, «Session.recv_ck» x, «Session.my_sk» x,
    «Session.my_pk» x, «Session.remote_pk» x)

section Scheme

variable {RK W Ct Sk : Type} {G : Type} [CG : CyclicGroup G] [Fintype RK] [Nonempty RK]
  [Fintype Sk] [Nonempty Sk] [SampleableType Ct]

variable (RK) in
/-- **The extracted double ratchet as a secure-messaging scheme.** Party states are sessions
of the crate; the secret keys are the uniform elements of `Sk`, encoded by `encSk`, with
exponents `decE`; group elements are encoded by `encG`, root keys by `encR`, words by `encW`,
model ciphertexts by `encC`; the plaintext length is `ptLen`. -/
noncomputable def drExtractedSM (ptLen : Int) (encR : RK → Array Int) (encG : G → Array Int)
    (encSk : Sk → Array Int) (decE : Sk → CG.Exp) (encW : W → Array Int)
    (encC : Ct → Array Int) : SMScheme Session_T (Array Int) Sk W (Array Int) DrLeak where
  init := SPComp.bind (SPComp.sample Sk) fun x => SPComp.bind (SPComp.sample RK) fun rk =>
    SPComp.pure (encG (CG.pow (decE x)),
      drInitSession (encR rk) (encSk x) (encG (CG.pow (decE x))) (encG (CG.pow (decE x))),
      drInitSession (encR rk) (encSk x) (encG (CG.pow (decE x))) (encG (CG.pow (decE x))))
  ratchet x y := (drOpen x (encSk y) (encG (CG.pow (decE y))), encG (CG.pow (decE y)))
  recv := sessionRecvStep
  send x m := (@Session_send (keyGhost inst) x #[]).1.map fun x' =>
    (x', aead_encrypt (@Session_send (keyGhost inst) x #[]).2 (encW m.1) ptLen (encW m.2))
  expose := drExpose
  idealCt := (PMF.uniformFintype Ct).map encC

end Scheme

/-! ## The simulation of the ACD construction -/

section Sim

variable {RK Sa W Ct Sk : Type} [SampleableType W] {G : Type} [CG : CyclicGroup G]
  [Fintype RK] [Nonempty RK] [Fintype Sk] [Nonempty Sk] [SampleableType Ct]

/-- A session and a party state of the ACD construction over `dhCKAOf G decE` correspond: the
root key, the chain keys, the secret key, its public value and the remote public value of the
session are the encodings of the components. -/
def drRel (encR : RK → Array Int) (encG : G → Array Int) (encSk : Sk → Array Int)
    (decE : Sk → CG.Exp) (encS : Sa → Array Int) (x' : Session_T)
    (x : SMPartySt (G × Sk) RK Sa) : Prop :=
  «Session.root_key» x' = encR x.rk ∧ «Session.send_ck» x' = x.snd.map encS ∧
    «Session.recv_ck» x' = x.rcv.map encS ∧ «Session.my_sk» x' = encSk x.ck.2 ∧
    «Session.my_pk» x' = encG (CG.pow (decE x.ck.2)) ∧ «Session.remote_pk» x' = encG x.ck.1

/-- The encoding of a corruption answer of the ACD construction as one of the extracted
scheme. -/
def drEncLeak (encR : RK → Array Int) (encG : G → Array Int) (encSk : Sk → Array Int)
    (decE : Sk → CG.Exp) (encS : Sa → Array Int) (x : SMPartySt (G × Sk) RK Sa) : DrLeak :=
  (encR x.rk, x.snd.map encS, x.rcv.map encS, encSk x.ck.2, encG (CG.pow (decE x.ck.2)),
    encG x.ck.1)

/-- The encoding of a party state of the ACD construction as a session with zero counters. -/
def drEncInit (encR : RK → Array Int) (encG : G → Array Int) (encSk : Sk → Array Int)
    (decE : Sk → CG.Exp) (encS : Sa → Array Int) (x : SMPartySt (G × Sk) RK Sa) : Session_T :=
  Session (encR x.rk) (x.snd.map encS) (x.rcv.map encS) 0 0 (encSk x.ck.2)
    (encG (CG.pow (decE x.ck.2))) (encG x.ck.1) 0

variable {R : PRGDef (RK × G) (RK × Sa)} {F : PRGDef Sa (W × Sa)} {D : AEADDef W Ct}
  {ptLen : Int} {encR : RK → Array Int} {encG : G → Array Int} {encSk : Sk → Array Int}
  {decE : Sk → CG.Exp} {encS : Sa → Array Int} {encW : W → Array Int} {encC : Ct → Array Int}

/-- **The extracted double ratchet simulates the ACD construction.** Under `DrHom`, the scheme
`drExtractedSM` simulates `acdSM (dhCKAOf G decE) R F D` along `drRel`, with public values
encoded by `encG`, ciphertexts by `encC`, corruption answers by `drEncLeak` and initial states
by `drEncInit`. Opening an epoch is `establish_enc` from a session without a receiving chain
key and `kdf_rk_enc` and `dh_enc` at the remote public value otherwise; receiving is
`kdf_rk_enc` and `dh_enc` at the received value; sending is `session_send_enc` and the equation
of the AEAD, and `session_send_none` on an absent sending chain. -/
theorem drExtracted_sim (h : DrHom G R F D ptLen encR encG encSk decE encS encW encC) :
    (drExtractedSM RK ptLen encR encG encSk decE encW encC).Sim
      (acdSM (dhCKAOf G decE) R F D) (drRel encR encG encSk decE encS) encG encC
      (drEncLeak encR encG encSk decE encS) (drEncInit encR encG encSk decE encS) where
  init := by
    simp only [drExtractedSM, acdSM, dhCKAOf, SPComp.bind_assoc, SPComp.pure_bind]
    rfl
  init_rel x := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  ratchet x' x r hx := by
    obtain ⟨hrk, hsnd, hrcv, hsk, hpk, hrpk⟩ := hx
    obtain ⟨a, b, c, d, e, f, i, j, k⟩ := x'
    simp only [«Session.root_key», «Session.send_ck», «Session.recv_ck», «Session.my_sk»,
      «Session.my_pk», «Session.remote_pk»] at hrk hsnd hrcv hsk hpk hrpk
    subst hrk hrpk hrcv
    cases hr : x.rcv with
    | none =>
      refine ⟨⟨?_, ?_, ?_, rfl, rfl, rfl⟩, rfl⟩
      · simp only [drExtractedSM, drOpen, hr, Option.map_none, «Session.recv_ck»,
          «Session.root_key», «Session.remote_pk», establish_enc h, acdSM, CKACoins.sendR]
      · simp only [drExtractedSM, drOpen, hr, Option.map_none, «Session.recv_ck»,
          «Session.root_key», «Session.send_ck», «Session.remote_pk», establish_enc h, acdSM,
          CKACoins.sendR, Option.map_some]
      · simp only [drExtractedSM, drOpen, hr, Option.map_none, «Session.recv_ck»,
          «Session.root_key», «Session.remote_pk», establish_enc h, acdSM]
    | some sa =>
      refine ⟨⟨?_, ?_, ?_, rfl, rfl, rfl⟩, rfl⟩
      · simp only [drExtractedSM, drOpen, hr, Option.map_some, «Session.recv_ck»,
          sessionRatchetStep, acdSM, CKACoins.sendR, Session, «Session.root_key»,
          «Session.remote_pk», dh_enc h, kdf_rk_enc h]
      · simp only [drExtractedSM, drOpen, hr, Option.map_some, «Session.recv_ck»,
          sessionRatchetStep, acdSM, CKACoins.sendR, Session, «Session.root_key»,
          «Session.send_ck», «Session.remote_pk», dh_enc h, kdf_rk_enc h]
      · simp only [drExtractedSM, drOpen, hr, Option.map_some, «Session.recv_ck»,
          sessionRatchetStep, acdSM, Session]
  recv x' x T hx := by
    obtain ⟨hrk, hsnd, hrcv, hsk, hpk, hrpk⟩ := hx
    obtain ⟨a, b, c, d, e, f, i, j, k⟩ := x'
    simp only [«Session.root_key», «Session.send_ck», «Session.recv_ck», «Session.my_sk»,
      «Session.my_pk», «Session.remote_pk»] at hrk hsnd hrcv hsk hpk hrpk
    subst hrk hsk
    refine ⟨?_, hsnd, ?_, rfl, hpk, rfl⟩
    · simp only [drExtractedSM, sessionRecvStep, acdSM, dhCKAOf, Session, «Session.root_key»,
        «Session.my_sk», dh_enc h, kdf_rk_enc h]
    · simp only [drExtractedSM, sessionRecvStep, acdSM, dhCKAOf, Session, «Session.root_key»,
        «Session.my_sk», «Session.recv_ck», dh_enc h, kdf_rk_enc h, Option.map_some]
  send x' x m hx := by
    obtain ⟨hrk, hsnd, hrcv, hsk, hpk, hrpk⟩ := hx
    obtain ⟨a, b, c, d, e, f, i, j, k⟩ := x'
    simp only [«Session.root_key», «Session.send_ck», «Session.recv_ck», «Session.my_sk»,
      «Session.my_pk», «Session.remote_pk»] at hrk hsnd hrcv hsk hpk hrpk
    subst hsnd
    cases hx : x.snd with
    | none =>
      simp only [drExtractedSM, acdSM, hx, Option.map_none, session_send_none]
      exact Option.Rel.none
    | some sa =>
      simp only [drExtractedSM, acdSM, hx, Option.map_some,
        session_send_enc (inst := keyGhost inst) h.ghost]
      refine Option.Rel.some ⟨⟨hrk, rfl, hrcv, hsk, hpk, hrpk⟩, h.aead_eq _ _ _⟩
  expose x' x hx := by
    obtain ⟨hrk, hsnd, hrcv, hsk, hpk, hrpk⟩ := hx
    simp only [drExtractedSM, acdSM, drExpose, drEncLeak, hrk, hsnd, hrcv, hsk, hpk, hrpk, id]
  idealCt := rfl

section Bounds

variable [Fintype Sa] [Nonempty Sa] [DecidableEq RK] [DecidableEq G]

omit [Fintype Sa] [Nonempty Sa] [DecidableEq RK] [DecidableEq G] in
/-- **The corruption game of the extracted double ratchet is that of the ACD construction.**
Under `DrHom`, the advantage of an adversary `A` against `drExtractedSM` is the advantage in
`sm_corrupt_game (dhCKAOf G decE) R F D` of `A` with the answers encoded and relabelled. -/
theorem drExtracted_corruptAdvantage_eq
    (h : DrHom G R F D ptLen encR encG encSk decE encS encW encC)
    (ΔFS ΔPCS : ℕ) (A : SMSchemeAdv (Array Int) W (Array Int) DrLeak) :
    (drExtractedSM RK ptLen encR encG encSk decE encW encC).corruptAdvantage ΔFS ΔPCS A =
      SM_Corrupt_Advantage (dhCKAOf G decE) R F D ΔFS ΔPCS
        (A.comap encG encC (drEncLeak encR encG encSk decE encS)).toSM := by
  rw [(drExtracted_sim h).corruptAdvantage_eq,
    acdSM_corruptAdvantage_eq (dhCKAOf G decE) (dhCKAOf_correct G decE) (dhInitPOf G decE)
      (dhCKAOf_init_eq G decE) (dhInitPOf_rel G decE)]

/-- **Forward secrecy and post-compromise security of the extracted double ratchet.** Under
`DrHom`, with `2 ≤ ΔFS` and `1 ≤ ΔPCS`, the advantage of every adversary `A` in the corruption
game over `drExtractedSM` is at most the CKA corruption advantages of `smcCKARed`, the PRF-PRNG
advantages of the root KDF `R` at `smcRootRed` and the FS-AEAD advantage at `smcFSRed`, for the
CKA `dhCKAOf G decE` and the adversary `A` with the answers encoded and relabelled. -/
theorem drExtracted_corruptAdvantage_le
    (h : DrHom G R F D ptLen encR encG encSk decE encS encW encC)
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS)
    (A : SMSchemeAdv (Array Int) W (Array Int) DrLeak) :
    (drExtractedSM RK ptLen encR encG encSk decE encW encC).corruptAdvantage ΔFS ΔPCS A ≤
      ∑ b : Bool, CKA_Corrupt_Advantage (dhCKAOf G decE) ΔFS ΔPCS
          (smcCKARed R F D b (A.comap encG encC (drEncLeak encR encG encSk decE encS)).toSM) +
        ∑ b : Bool, PRFPRNG_Advantage R (smcRootRed (dhCKAOf G decE) R F D ΔFS ΔPCS b
          (dhInitPOf G decE) (A.comap encG encC (drEncLeak encR encG encSk decE encS)).toSM) +
        FSAEAD_Corrupt_Advantage F D (smcFSRed (dhCKAOf G decE) R F D ΔFS ΔPCS
          (dhInitPOf G decE) (A.comap encG encC (drEncLeak encR encG encSk decE encS)).toSM) := by
  rw [(drExtracted_sim h).corruptAdvantage_eq]
  exact acdSM_corruptAdvantage_le (dhCKAOf G decE) (dhCKAOfCoins_sound G decE)
    (dhCKAOf_correct G decE) (dhInitPOf G decE) (dhCKAOf_init_eq G decE) (dhInitPOf_rel G decE)
    R F D hFS hPCS _

/-- **The extracted double ratchet with an adaptive challenge epoch.** Under `DrHom`, with
`2 ≤ ΔFS` and `1 ≤ ΔPCS`, the advantage of every adversary `A` in the game over `drExtractedSM`
with an adaptive challenge epoch is at most the sum over the epochs `e` of the CKA, PRF-PRNG and
FS-AEAD terms at the guessing reduction `smGuessAdv ΔFS ΔPCS _ e` of `A` with the answers
encoded and relabelled. -/
theorem drExtracted_adaptiveAdvantage_le
    (h : DrHom G R F D ptLen encR encG encSk decE encS encW encC)
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS)
    (A : Array Int → OracleAdv (SMQuery W) (SMSchemeAns (Array Int) (Array Int) DrLeak) Bool) :
    (drExtractedSM RK ptLen encR encG encSk decE encW encC).adaptiveAdvantage ΔFS ΔPCS A ≤
      ∑' e, (∑ b : Bool, CKA_Corrupt_Advantage (dhCKAOf G decE) ΔFS ΔPCS
            (smcCKARed R F D b (smGuessAdv ΔFS ΔPCS (fun T => ((A (encG T)).mapQueryAnswer id
              (SMSchemeAns.map encG encC (drEncLeak encR encG encSk decE encS))).mapQueryAnswer
                id SMAns.toScheme) e)) +
        ∑ b : Bool, PRFPRNG_Advantage R (smcRootRed (dhCKAOf G decE) R F D ΔFS ΔPCS b
          (dhInitPOf G decE) (smGuessAdv ΔFS ΔPCS (fun T => ((A (encG T)).mapQueryAnswer id
            (SMSchemeAns.map encG encC (drEncLeak encR encG encSk decE encS))).mapQueryAnswer
              id SMAns.toScheme) e)) +
        FSAEAD_Corrupt_Advantage F D (smcFSRed (dhCKAOf G decE) R F D ΔFS ΔPCS
          (dhInitPOf G decE) (smGuessAdv ΔFS ΔPCS (fun T => ((A (encG T)).mapQueryAnswer id
            (SMSchemeAns.map encG encC (drEncLeak encR encG encSk decE encS))).mapQueryAnswer
              id SMAns.toScheme) e))) := by
  rw [(drExtracted_sim h).adaptiveAdvantage_eq]
  exact acdSM_adaptiveAdvantage_le (dhCKAOf G decE) (dhCKAOfCoins_sound G decE)
    (dhCKAOf_correct G decE) (dhInitPOf G decE) (dhCKAOf_init_eq G decE) (dhInitPOf_rel G decE)
    R F D hFS hPCS _

end Bounds

end Sim

end CatCrypt.Crypto.Signal.DoubleRatchet.ExtractedScheme
