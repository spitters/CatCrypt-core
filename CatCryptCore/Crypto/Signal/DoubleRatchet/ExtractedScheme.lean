/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signal.DoubleRatchet.ExtractedStore
public import CatCryptCore.Crypto.Messaging.SMHdr
public import CatCryptCore.Crypto.Messaging.SMPrekey
public import CatCryptCore.Crypto.Messaging.SMHdrAdaptive

/-!
# The extracted double ratchet as a secure-messaging scheme

The state functions of the haxpipeT extraction of `doubleratchet-hax` as an instance
`drExtractedSM` of the secure-messaging record `SMScheme`, and its simulation of the ACD
construction with message headers `acdHdrSM (dhCKAOf G decE) R F D (drHdrAD adOf)` under `DrHom`
(`drExtracted_sim`). Through the transfer lemmas of `CatCryptCore.Crypto.Messaging.SMScheme`, the
corruption game over the extracted scheme is the game over `acdHdrSM` with the answers encoded,
and the bound `acdHdrSM_corruptAdvantage_le_prim` (forward secrecy and post-compromise security
with the delays `ΔFS`, `ΔPCS`) holds at the relabelled adversary
(`drExtracted_corruptAdvantage_le`). The game with an adaptive challenge epoch over `acdHdrSM` is
`sm_adaptive_game` at the wrapper adversary `smHdrAdaptive hdrAD A` (`smAdaptiveGame_acdHdr`,
the adaptive counterpart of `smCorruptGame_acdHdr`), which gives the bound of the extracted
ratchet with an adaptive challenge epoch (`drExtracted_adaptiveAdvantage_le`). The only
statement about the extracted code is the simulation; the game theorems are its instances.

`drExtractedSM` is the store-free abstraction of the ratchet. `drRecv` is the receiving half of
`dh_ratchet` alone, whereas the crate's `ratchet_receive_key` first runs `skip_message_keys` to
`PN`, which stores the keys of the old chain that have not been used. The bounds over
`drExtractedSM` are about corruptions that return the key material `drExpose`: the root key, the
chain keys, the key pair and the remote public value.

The bounds are stated for `1 ≤ ΔPCS` with the CKA advantage of `dhCKAOf G decE` as a term. That
term is bounded by DDH for `2 ≤ ΔPCS` (`dhCKAOf_corrupt_advantage_le`); at `ΔPCS = 1` the party
that sent in the epoch before the challenge still holds the exponent that determines the
challenge key.

## The scheme

A party state is a `RatchetState_T` of the crate. The record of ACD separates the receipt of
the peer's public value from the opening of the next epoch, so that a corruption may come
between them; the crate performs both in one call, `dh_ratchet`, the sending half
`dh_ratchet_send_half` after the receiving half `dh_ratchet_recv_half`. The receiving half also
sets `PN = Ns` and `Ns = 0`, the counters of the header of the next message; in the ACD
construction with headers the opening of an epoch sets them. The scheme takes the counter reset
with the second half: `drRecv` is `dh_ratchet_recv_half` with the sending counters `pn`, `ns`
kept, `drOpen` is `dh_ratchet_send_half` followed by `PN = Ns` and `Ns = 0`, and their
composition is `dh_ratchet` (`drOpen_drRecv`). The first epoch of the initiator is opened by
`drOpen` from the initial state `drInitState`, which is `ratchet_init_alice`
(`drOpen_drInitState`). The scheme `drExtractedSM`:

* `init` — a uniform secret key `x₀` of `Sk` and a uniform root key; both parties start in
  `drInitState` with the encoded root key, no chain keys, the key pair `(x₀, g ^ decE x₀)`, the
  remote public value `g ^ decE x₀`, zero counters and an empty store, as in the CKA
  initialisation of ACD;
* `ratchet` — `drOpen` with the fresh key pair `(y, g ^ decE y)` of the secret key `y`, and the
  public value `g ^ decE y`;
* `recv` — `drRecv`;
* `send` — `ratchet_encrypt` of the encoded plaintext with the associated data
  `encAD (adOf ad)` of the key agreement; the crate binds the header `(dhs_pk, pn, ns)` into the
  associated data of the AEAD. The ciphertext of the scheme is the ciphertext body: the header is
  public, a function of the state, and the ciphertext length is `ct_len ptLen`;
* `expose` — the key material of the state: the root key, the chain keys (`none` for an absent
  chain), the key pair and the remote public value (`drExpose`); the counters, which the
  transcript of the queries determines, and the store of skipped keys, which `drRecv` leaves
  empty, are not part of it;
* `idealCt` — the encoding of a uniform model ciphertext.

## The simulation

`drRel` relates a ratchet state to a party state of `acdHdrSM`: the root key, the chain keys,
the secret key and the remote public value are the encodings of the components, the public key
is the encoding of `drPub` (the public value of the sending epoch, which the header carries, and
the public value of the secret key before the first opening), the counters `pn`, `ns` are those
of the header data, and the store is empty. The model ciphertext carries no header: the crate's
output `(header, ct, ct_len)` is mapped to the model ciphertext by its second component, and
the header `(encG T, PN, N)` of the crate is the encoding `drEncH encG` of the header
`((T, PN), N)` of the header data of the related model state. The AEAD of the model has
associated data `A × ((G × ℕ) × ℕ)`, and `drHdrAD adOf` is the crate's layout
`CONCAT(AD, header)`: the associated data of the key agreement and the header.

## Main definitions

* `drRecv`, `drOpen`, `drInitState` — the halves of `dh_ratchet` and the initial state
* `drExpose`, `drExtractedSM` — the extracted scheme
* `drEncH`, `drHdrAD` — the header encoding and the associated-data layout of the crate
* `drPub`, `drRel`, `drEncLeak`, `drEncInit` — the encodings of the simulation

## Main results

* `drOpen_drRecv`, `drOpen_drInitState` — the halves compose to `dh_ratchet`, and the first
  opening is `ratchet_init_alice`
* `drExtracted_sim`, `drExtracted_sim_pair` — the extracted scheme simulates `acdHdrSM`
* `drExtracted_corruptAdvantage_eq` — the corruption game of the extracted scheme is that of
  `sm_corrupt_game` at the encoded wrapper adversary
* `drExtracted_corruptAdvantage_le` — the bound of `acdHdrSM_corruptAdvantage_le_prim` at
  `dhCKAOf G decE`, the root KDF `R`, the generator `F` and the AEAD `D`
* `acdAD_ad_step`, `smSchemeAdOracle_acdHdrSM_join`, `acdHdr_ad_step`, `smAdaptiveGame_acdHdr`,
  `acdHdrSM_adaptiveAdvantage_eq` — the adaptive game over `acdHdrSM` is `sm_adaptive_game` at
  the wrapper adversary `smHdrAdaptive`
* `drExtracted_adaptiveAdvantage_le` — the bound of `sm_adaptive_corrupt_advantage_le` at the
  wrapper adversary
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.DoubleRatchet.ExtractedScheme

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Messaging
open CatCrypt.Crypto.Assumptions CatCryptCore.Examples.CyclicGroupDDH
open CatCrypt.Crypto.Signal.DoubleRatchet.ExtractedCorrespondence
open CatCrypt.Crypto.Signal.DoubleRatchet.ExtractedStore
open Doubleratchet
open scoped ENNReal

variable (Dp : Type) [Inhabited Dp] [DoubleRatchetDeps Dp]

/-! ## The halves of the Diffie–Hellman ratchet of the crate -/

/-- The receiving half of `dh_ratchet` with the sending counters kept: `dh_ratchet_recv_half`
at the public value `T` (the root step on `dh dhs_sk T` gives the next root key and the
receiving chain key, `T` becomes the remote public value, `Nr = 0`), with `pn` and `ns` of
`x`. -/
def drRecv (x : RatchetState_T) (T : Array Int) : RatchetState_T :=
  RatchetState («.dhs_sk» (dh_ratchet_recv_half (D := Dp) x T))
    («.dhs_pk» (dh_ratchet_recv_half (D := Dp) x T)) («.dhr» (dh_ratchet_recv_half (D := Dp) x T))
    («.rk» (dh_ratchet_recv_half (D := Dp) x T)) («.cks» (dh_ratchet_recv_half (D := Dp) x T))
    («.ckr» (dh_ratchet_recv_half (D := Dp) x T)) («.ns» x)
    («.nr» (dh_ratchet_recv_half (D := Dp) x T)) («RatchetState.pn» x) («.sk_used» x)
    («.sk_dh» x) («.sk_n» x) («.sk_mk» x)

/-- **Opening an epoch** with the new key pair `(sk, pk)`: `dh_ratchet_send_half` (the root step
on `dh sk dhr` gives the next root key and the sending chain key), followed by `PN = Ns` and
`Ns = 0`. -/
def drOpen (x : RatchetState_T) (sk pk : Array Int) : RatchetState_T :=
  RatchetState («.dhs_sk» (dh_ratchet_send_half (D := Dp) x sk pk))
    («.dhs_pk» (dh_ratchet_send_half (D := Dp) x sk pk))
    («.dhr» (dh_ratchet_send_half (D := Dp) x sk pk))
    («.rk» (dh_ratchet_send_half (D := Dp) x sk pk))
    («.cks» (dh_ratchet_send_half (D := Dp) x sk pk))
    («.ckr» (dh_ratchet_send_half (D := Dp) x sk pk)) 0
    («.nr» (dh_ratchet_send_half (D := Dp) x sk pk)) («.ns» x) («.sk_used» x) («.sk_dh» x)
    («.sk_n» x) («.sk_mk» x)

/-- **The two halves compose to the Diffie–Hellman ratchet of the crate.** -/
theorem drOpen_drRecv (x : RatchetState_T) (T sk pk : Array Int) :
    drOpen Dp (drRecv Dp x T) sk pk = dh_ratchet (D := Dp) x T sk pk := by
  obtain ⟨a, b, c, d, e, f, i, j, k, l, m, n, o⟩ := x
  rfl

/-- The initial state of a party at the root key `rk`, the key pair `(sk, pk)` and the remote
public value `rpk`: no chain keys, zero counters and an empty store. It is `ratchet_init_bob`
with the remote public value `rpk` in place of none. -/
def drInitState (rk sk pk rpk : Array Int) : RatchetState_T :=
  RatchetState sk pk (some rpk) rk none none 0 0 0 (Hax.repeat_ false 32)
    (Hax.repeat_ (Hax.repeat_ 0 32) 32) (Hax.repeat_ 0 32) (Hax.repeat_ (Hax.repeat_ 0 32) 32)

/-- **The first opening is the initiator's initialisation of the crate**: opening an epoch from
`drInitState` with the key pair `(sk, pk)` is `ratchet_init_alice` at the root key, the remote
public value and the key pair. -/
theorem drOpen_drInitState (rk sk pk rpk sk' pk' : Array Int) :
    drOpen Dp (drInitState rk sk pk rpk) sk' pk' = ratchet_init_alice (D := Dp) rk rpk sk' pk' := by
  rfl

/-- The store of a state with the empty store arrays is empty. -/
theorem storeOf_emptyStore (sk pk rk : Array Int) (dhr cks ckr : Option (Array Int))
    (ns nr pn : Int) :
    storeOf (sk, pk, dhr, rk, cks, ckr, ns, nr, pn, Hax.repeat_ false 32,
      Hax.repeat_ (Hax.repeat_ 0 32) 32, Hax.repeat_ 0 32, Hax.repeat_ (Hax.repeat_ 0 32) 32) =
      ∅ := by
  rfl

/-! ## The scheme -/

/-- The corruption answers of the extracted scheme: root key, sending and receiving chain
keys (`none` for an absent chain), secret key, public key and remote public value. -/
abbrev DrLeak :=
  Array Int × Option (Array Int) × Option (Array Int) × Array Int × Array Int ×
    Option (Array Int)

/-- The key material of a state. -/
def drExpose (x : RatchetState_T) : DrLeak :=
  («.rk» x, «.cks» x, «.ckr» x, «.dhs_sk» x, «.dhs_pk» x, «.dhr» x)

section Scheme

variable {RK W Ct Sk A : Type} {G : Type} [CG : CyclicGroup G] [Fintype RK] [Nonempty RK]
  [Fintype Sk] [Nonempty Sk] [SampleableType Ct]

variable (RK) in
/-- **The store-free abstraction of the extracted double ratchet as a secure-messaging scheme**:
receiving stores no skipped key and a corruption returns `drExpose`. Party states are ratchet
states of the crate; the secret keys are the uniform elements of `Sk`, encoded by `encSk`, with
exponents `decE`; group elements are encoded by `encG`, root keys by `encR`, plaintexts by
`encPt`, model ciphertexts by `encC`; the associated data `ad` of a message is passed to the crate
as `encAD (adOf ad)`; the plaintext length is `ptLen`. -/
noncomputable def drExtractedSM (ptLen : Int) (encR : RK → Array Int) (encG : G → Array Int)
    (encSk : Sk → Array Int) (decE : Sk → CG.Exp) (encPt : W → Array Int)
    (encC : Ct → Array Int) (encAD : A → Array Int) (adOf : W → A) :
    SMScheme RatchetState_T (Array Int) Sk W (Array Int) DrLeak where
  init := SPComp.bind (SPComp.sample Sk) fun x => SPComp.bind (SPComp.sample RK) fun rk =>
    SPComp.pure (encG (CG.pow (decE x)),
      drInitState (encR rk) (encSk x) (encG (CG.pow (decE x))) (encG (CG.pow (decE x))),
      drInitState (encR rk) (encSk x) (encG (CG.pow (decE x))) (encG (CG.pow (decE x))))
  ratchet x y := (drOpen Dp x (encSk y) (encG (CG.pow (decE y))), encG (CG.pow (decE y)))
  recv := drRecv Dp
  send x m := (ratchet_encrypt (D := Dp) x (encPt m.1) ptLen (encAD (adOf m.2))).map fun y =>
    (y.1, y.2.2.1)
  expose := drExpose
  idealCt := (PMF.uniformFintype Ct).map encC

end Scheme

/-! ## The simulation of the ACD construction with headers -/

section Sim

variable {RK Sa W Ct Sk A : Type} [SampleableType W] {G : Type} [CG : CyclicGroup G]
  [Fintype RK] [Nonempty RK] [Fintype Sk] [Nonempty Sk] [SampleableType Ct]

/-- The encoding of a header `((T, PN), N)` of the model as a header of the crate. -/
def drEncH (encG : G → Array Int) (h : (G × ℕ) × ℕ) : MessageHeader_T :=
  (encG h.1.1, (h.1.2 : Int), (h.2 : Int))

/-- The associated data of the AEAD in the crate's layout `CONCAT(AD, header)`: the associated
data `adOf ad` of the key agreement and the header. -/
def drHdrAD (adOf : W → A) (ad : W) (h : (G × ℕ) × ℕ) : A × ((G × ℕ) × ℕ) := (adOf ad, h)

/-- The public key of a party state of `acdHdrSM`: the public value of the sending epoch, which
the header carries, once an epoch is open; the public value of the secret key before. -/
def drPub (decE : Sk → CG.Exp) (x : SMHdrSt (G × Sk) RK Sa G) : G :=
  match x.base.snd with
  | none => CG.pow (decE x.base.ck.2)
  | some _ => x.hd.pub

/-- A ratchet state and a party state of `acdHdrSM` over `dhCKAOf G decE` correspond: the root
key, the chain keys, the secret key and the remote public value of the ratchet state are the
encodings of the components, its public key is the encoding of `drPub`, its counters `pn`, `ns`
are those of the header data, and its store is empty. -/
def drRel (encR : RK → Array Int) (encG : G → Array Int) (encSk : Sk → Array Int)
    (decE : Sk → CG.Exp) (encS : Sa → Array Int) (x' : RatchetState_T)
    (x : SMHdrSt (G × Sk) RK Sa G) : Prop :=
  «.rk» x' = encR x.base.rk ∧ «.cks» x' = x.base.snd.map encS ∧
    «.ckr» x' = x.base.rcv.map encS ∧ «.dhs_sk» x' = encSk x.base.ck.2 ∧
    «.dhs_pk» x' = encG (drPub decE x) ∧ «.dhr» x' = some (encG x.base.ck.1) ∧
    «RatchetState.pn» x' = (x.hd.pn : Int) ∧ «.ns» x' = (x.hd.ns : Int) ∧ storeOf x' = ∅

/-- The encoding of a corruption answer of `acdHdrSM` as one of the extracted scheme. -/
def drEncLeak (encR : RK → Array Int) (encG : G → Array Int) (encSk : Sk → Array Int)
    (decE : Sk → CG.Exp) (encS : Sa → Array Int) (x : SMHdrSt (G × Sk) RK Sa G) : DrLeak :=
  (encR x.base.rk, x.base.snd.map encS, x.base.rcv.map encS, encSk x.base.ck.2,
    encG (drPub decE x), some (encG x.base.ck.1))

/-- The encoding of a party state of `acdHdrSM` as a ratchet state with `Nr = 0` and an empty
store. -/
def drEncInit (encR : RK → Array Int) (encG : G → Array Int) (encSk : Sk → Array Int)
    (decE : Sk → CG.Exp) (encS : Sa → Array Int) (x : SMHdrSt (G × Sk) RK Sa G) :
    RatchetState_T :=
  RatchetState (encSk x.base.ck.2) (encG (drPub decE x)) (some (encG x.base.ck.1))
    (encR x.base.rk) (x.base.snd.map encS) (x.base.rcv.map encS) (x.hd.ns : Int) 0
    (x.hd.pn : Int) (Hax.repeat_ false 32) (Hax.repeat_ (Hax.repeat_ 0 32) 32)
    (Hax.repeat_ 0 32) (Hax.repeat_ (Hax.repeat_ 0 32) 32)

variable {R : PRGDef (RK × G) (RK × Sa)} {F : PRGDef Sa (W × Sa)}
  {D : AEADDef W Ct (A × ((G × ℕ) × ℕ))} {ptLen : Int} {encR : RK → Array Int}
  {encG : G → Array Int} {encSk : Sk → Array Int} {decE : Sk → CG.Exp} {encS : Sa → Array Int}
  {encW : W → Array Int} {encPt : W → Array Int} {encC : Ct → Array Int}
  {encAD : A → Array Int} {adOf : W → A}

/-- **The extracted double ratchet simulates the ACD construction with headers.** Under `DrHom`
with the header encoding `drEncH encG`, the scheme `drExtractedSM` simulates
`acdHdrSM (dhCKAOf G decE) R F D (drHdrAD adOf)` along `drRel`, with public values encoded by
`encG`, ciphertexts by `encC`, corruption answers by `drEncLeak` and initial states by
`drEncInit`. Opening an epoch is `dh_ratchet_send_half_enc` at the remote public value;
receiving is `dh_ratchet_recv_half_enc` at the received value; sending is
`ratchet_encrypt_enc` at the header of the header data, and `ratchet_encrypt_none` on an absent
sending chain. -/
theorem drExtracted_sim
    (h : DrHom Dp G R F D ptLen encR encG encSk decE encS encW encPt encC encAD (drEncH encG)) :
    (drExtractedSM Dp RK ptLen encR encG encSk decE encPt encC encAD adOf).Sim
      (acdHdrSM (dhCKAOf G decE) R F D (drHdrAD adOf)) (drRel encR encG encSk decE encS) encG
      encC (drEncLeak encR encG encSk decE encS) (drEncInit encR encG encSk decE encS) where
  init := by
    simp only [drExtractedSM, acdHdrSM, dhCKAOf, SPComp.bind_assoc, SPComp.pure_bind]
    rfl
  init_rel x := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, storeOf_emptyStore _ _ _ _ _ _ _ _ _⟩
  ratchet x' x r hx := by
    obtain ⟨hrk, hsnd, hrcv, hsk, hpk, hdhr, hpn, hns, hst⟩ := hx
    obtain ⟨sk, pk, dhr, rk, cks, ckr, ns, nr, pn, u, sd, sn, sm⟩ := x'
    obtain ⟨⟨⟨T, s⟩, rk0, snd, rcv⟩, ⟨pub, pn0, ns0⟩⟩ := x
    simp only [«.rk», «.cks», «.ckr», «.dhs_sk», «.dhs_pk», «.dhr», «RatchetState.pn», «.ns»]
      at hrk hsnd hrcv hsk hpk hdhr hpn hns
    subst hrk hdhr hrcv hns hsk hpk hsnd hpn
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
    all_goals try simp only [drExtractedSM, drOpen, acdHdrSM, acdHdrBase, acdSMAD,
      CKACoins.sendR, dh_ratchet_send_half_enc h, drPub, RatchetState, «.rk», «.cks», «.ckr»,
      «.dhs_sk», «.dhs_pk», «.dhr», «RatchetState.pn», «.ns», «.nr», Option.map_some,
      Nat.cast_zero]
    all_goals rw [← hst]; exact storeOf_eq_of_store rfl rfl rfl rfl
  recv x' x T hx := by
    obtain ⟨hrk, hsnd, hrcv, hsk, hpk, hdhr, hpn, hns, hst⟩ := hx
    obtain ⟨sk, pk, dhr, rk, cks, ckr, ns, nr, pn, u, sd, sn, sm⟩ := x'
    obtain ⟨⟨⟨T0, s⟩, rk0, snd, rcv⟩, ⟨pub, pn0, ns0⟩⟩ := x
    simp only [«.rk», «.cks», «.ckr», «.dhs_sk», «.dhs_pk», «.dhr», «RatchetState.pn», «.ns»]
      at hrk hsnd hrcv hsk hpk hdhr hpn hns
    subst hrk hdhr hrcv hns hsk hpk hsnd hpn
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [drExtractedSM, drRecv, acdHdrSM, acdHdrBase, acdSMAD, dhCKAOf,
      dh_ratchet_recv_half_enc h, drPub, RatchetState, «.rk», «.cks», «.ckr», «.dhs_sk»,
      «.dhs_pk», «.dhr», «RatchetState.pn», «.ns», «.nr», Option.map_some]
    all_goals rw [← hst]; exact storeOf_eq_of_store rfl rfl rfl rfl
  send x' x m hx := by
    obtain ⟨hrk, hsnd, hrcv, hsk, hpk, hdhr, hpn, hns, hst⟩ := hx
    obtain ⟨sk, pk, dhr, rk, cks, ckr, ns, nr, pn, u, sd, sn, sm⟩ := x'
    obtain ⟨⟨⟨T0, s⟩, rk0, snd, rcv⟩, ⟨pub, pn0, ns0⟩⟩ := x
    simp only [«.rk», «.cks», «.ckr», «.dhs_sk», «.dhs_pk», «.dhr», «RatchetState.pn», «.ns»]
      at hrk hsnd hrcv hsk hpk hdhr hpn hns
    subst hsnd hpk hpn hns
    cases snd with
    | none =>
      simp only [drExtractedSM, acdHdrSM, acdHdrBase, acdSMAD, Option.map_none,
        ratchet_encrypt_none]
      exact Option.Rel.none
    | some sa =>
      have he := ratchet_encrypt_enc h sa m.1 (adOf m.2) ((pub, pn0), ns0) sk
        (encG pub) rk dhr ckr ns0 nr pn0 u sd sn sm rfl
      simp only [drPub, Option.map_some] at hst ⊢
      simp only [drExtractedSM, he, Option.map_some, acdHdrSM, acdHdrBase, acdSMAD, drHdrAD,
        SMHdrData.hdr]
      exact Option.Rel.some ⟨⟨hrk, rfl, hrcv, hsk, rfl, hdhr, rfl, by push_cast; rfl,
        by rw [← hst]; exact storeOf_eq_of_store rfl rfl rfl rfl⟩, rfl⟩
  expose x' x hx := by
    obtain ⟨hrk, hsnd, hrcv, hsk, hpk, hdhr, hpn, hns, hst⟩ := hx
    simp only [drExtractedSM, acdHdrSM, drExpose, drEncLeak, hrk, hsnd, hrcv, hsk, hpk, hdhr, id]
  idealCt := rfl

/-! ## The extracted double ratchet at the signed-prekey pair -/

section Pair

variable [Inhabited Sk]

/-- **The initial state of the initiator at the signed-prekey pair** of `y` at the root key
`rk`: the key pair of the default secret key and the remote public value `g ^ decE y`, the
signed prekey of the responder. -/
def drPairAlice (encR : RK → Array Int) (encG : G → Array Int) (encSk : Sk → Array Int)
    (decE : Sk → CG.Exp) (rk : RK) (y : Sk) : RatchetState_T :=
  drInitState (encR rk) (encSk default) (encG (CG.pow (decE default))) (encG (CG.pow (decE y)))

/-- **The initial state of the responder at the signed-prekey pair** of `y` at the root key
`rk`: the key pair `(y, g ^ decE y)` of the signed prekey and the remote public value
`g ^ decE y`. -/
def drPairBob (encR : RK → Array Int) (encG : G → Array Int) (encSk : Sk → Array Int)
    (decE : Sk → CG.Exp) (rk : RK) (y : Sk) : RatchetState_T :=
  drInitState (encR rk) (encSk y) (encG (CG.pow (decE y))) (encG (CG.pow (decE y)))

/-- **The keyed initialisation of the extracted double ratchet at the signed-prekey pair** of
`y`: the public value `g ^ decE y`, the initiator in `drPairAlice` and the responder in
`drPairBob` at the root key `rk`. -/
noncomputable def drExtractedIniPair (encR : RK → Array Int) (encG : G → Array Int)
    (encSk : Sk → Array Int) (decE : Sk → CG.Exp) (rk : RK) (y : Sk) :
    SPComp (Array Int × RatchetState_T × RatchetState_T) :=
  SPComp.pure (encG (CG.pow (decE y)), drPairAlice encR encG encSk decE rk y,
    drPairBob encR encG encSk decE rk y)

variable (RK) in
/-- **The extracted double ratchet at the signed-prekey pair** of `y`: the scheme
`drExtractedSM` with the initialisation `drExtractedIniPair` at a uniform root key. -/
noncomputable def drExtractedSMPair (ptLen : Int) (encR : RK → Array Int)
    (encG : G → Array Int) (encSk : Sk → Array Int) (decE : Sk → CG.Exp)
    (encPt : W → Array Int) (encC : Ct → Array Int) (encAD : A → Array Int) (adOf : W → A)
    (y : Sk) : SMScheme RatchetState_T (Array Int) Sk W (Array Int) DrLeak :=
  { drExtractedSM Dp RK ptLen encR encG encSk decE encPt encC encAD adOf with
    init := SPComp.bind (SPComp.sample RK) fun rk => drExtractedIniPair encR encG encSk decE rk y }

/-- **The gated extracted double ratchet simulates the gated ACD construction with headers at
the signed-prekey pair.** Under `DrHom`, the gate `(drExtractedSMPair … y).gateB` of the
extracted scheme at the pair of `y` simulates
`(acdHdrSM ((dhCKAOf G decE).atInit (dhPairInit decE y)) R F D (drHdrAD adOf)).gateB` along
`drRel` with equal opening flags, with corruption answers encoded by `drEncLeak` under `some`.
The steps are those of `drExtracted_sim`; the initialisations agree because `drPairAlice` and
`drPairBob` are the encodings by `drEncInit` of the party states of `dhPairInit decE y` with no
chain keys. -/
theorem drExtracted_sim_pair
    (h : DrHom Dp G R F D ptLen encR encG encSk decE encS encW encPt encC encAD (drEncH encG))
    (y : Sk) :
    (drExtractedSMPair Dp RK ptLen encR encG encSk decE encPt encC encAD adOf y).gateB.Sim
      (acdHdrSM ((dhCKAOf G decE).atInit (dhPairInit decE y)) R F D (drHdrAD adOf)).gateB
      (fun x' x => drRel encR encG encSk decE encS x'.1 x.1 ∧ x'.2 = x.2) encG encC
      (Option.map (drEncLeak encR encG encSk decE encS))
      (fun x => (drEncInit encR encG encSk decE encS x.1, x.2)) := by
  have hs := drExtracted_sim (RK := RK) (adOf := adOf) Dp h
  refine SMScheme.Sim.gateB
    { init := ?_, init_rel := hs.init_rel, ratchet := hs.ratchet, recv := hs.recv,
      send := hs.send, expose := hs.expose, idealCt := hs.idealCt }
  simp only [drExtractedSMPair, drExtractedIniPair, acdHdrSM, CKADef.atInit,
    SPComp.bind_assoc, SPComp.pure_bind]
  rfl

end Pair

section Bounds

variable [Fintype Sa] [Nonempty Sa] [DecidableEq RK] [Fintype G] [Nonempty G] [DecidableEq G]
  [DecidableEq A]

omit [Fintype Sa] [Nonempty Sa] [DecidableEq RK] [Fintype G] [Nonempty G] [DecidableEq G]
  [DecidableEq A] in
/-- **The corruption game of the extracted double ratchet is that of the ACD construction.**
Under `DrHom`, the advantage of an adversary `A` against `drExtractedSM` is the advantage in
`sm_corrupt_game (dhCKAOf G decE) R F D` of the wrapper adversary `toHdr (drHdrAD adOf)` of `A`
with the answers encoded and relabelled. -/
theorem drExtracted_corruptAdvantage_eq
    (h : DrHom Dp G R F D ptLen encR encG encSk decE encS encW encPt encC encAD (drEncH encG))
    (ΔFS ΔPCS : ℕ) (A : SMSchemeAdv (Array Int) W (Array Int) DrLeak) :
    (drExtractedSM Dp RK ptLen encR encG encSk decE encPt encC encAD adOf).corruptAdvantage
        ΔFS ΔPCS A =
      SM_Corrupt_Advantage (dhCKAOf G decE) R F D ΔFS ΔPCS
        ((A.comap encG encC (drEncLeak encR encG encSk decE encS)).toHdr (drHdrAD adOf)) := by
  rw [(drExtracted_sim Dp h).corruptAdvantage_eq,
    acdHdrSM_corruptAdvantage_eq (dhCKAOf G decE) (dhCKAOf_correct G decE) (dhInitPOf G decE)
      (dhCKAOf_init_eq G decE) (dhInitPOf_rel G decE)]

/-- **Forward secrecy and post-compromise security of the store-free abstraction `drExtractedSM`**
of the extracted double ratchet, for corruptions that return the key material `drExpose`. Under
`DrHom`, with `2 ≤ ΔFS` and `1 ≤ ΔPCS`, for an adversary `A` whose interactions ask at most `q`
queries, the advantage in the corruption game over `drExtractedSM` is at most the CKA
corruption advantages of `smcCKARed`, the PRF-PRNG advantages of the root KDF `R` at
`smcRootRed`, the PRG advantages of `F` at `fsCorrPRGRed` for the `q` positions and both bits,
and the AEAD advantage of `D` at `fsCorrAEADRed`, for the CKA `dhCKAOf G decE` and the wrapper
adversary `toHdr (drHdrAD adOf)` of `A` with the answers encoded and relabelled. -/
theorem drExtracted_corruptAdvantage_le
    (h : DrHom Dp G R F D ptLen encR encG encSk decE encS encW encPt encC encAD (drEncH encG))
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS)
    (A : SMSchemeAdv (Array Int) W (Array Int) DrLeak) (q : ℕ)
    (hA : ∀ t T, (A.play t T).IsQueryBound q) :
    (drExtractedSM Dp RK ptLen encR encG encSk decE encPt encC encAD adOf).corruptAdvantage
        ΔFS ΔPCS A ≤
      ∑ b : Bool, CKA_Corrupt_Advantage (dhCKAOf G decE) ΔFS ΔPCS (smcCKARed R F D b
          ((A.comap encG encC (drEncLeak encR encG encSk decE encS)).toHdr (drHdrAD adOf))) +
        ∑ b : Bool, PRFPRNG_Advantage R (smcRootRed (dhCKAOf G decE) R F D ΔFS ΔPCS b
          (dhInitPOf G decE)
          ((A.comap encG encC (drEncLeak encR encG encSk decE encS)).toHdr (drHdrAD adOf))) +
        (∑ i ∈ Finset.range q, PRG_Advantage F (fsCorrPRGRed F D false i
            (smcFSRed (dhCKAOf G decE) R F D ΔFS ΔPCS (dhInitPOf G decE)
              ((A.comap encG encC (drEncLeak encR encG encSk decE encS)).toHdr
                (drHdrAD adOf)))) +
          ∑ i ∈ Finset.range q, PRG_Advantage F (fsCorrPRGRed F D true i
            (smcFSRed (dhCKAOf G decE) R F D ΔFS ΔPCS (dhInitPOf G decE)
              ((A.comap encG encC (drEncLeak encR encG encSk decE encS)).toHdr
                (drHdrAD adOf)))) +
          AEAD_CCA_Advantage D (fsCorrAEADRed F D
            (smcFSRed (dhCKAOf G decE) R F D ΔFS ΔPCS (dhInitPOf G decE)
              ((A.comap encG encC (drEncLeak encR encG encSk decE encS)).toHdr
                (drHdrAD adOf))))) := by
  rw [(drExtracted_sim Dp h).corruptAdvantage_eq]
  exact acdHdrSM_corruptAdvantage_le_prim (dhCKAOf G decE) (dhCKAOfCoins_sound G decE)
    (dhCKAOf_correct G decE) (dhInitPOf G decE) (dhCKAOf_init_eq G decE) (dhInitPOf_rel G decE)
    R F D (drHdrAD adOf) hFS hPCS _ q (SMSchemeAdv.comap_play_isQueryBound hA)

end Bounds

end Sim

end CatCrypt.Crypto.Signal.DoubleRatchet.ExtractedScheme

namespace CatCrypt.Crypto.Signal.DoubleRatchet.ExtractedScheme

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Messaging
open CatCrypt.Crypto.Assumptions CatCryptCore.Examples.CyclicGroupDDH
open CatCrypt.Crypto.Signal.DoubleRatchet.ExtractedCorrespondence
open Doubleratchet

section Adaptive

variable (Dp : Type) [Inhabited Dp] [DoubleRatchetDeps Dp]
  {RK Sa W Ct Sk A : Type} [SampleableType W] {G : Type} [CG : CyclicGroup G]
  [Fintype RK] [Nonempty RK] [Fintype Sk] [Nonempty Sk] [SampleableType Ct]
  [Fintype Sa] [Nonempty Sa] [DecidableEq RK] [Fintype G] [Nonempty G] [DecidableEq G]
  {R : PRGDef (RK × G) (RK × Sa)} {F : PRGDef Sa (W × Sa)}
  {D : AEADDef W Ct (A × ((G × ℕ) × ℕ))} {ptLen : Int} {encR : RK → Array Int}
  {encG : G → Array Int} {encSk : Sk → Array Int} {decE : Sk → CG.Exp} {encS : Sa → Array Int}
  {encW : W → Array Int} {encPt : W → Array Int} {encC : Ct → Array Int}
  {encAD : A → Array Int} {adOf : W → A}

/-- **The store-free abstraction `drExtractedSM` with an adaptive challenge epoch**, for
corruptions that return the key material `drExpose`. Under `DrHom`, with
`2 ≤ ΔFS` and `1 ≤ ΔPCS`, the advantage of every adversary `A` in the game over `drExtractedSM`
with an adaptive challenge epoch is at most the sum over the epochs `e` of the CKA, PRF-PRNG and
FS-AEAD terms at the guessing reduction `smGuessAdv ΔFS ΔPCS _ e` of the wrapper adversary
`smHdrAdaptive (drHdrAD adOf)` of `A` with the answers encoded and relabelled. -/
theorem drExtracted_adaptiveAdvantage_le
    (h : DrHom Dp G R F D ptLen encR encG encSk decE encS encW encPt encC encAD (drEncH encG))
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS)
    (A : Array Int → OracleAdv (SMQuery W) (SMSchemeAns (Array Int) (Array Int) DrLeak) Bool) :
    (drExtractedSM Dp RK ptLen encR encG encSk decE encPt encC encAD adOf).adaptiveAdvantage
        ΔFS ΔPCS A ≤
      ∑' e, (∑ b : Bool, CKA_Corrupt_Advantage (dhCKAOf G decE) ΔFS ΔPCS
            (smcCKARed R F D b (smGuessAdv ΔFS ΔPCS (smHdrAdaptive (drHdrAD adOf)
              fun T => (A (encG T)).mapQueryAnswer id
                (SMSchemeAns.map encG encC (drEncLeak encR encG encSk decE encS))) e)) +
        ∑ b : Bool, PRFPRNG_Advantage R (smcRootRed (dhCKAOf G decE) R F D ΔFS ΔPCS b
          (dhInitPOf G decE) (smGuessAdv ΔFS ΔPCS (smHdrAdaptive (drHdrAD adOf)
            fun T => (A (encG T)).mapQueryAnswer id
              (SMSchemeAns.map encG encC (drEncLeak encR encG encSk decE encS))) e)) +
        FSAEAD_Corrupt_Advantage F D (smcFSRed (dhCKAOf G decE) R F D ΔFS ΔPCS
          (dhInitPOf G decE) (smGuessAdv ΔFS ΔPCS (smHdrAdaptive (drHdrAD adOf)
            fun T => (A (encG T)).mapQueryAnswer id
              (SMSchemeAns.map encG encC (drEncLeak encR encG encSk decE encS))) e))) := by
  rw [(drExtracted_sim Dp h).adaptiveAdvantage_eq,
    acdHdrSM_adaptiveAdvantage_eq (dhCKAOf G decE) (dhCKAOf_correct G decE) (dhInitPOf G decE)
      (dhCKAOf_init_eq G decE) (dhInitPOf_rel G decE)]
  exact sm_adaptive_corrupt_advantage_le (dhCKAOf G decE) (dhCKAOfCoins_sound G decE)
    (dhInitPOf G decE) (dhCKAOf_init_eq G decE) R F D hFS hPCS _

end Adaptive

end CatCrypt.Crypto.Signal.DoubleRatchet.ExtractedScheme
