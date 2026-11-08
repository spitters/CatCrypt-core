/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.PQXDH.SquareCorrespondence
public import CatCryptCore.Crypto.AKE.PQXDHSquareGDH

/-!
# The multi-session PQXDH game over the extracted functions

`extGameK P k coins encS encW encPK encSK encC encSS encM decW decC decSS` is the real game of the
square model `CatCryptCore.Crypto.AKE.PQXDHSquare` at a key-derivation operation
`k : KDFOp T (PInp W SS) K`, in which the adversary steps use the extracted functions of the Rust
crate `pqxdh-hax` in the `Pqxdh.PqxdhDeps` instance in scope, with the call of the key
derivation answered by `k`. The honest step is `pqHonK P k`. The KEM key pairs of responder
sessions are drawn from `P.keygen`, and the encapsulation randomness of an initiator from
`coins`. At each adversary call the values of the state are encoded, and the results of the
extracted functions are decoded by `decW`, `decC` and `decSS`:
* the public keys read by the adversary are `decW (Pqxdh.dh_pub (encS x))`;
* an initiator completes on the bundle of the encoded public keys and the encoded KEM public key
  of the responder, signed by `Pqxdh.sign` as in `Pqxdh.create_bundle`, and the encoded
  randomness, with the one-time prekey; it records the decoded encapsulation of the message of
  `Pqxdh.initiate`, and its key is `k.derive` at the session context and the decoded arguments
  of the key derivation of `Pqxdh.initiate` (`initKdfInp`, `initiate_key`);
* a responder completes on the message of the encoded identity key of the initiator, the encoded
  ephemeral key and the encoded encapsulation; its key is `k.derive` at the session context and
  the decoded arguments of the key derivation of `Pqxdh.respond` (`respKdfInp`, `respond_key`);
* a query of the adversary to the key derivation is `k.query`.

`extGame P coins encS encW encPK encSK encC encSS encM decW decC decSS decK` is the game at the
fixed key derivation `extKDF`, the extracted `Pqxdh.kdf` at encoded inputs decoded by `decK`.

Under `PqxdhSquareHom G P encS encW encPK encSK encC encSS encM encK encaps coins H`, with `decW`,
`decC`, `decSS` left inverses of `encW`, `encC`, `encSS`, and a scheme `P` whose decapsulation
accepts every encapsulation (implicit rejection), the game at every `k` is `realGameK P k G`
(`extGameK_eq`), so its system is `pqxdhRealK P k G` (`extSysK_eq`). At the lazily sampled random
function `lazyKDF` this is the random-oracle model, and the extracted system realizes `F_AKE`
behind `pqxdhSim P G` with the gap Diffie–Hellman bound of the square model
(`extSysK_lazy_realizesSim_gapDH`). With `decK` a left inverse of `encK`, `extKDF` is `H`
(`extKDF_eq`), so `extGame` is `realGameK P (fixedKDF H) G` (`extGame_eq`, `extSys_eq`), and its
session keys are the decoded keys of `Pqxdh.initiate` and `Pqxdh.respond` (`extKDF_initKdfInp`,
`extKDF_respKdfInp`).

## Main definitions

* `extBundle` — the bundle of a responder as `Pqxdh.create_bundle` forms it.
* `initKdfInp`, `respKdfInp` — the decoded input of the key derivation.
* `extKDF` — the extracted key derivation at encodings.
* `extCompleteK`, `extSendK`, `extAdvK` — the adversary steps of the game.
* `extGameK`, `extGame` — the game at a key-derivation operation and at `extKDF`.

## Main results

* `initiate_key`, `respond_key` — the extracted keys are `Pqxdh.kdf` at the encoded arguments
  that `initKdfInp` and `respKdfInp` decode.
* `extCompleteK_eq`, `extSendK_eq`, `extAdvK_eq` — each step is the step of `realGameK P k G`.
* `extGameK_eq`, `extSysK_eq` — the game and its system are those of the square model at `k`.
* `extSysK_lazy_realizesSim_gapDH` — the random-oracle-model statement.
* `extKDF_eq`, `extGame_eq`, `extSys_eq` — the game at the extracted key derivation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.PQXDH.ExtractedGame

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract (DHGroup)
open CatCrypt.Crypto.AKE.X3DHSquare (Inp aliceInp bobInp RSt ROut ltAt keyed realHon
  ephPubOf opkOf corruptRStep realAdv fixedKDF lazyKDF KDFOp rInit)
open CatCrypt.Crypto.AKE.PQXDHSquare
open CatCrypt.Crypto.AKE.PQXDH.SquareCorrespondence
open CatCrypt.Crypto.KEM.Games (Scheme)

variable {S W K PK SK SS C M : Type} [Field S] [Fintype S] [Pqxdh.PqxdhDeps]

section Inputs

variable (encS : S → Array Int) (encPK : PK → Array Int) (decW : Array Int → W)
  (decSS : Array Int → SS)

/-- The bundle of the encoded secrets `ik`, `spk`, `opk` of a responder and its encoded KEM
public key `pk`, as `Pqxdh.create_bundle` forms it. -/
def extBundle (ik spk opk : S) (pk : PK) :
    Array Int × Array Int × Array Int × Array Int × Array Int × Array Int :=
  Pqxdh.PqxdhPreKeyBundle (Pqxdh.dh_pub (encS ik)) (Pqxdh.dh_pub (encS spk))
    (Pqxdh.dh_pub (encS opk)) (encPK pk) (Pqxdh.sign (encS ik) (Pqxdh.dh_pub (encS spk)))
    (Pqxdh.sign (encS ik) (Pqxdh.kem_pk_encode (encPK pk)))

/-- The input of the key derivation of `Pqxdh.initiate` with the one-time prekey at the session
context `c`, the encoded secrets `ik`, `ek`, the bundle `b` and the randomness `m`: the context,
the four decoded Diffie–Hellman values and the decoded encapsulated secret. -/
def initKdfInp (c : SessionId × PartyId × PartyId) (ik ek : Array Int)
    (b : Array Int × Array Int × Array Int × Array Int × Array Int × Array Int)
    (m : Array Int) : PInp W SS :=
  (⟨c.1, c.2.1, c.2.2, decW (Pqxdh.dh ik (Pqxdh.«.spk» b)), decW (Pqxdh.dh ek (Pqxdh.«.ik» b)),
    decW (Pqxdh.dh ek (Pqxdh.«.spk» b)), decW (Pqxdh.dh ek (Pqxdh.«.opk» b))⟩,
    decSS (Pqxdh.kem_encaps (Pqxdh.«.pqpk» b) m).2)

/-- The input of the key derivation of `Pqxdh.respond` with the one-time prekey at the session
context `c`, the encoded secrets `ik`, `spk`, `opk`, `sk` and the message `msg`: the context, the
four decoded Diffie–Hellman values and the decoded decapsulated secret. -/
def respKdfInp (c : SessionId × PartyId × PartyId) (ik spk opk sk : Array Int)
    (msg : Array Int × Array Int × Array Int × Array Int) : PInp W SS :=
  (⟨c.1, c.2.1, c.2.2, decW (Pqxdh.dh spk (Pqxdh.«.ik_a» msg)),
    decW (Pqxdh.dh ik (Pqxdh.«.ek_a» msg)), decW (Pqxdh.dh spk (Pqxdh.«.ek_a» msg)),
    decW (Pqxdh.dh opk (Pqxdh.«.ek_a» msg))⟩, decSS (Pqxdh.kem_decaps sk (Pqxdh.«.kem_ct» msg)))

end Inputs

/-- The key of `Pqxdh.initiate` with the one-time prekey is `Pqxdh.kdf` at the arguments that
`initKdfInp` decodes. -/
theorem initiate_key (ik ek : Array Int)
    (b : Array Int × Array Int × Array Int × Array Int × Array Int × Array Int) (m : Array Int) :
    (Pqxdh.initiate ik ek b m true).1 =
      Pqxdh.kdf (Pqxdh.dh ik (Pqxdh.«.spk» b)) (Pqxdh.dh ek (Pqxdh.«.ik» b))
        (Pqxdh.dh ek (Pqxdh.«.spk» b)) (Pqxdh.dh ek (Pqxdh.«.opk» b))
        (Pqxdh.kem_encaps (Pqxdh.«.pqpk» b) m).2 := by
  simp only [Pqxdh.initiate, ↓reduceIte]

/-- The key of `Pqxdh.respond` with the one-time prekey is `Pqxdh.kdf` at the arguments that
`respKdfInp` decodes. -/
theorem respond_key (ik spk opk sk : Array Int)
    (msg : Array Int × Array Int × Array Int × Array Int) :
    Pqxdh.respond ik spk opk sk msg true =
      Pqxdh.kdf (Pqxdh.dh spk (Pqxdh.«.ik_a» msg)) (Pqxdh.dh ik (Pqxdh.«.ek_a» msg))
        (Pqxdh.dh spk (Pqxdh.«.ek_a» msg)) (Pqxdh.dh opk (Pqxdh.«.ek_a» msg))
        (Pqxdh.kem_decaps sk (Pqxdh.«.kem_ct» msg)) := by
  simp only [Pqxdh.respond, ↓reduceIte]

/-- **The extracted key derivation** at encodings: `Pqxdh.kdf` at the encoded Diffie–Hellman
values and the encoded shared secret of an input, decoded by `decK`. -/
def extKDF (encW : W → Array Int) (encSS : SS → Array Int) (decK : Array Int → K)
    (i : PInp W SS) : K :=
  decK (Pqxdh.kdf (encW i.1.dh1) (encW i.1.dh2) (encW i.1.dh3) (encW i.1.dh4) (encSS i.2))

section Steps

variable [DecidableEq W] [Fintype K] [Nonempty K] {T : Type} (P : Scheme PK SK SS C)
  (k : KDFOp T (PInp W SS) K) (coins : PMF M) (encS : S → Array Int)
  (encW : W → Array Int) (encPK : PK → Array Int) (encSK : SK → Array Int) (encC : C → Array Int)
  (encM : M → Array Int) (decW : Array Int → W) (decC : Array Int → C) (decSS : Array Int → SS)

/-- The completion of the initiator session `x = (sid, a)`: `Pqxdh.initiate` with the encoded
secrets of `a` on the bundle of the peer `b` and encoded randomness drawn from `coins`, with the
one-time prekey; the decoded encapsulation of its message is recorded, and the key is `k.derive`
at the decoded input of its key derivation. -/
noncomputable def extCompleteK (s : PStT S W K PK SK C T) (x : Inst) :
    PMF (POut S W K PK C × PStT S W K PK SK C T) :=
  match s.x.st.recs x, s.x.eph x with
  | some r, some ek =>
    match opkOf s.x x.1 r.peer, pkOf s x.1 r.peer with
    | some opk, some pk =>
      if r.role = .initiator ∧ r.key.isNone then
        (ltAt s.x x.2).bind fun la => (ltAt la.2 r.peer).bind fun lb =>
          coins.bind fun m =>
            let o := Pqxdh.initiate (encS la.1.1) (encS ek)
              (extBundle encS encPK lb.1.1 lb.1.2 opk pk) (encM m) true
            let ct := Function.update s.ct x (some (decC o.2.1.2.2.1))
            (k.derive s.ro x (initKdfInp decW decSS (x.1, x.2, r.peer) (encS la.1.1) (encS ek)
              (extBundle encS encPK lb.1.1 lb.1.2 opk pk) (encM m))).map fun q =>
                (.inl .ack, pKeyed { s with x := lb.2, ct := ct } x r q.1 q.2)
      else PMF.pure (.inl .ack, s)
    | _, _ => PMF.pure (.inl .ack, s)
  | _, _ => PMF.pure (.inl .ack, s)

/-- The completion of the responder session `x = (sid, b)` on the ephemeral public key `e` and
the encapsulation `c`: the key is `k.derive` at the decoded input of the key derivation of
`Pqxdh.respond` with the encoded secrets of `b` and its encoded KEM secret key, on the message of
the encoded identity key `Pqxdh.dh_pub` of the peer `a`, the encoded `e` and the encoded `c`,
with the one-time prekey. -/
noncomputable def extSendK (s : PStT S W K PK SK C T) (x : Inst) (e : W) (c : C) :
    PMF (POut S W K PK C × PStT S W K PK SK C T) :=
  match s.x.st.recs x, s.x.eph x, s.kem x with
  | some r, some opk, some kp =>
    if r.role = .responder ∧ r.key.isNone then
      (ltAt s.x x.2).bind fun lb => (ltAt lb.2 r.peer).bind fun la =>
        (k.derive s.ro x (respKdfInp decW decSS (x.1, r.peer, x.2) (encS lb.1.1) (encS lb.1.2)
          (encS opk) (encSK kp.2) (Pqxdh.dh_pub (encS la.1.1), encW e, encC c,
            #[0, 0, 0, 1]))).map fun q => (.inl .ack, pKeyed { s with x := la.2 } x r q.1 q.2)
    else PMF.pure (.inl .ack, s)
  | _, _, _ => PMF.pure (.inl .ack, s)

/-- A step of the adversary port; a query to the key derivation is answered by `k.query`. -/
noncomputable def extAdvK (s : PStT S W K PK SK C T) :
    PAEv W SS C → PMF (POut S W K PK C × PStT S W K PK SK C T)
  | .idle => PMF.pure (.inl .ack, s)
  | .poll => PMF.pure (.inl (.notice (pollStep s.x.st).2),
      { s with x := { s.x with st := (pollStep s.x.st).1 } })
  | .pub pid => (ltAt s.x pid).map fun l =>
      (.inl (.pub (decW (Pqxdh.dh_pub (encS l.1.1))) (decW (Pqxdh.dh_pub (encS l.1.2)))),
        { s with x := l.2 })
  | .ephPub sid pid => PMF.pure
      (.inl (.eph ((s.x.eph (sid, pid)).map fun y => decW (Pqxdh.dh_pub (encS y)))), s)
  | .pqPub sid pid => PMF.pure (.inr (pkOf s sid pid, s.ct (sid, pid)), s)
  | .corrupt pid => onX s (corruptRStep s.x pid)
  | .complete sid pid => extCompleteK k coins encS encPK encM decW decC decSS s (sid, pid)
  | .send sid pid e c => extSendK k encS encW encSK encC decW decSS s (sid, pid) e c
  | .kdf i => (k.query s.ro i).map fun p => (.inl (.hash p.1), { s with ro := p.2 })

/-- **The PQXDH game over the extracted functions at the key derivation `k`**: a trivial key,
the honest step is that of the square model at `k`, and the adversary step is the step of the
protocol whose cryptographic operations are the extracted functions, with the key derivation
answered by `k`. -/
noncomputable def extGameK : KeyedGame (HEv ⊕ PAEv W SS C) (HOut K ⊕ POut S W K PK C) where
  Key := Unit
  State := PStT S W K PK SK C T
  keyDist := PMF.pure ()
  oracle _ s
    | .inl h => (pqHonK P k s h).map fun p => (.inl p.1, p.2)
    | .inr a => (extAdvK k coins encS encW encPK encSK encC encM decW decC decSS s a).map
        fun p => (.inr p.1, p.2)
  init := ⟨rInit, fun _ => none, fun _ => none, k.init⟩

/-- **The PQXDH game over the extracted functions**, with the key derivation the extracted
`Pqxdh.kdf` at encodings (`extKDF`). -/
noncomputable def extGame (encSS : SS → Array Int) (decK : Array Int → K) :
    KeyedGame (HEv ⊕ PAEv W SS C) (HOut K ⊕ POut S W K PK C) :=
  extGameK P (fixedKDF (extKDF encW encSS decK)) coins encS encW encPK encSK encC encM decW decC
    decSS

end Steps

variable {G : DHGroup S W} {P : Scheme PK SK SS C} {encS : S → Array Int}
  {encW : W → Array Int} {encPK : PK → Array Int} {encSK : SK → Array Int}
  {encC : C → Array Int} {encSS : SS → Array Int} {encM : M → Array Int}
  {encK : K → Array Int} {encaps : PK → M → SS × C} {coins : PMF M} {H : PInp W SS → K}
  {decW : Array Int → W} {decC : Array Int → C} {decSS : Array Int → SS}
  {decK : Array Int → K} {T : Type} {k : KDFOp T (PInp W SS) K}

omit [Fintype S] in
/-- The decoded input of the initiator's key derivation at encoded secrets, a bundle of encoded
group elements with an encoded KEM public key, and encoded randomness is the initiator's input
`aliceInp` and the encapsulated secret. -/
theorem initKdfInp_square
    (h : PqxdhSquareHom G P encS encW encPK encSK encC encSS encM encK encaps coins H)
    (hW : ∀ Y, decW (encW Y) = Y) (hSS : ∀ ss, decSS (encSS ss) = ss)
    (c : SessionId × PartyId × PartyId) (ik ek : S) (IKB SPKB OPKB : W) (pk : PK) (m : M)
    (sig₁ sig₂ : Array Int) :
    initKdfInp decW decSS c (encS ik) (encS ek) (encW IKB, encW SPKB, encW OPKB, encPK pk, sig₁,
        sig₂) (encM m) =
      (aliceInp G c.1 c.2.1 c.2.2 ik ek IKB SPKB OPKB, (encaps pk m).1) := by
  simp only [initKdfInp, Pqxdh.«.ik», Pqxdh.«.spk», Pqxdh.«.opk», Pqxdh.«.pqpk», h.dh,
    h.kem_encaps, hW, hSS, aliceInp]

omit [Fintype S] in
/-- The decoded input of the responder's key derivation at encoded secrets and a message of
encoded group elements and an encapsulation `c` that `P` decapsulates under `sk` to `ss` is the
responder's input `bobInp` and `ss`. -/
theorem respKdfInp_square
    (h : PqxdhSquareHom G P encS encW encPK encSK encC encSS encM encK encaps coins H)
    (hW : ∀ Y, decW (encW Y) = Y) (hSS : ∀ ss, decSS (encSS ss) = ss)
    (c : SessionId × PartyId × PartyId) (IKA E : W) (ik spk opk : S) (sk : SK) (ct : C)
    (ss : SS) (hd : P.decaps sk ct = some ss) (oid : Array Int) :
    respKdfInp decW decSS c (encS ik) (encS spk) (encS opk) (encSK sk)
        (encW IKA, encW E, encC ct, oid) =
      (bobInp G c.1 c.2.1 c.2.2 IKA E ik spk opk, ss) := by
  simp only [respKdfInp, Pqxdh.«.ik_a», Pqxdh.«.ek_a», Pqxdh.«.kem_ct», h.dh,
    h.kem_decaps sk ct ss hd, hW, hSS, bobInp]

section Steps

variable [DecidableEq W] [Fintype K] [Nonempty K]

omit [DecidableEq W] [Fintype K] [Nonempty K] in
/-- The completion of an initiator is that of the square model with the key derivation `k`. -/
theorem extCompleteK_eq
    (h : PqxdhSquareHom G P encS encW encPK encSK encC encSS encM encK encaps coins H)
    (hW : ∀ Y, decW (encW Y) = Y) (hC : ∀ c, decC (encC c) = c)
    (hSS : ∀ ss, decSS (encSS ss) = ss) (s : PStT S W K PK SK C T) (x : Inst) :
    extCompleteK k coins encS encPK encM decW decC decSS s x = pqCompleteK P k G s x := by
  unfold extCompleteK pqCompleteK
  cases s.x.st.recs x with
  | none => rfl
  | some r =>
    cases s.x.eph x with
    | none => rfl
    | some ek =>
      dsimp only
      cases opkOf s.x x.1 r.peer with
      | none => rfl
      | some opk =>
        cases pkOf s x.1 r.peer with
        | none => rfl
        | some pk =>
          dsimp only
          split_ifs
          · simp only [extBundle, Pqxdh.PqxdhPreKeyBundle, h.dh_pub]
            simp only [h.encaps_coins pk, PMF.bind_map, initKdfInp_square h hW hSS,
              initiate_msg_square_enc h, hC, Function.comp_def]
          · rfl

omit [DecidableEq W] [Fintype K] [Nonempty K] in
/-- The completion of a responder is that of the square model with the key derivation `k`, for a
scheme whose decapsulation accepts every encapsulation. -/
theorem extSendK_eq
    (h : PqxdhSquareHom G P encS encW encPK encSK encC encSS encM encK encaps coins H)
    (hW : ∀ Y, decW (encW Y) = Y) (hSS : ∀ ss, decSS (encSS ss) = ss)
    (hdec : ∀ sk c, ∃ ss, P.decaps sk c = some ss)
    (s : PStT S W K PK SK C T) (x : Inst) (e : W) (c : C) :
    extSendK k encS encW encSK encC decW decSS s x e c = pqSendK P k G s x e c := by
  unfold extSendK pqSendK
  cases s.x.st.recs x with
  | none => rfl
  | some r =>
    cases s.x.eph x with
    | none => rfl
    | some opk =>
      cases s.kem x with
      | none => rfl
      | some kp =>
        dsimp only
        obtain ⟨ss, hss⟩ := hdec kp.2 c
        rw [hss]
        dsimp only
        split_ifs
        · simp only [h.dh_pub, respKdfInp_square h hW hSS _ _ _ _ _ _ kp.2 c ss hss]
        · rfl

/-- The adversary step is the adversary step of the square model with the key derivation `k`. -/
theorem extAdvK_eq
    (h : PqxdhSquareHom G P encS encW encPK encSK encC encSS encM encK encaps coins H)
    (hW : ∀ Y, decW (encW Y) = Y) (hC : ∀ c, decC (encC c) = c)
    (hSS : ∀ ss, decSS (encSS ss) = ss) (hdec : ∀ sk c, ∃ ss, P.decaps sk c = some ss)
    (s : PStT S W K PK SK C T) (e : PAEv W SS C) :
    extAdvK k coins encS encW encPK encSK encC encM decW decC decSS s e =
      pqAdvK P k G s e := by
  cases e with
  | complete sid pid => exact extCompleteK_eq h hW hC hSS s _
  | send sid pid e c => exact extSendK_eq h hW hSS hdec s _ e c
  | kdf i => rfl
  | _ => simp only [extAdvK, pqAdvK, onX, realAdv, X3DHSquare.realAdvK, ephPubOf, h.dh_pub, hW,
      PMF.pure_map, PMF.map_comp, Function.comp_def]

/-- **The extracted game is the square model at every key derivation.** Under `PqxdhSquareHom`,
with `decW`, `decC`, `decSS` left inverses of `encW`, `encC`, `encSS` and a scheme whose
decapsulation accepts every encapsulation, the game over the extracted functions at the key
derivation `k` is the real PQXDH game of `P` and `G` at `k`. -/
theorem extGameK_eq
    (h : PqxdhSquareHom G P encS encW encPK encSK encC encSS encM encK encaps coins H)
    (hW : ∀ Y, decW (encW Y) = Y) (hC : ∀ c, decC (encC c) = c)
    (hSS : ∀ ss, decSS (encSS ss) = ss) (hdec : ∀ sk c, ∃ ss, P.decaps sk c = some ss) :
    extGameK P k coins encS encW encPK encSK encC encM decW decC decSS = realGameK P k G := by
  have ho : (fun (_ : Unit) (s : PStT S W K PK SK C T) (q : HEv ⊕ PAEv W SS C) =>
      (extGameK P k coins encS encW encPK encSK encC encM decW decC decSS).oracle () s q) =
      fun _ s q => (realGameK P k G).oracle () s q := by
    funext _ s q
    cases q with
    | inl e => simp only [extGameK, realGameK]
    | inr e => simp only [extGameK, realGameK, extAdvK_eq h hW hC hSS hdec]
  simp only [extGameK, realGameK] at ho ⊢
  congr

/-- **The system of the extracted game at `k`** is the real PQXDH system of `P` and `G` with the
key derivation `k`. -/
theorem extSysK_eq
    (h : PqxdhSquareHom G P encS encW encPK encSK encC encSS encM encK encaps coins H)
    (hW : ∀ Y, decW (encW Y) = Y) (hC : ∀ c, decC (encC c) = c)
    (hSS : ∀ ss, decSS (encSS ss) = ss) (hdec : ∀ sk c, ∃ ss, P.decaps sk c = some ss) :
    (OProt.oracle (Q := HEv ⊕ PAEv W SS C) (A := HOut K ⊕ POut S W K PK C)).sys
        (extGameK P k coins encS encW encPK encSK encC encM decW decC decSS) =
      pqxdhRealK P k G := by
  have key : ∀ G₁ G₂ : KeyedGame (HEv ⊕ PAEv W SS C) (HOut K ⊕ POut S W K PK C), G₁ = G₂ →
      (OProt.oracle (Q := HEv ⊕ PAEv W SS C) (A := HOut K ⊕ POut S W K PK C)).sys G₁ ≍
        (OProt.oracle (Q := HEv ⊕ PAEv W SS C) (A := HOut K ⊕ POut S W K PK C)).sys G₂ := by
    rintro _ _ rfl
    rfl
  exact eq_of_heq (key _ _ (extGameK_eq h hW hC hSS hdec))

end Steps

/-- **The extracted PQXDH in the random-oracle model.** Under `PqxdhSquareHom`, with `decW`,
`decC`, `decSS` left inverses of `encW`, `encC`, `encSS` and a scheme `P` whose decapsulation
accepts every encapsulation (the implicit rejection of ML-KEM, FIPS 203), the system of the game
over the extracted functions with the key derivation the lazily sampled random function
`lazyKDF` realizes `F_AKE` behind `pqxdhSim P G`: for every finite set of parties `N` and every
environment `Z`, the distance is at most the gap Diffie–Hellman bound `gdhBoundP P G N` of the
square model at the oracle reduction of `Z` (`pqxdh_realizesSim_gapDH` transported by
`extSysK_eq`). -/
theorem extSysK_lazy_realizesSim_gapDH [SampleableType W] [Fintype K] [Nonempty K]
    [Inhabited K] [DecidableEq SS]
    (h : PqxdhSquareHom G P encS encW encPK encSK encC encSS encM encK encaps coins H)
    (hW : ∀ Y, decW (encW Y) = Y) (hC : ∀ c, decC (encC c) = c)
    (hSS : ∀ ss, decSS (encSS ss) = ss) (hdec : ∀ sk c, ∃ ss, P.decaps sk c = some ss)
    (N : Finset PartyId) :
    RealizesSim ((OProt.oracle (Q := HEv ⊕ PAEv W SS C) (A := HOut K ⊕ POut S W K PK C)).sys
        (extGameK P (lazyKDF (D := PInp W SS) (K := K)) coins encS encW encPK encSK encC encM
          decW decC decSS))
      (F_AKE (SPComp.sample K) true) (pqxdhSim P G)
      (fun _ Z => PQXDHSquareGDH.gdhBoundP P G N
        ((OProt.oracle (Q := OEv W SS C) (A := OOut S W K PK C)).reduction Z)) := by
  rw [extSysK_eq h hW hC hSS hdec]
  exact PQXDHSquareGDH.pqxdh_realizesSim_gapDH P G N

omit [Fintype S] in
/-- **The extracted key derivation is `H`.** Under `PqxdhSquareHom`, with `decK` a left inverse
of `encK`, `extKDF encW encSS decK` is `H`. -/
theorem extKDF_eq
    (h : PqxdhSquareHom G P encS encW encPK encSK encC encSS encM encK encaps coins H)
    (hK : ∀ k, decK (encK k) = k) :
    extKDF encW encSS decK = H := by
  funext i
  obtain ⟨⟨sid, a, b, d1, d2, d3, d4⟩, ss⟩ := i
  simp only [extKDF, h.kdf sid a b, hK]

omit [Fintype S] in
/-- At the extracted key derivation, the key of an initiator in the game is the decoded key of
`Pqxdh.initiate`. -/
theorem extKDF_initKdfInp
    (h : PqxdhSquareHom G P encS encW encPK encSK encC encSS encM encK encaps coins H)
    (hW : ∀ Y, decW (encW Y) = Y) (hSS : ∀ ss, decSS (encSS ss) = ss)
    (hK : ∀ k, decK (encK k) = k) (c : SessionId × PartyId × PartyId) (ik ek : S)
    (IKB SPKB OPKB : W) (pk : PK) (m : M) (sig₁ sig₂ : Array Int) :
    extKDF encW encSS decK (initKdfInp decW decSS c (encS ik) (encS ek)
        (encW IKB, encW SPKB, encW OPKB, encPK pk, sig₁, sig₂) (encM m)) =
      decK (Pqxdh.initiate (encS ik) (encS ek)
        (encW IKB, encW SPKB, encW OPKB, encPK pk, sig₁, sig₂) (encM m) true).1 := by
  rw [extKDF_eq h hK, initKdfInp_square h hW hSS, initiate_square_enc h c.1 c.2.1 c.2.2, hK]

omit [Fintype S] in
/-- At the extracted key derivation, the key of a responder in the game is the decoded key of
`Pqxdh.respond`, on an encapsulation that `P` decapsulates. -/
theorem extKDF_respKdfInp
    (h : PqxdhSquareHom G P encS encW encPK encSK encC encSS encM encK encaps coins H)
    (hW : ∀ Y, decW (encW Y) = Y) (hSS : ∀ ss, decSS (encSS ss) = ss)
    (hK : ∀ k, decK (encK k) = k) (c : SessionId × PartyId × PartyId) (IKA E : W)
    (ik spk opk : S) (sk : SK) (ct : C) (ss : SS) (hd : P.decaps sk ct = some ss)
    (oid : Array Int) :
    extKDF encW encSS decK (respKdfInp decW decSS c (encS ik) (encS spk) (encS opk) (encSK sk)
        (encW IKA, encW E, encC ct, oid)) =
      decK (Pqxdh.respond (encS ik) (encS spk) (encS opk) (encSK sk)
        (encW IKA, encW E, encC ct, oid) true) := by
  rw [extKDF_eq h hK, respKdfInp_square h hW hSS c IKA E ik spk opk sk ct ss hd,
    respond_square_enc h c.1 c.2.1 c.2.2 IKA E ik spk opk sk ct ss hd, hK]

section Fixed

variable [DecidableEq W] [Fintype K] [Nonempty K]

/-- **The extracted game is the square model.** Under `PqxdhSquareHom`, with `decW`, `decC`,
`decSS`, `decK` left inverses of `encW`, `encC`, `encSS`, `encK` and a scheme whose
decapsulation accepts every encapsulation, the game over the extracted functions is the real
PQXDH game of `P` and `G` with the key derivation the fixed function `H`. -/
theorem extGame_eq
    (h : PqxdhSquareHom G P encS encW encPK encSK encC encSS encM encK encaps coins H)
    (hW : ∀ Y, decW (encW Y) = Y) (hC : ∀ c, decC (encC c) = c)
    (hSS : ∀ ss, decSS (encSS ss) = ss) (hK : ∀ k, decK (encK k) = k)
    (hdec : ∀ sk c, ∃ ss, P.decaps sk c = some ss) :
    extGame P coins encS encW encPK encSK encC encM decW decC decSS encSS decK =
      realGameK P (fixedKDF H) G := by
  unfold extGame
  rw [extKDF_eq h hK]
  exact extGameK_eq h hW hC hSS hdec

/-- **The system of the extracted game** is the real PQXDH system of `P` and `G` with the key
derivation `H`. -/
theorem extSys_eq
    (h : PqxdhSquareHom G P encS encW encPK encSK encC encSS encM encK encaps coins H)
    (hW : ∀ Y, decW (encW Y) = Y) (hC : ∀ c, decC (encC c) = c)
    (hSS : ∀ ss, decSS (encSS ss) = ss) (hK : ∀ k, decK (encK k) = k)
    (hdec : ∀ sk c, ∃ ss, P.decaps sk c = some ss) :
    (OProt.oracle (Q := HEv ⊕ PAEv W SS C) (A := HOut K ⊕ POut S W K PK C)).sys
        (extGame P coins encS encW encPK encSK encC encM decW decC decSS encSS decK) =
      pqxdhRealK P (fixedKDF H) G := by
  unfold extGame
  rw [extKDF_eq h hK]
  exact extSysK_eq h hW hC hSS hdec

end Fixed

end CatCrypt.Crypto.AKE.PQXDH.ExtractedGame
