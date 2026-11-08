/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.PQXDH.SquareCorrespondence

/-!
# The multi-session PQXDH game over the extracted functions

`extGame P H coins encS encW encPK encSK encC encSS encM decW decC decK` is the real game of the
square model `CatCryptCore.Crypto.AKE.PQXDHSquare` at the fixed key derivation `fixedKDF H`, in
which the adversary steps use the extracted functions of the Rust crate `pqxdh-hax` in the
`Pqxdh.PqxdhDeps` instance in scope. The honest step is `pqHonK P (fixedKDF H)`. The state is
that of the square model with the key-derivation state `Unit`; the KEM key pairs of responder
sessions are drawn from `P.keygen`, and the encapsulation randomness of an initiator from
`coins`. At each adversary call the values of the state are encoded, and the results of the
extracted functions are decoded by `decW`, `decC` and `decK`:
* the public keys read by the adversary are `decW (Pqxdh.dh_pub (encS x))`;
* an initiator completes by `Pqxdh.initiate` on the bundle of the encoded public keys and the
  encoded KEM public key of the responder, signed by `Pqxdh.sign` as in `Pqxdh.create_bundle`,
  and the encoded randomness, with the one-time prekey; it records the decoded encapsulation of
  its message;
* a responder completes by `Pqxdh.respond` on the message of the encoded identity key of the
  initiator, the encoded ephemeral key and the encoded encapsulation;
* a query of the adversary to the key derivation is `Pqxdh.kdf` at the encoded input.

Under `PqxdhSquareHom G P encS encW encPK encSK encC encSS encM encK encaps coins H`, with
`decW`, `decC`, `decK` left inverses of `encW`, `encC`, `encK`, and a scheme `P` whose
decapsulation accepts every encapsulation (implicit rejection), the game is
`realGameK P (fixedKDF H) G` (`extGame_eq`), so its system is `pqxdhRealK P (fixedKDF H) G`
(`extSys_eq`).

## Main definitions

* `extComplete`, `extSend`, `extAdv` — the adversary steps of the game.
* `extGame` — the game.

## Main results

* `extComplete_eq`, `extSend_eq`, `extAdv_eq` — each step is the step of
  `realGameK P (fixedKDF H) G`.
* `extGame_eq`, `extSys_eq` — the game and its system are those of the square model.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.PQXDH.ExtractedGame

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract (DHGroup)
open CatCrypt.Crypto.AKE.X3DHSquare (Inp aliceInp bobInp RSt ROut ltAt keyed realHon
  ephPubOf opkOf corruptRStep realAdv fixedKDF rInit)
open CatCrypt.Crypto.AKE.PQXDHSquare
open CatCrypt.Crypto.AKE.PQXDH.SquareCorrespondence
open CatCrypt.Crypto.KEM.Games (Scheme)

variable {S W K PK SK SS C M : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Pqxdh.PqxdhDeps]

section Steps

variable (P : Scheme PK SK SS C) (H : PInp W SS → K) (coins : PMF M) (encS : S → Array Int)
  (encW : W → Array Int) (encPK : PK → Array Int) (encSK : SK → Array Int) (encC : C → Array Int)
  (encSS : SS → Array Int) (encM : M → Array Int) (decW : Array Int → W)
  (decC : Array Int → C) (decK : Array Int → K)

/-- The bundle of the encoded secrets `ik`, `spk`, `opk` of a responder and its encoded KEM
public key `pk`, as `Pqxdh.create_bundle` forms it. -/
def extBundle (ik spk opk : S) (pk : PK) :
    Array Int × Array Int × Array Int × Array Int × Array Int × Array Int :=
  Pqxdh.PqxdhPreKeyBundle (Pqxdh.dh_pub (encS ik)) (Pqxdh.dh_pub (encS spk))
    (Pqxdh.dh_pub (encS opk)) (encPK pk) (Pqxdh.sign (encS ik) (Pqxdh.dh_pub (encS spk)))
    (Pqxdh.sign (encS ik) (Pqxdh.kem_pk_encode (encPK pk)))

/-- The completion of the initiator session `x = (sid, a)`: `Pqxdh.initiate` with the encoded
secrets of `a` on the bundle of the peer `b` and encoded randomness drawn from `coins`, with the
one-time prekey; the key is the decoding of its session key, and the decoded encapsulation of
its message is recorded. -/
noncomputable def extComplete (s : PStT S W K PK SK C Unit) (x : Inst) :
    PMF (POut S W K PK C × PStT S W K PK SK C Unit) :=
  match s.x.st.recs x, s.x.eph x with
  | some r, some ek =>
    match opkOf s.x x.1 r.peer, pkOf s x.1 r.peer with
    | some opk, some pk =>
      if r.role = .initiator ∧ r.key.isNone then
        (ltAt s.x x.2).bind fun la => (ltAt la.2 r.peer).bind fun lb =>
          coins.map fun m =>
            let o := Pqxdh.initiate (encS la.1.1) (encS ek)
              (extBundle encS encPK lb.1.1 lb.1.2 opk pk) (encM m) true
            let ct := Function.update s.ct x (some (decC o.2.1.2.2.1))
            (.inl .ack, pKeyed { s with x := lb.2, ct := ct } x r (decK o.1) ())
      else PMF.pure (.inl .ack, s)
    | _, _ => PMF.pure (.inl .ack, s)
  | _, _ => PMF.pure (.inl .ack, s)

/-- The completion of the responder session `x = (sid, b)` on the ephemeral public key `e` and
the encapsulation `c`: `Pqxdh.respond` with the encoded secrets of `b` and its encoded KEM secret
key, on the message of the encoded identity key `Pqxdh.dh_pub` of the peer `a`, the encoded `e`
and the encoded `c`, with the one-time prekey; the key is the decoding of its result. -/
noncomputable def extSend (s : PStT S W K PK SK C Unit) (x : Inst) (e : W) (c : C) :
    PMF (POut S W K PK C × PStT S W K PK SK C Unit) :=
  match s.x.st.recs x, s.x.eph x, s.kem x with
  | some r, some opk, some kp =>
    if r.role = .responder ∧ r.key.isNone then
      (ltAt s.x x.2).bind fun lb => (ltAt lb.2 r.peer).bind fun la =>
        PMF.pure (.inl .ack, pKeyed { s with x := la.2 } x r
          (decK (Pqxdh.respond (encS lb.1.1) (encS lb.1.2) (encS opk) (encSK kp.2)
            (Pqxdh.dh_pub (encS la.1.1), encW e, encC c, #[0, 0, 0, 1]) true)) ())
    else PMF.pure (.inl .ack, s)
  | _, _, _ => PMF.pure (.inl .ack, s)

/-- A step of the adversary port. -/
noncomputable def extAdv (s : PStT S W K PK SK C Unit) :
    PAEv W SS C → PMF (POut S W K PK C × PStT S W K PK SK C Unit)
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
  | .complete sid pid => extComplete coins encS encPK encM decC decK s (sid, pid)
  | .send sid pid e c => extSend encS encW encSK encC decK s (sid, pid) e c
  | .kdf i => PMF.pure (.inl (.hash (decK (Pqxdh.kdf (encW i.1.dh1) (encW i.1.dh2)
      (encW i.1.dh3) (encW i.1.dh4) (encSS i.2)))), s)

/-- **The PQXDH game over the extracted functions**: a trivial key, the honest step is that of
the square model at the fixed key derivation `H`, and the adversary step is the step of the
protocol whose cryptographic operations are the extracted functions. -/
noncomputable def extGame : KeyedGame (HEv ⊕ PAEv W SS C) (HOut K ⊕ POut S W K PK C) where
  Key := Unit
  State := PStT S W K PK SK C Unit
  keyDist := PMF.pure ()
  oracle _ s
    | .inl h => (pqHonK P (fixedKDF H) s h).map fun p => (.inl p.1, p.2)
    | .inr a => (extAdv coins encS encW encPK encSK encC encSS encM decW decC decK s a).map
        fun p => (.inr p.1, p.2)
  init := ⟨rInit, fun _ => none, fun _ => none, ()⟩

end Steps

variable {G : DHGroup S W} {P : Scheme PK SK SS C} {encS : S → Array Int}
  {encW : W → Array Int} {encPK : PK → Array Int} {encSK : SK → Array Int}
  {encC : C → Array Int} {encSS : SS → Array Int} {encM : M → Array Int}
  {encK : K → Array Int} {encaps : PK → M → SS × C} {coins : PMF M} {H : PInp W SS → K}
  {decW : Array Int → W} {decC : Array Int → C} {decK : Array Int → K}

omit [DecidableEq W] [Fintype K] [Nonempty K] in
/-- The completion of an initiator is that of the square model with the key derivation `H`. -/
theorem extComplete_eq
    (h : PqxdhSquareHom G P encS encW encPK encSK encC encSS encM encK encaps coins H)
    (hC : ∀ c, decC (encC c) = c) (hK : ∀ k, decK (encK k) = k)
    (s : PStT S W K PK SK C Unit) (x : Inst) :
    extComplete coins encS encPK encM decC decK s x = pqCompleteK P (fixedKDF H) G s x := by
  unfold extComplete pqCompleteK
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
          · simp only [h.encaps_coins pk, PMF.bind_map, extBundle, Pqxdh.PqxdhPreKeyBundle,
              h.dh_pub, initiate_square_enc h x.1 x.2 r.peer, initiate_msg_square_enc h, hK, hC,
              fixedKDF, PMF.pure_map, Function.comp_def]
            rfl
          · rfl

omit [DecidableEq W] [Fintype K] [Nonempty K] in
/-- The completion of a responder is that of the square model with the key derivation `H`, for a
scheme whose decapsulation accepts every encapsulation. -/
theorem extSend_eq
    (h : PqxdhSquareHom G P encS encW encPK encSK encC encSS encM encK encaps coins H)
    (hK : ∀ k, decK (encK k) = k) (hdec : ∀ sk c, ∃ ss, P.decaps sk c = some ss)
    (s : PStT S W K PK SK C Unit) (x : Inst) (e : W) (c : C) :
    extSend encS encW encSK encC decK s x e c = pqSendK P (fixedKDF H) G s x e c := by
  unfold extSend pqSendK
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
        · have hr := fun IKA E ik spk opk' oid =>
            respond_square_enc h x.1 r.peer x.2 IKA E ik spk opk' kp.2 c ss hss oid
          simp only [h.dh_pub, hr, hK, fixedKDF, PMF.pure_map]
        · rfl

/-- The adversary step is the adversary step of the square model with the key derivation `H`. -/
theorem extAdv_eq
    (h : PqxdhSquareHom G P encS encW encPK encSK encC encSS encM encK encaps coins H)
    (hW : ∀ Y, decW (encW Y) = Y) (hC : ∀ c, decC (encC c) = c) (hK : ∀ k, decK (encK k) = k)
    (hdec : ∀ sk c, ∃ ss, P.decaps sk c = some ss) (s : PStT S W K PK SK C Unit)
    (e : PAEv W SS C) :
    extAdv coins encS encW encPK encSK encC encSS encM decW decC decK s e =
      pqAdvK P (fixedKDF H) G s e := by
  cases e with
  | complete sid pid => exact extComplete_eq h hC hK s _
  | send sid pid e c => exact extSend_eq h hK hdec s _ e c
  | kdf i => simp only [extAdv, pqAdvK, fixedKDF, h.kdf i.1.sid i.1.ini i.1.res, hK,
      PMF.pure_map]
  | _ => simp only [extAdv, pqAdvK, onX, realAdv, X3DHSquare.realAdvK, ephPubOf, h.dh_pub, hW,
      PMF.pure_map, PMF.map_comp, Function.comp_def]

/-- **The extracted game is the square model.** Under `PqxdhSquareHom`, with `decW`, `decC`,
`decK` left inverses of `encW`, `encC`, `encK` and a scheme whose decapsulation accepts every
encapsulation, the game over the extracted functions is the real PQXDH game of `P` and `G` with
the key derivation the fixed function `H`. -/
theorem extGame_eq
    (h : PqxdhSquareHom G P encS encW encPK encSK encC encSS encM encK encaps coins H)
    (hW : ∀ Y, decW (encW Y) = Y) (hC : ∀ c, decC (encC c) = c) (hK : ∀ k, decK (encK k) = k)
    (hdec : ∀ sk c, ∃ ss, P.decaps sk c = some ss) :
    extGame P H coins encS encW encPK encSK encC encSS encM decW decC decK =
      realGameK P (fixedKDF H) G := by
  have ho : (fun (_ : Unit) (s : PStT S W K PK SK C Unit) (q : HEv ⊕ PAEv W SS C) =>
      (extGame P H coins encS encW encPK encSK encC encSS encM decW decC decK).oracle () s q) =
      fun _ s q => (realGameK P (fixedKDF H) G).oracle () s q := by
    funext _ s q
    cases q with
    | inl e => simp only [extGame, realGameK]
    | inr e => simp only [extGame, realGameK, extAdv_eq h hW hC hK hdec]
  simp only [extGame, realGameK] at ho ⊢
  congr

/-- **The system of the extracted game** is the real PQXDH system of `P` and `G` with the key
derivation `H`. -/
theorem extSys_eq
    (h : PqxdhSquareHom G P encS encW encPK encSK encC encSS encM encK encaps coins H)
    (hW : ∀ Y, decW (encW Y) = Y) (hC : ∀ c, decC (encC c) = c) (hK : ∀ k, decK (encK k) = k)
    (hdec : ∀ sk c, ∃ ss, P.decaps sk c = some ss) :
    (OProt.oracle (Q := HEv ⊕ PAEv W SS C) (A := HOut K ⊕ POut S W K PK C)).sys
        (extGame P H coins encS encW encPK encSK encC encSS encM decW decC decK) =
      pqxdhRealK P (fixedKDF H) G := by
  have key : ∀ G₁ G₂ : KeyedGame (HEv ⊕ PAEv W SS C) (HOut K ⊕ POut S W K PK C), G₁ = G₂ →
      (OProt.oracle (Q := HEv ⊕ PAEv W SS C) (A := HOut K ⊕ POut S W K PK C)).sys G₁ ≍
        (OProt.oracle (Q := HEv ⊕ PAEv W SS C) (A := HOut K ⊕ POut S W K PK C)).sys G₂ := by
    rintro _ _ rfl
    rfl
  exact eq_of_heq (key _ _ (extGame_eq h hW hC hK hdec))

end CatCrypt.Crypto.AKE.PQXDH.ExtractedGame
