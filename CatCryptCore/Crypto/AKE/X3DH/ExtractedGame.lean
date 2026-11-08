/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DH.SquareCorrespondence
public import CatCryptCore.Crypto.AKE.X3DHSquareGDH

/-!
# The multi-session X3DH game over the extracted functions

`extGameK encCtx encS encW decW k` is the real game of the square model
`CatCryptCore.Crypto.AKE.X3DHSquare` at a key-derivation operation `k : KDFOp T (Inp W) K`, in
which the adversary steps use the extracted functions of the Rust crate `x3dh-hax` in the
`X3dh.X3dhDeps` instance in scope, with the call of the key derivation answered by `k`. The
honest step is `realHonK k`. The state holds the session records, the sampled scalars and the
state of `k`, as in `RStT S K T`; at each adversary call the scalars are encoded by `encS` and
the group elements by `encW`, and the results of the extracted functions are decoded by `decW`:
* the public keys read by the adversary are `decW (X3dh.dh_pub (encS x))`;
* an initiator completes when the input check of `X3dh.initiate` at the context
  `encCtx (sid, a, b)` accepts the bundle `X3dh.create_bundle` of the responder's encoded
  secrets, with the one-time prekey; its key is `k.derive` at the decoded arguments of the key
  derivation of `X3dh.initiate_checked` (`initKdfInp`, `initiate_checked_key`);
* a responder completes when the input check of `X3dh.respond` accepts the message of the
  initiator's encoded identity key `X3dh.dh_pub (encS ik)` and the encoded ephemeral key; its
  key is `k.derive` at the decoded arguments of the key derivation of `X3dh.respond_checked`
  (`respKdfInp`, `respond_checked_key`);
* a query of the adversary to the key derivation is `k.query`.
A rejection of the input check leaves the session without key.

`extGame encCtx encS encW decW decK` is the game at the fixed key derivation `extKDF`, the
extracted `X3dh.kdf` at encoded inputs decoded by `decK`.

Under `X3dhSquareHom G encCtx encS encW encK H`, with `decW` a left inverse of `encW`, the game
at every `k` is `realGameK k (x3dhAlg G)` (`extGameK_eq`), so its system is
`x3dhRealOfK k (x3dhAlg G)` (`extSysK_eq`). At the lazily sampled random function `lazyKDF` this
is the random-oracle model, and the extracted system realizes `F_AKE` behind `x3dhSim G` with the
gap Diffie–Hellman bound of the square model (`extSysK_lazy_realizesSim_gapDH`). With `decK` a
left inverse of `encK`, `extKDF` is `H` (`extKDF_eq`), so the game `extGame` is
`realGameK (fixedKDF H) (x3dhAlg G)` (`extGame_eq`, `extSys_eq`), and its session keys are the
decoded keys of `X3dh.initiate_checked` and `X3dh.respond_checked` (`extKDF_initKdfInp`,
`extKDF_respKdfInp`).

## Main definitions

* `kdfInp`, `initKdfInp`, `respKdfInp` — the decoded input of the key derivation.
* `extKDF` — the extracted key derivation at encodings.
* `extCompleteK`, `extSendK`, `extAdvK` — the adversary steps of the game.
* `extGameK`, `extGame` — the game at a key-derivation operation and at `extKDF`.

## Main results

* `initiate_checked_key`, `respond_checked_key` — the extracted keys are `X3dh.kdf` at the
  encoded arguments that `initKdfInp` and `respKdfInp` decode.
* `extCompleteK_eq`, `extSendK_eq`, `extAdvK_eq` — each step is the step of
  `realGameK k (x3dhAlg G)`.
* `extGameK_eq`, `extSysK_eq` — the game and its system are those of the square model at `k`.
* `extSysK_lazy_realizesSim_gapDH` — the random-oracle-model statement.
* `extKDF_eq`, `extGame_eq`, `extSys_eq` — the game at the extracted key derivation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.X3DH.ExtractedGame

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract (DHGroup)
open CatCrypt.Crypto.AKE.X3DHSquare
open CatCrypt.Crypto.AKE.X3DH.SquareCorrespondence

variable {S W K : Type} [Field S] [Fintype S] [Nonempty S] [X3dh.X3dhDeps]

section Inputs

variable (decW : Array Int → W)

/-- The input of the key derivation at the session context `c = (sid, a, b)` and the four
decoded Diffie–Hellman values. -/
def kdfInp (c : SessionId × PartyId × PartyId) (d1 d2 d3 d4 : Array Int) : Inp W :=
  ⟨c.1, c.2.1, c.2.2, decW d1, decW d2, decW d3, decW d4⟩

/-- The decoded input of the key derivation of `X3dh.initiate_checked` with the one-time prekey,
at the context `c`, the encoded secrets `ik`, `ek` and the bundle `b`. -/
def initKdfInp (c : SessionId × PartyId × PartyId) (ik ek : Array Int)
    (b : Array Int × Array Int × Array Int × Array Int) : Inp W :=
  kdfInp decW c (X3dh.dh ik (X3dh.«.spk» b)) (X3dh.dh ek (X3dh.«.ik» b))
    (X3dh.dh ek (X3dh.«.spk» b)) (X3dh.dh ek (X3dh.«.opk» b))

/-- The decoded input of the key derivation of `X3dh.respond_checked` with the one-time prekey,
at the context `c`, the encoded secrets `ik`, `spk`, `opk` and the message `m`. -/
def respKdfInp (c : SessionId × PartyId × PartyId) (ik spk opk : Array Int)
    (m : Array Int × Array Int × Array Int) : Inp W :=
  kdfInp decW c (X3dh.dh spk (X3dh.«.ik_a» m)) (X3dh.dh ik (X3dh.«.ek_a» m))
    (X3dh.dh spk (X3dh.«.ek_a» m)) (X3dh.dh opk (X3dh.«.ek_a» m))

end Inputs

/-- The key of `X3dh.initiate_checked` with the one-time prekey is `X3dh.kdf` at the context and
the arguments that `initKdfInp` decodes. -/
theorem initiate_checked_key (ctx ik ek : Array Int)
    (b : Array Int × Array Int × Array Int × Array Int) :
    (X3dh.initiate_checked ctx ik ek b true).1 =
      X3dh.kdf ctx (X3dh.dh ik (X3dh.«.spk» b)) (X3dh.dh ek (X3dh.«.ik» b))
        (X3dh.dh ek (X3dh.«.spk» b)) (X3dh.dh ek (X3dh.«.opk» b)) := by
  simp only [X3dh.initiate_checked, ↓reduceIte]

/-- The key of `X3dh.respond_checked` with the one-time prekey is `X3dh.kdf` at the context and
the arguments that `respKdfInp` decodes. -/
theorem respond_checked_key (ctx ik spk opk : Array Int) (m : Array Int × Array Int × Array Int) :
    X3dh.respond_checked ctx ik spk opk m true =
      X3dh.kdf ctx (X3dh.dh spk (X3dh.«.ik_a» m)) (X3dh.dh ik (X3dh.«.ek_a» m))
        (X3dh.dh spk (X3dh.«.ek_a» m)) (X3dh.dh opk (X3dh.«.ek_a» m)) := by
  simp only [X3dh.respond_checked, ↓reduceIte]

/-- **The extracted key derivation** at encodings: `X3dh.kdf` at the encoded context and the
encoded Diffie–Hellman values of an input, decoded by `decK`. -/
def extKDF (encCtx : SessionId × PartyId × PartyId → Array Int) (encW : W → Array Int)
    (decK : Array Int → K) (i : Inp W) : K :=
  decK (X3dh.kdf (encCtx (i.sid, i.ini, i.res)) (encW i.dh1) (encW i.dh2) (encW i.dh3)
    (encW i.dh4))

section Steps

variable {T : Type} (encCtx : SessionId × PartyId × PartyId → Array Int)
  (encS : S → Array Int) (encW : W → Array Int) (decW : Array Int → W) (k : KDFOp T (Inp W) K)

/-- The completion of the initiator session `x = (sid, a)`: when the input check of
`X3dh.initiate` at the context `encCtx (sid, a, b)` with the encoded identity and ephemeral
secrets of `a` accepts the bundle `X3dh.create_bundle` of the encoded secrets of the peer `b`, with
the one-time prekey, the key is `k.derive` at the decoded input of its key derivation. -/
noncomputable def extCompleteK (s : RStT S K T) (x : Inst) : PMF (ROut S W K × RStT S K T) :=
  match s.st.recs x, s.eph x with
  | some r, some ek =>
    match opkOf s x.1 r.peer with
    | some opk =>
      if r.role = .initiator ∧ r.key.isNone then
        (ltAt s x.2).bind fun la => (ltAt la.2 r.peer).bind fun lb =>
          match X3dh.initiate (encCtx (x.1, x.2, r.peer)) (encS la.1.1) (encS ek)
              (X3dh.create_bundle (encS lb.1.1) (encS lb.1.2) (encS opk)) true with
          | some _ =>
            (k.derive lb.2.ro x (initKdfInp decW (x.1, x.2, r.peer) (encS la.1.1) (encS ek)
              (X3dh.create_bundle (encS lb.1.1) (encS lb.1.2) (encS opk)))).map
              fun p => (.ack, keyed lb.2 x r p.1 p.2)
          | none => PMF.pure (.ack, lb.2)
      else PMF.pure (.ack, s)
    | none => PMF.pure (.ack, s)
  | _, _ => PMF.pure (.ack, s)

/-- The completion of the responder session `x = (sid, b)` on the ephemeral public key `e`: when
the input check of `X3dh.respond` at the context `encCtx (sid, a, b)` with the encoded secrets of
`b` accepts the message of the encoded identity key `X3dh.dh_pub` of the peer `a` and the encoded
`e`, with the one-time prekey, the key is `k.derive` at the decoded input of its key
derivation. -/
noncomputable def extSendK (s : RStT S K T) (x : Inst) (e : W) :
    PMF (ROut S W K × RStT S K T) :=
  match s.st.recs x, s.eph x with
  | some r, some opk =>
    if r.role = .responder ∧ r.key.isNone then
      (ltAt s x.2).bind fun lb => (ltAt lb.2 r.peer).bind fun la =>
        match X3dh.respond (encCtx (x.1, r.peer, x.2)) (encS lb.1.1) (encS lb.1.2) (encS opk)
            (X3dh.dh_pub (encS la.1.1), encW e, #[0, 0, 0, 1]) true with
        | some _ =>
          (k.derive la.2.ro x (respKdfInp decW (x.1, r.peer, x.2) (encS lb.1.1) (encS lb.1.2)
            (encS opk) (X3dh.dh_pub (encS la.1.1), encW e, #[0, 0, 0, 1]))).map
            fun p => (.ack, keyed la.2 x r p.1 p.2)
        | none => PMF.pure (.ack, la.2)
    else PMF.pure (.ack, s)
  | _, _ => PMF.pure (.ack, s)

/-- A step of the adversary port; a query to the key derivation is answered by `k.query`. -/
noncomputable def extAdvK (s : RStT S K T) : RAEv W → PMF (ROut S W K × RStT S K T)
  | .idle => PMF.pure (.ack, s)
  | .poll => PMF.pure (.notice (pollStep s.st).2, { s with st := (pollStep s.st).1 })
  | .pub pid => (ltAt s pid).map fun l =>
      (.pub (decW (X3dh.dh_pub (encS l.1.1))) (decW (X3dh.dh_pub (encS l.1.2))), l.2)
  | .ephPub sid pid =>
      PMF.pure (.eph ((s.eph (sid, pid)).map fun y => decW (X3dh.dh_pub (encS y))), s)
  | .corrupt pid => corruptRStep s pid
  | .complete sid pid => extCompleteK encCtx encS decW k s (sid, pid)
  | .send sid pid e => extSendK encCtx encS encW decW k s (sid, pid) e
  | .kdf i => (k.query s.ro i).map fun p => (.hash p.1, { s with ro := p.2 })

/-- **The X3DH game over the extracted functions at the key derivation `k`**: a trivial key, the
honest step is that of the square model at `k`, and the adversary step is the step of the
protocol whose cryptographic operations are the extracted functions, with the key derivation
answered by `k`. -/
noncomputable def extGameK : KeyedGame (HEv ⊕ RAEv W) (HOut K ⊕ ROut S W K) where
  Key := Unit
  State := RStT S K T
  keyDist := PMF.pure ()
  oracle _ s
    | .inl h => (realHonK k s h).map fun p => (.inl p.1, p.2)
    | .inr a => (extAdvK encCtx encS encW decW k s a).map fun p => (.inr p.1, p.2)
  init := ⟨initSt, fun _ => none, fun _ => none, k.init⟩

end Steps

/-- **The X3DH game over the extracted functions**, with the key derivation the extracted
`X3dh.kdf` at encodings (`extKDF`). -/
noncomputable def extGame (encCtx : SessionId × PartyId × PartyId → Array Int)
    (encS : S → Array Int) (encW : W → Array Int) (decW : Array Int → W)
    (decK : Array Int → K) : KeyedGame (HEv ⊕ RAEv W) (HOut K ⊕ ROut S W K) :=
  extGameK encCtx encS encW decW (fixedKDF (extKDF encCtx encW decK))

variable {G : DHGroup S W} {encCtx : SessionId × PartyId × PartyId → Array Int}
  {encS : S → Array Int} {encW : W → Array Int} {encK : K → Array Int} {H : Inp W → K}
  {decW : Array Int → W} {decK : Array Int → K} {T : Type} {k : KDFOp T (Inp W) K}

omit [Fintype S] [Nonempty S] in
/-- The decoded input of the initiator's key derivation at encoded secrets and a bundle of
encoded group elements is the initiator's input `aliceInp`. -/
theorem initKdfInp_square (h : X3dhSquareHom G encCtx encS encW encK H)
    (hW : ∀ Y, decW (encW Y) = Y) (c : SessionId × PartyId × PartyId) (ik ek : S)
    (IKB SPKB OPKB : W) (sig : Array Int) :
    initKdfInp decW c (encS ik) (encS ek) (encW IKB, encW SPKB, encW OPKB, sig) =
      aliceInp G c.1 c.2.1 c.2.2 ik ek IKB SPKB OPKB := by
  simp only [initKdfInp, kdfInp, X3dh.«.ik», X3dh.«.spk», X3dh.«.opk», h.dh, hW, aliceInp]

omit [Fintype S] [Nonempty S] in
/-- The decoded input of the responder's key derivation at encoded secrets and a message of
encoded group elements is the responder's input `bobInp`. -/
theorem respKdfInp_square (h : X3dhSquareHom G encCtx encS encW encK H)
    (hW : ∀ Y, decW (encW Y) = Y) (c : SessionId × PartyId × PartyId) (IKA E : W)
    (ik spk opk : S) (oid : Array Int) :
    respKdfInp decW c (encS ik) (encS spk) (encS opk) (encW IKA, encW E, oid) =
      bobInp G c.1 c.2.1 c.2.2 IKA E ik spk opk := by
  simp only [respKdfInp, kdfInp, X3dh.«.ik_a», X3dh.«.ek_a», h.dh, hW, bobInp]

/-- The completion of an initiator is that of the square model with the key derivation `k`. -/
theorem extCompleteK_eq (h : X3dhSquareHom G encCtx encS encW encK H)
    (hW : ∀ Y, decW (encW Y) = Y) (s : RStT S K T) (x : Inst) :
    extCompleteK encCtx encS decW k s x = completeStepK k (x3dhAlg G) s x := by
  unfold extCompleteK completeStepK
  cases s.st.recs x with
  | none => rfl
  | some r =>
    cases s.eph x with
    | none => rfl
    | some ek =>
      dsimp only
      cases opkOf s x.1 r.peer with
      | none => rfl
      | some opk =>
        dsimp only
        split_ifs
        · simp only [create_bundle_square_enc h, initiate_square_eq_some h,
            initKdfInp_square h hW]
        · rfl

/-- The completion of a responder is that of the square model with the key derivation `k`. -/
theorem extSendK_eq (h : X3dhSquareHom G encCtx encS encW encK H)
    (hW : ∀ Y, decW (encW Y) = Y) (s : RStT S K T) (x : Inst) (e : W) :
    extSendK encCtx encS encW decW k s x e = sendStepK k (x3dhAlg G) s x e := by
  unfold extSendK sendStepK
  cases s.st.recs x with
  | none => rfl
  | some r =>
    cases s.eph x with
    | none => rfl
    | some opk =>
      dsimp only
      split_ifs
      · simp only [h.dh_pub, respond_square_eq_some h, respKdfInp_square h hW]
      · rfl

/-- The adversary step is the adversary step of the square model with the key derivation `k`. -/
theorem extAdvK_eq (h : X3dhSquareHom G encCtx encS encW encK H) (hW : ∀ Y, decW (encW Y) = Y)
    (s : RStT S K T) (e : RAEv W) :
    extAdvK encCtx encS encW decW k s e = realAdvK k (x3dhAlg G) s e := by
  cases e with
  | complete sid pid => exact extCompleteK_eq h hW s _
  | send sid pid e => exact extSendK_eq h hW s _ e
  | kdf i => rfl
  | _ => simp [extAdvK, realAdvK, ephPubOf, h.dh_pub, hW]

/-- **The extracted game is the square model at every key derivation.** Under
`X3dhSquareHom G encCtx encS encW encK H`, with `decW` a left inverse of `encW`, the game over
the extracted functions at the key derivation `k` is the real game of `x3dhAlg G` at `k`. -/
theorem extGameK_eq (h : X3dhSquareHom G encCtx encS encW encK H)
    (hW : ∀ Y, decW (encW Y) = Y) :
    extGameK encCtx encS encW decW k = realGameK k (x3dhAlg G) := by
  have ho : (fun (_ : Unit) (s : RStT S K T) (q : HEv ⊕ RAEv W) =>
      (extGameK encCtx encS encW decW k).oracle () s q) =
      fun _ s q => (realGameK k (x3dhAlg G)).oracle () s q := by
    funext _ s q
    cases q with
    | inl e => simp only [extGameK, realGameK]
    | inr e => simp only [extGameK, realGameK, extAdvK_eq h hW]
  simp only [extGameK, realGameK] at ho ⊢
  congr

/-- **The system of the extracted game at `k`** is the real X3DH system of `x3dhAlg G` with the
key derivation `k`. -/
theorem extSysK_eq (h : X3dhSquareHom G encCtx encS encW encK H)
    (hW : ∀ Y, decW (encW Y) = Y) :
    (OProt.oracle (Q := HEv ⊕ RAEv W) (A := HOut K ⊕ ROut S W K)).sys
        (extGameK encCtx encS encW decW k) =
      x3dhRealOfK k (x3dhAlg G) := by
  have key : ∀ G₁ G₂ : KeyedGame (HEv ⊕ RAEv W) (HOut K ⊕ ROut S W K), G₁ = G₂ →
      (OProt.oracle (Q := HEv ⊕ RAEv W) (A := HOut K ⊕ ROut S W K)).sys G₁ ≍
        (OProt.oracle (Q := HEv ⊕ RAEv W) (A := HOut K ⊕ ROut S W K)).sys G₂ := by
    rintro _ _ rfl
    rfl
  exact eq_of_heq (key _ _ (extGameK_eq h hW))

/-- **The extracted X3DH in the random-oracle model.** Under
`X3dhSquareHom G encCtx encS encW encK H`, with `decW` a left inverse of `encW`, the system of
the game over the extracted functions with the key derivation the lazily sampled random function
`lazyKDF` realizes `F_AKE` behind `x3dhSim G`: for every finite set of parties `P` and every
environment `Z`, the distance is at most the gap Diffie–Hellman bound `gdhBound G P` of the
square model at the oracle reduction of `Z` (`x3dh_realizesSim_gapDH` transported by
`extSysK_eq`). -/
theorem extSysK_lazy_realizesSim_gapDH [SampleableType W] [Fintype K] [Nonempty K]
    [Inhabited K] (h : X3dhSquareHom G encCtx encS encW encK H)
    (hW : ∀ Y, decW (encW Y) = Y) (P : Finset PartyId) :
    RealizesSim ((OProt.oracle (Q := HEv ⊕ RAEv W) (A := HOut K ⊕ ROut S W K)).sys
        (extGameK encCtx encS encW decW (lazyKDF (D := Inp W) (K := K))))
      (F_AKE (SPComp.sample K) true) (x3dhSim G)
      (fun _ Z => X3DHSquareGDH.gdhBound G P
        ((OProt.oracle (Q := OEv W) (A := OOut S W K)).reduction Z)) := by
  rw [extSysK_eq h hW]
  exact X3DHSquareGDH.x3dh_realizesSim_gapDH G P

omit [Fintype S] [Nonempty S] in
/-- **The extracted key derivation is `H`.** Under `X3dhSquareHom G encCtx encS encW encK H`,
with `decK` a left inverse of `encK`, `extKDF encCtx encW decK` is `H`. -/
theorem extKDF_eq (h : X3dhSquareHom G encCtx encS encW encK H) (hK : ∀ k, decK (encK k) = k) :
    extKDF encCtx encW decK = H := by
  funext i
  simp only [extKDF, h.kdf, hK]

omit [Fintype S] [Nonempty S] in
/-- At the extracted key derivation, the key of an initiator in the game is the decoded key of
`X3dh.initiate_checked` at the context `encCtx c`. -/
theorem extKDF_initKdfInp (h : X3dhSquareHom G encCtx encS encW encK H)
    (hW : ∀ Y, decW (encW Y) = Y) (hK : ∀ k, decK (encK k) = k)
    (c : SessionId × PartyId × PartyId) (ik ek : S) (IKB SPKB OPKB : W) (sig : Array Int) :
    extKDF encCtx encW decK
        (initKdfInp decW c (encS ik) (encS ek) (encW IKB, encW SPKB, encW OPKB, sig)) =
      decK (X3dh.initiate_checked (encCtx c) (encS ik) (encS ek)
        (encW IKB, encW SPKB, encW OPKB, sig) true).1 := by
  rw [extKDF_eq h hK, initKdfInp_square h hW, initiate_square_enc h, hK]

omit [Fintype S] [Nonempty S] in
/-- At the extracted key derivation, the key of a responder in the game is the decoded key of
`X3dh.respond_checked` at the context `encCtx c`. -/
theorem extKDF_respKdfInp (h : X3dhSquareHom G encCtx encS encW encK H)
    (hW : ∀ Y, decW (encW Y) = Y) (hK : ∀ k, decK (encK k) = k)
    (c : SessionId × PartyId × PartyId) (IKA E : W) (ik spk opk : S) (oid : Array Int) :
    extKDF encCtx encW decK
        (respKdfInp decW c (encS ik) (encS spk) (encS opk) (encW IKA, encW E, oid)) =
      decK (X3dh.respond_checked (encCtx c) (encS ik) (encS spk) (encS opk)
        (encW IKA, encW E, oid) true) := by
  rw [extKDF_eq h hK, respKdfInp_square h hW, respond_square_enc h, hK]

/-- **The extracted game is the square model.** Under `X3dhSquareHom G encCtx encS encW encK H`,
with `decW`, `decK` left inverses of `encW`, `encK`, the game over the extracted functions is
the real game of `x3dhAlg G` with the key derivation the fixed function `H`. -/
theorem extGame_eq (h : X3dhSquareHom G encCtx encS encW encK H) (hW : ∀ Y, decW (encW Y) = Y)
    (hK : ∀ k, decK (encK k) = k) :
    extGame encCtx encS encW decW decK = realGameK (fixedKDF H) (x3dhAlg G) := by
  rw [extGame, extKDF_eq h hK]
  exact extGameK_eq h hW

/-- **The system of the extracted game** is the real X3DH system of `x3dhAlg G` with the key
derivation `H`. -/
theorem extSys_eq (h : X3dhSquareHom G encCtx encS encW encK H) (hW : ∀ Y, decW (encW Y) = Y)
    (hK : ∀ k, decK (encK k) = k) :
    (OProt.oracle (Q := HEv ⊕ RAEv W) (A := HOut K ⊕ ROut S W K)).sys
        (extGame encCtx encS encW decW decK) =
      x3dhRealOfK (fixedKDF H) (x3dhAlg G) := by
  unfold extGame
  rw [extKDF_eq h hK]
  exact extSysK_eq h hW

end CatCrypt.Crypto.AKE.X3DH.ExtractedGame
