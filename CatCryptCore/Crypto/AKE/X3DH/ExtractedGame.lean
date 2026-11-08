/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DH.SquareCorrespondence

/-!
# The multi-session X3DH game over the extracted functions

`extGame H encCtx encS encW decW decK` is the real game of the square model
`CatCryptCore.Crypto.AKE.X3DHSquare` at the fixed key derivation `fixedKDF H`, in which the
adversary steps use the extracted functions of the Rust crate `x3dh-hax` in the
`X3dh.X3dhDeps` instance in scope. The honest step is `realHonK (fixedKDF H)`. The state
holds the session records and the sampled scalars, as in `RStT S K Unit`; at each adversary
call the scalars are encoded by `encS` and the group elements by `encW`, and the results of the
extracted functions are decoded by `decW` and `decK`:
* the public keys read by the adversary are `decW (X3dh.dh_pub (encS x))`;
* an initiator completes by `X3dh.initiate` at the context `encCtx (sid, a, b)` on the bundle
  `X3dh.create_bundle` of the responder's encoded secrets, with the one-time prekey;
* a responder completes by `X3dh.respond` at the context `encCtx (sid, a, b)` on the message of
  the initiator's encoded identity key `X3dh.dh_pub (encS ik)` and the encoded ephemeral key;
* a query of the adversary to the key derivation is `X3dh.kdf` at the encoded input.
A rejection of the input check of `initiate` or `respond` leaves the session without key.

Under `X3dhSquareHom G encCtx encS encW encK H`, with `decW` and `decK` left inverses of `encW`
and `encK`, the game is `realGameK (fixedKDF H) (x3dhAlg G)` (`extGame_eq`), so its system is
`x3dhRealOfK (fixedKDF H) (x3dhAlg G)` (`extSys_eq`) and every statement about that system is a
statement about the extracted functions.

## Main definitions

* `extComplete`, `extSend`, `extAdv` — the adversary steps of the game.
* `extGame` — the game.

## Main results

* `extComplete_eq`, `extSend_eq`, `extAdv_eq` — each step is the step of
  `realGameK (fixedKDF H) (x3dhAlg G)`.
* `extGame_eq`, `extSys_eq` — the game and its system are those of the square model.
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

section Steps

variable (H : Inp W → K) (encCtx : SessionId × PartyId × PartyId → Array Int)
  (encS : S → Array Int) (encW : W → Array Int) (decW : Array Int → W) (decK : Array Int → K)

/-- The completion of the initiator session `x = (sid, a)`: `X3dh.initiate` at the context
`encCtx (sid, a, b)` with the encoded identity and ephemeral secrets of `a`, on the bundle
`X3dh.create_bundle` of the encoded secrets of the peer `b`, with the one-time prekey; the key
is the decoding of its session key. -/
noncomputable def extComplete (s : RStT S K Unit) (x : Inst) :
    PMF (ROut S W K × RStT S K Unit) :=
  match s.st.recs x, s.eph x with
  | some r, some ek =>
    match opkOf s x.1 r.peer with
    | some opk =>
      if r.role = .initiator ∧ r.key.isNone then
        (ltAt s x.2).bind fun la => (ltAt la.2 r.peer).bind fun lb =>
          match X3dh.initiate (encCtx (x.1, x.2, r.peer)) (encS la.1.1) (encS ek)
              (X3dh.create_bundle (encS lb.1.1) (encS lb.1.2) (encS opk)) true with
          | some o => PMF.pure (.ack, keyed lb.2 x r (decK o.1) ())
          | none => PMF.pure (.ack, lb.2)
      else PMF.pure (.ack, s)
    | none => PMF.pure (.ack, s)
  | _, _ => PMF.pure (.ack, s)

/-- The completion of the responder session `x = (sid, b)` on the ephemeral public key `e`:
`X3dh.respond` at the context `encCtx (sid, a, b)` with the encoded secrets of `b`, on the
message of the encoded identity key `X3dh.dh_pub` of the peer `a` and the encoded `e`, with the
one-time prekey; the key is the decoding of its result. -/
noncomputable def extSend (s : RStT S K Unit) (x : Inst) (e : W) :
    PMF (ROut S W K × RStT S K Unit) :=
  match s.st.recs x, s.eph x with
  | some r, some opk =>
    if r.role = .responder ∧ r.key.isNone then
      (ltAt s x.2).bind fun lb => (ltAt lb.2 r.peer).bind fun la =>
        match X3dh.respond (encCtx (x.1, r.peer, x.2)) (encS lb.1.1) (encS lb.1.2) (encS opk)
            (X3dh.dh_pub (encS la.1.1), encW e, #[0, 0, 0, 1]) true with
        | some k => PMF.pure (.ack, keyed la.2 x r (decK k) ())
        | none => PMF.pure (.ack, la.2)
    else PMF.pure (.ack, s)
  | _, _ => PMF.pure (.ack, s)

/-- A step of the adversary port. -/
noncomputable def extAdv (s : RStT S K Unit) : RAEv W → PMF (ROut S W K × RStT S K Unit)
  | .idle => PMF.pure (.ack, s)
  | .poll => PMF.pure (.notice (pollStep s.st).2, { s with st := (pollStep s.st).1 })
  | .pub pid => (ltAt s pid).map fun l =>
      (.pub (decW (X3dh.dh_pub (encS l.1.1))) (decW (X3dh.dh_pub (encS l.1.2))), l.2)
  | .ephPub sid pid =>
      PMF.pure (.eph ((s.eph (sid, pid)).map fun y => decW (X3dh.dh_pub (encS y))), s)
  | .corrupt pid => corruptRStep s pid
  | .complete sid pid => extComplete encCtx encS decK s (sid, pid)
  | .send sid pid e => extSend encCtx encS encW decK s (sid, pid) e
  | .kdf i => PMF.pure (.hash (decK (X3dh.kdf (encCtx (i.sid, i.ini, i.res)) (encW i.dh1)
      (encW i.dh2) (encW i.dh3) (encW i.dh4))), s)

/-- **The X3DH game over the extracted functions**: a trivial key, the honest step is that of
the square model at the fixed key derivation `H`, and the adversary step is the step of the
protocol whose cryptographic operations are the extracted functions. -/
noncomputable def extGame : KeyedGame (HEv ⊕ RAEv W) (HOut K ⊕ ROut S W K) where
  Key := Unit
  State := RStT S K Unit
  keyDist := PMF.pure ()
  oracle _ s
    | .inl h => (realHonK (fixedKDF H) s h).map fun p => (.inl p.1, p.2)
    | .inr a => (extAdv encCtx encS encW decW decK s a).map fun p => (.inr p.1, p.2)
  init := ⟨initSt, fun _ => none, fun _ => none, ()⟩

end Steps

variable {G : DHGroup S W} {encCtx : SessionId × PartyId × PartyId → Array Int}
  {encS : S → Array Int} {encW : W → Array Int} {encK : K → Array Int} {H : Inp W → K}
  {decW : Array Int → W} {decK : Array Int → K}

/-- The completion of an initiator is that of the square model with the key derivation `H`. -/
theorem extComplete_eq (h : X3dhSquareHom G encCtx encS encW encK H)
    (hK : ∀ k, decK (encK k) = k) (s : RStT S K Unit) (x : Inst) :
    extComplete encCtx encS decK s x = completeStepK (fixedKDF H) (x3dhAlg G) s x := by
  unfold extComplete completeStepK
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
            initiate_square_enc h, hK, fixedKDF, PMF.pure_map]
        · rfl

/-- The completion of a responder is that of the square model with the key derivation `H`. -/
theorem extSend_eq (h : X3dhSquareHom G encCtx encS encW encK H)
    (hK : ∀ k, decK (encK k) = k) (s : RStT S K Unit) (x : Inst) (e : W) :
    extSend encCtx encS encW decK s x e = sendStepK (fixedKDF H) (x3dhAlg G) s x e := by
  unfold extSend sendStepK
  cases s.st.recs x with
  | none => rfl
  | some r =>
    cases s.eph x with
    | none => rfl
    | some opk =>
      dsimp only
      split_ifs
      · simp only [h.dh_pub, respond_square_eq_some h, respond_square_enc h, hK, fixedKDF,
          PMF.pure_map]
      · rfl

/-- The adversary step is the adversary step of the square model with the key derivation `H`. -/
theorem extAdv_eq (h : X3dhSquareHom G encCtx encS encW encK H) (hW : ∀ Y, decW (encW Y) = Y)
    (hK : ∀ k, decK (encK k) = k) (s : RStT S K Unit) (e : RAEv W) :
    extAdv encCtx encS encW decW decK s e = realAdvK (fixedKDF H) (x3dhAlg G) s e := by
  cases e with
  | complete sid pid => exact extComplete_eq h hK s _
  | send sid pid e => exact extSend_eq h hK s _ e
  | kdf i => simp only [extAdv, realAdvK, fixedKDF, h.kdf, hK, PMF.pure_map]
  | _ => simp [extAdv, realAdvK, ephPubOf, h.dh_pub, hW]

/-- **The extracted game is the square model.** Under `X3dhSquareHom G encCtx encS encW encK H`,
with `decW`, `decK` left inverses of `encW`, `encK`, the game over the extracted functions is
the real game of `x3dhAlg G` with the key derivation the fixed function `H`. -/
theorem extGame_eq (h : X3dhSquareHom G encCtx encS encW encK H) (hW : ∀ Y, decW (encW Y) = Y)
    (hK : ∀ k, decK (encK k) = k) :
    extGame H encCtx encS encW decW decK = realGameK (fixedKDF H) (x3dhAlg G) := by
  have ho : (fun (_ : Unit) (s : RStT S K Unit) (q : HEv ⊕ RAEv W) =>
      (extGame H encCtx encS encW decW decK).oracle () s q) =
      fun _ s q => (realGameK (fixedKDF H) (x3dhAlg G)).oracle () s q := by
    funext _ s q
    cases q with
    | inl e => simp only [extGame, realGameK]
    | inr e => simp only [extGame, realGameK, extAdv_eq h hW hK]
  simp only [extGame, realGameK] at ho ⊢
  congr

/-- **The system of the extracted game** is the real X3DH system of `x3dhAlg G` with the key
derivation `H`. -/
theorem extSys_eq (h : X3dhSquareHom G encCtx encS encW encK H) (hW : ∀ Y, decW (encW Y) = Y)
    (hK : ∀ k, decK (encK k) = k) :
    (OProt.oracle (Q := HEv ⊕ RAEv W) (A := HOut K ⊕ ROut S W K)).sys
        (extGame H encCtx encS encW decW decK) =
      x3dhRealOfK (fixedKDF H) (x3dhAlg G) := by
  have key : ∀ G₁ G₂ : KeyedGame (HEv ⊕ RAEv W) (HOut K ⊕ ROut S W K), G₁ = G₂ →
      (OProt.oracle (Q := HEv ⊕ RAEv W) (A := HOut K ⊕ ROut S W K)).sys G₁ ≍
        (OProt.oracle (Q := HEv ⊕ RAEv W) (A := HOut K ⊕ ROut S W K)).sys G₂ := by
    rintro _ _ rfl
    rfl
  exact eq_of_heq (key _ _ (extGame_eq h hW hK))

end CatCrypt.Crypto.AKE.X3DH.ExtractedGame
