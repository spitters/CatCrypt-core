/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SMID
public import CatCryptCore.Crypto.Messaging.SaltedAEAD
public import CatCryptCore.Crypto.OracleLazyMulti
import CatCryptCore.Tactics.AutoDispatchExt

/-!
# A sidecar key schedule mixed into every message key

The deployed Signal Triple Ratchet runs the post-quantum ratchet SPQR beside the Double Ratchet
and encrypts each message under `KDF_HYBRID(ec_mk, pq_mk)`, a key derived from the message key
`ec_mk` of the Double Ratchet with the message key `pq_mk` of SPQR as salt. In the construction
of Dodis, Jost, Katsumata, Prest and Schmidt (*Triple Ratchet*, ePrint 2025/078) this is the
per-message step `K_aead ← KDF3(K^C_aead, K^Q_aead)`.

## The construction

A sidecar `P : SidecarDef PSt PHdr S` is a deterministic state machine: its initial states
(coins of a randomised sidecar are part of `P`), the header `P.hdr y` of the next message of a
sender in state `y`, the salt and the next state `P.next y` of a send, and the salt and the next
state `P.rkey y hp` of a receiver at the header `hp`, or `none`. An encoding
`E : SidecarPack PHdr S W` packs a sidecar header, a salt and associated data into one word.

`smidSidecar M P E` runs `M : SMIDScheme` and `P` side by side. Its header is the pair of the
headers. A send passes the associated data `E.pack hp s ad` to `M`, with the header `hp` and the
salt `s` of the sender's sidecar, and advances the sidecar when `M` encrypts. The key lookup
runs both lookups, and decryption passes `E.pack hp s ad` to `M` with the salt `s` of the
receiver's sidecar. The game commits the state of a key lookup only after a successful
decryption, so the sidecar of the receiver advances only after the message authenticates: this
is the modelled order of the deployed protocol, which is not confirmed against libsignal.

When `M` is a scheme whose AEAD is the salted AEAD `saltedAEAD D F` (`SaltedAEAD.lean`) reading
its salt from the associated data, `smidSidecar M P E` encrypts each message under `F mk s`. The
AEAD with the associated data relabelled by `ρ` is `aeadComapAD D ρ`, and for injective `ρ` its
advantage is the advantage of `D` against the relabelled adversary `aeadAdvMapAD ρ A`
(`AEAD_CCA_Advantage_comapAD`); an AEAD whose associated data is a word is a salted AEAD through
`ρ w = ((E.unpack w).2.1, …)`.

## The reduction and the bad event

`sidecarRed P E A` runs `A` and the sidecars of both parties: it forwards the queries of the
corruption game with the associated data of a send packed with the sidecar header and salt,
attaches the sidecar header to the answers, and delivers with the salt of the receiver's
sidecar, committing that sidecar on a successful decryption.

The games agree until `sidecarWrongSalt`: a delivery whose receiver salt `s` differs from the
salt logged with an undelivered matching honest ciphertext, i.e. the logged associated data of
that ciphertext is not `E.pack hp s ad`. The bad game `sidecarBadGame` runs `A` in the game of
`M ⊕ P` with the salts recorded (`sidecarGhostOracle`) and outputs whether this happened.

## Main definitions

* `SidecarDef`, `SidecarPack`, `smidSidecar`
* `sidecarImpl`, `sidecarRed`
* `sidecarView`, `sidecarGhostOracle`, `sidecarWrongSalt`, `sidecarBadGame`
* `aeadComapAD`, `aeadAdvMapAD`

## Main results

* `smIDGame_sidecar` — the game of `M` against `sidecarRed P E A` and the game of
  `smidSidecar M P E` against `A` differ by at most the probability of the bad game
* `SMIDScheme.idAdvantage_sidecar_le` — the advantage against `smidSidecar M P E` is at most the
  advantage against `M` of `sidecarRed P E A` plus the bad events of the two games
* `AEAD_CCA_Advantage_comapAD` — the advantage of an AEAD with relabelled associated data

## References

* Y. Dodis, D. Jost, S. Katsumata, T. Prest, R. Schmidt, *Triple Ratchet: A Bandwidth Efficient
  Hybrid-Secure Signal Protocol*, ePrint 2025/078.
* J. Alwen, S. Coretti, Y. Dodis, *The Double Ratchet: Security Notions, Proofs, and
  Modularization for the Signal Protocol*, EUROCRYPT 2019.
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open scoped ENNReal

/-! ## The construction -/

/-- A deterministic sidecar key schedule with states `PSt`, headers `PHdr` and salts `S`. -/
structure SidecarDef (PSt PHdr S : Type) where
  /-- The initial states of the first sender and of the first receiver. -/
  init : PSt × PSt
  /-- The header of the next message of a sender in state `y`. -/
  hdr : PSt → PHdr
  /-- The next state and the salt of a send. -/
  next : PSt → PSt × S
  /-- The next state and the salt of a receiver at a header, or `none`. -/
  rkey : PSt → PHdr → Option (PSt × S)

/-- An encoding of a sidecar header, a salt and associated data as one word. An injective
packing into a finite word type `W` forces a single salt and a single sidecar header, so
statements over `SidecarPack` apply only to runs with a constant salt. -/
structure SidecarPack (PHdr S W : Type) where
  /-- The encoding. -/
  pack : PHdr → S → W → W
  /-- The decoding. -/
  unpack : W → PHdr × S × W
  /-- The decoding is a left inverse of the encoding. -/
  unpack_pack : ∀ hp s a, unpack (pack hp s a) = (hp, s, a)

variable {St Pub Rand W Ct Leak Hdr K PSt PHdr S : Type}

/-- The message passed to the main scheme by a sender whose sidecar is in state `y`: the
associated data packed with the sidecar header and the salt. -/
def sidecarMsg (P : SidecarDef PSt PHdr S) (E : SidecarPack PHdr S W) (y : PSt) (m : W × W) :
    W × W :=
  (m.1, E.pack (P.hdr y) (P.next y).2 m.2)

/-- **The scheme `M` with the sidecar `P` mixed into every message.** The injective packing
`SidecarPack` into a finite word type forces a single salt and a single sidecar header, so the
scheme models only runs with a constant salt. -/
noncomputable def smidSidecar (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (P : SidecarDef PSt PHdr S) (E : SidecarPack PHdr S W) :
    SMIDScheme (St × PSt) Pub Rand W Ct (Leak × PSt) (Hdr × PHdr) (K × S) where
  init := SPComp.bind M.init fun i => SPComp.pure (i.1, (i.2.1, P.init.1), (i.2.2, P.init.2))
  ratchet x r := (((M.ratchet x.1 r).1, x.2), (M.ratchet x.1 r).2)
  recv x T := (M.recv x.1 T, x.2)
  send x m := (M.send x.1 (sidecarMsg P E x.2 m)).map fun z => ((z.1, (P.next x.2).1), z.2)
  expose x := (M.expose x.1, x.2)
  idealCt := M.idealCt
  hdr x := (M.hdr x.1, P.hdr x.2)
  hdrPub h := M.hdrPub h.1
  hdrPos h := M.hdrPos h.1
  rkey x h := match M.rkey x.1 h.1, P.rkey x.2 h.2 with
    | some a, some b => some ((a.1, b.1), (a.2, b.2))
    | _, _ => none
  decrypt k h ad c := M.decrypt k.1 h.1 (E.pack h.2 k.2 ad) c

/-! ## The reduction -/

/-- The sidecar states after the query `q` of the corruption game answered by `a`: the sender's
sidecar advances on a ciphertext. -/
def sidecarNext {C : Type} (P : SidecarDef PSt PHdr S) (ys : CKAParty → PSt) :
    SMQuery W → SMSchemeAns Pub C Leak → CKAParty → PSt
  | .send p _, .ct _ => Function.update ys p (P.next (ys p)).1
  | .chall p _, .ct _ => Function.update ys p (P.next (ys p)).1
  | _, _ => ys

/-- `sidecarNext` on an answer of the game with immediate decryption. -/
def sidecarNextID (P : SidecarDef PSt PHdr S) (ys : CKAParty → PSt) (q : SMQuery W) :
    SMIDAns Pub Hdr Ct Leak W → CKAParty → PSt
  | .sm a => sidecarNext P ys q a
  | .dec _ => ys

/-- The sidecar states after a delivery to `p` answered by `a`: the receiver's sidecar moves to
`y` on a successful decryption. -/
def sidecarCommit (ys : CKAParty → PSt) (p : CKAParty) (y : PSt) :
    SMIDAns Pub Hdr Ct Leak W → CKAParty → PSt
  | .dec (some _) => Function.update ys p y
  | _ => ys

/-- An answer of the game over `M` as an answer of the game over the sidecar scheme, for the
party whose sidecar is in state `y`. -/
def sidecarAns (P : SidecarDef PSt PHdr S) (y : PSt) :
    SMIDAns Pub Hdr Ct Leak W → SMIDAns Pub (Hdr × PHdr) Ct (Leak × PSt) W :=
  SMIDAns.map id (fun h => (h, P.hdr y)) id fun l => (l, y)

/-- The simulator of `sidecarRed`, with the sidecar states of both parties as its state. -/
def sidecarImpl (P : SidecarDef PSt PHdr S) (E : SidecarPack PHdr S W) (ys : CKAParty → PSt) :
    SMIDQuery W (Hdr × PHdr) Ct → OracleAdv (SMIDQuery W Hdr Ct) (SMIDAns Pub Hdr Ct Leak W)
      (SMIDAns Pub (Hdr × PHdr) Ct (Leak × PSt) W × (CKAParty → PSt))
  | .sm q => .query (.sm (q.mapMsg (sidecarMsg P E (ys q.party)))) fun a =>
      .ret (sidecarAns P (ys q.party) a, sidecarNextID P ys q a)
  | .deliver p h ad c =>
    match P.rkey (ys p) h.2 with
    | none => .ret (.dec none, ys)
    | some y => .query (.deliver p h.1 (E.pack h.2 y.2 ad) c) fun a =>
        .ret (sidecarAns P (ys p) a, sidecarCommit ys p y.1 a)

/-- The initial sidecar states. -/
def sidecarInitSt (P : SidecarDef PSt PHdr S) : CKAParty → PSt
  | .A => P.init.1
  | .B => P.init.2

/-- **The reduction to the game over `M`**: it runs `A` and the sidecars of both parties. -/
def sidecarRed (P : SidecarDef PSt PHdr S) (E : SidecarPack PHdr S W)
    (A : SMIDAdv Pub W (Hdr × PHdr) Ct (Leak × PSt)) : SMIDAdv Pub W Hdr Ct Leak where
  tStar := A.tStar
  play t pub := (OracleAdv.simulate (sidecarImpl P E) (A.play t pub) (sidecarInitSt P)).bind
    fun r => .ret r.1

/-! ## The game with the salts recorded -/

/-- A log entry of the game over `M` as a log entry of the game over the sidecar scheme: the
sidecar header and the associated data decoded from the logged associated data. -/
def sidecarEntry (E : SidecarPack PHdr S W) (l : SMIDLogEntry W Hdr Ct) :
    SMIDLogEntry W (Hdr × PHdr) Ct :=
  ⟨l.e, l.j, l.pt, (E.unpack l.ad).2.2, (l.hdr, (E.unpack l.ad).1), l.ct, l.delivered⟩

/-- The bookkeeping with the log entries decoded by `sidecarEntry`. -/
def sidecarAux (E : SidecarPack PHdr S W) (x : SMIDAux W Pub Hdr Ct) :
    SMIDAux W Pub (Hdr × PHdr) Ct :=
  ⟨x.log.map (sidecarEntry E), x.pubs, x.corrs⟩

/-- The game state over the sidecar scheme with the party states of `s` and the sidecar
states `ys`. -/
def sidecarLift (ys : CKAParty → PSt) (s : SMSchemeSt St Pub) : SMSchemeSt (St × PSt) Pub :=
  ⟨⟨fun p => (s.ck.st p, ys p), s.ck.t, s.ck.msg⟩, s.done⟩

/-- The game state over the sidecar scheme that a state of the reduction and of the game over
`M` corresponds to. -/
def sidecarView (E : SidecarPack PHdr S W)
    (σ : (CKAParty → PSt) × (SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct)) :
    SMSchemeSt (St × PSt) Pub × SMIDAux W Pub (Hdr × PHdr) Ct :=
  (sidecarLift σ.1 σ.2.1, sidecarAux E σ.2.2)

variable [DecidableEq Pub] [DecidableEq W] [DecidableEq Hdr] [DecidableEq PHdr] [DecidableEq Ct]

/-- The log with every entry whose decoded entry matches marked delivered. -/
def sidecarMark (E : SidecarPack PHdr S W) (x : SMIDAux W Pub Hdr Ct) (e : ℕ) (h : Hdr × PHdr)
    (ad : W) (c : Ct) : SMIDAux W Pub Hdr Ct :=
  { x with log := x.log.map fun l =>
      if (sidecarEntry E l).isMatch e h ad c then { l with delivered := true } else l }

/-- The delivery of the game over the sidecar scheme on the states of the reduction and of the
game over `M`. -/
def sidecarGhostDeliver (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (P : SidecarDef PSt PHdr S) (E : SidecarPack PHdr S W) (ΔFS ΔPCS : ℕ) (idealD : ℕ → Bool)
    (σ : (CKAParty → PSt) × (SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct)) (p : CKAParty)
    (h : Hdr × PHdr) (ad : W) (c : Ct) :
    Option W × ((CKAParty → PSt) × (SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct)) :=
  match σ.2.2.epochOf (ckaShadow σ.2.1.ck) p (M.hdrPub h.1) with
  | none => (none, σ)
  | some e =>
    if σ.2.2.safe ΔFS ΔPCS p e (M.hdrPos h.1) then
      match M.rkey (σ.2.1.ck.st p) h.1, P.rkey (σ.1 p) h.2 with
      | some a, some b =>
        match (if idealD e then ((sidecarAux E σ.2.2).findEntry e h ad c).map SMIDLogEntry.pt
          else M.decrypt a.2 h.1 (E.pack h.2 b.2 ad) c) with
        | some m => (some m, (Function.update σ.1 p b.1,
            (σ.2.1.upd p a.1 σ.2.1.done, sidecarMark E σ.2.2 e h ad c)))
        | none => (none, σ)
      | _, _ => (none, σ)
    else (none, σ)

variable [Fintype Rand] [Nonempty Rand]

/-- The oracle of the game over the sidecar scheme on the states of the reduction and of the
game over `M`: the queries of the corruption game as the reduction answers them, deliveries by
`sidecarGhostDeliver`. -/
noncomputable def sidecarGhostOracle (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (P : SidecarDef PSt PHdr S) (E : SidecarPack PHdr S W) (ΔFS ΔPCS t : ℕ) (idealC : Bool)
    (idealD : ℕ → Bool) (σ : (CKAParty → PSt) × (SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct)) :
    SMIDQuery W (Hdr × PHdr) Ct →
      PMF (SMIDAns Pub (Hdr × PHdr) Ct (Leak × PSt) W ×
        ((CKAParty → PSt) × (SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct)))
  | .sm q => OracleAdv.simOracle (sidecarImpl P E) (smIDOracleAt M ΔFS ΔPCS t idealC idealD) σ
      (.sm q)
  | .deliver p h ad c =>
    PMF.pure (Prod.map SMIDAns.dec id (sidecarGhostDeliver M P E ΔFS ΔPCS idealD σ p h ad c))

/-- **A wrong salt**: a delivery `(h, ad, c)` at which the receiver's sidecar gives the salt
`s`, while an undelivered honest ciphertext with the same header, associated data and
ciphertext was logged with associated data other than `E.pack h.2 s ad`, i.e. with another
salt. -/
def sidecarWrongSalt (P : SidecarDef PSt PHdr S) (E : SidecarPack PHdr S W)
    (σ : (CKAParty → PSt) × (SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct)) :
    SMIDQuery W (Hdr × PHdr) Ct → Bool
  | .sm _ => false
  | .deliver p h ad c =>
    match P.rkey (σ.1 p) h.2 with
    | none => false
    | some y => σ.2.2.log.any fun l =>
        (sidecarEntry E l).isMatch l.e h ad c && decide (l.ad ≠ E.pack h.2 y.2 ad)

/-- **The wrong-salt event**: the game that runs `A` against the game over the sidecar scheme
with the salts recorded and outputs whether a delivery met a wrong salt. -/
noncomputable def sidecarBadGame (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (P : SidecarDef PSt PHdr S) (E : SidecarPack PHdr S W) (ΔFS ΔPCS : ℕ) (idealC : Bool)
    (idealD : ℕ → Bool) (A : SMIDAdv Pub W (Hdr × PHdr) Ct (Leak × PSt)) : SPComp Bool :=
  SPComp.bind (liftPMF A.tStar) fun t => SPComp.bind M.init fun i =>
    liftPMF ((OracleAdv.run (OracleAdv.flagWhen (fun σ d _ => sidecarWrongSalt P E σ d = true)
        (sidecarGhostOracle M P E ΔFS ΔPCS t idealC idealD)) (A.play t i.1)
        ((sidecarInitSt P, (SMSchemeSt.init i, SMIDAux.init i.1)), false)).map fun x => x.2.2)

/-! ## The view of the game states -/

section View

omit [DecidableEq Pub] [DecidableEq W] [DecidableEq Hdr] [DecidableEq PHdr] [DecidableEq Ct]
  [Fintype Rand] [Nonempty Rand]

/-- The sidecar states after an answer with a header attached. -/
theorem sidecarNext_withHdr {C : Type} (P : SidecarDef PSt PHdr S) (ys : CKAParty → PSt)
    (q : SMQuery W) (h : Hdr) (a : SMSchemeAns Pub C Leak) :
    sidecarNext P ys q (a.withHdr h) = sidecarNext P ys q a := by
  cases q <;> cases a <;> rfl

/-- Unfolding lemma of `sidecarLift`: the party states. -/
@[simp] theorem sidecarLift_st (ys : CKAParty → PSt) (s : SMSchemeSt St Pub) (p : CKAParty) :
    (sidecarLift ys s).ck.st p = (s.ck.st p, ys p) := rfl

/-- Unfolding lemma of `sidecarLift`: the epoch counters. -/
@[simp] theorem sidecarLift_t (ys : CKAParty → PSt) (s : SMSchemeSt St Pub) :
    (sidecarLift ys s).ck.t = s.ck.t := rfl

/-- Unfolding lemma of `sidecarLift`: the public value in transit. -/
@[simp] theorem sidecarLift_msg (ys : CKAParty → PSt) (s : SMSchemeSt St Pub) :
    (sidecarLift ys s).ck.msg = s.ck.msg := rfl

/-- Unfolding lemma of `sidecarLift`: the challenge flag. -/
@[simp] theorem sidecarLift_done (ys : CKAParty → PSt) (s : SMSchemeSt St Pub) :
    (sidecarLift ys s).done = s.done := rfl

/-- Lifting the state after a party update. -/
theorem sidecarLift_upd (ys : CKAParty → PSt) (s : SMSchemeSt St Pub) (p : CKAParty) (x : St)
    (y : PSt) (d : Bool) :
    sidecarLift (Function.update ys p y) (s.upd p x d) = (sidecarLift ys s).upd p (x, y) d := by
  simp only [sidecarLift, SMSchemeSt.upd, SMSchemeSt.mk.injEq, CKAGameSt.mk.injEq, and_true]
  funext q
  by_cases hq : q = p
  · subst hq; simp
  · simp [Function.update_of_ne hq]

/-- The undelivered positions of the decoded bookkeeping. -/
theorem pending_sidecarAux (E : SidecarPack PHdr S W) (x : SMIDAux W Pub Hdr Ct)
    (sh : CKAGameSt Unit Unit) (p : CKAParty) :
    (sidecarAux E x).pending sh p = x.pending sh p := by
  simp only [SMIDAux.pending, sidecarAux, List.filter_map, List.map_map]
  rfl

/-- The corruption gate of the decoded bookkeeping. -/
theorem storeClear_sidecarAux (E : SidecarPack PHdr S W) (x : SMIDAux W Pub Hdr Ct)
    (sh : CKAGameSt Unit Unit) (p : CKAParty) :
    (sidecarAux E x).storeClear sh p = x.storeClear sh p := by
  simp only [SMIDAux.storeClear, sidecarAux, List.all_map]
  rfl

/-- Lifting the state after a send of the CKA game. -/
theorem sidecarLift_sent (ys : CKAParty → PSt) (s : SMSchemeSt St Pub) (p : CKAParty) (x : St)
    (T : Pub) (d : Bool) :
    sidecarLift ys ⟨s.ck.sent p x T, d⟩ = ⟨(sidecarLift ys s).ck.sent p (x, ys p) T, d⟩ := by
  simp only [sidecarLift, CKAGameSt.sent, SMSchemeSt.mk.injEq, CKAGameSt.mk.injEq, and_true]
  funext q
  by_cases hq : q = p
  · subst hq; simp
  · simp [Function.update_of_ne hq]

/-- Lifting the state after a receive of the CKA game. -/
theorem sidecarLift_recvd (ys : CKAParty → PSt) (s : SMSchemeSt St Pub) (p : CKAParty) (x : St)
    (d : Bool) :
    sidecarLift ys ⟨s.ck.recvd p x, d⟩ = ⟨(sidecarLift ys s).ck.recvd p (x, ys p), d⟩ := by
  simp only [sidecarLift, CKAGameSt.recvd, SMSchemeSt.mk.injEq, CKAGameSt.mk.injEq, and_true]
  funext q
  by_cases hq : q = p
  · subst hq; simp
  · simp [Function.update_of_ne hq]

end View

omit [DecidableEq Pub] [DecidableEq W] [DecidableEq Hdr] [DecidableEq PHdr] [DecidableEq Ct] in
/-- **The corruption game over the sidecar scheme on lifted states**: the call of the oracle of
`M` with the message of the sender's sidecar, with the corruption answer extended by the
sidecar state and the sidecar states advanced by `sidecarNext`. -/
theorem smSchemeOracle_sidecar (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (P : SidecarDef PSt PHdr S) (E : SidecarPack PHdr S W) (ΔFS ΔPCS t : ℕ) (ideal : Bool)
    (ys : CKAParty → PSt) (s : SMSchemeSt St Pub) (q : SMQuery W) :
    smSchemeOracle (smidSidecar M P E).toSMScheme ΔFS ΔPCS t ideal (sidecarLift ys s) q =
      (smSchemeOracle M.toSMScheme ΔFS ΔPCS t ideal s
          (q.mapMsg (sidecarMsg P E (ys q.party)))).map fun y =>
        (y.1.map id id fun l => (l, ys q.party), sidecarLift (sidecarNext P ys q y.1) y.2) := by
  cases q with
  | ratchet p =>
    have hc : (sidecarLift ys s).ck.canSend p = s.ck.canSend p := rfl
    simp only [smSchemeOracle, SMQuery.mapMsg, hc]
    split
    · simp only [PMF.map_bind, PMF.pure_map]
      refine congrArg _ (funext fun r => ?_)
      simp [SMSchemeAns.map, sidecarNext, smidSidecar, sidecarLift_sent]
    · simp [PMF.pure_map, SMSchemeAns.map, sidecarNext]
  | recv p =>
    have hc : (sidecarLift ys s).ck.canRecv p = s.ck.canRecv p := rfl
    simp only [smSchemeOracle, SMQuery.mapMsg, hc]
    split
    · simp [PMF.pure_map, SMSchemeAns.map, sidecarNext, smidSidecar, sidecarLift_recvd]
    · simp [PMF.pure_map, SMSchemeAns.map, sidecarNext]
  | send p m =>
    simp only [smSchemeOracle, SMQuery.mapMsg, SMQuery.party, sidecarLift_t]
    split_ifs with hc
    · simp only [smidSidecar, sidecarLift_st]
      cases M.send (s.ck.st p) (sidecarMsg P E (ys p) m)
      · simp [sidecarNext, SMSchemeAns.map, PMF.pure_map]
      · simp [PMF.pure_map, SMSchemeAns.map, sidecarNext, sidecarLift_upd]
        grind
    · simp [PMF.pure_map, SMSchemeAns.map, sidecarNext]
      grind
  | chall p m =>
    simp only [smSchemeOracle, SMQuery.mapMsg, SMQuery.party, sidecarLift_t, sidecarLift_done]
    split_ifs with hc
    · simp only [smidSidecar, sidecarLift_st]
      cases M.send (s.ck.st p) (sidecarMsg P E (ys p) m) <;> cases ideal <;>
        simp [PMF.pure_map, PMF.map_bind, SMSchemeAns.map, sidecarNext, sidecarLift_upd] <;>
        grind
    · simp [PMF.pure_map, SMSchemeAns.map, sidecarNext]
      grind
  | corrupt p =>
    have hc : ckaAllowCorr ΔFS ΔPCS t (sidecarLift ys s).ck p = ckaAllowCorr ΔFS ΔPCS t s.ck p :=
      rfl
    simp only [smSchemeOracle, SMQuery.mapMsg, PMF.pure_map, hc]
    cases ckaAllowCorr ΔFS ΔPCS t s.ck p <;>
      simp [SMSchemeAns.map, sidecarNext, smidSidecar, SMQuery.party]

omit [DecidableEq Pub] [DecidableEq W] [DecidableEq Hdr] [DecidableEq PHdr] [DecidableEq Ct]
  [Fintype Rand] [Nonempty Rand] in
/-- The decoded bookkeeping after a query of the corruption game forwarded by the reduction is
the bookkeeping of the sidecar scheme after the query. -/
theorem sidecarAux_upd (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (P : SidecarDef PSt PHdr S)
    (E : SidecarPack PHdr S W) (x : SMIDAux W Pub Hdr Ct) (sh : CKAGameSt Unit Unit)
    (ys : CKAParty → PSt) (q : SMQuery W) (a : SMSchemeAns Pub Ct Leak) (h : Hdr) :
    sidecarAux E (x.upd M.hdrPos sh (q.mapMsg (sidecarMsg P E (ys q.party))) (a.withHdr h)) =
      (sidecarAux E x).upd (smidSidecar M P E).hdrPos sh q
        ((a.map id id fun l => (l, ys q.party)).withHdr (h, P.hdr (ys q.party))) := by
  cases q with
  | corrupt p =>
    cases a <;> simp only [SMIDAux.upd, SMQuery.mapMsg, SMSchemeAns.withHdr, SMSchemeAns.map]
    simp only [sidecarAux, SMIDAux.mk.injEq, true_and]
    exact congrArg (fun l => (p, sh, l) :: x.corrs) (pending_sidecarAux E x sh p).symm
  | _ =>
    cases a <;>
      simp [SMIDAux.upd, SMQuery.mapMsg, SMSchemeAns.withHdr, SMSchemeAns.map, sidecarAux,
        SMIDAux.record, sidecarEntry, sidecarMsg, E.unpack_pack, smidSidecar, SMQuery.party]

omit [DecidableEq Pub] [DecidableEq W] [DecidableEq Hdr] [DecidableEq PHdr] [DecidableEq Ct]
  [Fintype Rand] [Nonempty Rand] in
/-- The gate of the decoded bookkeeping at a forwarded query. -/
theorem smIDGate_sidecar (P : SidecarDef PSt PHdr S) (E : SidecarPack PHdr S W)
    (x : SMIDAux W Pub Hdr Ct) (sh : CKAGameSt Unit Unit) (y : PSt) (q : SMQuery W) :
    smIDGate (sidecarAux E x) sh q = smIDGate x sh (q.mapMsg (sidecarMsg P E y)) := by
  cases q <;> simp [smIDGate, SMQuery.mapMsg, storeClear_sidecarAux]

omit [DecidableEq Pub] [DecidableEq W] [DecidableEq Hdr] [DecidableEq PHdr] [DecidableEq Ct]
  [Fintype Rand] [Nonempty Rand] in
/-- The epoch counters of a lifted state. -/
theorem ckaShadow_sidecarLift (ys : CKAParty → PSt) (s : SMSchemeSt St Pub) :
    ckaShadow (sidecarLift ys s).ck = ckaShadow s.ck := rfl

/-- **A query of the corruption game in the game with the salts recorded**, viewed in the game
over the sidecar scheme, is the query of that game. -/
theorem sidecarGhostOracle_view_sm (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (P : SidecarDef PSt PHdr S) (E : SidecarPack PHdr S W) (ΔFS ΔPCS t : ℕ) (idealC : Bool)
    (idealD : ℕ → Bool) (σ : (CKAParty → PSt) × (SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct))
    (q : SMQuery W) :
    (sidecarGhostOracle M P E ΔFS ΔPCS t idealC idealD σ (.sm q)).map
        (Prod.map id (sidecarView E)) =
      smIDOracleAt (smidSidecar M P E) ΔFS ΔPCS t idealC idealD (sidecarView E σ) (.sm q) := by
  simp only [sidecarGhostOracle, OracleAdv.simOracle, sidecarImpl, OracleAdv.run_query,
    OracleAdv.run_ret, smIDOracleAt, sidecarView, ckaShadow_sidecarLift,
    smIDGate_sidecar P E σ.2.2 _ (σ.1 q.party) q]
  split_ifs with hg
  · rw [smSchemeOracle_sidecar]
    simp only [PMF.map_bind, PMF.pure_map, PMF.map_comp]
    rw [PMF.bind_map, ← PMF.bind_pure_comp]
    refine congrArg _ (funext fun y => ?_)
    have hp : (q.mapMsg (sidecarMsg P E (σ.1 q.party))).party = q.party := by cases q <;> rfl
    simp only [Function.comp_apply, Prod.map, id, sidecarView, hp]
    simp [sidecarAns, SMIDAns.map, SMSchemeAns.withHdr_map, sidecarNextID, sidecarNext_withHdr,
      sidecarAux_upd, smidSidecar]
  · simp [PMF.pure_map, sidecarAns, SMIDAns.map, SMSchemeAns.map, sidecarNextID, sidecarNext]
    rfl

omit [DecidableEq Pub] [DecidableEq W] [DecidableEq Hdr] [DecidableEq PHdr] [DecidableEq Ct]
  [Fintype Rand] [Nonempty Rand] in
/-- Unfolding lemma of `sidecarAux` at `SMIDAux.epochOf`: the decoding keeps the public values. -/
@[simp] theorem epochOf_sidecarAux [DecidableEq Pub] (E : SidecarPack PHdr S W)
    (x : SMIDAux W Pub Hdr Ct) (sh : CKAGameSt Unit Unit) (p : CKAParty) (T : Pub) :
    (sidecarAux E x).epochOf sh p T = x.epochOf sh p T := rfl

omit [DecidableEq Pub] [DecidableEq W] [DecidableEq Hdr] [DecidableEq PHdr] [DecidableEq Ct]
  [Fintype Rand] [Nonempty Rand] in
/-- Unfolding lemma of `sidecarAux` at `SMIDAux.safe`: the decoding keeps the corruptions. -/
@[simp] theorem safe_sidecarAux (E : SidecarPack PHdr S W) (ΔFS ΔPCS : ℕ)
    (x : SMIDAux W Pub Hdr Ct) (p : CKAParty) (e j : ℕ) :
    (sidecarAux E x).safe ΔFS ΔPCS p e j = x.safe ΔFS ΔPCS p e j := rfl

omit [DecidableEq Pub] [Fintype Rand] [Nonempty Rand] in
/-- The decoded bookkeeping after `sidecarMark` is the marked decoded bookkeeping. -/
theorem sidecarAux_mark (E : SidecarPack PHdr S W) (x : SMIDAux W Pub Hdr Ct) (e : ℕ)
    (h : Hdr × PHdr) (ad : W) (c : Ct) :
    sidecarAux E (sidecarMark E x e h ad c) = (sidecarAux E x).mark e h ad c := by
  simp only [sidecarAux, sidecarMark, SMIDAux.mark, List.map_map, SMIDAux.mk.injEq, and_true]
  refine List.map_congr_left fun l _ => ?_
  simp only [Function.comp_apply]
  split <;> rfl

omit [Fintype Rand] [Nonempty Rand] in
/-- **The delivery with the salts recorded**, viewed in the game over the sidecar scheme, is the
delivery of that game. -/
theorem sidecarGhostDeliver_view (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (P : SidecarDef PSt PHdr S) (E : SidecarPack PHdr S W) (ΔFS ΔPCS : ℕ) (idealD : ℕ → Bool)
    (σ : (CKAParty → PSt) × (SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct)) (p : CKAParty)
    (h : Hdr × PHdr) (ad : W) (c : Ct) :
    Prod.map id (sidecarView E) (sidecarGhostDeliver M P E ΔFS ΔPCS idealD σ p h ad c) =
      smIDDeliver (smidSidecar M P E) ΔFS ΔPCS idealD (sidecarView E σ) p h ad c := by
  simp only [sidecarGhostDeliver, smIDDeliver, sidecarView, ckaShadow_sidecarLift,
    epochOf_sidecarAux, safe_sidecarAux, sidecarLift_st]
  rcases hE : σ.2.2.epochOf (ckaShadow σ.2.1.ck) p ((smidSidecar M P E).hdrPub h) with _ | e
  · simp only [smidSidecar] at hE
    simp only [hE]
    rfl
  · simp only [smidSidecar] at hE ⊢
    simp only [hE]
    by_cases hs : σ.2.2.safe ΔFS ΔPCS p e (M.hdrPos h.1) = true
    · simp only [hs, ↓reduceIte]
      rcases hM : M.rkey (σ.2.1.ck.st p) h.1 with _ | a
      · simp [sidecarView]
      rcases hP : P.rkey (σ.1 p) h.2 with _ | b
      · simp [sidecarView]
      simp only
      cases idealD e
      · rcases M.decrypt a.2 h.1 (E.pack h.2 b.2 ad) c with _ | m
        · simp [sidecarView]
        · simp [sidecarView, sidecarLift_upd, sidecarAux_mark]
      · rcases ((sidecarAux E σ.2.2).findEntry e h ad c) with _ | l
        · simp [sidecarView]
        · simp [sidecarView, sidecarLift_upd, sidecarAux_mark]
    · simp [hs, sidecarView]

omit [DecidableEq Pub] [Fintype Rand] [Nonempty Rand] in
/-- An entry whose logged associated data carries the salt `s` matches the delivery with that
salt packed exactly when its decoded entry matches the delivery. -/
theorem isMatch_sidecar (E : SidecarPack PHdr S W) (l : SMIDLogEntry W Hdr Ct) (e : ℕ)
    (h : Hdr × PHdr) (ad : W) (c : Ct) (s : S)
    (hl : ((sidecarEntry E l).isMatch l.e h ad c && decide (l.ad ≠ E.pack h.2 s ad)) = false) :
    l.isMatch e h.1 (E.pack h.2 s ad) c = (sidecarEntry E l).isMatch e h ad c := by
  have hu := E.unpack_pack h.2 s ad
  simp only [SMIDLogEntry.isMatch, sidecarEntry, Bool.and_eq_false_iff, decide_eq_false_iff_not,
    not_not] at hl ⊢
  by_cases had : l.ad = E.pack h.2 s ad
  · grind
  · grind

omit [DecidableEq Pub] [DecidableEq W] [DecidableEq Hdr] [DecidableEq PHdr] [DecidableEq Ct]
  [Fintype Rand] [Nonempty Rand] in
/-- `List.find?` with predicates that agree on the members of the list. -/
theorem find?_congr_mem {α : Type} {f g : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.find? f = l.find? g
  | [], _ => rfl
  | a :: l, hfg => by
    simp only [List.find?_cons, hfg a List.mem_cons_self,
      find?_congr_mem fun x hx => hfg x (List.mem_cons_of_mem a hx)]

/-- **Up to a wrong salt, the reduction answers as the game with the salts recorded.** -/
theorem sidecarGhost_agree (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (P : SidecarDef PSt PHdr S) (E : SidecarPack PHdr S W) (ΔFS ΔPCS t : ℕ) (idealC : Bool)
    (idealD : ℕ → Bool) (σ : (CKAParty → PSt) × (SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct))
    (d : SMIDQuery W (Hdr × PHdr) Ct) (hb : sidecarWrongSalt P E σ d = false) :
    OracleAdv.simOracle (sidecarImpl P E) (smIDOracleAt M ΔFS ΔPCS t idealC idealD) σ d =
      sidecarGhostOracle M P E ΔFS ΔPCS t idealC idealD σ d := by
  cases d with
  | sm q => rfl
  | deliver p h ad c =>
    simp only [sidecarGhostOracle, OracleAdv.simOracle, sidecarGhostDeliver]
    rcases hP : P.rkey (σ.1 p) h.2 with _ | b
    · simp only [sidecarImpl, hP, OracleAdv.run_ret, PMF.pure_map]
      split <;> (try split) <;> (try split) <;> first | rfl | simp_all
    · have hb' : ∀ l ∈ σ.2.2.log, ((sidecarEntry E l).isMatch l.e h ad c &&
          decide (l.ad ≠ E.pack h.2 b.2 ad)) = false := by
        simpa [sidecarWrongSalt, hP, List.any_eq_false] using hb
      have hm : ∀ e, ∀ l ∈ σ.2.2.log, l.isMatch e h.1 (E.pack h.2 b.2 ad) c =
          (sidecarEntry E l).isMatch e h ad c :=
        fun e l hl => isMatch_sidecar E l e h ad c b.2 (hb' l hl)
      have hfind : ∀ e, (σ.2.2.findEntry e h.1 (E.pack h.2 b.2 ad) c).map SMIDLogEntry.pt =
          ((sidecarAux E σ.2.2).findEntry e h ad c).map SMIDLogEntry.pt := by
        intro e
        simp only [SMIDAux.findEntry, sidecarAux, List.find?_map, Option.map_map]
        rw [find?_congr_mem (hm e)]
        rfl
      have hmark : ∀ e, σ.2.2.mark e h.1 (E.pack h.2 b.2 ad) c = sidecarMark E σ.2.2 e h ad c := by
        intro e
        simp only [SMIDAux.mark, sidecarMark]
        rw [List.map_congr_left fun l hl => by rw [hm e l hl]]
      simp only [sidecarImpl, hP, OracleAdv.run_query, OracleAdv.run_ret, smIDOracleAt,
        PMF.pure_bind, PMF.pure_map]
      congr 1
      unfold smIDDeliver
      rcases hE : σ.2.2.epochOf (ckaShadow σ.2.1.ck) p (M.hdrPub h.1) with _ | e
      · simp [sidecarAns, SMIDAns.map, sidecarCommit]
      · by_cases hs : σ.2.2.safe ΔFS ΔPCS p e (M.hdrPos h.1) = true
        · simp only [hs, ↓reduceIte]
          rcases hM : M.rkey (σ.2.1.ck.st p) h.1 with _ | a
          · simp [sidecarAns, SMIDAns.map, sidecarCommit]
          · simp only
            rw [← hfind e]
            generalize (if idealD e = true then
              Option.map SMIDLogEntry.pt (σ.2.2.findEntry e h.1 (E.pack h.2 b.2 ad) c)
              else M.decrypt a.2 h.1 (E.pack h.2 b.2 ad) c) = r
            cases r <;> simp [sidecarAns, SMIDAns.map, sidecarCommit, hmark]
        · simp [hs, sidecarAns, SMIDAns.map, sidecarCommit]

/-! ## The games -/

omit [DecidableEq PHdr] in
/-- The game over `M` against `sidecarRed P E A` is the run of `A` against the simulator and
the oracle of `M`. -/
theorem smIDGameAt_sidecarRed (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (P : SidecarDef PSt PHdr S) (E : SidecarPack PHdr S W) (ΔFS ΔPCS : ℕ) (idealC : Bool)
    (idealD : ℕ → Bool) (A : SMIDAdv Pub W (Hdr × PHdr) Ct (Leak × PSt)) :
    smIDGameAt M ΔFS ΔPCS idealC idealD (sidecarRed P E A) =
      SPComp.bind (liftPMF A.tStar) fun t => SPComp.bind M.init fun i =>
        liftPMF ((OracleAdv.run (OracleAdv.simOracle (sidecarImpl P E)
          (smIDOracleAt M ΔFS ΔPCS t idealC idealD)) (A.play t i.1)
          (sidecarInitSt P, (SMSchemeSt.init i, SMIDAux.init i.1))).map Prod.fst) := by
  simp only [smIDGameAt, sidecarRed]
  refine congrArg _ (funext fun t => congrArg _ (funext fun i => congrArg _ ?_))
  rw [OracleAdv.run_simulate_fst]

/-- The game over the sidecar scheme is the run of `A` against the game with the salts
recorded. -/
theorem smIDGameAt_sidecar_ghost (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (P : SidecarDef PSt PHdr S) (E : SidecarPack PHdr S W) (ΔFS ΔPCS : ℕ) (idealC : Bool)
    (idealD : ℕ → Bool) (A : SMIDAdv Pub W (Hdr × PHdr) Ct (Leak × PSt)) :
    smIDGameAt (smidSidecar M P E) ΔFS ΔPCS idealC idealD A =
      SPComp.bind (liftPMF A.tStar) fun t => SPComp.bind M.init fun i =>
        liftPMF ((OracleAdv.run (sidecarGhostOracle M P E ΔFS ΔPCS t idealC idealD)
          (A.play t i.1) (sidecarInitSt P, (SMSchemeSt.init i, SMIDAux.init i.1))).map
            Prod.fst) := by
  have hinit : (smidSidecar M P E).init = SPComp.bind M.init fun i =>
      SPComp.pure (i.1, (i.2.1, P.init.1), (i.2.2, P.init.2)) := rfl
  simp only [smIDGameAt, hinit, SPComp.bind_assoc, SPComp.pure_bind]
  refine congrArg _ (funext fun t => congrArg _ (funext fun i => congrArg _ ?_))
  have hv : sidecarView E (sidecarInitSt P, ((SMSchemeSt.init i : SMSchemeSt St Pub),
      (SMIDAux.init i.1 : SMIDAux W Pub Hdr Ct))) =
      (SMSchemeSt.init (i.1, (i.2.1, P.init.1), (i.2.2, P.init.2)), SMIDAux.init i.1) := by
    simp only [sidecarView, sidecarLift, SMSchemeSt.init, CKAGameSt.init, sidecarAux,
      SMIDAux.init, List.map_nil, Prod.mk.injEq, SMSchemeSt.mk.injEq, CKAGameSt.mk.injEq,
      and_true]
    funext p
    cases p <;> rfl
  have hstep : ∀ σ d, (sidecarGhostOracle M P E ΔFS ΔPCS t idealC idealD σ d).map
      (Prod.map id (sidecarView E)) =
      smIDOracleAt (smidSidecar M P E) ΔFS ΔPCS t idealC idealD (sidecarView E σ) d := by
    intro σ d
    cases d with
    | sm q => exact sidecarGhostOracle_view_sm M P E ΔFS ΔPCS t idealC idealD σ q
    | deliver p h ad c =>
      simp only [sidecarGhostOracle, smIDOracleAt, PMF.pure_map,
        ← sidecarGhostDeliver_view]
      rfl
  rw [← hv, ← OracleAdv.run_map_state _ _ (sidecarView E) hstep, PMF.map_comp]
  rfl

/-- **The sidecar scheme against the reduction, up to a wrong salt.** The game over `M`
against `sidecarRed P E A` and the game over `smidSidecar M P E` against `A`, with the same
challenge and decryption modes, differ by at most the probability of a wrong salt in the game
over the sidecar scheme. -/
theorem smIDGame_sidecar (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (P : SidecarDef PSt PHdr S) (E : SidecarPack PHdr S W) (ΔFS ΔPCS : ℕ) (idealC : Bool)
    (idealD : ℕ → Bool) (A : SMIDAdv Pub W (Hdr × PHdr) Ct (Leak × PSt)) :
    Advantage (smIDGameAt M ΔFS ΔPCS idealC idealD (sidecarRed P E A))
        (smIDGameAt (smidSidecar M P E) ΔFS ΔPCS idealC idealD A) ≤
      prTrue (sidecarBadGame M P E ΔFS ΔPCS idealC idealD A) Heap.empty := by
  have hmap : ∀ (O : ((CKAParty → PSt) × (SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct)) →
      SMIDQuery W (Hdr × PHdr) Ct → PMF (SMIDAns Pub (Hdr × PHdr) Ct (Leak × PSt) W ×
        ((CKAParty → PSt) × (SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct))))
      (B : OracleAdv (SMIDQuery W (Hdr × PHdr) Ct) (SMIDAns Pub (Hdr × PHdr) Ct (Leak × PSt) W)
        Bool) σ,
      (OracleAdv.run (OracleAdv.flagWhen (fun σ d _ => sidecarWrongSalt P E σ d = true) O) B
        (σ, false)).map Prod.fst = (OracleAdv.run O B σ).map Prod.fst := by
    intro O B σ
    rw [← OracleAdv.run_flagWhen_map (fun σ d _ => sidecarWrongSalt P E σ d = true) O B σ false,
      PMF.map_comp]
    rfl
  have h := advantage_bind_liftPMF_le_flag A.tStar M.init
    (fun t i => OracleAdv.run (OracleAdv.flagWhen (fun σ d _ => sidecarWrongSalt P E σ d = true)
      (OracleAdv.simOracle (sidecarImpl P E) (smIDOracleAt M ΔFS ΔPCS t idealC idealD)))
      (A.play t i.1) ((sidecarInitSt P, (SMSchemeSt.init i, SMIDAux.init i.1)), false))
    (fun t i => OracleAdv.run (OracleAdv.flagWhen (fun σ d _ => sidecarWrongSalt P E σ d = true)
      (sidecarGhostOracle M P E ΔFS ΔPCS t idealC idealD))
      (A.play t i.1) ((sidecarInitSt P, (SMSchemeSt.init i, SMIDAux.init i.1)), false))
    (fun t i a s => OracleAdv.run_flagWhen_apply_false_eq _ _ _
      (fun σ d _ hx => by
        rw [sidecarGhost_agree M P E ΔFS ΔPCS t idealC idealD σ d (by simpa using hx)]) _ _ a s)
  simp only [hmap] at h
  rw [smIDGameAt_sidecarRed, smIDGameAt_sidecar_ghost]
  exact h

/-- **The advantage against the sidecar scheme.** For every sidecar `P`, every encoding `E`
and every adversary `A`, the advantage against `smidSidecar M P E` is at most the advantage
against `M` of `sidecarRed P E A` plus the probabilities of a wrong salt in the real game and
in the game with a uniform challenge and decryption from the log. The injective packing
`SidecarPack` into a finite word type forces a single salt and a single sidecar header, so the
statement applies only to runs with a constant salt. -/
theorem SMIDScheme.idAdvantage_sidecar_le (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (P : SidecarDef PSt PHdr S) (E : SidecarPack PHdr S W) (ΔFS ΔPCS : ℕ)
    (A : SMIDAdv Pub W (Hdr × PHdr) Ct (Leak × PSt)) :
    (smidSidecar M P E).idAdvantage ΔFS ΔPCS A ≤
      M.idAdvantage ΔFS ΔPCS (sidecarRed P E A) +
        prTrue (sidecarBadGame M P E ΔFS ΔPCS false (fun _ => false) A) Heap.empty +
        prTrue (sidecarBadGame M P E ΔFS ΔPCS true (fun _ => true) A) Heap.empty := by
  have h1 := smIDGame_sidecar M P E ΔFS ΔPCS false (fun _ => false) A
  have h2 := smIDGame_sidecar M P E ΔFS ΔPCS true (fun _ => true) A
  have hsymm : ∀ G₀ G₁ : SPComp Bool, Advantage G₀ G₁ = Advantage G₁ G₀ := fun G₀ G₁ => by
    simp only [Advantage, max_comm]
  unfold SMIDScheme.idAdvantage smIDGame
  calc _ ≤ Advantage (smIDGameAt (smidSidecar M P E) ΔFS ΔPCS false (fun _ => false) A)
          (smIDGameAt M ΔFS ΔPCS false (fun _ => false) (sidecarRed P E A)) +
        Advantage (smIDGameAt M ΔFS ΔPCS false (fun _ => false) (sidecarRed P E A))
          (smIDGameAt (smidSidecar M P E) ΔFS ΔPCS true (fun _ => true) A) :=
        advantage_triangle _ _ _
    _ ≤ Advantage (smIDGameAt (smidSidecar M P E) ΔFS ΔPCS false (fun _ => false) A)
          (smIDGameAt M ΔFS ΔPCS false (fun _ => false) (sidecarRed P E A)) +
        (Advantage (smIDGameAt M ΔFS ΔPCS false (fun _ => false) (sidecarRed P E A))
          (smIDGameAt M ΔFS ΔPCS true (fun _ => true) (sidecarRed P E A)) +
        Advantage (smIDGameAt M ΔFS ΔPCS true (fun _ => true) (sidecarRed P E A))
          (smIDGameAt (smidSidecar M P E) ΔFS ΔPCS true (fun _ => true) A)) :=
        add_le_add le_rfl (advantage_triangle _ _ _)
    _ ≤ prTrue (sidecarBadGame M P E ΔFS ΔPCS false (fun _ => false) A) Heap.empty +
          (Advantage (smIDGameAt M ΔFS ΔPCS false (fun _ => false) (sidecarRed P E A))
            (smIDGameAt M ΔFS ΔPCS true (fun _ => true) (sidecarRed P E A)) +
          prTrue (sidecarBadGame M P E ΔFS ΔPCS true (fun _ => true) A) Heap.empty) :=
        add_le_add ((hsymm _ _).le.trans h1) (add_le_add le_rfl h2)
    _ = _ := by ring

/-! ## AEADs with relabelled associated data -/

section ComapAD

variable {W' : Type} [SampleableType W'] {C : Type} [SampleableType C] {AD AD' Kt : Type}
  [SampleableType Kt]

/-- The AEAD `D` with its associated data read through `ρ`. -/
def aeadComapAD (D : AEADDef W' C AD Kt) (ρ : AD' → AD) : AEADDef W' C AD' Kt where
  encrypt k pt ad := D.encrypt k pt (ρ ad)
  decrypt k ct ad := D.decrypt k ct (ρ ad)

/-- A query of the authenticated-encryption game with its associated data relabelled. -/
def aeadQueryMapAD (ρ : AD' → AD) : AEAD_CCA_Query W' C AD' → AEAD_CCA_Query W' C AD
  | .inl (pt, ad) => .inl (pt, ρ ad)
  | .inr (ct, ad) => .inr (ct, ρ ad)

/-- **Reduction** for relabelled associated data: run `A` with the associated data of each query
relabelled by `ρ`. -/
def aeadAdvMapAD (ρ : AD' → AD) (A : AEAD_CCA_Adversary W' C AD') : AEAD_CCA_Adversary W' C AD :=
  A.mapQueryAnswer (aeadQueryMapAD ρ) id

/-- The log of the ideal oracles with its associated data relabelled. -/
def aeadLogMapAD (ρ : AD' → AD) (L : List ((W' × AD') × C)) : List ((W' × AD) × C) :=
  L.map fun e => ((e.1.1, ρ e.1.2), e.2)

omit [SampleableType Kt] [SampleableType C] in
/-- The real oracles of the relabelled AEAD are the real oracles of `D` at relabelled
queries. -/
theorem aeadRealOracle_comapAD (D : AEADDef W' C AD Kt) (ρ : AD' → AD) (k : Kt) (u : Unit)
    (q : AEAD_CCA_Query W' C AD') :
    aeadRealOracle (aeadComapAD D ρ) k u q =
      (aeadRealOracle D k u (aeadQueryMapAD ρ q)).map fun x => (id x.1, x.2) := by
  rcases q with ⟨pt, ad⟩ | ⟨ct, ad⟩ <;> simp [aeadRealOracle, aeadQueryMapAD, aeadComapAD,
    PMF.pure_map]

/-- The ideal oracles at a relabelled log are the ideal oracles at the relabelled query, for an
injective relabelling. -/
theorem aeadIdealOracle_mapAD [DecidableEq AD] [DecidableEq AD']
    (ρ : AD' → AD) (hρ : Function.Injective ρ) (L : List ((W' × AD') × C))
    (q : AEAD_CCA_Query W' C AD') :
    (aeadIdealOracle L q).map (Prod.map id (aeadLogMapAD ρ)) =
      (aeadIdealOracle (aeadLogMapAD ρ L) (aeadQueryMapAD ρ q)).map fun x => (id x.1, x.2) := by
  have hlk : ∀ (pt : W') (ad : AD') (L : List ((W' × AD') × C)),
      (aeadLogMapAD ρ L).lookup (pt, ρ ad) = L.lookup (pt, ad) := by
    intro pt ad L
    induction L with
    | nil => rfl
    | cons e L ih =>
      simp only [aeadLogMapAD, List.map_cons, List.lookup_cons] at ih ⊢
      rcases e with ⟨⟨pt', ad'⟩, ct'⟩
      have hb : ((pt, ρ ad) == (pt', ρ ad')) = ((pt, ad) == (pt', ad')) := by
        simp [hρ.eq_iff]
      simp only [ih, hb, List.lookup_cons]
  have hdec : ∀ (ct : C) (ad : AD') (L : List ((W' × AD') × C)),
      aeadLogDecrypt (aeadLogMapAD ρ L) ct (ρ ad) = aeadLogDecrypt L ct ad := by
    intro ct ad L
    simp only [aeadLogDecrypt, aeadLogMapAD, List.find?_map, Option.map_map]
    congr 1
    · congr 1
      funext e
      simp [hρ.eq_iff]
  rcases q with ⟨pt, ad⟩ | ⟨ct, ad⟩
  · simp only [aeadIdealOracle, aeadQueryMapAD]
    rw [hlk]
    cases L.lookup (pt, ad) with
    | some ct => simp [PMF.pure_map]
    | none => simp [PMF.map_comp, Function.comp_def, aeadLogMapAD]
  · simp [aeadIdealOracle, aeadQueryMapAD, hdec, PMF.pure_map]

/-- **The advantage of an AEAD with relabelled associated data.** For an injective `ρ`, the
advantage of `A` against `aeadComapAD D ρ` is the advantage against `D` of `aeadAdvMapAD ρ A`. -/
theorem AEAD_CCA_Advantage_comapAD [DecidableEq AD] [DecidableEq AD']
    (D : AEADDef W' C AD Kt) (ρ : AD' → AD) (hρ : Function.Injective ρ)
    (A : AEAD_CCA_Adversary W' C AD') :
    AEAD_CCA_Advantage (aeadComapAD D ρ) A = AEAD_CCA_Advantage D (aeadAdvMapAD ρ A) := by
  unfold AEAD_CCA_Advantage AEAD_CCA_Game_Real AEAD_CCA_Game_Ideal aeadAdvMapAD
  congr 2
  · congr 1
    funext k
    rw [OracleAdv.run_mapQueryAnswer]
    congr 1
    congr 1
    funext u q
    exact aeadRealOracle_comapAD D ρ k u q
  · rw [OracleAdv.run_mapQueryAnswer]
    have h := OracleAdv.run_map_state (aeadIdealOracle (W := W') (C := C) (AD := AD'))
      (fun s d => (aeadIdealOracle s (aeadQueryMapAD ρ d)).map fun x => (id x.1, x.2))
      (aeadLogMapAD ρ) (fun L q => aeadIdealOracle_mapAD ρ hρ L q) A []
    rw [show ([] : List ((W' × AD) × C)) = aeadLogMapAD ρ [] from rfl, ← h, PMF.map_comp]
    rfl

end ComapAD

end CatCrypt.Crypto.Messaging
