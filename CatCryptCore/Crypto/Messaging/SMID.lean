/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SMScheme
import CatCryptCore.Tactics.AutoDispatchExt

/-!
# Secure messaging with immediate decryption and headers

The secure-messaging game of Alwen, Coretti and Dodis (EUROCRYPT 2019, §3) with immediate
decryption, stated over a scheme whose ciphertexts carry a public header in the form of the
Signal Double Ratchet specification: the header names the ratchet public key of the epoch and
the position of the message, and decryption looks up the message key of the header, stepping
the receiving chain or taking a stored key of a skipped position.

## Schemes

`SMIDScheme St Pub Rand W Ct Leak Hdr K` extends `SMScheme` by

* `hdr x` — the header `HEADER(DHs, PN, Ns)` of the next ciphertext of a sender in state `x`;
* `hdrPub h`, `hdrPos h` — the ratchet public key and the position named by the header `h`;
* `rkey x h` — `RatchetReceiveKey` without the Diffie–Hellman step: the message key of the
  header `h` and the state with that key used up, or `none` (an unknown ratchet key, a jump
  over the skip bound, a full store, a used position);
* `decrypt k h ad c` — `DECRYPT(mk, c, CONCAT(ad, h))`.

## The game

`smIDGame M ΔFS ΔPCS idealC idealD A` extends the corruption game `smCorruptGame` over
`M.toSMScheme` by the query `deliver p h ad c`. A send or a challenge is answered by the header
of the sender and the ciphertext `(M.hdr x, c)`; in the game with `idealC` the ciphertext of the
challenge is drawn from `M.idealCt` and carries the same header. The game keeps

* the log of the honest ciphertexts with their epoch, position, plaintext, associated data,
  header, ciphertext and a flag `delivered`;
* the public values of the opened epochs, so that the epoch of a delivery is the epoch whose
  public value is the ratchet key of the header among the epochs the receiver has received;
  a header with the ratchet key of no received epoch is rejected in both games;
* for each answered corruption, the party, the epoch counters and, for a corruption of a
  receiver, the undelivered logged positions of its current receiving epoch.

A delivery at the epoch `e` and the position `j` of the header is answered only when every
answered corruption leaves `e` outside its corruption window and, for a corruption of the
receiver, `(e, j)` outside its recorded positions. The real answer (`idealD = false`) runs
`M.rkey` and `M.decrypt`; on success the receiver moves to the state of `M.rkey`, and every
undelivered log entry with the same epoch, header, associated data and ciphertext is marked
delivered. The ideal answer runs `M.rkey` too, so that the rejections of the skip bound and the
store are the same in both games, and answers the plaintext of an undelivered matching entry,
or a rejection with the state unchanged.

A corruption of `p` is answered when `ckaAllowCorr` allows it and, in addition, no undelivered
log entry addressed to `p` belongs to an epoch `p` has received and left (the restricted gate):
a stored key of a closed epoch is never exposed.

* `SMIDScheme.idAdvantage` — the real game against the game with uniform challenge and ideal
  decryption;
* `SMIDScheme.intAdvantage` — the real game against the game with ideal decryption;
* `SMIDScheme.confAdvantage` — the games with ideal decryption, with the real against the
  uniform challenge.

## Transfer

`SMIDScheme.Sim M' M ρ κ encP encC encL encI encH` extends `SMScheme.Sim` of the underlying
schemes by the headers, the key lookup and the decryption: related states give encoded headers,
the lookup of an encoded header from related states gives related states and keys related by
`κ`, and related keys decrypt encoded inputs as the original ones. The encodings `encH` of
headers and `encC` of ciphertexts are equivalences, since the adversary chooses the headers and
ciphertexts of deliveries; the encoding of public values commutes with the ratchet key of a
header. `smIDGameAt_sim` proves that the game of `M'` against `A` is the game of `M` against
`A.comap`, which decodes the deliveries and encodes the answers.

## Main definitions

* `SMIDScheme`, `SMIDQuery`, `SMIDAns`, `SMIDLogEntry`, `SMIDAux`, `smIDGate`, `smIDDeliver`,
  `smIDOracleAt`, `SMIDAdv`, `smIDGameAt`, `smIDGame`
* `SMIDScheme.idAdvantage`, `SMIDScheme.intAdvantage`, `SMIDScheme.confAdvantage`
* `SMIDScheme.Sim`, `SMIDRel`, `SMIDAdv.comap`

## Main results

* `smIDDeliver_sim`, `smID_sim_step` — the delivery and the oracle calls of simulating schemes
* `smIDGameAt_sim`, `smIDGame_sim` — the transfer of the game along a simulation
* `SMIDScheme.Sim.idAdvantage_eq`, `SMIDScheme.Sim.intAdvantage_eq`,
  `SMIDScheme.Sim.confAdvantage_eq` — the transfer of the advantages

## References

* J. Alwen, S. Coretti, Y. Dodis, *The Double Ratchet: Security Notions, Proofs, and
  Modularization for the Signal Protocol*, EUROCRYPT 2019.
* T. Perrin, M. Marlinspike, *The Double Ratchet Algorithm*, Signal specification, 2016.
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

/-! ## Schemes with headers and immediate decryption -/

/-- A secure-messaging scheme with headers and immediate decryption, after the Signal Double
Ratchet specification: party states `St`, public values `Pub`, randomness `Rand`, words `W`,
ciphertext bodies `Ct`, corruption answers `Leak`, headers `Hdr` and message keys `K`. -/
structure SMIDScheme (St Pub Rand W Ct Leak Hdr K : Type)
    extends SMScheme St Pub Rand W Ct Leak where
  /-- The header of the next ciphertext of a sender in state `x`: `HEADER(DHs, PN, Ns)`. -/
  hdr : St → Hdr
  /-- The ratchet public key named by a header. -/
  hdrPub : Hdr → Pub
  /-- The position of the message named by a header. -/
  hdrPos : Hdr → ℕ
  /-- `RatchetReceiveKey` without the DH step: the key of the header from the store or from the
  receiving chain, and the state with it removed; `none` at an unknown ratchet key, a jump over
  `MAX_SKIP`, a full store or a used position. -/
  rkey : St → Hdr → Option (St × K)
  /-- `DECRYPT(mk, c, CONCAT(ad, h))`. -/
  decrypt : K → Hdr → W → Ct → Option W

/-- The party of a query of the corruption game. -/
def SMQuery.party {W : Type} : SMQuery W → CKAParty
  | .ratchet p => p
  | .recv p => p
  | .send p _ => p
  | .chall p _ => p
  | .corrupt p => p

/-- The queries of the game with immediate decryption: a query of the corruption game, or the
delivery of a header `h`, associated data `ad` and a ciphertext `c` to party `p`. -/
inductive SMIDQuery (W Hdr Ct : Type) where
  /-- A query of the corruption game. -/
  | sm (q : SMQuery W)
  /-- The delivery of a ciphertext to a party. -/
  | deliver (p : CKAParty) (h : Hdr) (ad : W) (c : Ct)

/-- The queries with the headers and ciphertexts of deliveries relabelled. -/
def SMIDQuery.map {W Hdr Ct Hdr' Ct' : Type} (f : Hdr → Hdr') (g : Ct → Ct') :
    SMIDQuery W Hdr Ct → SMIDQuery W Hdr' Ct'
  | .sm q => .sm q
  | .deliver p h ad c => .deliver p (f h) ad (g c)

/-- The answers of the game with immediate decryption. -/
inductive SMIDAns (Pub Hdr Ct Leak W : Type) where
  /-- An answer of the corruption game, with the header of a ciphertext. -/
  | sm (a : SMSchemeAns Pub (Hdr × Ct) Leak)
  /-- The answer to a delivery: a plaintext or a rejection. -/
  | dec (m : Option W)

/-- The answers with the public values, headers, ciphertexts and corruption answers
relabelled. -/
def SMIDAns.map {Pub Hdr Ct Leak W Pub' Hdr' Ct' Leak' : Type} (encP : Pub → Pub')
    (encH : Hdr → Hdr') (encC : Ct → Ct') (encL : Leak → Leak') :
    SMIDAns Pub Hdr Ct Leak W → SMIDAns Pub' Hdr' Ct' Leak' W
  | .sm a => .sm (a.map encP (Prod.map encH encC) encL)
  | .dec m => .dec m

/-- An answer of the corruption game with the header `h` attached to a ciphertext. -/
def SMSchemeAns.withHdr {Pub Ct Leak Hdr : Type} (h : Hdr) :
    SMSchemeAns Pub Ct Leak → SMSchemeAns Pub (Hdr × Ct) Leak
  | .none => .none
  | .msg T => .msg T
  | .ct c => .ct (h, c)
  | .state σ => .state σ

/-- Attaching a header commutes with relabelling the answer. -/
theorem SMSchemeAns.withHdr_map {Pub Ct Leak Hdr Pub' Ct' Leak' Hdr' : Type} (encP : Pub → Pub')
    (encH : Hdr → Hdr') (encC : Ct → Ct') (encL : Leak → Leak') (h : Hdr)
    (a : SMSchemeAns Pub Ct Leak) :
    (a.withHdr h).map encP (Prod.map encH encC) encL = (a.map encP encC encL).withHdr (encH h) := by
  cases a <;> rfl

/-- An honest ciphertext: its epoch, the position of its header, the plaintext, the associated
data, the header, the ciphertext, and whether it has been delivered. -/
structure SMIDLogEntry (W Hdr Ct : Type) where
  /-- The epoch. -/
  e : ℕ
  /-- The position named by the header. -/
  j : ℕ
  /-- The plaintext. -/
  pt : W
  /-- The associated data. -/
  ad : W
  /-- The header. -/
  hdr : Hdr
  /-- The ciphertext. -/
  ct : Ct
  /-- The entry has been delivered. -/
  delivered : Bool

namespace SMIDLogEntry

variable {W Hdr Ct Hdr' Ct' : Type}

/-- The entry with the header and the ciphertext relabelled. -/
def map (encH : Hdr → Hdr') (encC : Ct → Ct') (l : SMIDLogEntry W Hdr Ct) :
    SMIDLogEntry W Hdr' Ct' :=
  ⟨l.e, l.j, l.pt, l.ad, encH l.hdr, encC l.ct, l.delivered⟩

/-- The entry is undelivered and has the epoch `e`, the header `h`, the associated data `ad`
and the ciphertext `c`. -/
def isMatch [DecidableEq W] [DecidableEq Hdr] [DecidableEq Ct] (e : ℕ) (h : Hdr) (ad : W)
    (c : Ct) (l : SMIDLogEntry W Hdr Ct) : Bool :=
  !l.delivered && l.e == e && decide (l.hdr = h) && decide (l.ad = ad) && decide (l.ct = c)

/-- An entry relabelled by injective encodings matches the encoded header and ciphertext
exactly when the entry matches the header and ciphertext. -/
theorem isMatch_map [DecidableEq W] [DecidableEq Hdr] [DecidableEq Ct] [DecidableEq Hdr']
    [DecidableEq Ct'] {encH : Hdr → Hdr'} {encC : Ct → Ct'} (hH : Function.Injective encH)
    (hC : Function.Injective encC) (e : ℕ) (h : Hdr) (ad : W) (c : Ct)
    (l : SMIDLogEntry W Hdr Ct) :
    (l.map encH encC).isMatch e (encH h) ad (encC c) = l.isMatch e h ad c := by
  simp only [isMatch, map, hH.eq_iff, hC.eq_iff]; rfl

end SMIDLogEntry

/-- The receiving epoch of party `p` at the epoch counters `sh`: its own epoch when `p` is its
receiver, the epoch before it otherwise. -/
def smRecvEpoch (sh : CKAGameSt Unit Unit) (p : CKAParty) : ℕ :=
  if ckaSender (sh.t p) = p then sh.t p - 1 else sh.t p

/-- The bookkeeping of the game with immediate decryption: the log of the honest ciphertexts,
the public values of the opened epochs, and for every answered corruption the party, the epoch
counters and the recorded positions. -/
structure SMIDAux (W Pub Hdr Ct : Type) where
  /-- The honest ciphertexts. -/
  log : List (SMIDLogEntry W Hdr Ct)
  /-- The opened epochs with their public values. -/
  pubs : List (ℕ × Pub)
  /-- The answered corruptions with the recorded positions. -/
  corrs : List (CKAParty × CKAGameSt Unit Unit × List (ℕ × ℕ))

namespace SMIDAux

variable {W Pub Hdr Ct Leak Pub' Hdr' Ct' Leak' : Type}

/-- The bookkeeping at the initialisation with the public value `T` of the epoch `0`. -/
def init (T : Pub) : SMIDAux W Pub Hdr Ct := ⟨[], [(0, T)], []⟩

/-- The bookkeeping with the public values, headers and ciphertexts relabelled. -/
def map (encP : Pub → Pub') (encH : Hdr → Hdr') (encC : Ct → Ct') (x : SMIDAux W Pub Hdr Ct) :
    SMIDAux W Pub' Hdr' Ct' :=
  ⟨x.log.map (SMIDLogEntry.map encH encC), x.pubs.map (Prod.map id encP), x.corrs⟩

/-- The epoch whose public value is `T` among the epochs party `p` has received at the epoch
counters `sh`: the latest opened such epoch, or `none`. -/
def epochOf [DecidableEq Pub] (x : SMIDAux W Pub Hdr Ct) (sh : CKAGameSt Unit Unit)
    (p : CKAParty) (T : Pub) : Option ℕ :=
  (x.pubs.find? fun q => decide (q.2 = T) && decide (q.1 ≤ sh.t p) && (ckaSender q.1 != p)).map
    Prod.fst

/-- The undelivered logged positions of the current receiving epoch of party `p`. -/
def pending (x : SMIDAux W Pub Hdr Ct) (sh : CKAGameSt Unit Unit) (p : CKAParty) :
    List (ℕ × ℕ) :=
  (x.log.filter fun l => !l.delivered && (ckaSender l.e != p) && l.e == smRecvEpoch sh p).map
    fun l => (l.e, l.j)

/-- No undelivered entry addressed to party `p` belongs to an epoch before its current
receiving epoch: the restricted corruption gate. -/
def storeClear (x : SMIDAux W Pub Hdr Ct) (sh : CKAGameSt Unit Unit) (p : CKAParty) : Bool :=
  x.log.all fun l => l.delivered || ckaSender l.e == p || decide (smRecvEpoch sh p ≤ l.e)

/-- A delivery to party `p` at the epoch `e` and the position `j` is safe: every answered
corruption leaves `e` outside its window, and a corruption of `p` did not record `(e, j)`. -/
def safe (ΔFS ΔPCS : ℕ) (x : SMIDAux W Pub Hdr Ct) (p : CKAParty) (e j : ℕ) : Bool :=
  x.corrs.all fun c => ckaAllowCorr ΔFS ΔPCS e c.2.1 c.1 && (c.1 != p || decide ((e, j) ∉ c.2.2))

/-- The log with an honest ciphertext added. -/
def record (x : SMIDAux W Pub Hdr Ct) (e j : ℕ) (m : W × W) (h : Hdr) (c : Ct) :
    SMIDAux W Pub Hdr Ct :=
  { x with log := ⟨e, j, m.1, m.2, h, c, false⟩ :: x.log }

/-- The bookkeeping after the query `q` of the corruption game, answered by `a`, at the epoch
counters `sh` before the query, with the positions of headers read by `pos`: an opened epoch is
recorded with its public value, a ciphertext of a send or a challenge is logged, an answered
corruption is recorded with the counters and the pending positions. -/
def upd (pos : Hdr → ℕ) (x : SMIDAux W Pub Hdr Ct) (sh : CKAGameSt Unit Unit) :
    SMQuery W → SMSchemeAns Pub (Hdr × Ct) Leak → SMIDAux W Pub Hdr Ct
  | .ratchet p, .msg T => { x with pubs := (sh.t p + 1, T) :: x.pubs }
  | .send p m, .ct hc => x.record (sh.t p) (pos hc.1) m hc.1 hc.2
  | .chall p m, .ct hc => x.record (sh.t p) (pos hc.1) m hc.1 hc.2
  | .corrupt p, .state _ => { x with corrs := (p, sh, x.pending sh p) :: x.corrs }
  | _, _ => x

/-- The first undelivered entry with the epoch `e`, the header `h`, the associated data `ad`
and the ciphertext `c`. -/
def findEntry [DecidableEq W] [DecidableEq Hdr] [DecidableEq Ct] (x : SMIDAux W Pub Hdr Ct)
    (e : ℕ) (h : Hdr) (ad : W) (c : Ct) : Option (SMIDLogEntry W Hdr Ct) :=
  x.log.find? (SMIDLogEntry.isMatch e h ad c)

/-- The log with every undelivered entry with the epoch `e`, the header `h`, the associated
data `ad` and the ciphertext `c` marked delivered. -/
def mark [DecidableEq W] [DecidableEq Hdr] [DecidableEq Ct] (x : SMIDAux W Pub Hdr Ct)
    (e : ℕ) (h : Hdr) (ad : W) (c : Ct) : SMIDAux W Pub Hdr Ct :=
  { x with log := x.log.map fun l => if l.isMatch e h ad c then { l with delivered := true }
    else l }

/-- Unfolding lemma of `map` at the initial bookkeeping. -/
@[simp] theorem init_map (encP : Pub → Pub') (encH : Hdr → Hdr') (encC : Ct → Ct') (T : Pub) :
    (init T : SMIDAux W Pub Hdr Ct).map encP encH encC = init (encP T) := rfl

/-- Unfolding lemma of `safe` at a relabelled bookkeeping: `map` keeps the corruptions. -/
@[simp] theorem safe_map (encP : Pub → Pub') (encH : Hdr → Hdr') (encC : Ct → Ct')
    (ΔFS ΔPCS : ℕ) (x : SMIDAux W Pub Hdr Ct) (p : CKAParty) (e j : ℕ) :
    (x.map encP encH encC).safe ΔFS ΔPCS p e j = x.safe ΔFS ΔPCS p e j := rfl

/-- The epoch of a public value `T'` in the relabelled bookkeeping is the epoch of `T` when
`T'` is the encoding of `T` and of no other value. -/
theorem epochOf_map [DecidableEq Pub] [DecidableEq Pub'] (encP : Pub → Pub') (encH : Hdr → Hdr')
    (encC : Ct → Ct') (x : SMIDAux W Pub Hdr Ct) (sh : CKAGameSt Unit Unit) (p : CKAParty)
    (T' : Pub') (T : Pub) (hT : ∀ U, encP U = T' ↔ U = T) :
    (x.map encP encH encC).epochOf sh p T' = x.epochOf sh p T := by
  simp only [epochOf, map, List.find?_map, Option.map_map, Function.comp_def, Prod.map_fst,
    Prod.map_snd, id_eq, hT]

/-- Relabelling keeps the restricted corruption gate. -/
theorem storeClear_map (encP : Pub → Pub') (encH : Hdr → Hdr') (encC : Ct → Ct')
    (x : SMIDAux W Pub Hdr Ct) (sh : CKAGameSt Unit Unit) (p : CKAParty) :
    (x.map encP encH encC).storeClear sh p = x.storeClear sh p := by
  simp only [storeClear, map, List.all_map, SMIDLogEntry.map, Function.comp_def]; rfl

/-- Relabelling keeps the pending positions. -/
theorem pending_map (encP : Pub → Pub') (encH : Hdr → Hdr') (encC : Ct → Ct')
    (x : SMIDAux W Pub Hdr Ct) (sh : CKAGameSt Unit Unit) (p : CKAParty) :
    (x.map encP encH encC).pending sh p = x.pending sh p := by
  simp [pending, map, List.filter_map, List.map_map, SMIDLogEntry.map, Function.comp_def]

/-- Updating the bookkeeping commutes with relabelling, when the positions of encoded headers
are those of the headers. -/
theorem upd_map (encP : Pub → Pub') (encH : Hdr → Hdr') (encC : Ct → Ct') (encL : Leak → Leak')
    (pos : Hdr → ℕ) (pos' : Hdr' → ℕ) (hpos : ∀ h, pos' (encH h) = pos h)
    (x : SMIDAux W Pub Hdr Ct) (sh : CKAGameSt Unit Unit) (q : SMQuery W)
    (a : SMSchemeAns Pub (Hdr × Ct) Leak) :
    (x.upd pos sh q a).map encP encH encC =
      (x.map encP encH encC).upd pos' sh q (a.map encP (Prod.map encH encC) encL) := by
  cases q <;> cases a <;> simp only [upd, SMSchemeAns.map, Prod.map_fst, Prod.map_snd, hpos]
  all_goals first
    | rfl
    | (rw [← pending_map encP encH encC]; rfl)

/-- The plaintext found for an encoded header and ciphertext in the relabelled bookkeeping is
the plaintext found for the header and ciphertext. -/
theorem findEntry_map [DecidableEq W] [DecidableEq Hdr] [DecidableEq Ct] [DecidableEq Hdr']
    [DecidableEq Ct'] (encP : Pub → Pub') {encH : Hdr → Hdr'} {encC : Ct → Ct'}
    (hH : Function.Injective encH) (hC : Function.Injective encC) (x : SMIDAux W Pub Hdr Ct)
    (e : ℕ) (h : Hdr) (ad : W) (c : Ct) :
    ((x.map encP encH encC).findEntry e (encH h) ad (encC c)).map SMIDLogEntry.pt =
      (x.findEntry e h ad c).map SMIDLogEntry.pt := by
  have hf : (SMIDLogEntry.isMatch e (encH h) ad (encC c) ∘ SMIDLogEntry.map encH encC) =
      SMIDLogEntry.isMatch e h ad c :=
    funext fun l => SMIDLogEntry.isMatch_map hH hC e h ad c l
  simp only [findEntry, map, List.find?_map, Option.map_map, hf]
  rfl

/-- Marking entries delivered commutes with relabelling by injective encodings. -/
theorem mark_map [DecidableEq W] [DecidableEq Hdr] [DecidableEq Ct] [DecidableEq Hdr']
    [DecidableEq Ct'] (encP : Pub → Pub') {encH : Hdr → Hdr'} {encC : Ct → Ct'}
    (hH : Function.Injective encH) (hC : Function.Injective encC) (x : SMIDAux W Pub Hdr Ct)
    (e : ℕ) (h : Hdr) (ad : W) (c : Ct) :
    (x.mark e h ad c).map encP encH encC =
      (x.map encP encH encC).mark e (encH h) ad (encC c) := by
  simp only [mark, map, List.map_map, SMIDAux.mk.injEq, and_true]
  refine List.map_congr_left fun l _ => ?_
  simp only [Function.comp_apply, SMIDLogEntry.isMatch_map hH hC]
  split <;> rfl

end SMIDAux

/-! ## The game -/

section Game

variable {St Pub Rand W Ct Leak Hdr K : Type} [Fintype Rand] [Nonempty Rand] [DecidableEq Pub]
  [DecidableEq W] [DecidableEq Hdr] [DecidableEq Ct]

/-- The gate of the queries of the corruption game in the game with immediate decryption: a
corruption of `p` needs `SMIDAux.storeClear`; every other query passes. -/
def smIDGate (x : SMIDAux W Pub Hdr Ct) (sh : CKAGameSt Unit Unit) : SMQuery W → Bool
  | .corrupt p => x.storeClear sh p
  | _ => true

omit [Fintype Rand] [Nonempty Rand] in
/-- The answer to the delivery of the header `h`, the associated data `ad` and the ciphertext
`c` to party `p` in the game state `s`, with the decryption mode `idealD` per epoch, and the
next game state. -/
def smIDDeliver (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS : ℕ)
    (idealD : ℕ → Bool) (s : SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) (p : CKAParty) (h : Hdr)
    (ad : W) (c : Ct) : Option W × (SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) :=
  match s.2.epochOf (ckaShadow s.1.ck) p (M.hdrPub h) with
  | none => (none, s)
  | some e =>
    if s.2.safe ΔFS ΔPCS p e (M.hdrPos h) then
      match M.rkey (s.1.ck.st p) h with
      | none => (none, s)
      | some y =>
        match (if idealD e then (s.2.findEntry e h ad c).map SMIDLogEntry.pt
          else M.decrypt y.2 h ad c) with
        | some m => (some m, (s.1.upd p y.1 s.1.done, s.2.mark e h ad c))
        | none => (none, s)
    else (none, s)

/-- The oracle of the game with immediate decryption over `M` with the challenge epoch `t`, the
challenge mode `idealC` and the decryption mode `idealD` per epoch: the queries of the
corruption game pass `smIDGate`, are answered by `smSchemeOracle` with the header of the sender
attached, and are logged; deliveries are answered by `smIDDeliver`. -/
noncomputable def smIDOracleAt (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS t : ℕ)
    (idealC : Bool) (idealD : ℕ → Bool) (s : SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) :
    SMIDQuery W Hdr Ct →
      PMF (SMIDAns Pub Hdr Ct Leak W × (SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct))
  | .sm q =>
    if smIDGate s.2 (ckaShadow s.1.ck) q then
      (smSchemeOracle M.toSMScheme ΔFS ΔPCS t idealC s.1 q).map fun y =>
        (.sm (y.1.withHdr (M.hdr (s.1.ck.st q.party))),
          (y.2, s.2.upd M.hdrPos (ckaShadow s.1.ck) q (y.1.withHdr (M.hdr (s.1.ck.st q.party)))))
    else PMF.pure (.sm .none, s)
  | .deliver p h ad c =>
    PMF.pure (Prod.map SMIDAns.dec id (smIDDeliver M ΔFS ΔPCS idealD s p h ad c))

/-- An adversary of the game with immediate decryption: a distribution of the challenge epoch,
and for each challenge epoch and public value of the initialisation an oracle tree. -/
structure SMIDAdv (Pub W Hdr Ct Leak : Type) : Type 1 where
  /-- The choice of the challenge epoch. -/
  tStar : PMF ℕ
  /-- The interaction with the oracles. -/
  play : ℕ → Pub → OracleAdv (SMIDQuery W Hdr Ct) (SMIDAns Pub Hdr Ct Leak W) Bool

/-- The game with immediate decryption over a scheme with the decryption mode `idealD` per
epoch: the adversary chooses the challenge epoch `t`, the scheme is initialised, and the
adversary interacts with `smIDOracleAt`. -/
noncomputable def smIDGameAt (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS : ℕ)
    (idealC : Bool) (idealD : ℕ → Bool) (A : SMIDAdv Pub W Hdr Ct Leak) : SPComp Bool :=
  SPComp.bind (liftPMF A.tStar) fun t =>
    SPComp.bind M.init fun i =>
      liftPMF ((OracleAdv.run (smIDOracleAt M ΔFS ΔPCS t idealC idealD) (A.play t i.1)
        (SMSchemeSt.init i, SMIDAux.init i.1)).map Prod.fst)

/-- **The game with immediate decryption over a scheme**: `smIDGameAt` with the same
decryption mode `idealD` in every epoch. -/
noncomputable def smIDGame (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS : ℕ)
    (idealC idealD : Bool) (A : SMIDAdv Pub W Hdr Ct Leak) : SPComp Bool :=
  smIDGameAt M ΔFS ΔPCS idealC (fun _ => idealD) A

/-- **The advantage of `A` in the game with immediate decryption over `M`**: the real game
against the game with a uniform challenge ciphertext and decryption from the log. -/
noncomputable def SMIDScheme.idAdvantage (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (ΔFS ΔPCS : ℕ) (A : SMIDAdv Pub W Hdr Ct Leak) : ℝ≥0∞ :=
  Advantage (smIDGame M ΔFS ΔPCS false false A) (smIDGame M ΔFS ΔPCS true true A)

/-- **The integrity advantage of `A` over `M`**: the real game against the game with
decryption from the log. -/
noncomputable def SMIDScheme.intAdvantage (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (ΔFS ΔPCS : ℕ) (A : SMIDAdv Pub W Hdr Ct Leak) : ℝ≥0∞ :=
  Advantage (smIDGame M ΔFS ΔPCS false false A) (smIDGame M ΔFS ΔPCS false true A)

/-- **The confidentiality advantage of `A` over `M`**: the games with decryption from the log,
with the real against the uniform challenge ciphertext. -/
noncomputable def SMIDScheme.confAdvantage (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (ΔFS ΔPCS : ℕ) (A : SMIDAdv Pub W Hdr Ct Leak) : ℝ≥0∞ :=
  Advantage (smIDGame M ΔFS ΔPCS false true A) (smIDGame M ΔFS ΔPCS true true A)

end Game

/-! ## Simulations of schemes and the transfer of the game -/

section Sim

variable {St Pub Rand W Ct Leak Hdr K St' Pub' Ct' Leak' Hdr' K' : Type} [Fintype Rand]
  [Nonempty Rand]

/-- **A simulation of schemes with headers and immediate decryption.** The underlying schemes
simulate each other (`SMScheme.Sim`) along the relation `ρ` of party states with the encodings
`encP`, `encC`, `encL`, `encI`; related states give encoded headers; the ratchet key and the
position of an encoded header are those of the header, encoded; the key lookup of an encoded
header from related states gives related states and keys related by `κ`, or fails on both
sides; and related keys decrypt encoded headers and ciphertexts as the original ones. -/
structure SMIDScheme.Sim (M' : SMIDScheme St' Pub' Rand W Ct' Leak' Hdr' K')
    (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ρ : St' → St → Prop) (κ : K' → K → Prop)
    (encP : Pub → Pub') (encC : Ct ≃ Ct') (encL : Leak → Leak') (encI : St → St')
    (encH : Hdr ≃ Hdr') : Prop
    extends SMScheme.Sim M'.toSMScheme M.toSMScheme ρ encP encC encL encI where
  /-- The headers. -/
  hdr : ∀ x' x, ρ x' x → M'.hdr x' = encH (M.hdr x)
  /-- The ratchet key of an encoded header. -/
  hdrPub : ∀ h T, M'.hdrPub (encH h) = encP T ↔ M.hdrPub h = T
  /-- The position of an encoded header. -/
  hdrPos : ∀ h, M'.hdrPos (encH h) = M.hdrPos h
  /-- The key lookup. -/
  rkey : ∀ x' x h, ρ x' x →
    Option.Rel (fun y' y => ρ y'.1 y.1 ∧ κ y'.2 y.2) (M'.rkey x' (encH h)) (M.rkey x h)
  /-- The decryption. -/
  decrypt : ∀ k' k h ad c, κ k' k → M'.decrypt k' (encH h) ad (encC c) = M.decrypt k h ad c

/-- The relation of the states of the games with immediate decryption: related game states of
the corruption game, and the encoded bookkeeping. -/
def SMIDRel (ρ : St' → St → Prop) (encP : Pub → Pub') (encH : Hdr → Hdr') (encC : Ct → Ct')
    (s' : SMSchemeSt St' Pub' × SMIDAux W Pub' Hdr' Ct')
    (s : SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) : Prop :=
  SMSchemeSt.Related ρ encP s'.1 s.1 ∧ s'.2 = s.2.map encP encH encC

/-- An adversary against `M'` as an adversary against `M`: the public value of the
initialisation and the answers are encoded before `A` reads them, and the headers and
ciphertexts of its deliveries are decoded. -/
def SMIDAdv.comap (encP : Pub → Pub') (encC : Ct ≃ Ct') (encL : Leak → Leak')
    (encH : Hdr ≃ Hdr') (A : SMIDAdv Pub' W Hdr' Ct' Leak') : SMIDAdv Pub W Hdr Ct Leak where
  tStar := A.tStar
  play t T := (A.play t (encP T)).mapQueryAnswer (SMIDQuery.map encH.symm encC.symm)
    (SMIDAns.map encP encH encC encL)

variable [DecidableEq Pub] [DecidableEq W] [DecidableEq Hdr] [DecidableEq Ct] [DecidableEq Pub']
  [DecidableEq Hdr'] [DecidableEq Ct']

omit [Fintype Rand] [Nonempty Rand] in
/-- **The deliveries of simulating schemes agree.** From related game states, the delivery of an
encoded header and ciphertext to `M'` gives the answer of the delivery to `M` and a related
state. -/
theorem smIDDeliver_sim {M' : SMIDScheme St' Pub' Rand W Ct' Leak' Hdr' K'}
    {M : SMIDScheme St Pub Rand W Ct Leak Hdr K} {ρ : St' → St → Prop} {κ : K' → K → Prop}
    {encP : Pub → Pub'} {encC : Ct ≃ Ct'} {encL : Leak → Leak'} {encI : St → St'}
    {encH : Hdr ≃ Hdr'} (h : M'.Sim M ρ κ encP encC encL encI encH) (ΔFS ΔPCS : ℕ)
    (idealD : ℕ → Bool) (s' : SMSchemeSt St' Pub' × SMIDAux W Pub' Hdr' Ct')
    (s : SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) (hs : SMIDRel ρ encP encH encC s' s)
    (p : CKAParty) (hd : Hdr) (ad : W) (c : Ct) :
    (smIDDeliver M' ΔFS ΔPCS idealD s' p (encH hd) ad (encC c)).1 =
        (smIDDeliver M ΔFS ΔPCS idealD s p hd ad c).1 ∧
      SMIDRel ρ encP encH encC (smIDDeliver M' ΔFS ΔPCS idealD s' p (encH hd) ad (encC c)).2
        (smIDDeliver M ΔFS ΔPCS idealD s p hd ad c).2 := by
  rcases s' with ⟨s1', x'⟩
  rcases s with ⟨s1, x⟩
  obtain ⟨hs1, hx⟩ := hs
  dsimp only at hs1 hx
  subst hx
  have hsh : ckaShadow s1'.ck = ckaShadow s1.ck := by simp only [ckaShadow, hs1.t]
  have hE : (x.map encP encH encC).epochOf (ckaShadow s1.ck) p (M'.hdrPub (encH hd)) =
      x.epochOf (ckaShadow s1.ck) p (M.hdrPub hd) :=
    SMIDAux.epochOf_map _ _ _ _ _ _ _ _ fun U => by rw [eq_comm, h.hdrPub, eq_comm]
  simp only [smIDDeliver, hsh, hE, h.hdrPos, SMIDAux.safe_map]
  cases x.epochOf (ckaShadow s1.ck) p (M.hdrPub hd) with
  | none => exact ⟨rfl, hs1, rfl⟩
  | some e =>
    dsimp only
    by_cases hsafe : x.safe ΔFS ΔPCS p e (M.hdrPos hd) = true
    · simp only [hsafe, ↓reduceIte]
      have hr := h.rkey _ _ hd (hs1.st p)
      cases h1 : M'.rkey (s1'.ck.st p) (encH hd) <;> cases h2 : M.rkey (s1.ck.st p) hd <;>
        rw [h1, h2] at hr <;> cases hr
      · exact ⟨rfl, hs1, rfl⟩
      · rename_i y' y hy
        have hm : (if idealD e then
              ((x.map encP encH encC).findEntry e (encH hd) ad (encC c)).map SMIDLogEntry.pt
            else M'.decrypt y'.2 (encH hd) ad (encC c)) =
            (if idealD e then (x.findEntry e hd ad c).map SMIDLogEntry.pt
            else M.decrypt y.2 hd ad c) := by
          rw [SMIDAux.findEntry_map encP encH.injective encC.injective,
            h.decrypt _ _ _ _ _ hy.2]
        dsimp only
        rw [hm]
        cases (if idealD e then (x.findEntry e hd ad c).map SMIDLogEntry.pt
            else M.decrypt y.2 hd ad c) with
        | none => exact ⟨rfl, hs1, rfl⟩
        | some m =>
          refine ⟨rfl, ?_, ?_⟩
          · dsimp only
            rw [hs1.done]
            exact hs1.upd p hy.1 _
          · exact (SMIDAux.mark_map encP encH.injective encC.injective x e hd ad c).symm
    · simp only [hsafe, Bool.false_eq_true, ↓reduceIte]
      exact ⟨trivial, hs1, rfl⟩

/-- **The oracles of simulating schemes are coupled.** From related game states, each call of
the oracle over `M'` is coupled with the call over `M` at the decoded query, along the relation
of game states, with the answers of `M` encoded. -/
theorem smID_sim_step {M' : SMIDScheme St' Pub' Rand W Ct' Leak' Hdr' K'}
    {M : SMIDScheme St Pub Rand W Ct Leak Hdr K} {ρ : St' → St → Prop} {κ : K' → K → Prop}
    {encP : Pub → Pub'} {encC : Ct ≃ Ct'} {encL : Leak → Leak'} {encI : St → St'}
    {encH : Hdr ≃ Hdr'} (h : M'.Sim M ρ κ encP encC encL encI encH) (ΔFS ΔPCS t : ℕ)
    (idealC : Bool) (idealD : ℕ → Bool) (s' : SMSchemeSt St' Pub' × SMIDAux W Pub' Hdr' Ct')
    (s : SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) (hs : SMIDRel ρ encP encH encC s' s)
    (d : SMIDQuery W Hdr' Ct') :
    ∃ ν : PMF ((SMIDAns Pub Hdr Ct Leak W × (SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct)) ×
        (SMSchemeSt St' Pub' × SMIDAux W Pub' Hdr' Ct')),
      ν.map Prod.fst =
        smIDOracleAt M ΔFS ΔPCS t idealC idealD s (d.map encH.symm encC.symm) ∧
      ν.map (fun z => (SMIDAns.map encP encH encC encL z.1.1, z.2)) =
        smIDOracleAt M' ΔFS ΔPCS t idealC idealD s' d ∧
      ∀ z ∈ ν.support, SMIDRel ρ encP encH encC z.2 z.1.2 := by
  have hsh : ckaShadow s'.1.ck = ckaShadow s.1.ck := by simp only [ckaShadow, hs.1.t]
  cases d with
  | sm q =>
    have hg : smIDGate s'.2 (ckaShadow s'.1.ck) q = smIDGate s.2 (ckaShadow s.1.ck) q := by
      rw [hsh, hs.2]; cases q <;> simp only [smIDGate, SMIDAux.storeClear_map]
    simp only [SMIDQuery.map, smIDOracleAt, hg]
    by_cases hc : smIDGate s.2 (ckaShadow s.1.ck) q = true
    · simp only [hc, ↓reduceIte]
      obtain ⟨ν, h1, h2, h3⟩ := smScheme_sim_step h.toSim ΔFS ΔPCS t idealC s'.1 s.1 hs.1 q
      have hhd : M'.hdr (s'.1.ck.st q.party) = encH (M.hdr (s.1.ck.st q.party)) :=
        h.hdr _ _ (hs.1.st _)
      refine ⟨ν.map fun z => ((SMIDAns.sm (z.1.1.withHdr (M.hdr (s.1.ck.st q.party))),
          (z.1.2, s.2.upd M.hdrPos (ckaShadow s.1.ck) q
            (z.1.1.withHdr (M.hdr (s.1.ck.st q.party))))),
          (z.2, (s.2.upd M.hdrPos (ckaShadow s.1.ck) q
            (z.1.1.withHdr (M.hdr (s.1.ck.st q.party)))).map encP encH encC)), ?_, ?_, ?_⟩
      · rw [← h1, PMF.map_comp, PMF.map_comp]; rfl
      · rw [← h2, PMF.map_comp, PMF.map_comp, hhd, hs.2, hsh]
        congr 1
        funext z
        simp only [Function.comp_apply, SMIDAns.map, SMSchemeAns.withHdr_map,
          SMIDAux.upd_map encP encH encC encL M.hdrPos M'.hdrPos h.hdrPos]
      · intro z hz
        rw [PMF.support_map] at hz
        obtain ⟨w, hw, rfl⟩ := hz
        exact ⟨h3 w hw, rfl⟩
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact coupling_pure _ _ _ _ _ hs
  | deliver p h' ad c' =>
    obtain ⟨hd, rfl⟩ : ∃ hd, h' = encH hd := ⟨encH.symm h', (encH.apply_symm_apply h').symm⟩
    obtain ⟨c, rfl⟩ : ∃ c, c' = encC c := ⟨encC.symm c', (encC.apply_symm_apply c').symm⟩
    obtain ⟨hr1, hr2⟩ := smIDDeliver_sim h ΔFS ΔPCS idealD s' s hs p hd ad c
    simp only [SMIDQuery.map, smIDOracleAt, Equiv.symm_apply_apply]
    obtain ⟨ν, h1, h2, h3⟩ := coupling_pure (SMIDAns.map encP encH encC encL)
      (SMIDRel ρ encP encH encC) (SMIDAns.dec (smIDDeliver M ΔFS ΔPCS idealD s p hd ad c).1)
      (smIDDeliver M ΔFS ΔPCS idealD s p hd ad c).2 _ hr2
    refine ⟨ν, by rw [h1]; rfl, ?_, h3⟩
    rw [h2]
    simp only [Prod.map, SMIDAns.map, hr1, id_eq]

/-- **Transfer of the game with immediate decryption along a simulation.** If `M'` simulates
`M`, the game over `M'` against `A` is the game over `M` against `A` with the deliveries
decoded and the answers encoded. -/
theorem smIDGameAt_sim {M' : SMIDScheme St' Pub' Rand W Ct' Leak' Hdr' K'}
    {M : SMIDScheme St Pub Rand W Ct Leak Hdr K} {ρ : St' → St → Prop} {κ : K' → K → Prop}
    {encP : Pub → Pub'} {encC : Ct ≃ Ct'} {encL : Leak → Leak'} {encI : St → St'}
    {encH : Hdr ≃ Hdr'} (h : M'.Sim M ρ κ encP encC encL encI encH) (ΔFS ΔPCS : ℕ)
    (idealC : Bool) (idealD : ℕ → Bool) (A : SMIDAdv Pub' W Hdr' Ct' Leak') :
    smIDGameAt M' ΔFS ΔPCS idealC idealD A =
      smIDGameAt M ΔFS ΔPCS idealC idealD (A.comap encP encC encL encH) := by
  simp only [smIDGameAt, h.init, SPComp.bind_assoc, SPComp.pure_bind, SMIDAdv.comap]
  refine congrArg _ (funext fun t => congrArg _ (funext fun i => congrArg _ ?_))
  rw [OracleAdv.run_mapQueryAnswer, OracleAdv.run_map_fst_mapQueryAnswer_of_coupling
    (fun s d => smIDOracleAt M ΔFS ΔPCS t idealC idealD s (d.map encH.symm encC.symm))
    (smIDOracleAt M' ΔFS ΔPCS t idealC idealD) (SMIDAns.map encP encH encC encL)
    (SMIDRel ρ encP encH encC)
    (fun s' s d hs => smID_sim_step h ΔFS ΔPCS t idealC idealD s' s hs d) _ _
    (SMSchemeSt.init i, SMIDAux.init i.1) ⟨SMSchemeSt.related_init h.init_rel i, rfl⟩,
    OracleAdv.run_mapQueryAnswer]
  rfl

/-- **Transfer of the game with immediate decryption along a simulation**, with the same
decryption mode in every epoch. -/
theorem smIDGame_sim {M' : SMIDScheme St' Pub' Rand W Ct' Leak' Hdr' K'}
    {M : SMIDScheme St Pub Rand W Ct Leak Hdr K} {ρ : St' → St → Prop} {κ : K' → K → Prop}
    {encP : Pub → Pub'} {encC : Ct ≃ Ct'} {encL : Leak → Leak'} {encI : St → St'}
    {encH : Hdr ≃ Hdr'} (h : M'.Sim M ρ κ encP encC encL encI encH) (ΔFS ΔPCS : ℕ)
    (idealC idealD : Bool) (A : SMIDAdv Pub' W Hdr' Ct' Leak') :
    smIDGame M' ΔFS ΔPCS idealC idealD A =
      smIDGame M ΔFS ΔPCS idealC idealD (A.comap encP encC encL encH) :=
  smIDGameAt_sim h ΔFS ΔPCS idealC _ A

/-- **The advantage transfers along a simulation.** -/
theorem SMIDScheme.Sim.idAdvantage_eq {M' : SMIDScheme St' Pub' Rand W Ct' Leak' Hdr' K'}
    {M : SMIDScheme St Pub Rand W Ct Leak Hdr K} {ρ : St' → St → Prop} {κ : K' → K → Prop}
    {encP : Pub → Pub'} {encC : Ct ≃ Ct'} {encL : Leak → Leak'} {encI : St → St'}
    {encH : Hdr ≃ Hdr'} (h : M'.Sim M ρ κ encP encC encL encI encH) (ΔFS ΔPCS : ℕ)
    (A : SMIDAdv Pub' W Hdr' Ct' Leak') :
    M'.idAdvantage ΔFS ΔPCS A = M.idAdvantage ΔFS ΔPCS (A.comap encP encC encL encH) := by
  simp only [SMIDScheme.idAdvantage, smIDGame_sim h]

/-- **The integrity advantage transfers along a simulation.** -/
theorem SMIDScheme.Sim.intAdvantage_eq {M' : SMIDScheme St' Pub' Rand W Ct' Leak' Hdr' K'}
    {M : SMIDScheme St Pub Rand W Ct Leak Hdr K} {ρ : St' → St → Prop} {κ : K' → K → Prop}
    {encP : Pub → Pub'} {encC : Ct ≃ Ct'} {encL : Leak → Leak'} {encI : St → St'}
    {encH : Hdr ≃ Hdr'} (h : M'.Sim M ρ κ encP encC encL encI encH) (ΔFS ΔPCS : ℕ)
    (A : SMIDAdv Pub' W Hdr' Ct' Leak') :
    M'.intAdvantage ΔFS ΔPCS A = M.intAdvantage ΔFS ΔPCS (A.comap encP encC encL encH) := by
  simp only [SMIDScheme.intAdvantage, smIDGame_sim h]

/-- **The confidentiality advantage transfers along a simulation.** -/
theorem SMIDScheme.Sim.confAdvantage_eq {M' : SMIDScheme St' Pub' Rand W Ct' Leak' Hdr' K'}
    {M : SMIDScheme St Pub Rand W Ct Leak Hdr K} {ρ : St' → St → Prop} {κ : K' → K → Prop}
    {encP : Pub → Pub'} {encC : Ct ≃ Ct'} {encL : Leak → Leak'} {encI : St → St'}
    {encH : Hdr ≃ Hdr'} (h : M'.Sim M ρ κ encP encC encL encI encH) (ΔFS ΔPCS : ℕ)
    (A : SMIDAdv Pub' W Hdr' Ct' Leak') :
    M'.confAdvantage ΔFS ΔPCS A = M.confAdvantage ΔFS ΔPCS (A.comap encP encC encL encH) := by
  simp only [SMIDScheme.confAdvantage, smIDGame_sim h]

end Sim

end CatCrypt.Crypto.Messaging
