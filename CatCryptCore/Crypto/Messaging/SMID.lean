/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SMScheme
public import CatCryptCore.Crypto.Messaging.SMAuth
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

## The reduction to the corruption game of a base scheme

`SMIDScheme.Over M M₀ π ι V Inv` states that `M` is the base scheme `M₀ : SMScheme` with public
bookkeeping: the projection `π` of party states maps the algorithms of `M` to those of `M₀`
(the message of the base scheme is `V.msg` of the message and the header), the key lookup keeps
the projection, and on the states of an invariant `Inv` of the game with decryption from the
log the header, the success of the key lookup at a matching log entry and, under the restricted
gate, the corruption answer are computed by `V : SMIDView` from the bookkeeping and the epoch
counters. The reduction `smIDRed M V ΔFS ΔPCS A` keeps the log, the public values of the opened
epochs and the recorded positions, forwards the queries of the corruption game to the game over
`M₀`, completes their answers by `V`, and answers deliveries from the log. Its corruption game
is the game with decryption from the log (`smIDGame_logDec_eq`), so
(`SMIDScheme.idAdvantage_le`)

  `Adv_id(A) ≤ Adv_int(A) + Adv_corrupt,M₀(smIDRed A)`.

## The hybrid over the epochs and the forgery event

The hybrid `k` answers the deliveries whose header names an epoch below `k` from the log; for an
adversary asking at most `N` queries (`SMIDScheme.intAdvantage_le_sum`)

  `Adv_int(A) ≤ ∑_{k < N} Adv_int,k(A)`.

A forgery at the epoch `k` (`smIDBadAt`) is a safe delivery into the epoch `k` with a successful
key lookup whose real decryption differs from the plaintext of an undelivered matching entry,
so in particular an accepted delivery that matches no undelivered entry; then
(`SMIDScheme.epochIntAdvantage_le_bad`) `Adv_int,k(A) ≤ Pr[smIDBadGame k A]`, and the game
truncated at the first answered corruption with the epoch `k` in its window has the same output
(`smIDTruncGame_eq`).

## Main definitions

* `SMIDScheme`, `SMIDQuery`, `SMIDAns`, `SMIDLogEntry`, `SMIDAux`, `smIDGate`, `smIDDeliver`,
  `smIDOracleAt`, `SMIDAdv`, `smIDGameAt`, `smIDGame`
* `SMIDScheme.idAdvantage`, `SMIDScheme.intAdvantage`, `SMIDScheme.confAdvantage`
* `SMIDScheme.Sim`, `SMIDRel`, `SMIDAdv.comap`
* `SMIDView`, `SMIDScheme.Over`, `smIDLogDeliver`, `smIDImpl`, `smIDRed` — the reduction to the
  corruption game of a base scheme
* `SMIDScheme.epochIntAdvantage`, `smIDBadAt`, `smIDFlagOracle`, `smIDBadGame`,
  `smIDTruncOracle`, `smIDTruncGame` — the hybrid and the forgery event

## Main results

* `smIDDeliver_sim`, `smID_sim_step` — the delivery and the oracle calls of simulating schemes
* `smIDGameAt_sim`, `smIDGame_sim` — the transfer of the game along a simulation
* `SMIDScheme.Sim.idAdvantage_eq`, `SMIDScheme.Sim.intAdvantage_eq`,
  `SMIDScheme.Sim.confAdvantage_eq` — the transfer of the advantages
* `smIDGame_logDec_eq`, `SMIDScheme.idAdvantage_le` — the reduction to the base scheme
* `SMIDScheme.intAdvantage_le_sum`, `SMIDScheme.epochIntAdvantage_le_bad`, `smIDTruncGame_eq`
  — the bounds above

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

/-! ## The reduction to the corruption game of a base scheme -/

section Red

variable {St St₀ Pub Rand W W₀ Ct Leak Leak₀ Hdr K : Type}

/-- The query with the message of a send or a challenge mapped by `f`. -/
def SMQuery.mapMsg (f : W × W → W₀ × W₀) : SMQuery W → SMQuery W₀
  | .ratchet p => .ratchet p
  | .recv p => .recv p
  | .send p m => .send p (f m)
  | .chall p m => .chall p (f m)
  | .corrupt p => .corrupt p

/-- The party of a query with mapped messages is the party of the query. -/
@[simp] theorem SMQuery.party_mapMsg (f : W × W → W₀ × W₀) (q : SMQuery W) :
    (q.mapMsg f).party = q.party := by
  cases q <;> rfl

/-- **The public part of a scheme with headers over a base scheme**, computed from the
bookkeeping and the epoch counters of the game: the header of the next ciphertext of a party,
whether the key lookup of a header by a party succeeds, the corruption answer of a party from
the corruption answer of the base scheme, and the message of the base scheme for a message and
its header. -/
structure SMIDView (W Pub Hdr Ct Leak W₀ Leak₀ : Type) where
  /-- The header of the next ciphertext of a party. -/
  hdr : SMIDAux W Pub Hdr Ct → CKAGameSt Unit Unit → CKAParty → Hdr
  /-- Whether the key lookup of a header by a party succeeds. -/
  rkeyOk : SMIDAux W Pub Hdr Ct → CKAGameSt Unit Unit → CKAParty → Hdr → Bool
  /-- The corruption answer of a party from the corruption answer of the base scheme. -/
  leak : SMIDAux W Pub Hdr Ct → CKAGameSt Unit Unit → CKAParty → Leak₀ → Leak
  /-- The message of the base scheme for a message with a header. -/
  msg : Hdr → W × W → W₀ × W₀

variable [DecidableEq Pub] [DecidableEq W] [DecidableEq Hdr] [DecidableEq Ct]

/-- The answer of the reduction to the delivery of the header `h`, the associated data `ad` and
the ciphertext `c` to party `p`, from the epoch counters and the bookkeeping `σ`: the plaintext
of an undelivered matching log entry when the delivery is safe and the key lookup succeeds, with
the matching entries marked delivered; a rejection otherwise. -/
def smIDLogDeliver (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (V : SMIDView W Pub Hdr Ct Leak W₀ Leak₀) (ΔFS ΔPCS : ℕ)
    (σ : CKAGameSt Unit Unit × SMIDAux W Pub Hdr Ct) (p : CKAParty) (h : Hdr) (ad : W) (c : Ct) :
    Option W × (CKAGameSt Unit Unit × SMIDAux W Pub Hdr Ct) :=
  match σ.2.epochOf σ.1 p (M.hdrPub h) with
  | none => (none, σ)
  | some e =>
    if σ.2.safe ΔFS ΔPCS p e (M.hdrPos h) && V.rkeyOk σ.2 σ.1 p h then
      match σ.2.findEntry e h ad c with
      | some l => (some l.pt, (σ.1, σ.2.mark e h ad c))
      | none => (none, σ)
    else (none, σ)

/-- The simulator of the reduction to the corruption game of a base scheme. Its state is the
epoch counters and the bookkeeping of the game with immediate decryption: a query of the
corruption game that passes `smIDGate` is forwarded with the message of the base scheme, its
answer is completed by the header and the corruption answer of `V`, and it is logged; a
delivery is answered from the log by `smIDLogDeliver`. -/
def smIDImpl (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (V : SMIDView W Pub Hdr Ct Leak W₀ Leak₀) (ΔFS ΔPCS : ℕ)
    (σ : CKAGameSt Unit Unit × SMIDAux W Pub Hdr Ct) :
    SMIDQuery W Hdr Ct → OracleAdv (SMQuery W₀) (SMSchemeAns Pub Ct Leak₀)
      (SMIDAns Pub Hdr Ct Leak W × (CKAGameSt Unit Unit × SMIDAux W Pub Hdr Ct))
  | .sm q =>
    if smIDGate σ.2 σ.1 q then
      .query (q.mapMsg (V.msg (V.hdr σ.2 σ.1 q.party))) fun a =>
        .ret (.sm ((a.map id id (V.leak σ.2 σ.1 q.party)).withHdr (V.hdr σ.2 σ.1 q.party)),
          (ckaShadowStep σ.1 q, σ.2.upd M.hdrPos σ.1 q
            ((a.map id id (V.leak σ.2 σ.1 q.party)).withHdr (V.hdr σ.2 σ.1 q.party))))
    else .ret (.sm .none, σ)
  | .deliver p h ad c => .ret (Prod.map SMIDAns.dec id (smIDLogDeliver M V ΔFS ΔPCS σ p h ad c))

/-- **The reduction to the corruption game of a base scheme**: the adversary of
`smCorruptGame` that keeps the challenge epoch of `A` and runs `A` against the simulator
`smIDImpl`. -/
def smIDRed (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (V : SMIDView W Pub Hdr Ct Leak W₀ Leak₀)
    (ΔFS ΔPCS : ℕ) (A : SMIDAdv Pub W Hdr Ct Leak) : SMSchemeAdv Pub W₀ Ct Leak₀ where
  tStar := A.tStar
  play t pub := (OracleAdv.simulate (smIDImpl M V ΔFS ΔPCS) (A.play t pub)
    (CKAGameSt.init () () (), SMIDAux.init pub)).bind fun r => .ret r.1

/-- The state of the simulator and of the corruption game of the base scheme that a state of the
game with immediate decryption corresponds to, with the party states projected by `π`. -/
def smIDEmb (π : St → St₀) (s : SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) :
    (CKAGameSt Unit Unit × SMIDAux W Pub Hdr Ct) × SMSchemeSt St₀ Pub :=
  ((ckaShadow s.1.ck, s.2), ⟨⟨fun p => π (s.1.ck.st p), s.1.ck.t, s.1.ck.msg⟩, s.1.done⟩)

variable [Fintype Rand] [Nonempty Rand]

/-- **A scheme with headers over a base scheme.** The projection `π` of party states maps the
algorithms of `M` to those of `M₀`, with the message of the base scheme given by `V.msg` at the
header of the sender; the initial states of `M` are the embeddings `ι` of the initial states of
`M₀`; the key lookup keeps the projection. On the states of the invariant `Inv`, which holds
initially and which every call of the oracle with decryption from the log keeps, the header,
the success of the key lookup at a matching log entry and, when `SMIDAux.storeClear` allows the
corruption, the corruption answer are those that `V` computes from the bookkeeping. -/
structure SMIDScheme.Over (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (M₀ : SMScheme St₀ Pub Rand W₀ Ct Leak₀) (π : St → St₀) (ι : St₀ → St)
    (V : SMIDView W Pub Hdr Ct Leak W₀ Leak₀)
    (Inv : SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct → Prop) : Prop where
  /-- The initialisation. -/
  init : M.init = SPComp.bind M₀.init fun i => SPComp.pure (i.1, ι i.2.1, ι i.2.2)
  /-- The projection of the embedding. -/
  proj_emb : ∀ x, π (ι x) = x
  /-- Opening an epoch. -/
  ratchet : ∀ x r, Prod.map π id (M.ratchet x r) = M₀.ratchet (π x) r
  /-- Receiving. -/
  recv : ∀ x T, π (M.recv x T) = M₀.recv (π x) T
  /-- Sending. -/
  send : ∀ x m, (M.send x m).map (Prod.map π id) = M₀.send (π x) (V.msg (M.hdr x) m)
  /-- The ideal ciphertexts. -/
  idealCt : M.idealCt = M₀.idealCt
  /-- The key lookup keeps the projection. -/
  rkey : ∀ x h y, M.rkey x h = some y → π y.1 = π x
  /-- The invariant holds initially. -/
  inv_init : ∀ i : Pub × St₀ × St₀,
    Inv (SMSchemeSt.init (i.1, ι i.2.1, ι i.2.2), SMIDAux.init i.1)
  /-- The oracle with decryption from the log keeps the invariant. -/
  inv_step : ∀ ΔFS ΔPCS t idealC s d, Inv s →
    ∀ z ∈ (smIDOracleAt M ΔFS ΔPCS t idealC (fun _ => true) s d).support, Inv z.2
  /-- The headers. -/
  hdr_eq : ∀ s p, Inv s → M.hdr (s.1.ck.st p) = V.hdr s.2 (ckaShadow s.1.ck) p
  /-- The success of the key lookup at a matching log entry. -/
  rkeyOk_eq : ∀ s p h e ad c, Inv s → s.2.epochOf (ckaShadow s.1.ck) p (M.hdrPub h) = some e →
    (s.2.findEntry e h ad c).isSome →
      (M.rkey (s.1.ck.st p) h).isSome = V.rkeyOk s.2 (ckaShadow s.1.ck) p h
  /-- The corruption answers under the restricted gate. -/
  expose : ∀ s p, Inv s → s.2.storeClear (ckaShadow s.1.ck) p = true →
    M.expose (s.1.ck.st p) = V.leak s.2 (ckaShadow s.1.ck) p (M₀.expose (π (s.1.ck.st p)))

omit [DecidableEq Pub] [DecidableEq W] [DecidableEq Hdr] [DecidableEq Ct] in
/-- **The oracle of the corruption game along a projection.** If the projection `π` maps the
algorithms of `M` to those of `M₀`, with the message of the base scheme given by `msg` at the
header of the sender, and the corruption answer of the query is `L` of the base answer, the
call of the oracle over `M` with the party states projected is the call over `M₀` at the
projected state with the answer mapped by `L`. -/
theorem smSchemeOracle_proj (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (M₀ : SMScheme St₀ Pub Rand W₀ Ct Leak₀) (π : St → St₀) (msg : Hdr → W × W → W₀ × W₀)
    (hrat : ∀ x r, Prod.map π id (M.ratchet x r) = M₀.ratchet (π x) r)
    (hrecv : ∀ x T, π (M.recv x T) = M₀.recv (π x) T)
    (hsend : ∀ x m, (M.send x m).map (Prod.map π id) = M₀.send (π x) (msg (M.hdr x) m))
    (hideal : M.idealCt = M₀.idealCt) (ΔFS ΔPCS t : ℕ) (ideal : Bool) (s : SMSchemeSt St Pub)
    (q : SMQuery W) (L : Leak₀ → Leak)
    (hexp : ∀ p, q = .corrupt p → M.expose (s.ck.st p) = L (M₀.expose (π (s.ck.st p)))) :
    (smSchemeOracle M.toSMScheme ΔFS ΔPCS t ideal s q).map
        (fun y => (y.1, (⟨⟨fun p => π (y.2.ck.st p), y.2.ck.t, y.2.ck.msg⟩, y.2.done⟩ :
          SMSchemeSt St₀ Pub))) =
      (smSchemeOracle M₀ ΔFS ΔPCS t ideal ⟨⟨fun p => π (s.ck.st p), s.ck.t, s.ck.msg⟩, s.done⟩
        (q.mapMsg (msg (M.hdr (s.ck.st q.party))))).map fun y => (y.1.map id id L, y.2) := by
  have hupd : ∀ (f : CKAParty → St) (p : CKAParty) (x : St),
      (fun q => π (Function.update f p x q)) = Function.update (fun q => π (f q)) p (π x) := by
    intro f p x
    funext q
    by_cases hq : q = p
    · subst hq; simp
    · simp [Function.update_of_ne hq]
  cases q with
  | ratchet p =>
    have hc : (⟨fun p => π (s.ck.st p), s.ck.t, s.ck.msg⟩ : CKAGameSt St₀ Pub).canSend p =
        s.ck.canSend p := rfl
    simp only [smSchemeOracle, SMQuery.mapMsg, hc]
    split
    · simp only [PMF.map_bind, PMF.pure_map]
      refine congrArg _ (funext fun r => ?_)
      rw [← hrat]
      simp [SMSchemeAns.map, CKAGameSt.sent, hupd]
    · simp [PMF.pure_map, SMSchemeAns.map]
  | recv p =>
    have hc : (⟨fun p => π (s.ck.st p), s.ck.t, s.ck.msg⟩ : CKAGameSt St₀ Pub).canRecv p =
        s.ck.canRecv p := rfl
    simp only [smSchemeOracle, SMQuery.mapMsg, hc]
    split
    · simp [PMF.pure_map, SMSchemeAns.map, CKAGameSt.recvd, hupd, hrecv]
    · simp [PMF.pure_map, SMSchemeAns.map]
  | send p m =>
    simp only [smSchemeOracle, SMQuery.mapMsg, SMQuery.party]
    split_ifs with hc
    · rw [← hsend]
      cases M.send (s.ck.st p) m <;> simp [PMF.pure_map, SMSchemeAns.map, SMSchemeSt.upd, hupd]
    · simp [PMF.pure_map, SMSchemeAns.map]
  | chall p m =>
    simp only [smSchemeOracle, SMQuery.mapMsg, SMQuery.party]
    by_cases hc : (!s.done && ckaSender (s.ck.t p) == p && s.ck.t p == t) = true
    · rw [ite_eq_left hc, ite_eq_left (show _ from hc), ← hsend, ← hideal]
      cases M.send (s.ck.st p) m <;> cases ideal <;>
        simp [PMF.pure_map, PMF.map_bind, SMSchemeAns.map, SMSchemeSt.upd, hupd]
    · rw [ite_eq_right hc, ite_eq_right (show ¬ _ from hc)]
      simp [PMF.pure_map, SMSchemeAns.map]
  | corrupt p =>
    have hc : ckaAllowCorr ΔFS ΔPCS t
        (⟨fun p => π (s.ck.st p), s.ck.t, s.ck.msg⟩ : CKAGameSt St₀ Pub) p =
        ckaAllowCorr ΔFS ΔPCS t s.ck p := rfl
    simp only [smSchemeOracle, SMQuery.mapMsg, PMF.pure_map, hc]
    cases ckaAllowCorr ΔFS ΔPCS t s.ck p <;> simp [SMSchemeAns.map, hexp p rfl]

/-- **The delivery from the log is the delivery of the reduction.** On a state of the
invariant, the delivery with decryption from the log, mapped to the states of the reduction and
of the base game, is the delivery of `smIDLogDeliver`, which keeps the base state. -/
theorem smIDDeliver_emb {M : SMIDScheme St Pub Rand W Ct Leak Hdr K}
    {M₀ : SMScheme St₀ Pub Rand W₀ Ct Leak₀} {π : St → St₀} {ι : St₀ → St}
    {V : SMIDView W Pub Hdr Ct Leak W₀ Leak₀}
    {Inv : SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct → Prop} (hM : M.Over M₀ π ι V Inv)
    (ΔFS ΔPCS : ℕ) (s : SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) (hs : Inv s) (p : CKAParty)
    (h : Hdr) (ad : W) (c : Ct) :
    Prod.map id (smIDEmb π) (smIDDeliver M ΔFS ΔPCS (fun _ => true) s p h ad c) =
      ((smIDLogDeliver M V ΔFS ΔPCS (ckaShadow s.1.ck, s.2) p h ad c).1,
        ((smIDLogDeliver M V ΔFS ΔPCS (ckaShadow s.1.ck, s.2) p h ad c).2,
          (smIDEmb π s).2)) := by
  rcases s with ⟨s1, x⟩
  dsimp only at hs ⊢
  simp only [smIDDeliver, smIDLogDeliver]
  cases he : x.epochOf (ckaShadow s1.ck) p (M.hdrPub h) with
  | none => rfl
  | some e =>
    dsimp only
    by_cases hsafe : x.safe ΔFS ΔPCS p e (M.hdrPos h) = true
    · cases hf : x.findEntry e h ad c with
      | none =>
        simp only [hsafe, ite_true, Option.map_none]
        cases M.rkey (s1.ck.st p) h <;> simp [smIDEmb]
      | some l =>
        have hk := hM.rkeyOk_eq (s1, x) p h e ad c hs he (by simp [hf])
        dsimp only at hk
        cases hr : M.rkey (s1.ck.st p) h with
        | none =>
          rw [hr] at hk
          have hk' : V.rkeyOk x (ckaShadow s1.ck) p h = false := by simpa using hk.symm
          simp [hsafe, hk', smIDEmb]
        | some y =>
          rw [hr] at hk
          have hk' : V.rkeyOk x (ckaShadow s1.ck) p h = true := by simpa using hk.symm
          have hy := hM.rkey _ _ _ hr
          have hproj : (fun q => π (Function.update s1.ck.st p y.1 q)) =
              fun q => π (s1.ck.st q) := by
            funext q
            by_cases hq : q = p
            · subst hq; simp [hy]
            · simp [Function.update_of_ne hq]
          simp only [hsafe, hk', Bool.and_true, ite_true, Option.map_some, smIDEmb,
            SMSchemeSt.upd, hproj, Prod.map]
          rfl
    · simp [hsafe, smIDEmb]

/-- **The simulator is the oracle with decryption from the log.** On a state of the invariant,
each call of the oracle of the game with decryption from the log, mapped to the states of the
reduction and of the base game, is the call of `smIDImpl` against the oracle of the corruption
game over the base scheme. -/
theorem smID_step {M : SMIDScheme St Pub Rand W Ct Leak Hdr K}
    {M₀ : SMScheme St₀ Pub Rand W₀ Ct Leak₀} {π : St → St₀} {ι : St₀ → St}
    {V : SMIDView W Pub Hdr Ct Leak W₀ Leak₀}
    {Inv : SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct → Prop} (hM : M.Over M₀ π ι V Inv)
    (ΔFS ΔPCS t : ℕ) (idealC : Bool) (s : SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) (hs : Inv s)
    (d : SMIDQuery W Hdr Ct) :
    (smIDOracleAt M ΔFS ΔPCS t idealC (fun _ => true) s d).map (Prod.map id (smIDEmb π)) =
      OracleAdv.simOracle (smIDImpl M V ΔFS ΔPCS) (smSchemeOracle M₀ ΔFS ΔPCS t idealC)
        (smIDEmb π s) d := by
  cases d with
  | sm q =>
    by_cases hg : smIDGate s.2 (ckaShadow s.1.ck) q = true
    · have hL := smSchemeOracle_proj M M₀ π V.msg hM.ratchet hM.recv hM.send hM.idealCt ΔFS ΔPCS
        t idealC s.1 q (V.leak s.2 (ckaShadow s.1.ck) q.party)
        (fun p hq => by subst hq; exact hM.expose s p hs hg)
      have hH := hM.hdr_eq s q.party hs
      simp only [smIDOracleAt, hg, ite_true, OracleAdv.simOracle, smIDEmb, smIDImpl,
        OracleAdv.run_query, OracleAdv.run_ret, ← hH]
      let G : SMSchemeAns Pub Ct Leak × SMSchemeSt St₀ Pub → SMIDAns Pub Hdr Ct Leak W ×
          ((CKAGameSt Unit Unit × SMIDAux W Pub Hdr Ct) × SMSchemeSt St₀ Pub) :=
        fun z => (.sm (z.1.withHdr (M.hdr (s.1.ck.st q.party))),
          ((ckaShadowStep (ckaShadow s.1.ck) q, s.2.upd M.hdrPos (ckaShadow s.1.ck) q
            (z.1.withHdr (M.hdr (s.1.ck.st q.party)))), z.2))
      refine (?_ : _ = ((smSchemeOracle M.toSMScheme ΔFS ΔPCS t idealC s.1 q).map
          (fun y => (y.1, (⟨⟨fun p => π (y.2.ck.st p), y.2.ck.t, y.2.ck.msg⟩, y.2.done⟩ :
            SMSchemeSt St₀ Pub)))).map G).trans ?_
      · rw [PMF.map_comp, PMF.map_comp, ← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
        refine PMF.bind_congr_support _ _ _ fun y hy => ?_
        have hsh := smSchemeOracle_shadow M.toSMScheme ΔFS ΔPCS t idealC s.1 q y hy
        simp only [Function.comp_apply, Prod.map, id_eq, smIDEmb, G, hsh]
      · rw [hL, PMF.map_comp, PMF.map_bind, ← PMF.bind_pure_comp]
        simp only [PMF.pure_map]
        rfl
    · simp [smIDOracleAt, hg, OracleAdv.simOracle, smIDEmb, smIDImpl, PMF.pure_map]
  | deliver p h ad c =>
    simp only [smIDOracleAt, OracleAdv.simOracle, smIDImpl, OracleAdv.run_ret, PMF.pure_map]
    congr 1
    have := smIDDeliver_emb hM ΔFS ΔPCS s hs p h ad c
    simp only [Prod.map, smIDEmb] at this ⊢
    grind

/-- **The game with decryption from the log is the corruption game of the reduction.** Over a
scheme `M` over the base scheme `M₀`, the game with immediate decryption and decryption from the
log is the corruption game over `M₀` of the reduction `smIDRed M V ΔFS ΔPCS A`. -/
theorem smIDGame_logDec_eq {M : SMIDScheme St Pub Rand W Ct Leak Hdr K}
    {M₀ : SMScheme St₀ Pub Rand W₀ Ct Leak₀} {π : St → St₀} {ι : St₀ → St}
    {V : SMIDView W Pub Hdr Ct Leak W₀ Leak₀}
    {Inv : SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct → Prop} (hM : M.Over M₀ π ι V Inv)
    (ΔFS ΔPCS : ℕ) (idealC : Bool) (A : SMIDAdv Pub W Hdr Ct Leak) :
    smIDGame M ΔFS ΔPCS idealC true A =
      smCorruptGame M₀ ΔFS ΔPCS idealC (smIDRed M V ΔFS ΔPCS A) := by
  simp only [smIDGame, smIDGameAt, smCorruptGame, hM.init, SPComp.bind_assoc, SPComp.pure_bind]
  refine congrArg _ (funext fun t => congrArg _ (funext fun i => congrArg _ ?_))
  simp only [smIDRed]
  rw [OracleAdv.run_simulate_fst]
  have he : smIDEmb π ((SMSchemeSt.init (i.1, ι i.2.1, ι i.2.2) : SMSchemeSt St Pub),
      (SMIDAux.init i.1 : SMIDAux W Pub Hdr Ct)) =
      ((CKAGameSt.init () () (), SMIDAux.init i.1), SMSchemeSt.init i) := by
    simp only [smIDEmb, SMSchemeSt.init, ckaShadow_init, Prod.mk.injEq, true_and]
    simp only [CKAGameSt.init, SMSchemeSt.mk.injEq, CKAGameSt.mk.injEq, and_true]
    funext p
    cases p <;> simp [hM.proj_emb]
  rw [← he]
  exact OracleAdv.run_map_fst_of_map_state_inv _ _ (smIDEmb π) Inv
    (fun s d hs => hM.inv_step ΔFS ΔPCS t idealC s d hs)
    (fun s d hs => smID_step hM ΔFS ΔPCS t idealC s hs d) _ _ (hM.inv_init i)

/-- **Immediate decryption from integrity and the corruption game of the base scheme.** For a
scheme `M` over the base scheme `M₀` and every adversary `A`, the advantage of `A` in the game
with immediate decryption over `M` is at most its integrity advantage plus the corruption
advantage over `M₀` of the reduction `smIDRed M V ΔFS ΔPCS A`. -/
theorem SMIDScheme.idAdvantage_le {M : SMIDScheme St Pub Rand W Ct Leak Hdr K}
    {M₀ : SMScheme St₀ Pub Rand W₀ Ct Leak₀} {π : St → St₀} {ι : St₀ → St}
    {V : SMIDView W Pub Hdr Ct Leak W₀ Leak₀}
    {Inv : SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct → Prop} (hM : M.Over M₀ π ι V Inv)
    (ΔFS ΔPCS : ℕ) (A : SMIDAdv Pub W Hdr Ct Leak) :
    M.idAdvantage ΔFS ΔPCS A ≤
      M.intAdvantage ΔFS ΔPCS A + M₀.corruptAdvantage ΔFS ΔPCS (smIDRed M V ΔFS ΔPCS A) := by
  unfold SMIDScheme.idAdvantage SMIDScheme.intAdvantage SMScheme.corruptAdvantage
  rw [← smIDGame_logDec_eq hM, ← smIDGame_logDec_eq hM]
  exact advantage_triangle _ _ _

end Red

/-! ## The hybrid over the epochs -/

section Hybrid

variable {St Pub Rand W Ct Leak Hdr K : Type} [Fintype Rand] [Nonempty Rand] [DecidableEq Pub]
  [DecidableEq W] [DecidableEq Hdr] [DecidableEq Ct]

/-- The epoch counters of the state `s` of the game with immediate decryption are at most
`c`. -/
def smIDLevel (c : ℕ) (s : SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) : Prop :=
  ∀ p, s.1.ck.t p ≤ c

omit [DecidableEq W] [DecidableEq Hdr] [DecidableEq Ct] in
/-- The epoch of a public value among the epochs a party has received is at most its epoch
counter. -/
theorem SMIDAux.epochOf_le (x : SMIDAux W Pub Hdr Ct) (sh : CKAGameSt Unit Unit)
    (p : CKAParty) (T : Pub) (e : ℕ) (h : x.epochOf sh p T = some e) : e ≤ sh.t p := by
  simp only [SMIDAux.epochOf, Option.map_eq_some_iff] at h
  obtain ⟨q, hq, rfl⟩ := h
  have := List.find?_some hq
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1.2

omit [Fintype Rand] [Nonempty Rand] in
/-- A delivery keeps the epoch counters. -/
theorem smIDDeliver_t (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS : ℕ)
    (idealD : ℕ → Bool) (s : SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) (p : CKAParty) (h : Hdr)
    (ad : W) (c : Ct) : (smIDDeliver M ΔFS ΔPCS idealD s p h ad c).2.1.ck.t = s.1.ck.t := by
  unfold smIDDeliver
  repeat' split
  all_goals rfl

omit [Fintype Rand] [Nonempty Rand] in
/-- Two decryption modes that agree at the epoch of the header give the same delivery. -/
theorem smIDDeliver_congr (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS : ℕ)
    {idealD idealD' : ℕ → Bool} (s : SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) (p : CKAParty)
    (h : Hdr) (ad : W) (c : Ct)
    (hD : ∀ e, s.2.epochOf (ckaShadow s.1.ck) p (M.hdrPub h) = some e → idealD e = idealD' e) :
    smIDDeliver M ΔFS ΔPCS idealD s p h ad c = smIDDeliver M ΔFS ΔPCS idealD' s p h ad c := by
  unfold smIDDeliver
  cases he : s.2.epochOf (ckaShadow s.1.ck) p (M.hdrPub h) with
  | none => rfl
  | some e => simp only [hD e he]

/-- A call of the oracle of the game with immediate decryption raises each epoch counter by at
most one. -/
theorem smIDOracleAt_level (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS t : ℕ)
    (idealC : Bool) (idealD : ℕ → Bool) (c : ℕ) (s : SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct)
    (d : SMIDQuery W Hdr Ct) (hs : smIDLevel c s) :
    ∀ x ∈ (smIDOracleAt M ΔFS ΔPCS t idealC idealD s d).support, smIDLevel (c + 1) x.2 := by
  intro x hx p
  cases d with
  | sm q =>
    simp only [smIDOracleAt] at hx
    split at hx
    · simp only [PMF.support_map, Set.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have h := congrArg (fun z => z.t p)
        (smSchemeOracle_shadow M.toSMScheme ΔFS ΔPCS t idealC s.1 q y hy)
      have h' := ckaShadowStep_t_le (ckaShadow s.1.ck) q p
      have h'' := hs p
      simp only [ckaShadow] at h h'
      grind
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
      subst hx
      exact (hs p).trans (Nat.le_succ _)
  | deliver p' h ad c' =>
    simp only [smIDOracleAt, PMF.support_pure, Set.mem_singleton_iff] at hx
    subst hx
    have := smIDDeliver_t M ΔFS ΔPCS idealD s p' h ad c'
    simp only [Prod.map, id_eq, this]
    exact (hs p).trans (Nat.le_succ _)

/-- **Decryption modes that agree below the horizon.** For an adversary asking at most `N`
queries, every delivery is into an epoch below `N`, so two decryption modes that agree on the
epochs below `N` give the same game. -/
theorem smIDGameAt_congr_of_isQueryBound (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (ΔFS ΔPCS : ℕ) (idealC : Bool) {idealD idealD' : ℕ → Bool} {N : ℕ}
    (h : ∀ e < N, idealD e = idealD' e) (A : SMIDAdv Pub W Hdr Ct Leak)
    (hA : ∀ t pub, (A.play t pub).IsQueryBound N) :
    smIDGameAt M ΔFS ΔPCS idealC idealD A = smIDGameAt M ΔFS ΔPCS idealC idealD' A := by
  unfold smIDGameAt
  refine congrArg _ (funext fun t => congrArg _ (funext fun i => congrArg _ ?_))
  rw [OracleAdv.run_eq_of_agree_level _ (smIDOracleAt M ΔFS ΔPCS t idealC idealD')
    smIDLevel N (smIDOracleAt_level M ΔFS ΔPCS t idealC idealD) ?_ (hA t i.1) 0 _ ?_
    (by omega)]
  · intro c s d hc hs
    cases d with
    | sm q => rfl
    | deliver p h' ad c' =>
      simp only [smIDOracleAt]
      rw [smIDDeliver_congr M ΔFS ΔPCS s p h' ad c' fun e he => h e (by
        have h1 := SMIDAux.epochOf_le _ _ _ _ _ he
        have h2 := hs p
        simp only [ckaShadow_t] at h1
        omega)]
  · intro p
    simp [SMSchemeSt.init, CKAGameSt.init]

/-- **The integrity advantage at the epoch `k`**: the game with decryption from the log in the
epochs below `k` and real decryption from the epoch `k` on, against the game with decryption
from the log in the epochs up to `k`. The epoch of a delivery is the epoch of its header. -/
noncomputable def SMIDScheme.epochIntAdvantage (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (ΔFS ΔPCS k : ℕ) (A : SMIDAdv Pub W Hdr Ct Leak) : ℝ≥0∞ :=
  Advantage (smIDGameAt M ΔFS ΔPCS false (fun e => decide (e < k)) A)
    (smIDGameAt M ΔFS ΔPCS false (fun e => decide (e < k + 1)) A)

/-- **Integrity as a sum over the epochs.** For an adversary asking at most `N` queries, the
integrity advantage is at most the sum over the epochs `k < N` of the integrity advantages at
the epoch `k`. -/
theorem SMIDScheme.intAdvantage_le_sum (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (ΔFS ΔPCS N : ℕ) (A : SMIDAdv Pub W Hdr Ct Leak)
    (hA : ∀ t pub, (A.play t pub).IsQueryBound N) :
    M.intAdvantage ΔFS ΔPCS A ≤
      ∑ k ∈ Finset.range N, M.epochIntAdvantage ΔFS ΔPCS k A := by
  have h0 : smIDGame M ΔFS ΔPCS false false A =
      smIDGameAt M ΔFS ΔPCS false (fun e => decide (e < 0)) A := by
    simp only [smIDGame, Nat.not_lt_zero, decide_false]
  have hN : smIDGame M ΔFS ΔPCS false true A =
      smIDGameAt M ΔFS ΔPCS false (fun e => decide (e < N)) A :=
    smIDGameAt_congr_of_isQueryBound M ΔFS ΔPCS false (fun e he => by simp [he]) A hA
  unfold SMIDScheme.intAdvantage SMIDScheme.epochIntAdvantage
  rw [h0, hN]
  exact HybridArgument.advantage_hybrid_dep_bool
    (fun k => smIDGameAt M ΔFS ΔPCS false (fun e => decide (e < k)) A) N

end Hybrid

/-! ## Identical until a forgery at the epoch `k` -/

section UntilBad

variable {St Pub Rand W Ct Leak Hdr K : Type} [Fintype Rand] [Nonempty Rand] [DecidableEq Pub]
  [DecidableEq W] [DecidableEq Hdr] [DecidableEq Ct]

omit [Fintype Rand] [Nonempty Rand] in
/-- **A forgery at the epoch `k`**: the query `d` from the state `s` is a delivery whose header
names the epoch `k`, which is safe, whose key lookup succeeds, and whose real decryption differs
from the plaintext of an undelivered matching log entry; in particular an accepted delivery
into the epoch `k` that matches no undelivered entry. -/
def smIDBadAt (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS k : ℕ)
    (s : SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) : SMIDQuery W Hdr Ct → Bool
  | .sm _ => false
  | .deliver p h ad c =>
    match s.2.epochOf (ckaShadow s.1.ck) p (M.hdrPub h) with
    | none => false
    | some e => decide (e = k) && s.2.safe ΔFS ΔPCS p e (M.hdrPos h) &&
      match M.rkey (s.1.ck.st p) h with
      | none => false
      | some y => M.decrypt y.2 h ad c != (s.2.findEntry e h ad c).map SMIDLogEntry.pt

/-- The oracle `smIDOracleAt` with a flag that is set at a forgery at the epoch `k`. -/
noncomputable def smIDFlagOracle (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS t : ℕ)
    (idealC : Bool) (idealD : ℕ → Bool) (k : ℕ)
    (s : (SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) × Bool) (d : SMIDQuery W Hdr Ct) :
    PMF (SMIDAns Pub Hdr Ct Leak W × ((SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) × Bool)) :=
  (smIDOracleAt M ΔFS ΔPCS t idealC idealD s.1 d).map fun y =>
    (y.1, (y.2, s.2 || smIDBadAt M ΔFS ΔPCS k s.1 d))

/-- The run of `A` against the flagged oracle `smIDFlagOracle` at the challenge epoch `t` from
the initial state `i` of the scheme. -/
noncomputable def smIDFlagRun (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS : ℕ)
    (idealC : Bool) (idealD : ℕ → Bool) (k : ℕ) (A : SMIDAdv Pub W Hdr Ct Leak) (t : ℕ)
    (i : Pub × St × St) :
    PMF (Bool × ((SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) × Bool)) :=
  OracleAdv.run (smIDFlagOracle M ΔFS ΔPCS t idealC idealD k) (A.play t i.1)
    ((SMSchemeSt.init i, SMIDAux.init i.1), false)

/-- **The forgery event at the epoch `k`**: the game that runs `A` in the hybrid `k + 1` and
outputs whether a forgery at the epoch `k` was delivered. -/
noncomputable def smIDBadGame (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS k : ℕ)
    (A : SMIDAdv Pub W Hdr Ct Leak) : SPComp Bool :=
  SPComp.bind (liftPMF A.tStar) fun t => SPComp.bind M.init fun i =>
    liftPMF ((smIDFlagRun M ΔFS ΔPCS false (fun e => decide (e < k + 1)) k A t i).map
      fun x => x.2.2)

/-- The output of the flagged run is the output of the run against `smIDOracleAt`. -/
theorem smIDFlagRun_map_fst (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS : ℕ)
    (idealC : Bool) (idealD : ℕ → Bool) (k : ℕ) (A : SMIDAdv Pub W Hdr Ct Leak) (t : ℕ)
    (i : Pub × St × St) :
    (smIDFlagRun M ΔFS ΔPCS idealC idealD k A t i).map Prod.fst =
      (OracleAdv.run (smIDOracleAt M ΔFS ΔPCS t idealC idealD) (A.play t i.1)
        (SMSchemeSt.init i, SMIDAux.init i.1)).map Prod.fst := by
  have hstep : ∀ s d, (smIDFlagOracle M ΔFS ΔPCS t idealC idealD k s d).map
      (Prod.map id Prod.fst) = smIDOracleAt M ΔFS ΔPCS t idealC idealD s.1 d := by
    intro s d
    rw [smIDFlagOracle, PMF.map_comp]
    exact PMF.map_id _
  have h := OracleAdv.run_map_state _ _ Prod.fst hstep (A.play t i.1)
    ((SMSchemeSt.init i, SMIDAux.init i.1), false)
  dsimp only at h
  rw [smIDFlagRun, ← h, PMF.map_comp]
  rfl

omit [Fintype Rand] [Nonempty Rand] in
/-- Without a forgery at the epoch `k`, the hybrids `k` and `k + 1` answer a delivery alike. -/
theorem smIDDeliver_agree (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS k : ℕ)
    (s : SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) (p : CKAParty) (h : Hdr) (ad : W) (c : Ct)
    (hb : smIDBadAt M ΔFS ΔPCS k s (.deliver p h ad c) = false) :
    smIDDeliver M ΔFS ΔPCS (fun e => decide (e < k)) s p h ad c =
      smIDDeliver M ΔFS ΔPCS (fun e => decide (e < k + 1)) s p h ad c := by
  simp only [smIDBadAt] at hb
  unfold smIDDeliver
  cases he : s.2.epochOf (ckaShadow s.1.ck) p (M.hdrPub h) with
  | none => rfl
  | some e =>
    simp only [he] at hb
    dsimp only
    by_cases hek : e = k
    · subst hek
      by_cases hsafe : s.2.safe ΔFS ΔPCS p e (M.hdrPos h) = true
      · simp only [hsafe, ite_true]
        cases hr : M.rkey (s.1.ck.st p) h with
        | none => rfl
        | some y =>
          simp only [hsafe, hr, decide_true, Bool.true_and, bne_eq_false_iff_eq] at hb
          simp [hb]
      · simp [hsafe]
    · have hd : decide (e < k) = decide (e < k + 1) := by grind
      simp only [hd]

/-- The flag of `smIDFlagOracle` stays set. -/
theorem smIDFlagOracle_sticky (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS t : ℕ)
    (idealC : Bool) (idealD : ℕ → Bool) (k : ℕ) (s : SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct)
    (d : SMIDQuery W Hdr Ct) (r : SMIDAns Pub Hdr Ct Leak W)
    (s' : SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) :
    smIDFlagOracle M ΔFS ΔPCS t idealC idealD k (s, true) d (r, (s', false)) = 0 := by
  refine (PMF.apply_eq_zero_iff _ _).mpr ?_
  simp [smIDFlagOracle]

/-- The flagged hybrids `k` and `k + 1` agree on every transition that leaves the flag
cleared. -/
theorem smIDFlagOracle_agree (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS t : ℕ)
    (idealC : Bool) (k : ℕ) (s : (SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) × Bool)
    (d : SMIDQuery W Hdr Ct) (r : SMIDAns Pub Hdr Ct Leak W)
    (s' : SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) :
    smIDFlagOracle M ΔFS ΔPCS t idealC (fun e => decide (e < k)) k s d (r, (s', false)) =
      smIDFlagOracle M ΔFS ΔPCS t idealC (fun e => decide (e < k + 1)) k s d
        (r, (s', false)) := by
  by_cases hb : (s.2 || smIDBadAt M ΔFS ΔPCS k s.1 d) = true
  · rw [(PMF.apply_eq_zero_iff _ _).mpr, (PMF.apply_eq_zero_iff _ _).mpr] <;>
      simp [smIDFlagOracle, hb]
  · cases d with
    | sm q => rfl
    | deliver p h ad c =>
      simp only [Bool.or_eq_true, not_or] at hb
      simp only [smIDFlagOracle, smIDOracleAt]
      rw [smIDDeliver_agree M ΔFS ΔPCS k s.1 p h ad c (by simpa using hb.2)]

/-- **Identical until a forgery.** The integrity advantage at the epoch `k` is at most the
probability of a forgery at the epoch `k` in the hybrid `k + 1`. -/
theorem SMIDScheme.epochIntAdvantage_le_bad (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (ΔFS ΔPCS k : ℕ) (A : SMIDAdv Pub W Hdr Ct Leak) :
    M.epochIntAdvantage ΔFS ΔPCS k A ≤ prTrue (smIDBadGame M ΔFS ΔPCS k A) Heap.empty := by
  have hg : ∀ idealD, smIDGameAt M ΔFS ΔPCS false idealD A =
      SPComp.bind (liftPMF A.tStar) fun t => SPComp.bind M.init fun i =>
        liftPMF ((smIDFlagRun M ΔFS ΔPCS false idealD k A t i).map Prod.fst) := by
    intro idealD
    simp only [smIDGameAt, smIDFlagRun_map_fst]
  unfold SMIDScheme.epochIntAdvantage smIDBadGame
  rw [hg, hg]
  exact advantage_bind_liftPMF_le_flag _ _
    (fun t i => smIDFlagRun M ΔFS ΔPCS false (fun e => decide (e < k)) k A t i)
    (fun t i => smIDFlagRun M ΔFS ΔPCS false (fun e => decide (e < k + 1)) k A t i)
    fun t i a s => OracleAdv.run_apply_flag_false_eq _ _
      (smIDFlagOracle_sticky M ΔFS ΔPCS t false _ k)
      (smIDFlagOracle_sticky M ΔFS ΔPCS t false _ k)
      (smIDFlagOracle_agree M ΔFS ΔPCS t false k) _ _ a s

/-- The epoch `k` lies outside the corruption window of every answered corruption. -/
def SMIDAux.epochSafe {Pub' : Type} (ΔFS ΔPCS : ℕ) (x : SMIDAux W Pub' Hdr Ct) (k : ℕ) : Bool :=
  x.corrs.all fun c => ckaAllowCorr ΔFS ΔPCS k c.2.1 c.1

omit [DecidableEq Pub] [DecidableEq W] [DecidableEq Hdr] [DecidableEq Ct] in
/-- A safe delivery is into a safe epoch. -/
theorem SMIDAux.epochSafe_of_safe (ΔFS ΔPCS : ℕ) (x : SMIDAux W Pub Hdr Ct) (p : CKAParty)
    (e j : ℕ) (h : x.safe ΔFS ΔPCS p e j = true) : x.epochSafe ΔFS ΔPCS e = true := by
  simp only [SMIDAux.safe, List.all_eq_true, Bool.and_eq_true] at h
  simp only [SMIDAux.epochSafe, List.all_eq_true]
  exact fun c hc => (h c hc).1

omit [DecidableEq Pub] [DecidableEq W] [DecidableEq Hdr] [DecidableEq Ct] in
/-- An epoch outside the safe epochs stays outside them. -/
theorem SMIDAux.epochSafe_upd_of_false (ΔFS ΔPCS k : ℕ) (pos : Hdr → ℕ)
    (x : SMIDAux W Pub Hdr Ct) (sh : CKAGameSt Unit Unit) (q : SMQuery W)
    (a : SMSchemeAns Pub (Hdr × Ct) Leak) (h : x.epochSafe ΔFS ΔPCS k = false) :
    (x.upd pos sh q a).epochSafe ΔFS ΔPCS k = false := by
  cases q <;> cases a <;> simp_all [SMIDAux.upd, SMIDAux.record, SMIDAux.epochSafe]

omit [Fintype Rand] [Nonempty Rand] in
/-- A delivery keeps the answered corruptions. -/
theorem smIDDeliver_corrs (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS : ℕ)
    (idealD : ℕ → Bool) (s : SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) (p : CKAParty) (h : Hdr)
    (ad : W) (c : Ct) : (smIDDeliver M ΔFS ΔPCS idealD s p h ad c).2.2.corrs = s.2.corrs := by
  unfold smIDDeliver
  repeat' split
  all_goals rfl

omit [Fintype Rand] [Nonempty Rand] in
/-- Outside the safe epochs there is no forgery. -/
theorem smIDBadAt_of_epochSafe_false (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (ΔFS ΔPCS k : ℕ) (s : SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct)
    (hs : s.2.epochSafe ΔFS ΔPCS k = false) (d : SMIDQuery W Hdr Ct) :
    smIDBadAt M ΔFS ΔPCS k s d = false := by
  cases d with
  | sm q => rfl
  | deliver p h ad c =>
    simp only [smIDBadAt]
    cases he : s.2.epochOf (ckaShadow s.1.ck) p (M.hdrPub h) with
    | none => rfl
    | some e =>
      by_cases hek : e = k
      · subst hek
        have hsafe : s.2.safe ΔFS ΔPCS p e (M.hdrPos h) = false := by
          cases hc : s.2.safe ΔFS ΔPCS p e (M.hdrPos h)
          · rfl
          · rw [SMIDAux.epochSafe_of_safe ΔFS ΔPCS s.2 p e _ hc] at hs
            exact absurd hs (by decide)
        simp [hsafe]
      · simp [hek]

/-- **The oracle truncated at the corruption of the epoch `k`**: the flagged oracle, which from
the first answered corruption with the epoch `k` in its window on answers every query by a
rejection and keeps its state. -/
noncomputable def smIDTruncOracle (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS t : ℕ)
    (idealC : Bool) (idealD : ℕ → Bool) (k : ℕ)
    (s : (SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) × Bool) (d : SMIDQuery W Hdr Ct) :
    PMF (SMIDAns Pub Hdr Ct Leak W × ((SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) × Bool)) :=
  if s.1.2.epochSafe ΔFS ΔPCS k then smIDFlagOracle M ΔFS ΔPCS t idealC idealD k s d
  else PMF.pure (.dec none, s)

/-- **The truncated forgery game at the epoch `k`**: `smIDBadGame` with the oracle truncated at
the first corruption that falls in the window of the epoch `k`. -/
noncomputable def smIDTruncGame (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS k : ℕ)
    (A : SMIDAdv Pub W Hdr Ct Leak) : SPComp Bool :=
  SPComp.bind (liftPMF A.tStar) fun t => SPComp.bind M.init fun i =>
    liftPMF ((OracleAdv.run
      (smIDTruncOracle M ΔFS ΔPCS t false (fun e => decide (e < k + 1)) k) (A.play t i.1)
      ((SMSchemeSt.init i, SMIDAux.init i.1), false)).map fun x => x.2.2)

/-- After a corruption in the window of the epoch `k`, the flagged oracle keeps the flag and
the epoch outside the safe epochs. -/
theorem smIDFlagOracle_stopped (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS t : ℕ)
    (idealC : Bool) (idealD : ℕ → Bool) (k : ℕ)
    (s : (SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) × Bool)
    (hs : s.1.2.epochSafe ΔFS ΔPCS k = false) (d : SMIDQuery W Hdr Ct) :
    ∀ x ∈ (smIDFlagOracle M ΔFS ΔPCS t idealC idealD k s d).support,
      x.2.1.2.epochSafe ΔFS ΔPCS k = false ∧ x.2.2 = s.2 := by
  intro x hx
  simp only [smIDFlagOracle, PMF.support_map, Set.mem_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨?_, by simp [smIDBadAt_of_epochSafe_false M ΔFS ΔPCS k s.1 hs d]⟩
  cases d with
  | sm q =>
    simp only [smIDOracleAt] at hy
    split at hy
    · simp only [PMF.support_map, Set.mem_image] at hy
      obtain ⟨z, -, rfl⟩ := hy
      exact SMIDAux.epochSafe_upd_of_false _ _ _ _ _ _ _ _ hs
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact hs
  | deliver p h ad c =>
    simp only [smIDOracleAt, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    simp only [Prod.map, id_eq, SMIDAux.epochSafe, smIDDeliver_corrs]
    exact hs

/-- **Every forgery precedes the corruption of its epoch.** The truncated forgery game at the
epoch `k` is the forgery game at the epoch `k`: after a corruption in the window of the epoch
`k`, no delivery into the epoch `k` is answered. -/
theorem smIDTruncGame_eq (M : SMIDScheme St Pub Rand W Ct Leak Hdr K) (ΔFS ΔPCS k : ℕ)
    (A : SMIDAdv Pub W Hdr Ct Leak) :
    smIDTruncGame M ΔFS ΔPCS k A = smIDBadGame M ΔFS ΔPCS k A := by
  unfold smIDTruncGame smIDBadGame smIDFlagRun
  refine congrArg _ (funext fun t => congrArg _ (funext fun i => congrArg _ ?_))
  refine OracleAdv.run_map_eq_of_agree_until_stop _ _
    (fun s : (SMSchemeSt St Pub × SMIDAux W Pub Hdr Ct) × Bool =>
      s.1.2.epochSafe ΔFS ΔPCS k = false) (fun s => s.2) ?_ ?_ ?_ _ _
  · intro s d hs
    simp [smIDTruncOracle, hs]
  · intro s d hs x hx
    simp only [smIDTruncOracle, hs, Bool.false_eq_true, ite_false, PMF.support_pure,
      Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨hs, rfl⟩
  · exact fun s d hs => smIDFlagOracle_stopped M ΔFS ΔPCS t false _ k s hs d

end UntilBad

end CatCrypt.Crypto.Messaging
