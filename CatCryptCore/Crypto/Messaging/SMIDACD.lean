/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SMID
import CatCryptCore.Tactics.AutoDispatchExt

/-!
# The ACD construction with headers and a store of skipped keys

The double ratchet of Alwen, Coretti and Dodis (EUROCRYPT 2019) as a scheme with headers and
immediate decryption (`SMIDScheme`), after the Signal Double Ratchet specification.

## The construction

`acdIDHdrSM C R G D hdrAD pub₀ pnOk maxSkip maxStored` keeps, besides the state `SMPartySt` of
the ACD construction (`acdSMAD`), the public value `pubS = (T, PN)` of its sending epoch, the
number `ns` of messages sent in it, its epoch counter `ep`, its receiving epoch `er`, the next
position `nr` of the receiving chain, the received epochs with their public values `rpubs`, and
a store of skipped message keys indexed by epoch and position.

* The public value of an opening is `(T, PN)`: the CKA message and the number of messages the
  sender sent in its previous sending epoch. Both parties start with the public value
  `(pub₀ T₀, 0)` of their sending epoch at the public value `T₀` of the initialisation.
* The header of a message is `((T, PN), N)`, the public value of the sending epoch and the
  position `N`.
* Receiving the public value `(T, PN)` of a new epoch runs the skip check `pnOk x PN`; when it
  holds, the keys of the positions from `nr` below `PN` of the closed receiving chain are
  stored, otherwise the closed chain is dropped without storing keys. The receiving chain is
  replaced by the new one. `ACDIDSt.recvSkipOk` is the check of the Signal specification:
  `PN - nr ≤ maxSkip` and the store with the skipped keys holds at most `maxStored` keys.
* `rkey x h` resolves the public value of the header to the latest received epoch with that
  public value. At the receiving epoch and a position `N ≥ nr` it steps the receiving chain,
  when `N - nr ≤ maxSkip` and the store with the skipped keys holds at most `maxStored` keys,
  and stores the keys of the skipped positions; otherwise it takes the key of the epoch and the
  position out of the store.
* A send encrypts with the AEAD `D` at the associated data `hdrAD a h` of the message and its
  header (`acdIDHdrSM_send_ct`), and `decrypt k h a c = D.decrypt k c (hdrAD a h)`.

`acdIDSM C R G D dec enc maxSkip maxStored` is `acdIDHdrSM` at the AEAD `aeadEncComapAD D`,
which encrypts at `dec (enc h a)` and decrypts at `(a, h)`, at `hdrAD = Prod.mk`, the default
start value and the skip check that always holds. Its base scheme is
`acdIDBase C R G D dec = acdSMAD C R G D (fun _ w => dec w)`: the sender passes `(m, enc h a)` to
the base scheme, and when `dec` is a left inverse of `enc` the AEAD sees the associated data
`(a, h)` (`acdIDSM_send_ct`).

## The reduction to the base scheme

`acdIDViewAt` computes the header, the success of the key lookup, the public value of an opening
and the corruption answer from the bookkeeping of the game and the cuts `cut p e` of the closed
receiving epochs whose skip check failed: such an epoch keeps the keys of the positions below
the position `nr` at which it was closed. On the states of the invariant `ACDIDHdrInv` the store
holds exactly the keys of the logged messages of `acdQualAt`: the undelivered logged messages
addressed to the party in the closed receiving epochs below their cuts and at the skipped
positions of the receiving epoch, so that under the restricted gate of `SMIDAux.storeClear` it
holds keys of the receiving epoch only, which follow from the exposed receiving chain. Receiving
sets the cut of the closed epoch by the result of the skip check (`acdIDHdr_inv_recv`), and the
cuts stay empty when every skip check holds (`acdIDHdr_inv_step`).

For `acdIDSM` there are no cuts: `acdIDView` and `ACDIDInv` are `acdIDViewAt` and the invariant
at no cuts, and `acdIDSM_over` proves `SMIDScheme.Over` for `acdIDSM` over `acdIDBase`, so that
`SMIDScheme.idAdvantage_le` applies.

## Main definitions

* `ACDHdr`, `ACDIDSt`, `ACDIDLeak`, `ACDIDSt.recvSkipOk`, `acdIDRKey`, `aeadEncComapAD`,
  `acdIDHdrBase`, `acdIDHdrSM`, `acdIDBase`, `acdIDSM`
* `acdCnt`, `acdNr`, `acdQual`, `acdQualAt`, `acdNs`, `acdPubAt`, `acdPubSAt`, `acdPubS`,
  `acdRPubs`, `acdIDViewAt`, `acdIDView`, `acdCutRecv`
* `ACDIDPartyInvAt`, `ACDIDPartyInv`, `ACDIDInvAt`, `ACDIDHdrInv`, `ACDIDInv`

## Main results

* `acdIDHdrSM_send_ct`, `acdIDSM_send_ct` — the associated data of the AEAD
* `acdIDHdr_inv_init`, `acdIDHdr_inv_recv`, `acdIDHdr_inv_step` — the invariant of the
  header-aware construction
* `acdIDHdr_rkeyOk_eq`, `acdIDHdr_expose` — the key lookup and the corruption answer of the view
* `acdIDSM_over` — the construction over the base scheme
* `acdIDSM_idAdvantage_le` — the bound of `SMIDScheme.idAdvantage_le` at the construction
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open scoped ENNReal

/-! ## The construction -/

/-- The header of the ACD construction with headers: the public value `(T, PN)` of the sending
epoch and the position `N` of the message. -/
abbrev ACDHdr (Msg : Type) := (Msg × ℕ) × ℕ

/-- The party state of the ACD construction with headers. -/
structure ACDIDSt (Sc RK Sa Msg W : Type) where
  /-- The state of the ACD construction. -/
  base : SMPartySt Sc RK Sa
  /-- The public value of the sending epoch. -/
  pubS : Msg × ℕ
  /-- The number of messages sent in the sending epoch. -/
  ns : ℕ
  /-- The number of epochs opened or received. -/
  ep : ℕ
  /-- The receiving epoch. -/
  er : ℕ
  /-- The next position of the receiving chain. -/
  nr : ℕ
  /-- The received epochs with their public values, the latest first. -/
  rpubs : List (ℕ × (Msg × ℕ))
  /-- The stored keys with their epochs and positions. -/
  store : List (ℕ × ℕ × W)

/-- The corruption answer of the ACD construction with headers: the state, with the store given
by its lookup function. -/
structure ACDIDLeak (Sc RK Sa Msg W : Type) where
  /-- The state of the ACD construction. -/
  base : SMPartySt Sc RK Sa
  /-- The public value of the sending epoch. -/
  pubS : Msg × ℕ
  /-- The number of messages sent in the sending epoch. -/
  ns : ℕ
  /-- The number of epochs opened or received. -/
  ep : ℕ
  /-- The receiving epoch. -/
  er : ℕ
  /-- The next position of the receiving chain. -/
  nr : ℕ
  /-- The received epochs with their public values. -/
  rpubs : List (ℕ × (Msg × ℕ))
  /-- The stored key of an epoch and a position. -/
  keys : ℕ × ℕ → Option W

namespace ACDIDSt

variable {Sc RK Sa Msg Kt : Type}

/-- The state of the construction over a state of the ACD construction, with empty
bookkeeping. -/
def embed [Inhabited Msg] (b : SMPartySt Sc RK Sa) : ACDIDSt Sc RK Sa Msg Kt :=
  ⟨b, (default, 0), 0, 0, 0, 0, [], []⟩

/-- The epoch and the position of a stored key. -/
def tag (el : ℕ × ℕ × Kt) : ℕ × ℕ := (el.1, el.2.1)

/-- The stored key of the epoch and the position `t`. -/
def lookup (x : ACDIDSt Sc RK Sa Msg Kt) (t : ℕ × ℕ) : Option Kt :=
  (x.store.find? fun el => tag el == t).map fun el => el.2.2

/-- The keys of the `n` positions from `a` of the chain `sa` of the epoch `e`. -/
def skipKeys (G : PRGDef Sa (Kt × Sa)) (e : ℕ) (sa : Sa) (a n : ℕ) : List (ℕ × ℕ × Kt) :=
  (List.range' a n).map fun i => (e, i, chainKey G sa i)

/-- The skip check of a receiving step at the number `PN` of messages of the closed receiving
chain: at most `maxSkip` positions are skipped from `nr`, and the store with the skipped keys
holds at most `maxStored` keys. -/
def recvSkipOk (maxSkip maxStored : ℕ) (x : ACDIDSt Sc RK Sa Msg Kt) (PN : ℕ) : Bool :=
  decide (PN - x.nr ≤ maxSkip ∧ x.store.length + (PN - x.nr) ≤ maxStored)

end ACDIDSt

section Construction

variable {Sc Msg Key Rand RK Sa W Ct Kt : Type}

/-- The key lookup of the ACD construction with headers: the epoch of the header is the latest
received epoch with its public value; at the receiving epoch and a position from `nr` on, the
receiving chain is stepped within `maxSkip` positions and `maxStored` stored keys, and the keys
of the skipped positions are stored; otherwise the key is taken out of the store. -/
def acdIDRKey [DecidableEq Msg] (G : PRGDef Sa (Kt × Sa)) (maxSkip maxStored : ℕ)
    (x : ACDIDSt Sc RK Sa Msg Kt) (h : ACDHdr Msg) : Option (ACDIDSt Sc RK Sa Msg Kt × Kt) :=
  match x.rpubs.find? fun q => decide (q.2 = h.1) with
  | none => none
  | some q =>
    if q.1 = x.er ∧ x.nr ≤ h.2 then
      if h.2 - x.nr ≤ maxSkip ∧ x.store.length + (h.2 - x.nr) ≤ maxStored then
        x.base.rcv.map fun sa =>
          (⟨x.base, x.pubS, x.ns, x.ep, x.er, h.2 + 1, x.rpubs,
              ACDIDSt.skipKeys G x.er sa x.nr (h.2 - x.nr) ++ x.store⟩, chainKey G sa h.2)
      else none
    else
      (x.store.find? fun el => ACDIDSt.tag el == (q.1, h.2)).map fun el =>
        (⟨x.base, x.pubS, x.ns, x.ep, x.er, x.nr, x.rpubs,
          x.store.filter fun el' => ACDIDSt.tag el' != (q.1, h.2)⟩, el.2.2)

/-- The AEAD `D` with the associated data of its encryption read through `ρ`; decryption is that
of `D`. -/
def aeadEncComapAD {AD : Type} [SampleableType W] (D : AEADDef W Ct AD Kt) (ρ : AD → AD) :
    AEADDef W Ct AD Kt where
  encrypt k pt ad := D.encrypt k pt (ρ ad)
  decrypt := D.decrypt

variable [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct] [Fintype RK]
  [Nonempty RK] [SampleableType Kt]

/-- The base scheme of the header-aware ACD construction at the header `h`: `acdSMAD` with the
associated data `hdrAD ad h` of the AEAD. -/
noncomputable def acdIDHdrBase {AD : Type} (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct AD Kt)
    (hdrAD : W → ACDHdr Msg → AD) (h : ACDHdr Msg) :
    SMScheme (SMPartySt Sc RK Sa) Msg Rand W Ct (SMPartySt Sc RK Sa) :=
  acdSMAD C R G D fun _ ad => hdrAD ad h

/-- **The header-aware ACD construction with headers and a store of skipped keys.** The AEAD
`D` encrypts and decrypts at the associated data `hdrAD ad h` of the message and its header,
both parties start with the public value `(pub₀ T, 0)` of their sending epoch at the public value
`T` of the initialisation, and receiving the public value `(T, PN)` of a new epoch stores the
keys of the positions from `nr` below `PN` of the closed receiving chain when the skip check
`pnOk x PN` holds; when it fails, the closed chain is dropped without storing keys. -/
noncomputable def acdIDHdrSM {AD : Type} [Inhabited Msg] [DecidableEq Msg]
    (C : CKADef Sc Msg Key) [CKACoins C Rand] (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (Kt × Sa)) (D : AEADDef W Ct AD Kt) (hdrAD : W → ACDHdr Msg → AD)
    (pub₀ : Msg → Msg) (pnOk : ACDIDSt Sc RK Sa Msg Kt → ℕ → Bool) (maxSkip maxStored : ℕ) :
    SMIDScheme (ACDIDSt Sc RK Sa Msg Kt) (Msg × ℕ) Rand W Ct (ACDIDLeak Sc RK Sa Msg Kt)
      (ACDHdr Msg) Kt where
  init := SPComp.bind (acdIDHdrBase C R G D hdrAD default).init fun i =>
    SPComp.pure ((i.1, 0), ⟨i.2.1, (pub₀ i.1, 0), 0, 0, 0, 0, [], []⟩,
      ⟨i.2.2, (pub₀ i.1, 0), 0, 0, 0, 0, [], []⟩)
  ratchet x r :=
    (⟨((acdIDHdrBase C R G D hdrAD (x.pubS, x.ns)).ratchet x.base r).1,
        (((acdIDHdrBase C R G D hdrAD (x.pubS, x.ns)).ratchet x.base r).2, x.ns), 0, x.ep + 1,
        x.er, x.nr, x.rpubs, x.store⟩,
      (((acdIDHdrBase C R G D hdrAD (x.pubS, x.ns)).ratchet x.base r).2, x.ns))
  recv x T :=
    ⟨(acdIDHdrBase C R G D hdrAD (x.pubS, x.ns)).recv x.base T.1, x.pubS, x.ns, x.ep + 1,
      x.ep + 1, 0, (x.ep + 1, T) :: x.rpubs,
      (if x.er = 0 then [] else bif pnOk x T.2 then
        (x.base.rcv.map fun sa => ACDIDSt.skipKeys G x.er sa x.nr (T.2 - x.nr)).getD []
        else []) ++ x.store⟩
  send x m := ((acdIDHdrBase C R G D hdrAD (x.pubS, x.ns)).send x.base m).map fun y =>
    (⟨y.1, x.pubS, x.ns + 1, x.ep, x.er, x.nr, x.rpubs, x.store⟩, y.2)
  expose x := ⟨x.base, x.pubS, x.ns, x.ep, x.er, x.nr, x.rpubs, x.lookup⟩
  idealCt := (acdIDHdrBase C R G D hdrAD default).idealCt
  hdr x := (x.pubS, x.ns)
  hdrPub h := h.1
  hdrPos h := h.2
  rkey := acdIDRKey G maxSkip maxStored
  decrypt k h a c := D.decrypt k c (hdrAD a h)

/-- The base scheme of the ACD construction with headers: `acdSMAD` with the associated data of
the AEAD decoded by `dec` from the associated data of the message. -/
noncomputable def acdIDBase (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa))
    (D : AEADDef W Ct (W × ACDHdr Msg) Kt) (dec : W → W × ACDHdr Msg) :
    SMScheme (SMPartySt Sc RK Sa) Msg Rand W Ct (SMPartySt Sc RK Sa) :=
  acdSMAD C R G D fun _ w => dec w

/-- **The ACD construction with headers and a store of skipped keys**: `acdIDHdrSM` with the
associated data `(a, h)`, encryption at `dec (enc h a)`, the default public value of the sending
epoch at the start, and no skip check at receiving. -/
noncomputable def acdIDSM [Inhabited Msg] [DecidableEq Msg] (C : CKADef Sc Msg Key)
    [CKACoins C Rand] (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa))
    (D : AEADDef W Ct (W × ACDHdr Msg) Kt) (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W)
    (maxSkip maxStored : ℕ) :
    SMIDScheme (ACDIDSt Sc RK Sa Msg Kt) (Msg × ℕ) Rand W Ct (ACDIDLeak Sc RK Sa Msg Kt)
      (ACDHdr Msg) Kt :=
  acdIDHdrSM C R G (aeadEncComapAD D fun ah => dec (enc ah.2 ah.1)) Prod.mk (fun _ => default)
    (fun _ _ => true) maxSkip maxStored

omit [SampleableType Kt] [Fintype Rand] [Nonempty Rand] in
/-- **The associated data of the AEAD of the header-aware construction.** A send encrypts the
plaintext under the next key of the sending chain with the associated data `hdrAD` of the
message and the header `(pubS, ns)` of the sender. -/
theorem acdIDHdrSM_send_ct {AD : Type} [Inhabited Msg] [DecidableEq Msg] (C : CKADef Sc Msg Key)
    [CKACoins C Rand] (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa))
    (D : AEADDef W Ct AD Kt) (hdrAD : W → ACDHdr Msg → AD) (pub₀ : Msg → Msg)
    (pnOk : ACDIDSt Sc RK Sa Msg Kt → ℕ → Bool) (maxSkip maxStored : ℕ)
    (x : ACDIDSt Sc RK Sa Msg Kt) (m : W × W) :
    ((acdIDHdrSM C R G D hdrAD pub₀ pnOk maxSkip maxStored).send x m).map Prod.snd =
      x.base.snd.map fun sa => D.encrypt (G.stretch sa).1 m.1 (hdrAD m.2 (x.pubS, x.ns)) := by
  cases hs : x.base.snd <;> simp [acdIDHdrSM, acdIDHdrBase, acdSMAD, hs]

omit [SampleableType Kt] [Fintype Rand] [Nonempty Rand] in
/-- **The associated data of the AEAD.** When `dec` is a left inverse of `enc`, a send of the
construction encrypts the plaintext under the next key of the sending chain with the associated
data of the message and the header `(pubS, ns)` of the sender. The hypothesis `hdec`, an
injective packing of the header and the associated data into a finite word type `W`, holds for
no finite `W`, so the statement has content only for an infinite `W`. -/
theorem acdIDSM_send_ct [Inhabited Msg] [DecidableEq Msg] (C : CKADef Sc Msg Key)
    [CKACoins C Rand] (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (Kt × Sa))
    (D : AEADDef W Ct (W × ACDHdr Msg) Kt) (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W)
    (hdec : ∀ h a, dec (enc h a) = (a, h)) (maxSkip maxStored : ℕ)
    (x : ACDIDSt Sc RK Sa Msg Kt) (m : W × W) :
    ((acdIDSM C R G D dec enc maxSkip maxStored).send x m).map Prod.snd =
      x.base.snd.map fun sa =>
        D.encrypt (G.stretch sa).1 m.1 (m.2, (x.pubS, x.ns)) := by
  rw [acdIDSM, acdIDHdrSM_send_ct]
  simp [aeadEncComapAD, hdec]

end Construction

/-! ## The bookkeeping view -/

section View

variable {W Hdr Ct Msg : Type}

/-- The epoch and the position of a log entry. -/
def acdTag (l : SMIDLogEntry W Hdr Ct) : ℕ × ℕ := (l.e, l.j)

/-- The number of logged messages of the epoch `e`. -/
def acdCnt (log : List (SMIDLogEntry W Hdr Ct)) (e : ℕ) : ℕ :=
  (log.map acdTag).countP fun t => t.1 == e

/-- The position after the delivered logged messages of the epoch `e`. -/
def acdNr (log : List (SMIDLogEntry W Hdr Ct)) (e : ℕ) : ℕ :=
  ((log.filter fun l => l.delivered && l.e == e).map fun l => l.j + 1).foldr max 0

/-- The logged message is undelivered, addressed to `p`, of an epoch from `1`, and of an epoch
before `er` or of the epoch `er` at a position before `nr`: its key is stored by `p`. -/
def acdQual (p : CKAParty) (er nr : ℕ) (l : SMIDLogEntry W Hdr Ct) : Bool :=
  !l.delivered && ckaSender l.e != p && decide (1 ≤ l.e) &&
    (decide (l.e < er) || (l.e == er && decide (l.j < nr)))

/-- The logged message satisfies `acdQual`, and its epoch is not before `er` or its position is
below the cut `cut p e` of its epoch `e`, when there is one: its key is stored by `p` when each
closed receiving epoch `e` with `cut p e = some n` was closed at the position `n` after a failed
skip check. -/
def acdQualAt (cut : CKAParty → ℕ → Option ℕ) (p : CKAParty) (er nr : ℕ)
    (l : SMIDLogEntry W Hdr Ct) : Bool :=
  ((cut p l.e).all (fun n => decide (l.j < n)) || decide (er ≤ l.e)) && acdQual p er nr l

/-- The number of messages party `p` at the counter `t` sent in its sending epoch: the epoch
`t` when `p` sends it, the epoch `t - 1` otherwise, and none at the counter `0`. -/
def acdNs (log : List (SMIDLogEntry W Hdr Ct)) (t : ℕ) (p : CKAParty) : ℕ :=
  if ckaSender t = p then acdCnt log t else if t = 0 then 0 else acdCnt log (t - 1)

/-- The public value of the opened epoch `n`. -/
def acdPubAt [Inhabited Msg] (pubs : List (ℕ × (Msg × ℕ))) (n : ℕ) : Msg × ℕ :=
  ((pubs.find? fun q => q.1 == n).map Prod.snd).getD (default, 0)

/-- The public value of the sending epoch of `p` at the counter `t`, or `(pub₀ T, 0)` at the
public value `(T, _)` of the epoch `0` when `p` has opened no epoch. -/
def acdPubSAt [Inhabited Msg] (pub₀ : Msg → Msg) (pubs : List (ℕ × (Msg × ℕ))) (t : ℕ)
    (p : CKAParty) : Msg × ℕ :=
  if ckaSender t = p then (if t = 0 then (pub₀ (acdPubAt pubs 0).1, 0) else acdPubAt pubs t)
  else if t ≤ 1 then (pub₀ (acdPubAt pubs 0).1, 0) else acdPubAt pubs (t - 1)

/-- The public value of the sending epoch of `p` at the counter `t`, or the default value when
`p` has opened no epoch. -/
def acdPubS [Inhabited Msg] (pubs : List (ℕ × (Msg × ℕ))) (t : ℕ) (p : CKAParty) : Msg × ℕ :=
  acdPubSAt (fun _ => default) pubs t p

/-- The epochs from `1` received by `p` at the counter `t` with their public values. -/
def acdRPubs (pubs : List (ℕ × (Msg × ℕ))) (t : ℕ) (p : CKAParty) : List (ℕ × (Msg × ℕ)) :=
  pubs.filter fun q => decide (1 ≤ q.1) && decide (q.1 ≤ t) && ckaSender q.1 != p

variable {Sc RK Sa Kt : Type}

/-- The public part of the header-aware ACD construction, computed from the bookkeeping, with
the message of the base scheme given by `msg`, the start value `pub₀` of the public value of the
sending epoch, and the cuts `cut` of the closed receiving epochs whose skip check failed. -/
def acdIDViewAt [Inhabited Msg] [DecidableEq Msg] (G : PRGDef Sa (Kt × Sa))
    (maxSkip maxStored : ℕ) (msg : ACDHdr Msg → W × W → W × W) (pub₀ : Msg → Msg)
    (cut : CKAParty → ℕ → Option ℕ) :
    SMIDView W (Msg × ℕ) (ACDHdr Msg) Ct (ACDIDLeak Sc RK Sa Msg Kt) W Msg
      (SMPartySt Sc RK Sa) where
  hdr x sh p := (acdPubSAt pub₀ x.pubs (sh.t p) p, acdNs x.log (sh.t p) p)
  rkeyOk x sh p h :=
    match (acdRPubs x.pubs (sh.t p) p).find? fun q => decide (q.2 = h.1) with
    | none => false
    | some q =>
      if q.1 = smRecvEpoch sh p ∧ acdNr x.log (smRecvEpoch sh p) ≤ h.2 then
        decide (h.2 - acdNr x.log (smRecvEpoch sh p) ≤ maxSkip ∧
          (x.log.filter (acdQualAt cut p (smRecvEpoch sh p)
            (acdNr x.log (smRecvEpoch sh p)))).length +
            (h.2 - acdNr x.log (smRecvEpoch sh p)) ≤ maxStored)
      else (cut p q.1).all (fun n => decide (h.2 < n)) || decide (smRecvEpoch sh p ≤ q.1)
  leak x sh p b :=
    ⟨b, acdPubSAt pub₀ x.pubs (sh.t p) p, acdNs x.log (sh.t p) p, sh.t p,
      smRecvEpoch sh p, acdNr x.log (smRecvEpoch sh p), acdRPubs x.pubs (sh.t p) p,
      fun t => if t.1 = smRecvEpoch sh p ∧ (x.log.any fun l =>
          acdQualAt cut p (smRecvEpoch sh p) (acdNr x.log (smRecvEpoch sh p)) l &&
            acdTag l == t) then
        b.rcv.map fun sa => chainKey G sa t.2 else none⟩
  msg := msg
  pub x sh p T := (T, acdNs x.log (sh.t p) p)
  pubInit T := (T, 0)

/-- The public part of the ACD construction with headers, computed from the bookkeeping:
`acdIDViewAt` with the base message `(m.1, enc h m.2)`, the default start value and no
cuts. -/
def acdIDView [Inhabited Msg] [DecidableEq Msg] (G : PRGDef Sa (Kt × Sa)) (maxSkip maxStored : ℕ)
    (enc : ACDHdr Msg → W → W) :
    SMIDView W (Msg × ℕ) (ACDHdr Msg) Ct (ACDIDLeak Sc RK Sa Msg Kt) W Msg (SMPartySt Sc RK Sa) :=
  acdIDViewAt G maxSkip maxStored (fun h m => (m.1, enc h m.2)) (fun _ => default)
    (fun _ _ => none)

/-- The invariant of a party `p` in the state `x`, at the epoch counters `sh`, with the log
`log` and the opened epochs `pubs`, with the public value of the sending epoch read by `pubSOf`
and the stored log entries selected by `qual`: its counters and public values are those of the
bookkeeping, and its store holds exactly the keys of the logged messages of `qual`. -/
structure ACDIDPartyInvAt (G : PRGDef Sa (Kt × Sa))
    (pubSOf : List (ℕ × (Msg × ℕ)) → ℕ → CKAParty → Msg × ℕ)
    (qual : CKAParty → ℕ → ℕ → SMIDLogEntry W Hdr Ct → Bool)
    (log : List (SMIDLogEntry W Hdr Ct)) (pubs : List (ℕ × (Msg × ℕ)))
    (sh : CKAGameSt Unit Unit) (p : CKAParty) (x : ACDIDSt Sc RK Sa Msg Kt) : Prop where
  /-- The epoch counter. -/
  ep : x.ep = sh.t p
  /-- The receiving epoch. -/
  er : x.er = smRecvEpoch sh p
  /-- The public value of the sending epoch. -/
  pubS : x.pubS = pubSOf pubs (sh.t p) p
  /-- The number of messages sent in the sending epoch. -/
  ns : x.ns = acdNs log (sh.t p) p
  /-- The next position of the receiving chain. -/
  nr : x.nr = acdNr log x.er
  /-- The received epochs. -/
  rpubs : x.rpubs = acdRPubs pubs (sh.t p) p
  /-- A receiving epoch from `1` has a receiving chain. -/
  rcv : 1 ≤ x.er → x.base.rcv.isSome
  /-- Each epoch and position is stored at most once. -/
  nodup : (x.store.map ACDIDSt.tag).Nodup
  /-- A stored key is the key of a logged message of `qual`; a stored key of the receiving
  epoch is the key of the receiving chain at its position. -/
  sound : ∀ el ∈ x.store, (∃ l ∈ log, qual p x.er x.nr l = true ∧ acdTag l = ACDIDSt.tag el) ∧
    (el.1 = x.er → x.base.rcv.map (fun sa => chainKey G sa el.2.1) = some el.2.2)
  /-- The key of every logged message of `qual` is stored. -/
  complete : ∀ l ∈ log, qual p x.er x.nr l = true → acdTag l ∈ x.store.map ACDIDSt.tag

/-- The invariant of a party of the ACD construction with headers: `ACDIDPartyInvAt` with
`acdPubS` and `acdQual`. -/
abbrev ACDIDPartyInv [Inhabited Msg] (G : PRGDef Sa (Kt × Sa))
    (log : List (SMIDLogEntry W Hdr Ct)) (pubs : List (ℕ × (Msg × ℕ)))
    (sh : CKAGameSt Unit Unit) (p : CKAParty) (x : ACDIDSt Sc RK Sa Msg Kt) : Prop :=
  ACDIDPartyInvAt G acdPubS acdQual log pubs sh p x

/-- The invariant of the game over a header-aware ACD construction with decryption from the
log, with the public value of the sending epoch read by `pubSOf` and the stored log entries
selected by `qual`. -/
structure ACDIDInvAt (G : PRGDef Sa (Kt × Sa))
    (pubSOf : List (ℕ × (Msg × ℕ)) → ℕ → CKAParty → Msg × ℕ)
    (qual : CKAParty → ℕ → ℕ → SMIDLogEntry W (ACDHdr Msg) Ct → Bool)
    (s : SMSchemeSt (ACDIDSt Sc RK Sa Msg Kt) (Msg × ℕ) × SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct) :
    Prop where
  /-- The epoch counters differ by at most one. -/
  t_le : s.1.ck.t .A ≤ s.1.ck.t .B + 1 ∧ s.1.ck.t .B ≤ s.1.ck.t .A + 1
  /-- A party one epoch ahead sends its epoch. -/
  ahead : ∀ p, s.1.ck.t p.other = s.1.ck.t p + 1 → ckaSender (s.1.ck.t p.other) = p.other
  /-- The opened epochs, the latest with the public value in transit first, in decreasing
  order. -/
  pubs : ∃ rest, s.2.pubs = (max (s.1.ck.t .A) (s.1.ck.t .B), s.1.ck.msg) :: rest ∧
    (∀ q ∈ rest, q.1 < max (s.1.ck.t .A) (s.1.ck.t .B)) ∧ (rest.map Prod.fst).Pairwise (· > ·)
  /-- The `PN` in transit is the number of messages logged in the previous epoch of the
  opener. -/
  msg : s.1.ck.msg.2 = if max (s.1.ck.t .A) (s.1.ck.t .B) ≤ 1 then 0
    else acdCnt s.2.log (max (s.1.ck.t .A) (s.1.ck.t .B) - 2)
  /-- Messages are logged at opened epochs. -/
  log_e : ∀ t ∈ s.2.log.map acdTag, t.1 ≤ max (s.1.ck.t .A) (s.1.ck.t .B)
  /-- The position of a logged message is that of its header. -/
  log_j : ∀ l ∈ s.2.log, l.j = l.hdr.2
  /-- The positions of an epoch are those below its count. -/
  log_pos : ∀ e j, (e, j) ∈ s.2.log.map acdTag ↔ j < acdCnt s.2.log e
  /-- Each epoch and position is logged at most once. -/
  log_nodup : (s.2.log.map acdTag).Nodup
  /-- A delivered message was received by its receiver. -/
  log_dl : ∀ l ∈ s.2.log, l.delivered = true → ∀ p, ckaSender l.e ≠ p → l.e ≤ s.1.ck.t p
  /-- The invariant of each party. -/
  party : ∀ p, ACDIDPartyInvAt G pubSOf qual s.2.log s.2.pubs (ckaShadow s.1.ck) p (s.1.ck.st p)

/-- The invariant of the game over the header-aware ACD construction `acdIDHdrSM` at the start
value `pub₀`, with the cuts `cut` of the closed receiving epochs whose skip check failed. -/
abbrev ACDIDHdrInv [Inhabited Msg] (G : PRGDef Sa (Kt × Sa)) (pub₀ : Msg → Msg)
    (cut : CKAParty → ℕ → Option ℕ)
    (s : SMSchemeSt (ACDIDSt Sc RK Sa Msg Kt) (Msg × ℕ) × SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct) :
    Prop :=
  ACDIDInvAt G (acdPubSAt pub₀) (acdQualAt cut) s

/-- The invariant of the game over the ACD construction with headers with decryption from the
log: `ACDIDInvAt` with `acdPubS` and `acdQual`. -/
abbrev ACDIDInv [Inhabited Msg] (G : PRGDef Sa (Kt × Sa))
    (s : SMSchemeSt (ACDIDSt Sc RK Sa Msg Kt) (Msg × ℕ) × SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct) :
    Prop :=
  ACDIDInvAt G acdPubS acdQual s

/-- The cuts after party `p` closes its receiving epoch `er` at the position `nr` with the result
`b` of the skip check: no cut of `er` when `b` holds, the cut `nr` otherwise. -/
def acdCutRecv (b : Bool) (cut : CKAParty → ℕ → Option ℕ) (p : CKAParty) (er nr : ℕ) :
    CKAParty → ℕ → Option ℕ :=
  Function.update cut p (Function.update (cut p) er (if b then none else some nr))

end View

/-! ## Lemmas on the bookkeeping -/

section BookLemmas

variable {W Hdr Ct Msg : Type}

/-- Consecutive epochs have different senders. -/
theorem ckaSender_succ_ne (n : ℕ) : ckaSender (n + 1) ≠ ckaSender n := by
  rw [ckaSender_succ]
  cases ckaSender n <;> simp

/-- Two parties different from a third one are equal. -/
theorem CKAParty.eq_of_ne_ne (a b c : CKAParty) (h1 : a ≠ b) (h2 : a ≠ c) : b = c := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- A party that does not send the epoch `n + 1` sends the epoch `n`. -/
theorem ckaSender_eq_of_ne {n : ℕ} {p : CKAParty} (h : ckaSender (n + 1) ≠ p) :
    ckaSender n = p := by
  rw [ckaSender_succ] at h
  cases hn : ckaSender n <;> cases p <;> simp_all

/-- An opened epoch of another number does not change the public value of the epoch `n`. -/
theorem acdPubAt_cons_ne [Inhabited Msg] (pubs : List (ℕ × (Msg × ℕ))) (a : ℕ × (Msg × ℕ))
    (n : ℕ) (h : a.1 ≠ n) : acdPubAt (a :: pubs) n = acdPubAt pubs n := by
  simp [acdPubAt, h]

/-- The public value of the latest opened epoch. -/
theorem acdPubAt_cons_self [Inhabited Msg] (pubs : List (ℕ × (Msg × ℕ))) (n : ℕ)
    (T : Msg × ℕ) : acdPubAt ((n, T) :: pubs) n = T := by
  simp [acdPubAt]

/-- The received epochs of a list of opened epochs with one more epoch. -/
theorem acdRPubs_cons (pubs : List (ℕ × (Msg × ℕ))) (a : ℕ × (Msg × ℕ)) (t : ℕ)
    (p : CKAParty) : acdRPubs (a :: pubs) t p =
      if 1 ≤ a.1 ∧ a.1 ≤ t ∧ ckaSender a.1 ≠ p then a :: acdRPubs pubs t p
      else acdRPubs pubs t p := by
  by_cases h : 1 ≤ a.1 ∧ a.1 ≤ t ∧ ckaSender a.1 ≠ p
  · simp [acdRPubs, h]
  · rw [ite_eq_right h]
    simp only [acdRPubs, List.filter_cons]
    rw [ite_eq_right (by simpa [and_assoc] using h)]

/-- The received epochs at a counter beyond every opened epoch. -/
theorem acdRPubs_congr (pubs : List (ℕ × (Msg × ℕ))) (n t : ℕ) (p : CKAParty)
    (h : ∀ q ∈ pubs, q.1 ≤ n) (ht : n ≤ t) : acdRPubs pubs t p = acdRPubs pubs n p := by
  unfold acdRPubs
  refine List.filter_congr fun q hq => ?_
  have := h q hq
  grind

/-- No message is logged at an epoch beyond every logged epoch. -/
theorem acdCnt_eq_zero (log : List (SMIDLogEntry W Hdr Ct)) (n e : ℕ)
    (h : ∀ t ∈ log.map acdTag, t.1 ≤ n) (hn : n < e) : acdCnt log e = 0 := by
  unfold acdCnt
  rw [List.countP_eq_zero]
  intro t ht
  have := h t ht
  simp only [beq_iff_eq]
  omega

/-- A delivered message of the epoch `e` is at a position before `acdNr`. -/
theorem acdNr_gt (log : List (SMIDLogEntry W Hdr Ct)) (e : ℕ) (l : SMIDLogEntry W Hdr Ct)
    (hl : l ∈ log) (hd : l.delivered = true) (he : l.e = e) : l.j < acdNr log e := by
  induction log with
  | nil => simp at hl
  | cons a t ih =>
    unfold acdNr at ih ⊢
    rw [List.filter_cons]
    rcases List.mem_cons.1 hl with rfl | hl
    · simp [hd, he]
    · have := ih hl
      split <;> (try simp only [List.map_cons, List.foldr_cons]) <;> omega

/-- `acdNr` is `0` or the position after a delivered message of the epoch. -/
theorem acdNr_cases (log : List (SMIDLogEntry W Hdr Ct)) (e : ℕ) :
    acdNr log e = 0 ∨ ∃ l ∈ log, l.delivered = true ∧ l.e = e ∧ acdNr log e = l.j + 1 := by
  induction log with
  | nil => simp [acdNr]
  | cons a t ih =>
    unfold acdNr at ih ⊢
    rw [List.filter_cons]
    split
    · rename_i ha
      simp only [Bool.and_eq_true, beq_iff_eq] at ha
      simp only [List.map_cons, List.foldr_cons]
      rcases ih with h0 | ⟨l, hl, hd, he, hn⟩
      · right; exact ⟨a, by simp, ha.1, ha.2, by omega⟩
      · right
        by_cases hlt : a.j + 1 ≤ l.j + 1
        · exact ⟨l, by simp [hl], hd, he, by omega⟩
        · exact ⟨a, by simp, ha.1, ha.2, by omega⟩
    · rcases ih with h0 | ⟨l, hl, hd, he, hn⟩
      · left; exact h0
      · right; exact ⟨l, by simp [hl], hd, he, hn⟩

/-- The number of logged messages of an epoch after one more message is logged. -/
theorem acdCnt_cons (l : SMIDLogEntry W Hdr Ct) (log : List (SMIDLogEntry W Hdr Ct)) (e : ℕ) :
    acdCnt (l :: log) e = acdCnt log e + if l.e = e then 1 else 0 := by
  simp only [acdCnt, List.map_cons, List.countP_cons, acdTag, beq_iff_eq]

/-- Logging an undelivered message keeps `acdNr`. -/
theorem acdNr_cons_of_undelivered (l : SMIDLogEntry W Hdr Ct) (log : List (SMIDLogEntry W Hdr Ct))
    (e : ℕ) (hd : l.delivered = false) : acdNr (l :: log) e = acdNr log e := by
  simp [acdNr, hd]

/-- When the positions of each epoch are those below its count, `acdNr` is at most the count. -/
theorem acdNr_le_cnt (log : List (SMIDLogEntry W Hdr Ct)) (e : ℕ)
    (hpos : ∀ e j, (e, j) ∈ log.map acdTag ↔ j < acdCnt log e) : acdNr log e ≤ acdCnt log e := by
  rcases acdNr_cases log e with h | ⟨l, hl, -, he, h⟩
  · omega
  · have := (hpos e l.j).1 (List.mem_map.2 ⟨l, hl, by simp [acdTag, he]⟩)
    omega

/-- In a list ordered by decreasing first components, the first element of a filtered list
satisfying `b` is the first element of the list satisfying `a`, when `a` and `r ∧ b` agree
except on elements of first component `0`. -/
theorem acd_find?_filter_eq {β : Type} (L : List (ℕ × β)) (a r b : ℕ × β → Bool)
    (hs : (L.map Prod.fst).Pairwise (· > ·)) (hrb : ∀ y, r y = true → b y = true → a y = true)
    (hab : ∀ y, a y = true → b y = true) (ha0 : ∀ y, a y = true → r y = false → y.1 = 0)
    (q : ℕ × β) (h : (L.filter r).find? b = some q) : L.find? a = some q := by
  induction L with
  | nil => simp at h
  | cons x L ih =>
    rw [List.map_cons, List.pairwise_cons] at hs
    rw [List.filter_cons] at h
    rw [List.find?_cons]
    cases hax : a x
    · apply ih hs.2
      split at h
      · rename_i hrx
        rw [List.find?_cons] at h
        cases hbx : b x
        · simpa [hbx] using h
        · exact absurd (hrb x hrx hbx) (by simp [hax])
      · exact h
    · cases hrx : r x
      · exfalso
        have hx0 := ha0 x hax hrx
        rw [ite_eq_right (by simp [hrx])] at h
        have hq := List.mem_of_find?_eq_some h
        have hqL := (List.mem_filter.1 hq).1
        have := hs.1 q.1 (List.mem_map_of_mem hqL)
        omega
      · rw [ite_eq_left hrx, List.find?_cons, hab x hax] at h
        exact h

/-- A store whose epochs and positions are exactly those of the log entries satisfying `qual`,
each once, has as many elements as there are such entries. -/
theorem acd_length_eq {Sa : Type} (log : List (SMIDLogEntry W Hdr Ct))
    (store : List (ℕ × ℕ × Sa)) (qual : SMIDLogEntry W Hdr Ct → Bool)
    (hnd : (log.map acdTag).Nodup) (hnd' : (store.map ACDIDSt.tag).Nodup)
    (hsd : ∀ el ∈ store, ∃ l ∈ log, qual l = true ∧ acdTag l = ACDIDSt.tag el)
    (hcp : ∀ l ∈ log, qual l = true → acdTag l ∈ store.map ACDIDSt.tag) :
    store.length = (log.filter qual).length := by
  have hnd2 : ((log.filter qual).map acdTag).Nodup :=
    hnd.sublist (List.filter_sublist.map _)
  have hperm : (store.map ACDIDSt.tag).Perm ((log.filter qual).map acdTag) := by
    refine (List.perm_ext_iff_of_nodup hnd' hnd2).2 fun t => ⟨fun ht => ?_, fun ht => ?_⟩
    · obtain ⟨el, hel, rfl⟩ := List.mem_map.1 ht
      obtain ⟨l, hl, hq, he⟩ := hsd el hel
      exact List.mem_map.2 ⟨l, List.mem_filter.2 ⟨hl, hq⟩, he⟩
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 ht
      obtain ⟨hl, hq⟩ := List.mem_filter.1 hl
      exact hcp l hl hq
  simpa using hperm.length_eq

/-- `acdNr` of a log with one more entry. -/
theorem acdNr_cons (l : SMIDLogEntry W Hdr Ct) (log : List (SMIDLogEntry W Hdr Ct)) (e : ℕ) :
    acdNr (l :: log) e =
      if l.delivered = true ∧ l.e = e then max (l.j + 1) (acdNr log e) else acdNr log e := by
  by_cases h : l.delivered = true ∧ l.e = e
  · simp [acdNr, h]
  · rw [ite_eq_right h]
    simp only [acdNr, List.filter_cons]
    rw [ite_eq_right (by simpa using h)]

/-- The position after the delivered messages of an epoch, after one message at the epoch `e`
and the position `j` is delivered. -/
theorem acdNr_map_deliver (L : List (SMIDLogEntry W Hdr Ct)) (P : SMIDLogEntry W Hdr Ct → Bool)
    (e j : ℕ) (hP : ∀ l ∈ L, P l = true → l.e = e ∧ l.j = j) (e' : ℕ) :
    acdNr (L.map fun l => if P l then { l with delivered := true } else l) e' =
      if e' = e ∧ L.any P then max (acdNr L e') (j + 1) else acdNr L e' := by
  induction L with
  | nil => simp [acdNr]
  | cons a L ih =>
    have ih := ih (fun l hl => hP l (List.mem_cons_of_mem _ hl))
    rw [List.map_cons, acdNr_cons, acdNr_cons, ih]
    have ha := hP a List.mem_cons_self
    cases hPa : P a
    · simp only [Bool.false_eq_true, ↓reduceIte, List.any_cons]
      grind
    · grind

/-- `acdQual` as a proposition. -/
theorem acdQual_iff (p : CKAParty) (er nr : ℕ) (l : SMIDLogEntry W Hdr Ct) :
    acdQual p er nr l = true ↔ l.delivered = false ∧ ckaSender l.e ≠ p ∧ 1 ≤ l.e ∧
      (l.e < er ∨ (l.e = er ∧ l.j < nr)) := by
  simp [acdQual, and_assoc]

/-- `acdQualAt` as `acdQual` and the cut of an epoch before `er`. -/
theorem acdQualAt_iff (cut : CKAParty → ℕ → Option ℕ) (p : CKAParty) (er nr : ℕ)
    (l : SMIDLogEntry W Hdr Ct) : acdQualAt cut p er nr l = true ↔ acdQual p er nr l = true ∧
      (l.e < er → (cut p l.e).all (fun n => decide (l.j < n)) = true) := by
  simp only [acdQualAt, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1 | h1, h2⟩ <;> refine ⟨h2, fun h => ?_⟩
    · exact h1
    · omega
  · rintro ⟨h2, h1⟩
    refine ⟨?_, h2⟩
    by_cases h : l.e < er
    · exact Or.inl (h1 h)
    · exact Or.inr (by omega)

/-- A logged message of `acdQualAt` satisfies `acdQual`. -/
theorem acdQual_of_acdQualAt {cut : CKAParty → ℕ → Option ℕ} {p : CKAParty} {er nr : ℕ}
    {l : SMIDLogEntry W Hdr Ct} (h : acdQualAt cut p er nr l = true) :
    acdQual p er nr l = true :=
  ((acdQualAt_iff cut p er nr l).1 h).1

/-- A passed skip check leaves empty cuts empty. -/
theorem acdCutRecv_none (b : Bool) (cut : CKAParty → ℕ → Option ℕ) (p : CKAParty) (er nr : ℕ)
    (hb : b = true) (hc : ∀ q e, cut q e = none) (q : CKAParty) (e : ℕ) :
    acdCutRecv b cut p er nr q e = none := by
  subst hb
  unfold acdCutRecv
  by_cases hq : q = p
  · subst hq
    by_cases he : e = er
    · subst he
      simp
    · simp [Function.update_of_ne he, hc]
  · simp [Function.update_of_ne hq, hc]

/-- A logged message stored by `p` at the receiving epoch `er` and the position `nr` stays stored
after `p` closes `er` and moves to a later epoch `er'` at the position `0`. -/
theorem acdQualAt_cutRecv_old (b : Bool) (cut : CKAParty → ℕ → Option ℕ) (p : CKAParty)
    (er nr er' : ℕ) (l : SMIDLogEntry W Hdr Ct) (h : acdQualAt cut p er nr l = true)
    (he : er < er') : acdQualAt (acdCutRecv b cut p er nr) p er' 0 l = true := by
  rw [acdQualAt_iff] at h ⊢
  obtain ⟨hq, hc⟩ := h
  have hq' := (acdQual_iff _ _ _ _).1 hq
  refine ⟨(acdQual_iff _ _ _ _).2 ⟨hq'.1, hq'.2.1, hq'.2.2.1, Or.inl (by omega)⟩, fun _ => ?_⟩
  unfold acdCutRecv
  rw [Function.update_self]
  by_cases hle : l.e = er
  · rw [hle, Function.update_self]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, Option.all_some, decide_eq_true_eq]
      omega
    · rfl
  · rw [Function.update_of_ne hle]
    exact hc (by omega)

/-- A logged message stored by `p` after it closes its receiving epoch `er` at the position `nr`,
of an epoch up to `er`, was stored before, or is of the epoch `er` at a position from `nr` and
the skip check `b` held. -/
theorem acdQualAt_cutRecv_new (b : Bool) (cut : CKAParty → ℕ → Option ℕ) (p : CKAParty)
    (er nr er' : ℕ) (l : SMIDLogEntry W Hdr Ct)
    (h : acdQualAt (acdCutRecv b cut p er nr) p er' 0 l = true) (hle : l.e ≤ er) :
    acdQualAt cut p er nr l = true ∨ (l.e = er ∧ nr ≤ l.j ∧ b = true) := by
  rw [acdQualAt_iff] at h
  obtain ⟨hq, hc⟩ := h
  have hq' := (acdQual_iff _ _ _ _).1 hq
  have hlt : l.e < er' := by omega
  have hc' := hc hlt
  unfold acdCutRecv at hc'
  rw [Function.update_self] at hc'
  by_cases h1 : l.e < er
  · left
    rw [Function.update_of_ne (by omega)] at hc'
    exact (acdQualAt_iff _ _ _ _ _).2
      ⟨(acdQual_iff _ _ _ _).2 ⟨hq'.1, hq'.2.1, hq'.2.2.1, Or.inl h1⟩, fun _ => hc'⟩
  · by_cases h2 : l.j < nr
    · left
      exact (acdQualAt_iff _ _ _ _ _).2
        ⟨(acdQual_iff _ _ _ _).2 ⟨hq'.1, hq'.2.1, hq'.2.2.1, Or.inr ⟨by omega, h2⟩⟩,
          fun h => absurd h h1⟩
    · right
      have he : l.e = er := by omega
      rw [he, Function.update_self] at hc'
      refine ⟨he, by omega, ?_⟩
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte, Option.all_some, decide_eq_true_eq] at hc'
        omega
      · rfl

/-- The elements of `skipKeys`. -/
theorem ACDIDSt.mem_skipKeys {Sa Kt : Type} (G : PRGDef Sa (Kt × Sa)) (e : ℕ) (sa : Sa)
    (a n : ℕ) (el : ℕ × ℕ × Kt) : el ∈ ACDIDSt.skipKeys G e sa a n ↔
      ∃ i, a ≤ i ∧ i < a + n ∧ el = (e, i, chainKey G sa i) := by
  simp only [ACDIDSt.skipKeys, List.mem_map, List.mem_range'_1]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi.1, hi.2, rfl⟩
  · rintro ⟨i, h1, h2, rfl⟩; exact ⟨i, ⟨h1, h2⟩, rfl⟩

/-- Skipped keys of positions from `a` added to a store whose keys of the epoch `e` are at
positions below `a` give distinct epochs and positions. -/
theorem ACDIDSt.skipKeys_append_nodup {Sa Kt : Type} (G : PRGDef Sa (Kt × Sa)) (e : ℕ)
    (sa : Sa) (a n : ℕ) (store : List (ℕ × ℕ × Kt)) (hnd : (store.map ACDIDSt.tag).Nodup)
    (hdisj : ∀ el ∈ store, el.1 = e → el.2.1 < a) :
    ((ACDIDSt.skipKeys G e sa a n ++ store).map ACDIDSt.tag).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨?_, hnd, ?_⟩
  · simp only [ACDIDSt.skipKeys, List.map_map]
    refine List.Nodup.map (fun i j hij => ?_) List.nodup_range'
    simpa [ACDIDSt.tag] using hij
  · intro t ht t' ht'
    simp only [List.mem_map] at ht ht'
    obtain ⟨el, hel, rfl⟩ := ht
    obtain ⟨el', hel', rfl⟩ := ht'
    obtain ⟨i, hi1, -, rfl⟩ := (ACDIDSt.mem_skipKeys G e sa a n el).1 hel
    intro h
    simp only [ACDIDSt.tag, Prod.mk.injEq] at h
    have := hdisj el' hel' h.1.symm
    omega

end BookLemmas

/-! ## The construction over the base scheme -/

section Over

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [Fintype RK] [Nonempty RK] [Inhabited Msg] [DecidableEq Msg]
  [DecidableEq W] [DecidableEq Ct] {Kt : Type} [SampleableType Kt]

omit [SampleableType Kt] [SampleableType W] [Fintype RK] [Nonempty RK] [Inhabited Msg]
  [DecidableEq W] in
/-- The key lookup keeps the state of the ACD construction. -/
theorem acdIDRKey_base (G : PRGDef Sa (Kt × Sa)) (maxSkip maxStored : ℕ)
    (x : ACDIDSt Sc RK Sa Msg Kt) (h : ACDHdr Msg) (y : ACDIDSt Sc RK Sa Msg Kt × Kt)
    (hy : acdIDRKey G maxSkip maxStored x h = some y) : y.1.base = x.base := by
  unfold acdIDRKey at hy
  split at hy
  · simp at hy
  · split_ifs at hy
    · obtain ⟨sa, -, rfl⟩ := Option.map_eq_some_iff.1 hy
      rfl
    · obtain ⟨el, -, rfl⟩ := Option.map_eq_some_iff.1 hy
      rfl

variable (C : CKADef Sc Msg Key) [CKACoins C Rand] (R : PRGDef (RK × Key) (RK × Sa))
  (G : PRGDef Sa (Kt × Sa)) {AD : Type} (DH : AEADDef W Ct AD Kt) (hdrAD : W → ACDHdr Msg → AD)
  (pub₀ : Msg → Msg) (pnOk : ACDIDSt Sc RK Sa Msg Kt → ℕ → Bool) (cut : CKAParty → ℕ → Option ℕ)
  (D : AEADDef W Ct (W × ACDHdr Msg) Kt) (dec : W → W × ACDHdr Msg)
  (enc : ACDHdr Msg → W → W) (maxSkip maxStored : ℕ)

omit [SampleableType Kt] [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct]
  [Fintype RK][Nonempty RK] [Inhabited Msg] [DecidableEq Msg] [DecidableEq W] [DecidableEq Ct] in
/-- The opened epochs are listed in decreasing order. -/
theorem ACDIDInvAt.pubs_sorted {G : PRGDef Sa (Kt × Sa)}
    {pubSOf : List (ℕ × (Msg × ℕ)) → ℕ → CKAParty → Msg × ℕ}
    {qual : CKAParty → ℕ → ℕ → SMIDLogEntry W (ACDHdr Msg) Ct → Bool}
    {s : SMSchemeSt (ACDIDSt Sc RK Sa Msg Kt) (Msg × ℕ) × SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct}
    (hs : ACDIDInvAt G pubSOf qual s) : (s.2.pubs.map Prod.fst).Pairwise (· > ·) := by
  obtain ⟨rest, hrest, hlt, hsort⟩ := hs.pubs
  rw [hrest, List.map_cons, List.pairwise_cons]
  exact ⟨fun a ha => by obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ha; exact hlt q hq, hsort⟩

omit [SampleableType Kt] [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct]
  [Fintype RK][Nonempty RK] [DecidableEq Msg] [DecidableEq W] [DecidableEq Ct] in
/-- The opened epochs are listed in decreasing order. -/
theorem ACDIDInv.pubs_sorted {G : PRGDef Sa (Kt × Sa)}
    {s : SMSchemeSt (ACDIDSt Sc RK Sa Msg Kt) (Msg × ℕ) × SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct}
    (hs : ACDIDInv G s) : (s.2.pubs.map Prod.fst).Pairwise (· > ·) :=
  ACDIDInvAt.pubs_sorted hs

omit [SampleableType Kt] [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct]
  [Fintype RK][Nonempty RK] [Inhabited Msg] [DecidableEq Msg] [DecidableEq W] [DecidableEq Ct] in
/-- The invariant of a party with the stored log entries selected by `qual'`, from the
invariant with `qual` when the two agree at the party. -/
theorem ACDIDPartyInvAt.congr_qual {G : PRGDef Sa (Kt × Sa)}
    {pubSOf : List (ℕ × (Msg × ℕ)) → ℕ → CKAParty → Msg × ℕ}
    {qual qual' : CKAParty → ℕ → ℕ → SMIDLogEntry W (ACDHdr Msg) Ct → Bool}
    {log : List (SMIDLogEntry W (ACDHdr Msg) Ct)} {pubs : List (ℕ × (Msg × ℕ))}
    {sh : CKAGameSt Unit Unit} {p : CKAParty} {x : ACDIDSt Sc RK Sa Msg Kt}
    (h : ACDIDPartyInvAt G pubSOf qual log pubs sh p x) (hq : qual p = qual' p) :
    ACDIDPartyInvAt G pubSOf qual' log pubs sh p x := by
  obtain ⟨a, b, c, d, e, f, g, i, j, k⟩ := h
  rw [hq] at j k
  exact ⟨a, b, c, d, e, f, g, i, j, k⟩

omit [SampleableType Kt] [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct]
  [Fintype RK][Nonempty RK] [Inhabited Msg] [DecidableEq W] [DecidableEq Ct] in
/-- The epoch the scheme resolves a public value to is the epoch of the game. -/
theorem acdRPubs_find_epochOf (x : SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)
    (sh : CKAGameSt Unit Unit) (p : CKAParty) (T : Msg × ℕ)
    (hs : (x.pubs.map Prod.fst).Pairwise (· > ·)) (q : ℕ × (Msg × ℕ))
    (h : (acdRPubs x.pubs (sh.t p) p).find? (fun q => decide (q.2 = T)) = some q) :
    x.epochOf sh p T = some q.1 ∧ q.2 = T ∧ 1 ≤ q.1 ∧ q.1 ≤ sh.t p ∧ ckaSender q.1 ≠ p := by
  have hq := List.mem_of_find?_eq_some h
  have hqT := List.find?_some h
  obtain ⟨-, hqr⟩ := List.mem_filter.1 hq
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hqr hqT
  have hf := acd_find?_filter_eq x.pubs
    (fun q => decide (q.2 = T) && decide (q.1 ≤ sh.t p) && (ckaSender q.1 != p))
    (fun q => decide (1 ≤ q.1) && decide (q.1 ≤ sh.t p) && ckaSender q.1 != p)
    (fun q => decide (q.2 = T)) hs (by intro y; simp; tauto) (by intro y; simp; tauto)
    (by intro y; simp; grind) q h
  refine ⟨?_, hqT, hqr.1.1, hqr.1.2, hqr.2⟩
  simp only [SMIDAux.epochOf, hf, Option.map_some]

omit [SampleableType Kt] [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct]
  [Fintype RK][Nonempty RK] [Inhabited Msg] in
/-- An entry found in the log. -/
theorem acd_findEntry_some (x : SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct) (e : ℕ) (h : ACDHdr Msg)
    (ad : W) (c : Ct) (l : SMIDLogEntry W (ACDHdr Msg) Ct) (hl : x.findEntry e h ad c = some l) :
    l ∈ x.log ∧ l.delivered = false ∧ l.e = e ∧ l.hdr = h ∧ l.ad = ad ∧ l.ct = c := by
  refine ⟨List.mem_of_find?_eq_some hl, ?_⟩
  have := List.find?_some hl
  simp only [SMIDLogEntry.isMatch, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
    decide_eq_true_eq] at this
  tauto

/-- An epoch up to the counter of `p` that `p` does not send is at most its receiving epoch. -/
theorem acd_le_smRecvEpoch (sh : CKAGameSt Unit Unit) (p : CKAParty) (n : ℕ)
    (h1 : n ≤ sh.t p) (h2 : ckaSender n ≠ p) : n ≤ smRecvEpoch sh p := by
  unfold smRecvEpoch
  split_ifs with h
  · have : n ≠ sh.t p := fun hn => h2 (hn ▸ h)
    omega
  · exact h1

omit [SampleableType Kt] [SampleableType W] [SampleableType Ct] [Fintype RK] [Nonempty RK]
  [DecidableEq Msg] [DecidableEq W] [DecidableEq Ct] in
/-- The invariant of the header-aware construction holds at its initial states, with any cuts. -/
theorem acdIDHdr_inv_init (i : Msg × SMPartySt Sc RK Sa × SMPartySt Sc RK Sa) :
    ACDIDHdrInv G pub₀ cut (SMSchemeSt.init ((i.1, 0),
        (⟨i.2.1, (pub₀ i.1, 0), 0, 0, 0, 0, [], []⟩ : ACDIDSt Sc RK Sa Msg Kt),
        (⟨i.2.2, (pub₀ i.1, 0), 0, 0, 0, 0, [], []⟩ : ACDIDSt Sc RK Sa Msg Kt)),
      (SMIDAux.init (i.1, 0) : SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)) := by
  refine ⟨?_, ?_, ⟨[], ?_, ?_, List.Pairwise.nil⟩, ?_, ?_, ?_, ?_, ?_, ?_, fun p => ?_⟩ <;>
    first
    | (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> cases p <;>
        simp [SMSchemeSt.init, CKAGameSt.init, SMIDAux.init, ckaShadow, smRecvEpoch, acdPubSAt,
          acdPubAt, acdNs, acdCnt, acdNr, acdRPubs, ckaSender])
    | simp [SMSchemeSt.init, CKAGameSt.init, SMIDAux.init, acdCnt]

omit [SampleableType Kt] [SampleableType W] [SampleableType Ct] [Fintype RK] [Nonempty RK]
  [Inhabited Msg] [DecidableEq Msg] [DecidableEq W] [DecidableEq Ct] in
/-- The invariant depends on the bookkeeping through the log and the opened epochs only. -/
theorem acdIDInvAt_aux {pubSOf : List (ℕ × (Msg × ℕ)) → ℕ → CKAParty → Msg × ℕ}
    {qual : CKAParty → ℕ → ℕ → SMIDLogEntry W (ACDHdr Msg) Ct → Bool}
    (s : SMSchemeSt (ACDIDSt Sc RK Sa Msg Kt) (Msg × ℕ) × SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)
    (x : SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct) (hs : ACDIDInvAt G pubSOf qual s)
    (hl : x.log = s.2.log) (hp : x.pubs = s.2.pubs) : ACDIDInvAt G pubSOf qual (s.1, x) := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := hs
  rw [← hl, ← hp] at *
  exact ⟨a, b, c, d, e, f, g, h, i, j⟩

omit [SampleableType Kt] [Fintype Rand] [Nonempty Rand] [DecidableEq W] [DecidableEq Ct] in
/-- Opening an epoch keeps the invariant of the header-aware construction. -/
theorem acdIDHdr_inv_ratchet
    (s : SMSchemeSt (ACDIDSt Sc RK Sa Msg Kt) (Msg × ℕ) × SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)
    (hs : ACDIDHdrInv G pub₀ cut s) (p : CKAParty) (hc : s.1.ck.canSend p = true) (r : Rand) :
    ACDIDHdrInv G pub₀ cut
      (⟨s.1.ck.sent p
          ((acdIDHdrSM C R G DH hdrAD pub₀ pnOk maxSkip maxStored).ratchet (s.1.ck.st p) r).1
          ((acdIDHdrSM C R G DH hdrAD pub₀ pnOk maxSkip maxStored).ratchet (s.1.ck.st p) r).2,
        s.1.done⟩,
      { s.2 with pubs := (s.1.ck.t p + 1,
        ((acdIDHdrSM C R G DH hdrAD pub₀ pnOk maxSkip maxStored).ratchet (s.1.ck.st p) r).2) ::
          s.2.pubs }) := by
  obtain ⟨s1, x⟩ := s
  obtain ⟨hle, hah, ⟨rest, hrest, hlt, hsort⟩, hmsg, hle_e, hj, hpos, hnd, hdl, hpty⟩ := hs
  dsimp only at *
  set y := (acdIDHdrSM C R G DH hdrAD pub₀ pnOk maxSkip maxStored).ratchet (s1.ck.st p) r with hy
  have hcs : s1.ck.t .A = s1.ck.t .B ∧ ckaSender (s1.ck.t .A + 1) = p := by
    simpa [CKAGameSt.canSend] using hc
  obtain ⟨heq, hsend⟩ := hcs
  have htp : s1.ck.t p = s1.ck.t .A := by cases p <;> simp [heq]
  have htop : max (s1.ck.t .A) (s1.ck.t .B) = s1.ck.t .A := by simp [heq]
  have ht' : ∀ p', (s1.ck.sent p y.1 y.2).t p' = if p' = p then s1.ck.t .A + 1 else s1.ck.t .A := by
    intro p'
    by_cases hp : p' = p
    · subst hp; simp [CKAGameSt.sent, htp]
    · rw [ite_eq_right hp]
      simp only [CKAGameSt.sent, Function.update_of_ne hp]
      cases p' <;> simp [heq]
  have htop' : max ((s1.ck.sent p y.1 y.2).t .A) ((s1.ck.sent p y.1 y.2).t .B) =
      s1.ck.t .A + 1 := by
    rw [ht', ht']; cases p <;> simp
  have hsn : ckaSender (s1.ck.t .A) ≠ p := by
    rw [← hsend]; exact (ckaSender_succ_ne _).symm
  have hpubs_le : ∀ q ∈ x.pubs, q.1 ≤ s1.ck.t .A := by
    intro q hq
    rw [hrest] at hq
    rcases List.mem_cons.1 hq with rfl | hq
    · simp [htop]
    · have := hlt q hq; omega
  refine ⟨?_, ?_, ⟨x.pubs, ?_, ?_, ?_⟩, ?_, ?_, hj, hpos, hnd, ?_, fun p' => ?_⟩ <;>
    try dsimp only
  · rw [ht', ht']; cases p <;> simp <;> omega
  · intro q hq
    simp only [ht'] at hq ⊢
    cases p <;> cases q <;>
      simp only [CKAParty.other_A, CKAParty.other_B, reduceCtorEq, ↓reduceIte] at hq ⊢ <;>
      omega
  · rw [htop']; simp [CKAGameSt.sent, htp]
  · intro q hq; have := hpubs_le q hq; omega
  · rw [hrest, List.map_cons, List.pairwise_cons]
    exact ⟨fun a ha => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ha; have := hlt q hq; omega, hsort⟩
  · rw [htop']
    simp only [CKAGameSt.sent, hy, acdIDHdrSM]
    rw [(hpty p).ns]
    simp only [acdNs, ckaShadow_t, htp, ite_eq_right hsn]
    rcases Nat.eq_zero_or_pos (s1.ck.t .A) with h0 | h0
    · simp [h0]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      congr 1
  · intro t ht; have := hle_e t ht; omega
  · intro l hl hd q hq
    have := hdl l hl hd q hq
    have htq : s1.ck.t q = s1.ck.t .A := by cases q <;> simp [heq]
    rw [ht']; split <;> omega
  · obtain ⟨hep, her, hpS, hns, hnr, hrp, hrcv, hnd', hsd, hcp⟩ := hpty p'
    simp only [ckaShadow_t] at hep her hpS hns hrp
    have hsh : ∀ q, smRecvEpoch (ckaShadow (s1.ck.sent p y.1 y.2)) q =
        if ckaSender ((s1.ck.sent p y.1 y.2).t q) = q then (s1.ck.sent p y.1 y.2).t q - 1
        else (s1.ck.sent p y.1 y.2).t q := fun q => rfl
    have hsh0 : smRecvEpoch (ckaShadow s1.ck) p' =
        if ckaSender (s1.ck.t p') = p' then s1.ck.t p' - 1 else s1.ck.t p' := rfl
    by_cases hp : p' = p
    · subst hp
      have hst : (s1.ck.sent p' y.1 y.2).st p' = y.1 := by simp [CKAGameSt.sent]
      set B := acdIDHdrBase C R G DH hdrAD ((s1.ck.st p').pubS, (s1.ck.st p').ns) with hB
      have hy1 : y.1 = ⟨(B.ratchet (s1.ck.st p').base r).1,
          ((B.ratchet (s1.ck.st p').base r).2, (s1.ck.st p').ns), 0,
          (s1.ck.st p').ep + 1, (s1.ck.st p').er, (s1.ck.st p').nr, (s1.ck.st p').rpubs,
          (s1.ck.st p').store⟩ := rfl
      have hy2 : y.2 = ((B.ratchet (s1.ck.st p').base r).2, (s1.ck.st p').ns) := rfl
      have hrcv' : (B.ratchet (s1.ck.st p').base r).1.rcv = (s1.ck.st p').base.rcv := by
        simp [hB, acdIDHdrBase, acdSMAD]
      have hsheq : ckaShadow (s1.ck.sent p' y.1 y.2) =
          ⟨fun _ => (), Function.update s1.ck.t p' (s1.ck.t p' + 1), ()⟩ := rfl
      have hT1 : Function.update s1.ck.t p' (s1.ck.t p' + 1) p' = s1.ck.t .A + 1 := by
        simp [htp]
      have hsr : smRecvEpoch (⟨fun _ => (), Function.update s1.ck.t p' (s1.ck.t p' + 1), ()⟩ :
          CKAGameSt Unit Unit) p' = s1.ck.t .A := by
        simp only [smRecvEpoch, hT1, hsend]; simp
      rw [hst, hsheq, hy1]
      refine ⟨?_, ?_, ?_, ?_, hnr, ?_, ?_, hnd', ?_, hcp⟩ <;> dsimp only <;>
        try simp only [hT1, hsr]
      · rw [hep, htp]
      · rw [her, hsh0, htp, ite_eq_right hsn]
      · rw [acdPubSAt, ite_eq_left hsend, ite_eq_right (by omega), htp, acdPubAt_cons_self, hy2]
      · rw [acdNs, ite_eq_left hsend]
        exact (acdCnt_eq_zero x.log _ _ (fun t ht => (hle_e t ht).trans htop.le)
          (Nat.lt_succ_self _)).symm
      · rw [acdRPubs_cons, ite_eq_right (by simp [htp, hsend]),
          acdRPubs_congr x.pubs (s1.ck.t .A) _ _ hpubs_le (by omega), hrp, htp]
      · rw [hrcv']; exact hrcv
      · rw [hrcv']; exact hsd
    · have hst : (s1.ck.sent p y.1 y.2).st p' = s1.ck.st p' := by
        simp [CKAGameSt.sent, Function.update_of_ne hp]
      have htp' : (s1.ck.sent p y.1 y.2).t p' = s1.ck.t p' := by
        rw [ht', ite_eq_right hp]; cases p' <;> simp [heq]
      have htq : s1.ck.t p' = s1.ck.t .A := by cases p' <;> simp [heq]
      rw [hst]
      refine ⟨?_, ?_, ?_, hns.trans ?_, hnr, ?_, hrcv, hnd', hsd, hcp⟩
      · rw [hep, ckaShadow_t, htp']
      · rw [her, hsh, hsh0, htp']
      · rw [hpS, ckaShadow_t, htp']
        unfold acdPubSAt
        split_ifs <;> first | rfl | (rw [acdPubAt_cons_ne]; simp only [htp]; omega)
      · rw [ckaShadow_t, htp']
      · rw [hrp, ckaShadow_t, htp', acdRPubs_cons, ite_eq_right (by simp [htp]; omega)]

omit [SampleableType Kt] [Fintype Rand] [Nonempty Rand] [DecidableEq W] [DecidableEq Ct] in
/-- Receiving keeps the invariant of the header-aware construction, with the receiving epoch of
the receiver cut at its position when the skip check fails (`acdCutRecv`). -/
theorem acdIDHdr_inv_recv
    (s : SMSchemeSt (ACDIDSt Sc RK Sa Msg Kt) (Msg × ℕ) × SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)
    (hs : ACDIDHdrInv G pub₀ cut s) (p : CKAParty) (hc : s.1.ck.canRecv p = true) :
    ACDIDHdrInv G pub₀
      (acdCutRecv (pnOk (s.1.ck.st p) s.1.ck.msg.2) cut p (s.1.ck.st p).er (s.1.ck.st p).nr)
      (⟨s.1.ck.recvd p ((acdIDHdrSM C R G DH hdrAD pub₀ pnOk maxSkip maxStored).recv
        (s.1.ck.st p) s.1.ck.msg), s.1.done⟩, s.2) := by
  obtain ⟨s1, x⟩ := s
  obtain ⟨hle, hah, ⟨rest, hrest, hlt, hsort⟩, hmsg, hle_e, hj, hpos, hnd, hdl, hpty⟩ := hs
  dsimp only at *
  set x' := (acdIDHdrSM C R G DH hdrAD pub₀ pnOk maxSkip maxStored).recv (s1.ck.st p)
    s1.ck.msg with hx'
  have hcr : s1.ck.t p + 1 = s1.ck.t p.other := by simpa [CKAGameSt.canRecv] using hc
  have hsq : ckaSender (s1.ck.t p + 1) = p.other := by rw [hcr]; exact hah p hcr.symm
  have hsq' : ckaSender (s1.ck.t p + 1) ≠ p := by rw [hsq]; cases p <;> simp
  have hsp : ckaSender (s1.ck.t p) = p := ckaSender_eq_of_ne hsq'
  have htop : max (s1.ck.t .A) (s1.ck.t .B) = s1.ck.t p + 1 := by
    cases p <;> simp at hcr <;> omega
  have hsheq : ckaShadow (s1.ck.recvd p x') =
      ⟨fun _ => (), Function.update s1.ck.t p (s1.ck.t p + 1), ()⟩ := rfl
  have ht' : ∀ q, (s1.ck.recvd p x').t q = s1.ck.t p + 1 := by
    intro q
    by_cases hq : q = p
    · subst hq; simp [CKAGameSt.recvd]
    · have : q = p.other := by cases p <;> cases q <;> simp_all
      subst this
      simp [CKAGameSt.recvd, hcr]
  have htop' : max ((s1.ck.recvd p x').t .A) ((s1.ck.recvd p x').t .B) = s1.ck.t p + 1 := by
    rw [ht', ht']; simp
  refine ⟨?_, ?_, ⟨rest, ?_, ?_, hsort⟩, ?_, ?_, hj, hpos, hnd, ?_, fun p' => ?_⟩ <;> dsimp only
  · rw [ht', ht']; omega
  · intro q hq; rw [ht', ht'] at hq; omega
  · rw [htop', hrest, htop]; rfl
  · rw [htop', ← htop]; exact hlt
  · rw [htop', ← htop]; exact hmsg
  · rw [htop', ← htop]; exact hle_e
  · intro l hl hd q hq
    have := hdl l hl hd q hq
    rw [ht']
    have : s1.ck.t q ≤ s1.ck.t p + 1 := by cases p <;> cases q <;> simp at hcr ⊢ <;> omega
    omega
  · obtain ⟨hep, her, hpS, hns, hnr, hrp, hrcv, hnd', hsd, hcp⟩ := hpty p'
    simp only [ckaShadow_t] at hep her hpS hns hrp
    have hsh0 : smRecvEpoch (ckaShadow s1.ck) p' =
        if ckaSender (s1.ck.t p') = p' then s1.ck.t p' - 1 else s1.ck.t p' := rfl
    rw [hsheq]
    by_cases hp : p' = p
    · subst hp
      have hst : (s1.ck.recvd p' x').st p' = x' := by simp [CKAGameSt.recvd]
      have hT1 : Function.update s1.ck.t p' (s1.ck.t p' + 1) p' = s1.ck.t p' + 1 := by simp
      have hsr : smRecvEpoch (⟨fun _ => (), Function.update s1.ck.t p' (s1.ck.t p' + 1), ()⟩ :
          CKAGameSt Unit Unit) p' = s1.ck.t p' + 1 := by
        simp only [smRecvEpoch, hT1, ite_eq_right hsq']
      have her0 : (s1.ck.st p').er = s1.ck.t p' - 1 := by rw [her, hsh0, ite_eq_left hsp]
      rw [hst, hx']
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only [acdIDHdrSM] <;>
        try simp only [hT1, hsr]
      · rw [hep]
      · rw [hep]
      · rw [hpS]; unfold acdPubSAt; rw [ite_eq_right hsq', ite_eq_left hsp]
        by_cases h0 : s1.ck.t p' = 0 <;> simp [h0]
      · rw [hns]; unfold acdNs; rw [ite_eq_right hsq', ite_eq_left hsp]; simp
      · rw [hep]
        rcases acdNr_cases x.log (s1.ck.t p' + 1) with h | ⟨l, hl, hd, he, -⟩
        · exact h.symm
        · exfalso
          have := hdl l hl hd p' (by rw [he]; exact hsq')
          omega
      · rw [hrp, hep, hrest, htop]
        simp only [acdRPubs_cons]
        rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, le_rfl, hsq'⟩,
          acdRPubs_congr rest (s1.ck.t p')
          (s1.ck.t p' + 1) p' (fun q hq => by have := hlt q hq; omega) (by omega)]
      · intro _; simp [acdIDHdrBase, acdSMAD]
      · by_cases h0 : (s1.ck.st p').er = 0
        · rw [ite_eq_left h0, List.nil_append]; exact hnd'
        · rw [ite_eq_right h0]
          cases pnOk (s1.ck.st p') s1.ck.msg.2
          · simpa only [Bool.cond_false, List.nil_append] using hnd'
          obtain ⟨sa, hsa⟩ := Option.isSome_iff_exists.1 (hrcv (by omega))
          rw [Bool.cond_true, hsa, Option.map_some, Option.getD_some]
          refine ACDIDSt.skipKeys_append_nodup G _ sa _ _ _ hnd' fun el hel he => ?_
          obtain ⟨⟨l, -, hq, ht⟩, -⟩ := hsd el hel
          simp only [acdTag, ACDIDSt.tag, Prod.mk.injEq] at ht
          have hq := (acdQual_iff _ _ _ _).1 (acdQual_of_acdQualAt hq)
          omega
      · intro el hel
        rw [List.mem_append] at hel
        rcases hel with hel | hel
        · by_cases h0 : (s1.ck.st p').er = 0
          · simp [h0] at hel
          rw [ite_eq_right h0] at hel
          cases hb : pnOk (s1.ck.st p') s1.ck.msg.2
          · simp [hb] at hel
          obtain ⟨sa, hsa⟩ := Option.isSome_iff_exists.1 (hrcv (by omega))
          rw [hb, Bool.cond_true, hsa, Option.map_some, Option.getD_some] at hel
          obtain ⟨i, hi1, hi2, rfl⟩ := (ACDIDSt.mem_skipKeys G _ sa _ _ el).1 hel
          have hPN : s1.ck.msg.2 = acdCnt x.log (s1.ck.st p').er := by
            rw [hmsg, htop, ite_eq_right (by omega), her0]; congr 1
          have hi : i < acdCnt x.log (s1.ck.st p').er := by omega
          obtain ⟨l, hl, ht⟩ := List.mem_map.1 ((hpos _ i).2 hi)
          simp only [acdTag, Prod.mk.injEq] at ht
          refine ⟨⟨l, hl, ?_, by simp [acdTag, ACDIDSt.tag, ht.1, ht.2]⟩, fun he => ?_⟩
          · rw [acdQualAt_iff, acdQual_iff]
            refine ⟨⟨?_, ?_, by omega, Or.inl (by omega)⟩, fun _ => ?_⟩
            · cases hd : l.delivered
              · rfl
              · have := acdNr_gt x.log _ l hl hd ht.1
                rw [← hnr] at this
                omega
            · have hs := ckaSender_succ_ne (s1.ck.t p' - 1)
              rw [show s1.ck.t p' - 1 + 1 = s1.ck.t p' by omega, hsp] at hs
              rw [ht.1, her0]
              exact fun h => hs h.symm
            · simp [acdCutRecv, ht.1]
          · simp only at he; omega
        · obtain ⟨⟨l, hl, hq, ht⟩, -⟩ := hsd el hel
          refine ⟨⟨l, hl, acdQualAt_cutRecv_old _ _ _ _ _ _ _ hq (by omega), ht⟩, fun he => ?_⟩
          simp only [acdTag, ACDIDSt.tag, Prod.mk.injEq] at ht
          have hq := (acdQual_iff _ _ _ _).1 (acdQual_of_acdQualAt hq)
          omega
      · intro l hl hq
        have hq' := (acdQual_iff _ _ _ _).1 (acdQual_of_acdQualAt hq)
        have hne : l.e ≠ s1.ck.t p' := fun h => hq'.2.1 (h ▸ hsp)
        have hle' : l.e ≤ (s1.ck.st p').er := by rw [her0]; omega
        rw [List.map_append, List.mem_append]
        rcases acdQualAt_cutRecv_new _ _ _ _ _ _ _ hq hle' with hold | ⟨hle, hN, hb⟩
        · right
          exact hcp l hl hold
        · left
          have h0 : (s1.ck.st p').er ≠ 0 := by omega
          obtain ⟨sa, hsa⟩ := Option.isSome_iff_exists.1 (hrcv (by omega))
          rw [ite_eq_right h0, hb, Bool.cond_true, hsa, Option.map_some, Option.getD_some]
          have hPN : s1.ck.msg.2 = acdCnt x.log (s1.ck.st p').er := by
            rw [hmsg, htop, ite_eq_right (by omega), her0]; congr 1
          have hj' := (hpos l.e l.j).1 (List.mem_map_of_mem (f := acdTag) hl)
          rw [hle] at hj'
          refine List.mem_map.2 ⟨((s1.ck.st p').er, l.j, chainKey G sa l.j),
            (ACDIDSt.mem_skipKeys G _ sa _ _ _).2 ⟨l.j, by omega, by omega, rfl⟩, ?_⟩
          simp [acdTag, ACDIDSt.tag, hle]
    · have hst : (s1.ck.recvd p x').st p' = s1.ck.st p' := by
        simp [CKAGameSt.recvd, Function.update_of_ne hp]
      have hT1 : Function.update s1.ck.t p (s1.ck.t p + 1) p' = s1.ck.t p' := by
        simp [Function.update_of_ne hp]
      have hsr : smRecvEpoch (⟨fun _ => (), Function.update s1.ck.t p (s1.ck.t p + 1), ()⟩ :
          CKAGameSt Unit Unit) p' = smRecvEpoch (ckaShadow s1.ck) p' := by
        unfold smRecvEpoch; simp only [hT1]; rfl
      rw [hst]
      refine ACDIDPartyInvAt.congr_qual (qual := acdQualAt cut) ?_ ?_
      · refine ⟨?_, ?_, ?_, ?_, hnr, ?_, hrcv, hnd', hsd, hcp⟩ <;> (try dsimp only) <;>
          (try simp only [hT1, hsr]) <;> assumption
      · funext er nr l
        simp only [acdQualAt, acdCutRecv, Function.update_of_ne hp]

omit [SampleableType Kt] [Fintype Rand] [Nonempty Rand] [DecidableEq W] [DecidableEq Ct] in
/-- Sending, with any ciphertext logged, keeps the invariant of the header-aware
construction. -/
theorem acdIDHdr_inv_send
    (s : SMSchemeSt (ACDIDSt Sc RK Sa Msg Kt) (Msg × ℕ) × SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)
    (hs : ACDIDHdrInv G pub₀ cut s) (p : CKAParty) (hc : ckaSender (s.1.ck.t p) = p) (m : W × W)
    (y : ACDIDSt Sc RK Sa Msg Kt × Ct)
    (hy : (acdIDHdrSM C R G DH hdrAD pub₀ pnOk maxSkip maxStored).send (s.1.ck.st p) m = some y)
    (c : Ct) (b : Bool) :
    ACDIDHdrInv G pub₀ cut (s.1.upd p y.1 b,
      s.2.record (s.1.ck.t p) (s.1.ck.st p).ns m ((s.1.ck.st p).pubS, (s.1.ck.st p).ns) c) := by
  obtain ⟨s1, x⟩ := s
  obtain ⟨hle, hah, hpubs, hmsg, hle_e, hj, hpos, hnd, hdl, hpty⟩ := hs
  dsimp only at *
  obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 hy
  have hzr : z.1.rcv = (s1.ck.st p).base.rcv := by
    simp only [acdIDHdrBase, acdSMAD] at hz
    obtain ⟨sa, -, rfl⟩ := Option.map_eq_some_iff.1 hz
    rfl
  set n := s1.ck.t p with hn
  set ent : SMIDLogEntry W (ACDHdr Msg) Ct :=
    ⟨n, (s1.ck.st p).ns, m.1, m.2, ((s1.ck.st p).pubS, (s1.ck.st p).ns), c, false⟩ with hent
  have hlog : (x.record n (s1.ck.st p).ns m ((s1.ck.st p).pubS, (s1.ck.st p).ns) c).log =
      ent :: x.log := rfl
  have hns : (s1.ck.st p).ns = acdCnt x.log n := by
    rw [(hpty p).ns, ckaShadow_t, acdNs, ite_eq_left hc]
  have hntop : n ≤ max (s1.ck.t .A) (s1.ck.t .B) := by cases p <;> simp [hn]
  have hntop' : max (s1.ck.t .A) (s1.ck.t .B) ≤ n + 1 := by cases p <;> simp [hn] <;> omega
  have hcnt : ∀ e, e ≠ n → acdCnt (ent :: x.log) e = acdCnt x.log e := by
    intro e he; rw [acdCnt_cons]; simp [hent, Ne.symm he]
  have hcntn : acdCnt (ent :: x.log) n = acdCnt x.log n + 1 := by rw [acdCnt_cons]; simp [hent]
  have hnr : ∀ e, acdNr (ent :: x.log) e = acdNr x.log e := fun e =>
    acdNr_cons_of_undelivered ent x.log e rfl
  have hupd : ∀ q, (s1.upd p (⟨z.1, (s1.ck.st p).pubS, (s1.ck.st p).ns + 1, (s1.ck.st p).ep,
      (s1.ck.st p).er, (s1.ck.st p).nr, (s1.ck.st p).rpubs, (s1.ck.st p).store⟩, z.2).1 b).ck.st q =
      if q = p then ⟨z.1, (s1.ck.st p).pubS, (s1.ck.st p).ns + 1, (s1.ck.st p).ep,
        (s1.ck.st p).er, (s1.ck.st p).nr, (s1.ck.st p).rpubs, (s1.ck.st p).store⟩
      else s1.ck.st q := by
    intro q; by_cases hq : q = p
    · subst hq; simp [SMSchemeSt.upd]
    · simp [SMSchemeSt.upd, hq]
  refine ⟨hle, hah, hpubs, ?_, ?_, ?_, ?_, ?_, ?_, fun q => ?_⟩ <;> rw [hlog]
  · change s1.ck.msg.2 = if max (s1.ck.t .A) (s1.ck.t .B) ≤ 1 then 0
      else acdCnt (ent :: x.log) (max (s1.ck.t .A) (s1.ck.t .B) - 2)
    rw [hmsg]
    split_ifs with h1
    · rfl
    · rw [hcnt]; omega
  · intro t ht
    rcases List.mem_cons.1 ht with rfl | ht
    · exact hntop
    · exact hle_e t ht
  · intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · rfl
    · exact hj l hl
  · intro e j
    by_cases he : e = n
    · subst he
      rw [hcntn, List.map_cons, List.mem_cons, hpos, ← hns]
      simp only [acdTag, hent, Prod.mk.injEq, true_and]
      omega
    · rw [hcnt e he, List.map_cons, List.mem_cons, hpos]
      simp only [acdTag, hent, Prod.mk.injEq]
      constructor
      · rintro (⟨h1, -⟩ | h); · exact absurd h1 he
        · exact h
      · exact Or.inr
  · rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, hnd⟩
    have := (hpos _ _).1 hmem
    simp only [hent] at this
    omega
  · intro l hl hd q hq
    rcases List.mem_cons.1 hl with rfl | hl
    · simp [hent] at hd
    · exact hdl l hl hd q hq
  · have hqent : acdQualAt cut q (s1.ck.st q).er (s1.ck.st q).nr ent = false := by
      by_contra hcon
      rw [Bool.not_eq_false] at hcon
      replace hcon := (acdQual_iff _ _ _ _).1 (acdQual_of_acdQualAt hcon)
      obtain ⟨-, h2, -, h4⟩ := hcon
      have hqp : q ≠ p := fun h => h2 (by rw [h]; exact hc)
      have hqo : q = p.other := by cases p <;> cases q <;> simp_all
      have her := (hpty q).er
      have hnrq := (hpty q).nr
      have htq : s1.ck.t q ≤ n + 1 := by subst hqo; cases p <;> simp [hn] at hle ⊢ <;> omega
      have hah' : s1.ck.t q = n + 1 → ckaSender (s1.ck.t q) = q := by
        intro h; rw [hqo] at h ⊢; exact hah p h
      have herq : (s1.ck.st q).er ≤ n := by
        rw [her]; unfold smRecvEpoch; simp only [ckaShadow_t]
        split_ifs with h
        · grind
        · by_cases h' : s1.ck.t q = n + 1
          · exact absurd (hah' h') h
          · grind
      have hle' := acdNr_le_cnt x.log n hpos
      simp only [hent] at h4
      rcases h4 with h4 | ⟨h4, h5⟩
      · omega
      · rw [hnrq, ← h4] at h5; omega
    have hsh : ckaShadow (s1.upd p (⟨z.1, (s1.ck.st p).pubS, (s1.ck.st p).ns + 1, (s1.ck.st p).ep,
        (s1.ck.st p).er, (s1.ck.st p).nr, (s1.ck.st p).rpubs, (s1.ck.st p).store⟩, z.2).1 b).ck =
        ckaShadow s1.ck := rfl
    change ACDIDPartyInvAt G (acdPubSAt pub₀) (acdQualAt cut) (ent :: x.log) x.pubs _ q _
    rw [hsh, hupd]
    obtain ⟨hep, her, hpS, hns', hnr', hrp, hrcv, hnd', hsd, hcp⟩ := hpty q
    have hcomp : ∀ l ∈ ent :: x.log, acdQualAt cut q (s1.ck.st q).er (s1.ck.st q).nr l = true →
        acdTag l ∈ (s1.ck.st q).store.map ACDIDSt.tag := by
      intro l hl hql
      rcases List.mem_cons.1 hl with rfl | hl
      · rw [hqent] at hql; exact absurd hql (by simp)
      · exact hcp l hl hql
    have hsnd : ∀ el ∈ (s1.ck.st q).store, ∃ l ∈ ent :: x.log,
        acdQualAt cut q (s1.ck.st q).er (s1.ck.st q).nr l = true ∧
          acdTag l = ACDIDSt.tag el := by
      intro el hel
      obtain ⟨⟨l, hl, h1, h2⟩, -⟩ := hsd el hel
      exact ⟨l, List.mem_cons_of_mem _ hl, h1, h2⟩
    split_ifs with hq
    · subst hq
      refine ⟨hep, her, hpS, ?_, ?_, hrp, ?_, hnd', fun el hel => ⟨hsnd el hel, ?_⟩, hcomp⟩ <;>
        dsimp only
      · rw [ckaShadow_t, acdNs, ite_eq_left hc, hcntn, hns]
      · rw [hnr]; exact hnr'
      · rw [hzr]; exact hrcv
      · rw [hzr]; exact (hsd el hel).2
    · refine ⟨hep, her, hpS, ?_, ?_, hrp, hrcv, hnd', fun el hel => ⟨hsnd el hel, (hsd el hel).2⟩,
        hcomp⟩
      · rw [hns', ckaShadow_t]
        unfold acdNs
        have hqp : ckaSender n ≠ q := fun h => hq (h.symm.trans hc)
        split_ifs with h1 h2
        · rw [hcnt]; intro h; rw [h] at h1; exact hqp h1
        · rfl
        · rw [hcnt]
          intro h
          have := ckaSender_eq_of_ne (n := s1.ck.t q - 1)
            (by rw [show s1.ck.t q - 1 + 1 = s1.ck.t q by omega]; exact h1)
          rw [h] at this
          exact hqp this
      · rw [hnr]; exact hnr'

/-- An epoch from `1` sent by `q` is not the receiving epoch of `q`. -/
theorem acd_smRecvEpoch_ne (sh : CKAGameSt Unit Unit) (q : CKAParty) (e : ℕ) (h1 : 1 ≤ e)
    (h2 : ckaSender e = q) : smRecvEpoch sh q ≠ e := by
  unfold smRecvEpoch
  split_ifs with h
  · intro he
    have hs := ckaSender_succ_ne (sh.t q - 1)
    rw [show sh.t q - 1 + 1 = sh.t q by omega, h, he, h2] at hs
    exact hs rfl
  · intro he; rw [he] at h; exact h h2

omit [SampleableType Kt] [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct]
  [Fintype RK][Nonempty RK] in
/-- A delivery from the log with a successful key lookup keeps the invariant of the header-aware
construction. -/
theorem acdIDHdr_inv_mark
    (s : SMSchemeSt (ACDIDSt Sc RK Sa Msg Kt) (Msg × ℕ) × SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)
    (hs : ACDIDHdrInv G pub₀ cut s) (p : CKAParty) (h : ACDHdr Msg) (ad : W) (c : Ct) (e : ℕ)
    (he : s.2.epochOf (ckaShadow s.1.ck) p h.1 = some e) (l : SMIDLogEntry W (ACDHdr Msg) Ct)
    (hl : s.2.findEntry e h ad c = some l) (y : ACDIDSt Sc RK Sa Msg Kt × Kt)
    (hy : acdIDRKey G maxSkip maxStored (s.1.ck.st p) h = some y) (b : Bool) :
    ACDIDHdrInv G pub₀ cut (s.1.upd p y.1 b, s.2.mark e h ad c) := by
  obtain ⟨s1, x⟩ := s
  have hsort := hs.pubs_sorted
  obtain ⟨hle, hah, hpubs, hmsg, hle_e, hj, hpos, hnd, hdl, hpty⟩ := hs
  dsimp only at *
  obtain ⟨hlm, hld, hle', hlh, -, -⟩ := acd_findEntry_some x e h ad c l hl
  have hlj : l.j = h.2 := by rw [hj l hlm, hlh]
  have hPl : l.isMatch e h ad c = true := List.find?_some hl
  have hP : ∀ l' ∈ x.log, l'.isMatch e h ad c = true → l' = l := by
    intro l' hl' hm
    simp only [SMIDLogEntry.isMatch, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
    refine List.inj_on_of_nodup_map hnd hl' hlm ?_
    simp only [acdTag, hm.1.1.1.2, hle', hj l' hl', hm.1.1.2, hlj]
  have hmark : (x.mark e h ad c).log =
      x.log.map fun l' => if l'.isMatch e h ad c then { l' with delivered := true } else l' := rfl
  have hmarkTag : (x.mark e h ad c).log.map acdTag = x.log.map acdTag := by
    rw [hmark, List.map_map]
    refine List.map_congr_left fun l' _ => ?_
    simp only [Function.comp_apply]
    split <;> rfl
  have hcntm : ∀ e', acdCnt (x.mark e h ad c).log e' = acdCnt x.log e' := by
    intro e'; unfold acdCnt; rw [hmarkTag]
  have hnrm : ∀ e', acdNr (x.mark e h ad c).log e' =
      if e' = e then max (acdNr x.log e') (h.2 + 1) else acdNr x.log e' := by
    intro e'
    rw [hmark, acdNr_map_deliver x.log _ e h.2 (fun l' hl' hm => by
      rw [hP l' hl' hm]; exact ⟨hle', hlj⟩)]
    have hany : x.log.any (fun l' => l'.isMatch e h ad c) = true :=
      List.any_eq_true.2 ⟨l, hlm, hPl⟩
    simp only [hany, and_true]
  have hmem1 : ∀ l'' ∈ (x.mark e h ad c).log,
      l'' = { l with delivered := true } ∨ (l'' ∈ x.log ∧ l'' ≠ l) := by
    intro l'' hl''
    rw [hmark] at hl''
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl''
    split
    · rename_i hm; left; rw [hP l' hl' hm]
    · rename_i hm; right; exact ⟨hl', fun h' => by rw [h'] at hm; exact hm hPl⟩
  have hmem2 : ∀ l' ∈ x.log, l' ≠ l → l' ∈ (x.mark e h ad c).log := by
    intro l' hl' hne
    rw [hmark]
    refine List.mem_map.2 ⟨l', hl', ?_⟩
    rw [ite_eq_right fun hm => hne (hP l' hl' hm)]
  have hst : ∀ q, (s1.upd p y.1 b).ck.st q = if q = p then y.1 else s1.ck.st q := by
    intro q; by_cases hq : q = p
    · subst hq; simp [SMSchemeSt.upd]
    · simp [SMSchemeSt.upd, hq]
  have hsh : ckaShadow (s1.upd p y.1 b).ck = ckaShadow s1.ck := rfl
  -- the resolved epoch
  have hrp := (hpty p).rpubs
  unfold acdIDRKey at hy
  rw [hrp, ckaShadow_t] at hy
  obtain ⟨q, hq⟩ : ∃ q, (acdRPubs x.pubs (s1.ck.t p) p).find? (fun q => decide (q.2 = h.1)) =
      some q := by
    cases hq : (acdRPubs x.pubs (s1.ck.t p) p).find? (fun q => decide (q.2 = h.1)) with
    | none => rw [hq] at hy; exact absurd hy (by simp)
    | some q => exact ⟨q, rfl⟩
  rw [hq] at hy
  obtain ⟨hqe, -, hq1, hqt, hqs⟩ := acdRPubs_find_epochOf x (ckaShadow s1.ck) p h.1 hsort q hq
  have hqe' : q.1 = e := Option.some.inj (hqe.symm.trans he)
  rw [ckaShadow_t] at hqt
  refine ⟨hle, hah, hpubs, ?_, ?_, ?_, ?_, ?_, ?_, fun r => ?_⟩
  · change s1.ck.msg.2 = if max (s1.ck.t .A) (s1.ck.t .B) ≤ 1 then 0
      else acdCnt (x.mark e h ad c).log (max (s1.ck.t .A) (s1.ck.t .B) - 2)
    rw [hcntm, hmsg]
  · rw [hmarkTag]; exact hle_e
  · intro l'' hl''
    rcases hmem1 l'' hl'' with rfl | ⟨hl'', -⟩
    · exact hj l hlm
    · exact hj l'' hl''
  · intro e' j'; rw [hmarkTag, hcntm]; exact hpos e' j'
  · rw [hmarkTag]; exact hnd
  · intro l'' hl'' hd r hr
    rcases hmem1 l'' hl'' with rfl | ⟨hl'', -⟩
    · have : r = p := CKAParty.eq_of_ne_ne _ _ _ hr (by
        change ckaSender l.e ≠ p; rw [hle', ← hqe']; exact hqs)
      subst this
      change l.e ≤ s1.ck.t r
      rw [hle', ← hqe']; exact hqt
    · exact hdl l'' hl'' hd r hr
  · rw [hsh, hst]
    have hse : ckaSender e ≠ p := by rw [← hqe']; exact hqs
    have he1 : 1 ≤ e := by rw [← hqe']; exact hq1
    have hlnq : ∀ r', ckaSender e = r' → ∀ er' nr', acdQualAt cut r' er' nr' l = false := by
      intro r' hr' er' nr'
      by_contra hcon
      rw [Bool.not_eq_false] at hcon
      replace hcon := (acdQual_iff _ _ _ _).1 (acdQual_of_acdQualAt hcon)
      exact hcon.2.1 (by rw [hle', hr'])
    split_ifs with hrq
    · subst hrq
      obtain ⟨hep, her, hpS, hns, hnr, -, hrcv, hnd', hsd, hcp⟩ := hpty r
      have hlx : (e, h.2) ∈ x.log.map acdTag := List.mem_map.2 ⟨l, hlm, by simp [acdTag, hle', hlj]⟩
      have hjc : h.2 < acdCnt x.log e := (hpos e h.2).1 hlx
      dsimp only at hy
      split_ifs at hy with hc1 hb
      · obtain ⟨sa, hsa, rfl⟩ := Option.map_eq_some_iff.1 hy
        have hEe : (s1.ck.st r).er = e := by rw [← hc1.1, hqe']
        have hlnq' : acdQualAt cut r (s1.ck.st r).er (s1.ck.st r).nr l = false := by
          by_contra hcon
          rw [Bool.not_eq_false] at hcon
          replace hcon := (acdQual_iff _ _ _ _).1 (acdQual_of_acdQualAt hcon)
          rw [hle', hlj] at hcon
          omega
        refine ⟨hep, her, hpS, ?_, ?_, rfl, hrcv, ?_, ?_, ?_⟩ <;> dsimp only
        · rw [hns]; simp only [acdNs, hcntm]
        · rw [hnrm, ite_eq_left hEe, ← hnr]; exact (max_eq_right (by omega)).symm
        · refine ACDIDSt.skipKeys_append_nodup G _ sa _ _ _ hnd' fun el hel he' => ?_
          obtain ⟨⟨l', -, hq', ht'⟩, -⟩ := hsd el hel
          simp only [acdTag, ACDIDSt.tag, Prod.mk.injEq] at ht'
          have hq' := (acdQual_iff _ _ _ _).1 (acdQual_of_acdQualAt hq')
          omega
        · intro el hel
          rw [List.mem_append] at hel
          rcases hel with hel | hel
          · obtain ⟨i, hi1, hi2, rfl⟩ := (ACDIDSt.mem_skipKeys G _ sa _ _ el).1 hel
            have hi : i < acdCnt x.log (s1.ck.st r).er := by rw [hEe]; omega
            obtain ⟨l', hl', ht'⟩ := List.mem_map.1 ((hpos _ i).2 hi)
            simp only [acdTag, Prod.mk.injEq] at ht'
            have hne : l' ≠ l := by intro h'; rw [h', hlj] at ht'; omega
            refine ⟨⟨l', hmem2 l' hl' hne, ?_, by simp [acdTag, ACDIDSt.tag, ht'.1, ht'.2]⟩,
              fun _ => by rw [hsa]; rfl⟩
            rw [acdQualAt_iff, acdQual_iff]
            refine ⟨⟨?_, by rw [ht'.1, hEe]; exact hse, by rw [ht'.1, hEe]; exact he1,
              Or.inr ⟨ht'.1, by omega⟩⟩, fun h' => absurd h' (by omega)⟩
            cases hd : l'.delivered
            · rfl
            · have := acdNr_gt x.log _ l' hl' hd ht'.1
              rw [← hnr] at this
              omega
          · obtain ⟨⟨l', hl', hq', ht'⟩, hk⟩ := hsd el hel
            have hne : l' ≠ l := by intro h'; rw [h', hlnq'] at hq'; exact absurd hq' (by simp)
            refine ⟨⟨l', hmem2 l' hl' hne, ?_, ht'⟩, hk⟩
            rw [acdQualAt_iff, acdQual_iff] at hq' ⊢
            obtain ⟨⟨h1, h2, h3, h4⟩, hcq⟩ := hq'
            exact ⟨⟨h1, h2, h3, by omega⟩, hcq⟩
        · intro l'' hl'' hq''
          rw [List.map_append, List.mem_append]
          rcases hmem1 l'' hl'' with rfl | ⟨hl'', hne⟩
          · exact absurd ((acdQual_iff _ _ _ _).1 (acdQual_of_acdQualAt hq'')).1 (by simp)
          · rw [acdQualAt_iff, acdQual_iff] at hq''
            obtain ⟨⟨h1, h2, h3, h4⟩, hcq⟩ := hq''
            by_cases hold : l''.e < (s1.ck.st r).er ∨
                (l''.e = (s1.ck.st r).er ∧ l''.j < (s1.ck.st r).nr)
            · right
              exact hcp l'' hl''
                ((acdQualAt_iff _ _ _ _ _).2 ⟨(acdQual_iff _ _ _ _).2 ⟨h1, h2, h3, hold⟩, hcq⟩)
            · left
              have hje : l''.e = (s1.ck.st r).er := by omega
              have hjn : l''.j ≠ h.2 := by
                intro hj'
                exact hne (List.inj_on_of_nodup_map hnd hl'' hlm
                  (by simp [acdTag, hje, hEe, hle', hj', hlj]))
              refine List.mem_map.2 ⟨((s1.ck.st r).er, l''.j, chainKey G sa l''.j),
                (ACDIDSt.mem_skipKeys G _ sa _ _ _).2 ⟨l''.j, by omega, by omega, rfl⟩, ?_⟩
              simp [acdTag, ACDIDSt.tag, hje]
      · obtain ⟨el0, -, rfl⟩ := Option.map_eq_some_iff.1 hy
        have hne' : ∀ l' ∈ x.log, acdTag l' = (q.1, h.2) → l' = l := fun l' hl' ht' =>
          List.inj_on_of_nodup_map hnd hl' hlm (by rw [ht']; simp [acdTag, hle', hlj, hqe'])
        refine ⟨hep, her, hpS, ?_, ?_, rfl, hrcv, ?_, ?_, ?_⟩ <;> dsimp only
        · rw [hns]; simp only [acdNs, hcntm]
        · rw [hnrm, hnr]
          split_ifs with hEe
          · rw [hEe] at hc1 ⊢
            have : ¬ (acdNr x.log e ≤ h.2) := by
              intro h'; apply hc1; rw [hqe', ← hEe]; exact ⟨rfl, by rw [hnr, hEe]; exact h'⟩
            exact (max_eq_left (by omega)).symm
          · rfl
        · exact hnd'.sublist (List.filter_sublist.map _)
        · intro el hel
          obtain ⟨hel, hnt⟩ := List.mem_filter.1 hel
          obtain ⟨⟨l', hl', hq', ht'⟩, hk⟩ := hsd el hel
          refine ⟨⟨l', hmem2 l' hl' fun h' => ?_, hq', ht'⟩, hk⟩
          rw [h'] at ht'
          simp only [bne_iff_ne, ne_eq] at hnt
          exact hnt (by rw [← ht']; simp [acdTag, hle', hlj, hqe'])
        · intro l'' hl'' hq''
          rcases hmem1 l'' hl'' with rfl | ⟨hl'', hne⟩
          · exact absurd ((acdQual_iff _ _ _ _).1 (acdQual_of_acdQualAt hq'')).1 (by simp)
          · obtain ⟨el, hel, het⟩ := List.mem_map.1 (hcp l'' hl'' hq'')
            refine List.mem_map.2 ⟨el, List.mem_filter.2 ⟨hel, ?_⟩, het⟩
            simp only [bne_iff_ne, ne_eq]
            intro ht
            exact hne (hne' l'' hl'' (het.symm.trans ht))
    · obtain ⟨hep, her, hpS, hns, hnr, hrp2, hrcv, hnd', hsd, hcp⟩ := hpty r
      have hser : ckaSender e = r := CKAParty.eq_of_ne_ne p _ _ (Ne.symm hse) (Ne.symm hrq)
      have hne : (s1.ck.st r).er ≠ e := by
        rw [her]; exact acd_smRecvEpoch_ne _ r e he1 hser
      refine ⟨hep, her, hpS, ?_, ?_, hrp2, hrcv, hnd', fun el hel => ⟨?_, (hsd el hel).2⟩, ?_⟩
      · rw [hns]; simp only [acdNs, hcntm]
      · rw [hnrm, ite_eq_right hne, hnr]
      · obtain ⟨⟨l', hl', hq', ht'⟩, -⟩ := hsd el hel
        have : l' ≠ l := by
          intro h'; rw [h', hlnq r hser] at hq'; exact absurd hq' (by simp)
        exact ⟨l', hmem2 l' hl' this, hq', ht'⟩
      · intro l'' hl'' hq''
        rcases hmem1 l'' hl'' with rfl | ⟨hl'', -⟩
        · exact absurd ((acdQual_iff _ _ _ _).1 (acdQual_of_acdQualAt hq'')).1 (by simp)
        · exact hcp l'' hl'' hq''

omit [SampleableType Kt] [Fintype Rand] [Nonempty Rand] in
/-- A delivery with decryption from the log keeps the invariant of the header-aware
construction. -/
theorem acdIDHdr_inv_deliver (ΔFS ΔPCS : ℕ)
    (s : SMSchemeSt (ACDIDSt Sc RK Sa Msg Kt) (Msg × ℕ) × SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)
    (hs : ACDIDHdrInv G pub₀ cut s) (p : CKAParty) (h : ACDHdr Msg) (ad : W) (c : Ct) :
    ACDIDHdrInv G pub₀ cut (smIDDeliver (acdIDHdrSM C R G DH hdrAD pub₀ pnOk maxSkip maxStored)
      ΔFS ΔPCS (fun _ => true) s p h ad c).2 := by
  unfold smIDDeliver
  split
  · exact hs
  · rename_i e he
    split_ifs with hsafe hid
    · split
      · exact hs
      · rename_i y hy
        split
        · rename_i m hm
          obtain ⟨l, hl, -⟩ := Option.map_eq_some_iff.1 hm
          exact acdIDHdr_inv_mark G pub₀ cut maxSkip maxStored s hs p h ad c e he l hl y hy s.1.done
        · exact hs
    · exact absurd rfl hid
    · exact hs

omit [SampleableType Kt] in
/-- The oracle with decryption from the log keeps the invariant of the header-aware
construction, at cuts that stay empty when every skip check holds. -/
theorem acdIDHdr_inv_step (ΔFS ΔPCS t : ℕ) (idealC : Bool)
    (s : SMSchemeSt (ACDIDSt Sc RK Sa Msg Kt) (Msg × ℕ) × SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)
    (d : SMIDQuery W (ACDHdr Msg) Ct) (hs : ACDIDHdrInv G pub₀ cut s)
    (z) (hz : z ∈ (smIDOracleAt (acdIDHdrSM C R G DH hdrAD pub₀ pnOk maxSkip maxStored) ΔFS ΔPCS
      t idealC (fun _ => true) s d).support) :
    ∃ cut', ACDIDHdrInv G pub₀ cut' z.2 ∧
      ((∀ x n, pnOk x n = true) → (∀ q e, cut q e = none) → ∀ q e, cut' q e = none) := by
  rcases d with q | ⟨p, h, ad, c⟩
  · simp only [smIDOracleAt] at hz
    split_ifs at hz with hg
    · rw [PMF.mem_support_map_iff] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      cases q with
      | ratchet p =>
        simp only [smSchemeOracle] at hy
        split_ifs at hy with hc
        · simp only [PMF.support_bind, PMF.support_pure, Set.mem_iUnion,
            Set.mem_singleton_iff] at hy
          obtain ⟨r, -, rfl⟩ := hy
          exact ⟨cut, acdIDHdr_inv_ratchet C R G DH hdrAD pub₀ pnOk cut maxSkip maxStored s hs p
            hc r, fun _ h => h⟩
        · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
          subst hy
          exact ⟨cut, acdIDInvAt_aux G s _ hs rfl rfl, fun _ h => h⟩
      | recv p =>
        simp only [smSchemeOracle] at hy
        split_ifs at hy with hc
        · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
          subst hy
          exact ⟨_, acdIDInvAt_aux G _ _
            (acdIDHdr_inv_recv C R G DH hdrAD pub₀ pnOk cut maxSkip maxStored s hs p hc) rfl rfl,
            fun hp hn => acdCutRecv_none _ _ _ _ _ (hp _ _) hn⟩
        · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
          subst hy
          exact ⟨cut, acdIDInvAt_aux G s _ hs rfl rfl, fun _ h => h⟩
      | send p m =>
        simp only [smSchemeOracle] at hy
        split_ifs at hy with hc
        · cases hM : (acdIDHdrSM C R G DH hdrAD pub₀ pnOk maxSkip maxStored).toSMScheme.send
              (s.1.ck.st p) m with
          | none =>
            simp only [hM, PMF.support_pure, Set.mem_singleton_iff] at hy
            subst hy
            exact ⟨cut, acdIDInvAt_aux G s _ hs rfl rfl, fun _ h => h⟩
          | some y' =>
            simp only [hM, PMF.support_pure, Set.mem_singleton_iff] at hy
            subst hy
            exact ⟨cut, acdIDHdr_inv_send C R G DH hdrAD pub₀ pnOk cut maxSkip maxStored s hs p
              (by simpa using hc) m y' hM y'.2 s.1.done, fun _ h => h⟩
        · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
          subst hy
          exact ⟨cut, acdIDInvAt_aux G s _ hs rfl rfl, fun _ h => h⟩
      | chall p m =>
        simp only [smSchemeOracle] at hy
        by_cases hc : (!s.1.done && ckaSender (s.1.ck.t p) == p && s.1.ck.t p == t) = true
        · rw [ite_eq_left hc] at hy
          have hc' : ckaSender (s.1.ck.t p) = p := by
            simp only [Bool.and_eq_true, beq_iff_eq] at hc
            exact hc.1.2
          cases hM : (acdIDHdrSM C R G DH hdrAD pub₀ pnOk maxSkip maxStored).toSMScheme.send
              (s.1.ck.st p) m with
          | none =>
            simp only [hM, PMF.support_pure, Set.mem_singleton_iff] at hy
            subst hy
            exact ⟨cut, acdIDInvAt_aux G s _ hs rfl rfl, fun _ h => h⟩
          | some y' =>
            simp only [hM] at hy
            rw [PMF.mem_support_bind_iff] at hy
            obtain ⟨c', -, hy⟩ := hy
            simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
            subst hy
            exact ⟨cut, acdIDHdr_inv_send C R G DH hdrAD pub₀ pnOk cut maxSkip maxStored s hs p
              hc' m y' hM c' true, fun _ h => h⟩
        · rw [ite_eq_right hc] at hy
          simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
          subst hy
          exact ⟨cut, acdIDInvAt_aux G s _ hs rfl rfl, fun _ h => h⟩
      | corrupt p =>
        simp only [smSchemeOracle, PMF.support_pure, Set.mem_singleton_iff] at hy
        subst hy
        exact ⟨cut, acdIDInvAt_aux G s _ hs (by split <;> rfl) (by split <;> rfl), fun _ h => h⟩
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨cut, hs, fun _ h => h⟩
  · simp only [smIDOracleAt, PMF.support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨cut, acdIDHdr_inv_deliver C R G DH hdrAD pub₀ pnOk cut maxSkip maxStored ΔFS ΔPCS s hs
      p h ad c, fun _ h => h⟩

omit [SampleableType Kt] [SampleableType W] [SampleableType Ct] [Fintype RK] [Nonempty RK] in
/-- The success of the key lookup of the header-aware construction at a matching log entry is
that of the view. -/
theorem acdIDHdr_rkeyOk_eq (msg : ACDHdr Msg → W × W → W × W)
    (s : SMSchemeSt (ACDIDSt Sc RK Sa Msg Kt) (Msg × ℕ) × SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)
    (p : CKAParty) (h : ACDHdr Msg) (e : ℕ) (ad : W) (c : Ct) (hs : ACDIDHdrInv G pub₀ cut s)
    (he : s.2.epochOf (ckaShadow s.1.ck) p h.1 = some e) (hf : (s.2.findEntry e h ad c).isSome) :
    (acdIDRKey G maxSkip maxStored (s.1.ck.st p) h).isSome =
      (acdIDViewAt (Sc := Sc) (RK := RK) G maxSkip maxStored msg pub₀ cut).rkeyOk s.2
        (ckaShadow s.1.ck) p h := by
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 hf
  obtain ⟨hlm, hld, hle, hlh, -, -⟩ := acd_findEntry_some s.2 e h ad c l hl
  have hlj : l.j = h.2 := by rw [hs.log_j l hlm, hlh]
  obtain ⟨-, her, -, -, hnr, hrp, hrcv, hnd', hsd, hcp⟩ := hs.party p
  have hlen := acd_length_eq s.2.log (s.1.ck.st p).store
    (acdQualAt cut p (s.1.ck.st p).er (s.1.ck.st p).nr) hs.log_nodup hnd'
    (fun el hel => (hsd el hel).1) hcp
  rw [hnr, her] at hlen
  unfold acdIDRKey
  simp only [acdIDViewAt]
  rw [hrp, ckaShadow_t]
  cases hq : (acdRPubs s.2.pubs (s.1.ck.t p) p).find? (fun q => decide (q.2 = h.1)) with
  | none => rfl
  | some q =>
    obtain ⟨hqe, -, hq1, hqt, hqs⟩ := acdRPubs_find_epochOf s.2 (ckaShadow s.1.ck) p h.1
      hs.pubs_sorted q (by simpa using hq)
    have hqe' : q.1 = e := Option.some.inj (hqe.symm.trans he)
    dsimp only
    rw [hnr, her]
    by_cases hc1 : q.1 = smRecvEpoch (ckaShadow s.1.ck) p ∧
        acdNr s.2.log (smRecvEpoch (ckaShadow s.1.ck) p) ≤ h.2
    · rw [ite_eq_left hc1, ite_eq_left hc1]
      obtain ⟨sa, hsa⟩ := Option.isSome_iff_exists.1 (hrcv (by rw [her, ← hc1.1]; exact hq1))
      rw [hlen]
      split_ifs with hb
      · rw [hsa]; simp [hb]
      · exact (decide_eq_false hb).symm
    · rw [ite_eq_right hc1, ite_eq_right hc1]
      have hql0 : acdQual p (s.1.ck.st p).er (s.1.ck.st p).nr l = true := by
        rw [acdQual_iff, hnr, her]
        have hle' := acd_le_smRecvEpoch (ckaShadow s.1.ck) p l.e (by rw [hle, ← hqe']; exact hqt)
          (by rw [hle, ← hqe']; exact hqs)
        refine ⟨hld, by rw [hle, ← hqe']; exact hqs, by rw [hle, ← hqe']; exact hq1, ?_⟩
        rw [hle, ← hqe'] at hle' ⊢
        rw [hlj]
        by_cases heq : q.1 = smRecvEpoch (ckaShadow s.1.ck) p
        · right; exact ⟨heq, by have := fun h' => hc1 ⟨heq, h'⟩; omega⟩
        · left; omega
      rw [Option.isSome_map]
      by_cases hk : ((cut p q.1).all (fun n => decide (h.2 < n)) ||
          decide (smRecvEpoch (ckaShadow s.1.ck) p ≤ q.1)) = true
      · rw [hk]
        have hql : acdQualAt cut p (s.1.ck.st p).er (s.1.ck.st p).nr l = true := by
          refine (acdQualAt_iff _ _ _ _ _).2 ⟨hql0, fun hlt => ?_⟩
          rw [hle, ← hqe', hlj]
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hk
          rcases hk with hk | hk
          · exact hk
          · rw [her, hle, ← hqe'] at hlt; omega
        obtain ⟨el, hel, het⟩ := List.mem_map.1 (hcp l hlm hql)
        refine List.find?_isSome.2 ⟨el, hel, ?_⟩
        rw [het, hqe']
        simp [acdTag, hle, hlj]
      · rw [Bool.not_eq_true] at hk
        rw [hk]
        cases hf' : (s.1.ck.st p).store.find? (fun el => ACDIDSt.tag el == (q.1, h.2)) with
        | none => rfl
        | some el =>
          exfalso
          have ht := List.find?_some hf'
          simp only [beq_iff_eq] at ht
          obtain ⟨⟨l', -, hq', ht'⟩, -⟩ := hsd el (List.mem_of_find?_eq_some hf')
          rw [ht] at ht'
          simp only [acdTag, Prod.mk.injEq] at ht'
          obtain ⟨-, hc'⟩ := (acdQualAt_iff _ _ _ _ _).1 hq'
          simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_le] at hk
          rw [ht'.1, ht'.2, hk.1] at hc'
          exact absurd (hc' (by rw [her]; exact hk.2)) (by simp)

omit [SampleableType Kt] [Fintype Rand] [Nonempty Rand] [DecidableEq W] [DecidableEq Ct] in
/-- The corruption answer of the header-aware construction under the restricted gate is that of
the view. -/
theorem acdIDHdr_expose (msg : ACDHdr Msg → W × W → W × W)
    (s : SMSchemeSt (ACDIDSt Sc RK Sa Msg Kt) (Msg × ℕ) × SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)
    (p : CKAParty) (hs : ACDIDHdrInv G pub₀ cut s)
    (hc : s.2.storeClear (ckaShadow s.1.ck) p = true) :
    (acdIDHdrSM C R G DH hdrAD pub₀ pnOk maxSkip maxStored).expose (s.1.ck.st p) =
      (acdIDViewAt G maxSkip maxStored msg pub₀ cut).leak s.2 (ckaShadow s.1.ck) p
        (s.1.ck.st p).base := by
  obtain ⟨hep, her, hpS, hns, hnr, hrp, -, -, hsd, hcp⟩ := hs.party p
  have hE : ∀ el ∈ (s.1.ck.st p).store, el.1 = (s.1.ck.st p).er := by
    intro el hel
    obtain ⟨⟨l, hl, hq, ht⟩, -⟩ := hsd el hel
    simp only [acdTag, ACDIDSt.tag, Prod.mk.injEq] at ht
    have hq := (acdQual_iff _ _ _ _).1 (acdQual_of_acdQualAt hq)
    have hcl := List.all_eq_true.1 hc l hl
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hcl
    rw [← her] at hcl
    rcases hcl with (h1 | h1) | h1
    · simp [hq.1] at h1
    · exact absurd h1 hq.2.1
    · omega
  simp only [acdIDHdrSM, acdIDViewAt]
  rw [hpS, hns, hep, hrp, hnr, her]
  congr 1
  funext t
  unfold ACDIDSt.lookup
  rw [hnr, her] at hsd hcp
  rw [her] at hE
  by_cases hex : ∃ el ∈ (s.1.ck.st p).store, ACDIDSt.tag el = t
  · obtain ⟨el', hel', ht'⟩ := List.find?_isSome.1 (List.find?_isSome.2 (by
      obtain ⟨el, hel, ht⟩ := hex
      exact ⟨el, hel, by simp [ht]⟩) : ((s.1.ck.st p).store.find? fun el =>
        ACDIDSt.tag el == t).isSome = true)
    obtain ⟨el0, hel0⟩ := Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨el', hel', ht'⟩ :
      ((s.1.ck.st p).store.find? fun el => ACDIDSt.tag el == t).isSome = true)
    have hm0 := List.mem_of_find?_eq_some hel0
    have ht0 := List.find?_some hel0
    simp only [beq_iff_eq] at ht0
    obtain ⟨⟨l, hl, hq, hlt⟩, hkey⟩ := hsd el0 hm0
    rw [hel0, Option.map_some]
    have h1 : t.1 = smRecvEpoch (ckaShadow s.1.ck) p := by rw [← ht0]; exact hE el0 hm0
    rw [ite_eq_left ⟨h1, List.any_eq_true.2 ⟨l, hl, by simp [hq, hlt, ht0]⟩⟩]
    rw [← hkey (hE el0 hm0), ← ht0]
    rfl
  · have hnone : ((s.1.ck.st p).store.find? fun el => ACDIDSt.tag el == t) = none := by
      rw [List.find?_eq_none]
      intro el hel h
      exact hex ⟨el, hel, by simpa using h⟩
    rw [hnone, Option.map_none, ite_eq_right]
    rintro ⟨-, hany⟩
    obtain ⟨l, hl, hlq⟩ := List.any_eq_true.1 hany
    simp only [Bool.and_eq_true, beq_iff_eq] at hlq
    obtain ⟨el, hel, het⟩ := List.mem_map.1 (hcp l hl hlq.1)
    exact hex ⟨el, hel, het.trans hlq.2⟩

/-! ### The construction `acdIDSM` as an instance -/

omit [SampleableType Kt] [SampleableType W] [SampleableType Ct] [Fintype RK] [Nonempty RK]
  [DecidableEq Msg] [DecidableEq W] [DecidableEq Ct] in
/-- The invariant holds at the initial states. -/
theorem acdID_inv_init (i : Msg × SMPartySt Sc RK Sa × SMPartySt Sc RK Sa) :
    ACDIDInv G (SMSchemeSt.init ((i.1, 0), ACDIDSt.embed i.2.1, ACDIDSt.embed i.2.2),
      (SMIDAux.init (i.1, 0) : SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)) :=
  acdIDHdr_inv_init G (fun _ => default) (fun _ _ => none) i

omit [SampleableType Kt] [SampleableType W] [SampleableType Ct] [Fintype RK] [Nonempty RK]
  [DecidableEq Msg] [DecidableEq W] [DecidableEq Ct] in
/-- The invariant depends on the bookkeeping through the log and the opened epochs only. -/
theorem acdID_inv_aux
    (s : SMSchemeSt (ACDIDSt Sc RK Sa Msg Kt) (Msg × ℕ) × SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)
    (x : SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct) (hs : ACDIDInv G s) (hl : x.log = s.2.log)
    (hp : x.pubs = s.2.pubs) : ACDIDInv G (s.1, x) :=
  acdIDInvAt_aux G s x hs hl hp

omit [SampleableType Kt] [Fintype Rand] [Nonempty Rand] [DecidableEq W] [DecidableEq Ct] in
/-- Opening an epoch keeps the invariant. -/
theorem acdID_inv_ratchet
    (s : SMSchemeSt (ACDIDSt Sc RK Sa Msg Kt) (Msg × ℕ) × SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)
    (hs : ACDIDInv G s) (p : CKAParty) (hc : s.1.ck.canSend p = true) (r : Rand) :
    ACDIDInv G (⟨s.1.ck.sent p ((acdIDSM C R G D dec enc maxSkip maxStored).ratchet
        (s.1.ck.st p) r).1 ((acdIDSM C R G D dec enc maxSkip maxStored).ratchet (s.1.ck.st p) r).2,
        s.1.done⟩,
      { s.2 with pubs := (s.1.ck.t p + 1,
        ((acdIDSM C R G D dec enc maxSkip maxStored).ratchet (s.1.ck.st p) r).2) ::
          s.2.pubs }) :=
  acdIDHdr_inv_ratchet C R G (aeadEncComapAD D fun ah => dec (enc ah.2 ah.1)) Prod.mk
    (fun _ => default) (fun _ _ => true) (fun _ _ => none) maxSkip maxStored s hs p hc r

omit [SampleableType Kt] [Fintype Rand] [Nonempty Rand] [DecidableEq W] [DecidableEq Ct] in
/-- Receiving keeps the invariant. -/
theorem acdID_inv_recv
    (s : SMSchemeSt (ACDIDSt Sc RK Sa Msg Kt) (Msg × ℕ) × SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)
    (hs : ACDIDInv G s) (p : CKAParty) (hc : s.1.ck.canRecv p = true) :
    ACDIDInv G (⟨s.1.ck.recvd p ((acdIDSM C R G D dec enc maxSkip maxStored).recv
        (s.1.ck.st p) s.1.ck.msg), s.1.done⟩, s.2) := by
  have h := acdIDHdr_inv_recv C R G (aeadEncComapAD D fun ah => dec (enc ah.2 ah.1)) Prod.mk
    (fun _ => default) (fun _ _ => true) (fun _ _ => none) maxSkip maxStored s hs p hc
  rwa [show acdCutRecv true (fun _ _ => none) p (s.1.ck.st p).er (s.1.ck.st p).nr =
    fun _ _ => none from funext fun q => funext fun e =>
      acdCutRecv_none _ _ _ _ _ rfl (fun _ _ => rfl) q e] at h

omit [SampleableType Kt] [Fintype Rand] [Nonempty Rand] [DecidableEq W] [DecidableEq Ct] in
/-- Sending, with any ciphertext logged, keeps the invariant. -/
theorem acdID_inv_send
    (s : SMSchemeSt (ACDIDSt Sc RK Sa Msg Kt) (Msg × ℕ) × SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)
    (hs : ACDIDInv G s) (p : CKAParty) (hc : ckaSender (s.1.ck.t p) = p) (m : W × W)
    (y : ACDIDSt Sc RK Sa Msg Kt × Ct)
    (hy : (acdIDSM C R G D dec enc maxSkip maxStored).send (s.1.ck.st p) m = some y)
    (c : Ct) (b : Bool) :
    ACDIDInv G (s.1.upd p y.1 b,
      s.2.record (s.1.ck.t p) (s.1.ck.st p).ns m ((s.1.ck.st p).pubS, (s.1.ck.st p).ns) c) :=
  acdIDHdr_inv_send C R G (aeadEncComapAD D fun ah => dec (enc ah.2 ah.1)) Prod.mk
    (fun _ => default) (fun _ _ => true) (fun _ _ => none) maxSkip maxStored s hs p hc m y hy c b

omit [SampleableType Kt] [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct]
  [Fintype RK][Nonempty RK] in
/-- A delivery from the log with a successful key lookup keeps the invariant. -/
theorem acdID_inv_mark
    (s : SMSchemeSt (ACDIDSt Sc RK Sa Msg Kt) (Msg × ℕ) × SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)
    (hs : ACDIDInv G s) (p : CKAParty) (h : ACDHdr Msg) (ad : W) (c : Ct) (e : ℕ)
    (he : s.2.epochOf (ckaShadow s.1.ck) p h.1 = some e) (l : SMIDLogEntry W (ACDHdr Msg) Ct)
    (hl : s.2.findEntry e h ad c = some l) (y : ACDIDSt Sc RK Sa Msg Kt × Kt)
    (hy : acdIDRKey G maxSkip maxStored (s.1.ck.st p) h = some y) (b : Bool) :
    ACDIDInv G (s.1.upd p y.1 b, s.2.mark e h ad c) :=
  acdIDHdr_inv_mark G (fun _ => default) (fun _ _ => none) maxSkip maxStored s hs p h ad c e he l
    hl y hy b

omit [SampleableType Kt] [Fintype Rand] [Nonempty Rand] in
/-- A delivery with decryption from the log keeps the invariant. -/
theorem acdID_inv_deliver (ΔFS ΔPCS : ℕ)
    (s : SMSchemeSt (ACDIDSt Sc RK Sa Msg Kt) (Msg × ℕ) × SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)
    (hs : ACDIDInv G s) (p : CKAParty) (h : ACDHdr Msg) (ad : W) (c : Ct) :
    ACDIDInv G (smIDDeliver (acdIDSM C R G D dec enc maxSkip maxStored) ΔFS ΔPCS (fun _ => true)
      s p h ad c).2 :=
  acdIDHdr_inv_deliver C R G (aeadEncComapAD D fun ah => dec (enc ah.2 ah.1)) Prod.mk
    (fun _ => default) (fun _ _ => true) (fun _ _ => none) maxSkip maxStored ΔFS ΔPCS s hs p h ad c

omit [SampleableType Kt] in
/-- The oracle with decryption from the log keeps the invariant. -/
theorem acdID_inv_step (ΔFS ΔPCS t : ℕ) (idealC : Bool)
    (s : SMSchemeSt (ACDIDSt Sc RK Sa Msg Kt) (Msg × ℕ) × SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)
    (d : SMIDQuery W (ACDHdr Msg) Ct) (hs : ACDIDInv G s)
    (z) (hz : z ∈ (smIDOracleAt (acdIDSM C R G D dec enc maxSkip maxStored) ΔFS ΔPCS t idealC
      (fun _ => true) s d).support) : ACDIDInv G z.2 := by
  obtain ⟨cut', h, hcut⟩ := acdIDHdr_inv_step C R G (aeadEncComapAD D fun ah => dec (enc ah.2 ah.1))
    Prod.mk (fun _ => default) (fun _ _ => true) (fun _ _ => none) maxSkip maxStored ΔFS ΔPCS t
    idealC s d hs z hz
  obtain rfl : cut' = fun _ _ => none :=
    funext fun q => funext fun e => hcut (fun _ _ => rfl) (fun _ _ => rfl) q e
  exact h

omit [SampleableType Kt] [SampleableType W] [SampleableType Ct] [Fintype RK] [Nonempty RK] in
/-- The success of the key lookup at a matching log entry is that of the view. -/
theorem acdID_rkeyOk_eq
    (s : SMSchemeSt (ACDIDSt Sc RK Sa Msg Kt) (Msg × ℕ) × SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)
    (p : CKAParty) (h : ACDHdr Msg) (e : ℕ) (ad : W) (c : Ct) (hs : ACDIDInv G s)
    (he : s.2.epochOf (ckaShadow s.1.ck) p h.1 = some e) (hf : (s.2.findEntry e h ad c).isSome) :
    (acdIDRKey G maxSkip maxStored (s.1.ck.st p) h).isSome =
      (acdIDView (Sc := Sc) (RK := RK) G maxSkip maxStored enc).rkeyOk s.2 (ckaShadow s.1.ck) p
        h :=
  acdIDHdr_rkeyOk_eq G (fun _ => default) (fun _ _ => none) maxSkip maxStored
    (fun h m => (m.1, enc h m.2)) s p h e ad c hs he hf

omit [SampleableType Kt] [Fintype Rand] [Nonempty Rand] [DecidableEq W] [DecidableEq Ct] in
/-- The corruption answer under the restricted gate is that of the view. -/
theorem acdID_expose
    (s : SMSchemeSt (ACDIDSt Sc RK Sa Msg Kt) (Msg × ℕ) × SMIDAux W (Msg × ℕ) (ACDHdr Msg) Ct)
    (p : CKAParty) (hs : ACDIDInv G s)
    (hc : s.2.storeClear (ckaShadow s.1.ck) p = true) :
    (acdIDSM C R G D dec enc maxSkip maxStored).expose (s.1.ck.st p) =
      (acdIDView G maxSkip maxStored enc).leak s.2 (ckaShadow s.1.ck) p (s.1.ck.st p).base :=
  acdIDHdr_expose C R G (aeadEncComapAD D fun ah => dec (enc ah.2 ah.1)) Prod.mk
    (fun _ => default) (fun _ _ => true) (fun _ _ => none) maxSkip maxStored
    (fun h m => (m.1, enc h m.2)) s p hs hc

omit [SampleableType Kt] in
/-- **The ACD construction with headers over the ACD construction.** -/
theorem acdIDSM_over :
    (acdIDSM C R G D dec enc maxSkip maxStored).Over (acdIDBase C R G D dec) ACDIDSt.base
      Prod.fst ACDIDSt.embed (acdIDView G maxSkip maxStored enc) (ACDIDInv G) where
  init := rfl
  proj_emb _ := rfl
  proj_pubInit _ := rfl
  proj_pub _ _ _ _ := rfl
  ratchet _ _ := rfl
  ratchet_pub s p r hs _ := Prod.ext rfl (hs.party p).ns
  recv _ _ := rfl
  send x m := by
    cases hs : x.base.snd <;>
      simp [acdIDSM, acdIDHdrSM, acdIDHdrBase, acdIDBase, acdSMAD, acdIDView, acdIDViewAt,
        aeadEncComapAD, hs]
  idealCt := rfl
  rkey x h y hy := acdIDRKey_base G maxSkip maxStored x h y hy
  inv_init i := acdID_inv_init G i
  inv_step ΔFS ΔPCS t idealC s d hs z hz :=
    acdID_inv_step C R G D dec enc maxSkip maxStored ΔFS ΔPCS t idealC s d hs z hz
  hdr_eq s p hs := Prod.ext (hs.party p).pubS (hs.party p).ns
  rkeyOk_eq s p h e ad c hs he hf := acdID_rkeyOk_eq G enc maxSkip maxStored s p h e ad c hs he hf
  expose s p hs hc := acdID_expose C R G D dec enc maxSkip maxStored s p hs hc

omit [SampleableType Kt] in
/-- **Immediate decryption of the ACD construction with headers** from its integrity and the
corruption game of the ACD construction at the reduction `smIDRed`. -/
theorem acdIDSM_idAdvantage_le (ΔFS ΔPCS : ℕ)
    (A : SMIDAdv (Msg × ℕ) W (ACDHdr Msg) Ct (ACDIDLeak Sc RK Sa Msg Kt)) :
    (acdIDSM C R G D dec enc maxSkip maxStored).idAdvantage ΔFS ΔPCS A ≤
      (acdIDSM C R G D dec enc maxSkip maxStored).intAdvantage ΔFS ΔPCS A +
        (acdIDBase C R G D dec).corruptAdvantage ΔFS ΔPCS
          (smIDRed (acdIDSM C R G D dec enc maxSkip maxStored)
            (acdIDView G maxSkip maxStored enc) ΔFS ΔPCS A) :=
  SMIDScheme.idAdvantage_le (acdIDSM_over C R G D dec enc maxSkip maxStored) ΔFS ΔPCS A

end Over

end CatCrypt.Crypto.Messaging
