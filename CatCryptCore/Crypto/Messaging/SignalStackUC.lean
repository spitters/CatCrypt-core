/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SignalStack
public import CatCryptCore.Crypto.UCDeferred
public import CatCryptCore.Crypto.UCLoopSplit
public import CatCryptCore.Crypto.UCRoundHybrid
import CatCryptCore.Tactics.DeriveTimed

/-!
# The Signal stack realizes an ideal secure channel

The Signal stack runs X3DH and keys the double ratchet with the session key of X3DH
(`SignalStack`). This module proves that the stack realizes an ideal secure-channel
functionality behind a simulator, in the sense of Canetti and Krawczyk (Eurocrypt 2002, `F_SC`
from `F_KE`). The secure-messaging step uses that `F_AKE` delivers to a completed, unexposed
session a key that it samples and that no event reveals, and the adversary key to an exposed
session; the bound has no real-or-random term of the key.

**The ideal functionality.** `F_SC realV idealV` has the state and the adversary port of
`F_AKE (SPComp.sample K) true` (notices, adaptive corruption, `newKey`, `newKeyUnlinked`), except
that a session that completes without exposure stores the placeholder key `default`. Its honest
port opens sessions and answers `getKey` with the secure-messaging view of the session: the
ideal view `idealV` (for the ratchet, `sm_ideal C msgs`: the public CKA transcript and uniform
ciphertexts) for a completed session, the real view `realV k` (for the ratchet,
`smRealAt C R Gp D msgs k`) under the adversary key `k` for an exposed session, and nothing for a
session without a key.

**The real world.** `(x3dhReal G).seq (smLayer (smRealAt C R Gp D msgs))`: the real X3DH
protocol, and the ratchet keyed by the session key of every `getKey` answer.

**The simulator.** `scSim G` is the X3DH simulator `simProt G` running over `F_SC` (`simSC G`):
it keeps a copy of the real state, draws the long-term and session secrets, forwards the honest
events, answers `poll`, `pub`, `ephPub` and `kdf` on its copy, refuses or forwards `corrupt`
under the static rule of X3DH, and on `complete` and `send` passes the key-derivation value to
`newKey` for an exposed session and a placeholder key to `newKey` or `newKeyUnlinked` otherwise.
The answers of `F_SC` on the honest port pass unchanged; the simulator never reads them
(`simSC_opaque`).

**The proof.** The cascade theorem of the X3DH square (`SignalStack.signal_stack_realizes`)
replaces `x3dhReal G` by `F_AKE` behind `x3dhSim G`. Behind the simulator, this stack is
`simSC G` over `FR realV`, the functionality `F_AKE` whose honest port answers `getKey` by the
ratchet keyed by the stored key (`stack_ideal_stepMap`, distance `0`). Over the simulator, the
step from `FR realV` to `F_SC realV idealV` is a statement about the subroutine at the reduced
environment (`MultiHybrid.adv_withSub`), proved by a hybrid argument over the keys of the run
(`FR_realizes_F_SC`). The hybrid world `hyb i` keeps the keys outside the records of `F_AKE`, by
index: the key created at the non-idle activation `n` has index `n`; the keys of index below `i`
are read ideally, the others really. Then
* `hyb 0` is `FR realV` (`world_zero_stepMap`, filling the keys back into the records);
* `hyb i` and `hyb (i + 1)` differ in the key `i` (`hyb_step`): its draw moves from its creation
  to the start of the run (`run_world_create`, deferred sampling, `UCDeferred.run_deferred`),
  the first ratchet run on it moves to the start of the run (`run_world_read`), the pair is the
  real secure-messaging game `sm_real`, and the world that answers the first read of the key `i`
  by the challenge view is the reduction `hopRed i Z`; a later read of the key `i` is the bad
  event (`world_upto_reuse`);
* `hyb n` is `F_SC` on runs of at most `n` activations (`world_end`, `world_end_prBad`).

**The reuse of a key.** `smLayer` runs the ratchet afresh at every `getKey`, so a key read twice
(by the same session or by its partner) keys two ratchet runs with one root key. The
secure-messaging game `sm_real` uses a root key once, and the views of two runs on one root key
are not bounded by `SM_Advantage`: a root KDF that is a secure PRG on a uniform seed may give
correlated outputs on two seeds `(rk, I)`, `(rk, I')` that share `rk`. The bound therefore
contains, per key `i`, the probability `prBad (hyb i) (reuse i) Z` that the key `i` is read twice
in the world `hyb i`; it is `0` for environments that read each session key at most once.

## Main definitions

* `chanOut`, `chanHon`: the honest port of a channel over the state of `F_AKE`.
* `FR`: `F_AKE` followed by the ratchet layer, as one functionality.
* `F_SC`, `scView`: the ideal secure channel.
* `WSt`, `world`, `hyb`, `chalWorld`: the hybrid worlds; `WInv` their invariant.
* `hopRed`: the reduction of a step of the hybrid argument.
* `scBound`, `signalBound`: the bounds.
* `keyLayer`: the key layer over a key exchange with any adversary outputs.
* `FwdData`, `IsFwd`: forwarding simulators over `F_AKE`.
* `simSCOver`, `chanSim`: a forwarding simulator over `F_SC`; `simSC`, `scSim`: the simulator of
  the Signal stack.

## Main results

* `FR_realizes_F_SC`: `FR realV` realizes `F_SC realV idealV` with `scBound`.
* `hyb_step`: one step of the hybrid argument.
* `stack_realizes_FSC_of`: **KE-then-channel composition**: a key exchange that realizes `F_AKE`
  behind an opaque forwarding simulator `π`, followed by the key layer, realizes `F_SC` behind
  `chanSim π F`.
* `stack_ideal_stepMap_of`, `stack_ideal_stepMap`: a forwarding simulator over `F_AKE` followed
  by the key layer is its wrapper over `FR`.
* `simSC_opaque`: opacity of the simulator.
* `signal_stack_realizes_FSC`: **the Signal stack realizes `F_SC` behind `scSim G`** with the gap
  Diffie–Hellman bound and the sum over the keys of the secure-messaging advantages of `hopRed`
  and of the reuse probabilities.
* `hopRed.tree`, `hopRed.compile_tree`, `hopRed.tree.timed`, `hopRed.timeBound_timed`: the
  tree of `hopRed`, its costed form by `derive_timed` and its time.

**Keys with a public datum.** A `KeySplit K Ks D` writes a key as a secret part and a datum that
the key exchange makes public to both partners (for X3DH with the signed prekey, the prekey
secret of the responder). `F_SCK sp realV idealV` answers a completed session by the ideal view
`idealV d` at its datum `d`, and `F_SC` is `F_SCK` at the split without a datum. The hybrid
worlds `worldK` are generic in the split, the fresh-key kernel and the creation kernel; the old
worlds and their lemmas are their instances. In the step `i` the datum of the key `i` is chosen
during the run, so the challenge cannot be drawn before the run: the world draws the secret part
of the key `i` at its first read (`run_world_createK`, `run_world_readK`, `world_upto_reuseK`),
the run is split at that read (`run_world_read_atK`, `UCLoopSplit.run_deferred_at`), and the
reduction `hopRedK i Z` is a two-stage adversary `CDAdv` whose first stage outputs the split
point and the datum and whose second stage guesses from the challenge view.

* `KeySplit`, `F_SCK`, `FRK`, `worldK`, `hybK`, `CDAdv`, `hopRedK`, `scBoundK`.
* `hyb_stepK`, `FRK_realizes_F_SCK`: the hybrid argument at a split, with the chosen-datum
  advantage of `hopRedK` per key.
* `stack_ideal_stepMap_ofK`, `stack_realizes_FSCK_of`: **KE-then-channel composition with a
  datum**, from the realization of the stack's real part through the key layer.

## References

* R. Canetti, H. Krawczyk, *Universally composable notions of key exchange and secure
  channels*, Eurocrypt 2002.
* M. Marlinspike, T. Perrin, *The X3DH key agreement protocol*, 2016; *The double ratchet
  algorithm*, 2016.
* J. Alwen, S. Coretti, Y. Dodis, *The double ratchet: security notions, proofs, and
  modularization for the Signal protocol*, Eurocrypt 2019.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Messaging.SignalStackUC

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Messaging
open CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.UCCoupling
open CatCrypt.Crypto.AKE.X3DHSquare CatCrypt.Crypto.AKE.X3DHSquareGDH
open CatCrypt.Crypto.Messaging.SignalStack CatCrypt.Crypto.PAKE.DHExtract
open CatCrypt.Crypto.Assumptions
open PubView (eqView)
open scoped ENNReal

/-! ## Channel outputs of the honest port -/

section Chan

variable {K V : Type}

/-- The answer on the honest port to `getKey` at the session `x`: the view `f r k` when the
session `x` has the record `r` and the key `k`, and no key otherwise. -/
noncomputable def chanOut (f : Rec K → K → SPComp V) (t : St K) (x : Inst) :
    SPComp (HOut V) :=
  match t.recs x with
  | some r =>
    match r.key with
    | some k => SPComp.map (fun v => HOut.key (some v)) (f r k)
    | none => SPComp.pure (.key none)
  | none => SPComp.pure (.key none)

/-- The honest port of a channel functionality over the state of `F_AKE`: `newSession` as in
`F_AKE`, and `getKey` answers by `chanOut f`. -/
noncomputable def chanHon (f : Rec K → K → SPComp V) : Sys (St K) HEv (HOut V) where
  init := initSt
  step t e := match e with
    | .newSession sid pid peer role => SPComp.pure (addSession t (sid, pid) peer role, .ok)
    | .getKey sid pid => SPComp.map (fun o => (t, o)) (chanOut f t (sid, pid))

end Chan

/-! ## Keys with a public datum -/

/-- **A key with a public datum**: a key of type `K` is a secret part of type `Ks` together with
a datum of type `D` that the key exchange makes public to both partners (for X3DH with the
signed prekey, the prekey secret of the responder). `key s d` is the key of the secret part `s`
and the datum `d`, and `dat k` the datum of the key `k`. -/
structure KeySplit (K Ks D : Type) where
  /-- The key of a secret part and a datum. -/
  key : Ks → D → K
  /-- The datum of a key. -/
  dat : K → D
  /-- The datum of `key s d` is `d`. -/
  dat_key : ∀ s d, dat (key s d) = d

namespace KeySplit

variable {K Ks D V : Type}

/-- The split without a datum: the key is its own secret part. -/
def trivial (K : Type) : KeySplit K K Unit where
  key s _ := s
  dat _ := ()
  dat_key _ _ := rfl

/-- The stored stand-in of the key `k`: the default secret part with the datum of `k`. -/
def ph [Inhabited Ks] (sp : KeySplit K Ks D) (k : K) : K := sp.key default (sp.dat k)

/-- The fresh-key kernel of the split: on the proposal `p`, a uniform secret part with the
datum of `p`. -/
noncomputable def fresh [Fintype Ks] [Nonempty Ks] (sp : KeySplit K Ks D) (p : K) : SPComp K :=
  SPComp.map (fun s => sp.key s (sp.dat p)) (SPComp.sample Ks)

/-- The real view at the datum `d`: the view `realV` keyed by a uniform secret part with the
datum `d`. -/
noncomputable def real [Fintype Ks] [Nonempty Ks] (sp : KeySplit K Ks D) (realV : K → SPComp V)
    (d : D) : SPComp V :=
  SPComp.bind (SPComp.sample Ks) fun s => realV (sp.key s d)

/-- The datum of the stand-in of a key is the datum of the key. -/
theorem dat_ph [Inhabited Ks] (sp : KeySplit K Ks D) (k : K) : sp.dat (sp.ph k) = sp.dat k :=
  sp.dat_key _ _

end KeySplit

/-! ## The real stack over `F_AKE` and the ideal secure channel -/

section Func

variable {K V Ks D : Type} [Fintype K] [Nonempty K] [Inhabited K]

/-- **`F_AKEK fresh` followed by the ratchet layer**, as one functionality: `F_AKEK fresh` with
unlinked delivery, whose honest port answers `getKey` at a session with the key `k` by the view
`realV k` of the ratchet keyed by `k`. -/
noncomputable def FRK (fresh : K → SPComp K) (realV : K → SPComp V) :
    Sys (St K) (HEv ⊕ AEv K) (HOut V ⊕ AOut) :=
  Sys.ofPorts (chanHon fun _ k => realV k) (advSysK true true fresh)

/-- **`F_AKE` followed by the ratchet layer**, as one functionality: `F_AKE` with uniform keys
and unlinked delivery, whose honest port answers `getKey` at a session with the key `k` by the
view `realV k` of the ratchet keyed by `k`. -/
noncomputable def FR (realV : K → SPComp V) : Sys (St K) (HEv ⊕ AEv K) (HOut V ⊕ AOut) :=
  FRK (fun _ => SPComp.sample K) realV

/-- The view of the ideal channel with a datum at the session with the record `r` and the key
`k`: the ideal view `idealV (dat k)` at the datum of `k` at a session that completed with a key
chosen by the functionality, and the real view `realV k` at a session that holds the adversary
key `k`. -/
noncomputable def scViewK (sp : KeySplit K Ks D) (realV : K → SPComp V) (idealV : D → SPComp V)
    (r : Rec K) (k : K) : SPComp V :=
  if r.status = .completed then idealV (sp.dat k) else realV k

/-- The view of the ideal channel at the session with the record `r` and the key `k`: the ideal
view `idealV` at a session that completed with a key chosen by the functionality, and the real
view `realV k` at a session that holds the adversary key `k`. -/
noncomputable def scView (realV : K → SPComp V) (idealV : SPComp V) (r : Rec K) (k : K) :
    SPComp V :=
  scViewK (KeySplit.trivial K) realV (fun _ => idealV) r k

/-- **The ideal secure channel with a datum `F_SCK`**. The ports and the state of `F_AKE`: the
adversary port schedules sessions, corrupts parties and delivers keys exactly as in `F_AKE`
with unlinked delivery, except that a session that completes without exposure stores the
placeholder `sp.ph p` of the proposal `p` (the default secret part and the datum of `p`); the
honest port opens sessions and, on `getKey`, outputs the secure-messaging view of the session:
the ideal view `idealV d` at the datum `d` of the session for a completed session, and the real
view `realV k` under the adversary key `k` for an exposed session. -/
noncomputable def F_SCK [Inhabited Ks] (sp : KeySplit K Ks D) (realV : K → SPComp V)
    (idealV : D → SPComp V) : Sys (St K) (HEv ⊕ AEv K) (HOut V ⊕ AOut) :=
  Sys.ofPorts (chanHon (scViewK sp realV idealV))
    (advSysK true true fun p => SPComp.pure (sp.ph p))

/-- **The ideal secure channel `F_SC`** (Canetti–Krawczyk, `F_SC` from `F_KE`). The ports and
the state of `F_AKE`: the adversary port schedules sessions, corrupts parties and delivers keys
exactly as in `F_AKE` with unlinked delivery, except that a session that completes without
exposure stores no key (the placeholder `default`); the honest port opens sessions and, on
`getKey`, outputs the secure-messaging view of the session: the ideal view `idealV` for a
completed session, and the real view `realV k` under the adversary key `k` for an exposed
session. It is `F_SCK` at the split without a datum. -/
noncomputable def F_SC (realV : K → SPComp V) (idealV : SPComp V) :
    Sys (St K) (HEv ⊕ AEv K) (HOut V ⊕ AOut) :=
  F_SCK (KeySplit.trivial K) realV (fun _ => idealV)

end Func

/-! ## The hybrid worlds -/

section World

variable {K V : Type} [Fintype K] [Nonempty K] [Inhabited K]

/-- The state of a hybrid world: the state of the functionality, the index of the key of each
completed session, the number of non-idle activations, the number of reads of each key and the
key of each index. A key created at the activation `n` has index `n`. -/
structure WSt (K : Type) where
  /-- The state of the functionality; a completed session holds the placeholder key. -/
  st : St K
  /-- The index of the key of a completed session. -/
  ix : Inst → Option ℕ
  /-- The number of non-idle activations. -/
  steps : ℕ
  /-- The number of reads of the key of each index. -/
  rd : ℕ → ℕ
  /-- The key of each index. -/
  kv : ℕ → K

/-- The initial state of a hybrid world. -/
def WSt.init : WSt K := ⟨initSt, fun _ => none, 0, fun _ => 0, fun _ => default⟩

/-- Whether an event is the idle event of the adversary. -/
def isIdle : HEv ⊕ AEv K → Bool
  | .inr .idle => true
  | _ => false

/-- Whether an event delivers a key. -/
def isNewKey : HEv ⊕ AEv K → Bool
  | .inr (.newKey _ _ _) => true
  | .inr (.newKeyUnlinked _ _ _) => true
  | _ => false

/-- The key proposed by an event: the key of `newKey` and `newKeyUnlinked`, and `default`
otherwise. -/
def propOf : HEv ⊕ AEv K → K
  | .inr (.newKey _ _ k) => k
  | .inr (.newKeyUnlinked _ _ k) => k
  | _ => default

/-- The state of the functionality after an event, with the stand-in `sp.ph k` of the proposal
`k` for the sessions that complete without exposure. -/
def stNextK {Ks D : Type} [Inhabited Ks] (sp : KeySplit K Ks D) (t : St K) :
    HEv ⊕ AEv K → St K
  | .inl (.newSession sid pid peer role) => addSession t (sid, pid) peer role
  | .inl (.getKey _ _) => t
  | .inr .idle => t
  | .inr .poll => (pollStep t).1
  | .inr (.corrupt pid) => corruptStep t pid
  | .inr (.impersonate _ _) => t
  | .inr (.newKey sid pid k) => newKeyStep t (sid, pid) k (sp.ph k)
  | .inr (.newKeyUnlinked sid pid k) => newKeyFreshStep t (sid, pid) k (sp.ph k)

/-- The state of the functionality after an event, with the key `default` for the sessions
that complete without exposure. -/
def stNext (t : St K) : HEv ⊕ AEv K → St K := stNextK (KeySplit.trivial K) t

/-- The index given by `newKey` at the session `x`: the index of the completed partner, or the
new index `n`, to a session without a key that is not exposed. -/
def newKeyIx (t : St K) (ix : Inst → Option ℕ) (n : ℕ) (x : Inst) : Inst → Option ℕ :=
  match t.recs x with
  | some r =>
    if r.key.isNone ∧ ¬ Exposed t x r then
      Function.update ix x (match t.recs (x.1, r.peer) with
        | some p => if Partner x r p then ix (x.1, r.peer) else some n
        | none => some n)
    else ix
  | none => ix

/-- The index given by `newKeyUnlinked` at the session `x`: the new index `n`, to a session
without a key that is not exposed. -/
def newKeyFreshIx (t : St K) (ix : Inst → Option ℕ) (n : ℕ) (x : Inst) : Inst → Option ℕ :=
  match t.recs x with
  | some r => if r.key.isNone ∧ ¬ Exposed t x r then Function.update ix x (some n) else ix
  | none => ix

/-- The indices after an event. -/
def ixNext (w : WSt K) : HEv ⊕ AEv K → Inst → Option ℕ
  | .inr (.newKey sid pid _) => newKeyIx w.st w.ix w.steps (sid, pid)
  | .inr (.newKeyUnlinked sid pid _) => newKeyFreshIx w.st w.ix w.steps (sid, pid)
  | _ => w.ix

/-- The read counts after an event: `getKey` at a session with the index `j` reads the key
`j`. -/
def rdNext (w : WSt K) : HEv ⊕ AEv K → ℕ → ℕ
  | .inl (.getKey sid pid) =>
    match w.ix (sid, pid) with
    | some j => Function.update w.rd j (w.rd j + 1)
    | none => w.rd
  | _ => w.rd

/-- The state after an event at the split `sp`, with the drawn key `kf` stored at the index
`w.steps` when the event delivers a key. -/
def wNextK {Ks D : Type} [Inhabited Ks] (sp : KeySplit K Ks D) (w : WSt K) (e : HEv ⊕ AEv K)
    (kf : K) : WSt K where
  st := stNextK sp w.st e
  ix := ixNext w e
  steps := w.steps + (if isIdle e then 0 else 1)
  rd := rdNext w e
  kv := if isNewKey e then Function.update w.kv w.steps kf else w.kv

/-- The state after an event, with the drawn key `kf` stored at the index `w.steps` when the
event delivers a key. -/
def wNext (w : WSt K) (e : HEv ⊕ AEv K) (kf : K) : WSt K := wNextK (KeySplit.trivial K) w e kf

/-- The draw of the hybrid world `i` with the fresh-key kernel `fr` and the creation kernel
`cre`: at a key delivery, `cre` at the activation `i` and `fr` otherwise, at the proposal. -/
noncomputable def wDrawK (fr : K → SPComp K) (i : ℕ) (cre : K → SPComp K) (w : WSt K)
    (e : HEv ⊕ AEv K) : SPComp K :=
  if isNewKey e then (if w.steps = i then cre (propOf e) else fr (propOf e))
  else SPComp.pure default

section Gen

variable {Ks D : Type} [Inhabited Ks] (sp : KeySplit K Ks D)

/-- The view of the key with the index `j` in the hybrid world `i` at the split `sp`: ideal at
the datum of the key below `i`, real above `i`, and at `i` the first read by `rd1` and the later
reads by `rd2`. -/
noncomputable def readOutK (realV : K → SPComp V) (idealD : D → SPComp V) (i : ℕ)
    (rd1 rd2 : K → SPComp V) (w : WSt K) (j : ℕ) : SPComp V :=
  if j < i then idealD (sp.dat (w.kv j))
  else if j = i then (if w.rd i = 0 then rd1 (w.kv i) else rd2 (w.kv i))
  else realV (w.kv j)

/-- The view of the session `x` in the hybrid world `i` at the split `sp`: the view of its key
index, or the real view of its key when it has no index. -/
noncomputable def wViewK (realV : K → SPComp V) (idealD : D → SPComp V) (i : ℕ)
    (rd1 rd2 : K → SPComp V) (w : WSt K) (x : Inst) : Rec K → K → SPComp V :=
  fun _ k => match w.ix x with
    | some j => readOutK sp realV idealD i rd1 rd2 w j
    | none => realV k

/-- The output of the hybrid world `i` at the split `sp` at an event. -/
noncomputable def wOutK (realV : K → SPComp V) (idealD : D → SPComp V) (i : ℕ)
    (rd1 rd2 : K → SPComp V) (w : WSt K) : HEv ⊕ AEv K → SPComp (HOut V ⊕ AOut)
  | .inl (.newSession _ _ _ _) => SPComp.pure (.inl .ok)
  | .inl (.getKey sid pid) =>
    SPComp.map Sum.inl
      (chanOut (wViewK sp realV idealD i rd1 rd2 w (sid, pid)) w.st (sid, pid))
  | .inr .poll => SPComp.pure (.inr (.notice (pollStep w.st).2))
  | .inr _ => SPComp.pure (.inr .ack)

/-- **The hybrid world `i` at the split `sp`** with the fresh-key kernel `fr`, the creation
kernel `cre` of the key `i` and the reads `rd1`, `rd2` of the key `i`: the draw, the next state
and the output. -/
noncomputable def worldK (fr : K → SPComp K) (realV : K → SPComp V) (idealD : D → SPComp V)
    (i : ℕ) (cre : K → SPComp K) (rd1 rd2 : K → SPComp V) :
    Sys (WSt K) (HEv ⊕ AEv K) (HOut V ⊕ AOut) where
  init := WSt.init
  step w e := SPComp.bind (wDrawK fr i cre w e) fun kf =>
    SPComp.map (fun o => (wNextK sp w e kf, o)) (wOutK sp realV idealD i rd1 rd2 w e)

end Gen

variable (realV : K → SPComp V) (idealV : SPComp V)

/-- The view of the key with the index `j` in the hybrid world `i`: ideal below `i`, real
above `i`, and at `i` the first read by `rd1` and the later reads by `rd2`. -/
noncomputable def readOut (i : ℕ) (rd1 rd2 : K → SPComp V) (w : WSt K) (j : ℕ) : SPComp V :=
  readOutK (KeySplit.trivial K) realV (fun _ => idealV) i rd1 rd2 w j

/-- The view of the session `x` in the hybrid world `i`: the view of its key index, or the
real view of its key when it has no index. -/
noncomputable def wView (i : ℕ) (rd1 rd2 : K → SPComp V) (w : WSt K) (x : Inst) :
    Rec K → K → SPComp V :=
  wViewK (KeySplit.trivial K) realV (fun _ => idealV) i rd1 rd2 w x

/-- The output of the hybrid world `i` at an event. -/
noncomputable def wOut (i : ℕ) (rd1 rd2 : K → SPComp V) (w : WSt K) :
    HEv ⊕ AEv K → SPComp (HOut V ⊕ AOut) :=
  wOutK (KeySplit.trivial K) realV (fun _ => idealV) i rd1 rd2 w

/-- The draw of the hybrid world `i`: at a key delivery, `cre` at the activation `i` and a
uniform key otherwise. -/
noncomputable def wDraw (i : ℕ) (cre : SPComp K) (w : WSt K) (e : HEv ⊕ AEv K) : SPComp K :=
  wDrawK (fun _ => SPComp.sample K) i (fun _ => cre) w e

/-- **The hybrid world `i`** with the creation `cre` of the key `i` and the reads `rd1`, `rd2`
of the key `i`: the draw, the next state and the output. -/
noncomputable abbrev world (i : ℕ) (cre : SPComp K) (rd1 rd2 : K → SPComp V) :
    Sys (WSt K) (HEv ⊕ AEv K) (HOut V ⊕ AOut) :=
  worldK (KeySplit.trivial K) (fun _ => SPComp.sample K) realV (fun _ => idealV) i (fun _ => cre)
    rd1 rd2

/-! ## The invariant of the hybrid worlds -/

/-- The invariant of a state of the functionality with the indices `ix` and the keys `kv`
after `n` activations at the split `sp`: the indices are below `n` and belong to completed
sessions, and a completed session has an index `j` and holds the stand-in `sp.ph (kv j)` of its
key. -/
def WInvPK {Ks D : Type} [Inhabited Ks] (sp : KeySplit K Ks D) (t : St K)
    (ix : Inst → Option ℕ) (kv : ℕ → K) (n : ℕ) : Prop :=
  (∀ x j, ix x = some j → j < n ∧ ∃ r, t.recs x = some r ∧ r.status = .completed) ∧
  (∀ x r, t.recs x = some r → r.status = .completed →
    ∃ j, ix x = some j ∧ r.key = some (sp.ph (kv j)))

/-- The invariant of the hybrid worlds at the split `sp`. -/
def WInvK {Ks D : Type} [Inhabited Ks] (sp : KeySplit K Ks D) (w : WSt K) : Prop :=
  WInvPK sp w.st w.ix w.kv w.steps

/-- The invariant of a state of the functionality with the indices `ix` after `n` activations:
the indices are below `n` and belong to completed sessions, and a completed session holds the
placeholder key and has an index. -/
def WInvP (t : St K) (ix : Inst → Option ℕ) (n : ℕ) : Prop :=
  (∀ x j, ix x = some j → j < n ∧ ∃ r, t.recs x = some r ∧ r.status = .completed) ∧
  (∀ x r, t.recs x = some r → r.status = .completed → r.key = some default ∧ (ix x).isSome)

/-- The invariant of the hybrid worlds: the invariant at the split without a datum. -/
def WInv (w : WSt K) : Prop := WInvK (KeySplit.trivial K) w

omit [Fintype K] [Nonempty K] in
/-- The initial state satisfies the invariant at every split. -/
theorem wInv_initK {Ks D : Type} [Inhabited Ks] (sp : KeySplit K Ks D) :
    WInvK sp (WSt.init : WSt K) := by
  refine ⟨fun x j h => ?_, fun x r h => ?_⟩ <;> simp [WSt.init, initSt] at h

omit [Fintype K] [Nonempty K] in
/-- The initial state satisfies the invariant. -/
theorem wInv_init : WInv (WSt.init : WSt K) := wInv_initK _

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- `addSession` keeps the records it does not create. -/
theorem addSession_recs (t : St K) (x : Inst) (peer : PartyId) (role : Role) (y : Inst) :
    (addSession t x peer role).recs y =
      if (t.recs x).isSome then t.recs y
      else if y = x then some ⟨peer, role, .fresh, none⟩ else t.recs y := by
  unfold addSession
  by_cases h : (t.recs x).isSome
  · simp [h]
  · by_cases hy : y = x
    · subst hy; simp [h]
    · simp [h, hy]

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- `pollStep` keeps the records. -/
theorem pollStep_recs (t : St K) : (pollStep t).1.recs = t.recs := by
  unfold pollStep; split <;> rfl

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- `newKeyStep` changes at most the record of `x`. -/
theorem newKeyStep_recs (t : St K) (x : Inst) (r : Rec K) (hx : t.recs x = some r) (k kf : K)
    (y : Inst) :
    (newKeyStep t x k kf).recs y =
      if r.key.isNone ∧ y = x then
        some { r with key := some (newKeyVal t x r k kf),
                      status := if Exposed t x r then .compromised else .completed }
      else t.recs y := by
  unfold newKeyStep
  rw [hx]
  by_cases hk : r.key.isNone <;> by_cases hy : y = x <;> simp [hk, hy, setRec]

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- `newKeyFreshStep` changes at most the record of `x`. -/
theorem newKeyFreshStep_recs (t : St K) (x : Inst) (r : Rec K) (hx : t.recs x = some r)
    (k kf : K) (y : Inst) :
    (newKeyFreshStep t x k kf).recs y =
      if r.key.isNone ∧ y = x then
        some { r with key := some (if Exposed t x r then k else kf),
                      status := if Exposed t x r then .compromised else .completed }
      else t.recs y := by
  unfold newKeyFreshStep
  rw [hx]
  by_cases hk : r.key.isNone <;> by_cases hy : y = x <;> simp [hk, hy, setRec]

omit [Fintype K] [Nonempty K] in
/-- A key delivery at the session `x` with the record `r` keeps the invariant, when it stores
the placeholder key and an index below `n + 1` at a session that it completes. -/
theorem wInvP_deliver {t t' : St K} {ix ix' : Inst → Option ℕ} {n : ℕ} (h : WInvP t ix n)
    {x : Inst} {r : Rec K} (hx : t.recs x = some r) (kv : K) (jx : Option ℕ)
    (hr : ∀ y, t'.recs y = if r.key.isNone ∧ y = x then
        some { r with key := some kv,
                      status := if Exposed t x r then .compromised else .completed }
      else t.recs y)
    (hix : ∀ y, ix' y = if r.key.isNone ∧ ¬ Exposed t x r ∧ y = x then jx else ix y)
    (hkv : ¬ Exposed t x r → kv = default)
    (hjx : ¬ Exposed t x r → r.key.isNone → ∃ j, jx = some j ∧ j < n + 1) :
    WInvP t' ix' (n + 1) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun y j hj => ?_, fun y r' hr' hc => ?_⟩
  · rw [hix y] at hj
    by_cases hc : r.key.isNone ∧ ¬ Exposed t x r ∧ y = x
    · rw [ite_eq_left hc] at hj
      obtain ⟨j', hj', hlt⟩ := hjx hc.2.1 hc.1
      rw [hj'] at hj; cases hj
      refine ⟨hlt, _, (hr y).trans (ite_eq_left ⟨hc.1, hc.2.2⟩), by simp [hc.2.1]⟩
    · rw [ite_eq_right hc] at hj
      obtain ⟨hlt, r'', hr'', hc''⟩ := h1 y j hj
      refine ⟨by omega, ?_⟩
      by_cases hy : r.key.isNone ∧ y = x
      · exfalso
        obtain ⟨hk, rfl⟩ := hy
        rw [hx] at hr''; cases hr''
        have := (h2 _ _ hx hc'').1
        simp [this] at hk
      · exact ⟨r'', (hr y).trans (ite_eq_right hy) ▸ hr'', hc''⟩
  · rw [hr y] at hr'
    by_cases hy : r.key.isNone ∧ y = x
    · rw [ite_eq_left hy] at hr'
      cases hr'
      have he : ¬ Exposed t x r := by intro he; simp [he] at hc
      refine ⟨by simp [hkv he], ?_⟩
      rw [hix y, ite_eq_left ⟨hy.1, he, hy.2⟩]
      obtain ⟨j, hj, _⟩ := hjx he hy.1
      simp [hj]
    · rw [ite_eq_right hy] at hr'
      refine ⟨(h2 y r' hr' hc).1, ?_⟩
      rw [hix y, ite_eq_right (fun h => hy ⟨h.1, h.2.2⟩)]
      exact (h2 y r' hr' hc).2

section Gen

variable {Ks D : Type} [Inhabited Ks] (sp : KeySplit K Ks D)

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- A key delivery at the session `x` with the record `r` keeps the invariant at the split
`sp`, when it stores at a session that it completes the key `k₀`, the stand-in of the key of an
index below `n + 1`, and keeps the keys of the indices below `n`. -/
theorem wInvPK_deliver {t t' : St K} {ix ix' : Inst → Option ℕ} {kv kv' : ℕ → K} {n : ℕ}
    (h : WInvPK sp t ix kv n) {x : Inst} {r : Rec K} (hx : t.recs x = some r) (k₀ : K)
    (jx : Option ℕ)
    (hr : ∀ y, t'.recs y = if r.key.isNone ∧ y = x then
        some { r with key := some k₀,
                      status := if Exposed t x r then .compromised else .completed }
      else t.recs y)
    (hix : ∀ y, ix' y = if r.key.isNone ∧ ¬ Exposed t x r ∧ y = x then jx else ix y)
    (hkv : ∀ j, j < n → kv' j = kv j)
    (hjx : ¬ Exposed t x r → r.key.isNone →
      ∃ j, jx = some j ∧ j < n + 1 ∧ k₀ = sp.ph (kv' j)) :
    WInvPK sp t' ix' kv' (n + 1) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun y j hj => ?_, fun y r' hr' hc => ?_⟩
  · rw [hix y] at hj
    by_cases hc : r.key.isNone ∧ ¬ Exposed t x r ∧ y = x
    · rw [ite_eq_left hc] at hj
      obtain ⟨j', hj', hlt, _⟩ := hjx hc.2.1 hc.1
      rw [hj'] at hj; cases hj
      refine ⟨hlt, _, (hr y).trans (ite_eq_left ⟨hc.1, hc.2.2⟩), by simp [hc.2.1]⟩
    · rw [ite_eq_right hc] at hj
      obtain ⟨hlt, r'', hr'', hc''⟩ := h1 y j hj
      refine ⟨by omega, ?_⟩
      by_cases hy : r.key.isNone ∧ y = x
      · exfalso
        obtain ⟨hk, rfl⟩ := hy
        rw [hx] at hr''; cases hr''
        obtain ⟨_, _, hkey⟩ := h2 _ _ hx hc''
        simp [hkey] at hk
      · exact ⟨r'', (hr y).trans (ite_eq_right hy) ▸ hr'', hc''⟩
  · rw [hr y] at hr'
    by_cases hy : r.key.isNone ∧ y = x
    · rw [ite_eq_left hy] at hr'
      cases hr'
      have he : ¬ Exposed t x r := by intro he; simp [he] at hc
      obtain ⟨j, hj, _, hk⟩ := hjx he hy.1
      refine ⟨j, ?_, by simp [hk]⟩
      rw [hix y, ite_eq_left ⟨hy.1, he, hy.2⟩, hj]
    · rw [ite_eq_right hy] at hr'
      obtain ⟨j, hj, hk⟩ := h2 y r' hr' hc
      have hlt := (h1 y j hj).1
      refine ⟨j, ?_, by rw [hk, hkv j hlt]⟩
      rw [hix y, ite_eq_right (fun h => hy ⟨h.1, h.2.2⟩), hj]

omit [Fintype K] [Nonempty K] in
/-- **The invariant at the split `sp` is preserved** by every event and every drawn key whose
stand-in is the stand-in of the proposal. -/
theorem wInv_nextK {w : WSt K} (hw : WInvK sp w) (e : HEv ⊕ AEv K) (kf : K)
    (hkf : isNewKey e = true → sp.ph kf = sp.ph (propOf e)) :
    WInvK sp (wNextK sp w e kf) := by
  have hmono : ∀ {t : St K} {ix : Inst → Option ℕ} {kv' : ℕ → K} {n m : ℕ},
      WInvPK sp t ix w.kv n → (∀ j, j < n → kv' j = w.kv j) → n ≤ m → WInvPK sp t ix kv' m :=
    fun h hk hnm => ⟨fun y j hj => ⟨by have := (h.1 y j hj).1; omega, (h.1 y j hj).2⟩,
      fun y r hr hc => by
        obtain ⟨j, hj, hkey⟩ := h.2 y r hr hc
        exact ⟨j, hj, by rw [hkey, hk j (h.1 y j hj).1]⟩⟩
  obtain ⟨h1, h2⟩ := hw
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) |
    (_ | _ | pid | ⟨sid, pid⟩ | ⟨sid, pid, k⟩ | ⟨sid, pid, k⟩)
  · refine ⟨fun y j hj => ?_, fun y r hr hc => ?_⟩
    · simp only [wNextK, ixNext, stNextK] at hj ⊢
      obtain ⟨hlt, r, hr, hc⟩ := h1 y j hj
      refine ⟨by simp [isIdle]; omega, r, ?_, hc⟩
      rw [addSession_recs]
      split_ifs with ha hy
      · exact hr
      · subst hy; simp [hr] at ha
      · exact hr
    · simp only [wNextK, ixNext, stNextK, isNewKey, Bool.false_eq_true, ite_false] at hr hc ⊢
      rw [addSession_recs] at hr
      split_ifs at hr with ha hy
      · exact h2 y r hr hc
      · cases hr; simp at hc
      · exact h2 y r hr hc
  · exact hmono ⟨h1, h2⟩ (fun _ _ => rfl) (Nat.le_add_right _ _)
  · exact hmono ⟨h1, h2⟩ (fun _ _ => rfl) (Nat.le_add_right _ _)
  · have h' : WInvPK sp (pollStep w.st).1 w.ix w.kv w.steps := by
      unfold WInvPK; rw [pollStep_recs]; exact ⟨h1, h2⟩
    exact hmono h' (fun _ _ => rfl) (Nat.le_add_right _ _)
  · exact hmono (t := corruptStep w.st pid) ⟨h1, h2⟩ (fun _ _ => rfl) (Nat.le_add_right _ _)
  · exact hmono ⟨h1, h2⟩ (fun _ _ => rfl) (Nat.le_add_right _ _)
  · change WInvPK sp (newKeyStep w.st (sid, pid) k (sp.ph k))
      (newKeyIx w.st w.ix w.steps (sid, pid)) (Function.update w.kv w.steps kf) (w.steps + 1)
    have hkv : ∀ j, j < w.steps → Function.update w.kv w.steps kf j = w.kv j :=
      fun j hj => Function.update_of_ne (by omega) _ _
    rcases hx : w.st.recs (sid, pid) with _ | r
    · have hs : newKeyStep w.st (sid, pid) k (sp.ph k) = w.st := by simp [newKeyStep, hx]
      rw [hs]; simp only [newKeyIx, hx]
      exact hmono ⟨h1, h2⟩ hkv (by omega)
    · refine wInvPK_deliver sp ⟨h1, h2⟩ hx (newKeyVal w.st (sid, pid) r k (sp.ph k))
        (match w.st.recs (sid, r.peer) with
          | some p => if Partner (sid, pid) r p then w.ix (sid, r.peer) else some w.steps
          | none => some w.steps)
        (newKeyStep_recs _ _ r hx k _) (fun y => ?_) hkv (fun he _ => ?_)
      · simp only [newKeyIx, hx]
        by_cases hc : r.key.isNone ∧ ¬ Exposed w.st (sid, pid) r
        · rw [ite_eq_left hc]
          by_cases hy : y = (sid, pid)
          · subst hy; simp [hc]
          · simp [hy]
        · rw [ite_eq_right hc, ite_eq_right (fun h => hc ⟨h.1, h.2.1⟩)]
      · have hnew : sp.ph k = sp.ph (Function.update w.kv w.steps kf w.steps) := by
          rw [Function.update_self]; exact (hkf rfl).symm
        unfold newKeyVal
        rw [ite_eq_right he]
        change ∃ j, _ ∧ j < w.steps + 1 ∧ (match w.st.recs (sid, r.peer) with
          | some p => if Partner (sid, pid) r p then p.key.getD (sp.ph k) else sp.ph k
          | none => sp.ph k) = _
        rcases hp : w.st.recs (sid, r.peer) with _ | p
        · exact ⟨w.steps, rfl, by omega, hnew⟩
        · by_cases hpp : Partner (sid, pid) r p
          · obtain ⟨jp, hjp, hkey⟩ := h2 _ p hp hpp.2.2
            have hlt := (h1 _ jp hjp).1
            refine ⟨jp, by simp only [hpp, ite_true, hjp], by omega, ?_⟩
            simp only [hpp, ite_true, hkey, hkv jp hlt, Option.getD_some]
          · exact ⟨w.steps, by simp only [hpp, ite_false], by omega, by
              simp only [hpp, ite_false]; exact hnew⟩
  · change WInvPK sp (newKeyFreshStep w.st (sid, pid) k (sp.ph k))
      (newKeyFreshIx w.st w.ix w.steps (sid, pid)) (Function.update w.kv w.steps kf)
      (w.steps + 1)
    have hkv : ∀ j, j < w.steps → Function.update w.kv w.steps kf j = w.kv j :=
      fun j hj => Function.update_of_ne (by omega) _ _
    rcases hx : w.st.recs (sid, pid) with _ | r
    · have hs : newKeyFreshStep w.st (sid, pid) k (sp.ph k) = w.st := by
        simp [newKeyFreshStep, hx]
      rw [hs]; simp only [newKeyFreshIx, hx]
      exact hmono ⟨h1, h2⟩ hkv (by omega)
    · refine wInvPK_deliver sp ⟨h1, h2⟩ hx
        (if Exposed w.st (sid, pid) r then k else sp.ph k)
        (some w.steps) (newKeyFreshStep_recs _ _ r hx k _) (fun y => ?_) hkv
        (fun he _ => ⟨w.steps, rfl, by omega, by
          rw [ite_eq_right he, Function.update_self]; exact (hkf rfl).symm⟩)
      simp only [newKeyFreshIx, hx]
      by_cases hc : r.key.isNone ∧ ¬ Exposed w.st (sid, pid) r
      · rw [ite_eq_left hc]
        by_cases hy : y = (sid, pid)
        · subst hy; simp [hc]
        · simp [hy]
      · rw [ite_eq_right hc, ite_eq_right (fun h => hc ⟨h.1, h.2.1⟩)]

end Gen

omit [Fintype K] [Nonempty K] in
/-- **The invariant is preserved** by every event and every drawn key. -/
theorem wInv_next {w : WSt K} (hw : WInv w) (e : HEv ⊕ AEv K) (kf : K) :
    WInv (wNext w e kf) :=
  wInv_nextK _ hw e kf fun _ => rfl

end World

/-! ## Steps of the hybrid worlds at a split -/

section StepsK

variable {K V Ks D : Type} [Inhabited K] [Inhabited Ks] (sp : KeySplit K Ks D)
  (fr : K → SPComp K) (realV : K → SPComp V) (idealD : D → SPComp V)

/-- The outcomes of a step of a hybrid world at a split: the next state at a possible draw. -/
theorem world_outcomeK {i : ℕ} {cre : K → SPComp K} {rd1 rd2 : K → SPComp V} {w : WSt K}
    {e : HEv ⊕ AEv K} {q : WSt K × (HOut V ⊕ AOut)}
    (hq : IsOutcome ((worldK sp fr realV idealD i cre rd1 rd2).step w e) q) :
    ∃ kf, IsOutcome (wDrawK fr i cre w e) kf ∧ q.1 = wNextK sp w e kf := by
  simp only [worldK] at hq
  obtain ⟨kf, hkf, hq'⟩ := isOutcome_bind hq
  obtain ⟨o, _, rfl⟩ := isOutcome_map_iff.mp hq'
  exact ⟨kf, hkf, rfl⟩

/-- A draw of a hybrid world from kernels that keep the stand-in of the proposal has the
stand-in of the proposal. -/
theorem wDrawK_ph {i : ℕ} {cre : K → SPComp K}
    (hfr : ∀ p kf, IsOutcome (fr p) kf → sp.ph kf = sp.ph p)
    (hcre : ∀ p kf, IsOutcome (cre p) kf → sp.ph kf = sp.ph p) {w : WSt K}
    {e : HEv ⊕ AEv K} {kf : K} (h : IsOutcome (wDrawK fr i cre w e) kf) :
    isNewKey e = true → sp.ph kf = sp.ph (propOf e) := by
  intro hn
  simp only [wDrawK, hn, ite_true] at h
  split_ifs at h
  · exact hcre _ _ h
  · exact hfr _ _ h

/-- The steps of a hybrid world at a split keep the invariant, for kernels that keep the
stand-in of the proposal. -/
theorem world_invK {i : ℕ} {cre : K → SPComp K} {rd1 rd2 : K → SPComp V} {w : WSt K}
    (hfr : ∀ p kf, IsOutcome (fr p) kf → sp.ph kf = sp.ph p)
    (hcre : ∀ p kf, IsOutcome (cre p) kf → sp.ph kf = sp.ph p)
    {e : HEv ⊕ AEv K} {q : WSt K × (HOut V ⊕ AOut)} (hw : WInvK sp w)
    (hq : IsOutcome ((worldK sp fr realV idealD i cre rd1 rd2).step w e) q) : WInvK sp q.1 := by
  obtain ⟨kf, hkf, h⟩ := world_outcomeK sp fr realV idealD hq
  rw [h]; exact wInv_nextK sp hw e kf (wDrawK_ph sp fr hfr hcre hkf)

/-- The number of activations after a step of a hybrid world at a split. -/
theorem world_stepsK {i : ℕ} {cre : K → SPComp K} {rd1 rd2 : K → SPComp V} {w : WSt K}
    {e : HEv ⊕ AEv K} {q : WSt K × (HOut V ⊕ AOut)}
    (hq : IsOutcome ((worldK sp fr realV idealD i cre rd1 rd2).step w e) q) :
    q.1.steps = w.steps + (if isIdle e then 0 else 1) := by
  obtain ⟨kf, _, h⟩ := world_outcomeK sp fr realV idealD hq
  rw [h]; rfl

/-- The read counts after a step of a hybrid world at a split. -/
theorem world_rdK {i : ℕ} {cre : K → SPComp K} {rd1 rd2 : K → SPComp V} {w : WSt K}
    {e : HEv ⊕ AEv K} {q : WSt K × (HOut V ⊕ AOut)}
    (hq : IsOutcome ((worldK sp fr realV idealD i cre rd1 rd2).step w e) q) :
    q.1.rd = rdNext w e := by
  obtain ⟨kf, _, h⟩ := world_outcomeK sp fr realV idealD hq
  rw [h]; rfl

/-- A hybrid world at a split is idle at the idle event of the adversary. -/
theorem world_idleAtK (i : ℕ) (cre : K → SPComp K) (rd1 rd2 : K → SPComp V) :
    MultiHybrid.IdleAt (worldK sp fr realV idealD i cre rd1 rd2) (.inr .idle) (.inr .ack) := by
  intro w
  simp only [worldK, wDrawK, isNewKey, wOutK, SPComp.pure_bind, SPComp.map, Bool.false_eq_true,
    ite_false]
  rfl

omit [Inhabited K] in
/-- A map of a computation that does not fail does not fail. -/
theorem map_noFail {α β : Type} (f : α → β) {c : SPComp α} (hc : SPComp.NoFail c) :
    SPComp.NoFail (SPComp.map f c) :=
  Assumptions.SPComp.bind_noFail hc fun _ => SPComp.pure_noFail _

omit [Inhabited K] [Inhabited Ks] in
/-- The outputs of a hybrid world at a split do not fail when its views do not fail. -/
theorem wOut_noFailK {i : ℕ} {rd1 rd2 : K → SPComp V}
    (hR : ∀ k, SPComp.NoFail (realV k)) (hI : ∀ d, SPComp.NoFail (idealD d))
    (h1 : ∀ k, SPComp.NoFail (rd1 k)) (h2 : ∀ k, SPComp.NoFail (rd2 k))
    (w : WSt K) (e : HEv ⊕ AEv K) : SPComp.NoFail (wOutK sp realV idealD i rd1 rd2 w e) := by
  rcases e with (_ | ⟨sid, pid⟩) | (_ | _ | _ | _ | _ | _)
  all_goals try exact SPComp.pure_noFail _
  refine map_noFail _ ?_
  unfold chanOut
  split
  · split
    · refine map_noFail _ ?_
      unfold wViewK
      split
      · unfold readOutK
        split_ifs
        · exact hI _
        · exact h1 _
        · exact h2 _
        · exact hR _
      · exact hR _
    · exact SPComp.pure_noFail _
  · exact SPComp.pure_noFail _

/-- The steps of a hybrid world at a split do not fail when its views and its kernels do not
fail. -/
theorem world_noFailK {i : ℕ} {cre : K → SPComp K} {rd1 rd2 : K → SPComp V}
    (hR : ∀ k, SPComp.NoFail (realV k)) (hI : ∀ d, SPComp.NoFail (idealD d))
    (hfr : ∀ p, SPComp.NoFail (fr p)) (hc : ∀ p, SPComp.NoFail (cre p))
    (h1 : ∀ k, SPComp.NoFail (rd1 k)) (h2 : ∀ k, SPComp.NoFail (rd2 k))
    (w : WSt K) (e : HEv ⊕ AEv K) :
    SPComp.NoFail ((worldK sp fr realV idealD i cre rd1 rd2).step w e) := by
  simp only [worldK]
  refine Assumptions.SPComp.bind_noFail ?_ fun kf =>
    map_noFail _ (wOut_noFailK sp realV idealD hR hI h1 h2 w e)
  unfold wDrawK
  split_ifs
  · exact hc _
  · exact hfr _
  · exact SPComp.pure_noFail _

/-- **The key `i` drawn at its creation is the key `i` drawn before the run**, at a split. If
the creation kernel factors as `cre p = map (g · p) c` through a computation `c` that neither
touches the heap nor fails, the hybrid world with the creation `cre` has the run of the worlds
whose key `i` is `g a p` at the proposal `p`, averaged over `a` drawn from `c` before the run. -/
theorem run_world_createK (i : ℕ) {α : Type} {c : SPComp α} (hc : SPComp.IsPure c)
    (hcn : SPComp.NoFail c) (g : α → K → K) {cre : K → SPComp K}
    (hcre : ∀ p, cre p = SPComp.map (fun a => g a p) c) (rd1 rd2 : K → SPComp V) {ζ : Type}
    (bad : WSt K → Bool) (Z : Strat ζ (HEv ⊕ AEv K) (HOut V ⊕ AOut)) :
    SPComp.bind c (fun a =>
        run (worldK sp fr realV idealD i (fun p => SPComp.pure (g a p)) rd1 rd2) bad Z) =
      run (worldK sp fr realV idealD i cre rd1 rd2) bad Z := by
  refine run_deferred c hc hcn
    (fun a => worldK sp fr realV idealD i (fun p => SPComp.pure (g a p)) rd1 rd2)
    (worldK sp fr realV idealD i cre rd1 rd2) (fun _ => True) (fun w => i < w.steps)
    (fun w e => w.steps = i ∧ isNewKey e = true) (fun _ => rfl) trivial
    (by simp [worldK, WSt.init]) (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    ?_ ?_ ?_ ?_ ?_ bad Z
  · intro k w e _ hp
    simp only [worldK, wDrawK, show w.steps ≠ i by omega, ite_false]
  · intro w e q _ hp hq
    have := world_stepsK sp fr realV idealD hq
    omega
  · intro k w e _ hp hu
    simp only [worldK, wDrawK]
    by_cases hn : isNewKey e = true
    · simp only [hn, ite_true, show w.steps ≠ i from fun h => hu ⟨h, hn⟩, ite_false]
    · simp only [hn, Bool.false_eq_true, ite_false]
  · intro w e _ _ hu
    simp only [worldK, wDrawK, hu.1, hu.2, ite_true, hcre, SPComp.map, SPComp.bind_assoc,
      SPComp.pure_bind]
  · intro k w e q _ hp hu hq
    have := world_stepsK sp fr realV idealD hq
    have hi : isIdle e = false := by
      rcases e with _ | (_ | _ | _ | _ | _ | _) <;> simp_all [isNewKey, isIdle]
    rw [hi] at this
    simp only [Bool.false_eq_true, ite_false] at this
    omega

omit [Inhabited K] in
/-- The read counts do not decrease. -/
theorem rdNext_ge (w : WSt K) (e : HEv ⊕ AEv K) (j : ℕ) : w.rd j ≤ rdNext w e j := by
  rcases e with (_ | ⟨sid, pid⟩) | _
  · exact le_rfl
  · rcases h : w.ix (sid, pid) with _ | j'
    · simp only [rdNext, h, le_refl]
    · simp only [rdNext, h]
      by_cases hj : j = j'
      · subst hj; simp
      · rw [Function.update_of_ne hj]
  · exact le_rfl

omit [Inhabited K] in
/-- A new index is an existing index or the index of the current activation at a key
delivery. -/
theorem ixNext_some {w : WSt K} {e : HEv ⊕ AEv K} {y : Inst} {j : ℕ}
    (h : ixNext w e y = some j) :
    (∃ y', w.ix y' = some j) ∨ (j = w.steps ∧ isNewKey e = true) := by
  rcases e with _ | (_ | _ | _ | _ | ⟨sid, pid, k⟩ | ⟨sid, pid, k⟩)
  all_goals try exact Or.inl ⟨y, h⟩
  · simp only [ixNext, newKeyIx] at h
    rcases hx : w.st.recs (sid, pid) with _ | r
    · rw [hx] at h; exact Or.inl ⟨y, h⟩
    · rw [hx] at h
      dsimp only at h
      split_ifs at h with hc
      · by_cases hy : y = (sid, pid)
        · subst hy
          rw [Function.update_self] at h
          rcases hp : w.st.recs (sid, r.peer) with _ | p
          · rw [hp] at h; cases h; exact Or.inr ⟨rfl, rfl⟩
          · rw [hp] at h
            dsimp only at h
            split_ifs at h
            · exact Or.inl ⟨_, h⟩
            · cases h; exact Or.inr ⟨rfl, rfl⟩
        · rw [Function.update_of_ne hy] at h; exact Or.inl ⟨y, h⟩
      · exact Or.inl ⟨y, h⟩
  · simp only [ixNext, newKeyFreshIx] at h
    rcases hx : w.st.recs (sid, pid) with _ | r
    · rw [hx] at h; exact Or.inl ⟨y, h⟩
    · rw [hx] at h
      dsimp only at h
      split_ifs at h with hc
      · by_cases hy : y = (sid, pid)
        · subst hy
          rw [Function.update_self] at h
          cases h; exact Or.inr ⟨rfl, rfl⟩
        · rw [Function.update_of_ne hy] at h; exact Or.inl ⟨y, h⟩
      · exact Or.inl ⟨y, h⟩

omit [Inhabited K] [Inhabited Ks] in
/-- The views of the indices other than `i` do not depend on the reads of `i`. -/
theorem readOut_neK {i j : ℕ} (h : j ≠ i) (rd1 rd2 rd1' rd2' : K → SPComp V) (w : WSt K) :
    readOutK sp realV idealD i rd1 rd2 w j = readOutK sp realV idealD i rd1' rd2' w j := by
  simp [readOutK, h]

omit [Inhabited K] [Inhabited Ks] in
/-- After the first read of `i`, the views do not depend on the first read. -/
theorem readOut_postK {i : ℕ} (rd1 rd1' rd2 : K → SPComp V) {w : WSt K} (h : w.rd i ≠ 0)
    (j : ℕ) :
    readOutK sp realV idealD i rd1 rd2 w j = readOutK sp realV idealD i rd1' rd2 w j := by
  simp [readOutK, h]

omit [Inhabited K] [Inhabited Ks] in
/-- Two states with the same functionality state and indices, and two families of views that
agree at the index of the session that `e` reads, give the same output at `e`. -/
theorem wOut_congr₂K {i i' : ℕ} {rd1 rd2 rd1' rd2' : K → SPComp V} {w w' : WSt K}
    (hst : w.st = w'.st) (hix : w.ix = w'.ix) (e : HEv ⊕ AEv K)
    (h : ∀ sid pid j, e = .inl (.getKey sid pid) → w.ix (sid, pid) = some j →
      readOutK sp realV idealD i rd1 rd2 w j = readOutK sp realV idealD i' rd1' rd2' w' j) :
    wOutK sp realV idealD i rd1 rd2 w e = wOutK sp realV idealD i' rd1' rd2' w' e := by
  rcases e with (_ | ⟨sid, pid⟩) | (_ | _ | _ | _ | _ | _)
  all_goals try rfl
  · simp only [wOutK]
    congr 1
    unfold chanOut
    rw [← hst]
    split
    · split
      · congr 1
        unfold wViewK
        rw [← hix]
        split
        · next j hj => exact h sid pid j rfl hj
        · rfl
      · rfl
    · rfl
  · simp only [wOutK, hst]

omit [Inhabited K] [Inhabited Ks] in
/-- Two families of views that agree at the index of the session that `e` reads give the
same output at `e`. -/
theorem wOut_congrK {i i' : ℕ} {rd1 rd2 rd1' rd2' : K → SPComp V} {w : WSt K}
    (e : HEv ⊕ AEv K)
    (h : ∀ sid pid j, e = .inl (.getKey sid pid) → w.ix (sid, pid) = some j →
      readOutK sp realV idealD i rd1 rd2 w j = readOutK sp realV idealD i' rd1' rd2' w j) :
    wOutK sp realV idealD i rd1 rd2 w e = wOutK sp realV idealD i' rd1' rd2' w e :=
  wOut_congr₂K sp realV idealD rfl rfl e h

/-- The indices of a hybrid state are below its number of activations. -/
def IxLt (w : WSt K) : Prop := ∀ x j, w.ix x = some j → j < w.steps

omit [Inhabited K] in
/-- The next state keeps the indices below the number of activations. -/
theorem ixLt_next {w : WSt K} (h : IxLt w) (e : HEv ⊕ AEv K) (kf : K) :
    IxLt (wNextK sp w e kf) := by
  intro x j hj
  rcases ixNext_some hj with ⟨y, hy⟩ | ⟨rfl, hn⟩
  · have := h y j hy
    change j < w.steps + _
    omega
  · have hi : isIdle e = false := by
      rcases e with _ | (_ | _ | _ | _ | _ | _) <;> simp_all [isNewKey, isIdle]
    change w.steps < w.steps + (if isIdle e then 0 else 1)
    simp [hi]

/-- **The first read of the key `i` drawn at the read is the first read drawn before the run**,
at a split. If every key that the creation `cre` may give has the first view
`rd1 kf = bind c (rd1' · kf)`, the run of the hybrid world with the first read `rd1` is the run
of the worlds with the first read `rd1' a`, averaged over `a` drawn from `c` before the run. -/
theorem run_world_readK (i : ℕ) (cre : K → SPComp K) {α : Type} {c : SPComp α}
    (hc : SPComp.IsPure c) (hcn : SPComp.NoFail c) (rd1 : K → SPComp V)
    (rd1' : α → K → SPComp V) (rd2 : K → SPComp V)
    (hcre : ∀ p kf, IsOutcome (cre p) kf → rd1 kf = SPComp.bind c fun a => rd1' a kf)
    {ζ : Type} (bad : WSt K → Bool) (Z : Strat ζ (HEv ⊕ AEv K) (HOut V ⊕ AOut)) :
    SPComp.bind c (fun a => run (worldK sp fr realV idealD i cre (rd1' a) rd2) bad Z) =
      run (worldK sp fr realV idealD i cre rd1 rd2) bad Z := by
  have hinv : ∀ (r1 : K → SPComp V) (w : WSt K) (e : HEv ⊕ AEv K)
      (q : WSt K × (HOut V ⊕ AOut)),
      (IxLt w ∧ ∀ x, w.ix x = some i → rd1 (w.kv i) = SPComp.bind c fun a => rd1' a (w.kv i)) →
      IsOutcome ((worldK sp fr realV idealD i cre r1 rd2).step w e) q →
      IxLt q.1 ∧
        ∀ x, q.1.ix x = some i → rd1 (q.1.kv i) = SPComp.bind c fun a => rd1' a (q.1.kv i) := by
    intro r1 w e q ⟨hw, hr⟩ hq
    obtain ⟨kf, hkf, hq1⟩ := world_outcomeK sp fr realV idealD hq
    refine ⟨hq1 ▸ ixLt_next sp hw e kf, fun x hx => ?_⟩
    rw [hq1] at hx ⊢
    rcases ixNext_some hx with ⟨y', hy'⟩ | ⟨hi, hn⟩
    · have hlt := hw y' i hy'
      have : (wNextK sp w e kf).kv i = w.kv i := by
        simp only [wNextK]
        split_ifs
        · rw [Function.update_of_ne (by omega)]
        · rfl
      rw [this]; exact hr y' hy'
    · have hd : wDrawK fr i cre w e = cre (propOf e) := by simp [wDrawK, hn, ← hi]
      rw [hd] at hkf
      have : (wNextK sp w e kf).kv i = kf := by simp [wNextK, hn, hi]
      rw [this]; exact hcre _ kf hkf
  refine run_deferred c hc hcn (fun a => worldK sp fr realV idealD i cre (rd1' a) rd2)
    (worldK sp fr realV idealD i cre rd1 rd2)
    (fun w => IxLt w ∧ ∀ x, w.ix x = some i → rd1 (w.kv i) = SPComp.bind c fun a => rd1' a (w.kv i))
    (fun w => 1 ≤ w.rd i)
    (fun w e => ∃ sid pid, e = .inl (.getKey sid pid) ∧ w.ix (sid, pid) = some i)
    (fun _ => rfl) ⟨fun x j hx => by simp [worldK, WSt.init] at hx,
      fun x hx => by simp [worldK, WSt.init] at hx⟩
    (by simp [worldK, WSt.init]) (hinv rd1) (fun a => hinv _) ?_ ?_ ?_ ?_ ?_ bad Z
  · intro v w e _ hp
    simp only [worldK]
    rw [wOut_congrK sp realV idealD e (fun _ _ j _ _ => readOut_postK sp realV idealD _ rd1 rd2
      (show w.rd i ≠ 0 by omega) j)]
  · intro w e q _ hp hq
    rw [world_rdK sp fr realV idealD hq]
    exact le_trans hp (rdNext_ge w e i)
  · intro v w e _ hp hu
    simp only [worldK]
    congr 1; funext kf; congr 1
    refine wOut_congrK sp realV idealD e (fun sid pid j he hj => ?_)
    have hji : j ≠ i := fun h => hu ⟨sid, pid, he, h ▸ hj⟩
    exact readOut_neK sp realV idealD hji _ _ _ _ w
  · rintro w e ⟨_, hr⟩ hp ⟨sid, pid, rfl, hx⟩
    simp only [worldK, wDrawK, isNewKey, Bool.false_eq_true, ite_false, SPComp.pure_bind, wOutK]
    unfold chanOut wViewK
    rw [hx]
    rcases hr' : w.st.recs (sid, pid) with _ | r
    · dsimp only; exact (bind_const_of_isPure hc hcn _).symm
    · rcases hk : r.key with _ | k
      · simp only [hk]; exact (bind_const_of_isPure hc hcn _).symm
      · simp only [hk, readOutK, lt_irrefl, ite_false, ite_true, show w.rd i = 0 by omega,
          hr _ hx, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  · intro v w e q _ hp hu hq
    obtain ⟨sid, pid, rfl, hx⟩ := hu
    rw [world_rdK sp fr realV idealD hq]
    simp [rdNext, hx]

/-- The use of the key `i`: the event `getKey` at a session with the index `i`. -/
def useK (i : ℕ) (w : WSt K) : HEv ⊕ AEv K → Bool
  | .inl (.getKey sid pid) => decide (w.ix (sid, pid) = some i)
  | _ => false

omit [Inhabited K] in
/-- The use of the key `i` is `getKey` at a session with the index `i`. -/
theorem useK_iff {i : ℕ} {w : WSt K} {e : HEv ⊕ AEv K} :
    useK i w e = true ↔ ∃ sid pid, e = .inl (.getKey sid pid) ∧ w.ix (sid, pid) = some i := by
  rcases e with (_ | ⟨sid, pid⟩) | _ <;> simp [useK]

/-- **The run of a hybrid world split at the first use of the key `i`.** For a first read
`rd1` that neither touches the heap nor fails, the run is the first stage up to the first
`getKey` of the key `i`, then the first view `v` drawn from `rd1` at the key `i` of the state at
the split, then the second stage of the world whose first read of the key `i` returns `v`. -/
theorem run_world_read_atK (i : ℕ) (cre : K → SPComp K) (rd1 rd2 : K → SPComp V)
    (hrd1 : ∀ k, SPComp.IsPure (rd1 k) ∧ SPComp.NoFail (rd1 k)) {ζ : Type}
    (bad : WSt K → Bool) (Z : Strat ζ (HEv ⊕ AEv K) (HOut V ⊕ AOut)) :
    run (worldK sp fr realV idealD i cre rd1 rd2) bad Z =
      SPComp.bind (loopTo (worldK sp fr realV idealD i cre rd1 rd2) bad Z
          (fun w e => useK i w e = true) Z.rounds (Z.init, WSt.init, bad WSt.init)) fun s =>
        SPComp.bind (rd1 (s.2.1.2.1.kv i)) fun v =>
          loopRest (worldK sp fr realV idealD i cre (fun _ => SPComp.pure v) rd2) bad Z s := by
  refine run_deferred_at (fun w => rd1 (w.kv i)) (fun _ => (hrd1 _).1) (fun _ => (hrd1 _).2)
    (fun v => worldK sp fr realV idealD i cre (fun _ => SPComp.pure v) rd2)
    (worldK sp fr realV idealD i cre rd1 rd2) (fun _ => True) (fun w => 1 ≤ w.rd i)
    (fun w e => useK i w e = true) trivial (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ => trivial) ?_ ?_ ?_ ?_ bad Z
  · intro v w e _ hp
    simp only [worldK]
    rw [wOut_congrK sp realV idealD e (fun _ _ j _ _ => readOut_postK sp realV idealD _ rd1 rd2
      (show w.rd i ≠ 0 by omega) j)]
  · intro w e q _ hp hq
    rw [world_rdK sp fr realV idealD hq]
    exact le_trans hp (rdNext_ge w e i)
  · intro w e _ hp hu
    obtain ⟨sid, pid, rfl, hx⟩ := useK_iff.mp hu
    simp only [worldK, wDrawK, isNewKey, Bool.false_eq_true, ite_false, SPComp.pure_bind, wOutK]
    unfold chanOut wViewK
    rw [hx]
    rcases hr' : w.st.recs (sid, pid) with _ | r
    · dsimp only; exact (bind_const_of_isPure (hrd1 _).1 (hrd1 _).2 _).symm
    · rcases hk : r.key with _ | k
      · simp only [hk]; exact (bind_const_of_isPure (hrd1 _).1 (hrd1 _).2 _).symm
      · simp only [hk, readOutK, lt_irrefl, ite_false, ite_true, show w.rd i = 0 by omega,
          SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  · intro v w e q _ hp hu hq
    obtain ⟨sid, pid, rfl, hx⟩ := useK_iff.mp hu
    rw [world_rdK sp fr realV idealD hq]
    simp [rdNext, hx]

omit [Inhabited K] in
/-- A judgment at the equality of heaps conjoined with a fact `P` follows from the judgments
under `P`. -/
theorem rHoare_eqPre_and_of {α β : Type} {P : Prop} {c₁ : SPComp α} {c₂ : SPComp β}
    {Ψ : RPost α β} (h : P → rHoare eqPre c₁ c₂ Ψ) :
    rHoare (fun h₁ h₂ => h₁ = h₂ ∧ P) c₁ c₂ Ψ :=
  fun h₁ h₂ hp => h hp.2 h₁ h₂ hp.1

/-- The relation of two hybrid worlds that differ only in the key `i`: equal states except at
the key of the index `i`. -/
def relExcept (i : ℕ) (a b : WSt K) : Prop :=
  a.st = b.st ∧ a.ix = b.ix ∧ a.steps = b.steps ∧ a.rd = b.rd ∧ ∀ j, j ≠ i → a.kv j = b.kv j

/-- The bad event of the key `i`: it is read twice. -/
def reuse (i : ℕ) (w : WSt K) : Bool := decide (2 ≤ w.rd i)

omit [Inhabited K] in
/-- The next states of related states are related at a split, for draws that agree unless the
activation creates the key `i`. -/
theorem relExcept_nextK {i : ℕ} {a b : WSt K} (h : relExcept i a b) (e : HEv ⊕ AEv K)
    {kf kf' : K} (hk : a.steps ≠ i → kf = kf') :
    relExcept i (wNextK sp a e kf) (wNextK sp b e kf') := by
  obtain ⟨hst, hix, hs, hrd, hkv⟩ := h
  refine ⟨?_, ?_, ?_, ?_, fun j hj => ?_⟩
  · simp only [wNextK, hst]
  · rcases e with _ | (_ | _ | _ | _ | _ | _) <;> simp [wNextK, ixNext, hst, hix, hs]
  · simp only [wNextK, hs]
  · rcases e with (_ | ⟨sid, pid⟩) | _ <;> simp [wNextK, rdNext, hix, hrd]
  · simp only [wNextK]
    split_ifs
    · by_cases hjs : j = a.steps
      · subst hjs
        rw [Function.update_self, hs, Function.update_self]
        exact hk hj
      · rw [Function.update_of_ne hjs, ← hs, Function.update_of_ne hjs]; exact hkv j hj
    · exact hkv j hj

/-- The relation of two hybrid worlds that differ in the key `i`, with the keys `i` related by
`κ` once an index `i` exists. -/
def relK (κ : K → K → Prop) (i : ℕ) (a b : WSt K) : Prop :=
  relExcept i a b ∧ ((∃ x, a.ix x = some i) → κ (a.kv i) (b.kv i))

omit [Inhabited K] in
/-- The next states of `relK`-related states are related, for draws that agree unless the
activation creates the key `i`, and are related by `κ` when it does. -/
theorem relK_next {κ : K → K → Prop} {i : ℕ} {a b : WSt K} (h : relK κ i a b)
    (e : HEv ⊕ AEv K) {kf kf' : K} (hk : a.steps ≠ i → kf = kf')
    (hκ : a.steps = i → isNewKey e = true → κ kf kf') :
    relK κ i (wNextK sp a e kf) (wNextK sp b e kf') := by
  refine ⟨relExcept_nextK sp h.1 e hk, fun ⟨x, hx⟩ => ?_⟩
  have hs := h.1.2.2.1
  by_cases hc : a.steps = i ∧ isNewKey e = true
  · have hb : b.steps = i := hs ▸ hc.1
    simp only [wNextK, hc.2, ite_true]
    rw [← hc.1, Function.update_self, hs, Function.update_self]
    exact hκ hc.1 hc.2
  · have ha : (wNextK sp a e kf).kv i = a.kv i := by
      simp only [wNextK]
      split_ifs with hn
      · exact Function.update_of_ne (fun h => hc ⟨h.symm, hn⟩) _ _
      · rfl
    have hb : (wNextK sp b e kf').kv i = b.kv i := by
      simp only [wNextK]
      split_ifs with hn
      · exact Function.update_of_ne (fun h => hc ⟨hs.trans h.symm, hn⟩) _ _
      · rfl
    rw [ha, hb]
    rcases ixNext_some hx with ⟨y, hy⟩ | ⟨hi, hn⟩
    · exact h.2 ⟨y, hy⟩
    · exact absurd ⟨hi.symm, hn⟩ hc

/-- **Up to a second read of the key `i`**, at a split. Two hybrid worlds whose creations of the
key `i` are coupled into the relation `κ`, whose first reads of the key `i` agree on keys
related by `κ`, and whose later reads differ, are at distance at most the probability that the
key `i` is read twice in the first world. -/
theorem world_upto_reuseK (i : ℕ) (κ : K → K → Prop) {creA creB : K → SPComp K}
    {rd1 rd1' rdA rdB : K → SPComp V}
    (hcpl : ∀ p, rHoare eqPre (creA p) (creB p) fun a h b h' => h = h' ∧ κ a b)
    (hrd1 : ∀ a b, κ a b → rd1 a = rd1' b) (hR : ∀ k, SPComp.NoFail (realV k))
    (hI : ∀ d, SPComp.NoFail (idealD d)) (hfr : ∀ p, SPComp.NoFail (fr p))
    (hcA : ∀ p, SPComp.NoFail (creA p)) (hcB : ∀ p, SPComp.NoFail (creB p))
    (h1 : ∀ k, SPComp.NoFail (rd1 k)) (h1' : ∀ k, SPComp.NoFail (rd1' k))
    (hA : ∀ k, SPComp.NoFail (rdA k)) (hB : ∀ k, SPComp.NoFail (rdB k)) :
    Realizes (worldK sp fr realV idealD i creA rd1 rdA) (worldK sp fr realV idealD i creB rd1' rdB)
      (fun _ Z => prBad (worldK sp fr realV idealD i creA rd1 rdA) (reuse i) Z) := by
  refine realizes_upto_bad_rel _ _ (relK κ i) (reuse i)
    ⟨⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩, fun ⟨x, hx⟩ => by simp [worldK, WSt.init] at hx⟩
    (world_noFailK sp fr realV idealD hR hI hfr hcA h1 hA)
    (world_noFailK sp fr realV idealD hR hI hfr hcB h1' hB)
    fun a b e hab hbad => ?_
  have hmap : ∀ {α β : Type} (f : α → β) (c : SPComp α),
      SPComp.map f c = SPComp.bind c fun x => SPComp.pure (f x) := fun _ _ => rfl
  simp only [worldK, hmap]
  -- the draws
  have hdraw : rHoare eqPre (wDrawK fr i creA a e) (wDrawK fr i creB b e)
      (fun kf h kf' h' => h = h' ∧ (a.steps ≠ i → kf = kf') ∧
        (a.steps = i → isNewKey e = true → κ kf kf')) := by
    by_cases hc : isNewKey e = true ∧ a.steps = i
    · have hb : b.steps = i := hab.1.2.2.1 ▸ hc.2
      simp only [wDrawK, hc.1, hc.2, hb, ite_true]
      exact rHoare_conseq (fun _ _ h => h)
        (fun _ _ _ _ hh => ⟨hh.1, fun hn => absurd rfl hn, fun _ _ => hh.2⟩) (hcpl _)
    · have heq : wDrawK fr i creA a e = wDrawK fr i creB b e := by
        simp only [wDrawK, ← hab.1.2.2.1]
        by_cases hn : isNewKey e = true
        · have : a.steps ≠ i := fun h => hc ⟨hn, h⟩
          simp [hn, this]
        · simp [hn]
      rw [heq]
      exact rHoare_conseq (fun _ _ h => h)
        (fun _ _ _ _ hh => ⟨hh.2, fun _ => hh.1, fun h hn => absurd ⟨hn, h⟩ hc⟩)
        (rHoare_refl _)
  refine rHoare_bind hdraw fun kf kf' => ?_
  refine rHoare_eqPre_and_of (P := (a.steps ≠ i → kf = kf') ∧
    (a.steps = i → isNewKey e = true → κ kf kf')) fun hk => ?_
  have hnext := relK_next sp hab e hk.1 hk.2
  by_cases hbr : ∃ sid pid, e = .inl (.getKey sid pid) ∧ a.ix (sid, pid) = some i ∧
      a.rd i ≠ 0
  · -- a second read: the run is bad
    obtain ⟨sid, pid, rfl, hx, hr⟩ := hbr
    refine rHoare_bind (rHoare_true_of_noFail (wOut_noFailK sp realV idealD hR hI h1 hA a _)
      (wOut_noFailK sp realV idealD hR hI h1' hB b _)) fun o o' => rHoare_ret fun _ _ _ => ?_
    left
    have hle : 1 ≤ a.rd i := Nat.one_le_iff_ne_zero.mpr hr
    simp [reuse, wNextK, rdNext, hx]
    omega
  · have hout : wOutK sp realV idealD i rd1 rdA a e = wOutK sp realV idealD i rd1' rdB b e := by
      refine wOut_congr₂K sp realV idealD hab.1.1 hab.1.2.1 e fun sid pid j he hj => ?_
      unfold readOutK
      by_cases hji : j = i
      · subst hji
        have hr : a.rd j = 0 := by
          by_contra hr; exact hbr ⟨sid, pid, he, hj, hr⟩
        simp [hr, ← hab.1.2.2.2.1, hrd1 _ _ (hab.2 ⟨_, hj⟩)]
      · simp [hji, hab.1.2.2.2.2 j hji]
    rw [← hout]
    refine rHoare_bind (rHoare_refl _) fun o o' => rHoare_ret fun h h' hh => ?_
    obtain ⟨rfl, rfl⟩ := hh
    exact Or.inr ⟨rfl, hnext, rfl⟩

/-! ## The last hybrid world and the ideal secure channel, at a split -/

/-- The output of `F_SCK` at an event. -/
noncomputable def scOutK (t : St K) : HEv ⊕ AEv K → SPComp (HOut V ⊕ AOut)
  | .inl (.newSession _ _ _ _) => SPComp.pure (.inl .ok)
  | .inl (.getKey sid pid) => SPComp.map Sum.inl (chanOut (scViewK sp realV idealD) t (sid, pid))
  | .inr .poll => SPComp.pure (.inr (.notice (pollStep t).2))
  | .inr _ => SPComp.pure (.inr .ack)

omit [Inhabited K] in
/-- The steps of `F_SCK`: the next state of the functionality with the stand-in keys and the
output `scOutK`. -/
theorem F_SCK_step (t : St K) (e : HEv ⊕ AEv K) :
    (F_SCK sp realV idealD).step t e =
      SPComp.map (fun o => (stNextK sp t e, o)) (scOutK sp realV idealD t e) := by
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) |
    (_ | _ | pid | ⟨sid, pid⟩ | ⟨sid, pid, k⟩ | ⟨sid, pid, k⟩) <;>
    simp [F_SCK, chanHon, advSysK, advSysImp, stNextK, scOutK, SPComp.map, SPComp.bind_assoc,
      SPComp.pure_bind]

omit [Inhabited K] [Inhabited Ks] in
/-- Two view functions that agree at the record and the key of the session give the same
channel output. -/
theorem chanOut_congr {f g : Rec K → K → SPComp V} {t : St K} {x : Inst}
    (h : ∀ r k, t.recs x = some r → r.key = some k → f r k = g r k) :
    chanOut f t x = chanOut g t x := by
  unfold chanOut
  rcases hx : t.recs x with _ | r
  · rfl
  · rcases hk : r.key with _ | k
    · simp only [hk]
    · simp only [hk, h r k hx hk]

omit [Inhabited K] in
/-- In a state of the invariant at the split `sp` whose indices are below `n`, the hybrid world
`n` with real reads outputs as `F_SCK`. -/
theorem wOut_eq_scOutK {n : ℕ} {w : WSt K} (hw : WInvK sp w) (hn : w.steps ≤ n)
    (e : HEv ⊕ AEv K) :
    wOutK sp realV idealD n realV realV w e = scOutK sp realV idealD w.st e := by
  rcases e with (_ | ⟨sid, pid⟩) | (_ | _ | _ | _ | _ | _)
  all_goals try rfl
  simp only [wOutK, scOutK]
  congr 1
  refine chanOut_congr fun r k hr hk => ?_
  unfold wViewK scViewK
  rcases hj : w.ix (sid, pid) with _ | j
  · have hc : r.status ≠ .completed := fun hc => by
      obtain ⟨j', hj', _⟩ := hw.2 _ r hr hc
      rw [hj] at hj'; cases hj'
    simp [hc]
  · obtain ⟨hlt, r', hr', hc'⟩ := hw.1 _ j hj
    rw [hr] at hr'; cases hr'
    obtain ⟨j', hj', hkey⟩ := hw.2 _ r hr hc'
    rw [hj] at hj'; cases hj'
    rw [hk] at hkey; cases hkey
    simp [readOutK, show j < n by omega, hc', KeySplit.dat_ph]

omit [Inhabited K] in
/-- The draws of a hybrid world at a split neither touch the heap nor fail, for kernels that do
not. -/
theorem wDrawK_pureNF {i : ℕ} {cre : K → SPComp K}
    (hfr : ∀ p, SPComp.IsPure (fr p) ∧ SPComp.NoFail (fr p))
    (hc : ∀ p, SPComp.IsPure (cre p) ∧ SPComp.NoFail (cre p)) [Inhabited K] (w : WSt K)
    (e : HEv ⊕ AEv K) :
    SPComp.IsPure (wDrawK fr i cre w e) ∧ SPComp.NoFail (wDrawK fr i cre w e) := by
  unfold wDrawK
  split_ifs
  · exact hc _
  · exact hfr _
  · exact CatCrypt.Crypto.PAKE.CPaceSquare.pureNF_pure _

/-- **The last hybrid world at a split is the ideal secure channel `F_SCK` up to `n`
activations.** For a fresh-key kernel that neither touches the heap nor fails and keeps the
stand-in of the proposal, the hybrid world `n` with real reads realizes `F_SCK` with bound the
probability that the run exceeds `n` non-idle activations. -/
theorem world_endK (n : ℕ) (hR : ∀ k, SPComp.NoFail (realV k))
    (hI : ∀ d, SPComp.NoFail (idealD d))
    (hfr : ∀ p, SPComp.IsPure (fr p) ∧ SPComp.NoFail (fr p))
    (hfrp : ∀ p kf, IsOutcome (fr p) kf → sp.ph kf = sp.ph p) :
    Realizes (worldK sp fr realV idealD n fr realV realV) (F_SCK sp realV idealD)
      (fun _ Z => prBad (worldK sp fr realV idealD n fr realV realV)
        (fun w => decide (n < w.steps)) Z) := by
  refine realizes_upto_bad_rel _ _ (fun w t => w.st = t ∧ WInvK sp w)
    (fun w => decide (n < w.steps)) ⟨rfl, wInv_initK sp⟩
    (world_noFailK sp fr realV idealD hR hI (fun p => (hfr p).2) (fun p => (hfr p).2) hR hR)
    (fun t e => by
      rw [F_SCK_step]
      refine map_noFail _ ?_
      rcases e with (_ | ⟨sid, pid⟩) | (_ | _ | _ | _ | _ | _)
      all_goals try exact SPComp.pure_noFail _
      refine map_noFail _ ?_
      unfold chanOut
      split
      · split
        · refine map_noFail _ ?_
          unfold scViewK; split_ifs
          · exact hI _
          · exact hR _
        · exact SPComp.pure_noFail _
      · exact SPComp.pure_noFail _) fun w t e hwt hbad => ?_
  obtain ⟨rfl, hw⟩ := hwt
  have hn : w.steps ≤ n := by simpa using hbad
  have hd := wDrawK_pureNF fr hfr hfr (i := n) w e
  rw [F_SCK_step, ← wOut_eq_scOutK sp realV idealD hw hn e,
    ← bind_const_of_isPure hd.1 hd.2 (SPComp.map _ _)]
  simp only [worldK]
  -- the draw, with its outcomes
  have hdraw : rHoare eqPre (wDrawK fr n fr w e) (wDrawK fr n fr w e)
      (fun kf h kf' h' => (kf = kf' ∧ h = h') ∧ IsOutcome (wDrawK fr n fr w e) kf) := by
    intro h₁ h₂ hΦ
    obtain ⟨cp, hcp⟩ := rHoare_refl (wDrawK fr n fr w e) h₁ h₂ hΦ
    exact ⟨cp, fun p p' hp => ⟨hcp p p' hp, ⟨h₁, p.2, cp.in_left_support hp⟩⟩⟩
  refine rHoare_bind hdraw fun kf kf' =>
    rHoare_conseq (Φ := fun h h' => h = h' ∧ IsOutcome (wDrawK fr n fr w e) kf)
      (fun _ _ hh => ⟨hh.1.2, hh.2⟩) (fun _ _ _ _ h => h) ?_
  refine rHoare_of_pre_fact (fun _ _ hh => hh.2) fun hkf => ?_
  simp only [SPComp.map]
  refine rHoare_bind (rHoare_conseq (fun _ _ hh => hh.1) (fun _ _ _ _ h => h) (rHoare_refl _))
    fun o o' => rHoare_ret fun _ _ hh => ?_
  obtain ⟨rfl, rfl⟩ := hh
  exact Or.inr ⟨rfl, ⟨rfl, wInv_nextK sp hw e kf (wDrawK_ph sp fr hfrp hfrp hkf)⟩, rfl⟩

/-- **The counter of the last hybrid world at a split.** In a run of at most `n` activations,
the hybrid world never exceeds `n` non-idle activations. -/
theorem world_end_prBadK (n : ℕ) {cre : K → SPComp K} {rd1 rd2 : K → SPComp V} {ζ : Type}
    (Z : Env (Strat ζ (HEv ⊕ AEv K) (HOut V ⊕ AOut)) ζ) (hZ : Z.input.rounds ≤ n) :
    prBad (worldK sp fr realV idealD n cre rd1 rd2) (fun w => decide (n < w.steps)) Z = 0 :=
  prBad_counter_eq_zero _ WSt.steps n (fun w e q hq => by
    rw [world_stepsK sp fr realV idealD hq]; split_ifs <;> omega) Z
    (by simpa [worldK, WSt.init] using hZ)

/-! ## The first hybrid world and the real stack, at a split -/

/-- The record of the session `x` with the key of its index. -/
def fillRec (w : WSt K) (x : Inst) (r : Rec K) : Rec K :=
  match w.ix x with
  | some j => { r with key := some (w.kv j) }
  | none => r

/-- The state of `F_AKE` of a hybrid state: each completed session holds the key of its
index. -/
def fill (w : WSt K) : St K := { w.st with recs := fun x => (w.st.recs x).map (fillRec w x) }

omit [Inhabited K] in
/-- Extensionality of the state of `F_AKE`. -/
theorem St.ext' {t t' : St K} (h1 : t.recs = t'.recs) (h2 : t.corrupt = t'.corrupt)
    (h3 : t.notices = t'.notices) (h4 : t.cursor = t'.cursor) : t = t' := by
  cases t; cases t'; simp only at h1 h2 h3 h4; subst h1 h2 h3 h4; rfl

omit [Inhabited K] in
/-- `newKeyStep` changes only the records. -/
theorem newKeyStep_fields (t : St K) (x : Inst) (k kf : K) :
    (newKeyStep t x k kf).corrupt = t.corrupt ∧ (newKeyStep t x k kf).notices = t.notices ∧
      (newKeyStep t x k kf).cursor = t.cursor := by
  unfold newKeyStep
  split
  · split_ifs <;> exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

omit [Inhabited K] in
/-- `newKeyFreshStep` changes only the records. -/
theorem newKeyFreshStep_fields (t : St K) (x : Inst) (k kf : K) :
    (newKeyFreshStep t x k kf).corrupt = t.corrupt ∧
      (newKeyFreshStep t x k kf).notices = t.notices ∧
      (newKeyFreshStep t x k kf).cursor = t.cursor := by
  unfold newKeyFreshStep
  split
  · split_ifs <;> exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

omit [Inhabited K] in
/-- A session without a key has no index, at a split. -/
theorem ix_none_of_key_noneK {w : WSt K} (hw : WInvK sp w) {x : Inst} {r : Rec K}
    (hx : w.st.recs x = some r) (hk : r.key = none) : w.ix x = none := by
  rcases hj : w.ix x with _ | j
  · rfl
  · obtain ⟨_, r', hr', hc⟩ := hw.1 x j hj
    rw [hx] at hr'; cases hr'
    obtain ⟨_, _, hkey⟩ := hw.2 x r hx hc
    rw [hk] at hkey; cases hkey

omit [Inhabited K] in
/-- Filling with keys that agree at the indices below `n` gives the same record. -/
theorem fillRec_congr {w w' : WSt K} {x : Inst} (hix : w'.ix x = w.ix x)
    (hkv : ∀ j, w.ix x = some j → w'.kv j = w.kv j) (r : Rec K) :
    fillRec w' x r = fillRec w x r := by
  unfold fillRec
  rw [hix]
  rcases hj : w.ix x with _ | j
  · rfl
  · simp only [hkv j hj]

omit [Inhabited K] in
/-- The record filled at an index. -/
theorem fillRec_some {w : WSt K} {x : Inst} {j : ℕ} (h : w.ix x = some j) (r : Rec K) :
    fillRec w x r = { r with key := some (w.kv j) } := by
  simp [fillRec, h]

omit [Inhabited K] in
/-- The record of a session without index is not filled. -/
theorem fillRec_none {w : WSt K} {x : Inst} (h : w.ix x = none) (r : Rec K) :
    fillRec w x r = r := by
  simp [fillRec, h]

omit [Inhabited K] in
/-- Filling keeps the peer, the role and the status. -/
theorem fillRec_partner (w : WSt K) (x y : Inst) (r p : Rec K) :
    Partner x r (fillRec w y p) ↔ Partner x r p := by
  unfold fillRec; split <;> rfl

omit [Inhabited K] in
/-- **Filling commutes with `newKey`**, at a split. -/
theorem fill_newKeyK {w : WSt K} (hw : WInvK sp w) (sid : SessionId) (pid : PartyId)
    (k kf : K) :
    fill (wNextK sp w (.inr (.newKey sid pid k)) kf) = newKeyStep (fill w) (sid, pid) k kf := by
  have hkv : ∀ y j, w.ix y = some j →
      (wNextK sp w (.inr (.newKey sid pid k)) kf).kv j = w.kv j := fun y j hj => by
    have := (hw.1 y j hj).1
    simp only [wNextK, isNewKey, ite_true]
    rw [Function.update_of_ne (by omega)]
  have hixw : (wNextK sp w (.inr (.newKey sid pid k)) kf).ix =
      newKeyIx w.st w.ix w.steps (sid, pid) := rfl
  obtain ⟨hc1, hn1, hu1⟩ := newKeyStep_fields (fill w) (sid, pid) k kf
  obtain ⟨hc2, hn2, hu2⟩ := newKeyStep_fields w.st (sid, pid) k (sp.ph k)
  refine St.ext' ?_ (by rw [hc1]; exact hc2) (by rw [hn1]; exact hn2) (by rw [hu1]; exact hu2)
  funext y
  change Option.map (fillRec (wNextK sp w (.inr (.newKey sid pid k)) kf) y)
      ((newKeyStep w.st (sid, pid) k (sp.ph k)).recs y) =
    (newKeyStep (fill w) (sid, pid) k kf).recs y
  rcases hx : w.st.recs (sid, pid) with _ | r
  · have hs : newKeyStep w.st (sid, pid) k (sp.ph k) = w.st := by simp [newKeyStep, hx]
    have hf : (fill w).recs (sid, pid) = none := by simp [fill, hx]
    have hs' : newKeyStep (fill w) (sid, pid) k kf = fill w := by simp [newKeyStep, hf]
    rw [hs, hs']
    change _ = Option.map (fillRec w y) (w.st.recs y)
    congr 1; funext r'
    exact fillRec_congr (by rw [hixw]; simp [newKeyIx, hx]) (hkv y) r'
  · have hf : (fill w).recs (sid, pid) = some (fillRec w (sid, pid) r) := by simp [fill, hx]
    by_cases hk : r.key.isNone
    · have hk' : r.key = none := Option.isNone_iff_eq_none.mp hk
      have hix : w.ix (sid, pid) = none := ix_none_of_key_noneK sp hw hx hk'
      rw [fillRec_none hix] at hf
      rw [newKeyStep_recs (fill w) _ r hf k kf y, newKeyStep_recs w.st _ r hx k _ y]
      by_cases hy : y = (sid, pid)
      · subst hy
        simp only [hk, true_and, ite_true, Option.map_some]
        congr 1
        by_cases hex : Exposed w.st (sid, pid) r
        · have hex' : Exposed (fill w) (sid, pid) r := hex
          have hi' : (wNextK sp w (.inr (.newKey sid pid k)) kf).ix (sid, pid) = none := by
            rw [hixw]; simp [newKeyIx, hx, hex, hix]
          rw [fillRec_none hi']
          simp [newKeyVal, hex, hex']
        · have hex' : ¬ Exposed (fill w) (sid, pid) r := hex
          simp only [hex, hex', ite_false]
          have hpf : (fill w).recs (sid, r.peer) =
              (w.st.recs (sid, r.peer)).map (fillRec w (sid, r.peer)) := rfl
          unfold newKeyVal
          rw [ite_eq_right hex, ite_eq_right hex', hpf]
          rcases hp : w.st.recs (sid, r.peer) with _ | p
          · have hi' : (wNextK sp w (.inr (.newKey sid pid k)) kf).ix (sid, pid) =
                some w.steps := by
              rw [hixw]; simp [newKeyIx, hx, hk, hex, hp]
            rw [fillRec_some hi']
            simp [wNextK, isNewKey]
          · simp only [Option.map_some]
            by_cases hpp : Partner (sid, pid) r p
            · obtain ⟨jp, hjp, _⟩ := hw.2 _ p hp hpp.2.2
              have hlt := (hw.1 _ jp hjp).1
              have hi' : (wNextK sp w (.inr (.newKey sid pid k)) kf).ix (sid, pid) = some jp := by
                rw [hixw]; simp [newKeyIx, hx, hk, hex, hp, hpp, hjp]
              rw [fillRec_some hi', ite_eq_left hpp,
                ite_eq_left ((fillRec_partner w _ _ r p).mpr hpp),
                fillRec_some hjp, hkv _ jp hjp]
              simp
            · have hi' : (wNextK sp w (.inr (.newKey sid pid k)) kf).ix (sid, pid) =
                  some w.steps := by
                rw [hixw]; simp [newKeyIx, hx, hk, hex, hp, hpp]
              rw [fillRec_some hi', ite_eq_right hpp,
                ite_eq_right (fun h => hpp ((fillRec_partner w _ _ r p).mp h))]
              simp [wNextK, isNewKey]
      · simp only [hy, and_false, ite_false]
        change Option.map _ (w.st.recs y) = Option.map (fillRec w y) (w.st.recs y)
        congr 1; funext r'
        refine fillRec_congr ?_ (hkv y) r'
        rw [hixw]
        simp only [newKeyIx, hx]
        split_ifs <;> simp [Function.update_of_ne hy]
    · have hfk : (fillRec w (sid, pid) r).key.isNone = false := by
        unfold fillRec
        split
        · rfl
        · rcases h : r.key with _ | kk
          · simp [h] at hk
          · simp
      rw [newKeyStep_recs (fill w) _ _ hf k kf y, newKeyStep_recs w.st _ r hx k _ y]
      simp only [hfk, hk, Bool.false_eq_true, false_and, ite_false]
      change Option.map _ (w.st.recs y) = Option.map (fillRec w y) (w.st.recs y)
      congr 1; funext r'
      refine fillRec_congr ?_ (hkv y) r'
      rw [hixw]
      simp [newKeyIx, hx, hk]

omit [Inhabited K] in
/-- **Filling commutes with `newKeyUnlinked`**, at a split. -/
theorem fill_newKeyFreshK {w : WSt K} (hw : WInvK sp w) (sid : SessionId) (pid : PartyId)
    (k kf : K) :
    fill (wNextK sp w (.inr (.newKeyUnlinked sid pid k)) kf) =
      newKeyFreshStep (fill w) (sid, pid) k kf := by
  have hkv : ∀ y j, w.ix y = some j →
      (wNextK sp w (.inr (.newKeyUnlinked sid pid k)) kf).kv j = w.kv j := fun y j hj => by
    have := (hw.1 y j hj).1
    simp only [wNextK, isNewKey, ite_true]
    rw [Function.update_of_ne (by omega)]
  have hixw : (wNextK sp w (.inr (.newKeyUnlinked sid pid k)) kf).ix =
      newKeyFreshIx w.st w.ix w.steps (sid, pid) := rfl
  obtain ⟨hc1, hn1, hu1⟩ := newKeyFreshStep_fields (fill w) (sid, pid) k kf
  obtain ⟨hc2, hn2, hu2⟩ := newKeyFreshStep_fields w.st (sid, pid) k (sp.ph k)
  refine St.ext' ?_ (by rw [hc1]; exact hc2) (by rw [hn1]; exact hn2) (by rw [hu1]; exact hu2)
  funext y
  change Option.map (fillRec (wNextK sp w (.inr (.newKeyUnlinked sid pid k)) kf) y)
      ((newKeyFreshStep w.st (sid, pid) k (sp.ph k)).recs y) =
    (newKeyFreshStep (fill w) (sid, pid) k kf).recs y
  rcases hx : w.st.recs (sid, pid) with _ | r
  · have hs : newKeyFreshStep w.st (sid, pid) k (sp.ph k) = w.st := by
      simp [newKeyFreshStep, hx]
    have hf : (fill w).recs (sid, pid) = none := by simp [fill, hx]
    have hs' : newKeyFreshStep (fill w) (sid, pid) k kf = fill w := by
      simp [newKeyFreshStep, hf]
    rw [hs, hs']
    change _ = Option.map (fillRec w y) (w.st.recs y)
    congr 1; funext r'
    exact fillRec_congr (by rw [hixw]; simp [newKeyFreshIx, hx]) (hkv y) r'
  · have hf : (fill w).recs (sid, pid) = some (fillRec w (sid, pid) r) := by simp [fill, hx]
    by_cases hk : r.key.isNone
    · have hk' : r.key = none := Option.isNone_iff_eq_none.mp hk
      have hix : w.ix (sid, pid) = none := ix_none_of_key_noneK sp hw hx hk'
      rw [fillRec_none hix] at hf
      rw [newKeyFreshStep_recs (fill w) _ r hf k kf y,
        newKeyFreshStep_recs w.st _ r hx k _ y]
      by_cases hy : y = (sid, pid)
      · subst hy
        simp only [hk, true_and, ite_true, Option.map_some]
        congr 1
        by_cases hex : Exposed w.st (sid, pid) r
        · have hex' : Exposed (fill w) (sid, pid) r := hex
          have hi' : (wNextK sp w (.inr (.newKeyUnlinked sid pid k)) kf).ix (sid, pid) =
              none := by
            rw [hixw]; simp [newKeyFreshIx, hx, hex, hix]
          rw [fillRec_none hi']
          simp [hex, hex']
        · have hex' : ¬ Exposed (fill w) (sid, pid) r := hex
          have hi' : (wNextK sp w (.inr (.newKeyUnlinked sid pid k)) kf).ix (sid, pid) =
              some w.steps := by
            rw [hixw]; simp [newKeyFreshIx, hx, hk, hex]
          rw [fillRec_some hi']
          simp [hex, hex', wNextK, isNewKey]
      · simp only [hy, and_false, ite_false]
        change Option.map _ (w.st.recs y) = Option.map (fillRec w y) (w.st.recs y)
        congr 1; funext r'
        refine fillRec_congr ?_ (hkv y) r'
        rw [hixw]
        simp only [newKeyFreshIx, hx]
        split_ifs <;> simp [Function.update_of_ne hy]
    · have hfk : (fillRec w (sid, pid) r).key.isNone = false := by
        unfold fillRec
        split
        · rfl
        · rcases h : r.key with _ | kk
          · simp [h] at hk
          · simp
      rw [newKeyFreshStep_recs (fill w) _ _ hf k kf y,
        newKeyFreshStep_recs w.st _ r hx k _ y]
      simp only [hfk, hk, Bool.false_eq_true, false_and, ite_false]
      change Option.map _ (w.st.recs y) = Option.map (fillRec w y) (w.st.recs y)
      congr 1; funext r'
      refine fillRec_congr ?_ (hkv y) r'
      rw [hixw]
      simp [newKeyFreshIx, hx, hk]

omit [Inhabited K] in
/-- Filling commutes with `addSession`, at a split. -/
theorem fill_addSessionK {w : WSt K} (hw : WInvK sp w) (sid : SessionId) (pid peer : PartyId)
    (role : Role) (kf : K) :
    fill (wNextK sp w (.inl (.newSession sid pid peer role)) kf) =
      addSession (fill w) (sid, pid) peer role := by
  have hS : ((fill w).recs (sid, pid)).isSome = (w.st.recs (sid, pid)).isSome := by
    simp [fill]
  by_cases h : (w.st.recs (sid, pid)).isSome
  · have h' : ((fill w).recs (sid, pid)).isSome := hS ▸ h
    have e1 : addSession w.st (sid, pid) peer role = w.st := by simp [addSession, h]
    have e2 : addSession (fill w) (sid, pid) peer role = fill w := by simp [addSession, h']
    rw [e2]
    refine St.ext' ?_ (by simp [fill, wNextK, stNextK, e1]) (by simp [fill, wNextK, stNextK, e1])
      (by simp [fill, wNextK, stNextK, e1])
    funext y
    change Option.map (fillRec (wNextK sp w (.inl (.newSession sid pid peer role)) kf) y)
      ((addSession w.st (sid, pid) peer role).recs y) = Option.map (fillRec w y) (w.st.recs y)
    rw [e1]
    rfl
  · have h' : ¬ ((fill w).recs (sid, pid)).isSome := hS ▸ h
    have hix : w.ix (sid, pid) = none := by
      rcases hj : w.ix (sid, pid) with _ | j
      · rfl
      · obtain ⟨_, r, hr, _⟩ := hw.1 _ j hj; simp [hr] at h
    refine St.ext' ?_ (by simp [fill, wNextK, stNextK, addSession, h])
      (by simp [fill, wNextK, stNextK, addSession, h])
      (by simp [fill, wNextK, stNextK, addSession, h])
    funext y
    change Option.map (fillRec w y) ((addSession w.st (sid, pid) peer role).recs y) =
      (addSession (fill w) (sid, pid) peer role).recs y
    rw [addSession_recs, addSession_recs]
    simp only [h, h', Bool.false_eq_true, ite_false]
    by_cases hy : y = (sid, pid)
    · subst hy; simp [fillRec_none hix]
    · simp only [hy, ite_false]; rfl

omit [Inhabited K] in
/-- The step of `poll`. -/
theorem pollStep_eq (t : St K) :
    pollStep t = ({ t with cursor := if (t.notices[t.cursor]?).isSome then t.cursor + 1
        else t.cursor }, t.notices[t.cursor]?) := by
  unfold pollStep
  split <;> simp_all

omit [Inhabited K] in
/-- The real views of the first hybrid world at a split are the views of the real stack at the
filled state. -/
theorem chanOut_fillK {w : WSt K} (hw : WInvK sp w) (x : Inst) :
    chanOut (wViewK sp realV idealD 0 realV realV w x) w.st x =
      chanOut (fun _ k => realV k) (fill w) x := by
  unfold chanOut
  rw [show (fill w).recs x = (w.st.recs x).map (fillRec w x) from rfl]
  rcases hx : w.st.recs x with _ | r
  · rfl
  · simp only [Option.map_some]
    rcases hj : w.ix x with _ | j
    · rw [fillRec_none hj]
      rcases hk : r.key with _ | k
      · rfl
      · simp only [wViewK, hj]
    · rw [fillRec_some hj]
      obtain ⟨_, r', hr', hc⟩ := hw.1 x j hj
      rw [hx] at hr'; cases hr'
      obtain ⟨_, _, hkey⟩ := hw.2 x r hx hc
      rw [hkey]
      simp only [wViewK, hj, readOutK]
      split_ifs <;> first | omega | (subst_vars; rfl)

/-- **The first hybrid world at a split is the real stack over `F_AKEK fr`**: filling the keys
of the indices is a step map on the invariant, for a fresh-key kernel that keeps the stand-in
of the proposal. -/
theorem world_zero_stepMapK (hfrp : ∀ p kf, IsOutcome (fr p) kf → sp.ph kf = sp.ph p) :
    Sys.StepMapOn (worldK sp fr realV idealD 0 fr realV realV) (FRK fr realV) (WInvK sp)
      fill where
  init_inv := wInv_initK sp
  init_map := by
    refine St.ext' ?_ rfl rfl rfl
    funext y; rfl
  pres w e hw q hq := world_invK sp fr realV idealD hfrp hfrp hw hq
  step w e hw := by
    rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) |
      (_ | _ | pid | ⟨sid, pid⟩ | ⟨sid, pid, k⟩ | ⟨sid, pid, k⟩)
    · simp only [worldK, wDrawK, isNewKey, Bool.false_eq_true, ite_false, SPComp.pure_bind,
        wOutK, SPComp.map]
      rw [fill_addSessionK sp hw]
      simp [FRK, chanHon, SPComp.map]
    · simp only [worldK, wDrawK, isNewKey, Bool.false_eq_true, ite_false, SPComp.pure_bind,
        wOutK]
      rw [chanOut_fillK sp realV idealD hw]
      simp only [FRK, Sys.ofPorts_step_inl, chanHon, SPComp.map, SPComp.bind_assoc,
        SPComp.pure_bind]
      rfl
    · simp only [worldK, wDrawK, isNewKey, Bool.false_eq_true, ite_false, SPComp.pure_bind,
        wOutK, SPComp.map]
      simp only [FRK, Sys.ofPorts_step_inr, advSysK, advSysImp, SPComp.map, SPComp.pure_bind]
      rfl
    · simp only [worldK, wDrawK, isNewKey, Bool.false_eq_true, ite_false, SPComp.pure_bind,
        wOutK, SPComp.map]
      simp only [FRK, Sys.ofPorts_step_inr, advSysK, advSysImp, SPComp.map, SPComp.pure_bind]
      congr 2
      · refine St.ext' ?_
          (by change (pollStep w.st).1.corrupt = _; rw [pollStep_eq, pollStep_eq]; rfl)
          (by change (pollStep w.st).1.notices = _; rw [pollStep_eq, pollStep_eq]; rfl)
          (by change (pollStep w.st).1.cursor = _; rw [pollStep_eq, pollStep_eq]; rfl)
        funext y
        change Option.map _ ((pollStep w.st).1.recs y) = (pollStep (fill w)).1.recs y
        rw [pollStep_recs, pollStep_recs]; rfl
      · rw [pollStep_eq, pollStep_eq]; rfl
    · simp only [worldK, wDrawK, isNewKey, Bool.false_eq_true, ite_false, SPComp.pure_bind,
        wOutK, SPComp.map]
      simp only [FRK, Sys.ofPorts_step_inr, advSysK, advSysImp, SPComp.map, SPComp.pure_bind]
      rfl
    · simp only [worldK, wDrawK, isNewKey, Bool.false_eq_true, ite_false, SPComp.pure_bind,
        wOutK, SPComp.map]
      simp only [FRK, Sys.ofPorts_step_inr, advSysK, advSysImp, Bool.not_true, impStepOf_false,
        SPComp.map, SPComp.pure_bind]
      rfl
    · simp only [worldK, wDrawK, isNewKey, ite_true, ite_self, wOutK, SPComp.map,
        SPComp.bind_assoc, SPComp.pure_bind, propOf]
      simp only [FRK, Sys.ofPorts_step_inr, advSysK, advSysImp, SPComp.map, SPComp.bind_assoc,
        SPComp.pure_bind, fill_newKeyK sp hw]
    · simp only [worldK, wDrawK, isNewKey, ite_true, ite_self, wOutK, SPComp.map,
        SPComp.bind_assoc, SPComp.pure_bind, propOf]
      simp only [FRK, Sys.ofPorts_step_inr, advSysK, advSysImp, SPComp.map, SPComp.bind_assoc,
        SPComp.pure_bind, fill_newKeyFreshK sp hw, ite_true]

omit [Inhabited K] [Inhabited Ks] in
/-- The views of the step `i + 1` from below, at a split. -/
theorem readOut_succK (i : ℕ) (w : WSt K) (j : ℕ) :
    readOutK sp realV idealD i (fun k => idealD (sp.dat k)) (fun k => idealD (sp.dat k)) w j =
      readOutK sp realV idealD (i + 1) realV realV w j := by
  rcases lt_trichotomy j i with h | rfl | h
  · simp [readOutK, h, show j < i + 1 by omega]
  · simp [readOutK]
  · rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt h) with h' | h'
    · subst h'; simp [readOutK]
    · simp [readOutK, show ¬ j < i by omega, show j ≠ i by omega, show ¬ j < i + 1 by omega,
        show j ≠ i + 1 by omega]

/-- The hybrid world `i` at a split whose reads of the key `i` are ideal is the hybrid world
`i + 1`. -/
theorem chalWorld_idealK (i : ℕ) :
    worldK sp fr realV idealD i fr (fun k => idealD (sp.dat k)) (fun k => idealD (sp.dat k)) =
      worldK sp fr realV idealD (i + 1) fr realV realV := by
  simp only [worldK]
  congr 1
  funext w e
  have hd : wDrawK fr i fr w e = wDrawK fr (i + 1) fr w e := by
    simp [wDrawK]
  rw [hd, wOut_congrK sp realV idealD e fun _ _ j _ _ => readOut_succK sp realV idealD i w j]

end StepsK

/-! ## The two-stage game at a chosen datum -/

/-- **A two-stage adversary against a view at a chosen datum**: the first stage outputs a state
and a datum, the second stage guesses from the state and the view drawn at the datum. -/
structure CDAdv (σ D V : Type) where
  /-- The first stage: a state and the chosen datum. -/
  pre : SPComp (σ × D)
  /-- The second stage: the guess from the state and the view. -/
  guess : σ → V → SPComp Bool

/-- The game of a two-stage adversary with the view `ch d` at the chosen datum `d`. -/
noncomputable def CDAdv.game {σ D V : Type} (A : CDAdv σ D V) (ch : D → SPComp V) :
    SPComp Bool :=
  SPComp.bind A.pre fun p => SPComp.bind (ch p.2) (A.guess p.1)

/-- **The chosen-datum advantage** of a two-stage adversary between the views `real d` and
`ideal d` at the datum `d` that its first stage chooses. -/
noncomputable def CDAdv.advantage {σ D V : Type} (real ideal : D → SPComp V)
    (A : CDAdv σ D V) : ℝ≥0∞ :=
  Advantage (A.game real) (A.game ideal)

/-! ## One step of the hybrid argument at a split -/

section HybK

variable {K V Ks D : Type} [Inhabited K] [Fintype Ks] [Nonempty Ks] [Inhabited Ks]
  (sp : KeySplit K Ks D) (realV : K → SPComp V) (idealD : D → SPComp V)

/-- The hybrid world `i` at the split `sp`: the keys below `i` read ideally at their datum, the
keys from `i` on read really, every key drawn by the kernel `sp.fresh`. -/
noncomputable abbrev hybK (i : ℕ) : Sys (WSt K) (HEv ⊕ AEv K) (HOut V ⊕ AOut) :=
  worldK sp sp.fresh realV idealD i sp.fresh realV realV

/-- The world of the second stage of the reduction of the step `i`: the first read of the key
`i` returns the challenge `v`, its later reads are ideal. -/
noncomputable abbrev chalWorldK (i : ℕ) (v : V) : Sys (WSt K) (HEv ⊕ AEv K) (HOut V ⊕ AOut) :=
  worldK sp sp.fresh realV idealD i sp.fresh (fun _ => SPComp.pure v)
    (fun k => idealD (sp.dat k))

/-- **The two-stage reduction of the step `i`.** The first stage runs the environment `Z` from
its heap against the hybrid world `i + 1` up to the first `getKey` of the key `i`, and outputs
the split point and the datum of the key `i`. The second stage continues the run from the split
point against the world whose first read of the key `i` returns the challenge view, and applies
the distinguisher of `Z`. -/
noncomputable def hopRedK (i : ℕ) {ζ : Type}
    (Z : Env (Strat ζ (HEv ⊕ AEv K) (HOut V ⊕ AOut)) ζ) :
    CDAdv (ℕ × (ζ × WSt K × Bool) × Option (HEv ⊕ AEv K)) D V where
  pre _ := SPComp.map (fun s => (s, sp.dat (s.2.1.2.1.kv i)))
    (loopTo (hybK sp realV idealD (i + 1)) (fun _ => false) Z.input
      (fun w e => useK i w e = true) Z.input.rounds (Z.input.init, WSt.init, false)) Z.heap
  guess s v := SPComp.bind (loopRest (chalWorldK sp realV idealD i v) (fun _ => false) Z.input s)
    fun c => Z.dist c.1

/-- The game of the two-stage reduction from the empty heap is the two-stage run from the heap of
the environment. -/
theorem hopRedK_game (i : ℕ) {ζ : Type} (Z : Env (Strat ζ (HEv ⊕ AEv K) (HOut V ⊕ AOut)) ζ)
    (ch : D → SPComp V) :
    prTrue ((hopRedK sp realV idealD i Z).game ch) Heap.empty =
      prTrue (SPComp.bind (loopTo (hybK sp realV idealD (i + 1)) (fun _ => false) Z.input
          (fun w e => useK i w e = true) Z.input.rounds (Z.input.init, WSt.init, false))
        fun s => SPComp.bind (ch (sp.dat (s.2.1.2.1.kv i))) fun v =>
          SPComp.bind (loopRest (chalWorldK sp realV idealD i v) (fun _ => false) Z.input s)
            fun c => Z.dist c.1) Z.heap := by
  have h : prTrue ((hopRedK sp realV idealD i Z).game ch) Heap.empty =
      prTrue (SPComp.bind (SPComp.map (fun s => (s, sp.dat (s.2.1.2.1.kv i)))
        (loopTo (hybK sp realV idealD (i + 1)) (fun _ => false) Z.input
          (fun w e => useK i w e = true) Z.input.rounds (Z.input.init, WSt.init, false)))
        fun p => SPComp.bind (ch p.2) ((hopRedK sp realV idealD i Z).guess p.1)) Z.heap := rfl
  rw [h]
  simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  rfl

omit [Inhabited K] [Inhabited Ks] in
/-- The kernel `sp.fresh` neither touches the heap nor fails. -/
theorem KeySplit.fresh_pureNF (p : K) :
    SPComp.IsPure (sp.fresh p) ∧ SPComp.NoFail (sp.fresh p) :=
  CatCrypt.Crypto.PAKE.CPaceSquare.PureNF.map _ (CatCrypt.Crypto.PAKE.CPaceSquare.pureNF_sample Ks)

omit [Inhabited K] in
/-- The keys drawn by `sp.fresh` have the stand-in of the proposal. -/
theorem KeySplit.ph_of_fresh (p kf : K)
    (h : IsOutcome (sp.fresh p) kf) : sp.ph kf = sp.ph p := by
  obtain ⟨s, _, rfl⟩ := isOutcome_map_iff.mp h
  simp [KeySplit.ph, sp.dat_key]

/-- **One step of the hybrid argument at a split.** For views `realV k` and `idealD d` that
neither touch the heap nor fail, the distance between the hybrid worlds `i` and `i + 1` at the
environment `Z` is at most the chosen-datum advantage of the two-stage reduction `hopRedK i Z`
between the real view at a uniform secret part (`sp.real realV`) and the ideal view `idealD`,
plus the probability that the key `i` is read twice in the world `i`. -/
theorem hyb_stepK (hR : ∀ k, SPComp.IsPure (realV k) ∧ SPComp.NoFail (realV k))
    (hI : ∀ d, SPComp.IsPure (idealD d) ∧ SPComp.NoFail (idealD d)) (i : ℕ) {ζ : Type}
    (Z : Env (Strat ζ (HEv ⊕ AEv K) (HOut V ⊕ AOut)) ζ) :
    Env.gap (view (hybK sp realV idealD i)) (view (hybK sp realV idealD (i + 1))) Z ≤
      (hopRedK sp realV idealD i Z).advantage (sp.real realV) idealD +
        prBad (hybK sp realV idealD i) (reuse i) Z := by
  have hs := CatCrypt.Crypto.PAKE.CPaceSquare.pureNF_sample Ks
  have hF := KeySplit.fresh_pureNF sp
  have hRK : ∀ d, SPComp.IsPure (sp.real realV d) ∧ SPComp.NoFail (sp.real realV d) :=
    fun d => CatCrypt.Crypto.PAKE.CPaceSquare.PureNF.bind hs fun s => hR _
  set rdI : K → SPComp V := fun k => idealD (sp.dat k) with hrdI
  set L := worldK sp sp.fresh realV idealD i sp.fresh (fun k => sp.real realV (sp.dat k)) rdI
  set Hs : Ks → Sys (WSt K) (HEv ⊕ AEv K) (HOut V ⊕ AOut) := fun s =>
    worldK sp sp.fresh realV idealD i (fun p => SPComp.pure (sp.key s (sp.dat p))) realV realV
  set Ls : Ks → Sys (WSt K) (HEv ⊕ AEv K) (HOut V ⊕ AOut) := fun s =>
    worldK sp sp.fresh realV idealD i sp.fresh (fun k => realV (sp.key s (sp.dat k))) rdI
  -- the key `i` drawn before the run, in the world `i` and in the lazy world `L`
  have hH : ∀ bad : WSt K → Bool, SPComp.bind (SPComp.sample Ks)
      (fun s => run (Hs s) bad Z.input) = run (hybK sp realV idealD i) bad Z.input := fun bad =>
    run_world_createK sp sp.fresh realV idealD i hs.1 hs.2 (fun s p => sp.key s (sp.dat p))
      (fun _ => rfl) realV realV bad Z.input
  have hL : SPComp.bind (SPComp.sample Ks) (fun s => run (Ls s) (fun _ => false) Z.input) =
      run L (fun _ => false) Z.input :=
    run_world_readK sp sp.fresh realV idealD i sp.fresh hs.1 hs.2
      (fun k => sp.real realV (sp.dat k)) (fun s k => realV (sp.key s (sp.dat k))) rdI
      (fun _ _ _ => rfl) _ Z.input
  -- up to a second read of the key `i`, for each secret part
  have hup : ∀ s, Realizes (Hs s) (Ls s) (fun _ Z => prBad (Hs s) (reuse i) Z) := fun s =>
    world_upto_reuseK sp sp.fresh realV idealD i (fun a b => a = sp.key s (sp.dat b))
      (fun p => by
        unfold KeySplit.fresh SPComp.map
        exact rHoare_sample_r fun s' => rHoare_ret fun _ _ hh => ⟨hh, by rw [sp.dat_key]⟩)
      (fun a b h => by rw [h]) (fun k => (hR k).2) (fun d => (hI d).2) (fun p => (hF p).2)
      (fun _ => SPComp.pure_noFail _) (fun p => (hF p).2) (fun k => (hR k).2)
      (fun k => (hR _).2) (fun k => (hR k).2) (fun k => (hI _).2)
  have h1 : absDiff (prTrue (SPComp.bind (view (hybK sp realV idealD i) Z.input) Z.dist) Z.heap)
      (prTrue (SPComp.bind (view L Z.input) Z.dist) Z.heap) ≤
      prBad (hybK sp realV idealD i) (reuse i) Z := by
    have h := absDiff_prTrue_bind_le_bind (SPComp.sample Ks)
      (fun s => SPComp.bind (view (Hs s) Z.input) Z.dist)
      (fun s => SPComp.bind (view (Ls s) Z.input) Z.dist)
      (fun s => SPComp.bind (run (Hs s) (reuse i) Z.input) fun q => SPComp.pure q.2.2)
      Z.heap fun s h => hup s ζ ⟨Z.input, h, Z.dist⟩
    simp only [view, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind] at h
    simp only [prBad, view, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, ← hH, ← hL]
    exact h
  -- the split at the first read of the key `i`
  have hI1 : hybK sp realV idealD (i + 1) =
      worldK sp sp.fresh realV idealD i sp.fresh rdI rdI :=
    (chalWorld_idealK sp sp.fresh realV idealD i).symm
  have hcongr : loopTo L (fun _ => false) Z.input (fun w e => useK i w e = true)
        Z.input.rounds (Z.input.init, WSt.init, false) =
      loopTo (hybK sp realV idealD (i + 1)) (fun _ => false) Z.input
        (fun w e => useK i w e = true) Z.input.rounds (Z.input.init, WSt.init, false) := by
    rw [hI1]
    refine loopTo_congr _ L (fun _ => false) Z.input _ (fun _ => True)
      (fun _ _ _ _ _ => trivial) (fun t e _ hu => ?_) _ _ trivial
    simp only [L, worldK]
    rw [wOut_congrK sp realV idealD e fun sid pid j he hj => readOut_neK sp realV idealD
      (fun hji : j = i => hu (useK_iff.mpr ⟨sid, pid, he, by rw [← hji]; exact hj⟩))
      _ _ _ _ t]
  have hsL := run_world_read_atK sp sp.fresh realV idealD i sp.fresh
    (fun k => sp.real realV (sp.dat k)) rdI (fun k => hRK _) (fun _ => false) Z.input
  have hsI := run_world_read_atK sp sp.fresh realV idealD i sp.fresh rdI rdI
    (fun k => hI _) (fun _ => false) Z.input
  have hreal : prTrue (SPComp.bind (view L Z.input) Z.dist) Z.heap =
      prTrue ((hopRedK sp realV idealD i Z).game (sp.real realV)) Heap.empty := by
    rw [hopRedK_game, ← hcongr]
    simp only [view]
    rw [show run L (fun _ => false) Z.input = _ from hsL]
    simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    rfl
  have hideal : prTrue (SPComp.bind (view (hybK sp realV idealD (i + 1)) Z.input) Z.dist)
      Z.heap = prTrue ((hopRedK sp realV idealD i Z).game idealD) Heap.empty := by
    rw [hopRedK_game, hI1]
    simp only [view, hsI, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    rfl
  rw [hreal] at h1
  unfold Env.gap
  refine le_trans (absDiff_triangle _
    (prTrue ((hopRedK sp realV idealD i Z).game (sp.real realV)) Heap.empty) _) ?_
  rw [hideal, add_comm]
  exact add_le_add le_rfl h1

/-- The bound of the hybrid argument at a split at an environment `Z` of the functionality:
over the keys `i` below the number of activations of `Z`, the chosen-datum advantage of the
two-stage reduction `hopRedK i Z`, plus the probability that the key `i` is read twice. -/
noncomputable def scBoundK {ζ : Type} (Z : Env (Strat ζ (HEv ⊕ AEv K) (HOut V ⊕ AOut)) ζ) :
    ℝ≥0∞ :=
  ∑ i ∈ Finset.range Z.input.rounds,
    ((hopRedK sp realV idealD i Z).advantage (sp.real realV) idealD +
      prBad (hybK sp realV idealD i) (reuse i) Z)

/-- **`F_AKEK sp.fresh` followed by the ratchet realizes the ideal secure channel with a datum
`F_SCK`.** For views `realV k` and `idealD d` that neither touch the heap nor fail,
`FRK sp.fresh realV` realizes `F_SCK sp realV idealD` with the bound `scBoundK`: a hybrid
argument over the keys that the run creates (one per activation), each step bounded by
`hyb_stepK`. -/
theorem FRK_realizes_F_SCK (hR : ∀ k, SPComp.IsPure (realV k) ∧ SPComp.NoFail (realV k))
    (hI : ∀ d, SPComp.IsPure (idealD d) ∧ SPComp.NoFail (idealD d)) :
    Realizes (FRK sp.fresh realV) (F_SCK sp realV idealD)
      (fun _ Z => scBoundK sp realV idealD Z) := by
  have hfrp : ∀ p kf, IsOutcome (sp.fresh p) kf → sp.ph kf = sp.ph p := sp.ph_of_fresh
  have h0 : Realizes (FRK sp.fresh realV) (hybK sp realV idealD 0) (fun _ _ => 0) :=
    realizes_symm (world_zero_stepMapK sp sp.fresh realV idealD hfrp).realizes
  have hH := Realizes.hybrid_rounds (hybK sp realV idealD) (F_SCK sp realV idealD)
    (fun i _ Z => (hopRedK sp realV idealD i Z).advantage (sp.real realV) idealD +
      prBad (hybK sp realV idealD i) (reuse i) Z)
    (fun _ _ => 0) (fun i _ Z => hyb_stepK sp realV idealD hR hI i Z) fun _ Z => by
      have h := world_endK sp sp.fresh realV idealD Z.input.rounds (fun k => (hR k).2)
        (fun d => (hI d).2) (KeySplit.fresh_pureNF sp) hfrp _ Z
      dsimp only at h
      rwa [world_end_prBadK sp sp.fresh realV idealD _ Z le_rfl] at h
  intro ζ Z
  have := (h0.trans hH) ζ Z
  simpa [scBoundK] using this

end HybK

/-! ## Steps of the hybrid worlds -/

section Steps

variable {K V : Type} [Fintype K] [Nonempty K] [Inhabited K]
  (realV : K → SPComp V) (idealV : SPComp V)

/-- The outcomes of a step of a hybrid world: the next state at a possible draw. -/
theorem world_outcome {i : ℕ} {cre : SPComp K} {rd1 rd2 : K → SPComp V} {w : WSt K}
    {e : HEv ⊕ AEv K} {q : WSt K × (HOut V ⊕ AOut)}
    (hq : IsOutcome ((world realV idealV i cre rd1 rd2).step w e) q) :
    ∃ kf, IsOutcome (wDraw i cre w e) kf ∧ q.1 = wNext w e kf :=
  world_outcomeK _ _ realV _ hq

/-- The steps of a hybrid world keep the invariant. -/
theorem world_inv {i : ℕ} {cre : SPComp K} {rd1 rd2 : K → SPComp V} {w : WSt K}
    {e : HEv ⊕ AEv K} {q : WSt K × (HOut V ⊕ AOut)} (hw : WInv w)
    (hq : IsOutcome ((world realV idealV i cre rd1 rd2).step w e) q) : WInv q.1 := by
  obtain ⟨kf, _, h⟩ := world_outcome realV idealV hq
  rw [h]; exact wInv_next hw e kf

/-- The number of activations after a step. -/
theorem world_steps {i : ℕ} {cre : SPComp K} {rd1 rd2 : K → SPComp V} {w : WSt K}
    {e : HEv ⊕ AEv K} {q : WSt K × (HOut V ⊕ AOut)}
    (hq : IsOutcome ((world realV idealV i cre rd1 rd2).step w e) q) :
    q.1.steps = w.steps + (if isIdle e then 0 else 1) :=
  world_stepsK _ _ realV _ hq

/-- The read counts after a step. -/
theorem world_rd {i : ℕ} {cre : SPComp K} {rd1 rd2 : K → SPComp V} {w : WSt K}
    {e : HEv ⊕ AEv K} {q : WSt K × (HOut V ⊕ AOut)}
    (hq : IsOutcome ((world realV idealV i cre rd1 rd2).step w e) q) :
    q.1.rd = rdNext w e :=
  world_rdK _ _ realV _ hq

/-- A hybrid world is idle at the idle event of the adversary. -/
theorem world_idleAt (i : ℕ) (cre : SPComp K) (rd1 rd2 : K → SPComp V) :
    MultiHybrid.IdleAt (world realV idealV i cre rd1 rd2) (.inr .idle) (.inr .ack) :=
  world_idleAtK _ _ realV _ i _ rd1 rd2

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- The outputs of a hybrid world do not fail when its views do not fail. -/
theorem wOut_noFail {i : ℕ} {rd1 rd2 : K → SPComp V}
    (hR : ∀ k, SPComp.NoFail (realV k)) (hI : SPComp.NoFail idealV)
    (h1 : ∀ k, SPComp.NoFail (rd1 k)) (h2 : ∀ k, SPComp.NoFail (rd2 k))
    (w : WSt K) (e : HEv ⊕ AEv K) : SPComp.NoFail (wOut realV idealV i rd1 rd2 w e) :=
  wOut_noFailK _ realV _ hR (fun _ => hI) h1 h2 w e

/-- The steps of a hybrid world do not fail when its views and its creation do not fail. -/
theorem world_noFail {i : ℕ} {cre : SPComp K} {rd1 rd2 : K → SPComp V}
    (hR : ∀ k, SPComp.NoFail (realV k)) (hI : SPComp.NoFail idealV)
    (hc : SPComp.NoFail cre) (h1 : ∀ k, SPComp.NoFail (rd1 k)) (h2 : ∀ k, SPComp.NoFail (rd2 k))
    (w : WSt K) (e : HEv ⊕ AEv K) :
    SPComp.NoFail ((world realV idealV i cre rd1 rd2).step w e) :=
  world_noFailK _ _ realV _ hR (fun _ => hI)
    (fun _ => (CatCrypt.Crypto.PAKE.CPaceSquare.pureNF_sample K).2) (fun _ => hc) h1 h2 w e

/-! ## Deferred sampling at the creation of the key `i` -/

/-- **The key `i` drawn at its creation is the key `i` drawn before the run.** The hybrid world
whose key `i` is drawn from `c` at the activation `i` has the run of the worlds whose key `i` is
`k`, averaged over `k` drawn from `c` before the run. -/
theorem run_world_create (i : ℕ) {c : SPComp K} (hc : SPComp.IsPure c) (hcn : SPComp.NoFail c)
    (rd1 rd2 : K → SPComp V) {ζ : Type} (bad : WSt K → Bool) (Z : Strat ζ (HEv ⊕ AEv K) _) :
    SPComp.bind c (fun k => run (world realV idealV i (SPComp.pure k) rd1 rd2) bad Z) =
      run (world realV idealV i c rd1 rd2) bad Z :=
  run_world_createK _ _ realV _ i hc hcn (fun a _ => a) (cre := fun _ => c)
    (fun _ => (SPComp.bind_pure c).symm) rd1 rd2 bad Z

/-! ## Deferred sampling at the first read of the key `i` -/

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- The views of the indices other than `i` do not depend on the reads of `i`. -/
theorem readOut_ne {i j : ℕ} (h : j ≠ i) (rd1 rd2 rd1' rd2' : K → SPComp V) (w : WSt K) :
    readOut realV idealV i rd1 rd2 w j = readOut realV idealV i rd1' rd2' w j :=
  readOut_neK _ realV _ h rd1 rd2 rd1' rd2' w

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- After the first read of `i`, the views do not depend on the first read. -/
theorem readOut_post {i : ℕ} (rd1 rd1' rd2 : K → SPComp V) {w : WSt K} (h : w.rd i ≠ 0)
    (j : ℕ) : readOut realV idealV i rd1 rd2 w j = readOut realV idealV i rd1' rd2 w j :=
  readOut_postK _ realV _ rd1 rd1' rd2 h j

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- Two states with the same functionality state and indices, and two families of views that
agree at the index of the session that `e` reads, give the same output at `e`. -/
theorem wOut_congr₂ {i i' : ℕ} {rd1 rd2 rd1' rd2' : K → SPComp V} {w w' : WSt K}
    (hst : w.st = w'.st) (hix : w.ix = w'.ix) (e : HEv ⊕ AEv K)
    (h : ∀ sid pid j, e = .inl (.getKey sid pid) → w.ix (sid, pid) = some j →
      readOut realV idealV i rd1 rd2 w j = readOut realV idealV i' rd1' rd2' w' j) :
    wOut realV idealV i rd1 rd2 w e = wOut realV idealV i' rd1' rd2' w' e :=
  wOut_congr₂K _ realV _ hst hix e h

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- Two families of views that agree at the index of the session that `e` reads give the
same output at `e`. -/
theorem wOut_congr {i i' : ℕ} {rd1 rd2 rd1' rd2' : K → SPComp V} {w : WSt K}
    (e : HEv ⊕ AEv K)
    (h : ∀ sid pid j, e = .inl (.getKey sid pid) → w.ix (sid, pid) = some j →
      readOut realV idealV i rd1 rd2 w j = readOut realV idealV i' rd1' rd2' w j) :
    wOut realV idealV i rd1 rd2 w e = wOut realV idealV i' rd1' rd2' w e :=
  wOut_congr₂ realV idealV rfl rfl e h

/-- **The first read of the key `i` drawn at the read is the first read drawn before the run.**
If every key that the creation `cre` may give has the first view `rd1 kf = c`, the run of the
hybrid world with the first read `rd1` is the run of the worlds whose first read of the key `i`
returns `v`, averaged over `v` drawn from `c` before the run. -/
theorem run_world_read (i : ℕ) (cre : SPComp K) {c : SPComp V} (hc : SPComp.IsPure c)
    (hcn : SPComp.NoFail c) (rd1 rd2 : K → SPComp V)
    (hcre : ∀ kf, IsOutcome cre kf → rd1 kf = c) {ζ : Type} (bad : WSt K → Bool)
    (Z : Strat ζ (HEv ⊕ AEv K) _) :
    SPComp.bind c (fun v => run (world realV idealV i cre (fun _ => SPComp.pure v) rd2) bad Z) =
      run (world realV idealV i cre rd1 rd2) bad Z :=
  run_world_readK _ _ realV _ i (fun _ => cre) hc hcn rd1 (fun v _ => SPComp.pure v) rd2
    (fun _ kf hkf => by rw [hcre kf hkf]; exact (SPComp.bind_pure c).symm) bad Z

/-! ## A second read of the key `i` -/

omit [Fintype K] [Nonempty K] in
/-- The next states of related states are related, for draws that agree unless the activation
creates the key `i`. -/
theorem relExcept_next {i : ℕ} {a b : WSt K} (h : relExcept i a b) (e : HEv ⊕ AEv K)
    {kf kf' : K} (hk : a.steps ≠ i → kf = kf') :
    relExcept i (wNext a e kf) (wNext b e kf') :=
  relExcept_nextK _ h e hk

/-- **Up to a second read of the key `i`.** Two hybrid worlds whose key `i` is created as `k`
and as a uniform key, whose first read of the key `i` does not depend on the key, and whose
later reads differ, are at distance at most the probability that the key `i` is read twice in
the first world. -/
theorem world_upto_reuse (i : ℕ) (k : K) {rd1 rdA rdB : K → SPComp V}
    (hrd1 : ∀ a b, rd1 a = rd1 b) (hR : ∀ k, SPComp.NoFail (realV k))
    (hI : SPComp.NoFail idealV) (h1 : ∀ k, SPComp.NoFail (rd1 k))
    (hA : ∀ k, SPComp.NoFail (rdA k)) (hB : ∀ k, SPComp.NoFail (rdB k)) :
    Realizes (world realV idealV i (SPComp.pure k) rd1 rdA)
      (world realV idealV i (SPComp.sample K) rd1 rdB)
      (fun _ Z => prBad (world realV idealV i (SPComp.pure k) rd1 rdA) (reuse i) Z) := by
  have hs := CatCrypt.Crypto.PAKE.CPaceSquare.pureNF_sample K
  refine world_upto_reuseK _ _ realV _ i (fun _ _ => True) (fun _ => ?_)
    (fun a b _ => hrd1 a b) hR (fun _ => hI) (fun _ => hs.2) (fun _ => SPComp.pure_noFail k)
    (fun _ => hs.2) h1 h1 hA hB
  rw [← SPComp.bind_pure (SPComp.sample K)]
  exact rHoare_sample_r fun _ => rHoare_ret fun _ _ hh => ⟨hh, trivial⟩

/-! ## The last hybrid world and the ideal secure channel -/

/-- The output of `F_SC` at an event. -/
noncomputable def scOut (t : St K) : HEv ⊕ AEv K → SPComp (HOut V ⊕ AOut) :=
  scOutK (KeySplit.trivial K) realV (fun _ => idealV) t

omit [Fintype K] [Nonempty K] in
/-- The steps of `F_SC`: the next state of the functionality with the key `default` and the
output `scOut`. -/
theorem F_SC_step (t : St K) (e : HEv ⊕ AEv K) :
    (F_SC realV idealV).step t e =
      SPComp.map (fun o => (stNext t e, o)) (scOut realV idealV t e) :=
  F_SCK_step _ realV _ t e

omit [Fintype K] [Nonempty K] in
/-- In a state of the invariant whose indices are below `n`, the hybrid world `n` with real
reads outputs as `F_SC`. -/
theorem wOut_eq_scOut {n : ℕ} {w : WSt K} (hw : WInv w) (hn : w.steps ≤ n)
    (e : HEv ⊕ AEv K) :
    wOut realV idealV n realV realV w e = scOut realV idealV w.st e :=
  wOut_eq_scOutK _ realV _ hw hn e

omit [Inhabited K] in
/-- The draws of a hybrid world neither touch the heap nor fail, for a creation that does
not. -/
theorem wDraw_pureNF {i : ℕ} {cre : SPComp K} (hc : SPComp.IsPure cre ∧ SPComp.NoFail cre)
    [Inhabited K] (w : WSt K) (e : HEv ⊕ AEv K) :
    SPComp.IsPure (wDraw i cre w e) ∧ SPComp.NoFail (wDraw i cre w e) :=
  wDrawK_pureNF _ (fun _ => CatCrypt.Crypto.PAKE.CPaceSquare.pureNF_sample K) (fun _ => hc) w e

/-- **The last hybrid world is the ideal secure channel up to `n` activations.** The hybrid
world `n` with real reads realizes `F_SC` with bound the probability that the run exceeds `n`
non-idle activations. -/
theorem world_end (n : ℕ) (hR : ∀ k, SPComp.NoFail (realV k)) (hI : SPComp.NoFail idealV) :
    Realizes (world realV idealV n (SPComp.sample K) realV realV) (F_SC realV idealV)
      (fun _ Z => prBad (world realV idealV n (SPComp.sample K) realV realV)
        (fun w => decide (n < w.steps)) Z) :=
  world_endK _ _ realV _ n hR (fun _ => hI)
    (fun _ => CatCrypt.Crypto.PAKE.CPaceSquare.pureNF_sample K) (fun _ _ _ => rfl)

/-- **The counter of the last hybrid world.** In a run of at most `n` activations, the hybrid
world never exceeds `n` non-idle activations. -/
theorem world_end_prBad (n : ℕ) {cre : SPComp K} {rd1 rd2 : K → SPComp V} {ζ : Type}
    (Z : Env (Strat ζ (HEv ⊕ AEv K) (HOut V ⊕ AOut)) ζ) (hZ : Z.input.rounds ≤ n) :
    prBad (world realV idealV n cre rd1 rd2) (fun w => decide (n < w.steps)) Z = 0 :=
  world_end_prBadK _ _ realV _ n Z hZ

/-! ## The first hybrid world and the real stack over `F_AKE` -/

omit [Fintype K] [Nonempty K] in
/-- A session without a key has no index. -/
theorem ix_none_of_key_none {w : WSt K} (hw : WInv w) {x : Inst} {r : Rec K}
    (hx : w.st.recs x = some r) (hk : r.key = none) : w.ix x = none :=
  ix_none_of_key_noneK _ hw hx hk

omit [Fintype K] [Nonempty K] in
/-- **Filling commutes with `newKey`.** -/
theorem fill_newKey {w : WSt K} (hw : WInv w) (sid : SessionId) (pid : PartyId) (k kf : K) :
    fill (wNext w (.inr (.newKey sid pid k)) kf) = newKeyStep (fill w) (sid, pid) k kf :=
  fill_newKeyK _ hw sid pid k kf

omit [Fintype K] [Nonempty K] in
/-- **Filling commutes with `newKeyUnlinked`.** -/
theorem fill_newKeyFresh {w : WSt K} (hw : WInv w) (sid : SessionId) (pid : PartyId)
    (k kf : K) :
    fill (wNext w (.inr (.newKeyUnlinked sid pid k)) kf) =
      newKeyFreshStep (fill w) (sid, pid) k kf :=
  fill_newKeyFreshK _ hw sid pid k kf

omit [Fintype K] [Nonempty K] in
/-- Filling commutes with `addSession`. -/
theorem fill_addSession {w : WSt K} (hw : WInv w) (sid : SessionId) (pid peer : PartyId)
    (role : Role) (kf : K) :
    fill (wNext w (.inl (.newSession sid pid peer role)) kf) =
      addSession (fill w) (sid, pid) peer role :=
  fill_addSessionK _ hw sid pid peer role kf

omit [Fintype K] [Nonempty K] in
/-- The real views of the first hybrid world are the views of the real stack at the filled
state. -/
theorem chanOut_fill {w : WSt K} (hw : WInv w) (x : Inst) :
    chanOut (wView realV idealV 0 realV realV w x) w.st x =
      chanOut (fun _ k => realV k) (fill w) x :=
  chanOut_fillK _ realV _ hw x

/-- **The first hybrid world is the real stack over `F_AKE`**: filling the keys of the indices
is a step map on the invariant. -/
theorem world_zero_stepMap :
    Sys.StepMapOn (world realV idealV 0 (SPComp.sample K) realV realV) (FR realV) WInv fill :=
  world_zero_stepMapK _ _ realV _ fun _ _ _ => rfl

/-! ## One step of the hybrid argument -/

/-- The hybrid world `i`: the keys below `i` read ideally, the keys from `i` on read really. -/
noncomputable abbrev hyb (i : ℕ) : Sys (WSt K) (HEv ⊕ AEv K) (HOut V ⊕ AOut) :=
  world realV idealV i (SPComp.sample K) realV realV

/-- The world of the reduction of the step `i`: the first read of the key `i` returns the
challenge `v`, its later reads are ideal. -/
noncomputable abbrev chalWorld (i : ℕ) (v : V) : Sys (WSt K) (HEv ⊕ AEv K) (HOut V ⊕ AOut) :=
  world realV idealV i (SPComp.sample K) (fun _ => SPComp.pure v) (fun _ => idealV)

/-- **The reduction of the step `i`**: on the challenge view `v`, it runs the environment `Z`
from its heap against the world in which the first read of the key `i` returns `v`, and
applies the distinguisher of `Z`. -/
noncomputable def hopRed (i : ℕ) {ζ : Type} (Z : Env (Strat ζ (HEv ⊕ AEv K) (HOut V ⊕ AOut)) ζ) :
    V → SPComp Bool :=
  fixHeap Z.heap fun v => SPComp.bind (view (chalWorld realV idealV i v) Z.input) Z.dist

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- The views of the step `i + 1` from below. -/
theorem readOut_succ (i : ℕ) (w : WSt K) (j : ℕ) :
    readOut realV idealV i (fun _ => idealV) (fun _ => idealV) w j =
      readOut realV idealV (i + 1) realV realV w j :=
  readOut_succK _ realV _ i w j

/-- The challenge world at the ideal view is the hybrid world `i + 1`. -/
theorem chalWorld_ideal (i : ℕ) :
    world realV idealV i (SPComp.sample K) (fun _ => idealV) (fun _ => idealV) =
      hyb realV idealV (i + 1) :=
  chalWorld_idealK _ _ realV _ i

/-- **One step of the hybrid argument.** For views `realV k` and `idealV` that neither touch
the heap nor fail, the distance between the hybrid worlds `i` and `i + 1` at the environment
`Z` is at most the advantage of the reduction `hopRed i Z` between the real game (a uniform key
`k`, then `realV k`) and the ideal game `idealV`, plus the probability that the key `i` is read
twice in the world `i`. -/
theorem hyb_step (hR : ∀ k, SPComp.IsPure (realV k) ∧ SPComp.NoFail (realV k))
    (hI : SPComp.IsPure idealV ∧ SPComp.NoFail idealV) (i : ℕ) {ζ : Type}
    (Z : Env (Strat ζ (HEv ⊕ AEv K) (HOut V ⊕ AOut)) ζ) :
    Env.gap (view (hyb realV idealV i)) (view (hyb realV idealV (i + 1))) Z ≤
      AdvantageA (SPComp.bind (SPComp.sample K) realV) idealV (hopRed realV idealV i Z) +
        prBad (hyb realV idealV i) (reuse i) Z := by
  have hs := CatCrypt.Crypto.PAKE.CPaceSquare.pureNF_sample K
  set Y : K → V → Sys (WSt K) (HEv ⊕ AEv K) (HOut V ⊕ AOut) := fun k v =>
    world realV idealV i (SPComp.pure k) (fun _ => SPComp.pure v) realV
  -- the two deferrals, for any flag
  have hmix : ∀ bad : WSt K → Bool,
      SPComp.bind (SPComp.sample K) (fun k => SPComp.bind (realV k) fun v =>
        run (Y k v) bad Z.input) = run (hyb realV idealV i) bad Z.input := fun bad => by
    rw [← run_world_create realV idealV i hs.1 hs.2 realV realV bad Z.input]
    congr 1; funext k
    exact run_world_read realV idealV i (SPComp.pure k) (hR k).1 (hR k).2 realV realV
      (fun kf hkf => by rw [← isOutcome_pure hkf]) bad Z.input
  have hideal : SPComp.bind idealV (fun v => view (chalWorld realV idealV i v) Z.input) =
      view (hyb realV idealV (i + 1)) Z.input := by
    rw [← chalWorld_ideal realV idealV i]
    have h := run_world_read realV idealV i (SPComp.sample K) hI.1 hI.2 (fun _ => idealV)
      (fun _ => idealV) (fun _ _ => rfl) (fun _ => false) Z.input
    simp only [view, SPComp.map] at h ⊢
    rw [← h, SPComp.bind_assoc]
  -- the pair of the key and the view
  set c : SPComp (K × V) := SPComp.bind (SPComp.sample K) fun k =>
    SPComp.map (fun v => (k, v)) (realV k)
  have hc : ∀ {β : Type} (f : K → V → SPComp β),
      SPComp.bind c (fun p => f p.1 p.2) =
        SPComp.bind (SPComp.sample K) fun k => SPComp.bind (realV k) fun v => f k v := by
    intro β f
    simp only [c, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  have h1 : prTrue (SPComp.bind (view (hyb realV idealV i) Z.input) Z.dist) Z.heap =
      prTrue (SPComp.bind c fun p => SPComp.bind (view (Y p.1 p.2) Z.input) Z.dist) Z.heap := by
    rw [hc (fun k v => SPComp.bind (view (Y k v) Z.input) Z.dist)]
    simp only [view, ← hmix, SPComp.map, SPComp.bind_assoc]
  have h2 : prBad (hyb realV idealV i) (reuse i) Z =
      prTrue (SPComp.bind c fun p => SPComp.bind (run (Y p.1 p.2) (reuse i) Z.input)
        fun q => SPComp.pure q.2.2) Z.heap := by
    rw [hc (fun k v => SPComp.bind (run (Y k v) (reuse i) Z.input) fun q => SPComp.pure q.2.2)]
    simp only [prBad, ← hmix, SPComp.bind_assoc]
  have h3 : prTrue (SPComp.bind c fun p =>
        SPComp.bind (view (chalWorld realV idealV i p.2) Z.input) Z.dist) Z.heap =
      prTrue (SPComp.bind (SPComp.bind (SPComp.sample K) realV)
        fun v => SPComp.bind (view (chalWorld realV idealV i v) Z.input) Z.dist) Z.heap := by
    rw [hc (fun _ v => SPComp.bind (view (chalWorld realV idealV i v) Z.input) Z.dist),
      SPComp.bind_assoc]
  have hreal : SPComp.IsPure (SPComp.bind (SPComp.sample K) realV) :=
    SPComp.bind_isPure hs.1 fun k => (hR k).1
  have h4 := absDiff_prTrue_bind_eq_advantageA hreal hI.1
    (fun v => SPComp.bind (view (chalWorld realV idealV i v) Z.input) Z.dist) Z.heap
  have h5 : prTrue (SPComp.bind idealV fun v =>
        SPComp.bind (view (chalWorld realV idealV i v) Z.input) Z.dist) Z.heap =
      prTrue (SPComp.bind (view (hyb realV idealV (i + 1)) Z.input) Z.dist) Z.heap := by
    rw [← hideal, SPComp.bind_assoc]
  have hupto := absDiff_prTrue_bind_le_bind c
    (fun p => SPComp.bind (view (Y p.1 p.2) Z.input) Z.dist)
    (fun p => SPComp.bind (view (chalWorld realV idealV i p.2) Z.input) Z.dist)
    (fun p => SPComp.bind (run (Y p.1 p.2) (reuse i) Z.input) fun q => SPComp.pure q.2.2)
    Z.heap fun p h => world_upto_reuse realV idealV i p.1 (fun _ _ => rfl)
      (fun k => (hR k).2) hI.2 (fun _ => SPComp.pure_noFail _) (fun k => (hR k).2)
      (fun _ => hI.2) ζ ⟨Z.input, h, Z.dist⟩
  unfold Env.gap
  rw [h1, h2, ← h5]
  rw [h3] at hupto
  refine le_trans (absDiff_triangle _ (prTrue (SPComp.bind (SPComp.bind (SPComp.sample K) realV)
    fun v => SPComp.bind (view (chalWorld realV idealV i v) Z.input) Z.dist) Z.heap) _) ?_
  exact (add_le_add hupto (le_of_eq h4)).trans (le_of_eq (add_comm _ _))

/-! ## The secure channel over `F_AKE` -/

/-- The bound of the hybrid argument at an environment `Z` of the functionality: over the
keys `i` below the number of activations of `Z`, the advantage of the reduction `hopRed i Z`
between the real and the ideal secure-messaging games, plus the probability that the key `i`
is read twice. -/
noncomputable def scBound {ζ : Type} (Z : Env (Strat ζ (HEv ⊕ AEv K) (HOut V ⊕ AOut)) ζ) :
    ℝ≥0∞ :=
  ∑ i ∈ Finset.range Z.input.rounds,
    (AdvantageA (SPComp.bind (SPComp.sample K) realV) idealV (hopRed realV idealV i Z) +
      prBad (hyb realV idealV i) (reuse i) Z)

/-- **`F_AKE` followed by the ratchet realizes the ideal secure channel.** For views `realV k`
and `idealV` that neither touch the heap nor fail, `FR realV` realizes `F_SC realV idealV`
with the bound `scBound`: a hybrid argument over the keys that the run creates (one per
activation), each step bounded by `hyb_step`. -/
theorem FR_realizes_F_SC (hR : ∀ k, SPComp.IsPure (realV k) ∧ SPComp.NoFail (realV k))
    (hI : SPComp.IsPure idealV ∧ SPComp.NoFail idealV) :
    Realizes (FR realV) (F_SC realV idealV) (fun _ Z => scBound realV idealV Z) := by
  have h0 : Realizes (FR realV) (hyb realV idealV 0) (fun _ _ => 0) :=
    realizes_symm (world_zero_stepMap realV idealV).realizes
  have hH := Realizes.hybrid_rounds (hyb realV idealV) (F_SC realV idealV)
    (fun i _ Z => AdvantageA (SPComp.bind (SPComp.sample K) realV) idealV
      (hopRed realV idealV i Z) + prBad (hyb realV idealV i) (reuse i) Z)
    (fun _ _ => 0) (fun i _ Z => hyb_step realV idealV hR hI i Z) fun _ Z => by
      have h := world_end realV idealV Z.input.rounds (fun k => (hR k).2) hI.2 _ Z
      dsimp only at h
      rwa [world_end_prBad realV idealV _ Z le_rfl] at h
  intro ζ Z
  have := (h0.trans hH) ζ Z
  simpa [scBound] using this

end Steps

/-! ## The simulator -/

section Sim

/-- The view of the honest port of the secure channel: equal events, any two outputs. -/
def scHonView {V : Type} : PubView HEv (HOut V) where
  ev := Eq
  out _ _ := True

/-- The outer view of the Signal stack: the view of the honest port and equal adversary
outputs. -/
abbrev scOuterView {S W K V : Type} : PubView (OEv W) (HOut V ⊕ ROut S W K) :=
  scHonView.sum eqView

/-- The view of `F_SC`. -/
abbrev scSubView {K V : Type} : PubView (FEv K) (HOut V ⊕ AOut) := scHonView.sum eqView

section Generic

variable {K V AE R σ : Type}

/-- **The key layer** over a key exchange with adversary outputs `R`: on the output
`key (some k)` of the honest port, the view `sm k` keyed by `k`; every other output passes. -/
noncomputable def keyLayer (sm : K → SPComp V) : Sys Unit (HOut K ⊕ R) (HOut V ⊕ R) where
  init := ()
  step _ o := match o with
    | .inl .ok => SPComp.pure ((), .inl .ok)
    | .inl (.key none) => SPComp.pure ((), .inl (.key none))
    | .inl (.key (some k)) => SPComp.map (fun v => ((), .inl (.key (some v)))) (sm k)
    | .inr r => SPComp.pure ((), .inr r)

/-- The key layer of views that never fail never fails. -/
theorem keyLayer_noFail {sm : K → SPComp V} (hsm : ∀ k, SPComp.NoFail (sm k)) (u : Unit)
    (o : HOut K ⊕ R) : SPComp.NoFail ((keyLayer sm).step u o) := by
  rcases o with (_ | (_ | k)) | r
  · exact SPComp.pure_noFail _
  · exact SPComp.pure_noFail _
  · simp only [keyLayer, SPComp.map]
    exact Assumptions.SPComp.bind_noFail (hsm k) fun _ => SPComp.pure_noFail _
  · exact SPComp.pure_noFail _

/-- The forwarding data of a simulator over `F_AKE` with states `σ` and adversary outputs `R`:
the state after an answer of `F_AKE`, the adversary output stored in a state (`none` forwards
the answer of the honest port), and the output on an adversary answer in the forwarding
phase. -/
structure FwdData (σ R : Type) where
  /-- The state after an answer of the functionality. -/
  reset : σ → σ
  /-- The stored adversary output of a state; `none` forwards the answer on the honest port. -/
  phase : σ → Option R
  /-- The output on an adversary answer in the forwarding phase. -/
  ack : R

/-- The answer of a forwarding simulator to an answer of the functionality: at the phase `none`,
the answer on the honest port, and `ack` for an answer on the adversary port; at `some r`, the
stored output `r`. -/
def fwdOut (ack : R) : Option R → HOut V ⊕ AOut → HOut V ⊕ R
  | none, .inl o => .inl o
  | none, .inr _ => .inr ack
  | some r, _ => .inr r

/-- A decision of a simulator over `F_AKE` as a decision over `F_SC`: a call passes, an
adversary output passes, and an honest output is an acknowledgement. -/
def decK : FEv K ⊕ (HOut K ⊕ R) → FEv K ⊕ (HOut V ⊕ R)
  | .inl ev => .inl ev
  | .inr (.inl _) => .inr (.inl .ok)
  | .inr (.inr r) => .inr (.inr r)

/-- **A multi-call simulator over `F_SC`** wrapping a multi-call simulator `π` over `F_AKE`
with the forwarding data `F`: its `start` step is that of `π` with the decision read over
`F_SC` (`decK`), and an answer of `F_SC` is answered by `fwdOut` at the phase of the state. -/
noncomputable def simSCOver (π : MultiHybrid σ (HEv ⊕ AE) (HOut K ⊕ R) (FEv K) (FOut K))
    (F : FwdData σ R) :
    MultiHybrid σ (HEv ⊕ AE) (HOut V ⊕ R) (FEv K) (HOut V ⊕ AOut) where
  init := π.init
  fuel := 0
  start s e := SPComp.map (fun q => (q.1, decK q.2)) (π.start s e)
  resume s o := SPComp.pure (F.reset s, .inr (fwdOut F.ack (F.phase s) o))
  finish s o := SPComp.pure (F.reset s, fwdOut F.ack (F.phase s) o)
  start_noFail s e := map_noFail _ (π.start_noFail s e)
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

/-- **A forwarding simulator** over `F_AKE` for the data `F`: one call per activation, every
answer of `F_AKE` answered by `fwdOut` at the phase of the state, and no honest output from the
`start` step. -/
structure IsFwd (π : MultiHybrid σ (HEv ⊕ AE) (HOut K ⊕ R) (FEv K) (FOut K))
    (F : FwdData σ R) : Prop where
  /-- One call per activation. -/
  fuel_eq : π.fuel = 0
  /-- The answer to `F_AKE` is `fwdOut` at the phase of the state. -/
  finish_eq : ∀ s o, π.finish s o = SPComp.pure (F.reset s, fwdOut F.ack (F.phase s) o)
  /-- The `start` step outputs nothing on the honest port. -/
  start_noHon : ∀ s e q, IsOutcome (π.start s e) q → ∀ h, q.2 ≠ .inr (.inl h)

/-- Every decision over `F_SC` is related to itself. -/
theorem decSC_rel (d : FEv K ⊕ (HOut V ⊕ R)) :
    PubView.StepRel ((scHonView (V := V)).sum (eqView (E := AE) (O := R)))
      (scSubView (K := K) (V := V)) d d := by
  rcases d with (h | a) | (o | o)
  · exact Sum.LiftRel.inl rfl
  · exact Sum.LiftRel.inr rfl
  · exact Sum.LiftRel.inl trivial
  · exact Sum.LiftRel.inr rfl

/-- The answers of a forwarding simulator to related answers of `F_SC` are related. -/
theorem fwdOut_rel (ack : R) (ph : Option R) {o o' : HOut V ⊕ AOut}
    (h : (scSubView (K := K)).out o o') :
    ((scHonView (V := V)).sum (eqView (E := AE) (O := R))).out (fwdOut ack ph o)
      (fwdOut ack ph o') := by
  cases ph with
  | none =>
    cases h with
    | inl _ => exact Sum.LiftRel.inl trivial
    | inr _ => exact Sum.LiftRel.inr rfl
  | some r => exact Sum.LiftRel.inr rfl

/-- **Opacity of the wrapper**: its state and its decisions depend on its events and not on the
answers of `F_SC` on the honest port. -/
theorem simSCOver_opaque (π : MultiHybrid σ (HEv ⊕ AE) (HOut K ⊕ R) (FEv K) (FOut K))
    (F : FwdData σ R) :
    (simSCOver (V := V) π F).Opaque ((scHonView (V := V)).sum (eqView (E := AE) (O := R)))
      scSubView := by
  refine ⟨Eq, rfl, ?_, ?_, ?_⟩
  · rintro s _ e e' rfl he
    have he' : e = e' := by
      cases he with
      | inl h => exact congrArg Sum.inl h
      | inr h => exact congrArg Sum.inr h
    subst he'
    exact rHoare_conseq (fun _ _ h => h)
      (fun _ _ _ _ hp => by obtain ⟨rfl, rfl⟩ := hp; exact ⟨rfl, rfl, decSC_rel _⟩)
      (rHoare_refl _)
  · rintro s _ o o' rfl ho
    exact rHoare_ret fun _ _ hh => ⟨hh, rfl, fwdOut_rel _ _ ho⟩
  · rintro s _ o o' rfl ho
    exact rHoare_ret fun _ _ hh => ⟨hh, rfl, fwdOut_rel _ _ ho⟩

/-- **The simulator over `F_SC` of a forwarding simulator `π` over `F_AKE`**, bundled: the
wrapper `simSCOver π F` with its opacity. -/
noncomputable def chanSim (π : MultiHybrid σ (HEv ⊕ AE) (HOut K ⊕ R) (FEv K) (FOut K))
    (F : FwdData σ R) :
    Simulator (HEv ⊕ AE) (HOut V ⊕ R) (FEv K) (HOut V ⊕ AOut)
      ((scHonView (V := V)).sum (eqView (E := AE) (O := R))) scSubView :=
  Simulator.ofMultiHybrid (simSCOver π F) (simSCOver_opaque π F)

/-- The key layer on an answer of a forwarding simulator to an adversary answer of
`F_AKE`. -/
theorem keyLayer_fwdOut_inr (realV : K → SPComp V) (ack : R) (ph : Option R) (a : AOut) :
    (keyLayer realV).step () (fwdOut ack ph (.inr a)) =
      SPComp.pure ((), fwdOut ack ph (.inr a)) := by
  cases ph <;> rfl

/-- The key layer on the key of a session is the channel output of the real stack. -/
theorem keyLayer_key (realV : K → SPComp V) (t : St K) (x : Inst) :
    (keyLayer (R := R) realV).step () (.inl (.key (keyOf t x))) =
      SPComp.map (fun o => ((), .inl o)) (chanOut (fun _ k => realV k) t x) := by
  unfold chanOut keyOf
  rcases hx : t.recs x with _ | r
  · simp [keyLayer, SPComp.map]
  · rcases hk : r.key with _ | k
    · simp [keyLayer, hk, SPComp.map]
    · simp [keyLayer, hk, SPComp.map, SPComp.bind_assoc]

/-- The channel output of views that neither touch the heap nor fail neither touches the heap
nor fails. -/
theorem chanOut_pureNF {f : Rec K → K → SPComp V}
    (hf : ∀ r k, SPComp.IsPure (f r k) ∧ SPComp.NoFail (f r k)) (t : St K) (x : Inst) :
    SPComp.IsPure (chanOut f t x) ∧ SPComp.NoFail (chanOut f t x) := by
  unfold chanOut
  split
  · split
    · exact ((CatCrypt.Crypto.PAKE.CPaceSquare.PureNF.map _ (hf _ _)))
    · exact CatCrypt.Crypto.PAKE.CPaceSquare.pureNF_pure _
  · exact CatCrypt.Crypto.PAKE.CPaceSquare.pureNF_pure _

/-- **A forwarding simulator over `F_AKEK fresh` followed by the key layer is its wrapper over
the real stack `FRK fresh`** (composition plumbing): the cascade of `π` running with
`F_AKEK fresh` and the key layer and `simSCOver π F` running with `FRK fresh realV` have the
same steps, up to the unit state of the layer. -/
theorem stack_ideal_stepMap_ofK (fresh : K → SPComp K)
    (π : MultiHybrid σ (HEv ⊕ AE) (HOut K ⊕ R) (FEv K) (FOut K)) (F : FwdData σ R)
    (hF : IsFwd π F) (realV : K → SPComp V)
    (hR : ∀ k, SPComp.IsPure (realV k) ∧ SPComp.NoFail (realV k)) :
    Sys.StepMapOn ((simSCOver (V := V) π F).withSub (FRK fresh realV))
      ((π.withSub (F_AKEK fresh true)).seq (keyLayer realV))
      (fun _ => True) (fun p => (p, ())) where
  init_inv := trivial
  init_map := rfl
  pres _ _ _ _ _ := trivial
  step p e _ := by
    rcases p with ⟨s, t⟩
    rw [Sys.seq_step]
    simp only [MultiHybrid.withSub, simSCOver, hF.fuel_eq, SPComp.map, SPComp.bind_assoc,
      SPComp.pure_bind]
    refine bind_congr_isOutcome fun r hr => ?_
    have hn := hF.start_noHon s e r hr
    rcases r with ⟨s', (ev | (h | ro))⟩
    · simp only [MultiHybrid.drive, decK, hF.finish_eq, SPComp.bind_assoc, SPComp.pure_bind]
      rcases ev with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | ev
      · cases F.phase s' <;> simp [FRK, chanHon, F_AKEK, F_AKEImpK, honSys, honStep, keyLayer,
          fwdOut, SPComp.map, SPComp.pure_bind]
      · have hc := chanOut_pureNF (fun _ k => hR k) t (sid, pid)
        cases F.phase s' with
        | none =>
          simp only [FRK, F_AKEK, F_AKEImpK, Sys.ofPorts_step_inl, chanHon, honSys, honStep,
            SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, fwdOut]
          have hk := keyLayer_key (R := R) realV t (sid, pid)
          simp only [SPComp.map] at hk
          rw [hk]
          simp only [SPComp.bind_assoc, SPComp.pure_bind]
        | some r =>
          simp only [FRK, F_AKEK, F_AKEImpK, Sys.ofPorts_step_inl, chanHon, honSys, honStep,
            SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, fwdOut, keyLayer]
          exact bind_const_of_isPure hc.1 hc.2 _
      · simp only [FRK, F_AKEK, F_AKEImpK, advSysK, Bool.not_true, Sys.ofPorts_step_inr,
          SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
        congr 1; funext q
        rw [keyLayer_fwdOut_inr]
        simp only [SPComp.pure_bind]
    · exact (hn h rfl).elim
    · simp [MultiHybrid.drive, decK, keyLayer, SPComp.map, SPComp.pure_bind]

/-- **A forwarding simulator over `F_AKE` followed by the key layer is its wrapper over the real
stack `FR`** (composition plumbing): the cascade of `π` running with `F_AKE` and the key layer
and `simSCOver π F` running with `FR realV` have the same steps, up to the unit state of the
layer. -/
theorem stack_ideal_stepMap_of [Fintype K] [Nonempty K]
    (π : MultiHybrid σ (HEv ⊕ AE) (HOut K ⊕ R) (FEv K) (FOut K)) (F : FwdData σ R)
    (hF : IsFwd π F) (realV : K → SPComp V)
    (hR : ∀ k, SPComp.IsPure (realV k) ∧ SPComp.NoFail (realV k)) :
    Sys.StepMapOn ((simSCOver (V := V) π F).withSub (FR realV))
      ((π.withSub (F_AKE (SPComp.sample K) true)).seq (keyLayer realV))
      (fun _ => True) (fun p => (p, ())) :=
  stack_ideal_stepMap_ofK _ π F hF realV hR

end Generic

variable {S W K V : Type}

/-- The stored adversary output of a phase of the X3DH simulator: none in the phase `fwd`. -/
def phaseOut : Phase S W K → Option (ROut S W K)
  | .fwd => none
  | .out r => some r

/-- **The forwarding data of the X3DH simulator**: the phase `fwd` after an answer of `F_AKE`,
the output stored in the phase, and the acknowledgement `ack`. -/
def x3dhFwd : FwdData (SimSt S W K) (ROut S W K) where
  reset s := (s.1, s.2.1, .fwd)
  phase s := phaseOut s.2.2
  ack := .ack

variable [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  (G : DHGroup S W)

/-- **The simulator of the Signal stack**: the X3DH simulator `simProt G` over `F_SC`. It keeps
the copy of the real state of `simProt G`, draws the long-term and session secrets itself,
forwards the honest events to `F_SC`, answers `poll`, `pub`, `ephPub` and `kdf` on its copy,
corrupts in `F_SC` under the static rule of X3DH, and delivers keys as `simProt G` does: the
key-derivation value to an exposed session, `newKey` or `newKeyUnlinked` with a placeholder
key otherwise. The honest outputs of `F_SC` (the views of the channel) pass unchanged. -/
noncomputable def simSC :
    MultiHybrid (SimSt S W K) (OEv W) (HOut V ⊕ ROut S W K) (FEv K) (HOut V ⊕ AOut) :=
  simSCOver (simProt G) x3dhFwd

/-- **Opacity of the simulator**: its state and its decisions depend on its events and not on
the answers of `F_SC` on the honest port. -/
theorem simSC_opaque :
    (simSC (V := V) G).Opaque (scOuterView (K := K)) scSubView :=
  simSCOver_opaque _ _

/-- **The simulator of the Signal stack** as a bundled opaque simulator over `F_SC`. -/
noncomputable def scSim : Simulator (OEv W) (HOut V ⊕ ROut S W K) (FEv K) (HOut V ⊕ AOut)
    scOuterView scSubView :=
  chanSim (simProt G) x3dhFwd

/-- A decision that is not an honest output. -/
def NoHon (d : Dec S W K) : Prop := ∀ h, d ≠ .inr (.inl h)

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- A point mass at a decision that is not an honest output. -/
theorem noHon_pure {a : SimSt S W K} {d : Dec S W K} (hd : NoHon d)
    {q : SimSt S W K × Dec S W K} (hq : IsOutcome (SPComp.pure (a, d)) q) : NoHon q.2 := by
  rw [← isOutcome_pure hq]; exact hd

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The outcomes of a map whose values are not honest outputs. -/
theorem noHon_map {α : Type} {c : SPComp α} {f : α → SimSt S W K × Dec S W K}
    (hf : ∀ a, NoHon (f a).2) {q : SimSt S W K × Dec S W K}
    (hq : IsOutcome (SPComp.map f c) q) : NoHon q.2 := by
  obtain ⟨a, _, rfl⟩ := isOutcome_map_iff.mp hq; exact hf a

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The outcomes of a bind whose continuations give no honest output. -/
theorem noHon_bind {α : Type} {c : SPComp α} {f : α → SPComp (SimSt S W K × Dec S W K)}
    (hf : ∀ a q, IsOutcome (f a) q → NoHon q.2) {q : SimSt S W K × Dec S W K}
    (hq : IsOutcome (SPComp.bind c f) q) : NoHon q.2 := by
  obtain ⟨a, _, ha⟩ := isOutcome_bind hq; exact hf a q ha

omit [Field S] [Fintype S] in
/-- The delivery of a key calls `F_SC`. -/
theorem deliver_noHon (rs : RSt S W K) (inp : Inst → Option (Inp W)) (x : Inst) (r : Rec K)
    (ip : Inp W) {q : SimSt S W K × Dec S W K} (hq : IsOutcome (deliver rs inp x r ip) q) :
    NoHon q.2 := by
  unfold deliver at hq
  split at hq
  · exact noHon_map (fun _ _ h => by simp at h) hq
  · exact noHon_pure (fun _ h => by simp at h) hq

/-- **The X3DH simulator outputs nothing on the honest port by itself**: every honest output of
the simulated world is an answer of the functionality. -/
theorem simStart_noHon (s : SimSt S W K) (e : OEv W) {q : SimSt S W K × Dec S W K}
    (hq : IsOutcome (simStart G s e) q) : NoHon q.2 := by
  have hp : ∀ (a : SimSt S W K) (r : ROut S W K) {q : SimSt S W K × Dec S W K},
      IsOutcome (SPComp.pure (a, (.inr (.inr r) : Dec S W K))) q → NoHon q.2 :=
    fun _ _ _ hq => noHon_pure (fun _ h => by simp at h) hq
  have hl : ∀ (a : SimSt S W K) (ev : FEv K) {q : SimSt S W K × Dec S W K},
      IsOutcome (SPComp.pure (a, (.inl ev : Dec S W K))) q → NoHon q.2 :=
    fun _ _ _ hq => noHon_pure (fun _ h => by simp at h) hq
  have hd : ∀ {α β : Type} (c : SPComp α) (c' : α → SPComp β)
      (f : α → β → SPComp (SimSt S W K × Dec S W K)),
      (∀ a b q, IsOutcome (f a b) q → NoHon q.2) → ∀ q,
      IsOutcome (SPComp.bind c fun a => SPComp.bind (c' a) (f a)) q → NoHon q.2 :=
    fun c c' f hf q hq => noHon_bind (fun a q' hq' => noHon_bind (hf a) hq') hq
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) |
    (_ | _ | pid | ⟨sid, pid⟩ | pid | ⟨sid, pid⟩ | ⟨sid, pid, e⟩ | x)
  · simp only [simStart] at hq
    split at hq
    · exact noHon_map (fun _ _ h => by simp at h) hq
    · exact hl _ _ hq
  · exact hl _ _ hq
  · exact hp _ _ hq
  · exact hp _ _ hq
  · exact noHon_map (fun _ _ h => by simp at h) hq
  · exact hp _ _ hq
  · simp only [simStart, simCorrupt] at hq
    split at hq
    · exact hp _ _ hq
    · exact noHon_map (fun _ _ h => by simp at h) hq
  · simp only [simStart, simComplete] at hq
    repeat' split at hq
    all_goals first
      | exact hp _ _ hq
      | exact hd _ _ _ (fun _ _ _ h => deliver_noHon _ _ _ _ _ h) q hq
  · simp only [simStart, simSend] at hq
    repeat' split at hq
    all_goals first
      | exact hp _ _ hq
      | exact hd _ _ _ (fun _ _ _ h => deliver_noHon _ _ _ _ _ h) q hq
  · exact noHon_map (fun _ _ h => by simp at h) hq

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The ratchet layer of the X3DH stack is the key layer at the adversary outputs of X3DH. -/
theorem smLayer_eq_keyLayer (realV : K → SPComp V) :
    smLayer (S := S) (W := W) realV = keyLayer realV := by
  unfold smLayer keyLayer
  congr 1
  funext u o
  rcases o with (_ | (_ | k)) | r <;> rfl

/-- **The X3DH simulator is a forwarding simulator** for the data `x3dhFwd`. -/
theorem simProt_isFwd : IsFwd (simProt (K := K) G) x3dhFwd where
  fuel_eq := rfl
  finish_eq s o := by
    rcases s with ⟨a, b, ph⟩
    cases ph <;> rcases o with o | o <;> rfl
  start_noHon s e _ hq := simStart_noHon G s e hq

/-- **The stack over `F_AKE` behind the X3DH simulator is the simulator `simSC` over the real
stack `FR`** (composition plumbing): the cascade of `x3dhIdeal G` and the ratchet layer and
`simSC G` running with `FR realV` have the same steps, up to the unit state of the layer. -/
theorem stack_ideal_stepMap (realV : K → SPComp V)
    (hR : ∀ k, SPComp.IsPure (realV k) ∧ SPComp.NoFail (realV k)) :
    Sys.StepMapOn ((simSC (V := V) G).withSub (FR realV)) ((x3dhIdeal G).seq (smLayer realV))
      (fun _ => True) (fun p => (p, ())) := by
  rw [smLayer_eq_keyLayer]
  exact stack_ideal_stepMap_of (simProt G) x3dhFwd (simProt_isFwd G) realV hR

end Sim

/-! ## The Signal stack realizes the ideal secure channel -/

section Stack

variable {S W K : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K]
  [Inhabited K] (G : DHGroup S W)

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- `FRK fresh` is idle at the idle event of the adversary. -/
theorem FRK_idleAt {V : Type} (fresh : K → SPComp K) (realV : K → SPComp V) :
    MultiHybrid.IdleAt (FRK fresh realV) (.inr .idle) (.inr .ack) := fun t => by
  simp [FRK, advSysK, advSysImp, SPComp.map]

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- `F_SCK` is idle at the idle event of the adversary. -/
theorem F_SCK_idleAt {V Ks D : Type} [Inhabited Ks] (sp : KeySplit K Ks D)
    (realV : K → SPComp V) (idealV : D → SPComp V) :
    MultiHybrid.IdleAt (F_SCK sp realV idealV) (.inr .idle) (.inr .ack) := fun t => by
  simp [F_SCK, advSysK, advSysImp, SPComp.map]

omit [Inhabited K] in
/-- `FR` is idle at the idle event of the adversary. -/
theorem FR_idleAt {V : Type} (realV : K → SPComp V) :
    MultiHybrid.IdleAt (FR realV) (.inr .idle) (.inr .ack) :=
  FRK_idleAt _ realV

omit [Fintype K] [Nonempty K] in
/-- `F_SC` is idle at the idle event of the adversary. -/
theorem F_SC_idleAt {V : Type} (realV : K → SPComp V) (idealV : SPComp V) :
    MultiHybrid.IdleAt (F_SC realV idealV) (.inr .idle) (.inr .ack) :=
  F_SCK_idleAt _ realV _

omit [Field S] [Fintype S] [SampleableType W] in
/-- **The wrapper over `FR` realizes the wrapper over `F_SC`**: for views that neither touch the
heap nor fail, `simSCOver π F` over `FR realV` realizes `simSCOver π F` over
`F_SC realV idealV` with `scBound` at the environment reduced through the wrapper. -/
theorem simSCOver_realizes {σ AE R V : Type}
    (π : MultiHybrid σ (HEv ⊕ AE) (HOut K ⊕ R) (FEv K) (FOut K)) (F : FwdData σ R)
    (realV : K → SPComp V) (idealV : SPComp V)
    (hR : ∀ k, SPComp.IsPure (realV k) ∧ SPComp.NoFail (realV k))
    (hI : SPComp.IsPure idealV ∧ SPComp.NoFail idealV) :
    Realizes ((simSCOver (V := V) π F).withSub (FR realV))
      ((simSCOver π F).withSub (F_SC realV idealV))
      (fun _ Z => scBound realV idealV ((simSCOver π F).reduceEnv (.inr .idle) Z)) := by
  intro ζ Z
  have h := MultiHybrid.adv_withSub (simSCOver (V := V) π F) (.inr .idle) (.inr .ack)
    (.inr .ack) (FR realV) (F_SC realV idealV) (FR_idleAt realV) (F_SC_idleAt realV idealV) Z
  unfold adv at h
  change Env.gap _ _ Z ≤ _
  rw [h]
  exact FR_realizes_F_SC realV idealV hR hI _ _

/-- **The simulator over `F_AKE` with the ratchet realizes the simulator over `F_SC`**: for
views that neither touch the heap nor fail, `simSC G` over `FR realV` realizes `simSC G` over
`F_SC realV idealV` with `scBound` at the environment reduced through the simulator. -/
theorem simSC_realizes {V : Type} (realV : K → SPComp V) (idealV : SPComp V)
    (hR : ∀ k, SPComp.IsPure (realV k) ∧ SPComp.NoFail (realV k))
    (hI : SPComp.IsPure idealV ∧ SPComp.NoFail idealV) :
    Realizes ((simSC (V := V) G).withSub (FR realV)) ((simSC G).withSub (F_SC realV idealV))
      (fun _ Z => scBound realV idealV ((simSC G).reduceEnv (.inr .idle) Z)) :=
  simSCOver_realizes _ _ realV idealV hR hI

/-- **KE-then-channel composition, generic in the key exchange** (genuine UC). Let the key
exchange `X` realize `F_AKE` with uniform keys and unlinked delivery behind the opaque
forwarding simulator `π` with the bound `ε`, and let the views `realV k` and `idealV` neither
touch the heap nor fail.

*Ideal functionality.* `F_SC realV idealV`.

*Real world.* `X` followed by the key layer `keyLayer realV`, which keys the view `realV` with
the session key of every `getKey` answer of `X`.

*Simulator.* `chanSim π F`: `π` with its decisions read over `F_SC`; it forwards the honest
answers of `F_SC` at the phases where `π` forwards those of `F_AKE`.

*Bound.* For every environment `Z`, the bound `ε` at the environment reduced through the key
layer, plus `scBound realV idealV` at the environment reduced through the simulator. -/
theorem stack_realizes_FSC_of {τ σ AE R V : Type} (X : Sys τ (HEv ⊕ AE) (HOut K ⊕ R))
    (π : MultiHybrid σ (HEv ⊕ AE) (HOut K ⊕ R) (FEv K) (FOut K))
    (hπ : π.Opaque ((keHonView (K := K)).sum (eqView (E := AE) (O := R))) subView)
    (F : FwdData σ R) (hF : IsFwd π F)
    {ε : (ζ : Type) → Env (Strat ζ (HEv ⊕ AE) (HOut K ⊕ R)) ζ → ℝ≥0∞}
    (hX : RealizesSim X (F_AKE (SPComp.sample K) true) (Simulator.ofMultiHybrid π hπ) ε)
    (realV : K → SPComp V) (idealV : SPComp V)
    (hR : ∀ k, SPComp.IsPure (realV k) ∧ SPComp.NoFail (realV k))
    (hI : SPComp.IsPure idealV ∧ SPComp.NoFail idealV) :
    RealizesSim (X.seq (keyLayer realV)) (F_SC realV idealV) (chanSim π F)
      (fun ζ Z => ε (ζ × Unit)
          ((Hybrid.seqCtxR (E := HEv ⊕ AE) (keyLayer realV)
            (keyLayer_noFail fun k => (hR k).2)).reduceEnv Z) +
        scBound realV idealV ((simSCOver π F).reduceEnv (.inr .idle) Z)) := by
  have hA := realizes_seq_left (keyLayer realV) (keyLayer_noFail fun k => (hR k).2) hX
  have hB := realizes_symm (stack_ideal_stepMap_of π F hF realV hR).realizes
  have hC := simSCOver_realizes π F realV idealV hR hI
  intro ζ Z
  have h := ((hA.trans hB).trans hC) ζ Z
  simp only [add_zero] at h
  exact h

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] in
/-- **The wrapper over `FRK sp.fresh` realizes the wrapper over `F_SCK`**: for views that
neither touch the heap nor fail, `simSCOver π F` over `FRK sp.fresh realV` realizes
`simSCOver π F` over `F_SCK sp realV idealV` with `scBoundK` at the environment reduced through
the wrapper. -/
theorem simSCOver_realizesK {σ AE R V Ks D : Type} [Fintype Ks] [Nonempty Ks] [Inhabited Ks]
    (π : MultiHybrid σ (HEv ⊕ AE) (HOut K ⊕ R) (FEv K) (FOut K)) (F : FwdData σ R)
    (sp : KeySplit K Ks D) (realV : K → SPComp V) (idealV : D → SPComp V)
    (hR : ∀ k, SPComp.IsPure (realV k) ∧ SPComp.NoFail (realV k))
    (hI : ∀ d, SPComp.IsPure (idealV d) ∧ SPComp.NoFail (idealV d)) :
    Realizes ((simSCOver (V := V) π F).withSub (FRK sp.fresh realV))
      ((simSCOver π F).withSub (F_SCK sp realV idealV))
      (fun _ Z => scBoundK sp realV idealV ((simSCOver π F).reduceEnv (.inr .idle) Z)) := by
  intro ζ Z
  have h := MultiHybrid.adv_withSub (simSCOver (V := V) π F) (.inr .idle) (.inr .ack)
    (.inr .ack) (FRK sp.fresh realV) (F_SCK sp realV idealV) (FRK_idleAt _ realV)
    (F_SCK_idleAt sp realV idealV) Z
  unfold adv at h
  change Env.gap _ _ Z ≤ _
  rw [h]
  exact FRK_realizes_F_SCK sp realV idealV hR hI _ _

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] in
/-- **KE-then-channel composition with a public datum** (genuine UC). Let the key exchange `X`
followed by the key layer realize, with the bound `ε`, the opaque forwarding simulator `π` over
`F_AKEK sp.fresh` with unlinked delivery followed by the key layer, and let the views `realV k`
and `idealV d` neither touch the heap nor fail.

*Ideal functionality.* `F_SCK sp realV idealV`: the secure channel whose completed sessions show
the ideal view `idealV d` at the datum `d` of the session.

*Real world.* `X` followed by the key layer `keyLayer realV`, which keys the view `realV` with
the session key of every `getKey` answer of `X`.

*Simulator.* `chanSim π F`: `π` with its decisions read over `F_SCK`; it forwards the honest
answers of `F_SCK` at the phases where `π` forwards those of `F_AKEK sp.fresh`.

*Bound.* For every environment `Z`, `ε Z`, plus `scBoundK sp realV idealV` at the environment
reduced through the simulator: per key, the chosen-datum advantage of the two-stage reduction
`hopRedK` between `sp.real realV` and `idealV`, and the probability that the key is read twice.

The hypothesis is the realization through the key layer, which a key-exchange square with a
datum read only through the layer provides; a realization of `F_AKEK sp.fresh` at every
environment gives it by `realizes_seq_left`. -/
theorem stack_realizes_FSCK_of {τ σ AE R V Ks D : Type} [Fintype Ks] [Nonempty Ks]
    [Inhabited Ks] (X : Sys τ (HEv ⊕ AE) (HOut K ⊕ R))
    (π : MultiHybrid σ (HEv ⊕ AE) (HOut K ⊕ R) (FEv K) (FOut K))
    (hπ : π.Opaque ((keHonView (K := K)).sum (eqView (E := AE) (O := R))) subView)
    (F : FwdData σ R) (hF : IsFwd π F) (sp : KeySplit K Ks D) (realV : K → SPComp V)
    (idealV : D → SPComp V)
    (hR : ∀ k, SPComp.IsPure (realV k) ∧ SPComp.NoFail (realV k))
    (hI : ∀ d, SPComp.IsPure (idealV d) ∧ SPComp.NoFail (idealV d))
    {ε : (ζ : Type) → Env (Strat ζ (HEv ⊕ AE) (HOut V ⊕ R)) ζ → ℝ≥0∞}
    (hXL : Realizes (X.seq (keyLayer realV))
      (((Simulator.ofMultiHybrid π hπ).withSub (F_AKEK sp.fresh true)).seq (keyLayer realV)) ε) :
    RealizesSim (X.seq (keyLayer realV)) (F_SCK sp realV idealV) (chanSim π F)
      (fun ζ Z => ε ζ Z +
        scBoundK sp realV idealV ((simSCOver π F).reduceEnv (.inr .idle) Z)) := by
  have hB := realizes_symm (stack_ideal_stepMap_ofK sp.fresh π F hF realV hR).realizes
  have hC := simSCOver_realizesK π F sp realV idealV hR hI
  intro ζ Z
  have h := ((hXL.trans hB).trans hC) ζ Z
  simp only [add_zero] at h
  exact h

variable {Sc Msg Key Sa M Ct : Type} [SampleableType M] [SampleableType Ct] [Fintype Key]
  [Nonempty Key] [Fintype Sa] [Nonempty Sa]

omit [SampleableType M] [Fintype Key] [Nonempty Key] [Fintype Sa] [Nonempty Sa] in
/-- The ideal secure-messaging game of a CKA of `CKAPureNF` neither touches the heap nor
fails. -/
theorem sm_ideal_pureNF {C : CKADef Sc Msg Key} (hC : CKAPureNF C)
    (msgs : List (List (M × M))) :
    SPComp.IsPure (sm_ideal (Ct := Ct) C msgs) ∧ SPComp.NoFail (sm_ideal (Ct := Ct) C msgs) := by
  unfold sm_ideal ckaPub
  exact (hC.1.bind fun _ => (ckaRun_pureNF hC _ _ _).bind fun _ =>
    CatCrypt.Crypto.PAKE.CPaceSquare.pureNF_pure _).bind fun _ =>
      (CatCrypt.Crypto.PAKE.CPaceSquare.pureNF_sample _).bind fun _ =>
        CatCrypt.Crypto.PAKE.CPaceSquare.pureNF_pure _

/-- The bound of the Signal stack at an environment `Z` of the stack: the gap Diffie–Hellman
bound of the X3DH square at the environment reduced through the ratchet layer, and, at the
environment `Z'` reduced through the simulator, over the keys `i` below the number of
activations of `Z'`, the secure-messaging advantage of the reduction `hopRed i Z'` and the
probability that the key `i` is read twice. -/
noncomputable def signalBound (P : Finset PartyId) (C : CKADef Sc Msg Key)
    (R : PRGDef (K × Key) (K × Sa)) (Gp : PRGDef Sa (M × Sa)) (D : AEADDef M Ct)
    (msgs : List (List (M × M))) (hC : CKAPureNF C) (ζ : Type)
    (Z : Env (Strat ζ (OEv W) (HOut (SMView Msg Ct) ⊕ ROut S W K)) ζ) : ℝ≥0∞ :=
  gdhBound G P ((OProt.oracle (Q := OEv W) (A := OOut S W K)).reduction
      ((Hybrid.seqCtxR (E := OEv W) (smLayer (smRealAt C R Gp D msgs))
        (smLayer_noFail fun k => (smRealAt_pureNF hC R Gp D msgs k).2)).reduceEnv Z)) +
    ∑ i ∈ Finset.range ((simSC (V := SMView Msg Ct) G).reduceEnv (.inr .idle) Z).input.rounds,
      (SM_Advantage C R Gp D msgs (hopRed (smRealAt C R Gp D msgs) (sm_ideal C msgs) i
          ((simSC G).reduceEnv (.inr .idle) Z)) +
        prBad (hyb (smRealAt C R Gp D msgs) (sm_ideal C msgs) i) (reuse i)
          ((simSC G).reduceEnv (.inr .idle) Z))

omit [Fintype Key] [Nonempty Key] [Fintype Sa] [Nonempty Sa] in
/-- **The Signal stack realizes the ideal secure channel** (genuine UC).

*Ideal functionality.* `F_SC (smRealAt C R Gp D msgs) (sm_ideal C msgs)`: the multi-session
secure channel built from the authenticated key exchange `F_AKE` with unlinked delivery. Its
adversary port is the adversary port of `F_AKE` (notices, adaptive corruption, `newKey`,
`newKeyUnlinked`), except that a session that completes without exposure stores no key. Its
honest port opens sessions and, on `getKey`, outputs the secure-messaging view of the session:
for a completed session the ideal view `sm_ideal C msgs` (the public CKA transcript and uniform
ciphertexts), for a session exposed by corruption the real view `smRealAt C R Gp D msgs k` under
the adversary key `k`, and nothing for a session without a key.

*Real world.* The real X3DH protocol `x3dhReal G` followed by the double ratchet layer
`smLayer (smRealAt C R Gp D msgs)`, which keys the ratchet with the session key of every
`getKey` answer.

*Simulator.* `scSim G`, the X3DH simulator over `F_SC`: it keeps a copy of the real state,
draws all long-term and session secrets, forwards the honest events, answers `poll`, `pub`,
`ephPub` and `kdf` on its copy, refuses or forwards `corrupt` under the static rule of X3DH, and
on `complete` and `send` computes the key-derivation input of the session and calls `newKey` with
the key-derivation value for an exposed session and `newKey` or `newKeyUnlinked` with a
placeholder key otherwise. It never reads an answer of `F_SC` on the honest port.

*Bound.* For a CKA that neither touches the heap nor fails, for every finite set of parties `P`
and every environment `Z`, the distance is at most `signalBound`: the gap Diffie–Hellman bound
of the X3DH square, and a sum over the keys of the run of the secure-messaging advantages of the
explicit reductions `hopRed` and of the probability that a key is read twice. The last term is
the reuse of one root key by two ratchet runs, which `SM_Advantage` does not cover; it is `0`
for environments that read each session key (with its partner) at most once. No real-or-random
term of the key appears. -/
theorem signal_stack_realizes_FSC (P : Finset PartyId) {C : CKADef Sc Msg Key}
    (hC : CKAPureNF C) (R : PRGDef (K × Key) (K × Sa)) (Gp : PRGDef Sa (M × Sa))
    (D : AEADDef M Ct) (msgs : List (List (M × M))) :
    RealizesSim ((x3dhReal (K := K) G).seq (smLayer (smRealAt C R Gp D msgs)))
      (F_SC (smRealAt C R Gp D msgs) (sm_ideal C msgs)) (scSim G)
      (signalBound G P C R Gp D msgs hC) := by
  have hR : ∀ k, SPComp.IsPure (smRealAt C R Gp D msgs k) ∧
      SPComp.NoFail (smRealAt C R Gp D msgs k) := fun k => smRealAt_pureNF hC R Gp D msgs k
  have h := stack_realizes_FSC_of (x3dhReal (K := K) G) (simProt G) (simProt_opaque G) x3dhFwd
    (simProt_isFwd G) (x3dh_realizesSim_gapDH G P) (smRealAt C R Gp D msgs) (sm_ideal C msgs) hR
    (sm_ideal_pureNF hC msgs)
  intro ζ Z
  rw [smLayer_eq_keyLayer]
  refine (h ζ Z).trans (le_of_eq ?_)
  simp only [signalBound, scBound, SM_Advantage, sm_real_eq_bind_smRealAt, smLayer_eq_keyLayer]
  rfl

end Stack

/-! ## Time certificates -/

section Time

variable {K V : Type} [Fintype K] [Nonempty K] [Inhabited K]
  (realV : K → SPComp V) (idealV : SPComp V)

/-- **The tree of the reduction of the step `i`**: the environment reduction `sysEnvTree` of
`UCConcreteTimed` over the family of challenge worlds, with trees `next`, `obs`, `dist` of the
strategy and the distinguisher of `Z` and a tree `step` of the step of the challenge world. -/
noncomputable def hopRed.tree (i : ℕ) {ζ : Type}
    (Z : Env (Strat ζ (HEv ⊕ AEv K) (HOut V ⊕ AOut)) ζ) (next : ζ → SPTree (ζ × (HEv ⊕ AEv K)))
    (step : V → WSt K → HEv ⊕ AEv K → SPTree (WSt K × (HOut V ⊕ AOut)))
    (obs : ζ → HOut V ⊕ AOut → SPTree ζ) (dist : ζ → SPTree Bool) (v : V) : SPTree Bool :=
  sysEnvTree (chalWorld realV idealV i) Z next step obs dist v

/-- The tree of the reduction of the step `i` compiles to `hopRed i Z`. -/
theorem hopRed.compile_tree (i : ℕ) {ζ : Type}
    (Z : Env (Strat ζ (HEv ⊕ AEv K) (HOut V ⊕ AOut)) ζ)
    {next : ζ → SPTree (ζ × (HEv ⊕ AEv K))}
    {step : V → WSt K → HEv ⊕ AEv K → SPTree (WSt K × (HOut V ⊕ AOut))}
    {obs : ζ → HOut V ⊕ AOut → SPTree ζ} {dist : ζ → SPTree Bool}
    (hn : ∀ z, (next z).compile = Z.input.next z)
    (hs : ∀ v t e, (step v t e).compile = (chalWorld realV idealV i v).step t e)
    (ho : ∀ z o, (obs z o).compile = Z.input.obs z o) (hd : ∀ z, (dist z).compile = Z.dist z)
    (v : V) :
    (hopRed.tree realV idealV i Z next step obs dist v).compile = hopRed realV idealV i Z v :=
  sysEnvTree_compile _ Z hn hs ho hd v

derive_timed hopRed.tree

/-- **Time of the reduction of the step `i`.** On the challenge `v`, for a costed strategy of
`Z` and a costed step of the challenge world over the same interface, from initial states of
their invariants, and a distinguisher of time at most `tD` on the final states, the costed form
of the tree of `hopRed i Z` takes at most the reset to the heap of `Z`, the time of the strategy
over its `q = Z.input.rounds` activations, `tD`, the time of `q` steps of the challenge world,
`9` per activation and `11`: the time of the environment plus the steps of the world. -/
theorem hopRed.timeBound_timed (realVCost : K → ℕ) (i : ℕ) {ζ : Type}
    (Z : Env (Strat ζ (HEv ⊕ AEv K) (HOut V ⊕ AOut)) ζ)
    {next : ζ → SPTree.Timed (ζ × (HEv ⊕ AEv K))} {nextCost : ζ → ℕ}
    {step : V → WSt K → HEv ⊕ AEv K → SPTree.Timed (WSt K × (HOut V ⊕ AOut))}
    {stepCost : V → WSt K → HEv ⊕ AEv K → ℕ}
    {obs : ζ → HOut V ⊕ AOut → SPTree.Timed ζ} {obsCost : ζ → HOut V ⊕ AOut → ℕ}
    {dist : ζ → SPTree.Timed Bool} {distCost : ζ → ℕ} (v : V) {InvZ MidZ : ℕ → ζ → Prop}
    {InvS : ℕ → WSt K → Prop} {Ev : ℕ → HEv ⊕ AEv K → Prop} {Out : ℕ → HOut V ⊕ AOut → Prop}
    {tN tS tO : ℕ → ℕ} {tD : ℕ}
    (hZ : StratRunBound next nextCost obs obsCost InvZ MidZ Ev Out tN tO)
    (hS : SysRunBound (step v) (stepCost v) InvS Ev Out tS)
    (hz : InvZ 0 Z.input.init) (ht : InvS 0 (chalWorld realV idealV i v).init)
    (hd : ∀ z, InvZ Z.input.rounds z → SPTree.Timed.stepTime (distCost z, dist z) ≤ tD) :
    SPTree.Timed.stepTime (hopRed.tree.timed realV realVCost idealV i Z next nextCost step
        stepCost obs obsCost dist distCost v) ≤
      Z.heap.data.keys.card + (∑ j ∈ Finset.range Z.input.rounds, (tN j + tO j)) + tD +
        (∑ j ∈ Finset.range Z.input.rounds, tS j) + 9 * Z.input.rounds + 11 := by
  have h := sysEnvTree.timeBound_timed (chalWorld realV idealV i) (fun _ => 4) Z v hZ hS hz ht hd
  simp only [hopRed.tree.timed, SPTree.Timed.stepTime_delay]
  omega

end Time

end CatCrypt.Crypto.Messaging.SignalStackUC
