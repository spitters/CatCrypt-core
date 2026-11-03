/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.CKA
public import CatCryptCore.Crypto.OracleSimulation
public import CatCryptCore.Crypto.SPCompPMF
public import CatCryptCore.ForMathlib.PMFUniform

/-!
# Continuous key agreement with state corruption and randomness leakage

The CKA security game of Alwen, Coretti and Dodis (Definition 12), in the form of Dodis, Jost,
Katsumata, Prest and Schmidt (Definition 2.12, Figure 4). The adversary first chooses the
challenge epoch `t*`, then receives the public value of the initialisation and interacts with
the oracles of the game:

* `send P` — party `P` runs the sending algorithm; the message and the key are returned;
* `recv P` — party `P` receives the message in transit;
* `chall P` — as `send P` at the epoch `t*`, with the key replaced in the ideal game by a
  uniform key;
* `corrupt P` — the state of `P` is returned, if the corruption gate allows it;
* `sendLeak P` — as `send P`, with the randomness of the sending algorithm returned, if the
  leakage gate allows it.

The parties alternate: `A` sends in the odd epochs and `B` in the even ones, and a party
receives the message of an epoch before it sends in the next one. Each party has an epoch
counter `t_P`, incremented by its sends and its receives, so that both counters equal `t` after
epoch `t`. With the parameters `ΔFS` (forward secrecy) and `ΔPCS` (post-compromise security),

* the corruption of `P` is allowed when `max(t_A, t_B) + ΔPCS ≤ t*` (both parties are at least
  `ΔPCS` epochs before the challenge) or when `t* + ΔFS ≤ t_P` (party `P` is `ΔFS` epochs past
  the challenge);
* the send with leaked randomness is allowed when the epoch it opens is at least `ΔPCS` epochs
  before the challenge, `t_P + 1 + ΔPCS ≤ t*`.

Refused queries return `none` and leave the game state unchanged. The advantage
`CKA_Corrupt_Advantage C ΔFS ΔPCS A` is the distance between the games with the real and with
the uniform challenge key.

For the Diffie–Hellman scheme `dhCKA` of `CatCryptCore.Crypto.Messaging.CKA`, whose state
keeps the own last exponent next to the peer's public value, the forward-secrecy delay is `2`:
the challenged party holds the challenge exponent until its next send, two epochs after the
challenge. The advantage with `ΔFS = 2`, `ΔPCS = 2` equals the DDH advantage of the reduction
`ckaCorruptDDHRed A` (`dhCKA_corrupt_advantage_eq_ddh`). With `ΔFS = 1` the game allows the
corruption of the challenged party after it received the next message, and its state then
gives the challenge key.

The passive game `cka_real`/`cka_ideal` of `CatCryptCore.Crypto.Messaging.CKA` is the
corruption game of the adversary `ckaPassiveAdv k m`, which challenges epoch `k + 1`, never
corrupts and never leaks (`cka_advantage_eq_corrupt`).

## Main definitions

* `CKAParty`, `CKAQuery`, `CKAAns`, `CKAGameSt` — parties, queries, answers and game states
* `CKACoins` — a CKA scheme with an explicit-randomness sending algorithm
* `CKACorruptAdv` — an adversary: a distribution of the challenge epoch and an oracle tree
* `ckaCorruptOracle`, `cka_corrupt_game`, `CKA_Corrupt_Advantage` — the game and the advantage
* `ckaPassiveAdv` — the adversary of the passive game
* `dhCKAStep`, `dhCKASimStep` — the steps of the oracle of `dhCKA` and of its simulation
* `ckaCorruptDDHTreeOf`, `ckaCorruptDDHRed` — the DDH reduction

## Main results

* `cka_real_eq_corrupt`, `cka_ideal_eq_corrupt`, `cka_advantage_eq_corrupt` — the passive game
  is the corruption game of `ckaPassiveAdv`
* `OracleAdv.run_nf_eq_eager` — a uniform value used at one step of an oracle can be sampled in
  advance
* `OracleAdv.run_nf_map_fst_eq_of_rel` — related oracle states give equal outputs
* `dhCKA_corrupt_advantage_eq_ddh` — the corruption advantage of `dhCKA` with `ΔFS = 2`,
  `ΔPCS = 2` equals the DDH advantage of `ckaCorruptDDHRed A`
* `dhCKA_corrupt_advantage_le` — the same as an upper bound

## References

* J. Alwen, S. Coretti, Y. Dodis, *The Double Ratchet: Security Notions, Proofs, and
  Modularization for the Signal Protocol*, EUROCRYPT 2019, Definition 12 and Figure 3
* Y. Dodis, D. Jost, S. Katsumata, T. Prest, R. Schmidt, *Triple Ratchet: A Bandwidth Efficient
  Hybrid-Secure Signal Protocol*, EUROCRYPT 2025, Definition 2.12 and Figure 4
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCryptCore.Examples.CyclicGroupDDH
open scoped ENNReal

/-! ## Parties, queries and game states -/

/-- The two parties of a CKA run. -/
inductive CKAParty where
  | A
  | B
  deriving DecidableEq, Repr

/-- The peer of a party. -/
def CKAParty.other : CKAParty → CKAParty
  | .A => .B
  | .B => .A

@[simp] theorem CKAParty.other_other (p : CKAParty) : p.other.other = p := by
  cases p <;> rfl

@[simp] theorem CKAParty.other_ne (p : CKAParty) : p.other ≠ p := by
  cases p <;> decide

@[simp] theorem CKAParty.ne_other (p : CKAParty) : p ≠ p.other := by
  cases p <;> decide

@[simp] theorem CKAParty.other_A : CKAParty.A.other = .B := rfl

@[simp] theorem CKAParty.other_B : CKAParty.B.other = .A := rfl

theorem CKAParty.eq_or_eq_other (q p : CKAParty) : q = p ∨ q = p.other := by
  cases q <;> cases p <;> simp

/-- The sender of epoch `e`: `A` in the odd epochs, `B` in the even ones. -/
def ckaSender (e : ℕ) : CKAParty := if e % 2 = 1 then .A else .B

theorem ckaSender_succ (e : ℕ) : ckaSender (e + 1) = (ckaSender e).other := by
  unfold ckaSender
  rcases Nat.mod_two_eq_zero_or_one e with h | h
  · have h' : (e + 1) % 2 = 1 := by omega
    simp [h, h', CKAParty.other]
  · have h' : (e + 1) % 2 = 0 := by omega
    simp [h, h', CKAParty.other]

theorem ckaSender_add_two (e : ℕ) : ckaSender (e + 2) = ckaSender e := by
  rw [ckaSender_succ, ckaSender_succ, CKAParty.other_other]

/-- The queries of the CKA adversary. -/
inductive CKAQuery where
  /-- The party sends. -/
  | send (p : CKAParty)
  /-- The party receives the message in transit. -/
  | recv (p : CKAParty)
  /-- The party sends at the challenge epoch, with a real or a uniform key. -/
  | chall (p : CKAParty)
  /-- The state of the party is returned. -/
  | corrupt (p : CKAParty)
  /-- The party sends, and the randomness of the sending algorithm is returned. -/
  | sendLeak (p : CKAParty)

/-- The answers of the CKA oracles. -/
inductive CKAAns (St Msg Key Rand : Type) where
  /-- A refused query, or a receive. -/
  | none
  /-- The message and the key of a send. -/
  | out (T : Msg) (I : Key)
  /-- The state of a corrupted party. -/
  | state (s : St)
  /-- The message, the key and the randomness of a send with leaked randomness. -/
  | leak (T : Msg) (I : Key) (r : Rand)

/-- The state of the CKA game: the states and the epoch counters of the parties, and the
message in transit. -/
structure CKAGameSt (St Msg : Type) where
  /-- The states of the parties. -/
  st : CKAParty → St
  /-- The epoch counters of the parties. -/
  t : CKAParty → ℕ
  /-- The last message sent. -/
  msg : Msg

namespace CKAGameSt

variable {St Msg : Type}

/-- The initial game state: the first sender `A` in state `sA`, the first receiver `B` in
state `sB`, both counters at `0`; the message slot holds the public value `pub`. -/
def init (pub : Msg) (sA sB : St) : CKAGameSt St Msg where
  st := fun p => match p with
    | .A => sA
    | .B => sB
  t := fun _ => 0
  msg := pub

/-- The state after party `p` sent the message `T` and moved to state `x`. -/
def sent (s : CKAGameSt St Msg) (p : CKAParty) (x : St) (T : Msg) : CKAGameSt St Msg where
  st := Function.update s.st p x
  t := Function.update s.t p (s.t p + 1)
  msg := T

/-- The state after party `p` received the message in transit and moved to state `x`. -/
def recvd (s : CKAGameSt St Msg) (p : CKAParty) (x : St) : CKAGameSt St Msg where
  st := Function.update s.st p x
  t := Function.update s.t p (s.t p + 1)
  msg := s.msg

/-- Party `p` may send: both counters are equal and `p` is the sender of the next epoch. -/
def canSend (s : CKAGameSt St Msg) (p : CKAParty) : Bool :=
  s.t .A == s.t .B && ckaSender (s.t .A + 1) == p

/-- Party `p` may receive: its peer is one epoch ahead. -/
def canRecv (s : CKAGameSt St Msg) (p : CKAParty) : Bool :=
  s.t p + 1 == s.t p.other

end CKAGameSt

/-- The corruption gate of the game with challenge epoch `t` for party `p`: both counters are
at least `ΔPCS` epochs before the challenge, or `p` is at least `ΔFS` epochs past it. -/
def ckaAllowCorr {St Msg : Type} (ΔFS ΔPCS t : ℕ) (s : CKAGameSt St Msg) (p : CKAParty) :
    Bool :=
  decide (max (s.t .A) (s.t .B) + ΔPCS ≤ t) || decide (t + ΔFS ≤ s.t p)

/-- The leakage gate of the game with challenge epoch `t` for party `p`: `p` may send, and the
epoch it opens is at least `ΔPCS` epochs before the challenge. -/
def ckaAllowLeak {St Msg : Type} (ΔPCS t : ℕ) (s : CKAGameSt St Msg) (p : CKAParty) : Bool :=
  s.canSend p && decide (s.t p + 1 + ΔPCS ≤ t)

/-! ## The game -/

/-- A CKA scheme whose sending algorithm is given with its randomness in `Rand`:
`sendR s r` is the next state, the message and the key of a send from state `s` with the
randomness `r`. -/
class CKACoins {St Msg Key : Type} (C : CKADef St Msg Key) (Rand : outParam Type) where
  /-- The sending algorithm with explicit randomness. -/
  sendR : St → Rand → St × Msg × Key

/-- The explicit-randomness sending algorithm is that of the scheme: sending samples a uniform
randomness and runs `sendR`. -/
def CKACoins.Sound {St Msg Key Rand : Type} (C : CKADef St Msg Key) [CKACoins C Rand]
    [Fintype Rand] [Nonempty Rand] : Prop :=
  ∀ s, C.send s = SPComp.bind (SPComp.sample Rand) fun r =>
    SPComp.pure (CKACoins.sendR (C := C) s r)

/-- A CKA adversary with output in `α`: a distribution `tStar` of the challenge epoch, and for
each challenge epoch and public value of the initialisation an oracle tree. -/
structure CKACorruptAdv (St Msg Key Rand α : Type) : Type 1 where
  /-- The choice of the challenge epoch. -/
  tStar : PMF ℕ
  /-- The interaction with the oracles, from the challenge epoch and the public value. -/
  play : ℕ → Msg → OracleAdv CKAQuery (CKAAns St Msg Key Rand) α

/-- The run of an oracle tree against an oracle with computations in `SPComp`; the sampling
nodes of the tree are lifted distributions. -/
noncomputable def OracleAdv.runSP {S D R α : Type} (O : S → D → SPComp (R × S)) :
    OracleAdv D R α → S → SPComp (α × S)
  | .ret a, s => SPComp.pure (a, s)
  | .rand p k, s => SPComp.bind (liftPMF p) fun b => OracleAdv.runSP O (k b) s
  | .query d k, s => SPComp.bind (O s d) fun x => OracleAdv.runSP O (k x.1) x.2

variable {St Msg Key Rand α : Type}

/-- The oracle of the CKA game of `C` with the parameters `ΔFS`, `ΔPCS`, the challenge epoch
`t` and the challenge mode `ideal`. -/
noncomputable def ckaCorruptOracle (C : CKADef St Msg Key) [CKACoins C Rand] [Fintype Key]
    [Nonempty Key] [Fintype Rand] [Nonempty Rand] (ΔFS ΔPCS t : ℕ) (ideal : Bool)
    (s : CKAGameSt St Msg) : CKAQuery → SPComp (CKAAns St Msg Key Rand × CKAGameSt St Msg)
  | .send p =>
    if s.canSend p then
      SPComp.bind (C.send (s.st p)) fun o => SPComp.pure (.out o.2.1 o.2.2, s.sent p o.1 o.2.1)
    else SPComp.pure (.none, s)
  | .recv p =>
    SPComp.pure (if s.canRecv p then (.none, s.recvd p (C.recv (s.st p) s.msg).1)
      else (.none, s))
  | .chall p =>
    if s.canSend p && s.t p + 1 == t then
      SPComp.bind (C.send (s.st p)) fun o =>
        SPComp.bind (if ideal then SPComp.sample Key else SPComp.pure o.2.2) fun k =>
          SPComp.pure (.out o.2.1 k, s.sent p o.1 o.2.1)
    else SPComp.pure (.none, s)
  | .corrupt p =>
    SPComp.pure (if ckaAllowCorr ΔFS ΔPCS t s p then .state (s.st p) else .none, s)
  | .sendLeak p =>
    if ckaAllowLeak ΔPCS t s p then
      SPComp.bind (SPComp.sample Rand) fun r =>
        SPComp.pure (.leak (CKACoins.sendR (C := C) (s.st p) r).2.1
          (CKACoins.sendR (C := C) (s.st p) r).2.2 r,
          s.sent p (CKACoins.sendR (C := C) (s.st p) r).1
            (CKACoins.sendR (C := C) (s.st p) r).2.1)
    else SPComp.pure (.none, s)

/-- The CKA game with corruption and leakage: the adversary chooses the challenge epoch `t`,
the initialisation is run, and the adversary interacts with the oracle from the initial game
state. -/
noncomputable def cka_corrupt_game (C : CKADef St Msg Key) [CKACoins C Rand] [Fintype Key]
    [Nonempty Key] [Fintype Rand] [Nonempty Rand] (ΔFS ΔPCS : ℕ) (ideal : Bool)
    (A : CKACorruptAdv St Msg Key Rand α) : SPComp α :=
  SPComp.bind (liftPMF A.tStar) fun t =>
    SPComp.bind C.init fun i =>
      SPComp.bind (OracleAdv.runSP (ckaCorruptOracle C ΔFS ΔPCS t ideal) (A.play t i.1)
        (CKAGameSt.init i.1 i.2.1 i.2.2)) fun x => SPComp.pure x.1

/-- The real CKA game with corruption and leakage. -/
noncomputable abbrev cka_corrupt_real (C : CKADef St Msg Key) [CKACoins C Rand] [Fintype Key]
    [Nonempty Key] [Fintype Rand] [Nonempty Rand] (ΔFS ΔPCS : ℕ)
    (A : CKACorruptAdv St Msg Key Rand α) : SPComp α :=
  cka_corrupt_game C ΔFS ΔPCS false A

/-- The ideal CKA game with corruption and leakage: the challenge key is uniform. -/
noncomputable abbrev cka_corrupt_ideal (C : CKADef St Msg Key) [CKACoins C Rand] [Fintype Key]
    [Nonempty Key] [Fintype Rand] [Nonempty Rand] (ΔFS ΔPCS : ℕ)
    (A : CKACorruptAdv St Msg Key Rand α) : SPComp α :=
  cka_corrupt_game C ΔFS ΔPCS true A

/-- The advantage of the adversary `A` with output in `α` and the distinguisher `D`. -/
noncomputable def CKA_Corrupt_AdvantageA (C : CKADef St Msg Key) [CKACoins C Rand]
    [Fintype Key] [Nonempty Key] [Fintype Rand] [Nonempty Rand] (ΔFS ΔPCS : ℕ)
    (A : CKACorruptAdv St Msg Key Rand α) (D : α → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (cka_corrupt_real C ΔFS ΔPCS A) (cka_corrupt_ideal C ΔFS ΔPCS A) D

/-- **CKA advantage with state corruption and randomness leakage** of the adversary `A`: the
distance between the real and the ideal game. -/
noncomputable def CKA_Corrupt_Advantage (C : CKADef St Msg Key) [CKACoins C Rand]
    [Fintype Key] [Nonempty Key] [Fintype Rand] [Nonempty Rand] (ΔFS ΔPCS : ℕ)
    (A : CKACorruptAdv St Msg Key Rand Bool) : ℝ≥0∞ :=
  Advantage (cka_corrupt_real C ΔFS ΔPCS A) (cka_corrupt_ideal C ΔFS ΔPCS A)

/-! ## The passive game as a corruption game -/

namespace OracleAdv

variable {S D R β : Type}

/-- Running `A.bind f` runs `A`, then `f` on its output from the reached state. -/
theorem runSP_bind (O : S → D → SPComp (R × S)) (A : OracleAdv D R α)
    (f : α → OracleAdv D R β) (s : S) :
    runSP O (A.bind f) s = SPComp.bind (runSP O A s) fun x => runSP O (f x.1) x.2 := by
  induction A generalizing s with
  | ret a => simp only [OracleAdv.bind, runSP, SPComp.pure_bind]
  | rand p k ih => simp only [OracleAdv.bind, runSP, SPComp.bind_assoc, ih]
  | query d k ih => simp only [OracleAdv.bind, runSP, SPComp.bind_assoc, ih]

end OracleAdv

/-- The message and the key of a send answer, or the default `d`. -/
def CKAAns.outPair (d : Msg × Key) : CKAAns St Msg Key Rand → Msg × Key
  | .out T I => (T, I)
  | _ => d

/-- The last message of a transcript, or `d` for the empty transcript. -/
def ckaLastMsg : List (Msg × Key) → Msg → Msg
  | [], d => d
  | x :: l, _ => ckaLastMsg l x.1

/-- The adversary part of `n` epochs from the epoch `e`: the sender of each epoch sends, the
peer receives; the transcript is collected, with the default `d` for refused queries. -/
def ckaEpochs (d : Msg × Key) :
    ℕ → ℕ → OracleAdv CKAQuery (CKAAns St Msg Key Rand) (List (Msg × Key))
  | _, 0 => .ret []
  | e, n + 1 =>
    .query (.send (ckaSender (e + 1))) fun r =>
      .query (.recv (ckaSender (e + 1)).other) fun _ =>
        (ckaEpochs d (e + 1) n).bind fun l => .ret (r.outPair d :: l)

/-- **The adversary of the passive game**: challenge epoch `k + 1`; it runs `k` epochs, the
challenge epoch and `m` epochs, and outputs the public value and the transcript. It never
corrupts and never leaks. -/
noncomputable def ckaPassiveAdv [Nonempty Key] (k m : ℕ) :
    CKACorruptAdv St Msg Key Rand (CKAView Msg Key) where
  tStar := PMF.pure (k + 1)
  play _ pub :=
    (ckaEpochs (pub, Classical.arbitrary Key) 0 k).bind fun pre =>
      .query (.chall (ckaSender (k + 1))) fun r =>
        .query (.recv (ckaSender (k + 1)).other) fun _ =>
          (ckaEpochs (pub, Classical.arbitrary Key) (k + 1) m).bind fun post =>
            .ret (pub, pre, r.outPair (pub, Classical.arbitrary Key), post)

/-- The game state after `n` epochs from the epoch `e`: the next sender is in state `p.1`,
its peer in state `p.2`, both counters are `e + n`, and the message slot holds the last
message of the transcript `l`. -/
def ckaAfter (e n : ℕ) (l : List (Msg × Key)) (p : St × St) (m₀ : Msg) : CKAGameSt St Msg where
  st := fun q => if q = ckaSender (e + n + 1) then p.1 else p.2
  t := fun _ => e + n
  msg := ckaLastMsg l m₀

section Passive

variable (C : CKADef St Msg Key) [CKACoins C Rand] [Fintype Key] [Nonempty Key] [Fintype Rand]
  [Nonempty Rand]

theorem CKAGameSt.ext' {s s' : CKAGameSt St Msg} (h1 : s.st = s'.st) (h2 : s.t = s'.t)
    (h3 : s.msg = s'.msg) : s = s' := by
  cases s; cases s'; simp_all

/-- **Epochs of the passive adversary.** From a game state with both counters at `e`, the
`n` epochs of `ckaEpochs` run the sending and receiving algorithms as `ckaRun`. -/
theorem runSP_ckaEpochs (ΔFS ΔPCS t : ℕ) (ideal : Bool) {β : Type} (d : Msg × Key) (n : ℕ) :
    ∀ (e : ℕ) (s : CKAGameSt St Msg)
      (K : List (Msg × Key) → OracleAdv CKAQuery (CKAAns St Msg Key Rand) β),
      s.t .A = e → s.t .B = e →
      OracleAdv.runSP (ckaCorruptOracle C ΔFS ΔPCS t ideal) ((ckaEpochs d e n).bind K) s =
        SPComp.bind (ckaRun C n (s.st (ckaSender (e + 1))) (s.st (ckaSender (e + 1)).other))
          fun p => OracleAdv.runSP (ckaCorruptOracle C ΔFS ΔPCS t ideal) (K p.1)
            (ckaAfter e n p.1 p.2 s.msg) := by
  induction n with
  | zero =>
    intro e s K hA hB
    simp only [ckaEpochs, OracleAdv.bind, ckaRun, SPComp.pure_bind]
    congr 1
    refine CKAGameSt.ext' (funext fun q => ?_) (funext fun q => ?_) rfl
    · simp only [ckaAfter, Nat.add_zero]
      by_cases hq : q = ckaSender (e + 1)
      · rw [if_pos hq, hq]
      · rw [if_neg hq]
        cases q <;> cases h : ckaSender (e + 1) <;> simp_all [CKAParty.other]
    · cases q <;> simp [ckaAfter, hA, hB]
  | succ n ih =>
    intro e s K hA hB
    have hsend : s.canSend (ckaSender (e + 1)) = true := by
      simp [CKAGameSt.canSend, hA, hB]
    simp only [ckaEpochs, OracleAdv.bind, OracleAdv.runSP, ckaCorruptOracle, hsend, if_true,
      SPComp.bind_assoc, SPComp.pure_bind, ckaRun]
    congr 1; funext o
    have hrecv : (s.sent (ckaSender (e + 1)) o.1 o.2.1).canRecv (ckaSender (e + 1)).other =
        true := by
      cases h : ckaSender (e + 1) <;>
        simp [CKAGameSt.canRecv, CKAGameSt.sent, Function.update, CKAParty.other, hA, hB]
    simp only [hrecv, if_true, SPComp.pure_bind, OracleAdv.bind_assoc, OracleAdv.bind_ret]
    rw [ih (e + 1) _ _ (by cases h : ckaSender (e + 1) <;>
          simp [CKAGameSt.recvd, CKAGameSt.sent, Function.update, CKAParty.other, hA, hB])
        (by cases h : ckaSender (e + 1) <;>
          simp [CKAGameSt.recvd, CKAGameSt.sent, Function.update, CKAParty.other, hA, hB])]
    have h2 : ckaSender (e + 1 + 1) = (ckaSender (e + 1)).other := ckaSender_succ _
    simp only [h2, CKAParty.other_other, CKAGameSt.recvd, CKAGameSt.sent,
      Function.update_self, Function.update_of_ne (CKAParty.ne_other _),
      Function.update_of_ne (CKAParty.other_ne _), SPComp.bind_assoc, SPComp.pure_bind]
    congr 1; funext p
    simp only [CKAAns.outPair]
    congr 1
    refine CKAGameSt.ext' (funext fun q => ?_) (funext fun q => ?_) rfl
    · simp only [ckaAfter, show e + 1 + n + 1 = e + (n + 1) + 1 by omega]
    · simp only [ckaAfter]; omega

/-- The real passive game is the real corruption game of `ckaPassiveAdv k m`. -/
theorem cka_real_eq_corrupt (ΔFS ΔPCS k m : ℕ) :
    cka_real C k m = cka_corrupt_real C ΔFS ΔPCS (ckaPassiveAdv (Rand := Rand) k m) := by
  unfold cka_corrupt_real cka_corrupt_game cka_real
  simp only [ckaPassiveAdv, ← liftPMF_pure, SPComp.pure_bind]
  congr 1; funext i
  rw [runSP_ckaEpochs C ΔFS ΔPCS (k + 1) false _ k 0 _ _ rfl rfl, SPComp.bind_assoc]
  simp only [Nat.zero_add, CKAGameSt.init]
  have h1 : ckaSender 1 = .A := rfl
  simp only [h1, CKAParty.other_A]
  congr 1; funext p
  have hch : (ckaAfter 0 k p.1 p.2 i.1 : CKAGameSt St Msg).canSend (ckaSender (k + 1)) &&
      (ckaAfter 0 k p.1 p.2 i.1 : CKAGameSt St Msg).t (ckaSender (k + 1)) + 1 == k + 1 :=
    by simp [ckaAfter, CKAGameSt.canSend]
  simp only [OracleAdv.runSP, ckaCorruptOracle, hch, if_true, SPComp.bind_assoc,
    SPComp.pure_bind, Bool.false_eq_true, if_false]
  simp only [ckaAfter, Nat.zero_add, if_true]
  congr 1; funext o
  have hrecv : (CKAGameSt.sent ⟨fun q => if q = ckaSender (k + 1) then p.2.1 else p.2.2,
      fun _ => k, ckaLastMsg p.1 i.1⟩ (ckaSender (k + 1)) o.1 o.2.1).canRecv
        (ckaSender (k + 1)).other = true := by
    simp [CKAGameSt.canRecv, CKAGameSt.sent, Function.update]
  simp only [hrecv, if_true, SPComp.pure_bind]
  rw [runSP_ckaEpochs C ΔFS ΔPCS (k + 1) false _ m (k + 1) _ _
    (by cases h : ckaSender (k + 1) <;>
      simp [CKAGameSt.recvd, CKAGameSt.sent, Function.update, CKAParty.other])
    (by cases h : ckaSender (k + 1) <;>
      simp [CKAGameSt.recvd, CKAGameSt.sent, Function.update, CKAParty.other]),
    SPComp.bind_assoc]
  simp only [ckaSender_succ, CKAParty.other_other, CKAGameSt.recvd, CKAGameSt.sent,
    Function.update_self, Function.update_of_ne (CKAParty.ne_other _),
    Function.update_of_ne (CKAParty.other_ne _), OracleAdv.runSP, SPComp.pure_bind,
    CKAAns.outPair, CKAParty.ne_other, ↓reduceIte]

/-- The ideal passive game is the ideal corruption game of `ckaPassiveAdv k m`. -/
theorem cka_ideal_eq_corrupt (ΔFS ΔPCS k m : ℕ) :
    cka_ideal C k m = cka_corrupt_ideal C ΔFS ΔPCS (ckaPassiveAdv (Rand := Rand) k m) := by
  unfold cka_corrupt_ideal cka_corrupt_game cka_ideal
  simp only [ckaPassiveAdv, ← liftPMF_pure, SPComp.pure_bind]
  congr 1; funext i
  rw [runSP_ckaEpochs C ΔFS ΔPCS (k + 1) true _ k 0 _ _ rfl rfl, SPComp.bind_assoc]
  simp only [Nat.zero_add, CKAGameSt.init]
  have h1 : ckaSender 1 = .A := rfl
  simp only [h1, CKAParty.other_A]
  congr 1; funext p
  have hch : (ckaAfter 0 k p.1 p.2 i.1 : CKAGameSt St Msg).canSend (ckaSender (k + 1)) &&
      (ckaAfter 0 k p.1 p.2 i.1 : CKAGameSt St Msg).t (ckaSender (k + 1)) + 1 == k + 1 :=
    by simp [ckaAfter, CKAGameSt.canSend]
  simp only [OracleAdv.runSP, ckaCorruptOracle, hch, if_true, SPComp.bind_assoc,
    SPComp.pure_bind]
  simp only [ckaAfter, Nat.zero_add, if_true]
  congr 1; funext o; congr 1; funext u
  have hrecv : (CKAGameSt.sent ⟨fun q => if q = ckaSender (k + 1) then p.2.1 else p.2.2,
      fun _ => k, ckaLastMsg p.1 i.1⟩ (ckaSender (k + 1)) o.1 o.2.1).canRecv
        (ckaSender (k + 1)).other = true := by
    simp [CKAGameSt.canRecv, CKAGameSt.sent, Function.update]
  simp only [hrecv, if_true, SPComp.pure_bind]
  rw [runSP_ckaEpochs C ΔFS ΔPCS (k + 1) true _ m (k + 1) _ _
    (by cases h : ckaSender (k + 1) <;>
      simp [CKAGameSt.recvd, CKAGameSt.sent, Function.update, CKAParty.other])
    (by cases h : ckaSender (k + 1) <;>
      simp [CKAGameSt.recvd, CKAGameSt.sent, Function.update, CKAParty.other]),
    SPComp.bind_assoc]
  simp only [ckaSender_succ, CKAParty.other_other, CKAGameSt.recvd, CKAGameSt.sent,
    Function.update_self, Function.update_of_ne (CKAParty.ne_other _),
    Function.update_of_ne (CKAParty.other_ne _), OracleAdv.runSP, SPComp.pure_bind,
    CKAAns.outPair, CKAParty.ne_other, ↓reduceIte]

/-- **The passive game is a corruption game.** For all parameters `ΔFS`, `ΔPCS`, the passive
CKA advantage of the distinguisher `D` at the challenge epoch `k + 1` with `m` epochs after it
is the corruption-game advantage of the adversary `ckaPassiveAdv k m`, which never corrupts
and never leaks, followed by `D`. -/
theorem cka_advantage_eq_corrupt (ΔFS ΔPCS k m : ℕ) (D : CKAView Msg Key → SPComp Bool) :
    CKA_Advantage C k m D =
      CKA_Corrupt_AdvantageA C ΔFS ΔPCS (ckaPassiveAdv (Rand := Rand) k m) D := by
  unfold CKA_Advantage CKA_Corrupt_AdvantageA
  rw [cka_real_eq_corrupt C ΔFS ΔPCS k m, cka_ideal_eq_corrupt C ΔFS ΔPCS k m]

end Passive

/-! ## Oracles in normal form

An oracle in normal form draws a value `e` from a fixed distribution `μ` at each query and
answers deterministically by a step function `δ s d e`. -/

namespace OracleAdv

variable {S S' D R E β : Type}

/-- The oracle that draws `e` from `μ` and answers with `δ s d e`. -/
noncomputable abbrev nfOracle (μ : PMF E) (δ : S → D → E → R × S) : S → D → PMF (R × S) :=
  fun s d => μ.map (δ s d)

/-- **Related states give equal outputs.** If the steps `δ` and `δ'` give equal answers and
related next states from related states, for every drawn value, then the outputs of the runs
from related states are equal. -/
theorem run_nf_map_fst_eq_of_rel (μ : PMF E) (δ : S → D → E → R × S)
    (δ' : S' → D → E → R × S') (Rel : S → S' → Prop)
    (h : ∀ s s', Rel s s' → ∀ d e, (δ s d e).1 = (δ' s' d e).1 ∧
      Rel (δ s d e).2 (δ' s' d e).2)
    (A : OracleAdv D R β) (s : S) (s' : S') (hs : Rel s s') :
    (OracleAdv.run (nfOracle μ δ) A s).map Prod.fst = (OracleAdv.run (nfOracle μ δ') A s').map Prod.fst := by
  induction A generalizing s s' with
  | ret a => simp only [OracleAdv.run_ret, PMF.pure_map]
  | rand p k ih => simp only [OracleAdv.run_rand, PMF.map_bind, ih _ s s' hs]
  | query d k ih =>
    simp only [OracleAdv.run_query, nfOracle, PMF.bind_map, PMF.map_bind]
    congr 1; funext e
    obtain ⟨h1, h2⟩ := h s s' hs d e
    simp only [Function.comp_apply, h1]
    exact ih _ _ _ h2

/-- The step `δ` with the drawn value replaced by `v` at the critical steps `c s d`. -/
def eagerStep (δ : S → D → E → R × S) (c : S → D → Bool) (v : E) (s : S) (d : D) (e : E) :
    R × S :=
  if c s d then δ s d v else δ s d e

theorem eagerStep_exists (δ : S → D → E → R × S) (c : S → D → Bool) (v : E) (s : S) (d : D)
    (e : E) : ∃ e', eagerStep δ c v s d e = δ s d e' := by
  unfold eagerStep; split
  · exact ⟨v, rfl⟩
  · exact ⟨e, rfl⟩

/-- After the critical step, the eager oracle is the lazy one. -/
theorem run_nf_eager_of_done (μ : PMF E) (δ : S → D → E → R × S) (c : S → D → Bool)
    (N : S → Prop) (h2 : ∀ s d e, N s → N (δ s d e).2) (h3 : ∀ s d, N s → c s d = false)
    (v : E) (A : OracleAdv D R β) (s : S) (hs : N s) :
    OracleAdv.run (nfOracle μ (eagerStep δ c v)) A s = OracleAdv.run (nfOracle μ δ) A s := by
  induction A generalizing s with
  | ret a => rfl
  | rand p k ih => simp only [OracleAdv.run_rand, ih _ s hs]
  | query d k ih =>
    simp only [OracleAdv.run_query, nfOracle, PMF.bind_map]
    have he : eagerStep δ c v s d = δ s d := by
      funext e; simp only [eagerStep, h3 s d hs, Bool.false_eq_true, if_false]
    rw [he]
    congr 1; funext e
    exact ih _ _ (h2 s d e hs)

/-- **Eager sampling.** If the critical steps `c` lead to the states `N`, which are kept by
every step and admit no critical step, then drawing the value of the critical step in advance
does not change the run. -/
theorem run_nf_eq_eager (μ : PMF E) (δ : S → D → E → R × S) (c : S → D → Bool)
    (N : S → Prop) (h1 : ∀ s d e, c s d = true → N (δ s d e).2)
    (h2 : ∀ s d e, N s → N (δ s d e).2) (h3 : ∀ s d, N s → c s d = false)
    (A : OracleAdv D R β) (s : S) :
    OracleAdv.run (nfOracle μ δ) A s = μ.bind fun v => OracleAdv.run (nfOracle μ (eagerStep δ c v)) A s := by
  induction A generalizing s with
  | ret a => simp only [OracleAdv.run_ret, PMF.bind_const]
  | rand p k ih =>
    simp only [OracleAdv.run_rand, ih]
    exact PMF.bind_comm _ _ _
  | query d k ih =>
    simp only [OracleAdv.run_query, nfOracle, PMF.bind_map]
    cases hc : c s d with
    | true =>
      have he : ∀ v, eagerStep δ c v s d = fun _ => δ s d v := by
        intro v; funext e; simp only [eagerStep, hc, if_true]
      simp only [he]
      refine congrArg _ (funext fun v => ?_)
      simp only [Function.comp_def, PMF.bind_const]
      exact (run_nf_eager_of_done μ δ c N h2 h3 v _ _ (h1 s d v hc)).symm
    | false =>
      have he : ∀ v, eagerStep δ c v s d = δ s d := by
        intro v; funext e; simp only [eagerStep, hc, Bool.false_eq_true, if_false]
      simp only [he, Function.comp_def, ih]
      exact PMF.bind_comm _ _ _

end OracleAdv

/-! ## The Diffie–Hellman instance -/

section DHSteps

variable {E Gr : Type}

/-- The step of the oracle of the corruption game of the Diffie–Hellman CKA with the
exponentiations `pow` (of the generator) and `epow` (of a group element), on the drawn exponent
`e.1` and the drawn group element `e.2` (the uniform challenge key of the ideal game). -/
def dhCKAStepOf (pow : E → Gr) (epow : Gr → E → Gr) (ΔFS ΔPCS t : ℕ) (ideal : Bool)
    (s : CKAGameSt (Gr × E) Gr) (q : CKAQuery) (e : E × Gr) :
    CKAAns (Gr × E) Gr Gr E × CKAGameSt (Gr × E) Gr :=
  match q with
  | .send p =>
    if s.canSend p then
      (.out (pow e.1) (epow (s.st p).1 e.1), s.sent p ((s.st p).1, e.1) (pow e.1))
    else (.none, s)
  | .recv p => if s.canRecv p then (.none, s.recvd p (s.msg, (s.st p).2)) else (.none, s)
  | .chall p =>
    if s.canSend p && s.t p + 1 == t then
      (.out (pow e.1) (if ideal then e.2 else epow (s.st p).1 e.1),
        s.sent p ((s.st p).1, e.1) (pow e.1))
    else (.none, s)
  | .corrupt p => (if ckaAllowCorr ΔFS ΔPCS t s p then .state (s.st p) else .none, s)
  | .sendLeak p =>
    if ckaAllowLeak ΔPCS t s p then
      (.leak (pow e.1) (epow (s.st p).1 e.1) e.1, s.sent p ((s.st p).1, e.1) (pow e.1))
    else (.none, s)

/-- **The step of the simulator** with the DDH triple `(ga, gb, z)`: as `dhCKAStepOf`, except
that the send of epoch `t - 1` has the message `ga`, whose exponent is unknown, and the key
`ga` raised to the exponent of the receiver, and that the challenge has the message `gb` and
the key `z`. The exponent stored for these sends is the drawn one, which the game never
reveals. -/
def dhCKASimStepOf (pow : E → Gr) (epow : Gr → E → Gr) (ΔFS ΔPCS t : ℕ) (ga gb z : Gr)
    (s : CKAGameSt (Gr × E) Gr) (q : CKAQuery) (e : E × Gr) :
    CKAAns (Gr × E) Gr Gr E × CKAGameSt (Gr × E) Gr :=
  match q with
  | .send p =>
    if s.canSend p then
      if s.t p + 2 == t then
        (.out ga (epow ga (s.st p.other).2), s.sent p ((s.st p).1, e.1) ga)
      else (.out (pow e.1) (epow (s.st p).1 e.1), s.sent p ((s.st p).1, e.1) (pow e.1))
    else (.none, s)
  | .recv p => if s.canRecv p then (.none, s.recvd p (s.msg, (s.st p).2)) else (.none, s)
  | .chall p =>
    if s.canSend p && s.t p + 1 == t then (.out gb z, s.sent p ((s.st p).1, e.1) gb)
    else (.none, s)
  | .corrupt p => (if ckaAllowCorr ΔFS ΔPCS t s p then .state (s.st p) else .none, s)
  | .sendLeak p =>
    if ckaAllowLeak ΔPCS t s p then
      (.leak (pow e.1) (epow (s.st p).1 e.1) e.1, s.sent p ((s.st p).1, e.1) (pow e.1))
    else (.none, s)

/-- The critical step of the first eager hop: the send of epoch `t - 1`. -/
def dhCritA {St Msg : Type} (t : ℕ) (s : CKAGameSt St Msg) : CKAQuery → Bool
  | .send p => s.canSend p && s.t p + 2 == t
  | _ => false

/-- The critical step of the second eager hop: the challenge. -/
def dhCritB {St Msg : Type} (t : ℕ) (s : CKAGameSt St Msg) : CKAQuery → Bool
  | .chall p => s.canSend p && s.t p + 1 == t
  | _ => false

/-- The send of epoch `t - 1` has happened, or cannot happen any more. -/
def dhDoneA {St Msg : Type} (t : ℕ) (s : CKAGameSt St Msg) : Prop :=
  2 * t < s.t .A + s.t .B + 4

/-- The challenge has happened, or cannot happen any more. -/
def dhDoneB {St Msg : Type} (t : ℕ) (s : CKAGameSt St Msg) : Prop :=
  2 * t < s.t .A + s.t .B + 2

/-- The exponent of party `p` is not determined by the view of the simulator: the window of
the challenged party `ckaSender t` is `[t - 1, t + 1]`, that of its peer `[t - 1, t]`. -/
def dhHidden {St Msg : Type} (t : ℕ) (s : CKAGameSt St Msg) (p : CKAParty) : Prop :=
  t - 1 ≤ s.t p ∧ (if p = ckaSender t then s.t p ≤ t + 1 else s.t p ≤ t)

end DHSteps

/-! ### Game-state lemmas -/

namespace CKAGameSt

variable {St Msg : Type}

@[simp] theorem sent_st (s : CKAGameSt St Msg) (p q : CKAParty) (x : St) (T : Msg) :
    (s.sent p x T).st q = if q = p then x else s.st q := by
  simp only [sent, Function.update_apply]

@[simp] theorem sent_t (s : CKAGameSt St Msg) (p q : CKAParty) (x : St) (T : Msg) :
    (s.sent p x T).t q = if q = p then s.t p + 1 else s.t q := by
  simp only [sent, Function.update_apply]

@[simp] theorem sent_msg (s : CKAGameSt St Msg) (p : CKAParty) (x : St) (T : Msg) :
    (s.sent p x T).msg = T := rfl

@[simp] theorem recvd_st (s : CKAGameSt St Msg) (p q : CKAParty) (x : St) :
    (s.recvd p x).st q = if q = p then x else s.st q := by
  simp only [recvd, Function.update_apply]

@[simp] theorem recvd_t (s : CKAGameSt St Msg) (p q : CKAParty) (x : St) :
    (s.recvd p x).t q = if q = p then s.t p + 1 else s.t q := by
  simp only [recvd, Function.update_apply]

@[simp] theorem recvd_msg (s : CKAGameSt St Msg) (p : CKAParty) (x : St) :
    (s.recvd p x).msg = s.msg := rfl

theorem canSend_iff (s : CKAGameSt St Msg) (p : CKAParty) :
    s.canSend p = true ↔ s.t .A = s.t .B ∧ ckaSender (s.t .A + 1) = p := by
  simp [canSend]

theorem canRecv_iff (s : CKAGameSt St Msg) (p : CKAParty) :
    s.canRecv p = true ↔ s.t p + 1 = s.t p.other := by
  simp [canRecv]

theorem t_eq_of_eq {s : CKAGameSt St Msg} (h : s.t .A = s.t .B) (p : CKAParty) :
    s.t p = s.t .A := by
  cases p
  · rfl
  · exact h.symm

theorem t_other_eq_of_eq {s : CKAGameSt St Msg} (h : s.t .A = s.t .B) (p : CKAParty) :
    s.t p.other = s.t .A := by
  cases p
  · exact h.symm
  · rfl

theorem sum_t (s : CKAGameSt St Msg) (p : CKAParty) :
    s.t .A + s.t .B = s.t p + s.t p.other := by
  cases p
  · rfl
  · exact Nat.add_comm _ _

end CKAGameSt

section DHRel

variable {G : Type} [CG : CyclicGroup G]

/-- **The simulation relation** between a state `s` of the eager game, in which the send of
epoch `t - 1` used the exponent `a`, and a state `σ` of the simulator: equal counters,
messages and public values, and equal exponents outside the hidden windows; and the
invariants of the eager game: the counters are equal or the last sender is one epoch ahead,
the next sender holds the public value of its peer's exponent, the message in transit is the
public value of its sender's exponent, and the peer of the challenged party holds `a` in its
hidden window. -/
structure DHRel (a : CG.Exp) (t : ℕ) (s σ : CKAGameSt (G × CG.Exp) G) : Prop where
  t_eq : s.t = σ.t
  msg_eq : s.msg = σ.msg
  h_eq : ∀ p, (s.st p).1 = (σ.st p).1
  y_eq : ∀ p, ¬ dhHidden t s p → (s.st p).2 = (σ.st p).2
  shape : s.t .A = s.t .B ∨ ∃ p, s.t p = s.t p.other + 1 ∧ ckaSender (s.t p) = p
  inv1 : s.t .A = s.t .B →
    (s.st (ckaSender (s.t .A + 1))).1 = CG.pow (s.st (ckaSender (s.t .A + 1)).other).2
  inv2 : ∀ p, s.t p = s.t p.other + 1 → s.msg = CG.pow (s.st p).2
  inv3 : 1 ≤ t → t - 1 ≤ s.t (ckaSender t).other → s.t (ckaSender t).other ≤ t →
    (s.st (ckaSender t).other).2 = a

end DHRel

theorem dhHidden_sent_of_ne {St Msg : Type} (t : ℕ) (s : CKAGameSt St Msg) {p q : CKAParty}
    (hq : q ≠ p) (x : St) (T : Msg) : dhHidden t (s.sent p x T) q ↔ dhHidden t s q := by
  simp only [dhHidden, CKAGameSt.sent_t, hq, if_false]

theorem dhHidden_recvd_of_ne {St Msg : Type} (t : ℕ) (s : CKAGameSt St Msg) {p q : CKAParty}
    (hq : q ≠ p) (x : St) : dhHidden t (s.recvd p x) q ↔ dhHidden t s q := by
  simp only [dhHidden, CKAGameSt.recvd_t, hq, if_false]

/-- A party that the gates with `ΔFS = 2` and `ΔPCS = 2` allow to corrupt is outside its
hidden window. -/
theorem not_dhHidden_of_allowCorr {St Msg : Type} {t : ℕ} {s : CKAGameSt St Msg}
    {p : CKAParty} (h : ckaAllowCorr 2 2 t s p = true) : ¬ dhHidden t s p := by
  intro ⟨h1, h2⟩
  have hp : s.t p ≤ max (s.t .A) (s.t .B) := by
    cases p
    · exact le_max_left _ _
    · exact le_max_right _ _
  have h2' : s.t p ≤ t + 1 := by split at h2 <;> omega
  simp only [ckaAllowCorr, Bool.or_eq_true, decide_eq_true_eq] at h
  omega

namespace DHRel

variable {G : Type} [CG : CyclicGroup G] {a : CG.Exp} {t : ℕ} {s σ : CKAGameSt (G × CG.Exp) G}

/-- The simulation relation after a send of party `p` with the exponents `x` (eager game) and
`x'` (simulator), equal outside the hidden window. -/
theorem sent (h : DHRel a t s σ) {p : CKAParty} (hc : s.canSend p = true) (x x' : CG.Exp)
    (T : G) (hT : T = CG.pow x)
    (hx : ¬ dhHidden t (s.sent p ((s.st p).1, x) T) p → x = x')
    (ha : p = (ckaSender t).other → 1 ≤ t → t - 1 ≤ s.t p + 1 → s.t p + 1 ≤ t → x = a) :
    DHRel a t (s.sent p ((s.st p).1, x) T) (σ.sent p ((σ.st p).1, x') T) := by
  rw [CKAGameSt.canSend_iff] at hc
  obtain ⟨hAB, hp⟩ := hc
  have htp : s.t p = s.t .A := CKAGameSt.t_eq_of_eq hAB p
  have hto : s.t p.other = s.t .A := CKAGameSt.t_other_eq_of_eq hAB p
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext q
    simp only [CKAGameSt.sent_t, h.t_eq]
  · intro q
    simp only [CKAGameSt.sent_st]
    split
    · subst q; exact h.h_eq _
    · exact h.h_eq q
  · intro q hq
    by_cases hqp : q = p
    · subst hqp
      simp only [CKAGameSt.sent_st, if_true]
      exact hx hq
    · simp only [CKAGameSt.sent_st, hqp, if_false]
      exact h.y_eq q ((not_congr (dhHidden_sent_of_ne t s hqp _ _)).1 hq)
  · right
    refine ⟨p, ?_, ?_⟩
    · simp only [CKAGameSt.sent_t, if_true, CKAParty.other_ne, if_false]
      omega
    · simp only [CKAGameSt.sent_t, if_true, htp, hp]
  · intro hAB'
    exfalso
    cases p <;> simp only [CKAGameSt.sent_t, if_true, reduceCtorEq, if_false] at hAB' <;>
      simp only [CKAParty.other] at hto <;> omega
  · intro q hq
    by_cases hqp : q = p
    · subst hqp
      simp only [CKAGameSt.sent_msg, CKAGameSt.sent_st, if_true, hT]
    · exfalso
      have hqo : q = p.other := (CKAParty.eq_or_eq_other q p).resolve_left hqp
      subst hqo
      simp only [CKAGameSt.sent_t, CKAParty.other_other, if_true, CKAParty.other_ne,
        if_false] at hq
      omega
  · intro h1 hlo hhi
    by_cases hP : p = (ckaSender t).other
    · have hP' := hP
      subst hP
      simp only [CKAGameSt.sent_st, CKAGameSt.sent_t, if_true] at hlo hhi ⊢
      exact ha rfl h1 hlo hhi
    · have hne : (ckaSender t).other ≠ p := fun e => hP e.symm
      simp only [CKAGameSt.sent_st, CKAGameSt.sent_t, hne, if_false] at hlo hhi ⊢
      exact h.inv3 h1 hlo hhi

/-- The simulation relation after a receive of party `p`. -/
theorem recvd (h : DHRel a t s σ) {p : CKAParty} (hc : s.canRecv p = true) :
    DHRel a t (s.recvd p (s.msg, (s.st p).2)) (σ.recvd p (σ.msg, (σ.st p).2)) := by
  rw [CKAGameSt.canRecv_iff] at hc
  have hahead : ckaSender (s.t p.other) = p.other := by
    rcases h.shape with hAB | ⟨q, hq1, hq2⟩
    · exfalso
      have h1 := CKAGameSt.t_eq_of_eq hAB p
      have h2 := CKAGameSt.t_other_eq_of_eq hAB p
      omega
    · by_cases hqp : q = p
      · subst hqp; omega
      · have hqo : q = p.other := (CKAParty.eq_or_eq_other q p).resolve_left hqp
        subst hqo; exact hq2
  have hsnd : ckaSender (s.t p + 1) = p.other := by rw [hc]; exact hahead
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext q
    simp only [CKAGameSt.recvd_t, h.t_eq]
  · simp only [CKAGameSt.recvd_msg, h.msg_eq]
  · intro q
    simp only [CKAGameSt.recvd_st]
    split
    · exact h.msg_eq
    · exact h.h_eq q
  · intro q hq
    by_cases hqp : q = p
    · subst hqp
      simp only [CKAGameSt.recvd_st, if_true]
      refine h.y_eq _ fun hh => hq ?_
      obtain ⟨hh1, hh2⟩ := hh
      refine ⟨by simp only [CKAGameSt.recvd_t, if_true]; omega, ?_⟩
      simp only [CKAGameSt.recvd_t, if_true]
      by_cases hS : q = ckaSender t
      · rw [if_pos hS] at hh2 ⊢
        by_contra hlt
        have heq : s.t q = t + 1 := by omega
        rw [heq, show t + 1 + 1 = t + 2 by omega, ckaSender_add_two, ← hS] at hsnd
        exact CKAParty.ne_other _ hsnd
      · rw [if_neg hS] at hh2 ⊢
        by_contra hlt
        have heq : s.t q = t := by omega
        have hq' : q = (ckaSender t).other :=
          (CKAParty.eq_or_eq_other q (ckaSender t)).resolve_left hS
        rw [heq, ckaSender_succ, ← hq'] at hsnd
        exact CKAParty.ne_other _ hsnd
    · simp only [CKAGameSt.recvd_st, hqp, if_false]
      exact h.y_eq q ((not_congr (dhHidden_recvd_of_ne t s hqp _)).1 hq)
  · left
    cases p <;> simp only [CKAGameSt.recvd_t, if_true, reduceCtorEq, if_false] <;>
      simp only [CKAParty.other] at hc <;> omega
  · intro _
    have hA : (s.recvd p (s.msg, (s.st p).2)).t .A + 1 = s.t p.other + 1 := by
      cases p <;> simp only [CKAGameSt.recvd_t, if_true, reduceCtorEq, if_false] <;>
        simp only [CKAParty.other] at hc ⊢ <;> omega
    have hn : ckaSender ((s.recvd p (s.msg, (s.st p).2)).t .A + 1) = p := by
      rw [hA, ckaSender_succ, hahead, CKAParty.other_other]
    rw [hn]
    simp only [CKAGameSt.recvd_st, if_true, CKAParty.other_ne, if_false]
    exact h.inv2 p.other (by rw [CKAParty.other_other]; omega)
  · intro q hq
    exfalso
    cases p <;> cases q <;> simp only [CKAGameSt.recvd_t, if_true, reduceCtorEq, if_false,
      CKAParty.other] at hq hc <;> omega
  · intro h1 hlo hhi
    by_cases hP : p = (ckaSender t).other
    · have hsP : ckaSender (s.t p + 1) = p.other := hsnd
      subst hP
      simp only [CKAGameSt.recvd_st, CKAGameSt.recvd_t, if_true] at hlo hhi ⊢
      by_cases hw : t - 1 ≤ s.t (ckaSender t).other
      · exact h.inv3 h1 hw (by omega)
      · exfalso
        have heq : s.t (ckaSender t).other + 2 = t := by omega
        have : ckaSender (s.t (ckaSender t).other + 1 + 1) = ckaSender t := by
          rw [show s.t (ckaSender t).other + 1 + 1 = t by omega]
        rw [ckaSender_succ, hsP, CKAParty.other_other] at this
        exact CKAParty.other_ne _ this
    · have hne : (ckaSender t).other ≠ p := fun e => hP e.symm
      simp only [CKAGameSt.recvd_st, CKAGameSt.recvd_t, hne, if_false] at hlo hhi ⊢
      exact h.inv3 h1 hlo hhi

end DHRel

namespace CKAGameSt

variable {St Msg St' Msg' : Type}

theorem canSend_eq_of_t {s : CKAGameSt St Msg} {s' : CKAGameSt St' Msg'} (h : s.t = s'.t)
    (p : CKAParty) : s'.canSend p = s.canSend p := by
  simp only [canSend, h]

theorem canRecv_eq_of_t {s : CKAGameSt St Msg} {s' : CKAGameSt St' Msg'} (h : s.t = s'.t)
    (p : CKAParty) : s'.canRecv p = s.canRecv p := by
  simp only [canRecv, h]

theorem allowCorr_eq_of_t {s : CKAGameSt St Msg} {s' : CKAGameSt St' Msg'} (h : s.t = s'.t)
    (ΔFS ΔPCS t : ℕ) (p : CKAParty) : ckaAllowCorr ΔFS ΔPCS t s' p = ckaAllowCorr ΔFS ΔPCS t s p := by
  simp only [ckaAllowCorr, h]

theorem allowLeak_eq_of_t {s : CKAGameSt St Msg} {s' : CKAGameSt St' Msg'} (h : s.t = s'.t)
    (ΔPCS t : ℕ) (p : CKAParty) : ckaAllowLeak ΔPCS t s' p = ckaAllowLeak ΔPCS t s p := by
  simp only [ckaAllowLeak, canSend_eq_of_t h, h]

theorem sum_sent (s : CKAGameSt St Msg) (p : CKAParty) (x : St) (T : Msg) :
    (s.sent p x T).t .A + (s.sent p x T).t .B = s.t .A + s.t .B + 1 := by
  cases p <;> simp <;> omega

theorem le_sent (s : CKAGameSt St Msg) (p q : CKAParty) (x : St) (T : Msg) :
    s.t q ≤ (s.sent p x T).t q := by
  by_cases h : q = p
  · subst h; simp
  · simp [h]

theorem le_recvd (s : CKAGameSt St Msg) (p q : CKAParty) (x : St) :
    s.t q ≤ (s.recvd p x).t q := by
  by_cases h : q = p
  · subst h; simp
  · simp [h]

end CKAGameSt

section DHStepLemmas

variable {E Gr : Type}

/-- The steps of the Diffie–Hellman game do not decrease the counters. -/
theorem dhCKAStepOf_t_le (pow : E → Gr) (epow : Gr → E → Gr) (ΔFS ΔPCS t : ℕ) (ideal : Bool)
    (s : CKAGameSt (Gr × E) Gr) (q : CKAQuery) (e : E × Gr) (r : CKAParty) :
    s.t r ≤ (dhCKAStepOf pow epow ΔFS ΔPCS t ideal s q e).2.t r := by
  cases q with
  | send p =>
    simp only [dhCKAStepOf]; split
    · exact CKAGameSt.le_sent _ _ _ _ _
    · exact le_refl _
  | recv p =>
    simp only [dhCKAStepOf]; split
    · exact CKAGameSt.le_recvd _ _ _ _
    · exact le_refl _
  | chall p =>
    simp only [dhCKAStepOf]; split
    · exact CKAGameSt.le_sent _ _ _ _ _
    · exact le_refl _
  | corrupt p => exact le_refl _
  | sendLeak p =>
    simp only [dhCKAStepOf]; split
    · exact CKAGameSt.le_sent _ _ _ _ _
    · exact le_refl _

theorem dhDoneA_step (pow : E → Gr) (epow : Gr → E → Gr) (ΔFS ΔPCS t : ℕ) (ideal : Bool)
    (s : CKAGameSt (Gr × E) Gr) (q : CKAQuery) (e : E × Gr) (h : dhDoneA t s) :
    dhDoneA t (dhCKAStepOf pow epow ΔFS ΔPCS t ideal s q e).2 := by
  have := dhCKAStepOf_t_le pow epow ΔFS ΔPCS t ideal s q e .A
  have := dhCKAStepOf_t_le pow epow ΔFS ΔPCS t ideal s q e .B
  unfold dhDoneA at *; omega

theorem dhDoneB_step (pow : E → Gr) (epow : Gr → E → Gr) (ΔFS ΔPCS t : ℕ) (ideal : Bool)
    (s : CKAGameSt (Gr × E) Gr) (q : CKAQuery) (e : E × Gr) (h : dhDoneB t s) :
    dhDoneB t (dhCKAStepOf pow epow ΔFS ΔPCS t ideal s q e).2 := by
  have := dhCKAStepOf_t_le pow epow ΔFS ΔPCS t ideal s q e .A
  have := dhCKAStepOf_t_le pow epow ΔFS ΔPCS t ideal s q e .B
  unfold dhDoneB at *; omega

theorem dhDoneA_crit (pow : E → Gr) (epow : Gr → E → Gr) (ΔFS ΔPCS t : ℕ) (ideal : Bool)
    (s : CKAGameSt (Gr × E) Gr) (q : CKAQuery) (e : E × Gr) (h : dhCritA t s q = true) :
    dhDoneA t (dhCKAStepOf pow epow ΔFS ΔPCS t ideal s q e).2 := by
  cases q with
  | send p =>
    simp only [dhCritA, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hc, ht⟩ := h
    simp only [dhCKAStepOf, hc, if_true]
    have hs := CKAGameSt.sum_t s p
    have hAB := ((CKAGameSt.canSend_iff s p).1 hc).1
    have h1 := CKAGameSt.t_eq_of_eq hAB p
    have := CKAGameSt.sum_sent s p ((s.st p).1, e.1) (pow e.1)
    unfold dhDoneA; omega
  | _ => simp [dhCritA] at h

theorem dhDoneA_noCrit {St Msg : Type} (t : ℕ) (s : CKAGameSt St Msg) (q : CKAQuery)
    (h : dhDoneA t s) : dhCritA t s q = false := by
  cases q with
  | send p =>
    simp only [dhCritA, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
    by_cases hc : s.canSend p = true
    · right
      have hAB := ((CKAGameSt.canSend_iff s p).1 hc).1
      have h1 := CKAGameSt.t_eq_of_eq hAB p
      unfold dhDoneA at h; omega
    · left; simpa using hc
  | _ => rfl

theorem dhDoneB_noCrit {St Msg : Type} (t : ℕ) (s : CKAGameSt St Msg) (q : CKAQuery)
    (h : dhDoneB t s) : dhCritB t s q = false := by
  cases q with
  | chall p =>
    simp only [dhCritB, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
    by_cases hc : s.canSend p = true
    · right
      have hAB := ((CKAGameSt.canSend_iff s p).1 hc).1
      have h1 := CKAGameSt.t_eq_of_eq hAB p
      unfold dhDoneB at h; omega
    · left; simpa using hc
  | _ => rfl

/-- The step of the eager game: the send of epoch `t - 1` uses the exponent of `va`, the
challenge the exponent and the group element of `vb`. -/
def dhCKAEagerStepOf (pow : E → Gr) (epow : Gr → E → Gr) (ΔFS ΔPCS t : ℕ) (ideal : Bool)
    (va vb : E × Gr) : CKAGameSt (Gr × E) Gr → CKAQuery → E × Gr →
      CKAAns (Gr × E) Gr Gr E × CKAGameSt (Gr × E) Gr :=
  OracleAdv.eagerStep (OracleAdv.eagerStep (dhCKAStepOf pow epow ΔFS ΔPCS t ideal) (dhCritA t)
    va) (dhCritB t) vb

theorem dhDoneB_crit (pow : E → Gr) (epow : Gr → E → Gr) (ΔFS ΔPCS t : ℕ) (ideal : Bool)
    (va : E × Gr) (s : CKAGameSt (Gr × E) Gr) (q : CKAQuery) (e : E × Gr)
    (h : dhCritB t s q = true) :
    dhDoneB t (OracleAdv.eagerStep (dhCKAStepOf pow epow ΔFS ΔPCS t ideal) (dhCritA t) va
      s q e).2 := by
  cases q with
  | chall p =>
    simp only [dhCritB, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hc, ht⟩ := h
    simp only [OracleAdv.eagerStep, dhCritA, Bool.false_eq_true, if_false, dhCKAStepOf, hc, ht,
      beq_self_eq_true, Bool.and_self, if_true]
    have hs := CKAGameSt.sum_t s p
    have hAB := ((CKAGameSt.canSend_iff s p).1 hc).1
    have h1 := CKAGameSt.t_eq_of_eq hAB p
    have := CKAGameSt.sum_sent s p ((s.st p).1, e.1) (pow e.1)
    unfold dhDoneB; omega
  | _ => simp [dhCritB] at h

theorem dhDoneB_eager (pow : E → Gr) (epow : Gr → E → Gr) (ΔFS ΔPCS t : ℕ) (ideal : Bool)
    (va : E × Gr) (s : CKAGameSt (Gr × E) Gr) (q : CKAQuery) (e : E × Gr) (h : dhDoneB t s) :
    dhDoneB t (OracleAdv.eagerStep (dhCKAStepOf pow epow ΔFS ΔPCS t ideal) (dhCritA t) va
      s q e).2 := by
  obtain ⟨e', he⟩ := OracleAdv.eagerStep_exists (dhCKAStepOf pow epow ΔFS ΔPCS t ideal)
    (dhCritA t) va s q e
  rw [he]
  exact dhDoneB_step pow epow ΔFS ΔPCS t ideal s q e' h

end DHStepLemmas

section DHSim

variable {G : Type} [CG : CyclicGroup G]

/-- **The simulation step.** From related states, the eager game with the exponents `a = va.1`,
`b = vb.1` and the group element `vb.2`, and the simulator with the triple
`(g^a, g^b, z)`, where `z` is `vb.2` in the ideal game and `g^{ab}` in the real one, give equal
answers and related states. -/
theorem dhRel_step (t : ℕ) (ideal : Bool) (va vb : CG.Exp × G) (z : G)
    (hz : z = if ideal then vb.2 else CG.pow (CG.expMul va.1 vb.1))
    (s σ : CKAGameSt (G × CG.Exp) G) (h : DHRel va.1 t s σ) (q : CKAQuery)
    (e : CG.Exp × G) :
    (dhCKAEagerStepOf CG.pow CyclicGroup.elemPow 2 2 t ideal va vb s q e).1 =
        (dhCKASimStepOf CG.pow CyclicGroup.elemPow 2 2 t (CG.pow va.1) (CG.pow vb.1) z σ q
          e).1 ∧
      DHRel va.1 t (dhCKAEagerStepOf CG.pow CyclicGroup.elemPow 2 2 t ideal va vb s q e).2
        (dhCKASimStepOf CG.pow CyclicGroup.elemPow 2 2 t (CG.pow va.1) (CG.pow vb.1) z σ q
          e).2 := by
  have hcs := CKAGameSt.canSend_eq_of_t h.t_eq
  have hcr := CKAGameSt.canRecv_eq_of_t h.t_eq
  have hco := CKAGameSt.allowCorr_eq_of_t h.t_eq
  have hcl := CKAGameSt.allowLeak_eq_of_t h.t_eq
  have hσt : σ.t = s.t := h.t_eq.symm
  cases q with
  | send p =>
    simp only [dhCKAEagerStepOf, OracleAdv.eagerStep, dhCritA, dhCritB, Bool.false_eq_true,
      if_false, dhCKAStepOf, dhCKASimStepOf, hcs, hσt]
    rcases (Bool.eq_false_or_eq_true (s.canSend p)).symm with hc | hc
    · simp only [hc, if_false, Bool.false_eq_true]; exact ⟨by trivial, h⟩
    · simp only [hc, if_true]
      obtain ⟨hAB, hp⟩ := (CKAGameSt.canSend_iff s p).1 hc
      have htp := CKAGameSt.t_eq_of_eq hAB p
      have hto := CKAGameSt.t_other_eq_of_eq hAB p
      by_cases ht2 : s.t p + 2 = t
      · simp only [ht2, beq_self_eq_true, Bool.and_self, if_true]
        have hP : ckaSender t = p.other := by
          rw [← ht2, show s.t p + 2 = s.t .A + 1 + 1 by omega, ckaSender_succ, hp]
        have hnh : ¬ dhHidden t s p.other := by
          rintro ⟨h1, -⟩; omega
        refine ⟨?_, h.sent hc va.1 e.1 _ rfl ?_ fun _ _ _ _ => rfl⟩
        · have h1 := h.inv1 hAB
          rw [hp] at h1
          rw [h1, ← h.y_eq _ hnh, elemPow_pow_comm]
        · intro hh; exfalso; apply hh
          refine ⟨by simp; omega, ?_⟩
          rw [if_neg (by rw [hP]; exact CKAParty.ne_other p)]
          simp; omega
      · have hne : (s.t p + 2 == t) = false := by simpa using ht2
        simp only [hne, Bool.and_false, Bool.false_eq_true, if_false]
        refine ⟨by rw [h.h_eq p], h.sent hc e.1 e.1 _ rfl (fun _ => rfl) ?_⟩
        intro hpP h1 hlo hhi
        exfalso
        have hpt : s.t p + 1 = t := by omega
        have : ckaSender t = p := by rw [← hpt, htp, hp]
        rw [this] at hpP
        exact CKAParty.ne_other p hpP
  | recv p =>
    simp only [dhCKAEagerStepOf, OracleAdv.eagerStep, dhCritA, dhCritB, Bool.false_eq_true,
      if_false, dhCKAStepOf, dhCKASimStepOf, hcr]
    rcases (Bool.eq_false_or_eq_true (s.canRecv p)).symm with hc | hc
    · simp only [hc, if_false, Bool.false_eq_true]; exact ⟨by trivial, h⟩
    · simp only [hc, if_true]; exact ⟨by trivial, h.recvd hc⟩
  | chall p =>
    simp only [dhCKAEagerStepOf, OracleAdv.eagerStep, dhCritA, dhCritB, Bool.false_eq_true,
      if_false, dhCKAStepOf, dhCKASimStepOf, hcs, hσt]
    rcases (Bool.eq_false_or_eq_true (s.canSend p && s.t p + 1 == t)).symm with hcb | hcb
    · simp only [hcb, if_false, Bool.false_eq_true]; exact ⟨by trivial, h⟩
    · simp only [hcb, if_true]
      simp only [Bool.and_eq_true, beq_iff_eq] at hcb
      obtain ⟨hc, ht1⟩ := hcb
      obtain ⟨hAB, hp⟩ := (CKAGameSt.canSend_iff s p).1 hc
      have htp := CKAGameSt.t_eq_of_eq hAB p
      have hto := CKAGameSt.t_other_eq_of_eq hAB p
      have hP : ckaSender t = p := by rw [← ht1, htp, hp]
      refine ⟨?_, h.sent hc vb.1 e.1 _ rfl ?_ ?_⟩
      · rw [hz]
        cases ideal with
        | true => rfl
        | false =>
          simp only [Bool.false_eq_true, if_false]
          have h1 := h.inv1 hAB
          rw [hp] at h1
          have h3 := h.inv3 (by omega) (by rw [hP]; omega) (by rw [hP]; omega)
          rw [hP] at h3
          rw [h1, h3, CyclicGroup.elemPow_pow]
      · intro hh; exfalso; apply hh
        refine ⟨by simp; omega, ?_⟩
        rw [if_pos (by rw [hP])]
        simp; omega
      · intro hpP
        exfalso
        rw [hP] at hpP
        exact CKAParty.ne_other p hpP
  | corrupt p =>
    simp only [dhCKAEagerStepOf, OracleAdv.eagerStep, dhCritA, dhCritB, Bool.false_eq_true,
      if_false, dhCKAStepOf, dhCKASimStepOf, hco]
    rcases (Bool.eq_false_or_eq_true (ckaAllowCorr 2 2 t s p)).symm with hg | hg
    · simp only [hg, if_false, Bool.false_eq_true]; exact ⟨by trivial, h⟩
    · simp only [hg, if_true]
      refine ⟨?_, h⟩
      rw [Prod.ext (h.h_eq p) (h.y_eq p (not_dhHidden_of_allowCorr hg))]
  | sendLeak p =>
    simp only [dhCKAEagerStepOf, OracleAdv.eagerStep, dhCritA, dhCritB, Bool.false_eq_true,
      if_false, dhCKAStepOf, dhCKASimStepOf, hcl]
    rcases (Bool.eq_false_or_eq_true (ckaAllowLeak 2 t s p)).symm with hl | hl
    · simp only [hl, if_false, Bool.false_eq_true]; exact ⟨by trivial, h⟩
    · simp only [hl, if_true]
      simp only [ckaAllowLeak, Bool.and_eq_true, decide_eq_true_eq] at hl
      obtain ⟨hc, ht3⟩ := hl
      refine ⟨by rw [h.h_eq p], h.sent hc e.1 e.1 _ rfl (fun _ => rfl) ?_⟩
      intro _ _ hlo _
      omega

end DHSim

/-! ### The game of `dhCKA` as a probability mass function -/

/-- A run against an oracle whose computations are lifted distributions is the lifted run. -/
theorem OracleAdv.runSP_eq_liftPMF {S D R : Type} (O : S → D → SPComp (R × S))
    (O' : S → D → PMF (R × S)) (hO : ∀ s d, O s d = liftPMF (O' s d))
    (A : OracleAdv D R α) (s : S) :
    OracleAdv.runSP O A s = liftPMF (OracleAdv.run O' A s) := by
  induction A generalizing s with
  | ret a => exact liftPMF_pure _
  | rand p k ih =>
    simp only [OracleAdv.runSP, ih, liftPMF_bind_liftPMF, OracleAdv.run_rand]
  | query d k ih =>
    simp only [OracleAdv.runSP, hO, ih, liftPMF_bind_liftPMF, OracleAdv.run_query]

section DHGame

variable (G : Type) [CG : CyclicGroup G]

/-- The sending algorithm of `dhCKA` with its exponent as explicit randomness. -/
noncomputable instance dhCKACoins : CKACoins (dhCKA G) CG.Exp where
  sendR s x := ((s.1, x), CG.pow x, CyclicGroup.elemPow s.1 x)

/-- The explicit-randomness sending algorithm of `dhCKA` is its sending algorithm. -/
theorem dhCKACoins_sound : CKACoins.Sound (dhCKA G) := fun _ => rfl

/-- The value drawn at each query of the game of `dhCKA`: a uniform exponent and an
independent uniform group element. -/
noncomputable def dhDraw : PMF (CG.Exp × G) :=
  (PMF.uniformFintype CG.Exp).bind fun x => (PMF.uniformFintype G).map fun u => (x, u)

variable {G}

theorem dhDraw_bind {β : Type} (f : CG.Exp × G → PMF β) :
    (dhDraw G).bind f =
      (PMF.uniformFintype CG.Exp).bind fun x => (PMF.uniformFintype G).bind fun u => f (x, u) := by
  unfold dhDraw
  rw [PMF.bind_bind]
  congr 1; funext x
  rw [PMF.bind_map]; rfl

theorem dhDraw_bind_fst {β : Type} (f : CG.Exp → PMF β) :
    (dhDraw G).bind (fun v => f v.1) = (PMF.uniformFintype CG.Exp).bind f := by
  rw [dhDraw_bind]
  simp only [PMF.bind_const]

theorem dhDraw_map {β : Type} (g : CG.Exp × G → β) :
    (dhDraw G).map g = (PMF.uniformFintype CG.Exp).bind fun x =>
      (PMF.uniformFintype G).bind fun u => PMF.pure (g (x, u)) := by
  rw [← PMF.bind_pure_comp, dhDraw_bind]; rfl

/-- **The oracle of `dhCKA` in normal form.** Each oracle computation of the game of `dhCKA`
is the lifted distribution of the step `dhCKAStepOf` on a draw of `dhDraw`. -/
theorem dhCKA_oracle_eq (ΔFS ΔPCS t : ℕ) (ideal : Bool) (s : CKAGameSt (G × CG.Exp) G)
    (q : CKAQuery) :
    ckaCorruptOracle (dhCKA G) ΔFS ΔPCS t ideal s q =
      liftPMF ((dhDraw G).map (dhCKAStepOf CG.pow CyclicGroup.elemPow ΔFS ΔPCS t ideal s q)) := by
  rw [dhDraw_map]
  cases q with
  | send p =>
    simp only [ckaCorruptOracle, dhCKAStepOf]
    rcases (Bool.eq_false_or_eq_true (s.canSend p)).symm with hc | hc
    · simp only [hc, Bool.false_eq_true, if_false, PMF.bind_const, liftPMF_pure]
    · simp only [hc, if_true, dhCKA, SPComp.bind_assoc, SPComp.pure_bind, PMF.bind_const,
        sample_eq_liftPMF, liftPMF_pure, liftPMF_bind_liftPMF, PMF.bind_bind, PMF.pure_bind]
  | recv p =>
    simp only [ckaCorruptOracle, dhCKAStepOf, dhCKA]
    rcases (Bool.eq_false_or_eq_true (s.canRecv p)).symm with hc | hc
    · simp only [hc, Bool.false_eq_true, if_false, PMF.bind_const, liftPMF_pure]
    · simp only [hc, if_true, PMF.bind_const, liftPMF_pure]
  | chall p =>
    simp only [ckaCorruptOracle, dhCKAStepOf]
    rcases (Bool.eq_false_or_eq_true (s.canSend p && s.t p + 1 == t)).symm with hc | hc
    · simp only [hc, Bool.false_eq_true, if_false, PMF.bind_const, liftPMF_pure]
    · cases ideal with
      | true =>
        simp only [hc, if_true, dhCKA, SPComp.bind_assoc, SPComp.pure_bind,
          sample_eq_liftPMF, liftPMF_pure, liftPMF_bind_liftPMF, PMF.bind_bind, PMF.pure_bind]
      | false =>
        simp only [hc, if_true, Bool.false_eq_true, if_false, dhCKA, SPComp.bind_assoc,
          SPComp.pure_bind, PMF.bind_const, sample_eq_liftPMF, liftPMF_pure,
          liftPMF_bind_liftPMF, PMF.bind_bind, PMF.pure_bind]
  | corrupt p =>
    simp only [ckaCorruptOracle, dhCKAStepOf, PMF.bind_const, liftPMF_pure]
  | sendLeak p =>
    simp only [ckaCorruptOracle, dhCKAStepOf]
    rcases (Bool.eq_false_or_eq_true (ckaAllowLeak ΔPCS t s p)).symm with hc | hc
    · simp only [hc, Bool.false_eq_true, if_false, PMF.bind_const, liftPMF_pure]
    · simp only [hc, if_true, CKACoins.sendR, PMF.bind_const, sample_eq_liftPMF, liftPMF_pure,
        liftPMF_bind_liftPMF]

theorem runSP_dhCKA (ΔFS ΔPCS t : ℕ) (ideal : Bool)
    (A : OracleAdv CKAQuery (CKAAns (G × CG.Exp) G G CG.Exp) α) (s : CKAGameSt (G × CG.Exp) G) :
    OracleAdv.runSP (ckaCorruptOracle (dhCKA G) ΔFS ΔPCS t ideal) A s =
      liftPMF (OracleAdv.run (OracleAdv.nfOracle (dhDraw G)
        (dhCKAStepOf CG.pow CyclicGroup.elemPow ΔFS ΔPCS t ideal)) A s) :=
  OracleAdv.runSP_eq_liftPMF _ _ (dhCKA_oracle_eq ΔFS ΔPCS t ideal) A s

/-- The distribution of the output of the game of `dhCKA` with the challenge epoch `t`. -/
noncomputable def dhCKAGamePMF (ΔFS ΔPCS t : ℕ) (ideal : Bool)
    (play : G → OracleAdv CKAQuery (CKAAns (G × CG.Exp) G G CG.Exp) α) : PMF α :=
  (PMF.uniformFintype CG.Exp).bind fun x₀ =>
    (OracleAdv.run (OracleAdv.nfOracle (dhDraw G)
      (dhCKAStepOf CG.pow CyclicGroup.elemPow ΔFS ΔPCS t ideal)) (play (CG.pow x₀))
      (CKAGameSt.init (CG.pow x₀) (CG.pow x₀, x₀) (CG.pow x₀, x₀))).map Prod.fst

/-- The corruption game of `dhCKA` is the lifted distribution `dhCKAGamePMF` after the choice
of the challenge epoch. -/
theorem dhCKA_game_eq (ΔFS ΔPCS : ℕ) (ideal : Bool)
    (A : CKACorruptAdv (G × CG.Exp) G G CG.Exp α) :
    cka_corrupt_game (dhCKA G) ΔFS ΔPCS ideal A =
      liftPMF (A.tStar.bind fun t => dhCKAGamePMF ΔFS ΔPCS t ideal (A.play t)) := by
  unfold cka_corrupt_game dhCKAGamePMF
  simp only [runSP_dhCKA]
  simp only [dhCKA, SPComp.bind_assoc, SPComp.pure_bind, sample_eq_liftPMF, liftPMF_bind_pure,
    liftPMF_bind_liftPMF, PMF.bind_map]
  rfl

end DHGame

/-! ### The reduction -/

section DHRed

variable {E Gr : Type} [Fintype E] [Nonempty E] [Fintype Gr] [Nonempty Gr]

/-- The simulator answers a query by drawing an exponent and a group element and running the
simulation step. -/
noncomputable def ckaCorruptSimImplOf (pow : E → Gr) (epow : Gr → E → Gr) (ΔFS ΔPCS t : ℕ)
    (ga gb z : Gr) (σ : CKAGameSt (Gr × E) Gr) (q : CKAQuery) :
    OracleAdv Empty Unit (CKAAns (Gr × E) Gr Gr E × CKAGameSt (Gr × E) Gr) :=
  .rand (PMF.uniformFintype E) fun x =>
    .rand (PMF.uniformFintype Gr) fun u =>
      .ret (dhCKASimStepOf pow epow ΔFS ΔPCS t ga gb z σ q (x, u))

/-- **The DDH reduction** as an oracle tree without queries. On the triple `(ga, gb, z)` it
draws the challenge epoch `t` of the adversary and an exponent `x₀`; the public value of the
initialisation is `ga` if `t = 1` and `g^{x₀}` otherwise; it runs the adversary against the
simulator `ckaCorruptSimImplOf` and returns its output. -/
noncomputable def ckaCorruptDDHTreeOf (pow : E → Gr) (epow : Gr → E → Gr) (ΔFS ΔPCS : ℕ)
    (tStar : PMF ℕ) (play : ℕ → Gr → OracleAdv CKAQuery (CKAAns (Gr × E) Gr Gr E) Bool)
    (ga gb z : Gr) : OracleAdv Empty Unit Bool :=
  .rand tStar fun t =>
    .rand (PMF.uniformFintype E) fun x₀ =>
      (OracleAdv.simulate (ckaCorruptSimImplOf pow epow ΔFS ΔPCS t ga gb z)
        (play t (if t = 1 then ga else pow x₀))
        (CKAGameSt.init (if t = 1 then ga else pow x₀) (if t = 1 then ga else pow x₀, x₀)
          (if t = 1 then ga else pow x₀, x₀))).bind fun r => .ret r.1

end DHRed

/-! ### The costed reduction -/

derive_timed ckaCorruptDDHTreeOf

/-- The bound of the simulator's cost companions after `i` queries: every state companion is
at most `1 + 3 i`, every counter companion at most `3 i` (each update of a party's state or
counter adds one closure layer of cost at most `3`). -/
def ckaSimCostInv {St Msg : Type} (i : ℕ) (ŝ : ((CKAParty → St) × (CKAParty → ℕ)) ×
    ((CKAParty → ℕ) × (CKAParty → ℕ)) × Msg) : Prop :=
  (∀ p, ŝ.1.2 p ≤ 1 + 3 * i) ∧ ∀ p, ŝ.2.1.2 p ≤ 3 * i

/-- The time of the `i`-th simulated query, with exponentiations of costs at most `P` and `X`:
the closure layers of the state cost linearly in `i`. -/
def ckaSimQueryTime (P X i : ℕ) : ℕ := 2 * P + X + 21 * i + 50

section DHTime

variable {E Gr : Type} [Fintype E] [Nonempty E] [Fintype Gr] [Nonempty Gr]

/-- **Time of a simulated query.** From a costed state within the bound `ckaSimCostInv i`, the
costed simulator answers in time at most `ckaSimQueryTime P X i` and returns a costed state
within the bound `ckaSimCostInv (i + 1)`. -/
theorem ckaCorruptSimImplOf.timed_bound (pow : E → Gr) (powCost : E → ℕ) (epow : Gr → E → Gr)
    (epowCost : Gr → E → ℕ) (ΔFS ΔPCS t : ℕ) (ga gb z : Gr) {P X : ℕ}
    (hP : ∀ x, powCost x ≤ P) (hX : ∀ g x, epowCost g x ≤ X) (i : ℕ)
    (σ : CKAGameSt (Gr × E) Gr) (q : CKAQuery) (stCost tCost : CKAParty → ℕ)
    (hS : ∀ p, stCost p ≤ 1 + 3 * i) (hT : ∀ p, tCost p ≤ 3 * i) :
    OracleAdv.Timed.StepTimeBound
        (OracleAdv.Timed.delay 1 (ckaCorruptSimImplOf.timed pow powCost epow epowCost ΔFS ΔPCS t
          ga gb z σ q stCost tCost)) (ckaSimQueryTime P X i) ∧
      OracleAdv.Timed.AllRet (fun y => ckaSimCostInv (i + 1) y.2)
        (ckaCorruptSimImplOf.timed pow powCost epow epowCost ΔFS ΔPCS t ga gb z σ q stCost
          tCost).2 := by
  refine ⟨?_, ?_⟩
  · unfold ckaSimQueryTime
    refine ⟨by simp [OracleAdv.Timed.delay, ckaCorruptSimImplOf.timed], ?_⟩
    simp only [OracleAdv.Timed.delay, ckaCorruptSimImplOf.timed, Nat.add_zero]
    refine ⟨by omega, fun x => ⟨Nat.zero_le _, by dsimp only; omega, fun u => ⟨?_, trivial⟩⟩⟩
    have := hP x
    cases q with
    | send p =>
      have := hS p; have := hS p.other; have := hT p; have := hT .A; have := hT .B
      have := hX ga (σ.st p.other).2; have := hX (σ.st p).1 x
      dsimp only
      split
      · split <;> omega
      · omega
    | recv p =>
      have := hS p; have := hT p; have := hT p.other
      dsimp only
      split <;> omega
    | chall p =>
      have := hS p; have := hT p; have := hT .A; have := hT .B
      dsimp only
      split <;> omega
    | corrupt p =>
      have := hS p; have := hT p; have := hT .A; have := hT .B
      dsimp only
      split <;> omega
    | sendLeak p =>
      have := hS p; have := hT p; have := hT .A; have := hT .B; have := hX (σ.st p).1 x
      dsimp only
      split <;> omega
  · intro x u
    have hS' : ∀ p, stCost p ≤ 1 + 3 * (i + 1) := fun p => by have := hS p; omega
    have hT' : ∀ p, tCost p ≤ 3 * (i + 1) := fun p => by have := hT p; omega
    have hU : ∀ p : CKAParty, (fun a => 2 + if a = p then 0 else 1 + stCost a) =
        (fun a => 2 + if a = p then 0 else 1 + stCost a) := fun _ => rfl
    have hSu : ∀ p a, (2 + if _ : a = p then 0 else 1 + stCost a) ≤ 1 + 3 * (i + 1) :=
      fun p a => by have := hS a; split <;> omega
    have hTu : ∀ p a, (2 + if _ : a = p then 0 else 1 + tCost a) ≤ 3 * (i + 1) :=
      fun p a => by have := hT a; split <;> omega
    cases q with
    | send p =>
      dsimp only [OracleAdv.Timed.AllRet]
      split
      · split
        · exact ⟨hSu p, hTu p⟩
        · exact ⟨hSu p, hTu p⟩
      · exact ⟨hS', hT'⟩
    | recv p =>
      dsimp only [OracleAdv.Timed.AllRet]
      split
      · exact ⟨hSu p, hTu p⟩
      · exact ⟨hS', hT'⟩
    | chall p =>
      dsimp only [OracleAdv.Timed.AllRet]
      split
      · exact ⟨hSu p, hTu p⟩
      · exact ⟨hS', hT'⟩
    | corrupt p => exact ⟨hS', hT'⟩
    | sendLeak p =>
      dsimp only [OracleAdv.Timed.AllRet]
      split
      · exact ⟨hSu p, hTu p⟩
      · exact ⟨hS', hT'⟩

/-- The time of a tree that draws `t` from `τ` and `x₀` from `μ` at the step cost `c t x₀`, and
then runs a step-prefixed tree `S t x₀` of time at most `B` and returns the first component of
its output. -/
theorem timeBound_rand_rand_bind {D R Ŝ : Type} (τ : PMF ℕ) (μ : PMF E) (c : ℕ → E → ℕ)
    (S : ℕ → E → ℕ × OracleAdv.Timed D R (Bool × Ŝ)) {K B : ℕ} (hc : ∀ t x₀, c t x₀ ≤ K)
    (hS : ∀ t x₀, OracleAdv.Timed.StepTimeBound (S t x₀) B) :
    OracleAdv.Timed.StepTimeBound (0, OracleAdv.Timed.rand τ (fun _ => 0) fun t =>
      OracleAdv.Timed.rand μ (fun x₀ => c t x₀ + (S t x₀).1 +
        ((S t x₀).2.bind fun r => (0, OracleAdv.Timed.ret r.1)).1)
        fun x₀ => ((S t x₀).2.bind fun r => (0, OracleAdv.Timed.ret r.1)).2) (K + B + 2) := by
  refine ⟨Nat.zero_le _, by dsimp only; omega, fun t => ⟨Nat.zero_le _, by dsimp only; omega,
    fun x₀ => ?_⟩⟩
  obtain ⟨h1, h2⟩ := hS t x₀
  obtain ⟨h3, h4⟩ := OracleAdv.Timed.timeBound_bind (n := 0) h2
    (f := fun r => (0, OracleAdv.Timed.ret r.1)) fun _ => ⟨le_refl _, trivial⟩
  have := hc t x₀
  refine ⟨by dsimp only; omega, h4.mono ?_⟩
  dsimp only; omega

end DHTime

/-- **Time of the DDH reduction.** For an adversary whose costed trees have time at most `T`,
at most `q` queries and call cost at most `a`, and exponentiations of costs at most `P` (of the
generator) and `X` (of a group element), the costed reduction tree has time at most
`T + ∑_{j < q} (2 P + X + 21 j + 50) + a + 4 P + 12`: the adversary, one simulated query per
query, whose cost grows with the closure layers of the simulator state, and the choice of the
initial exponent. -/
theorem ckaCorruptDDHTreeOf.timeBound_timed {E Gr : Type} [Fintype E] [Nonempty E] [Fintype Gr]
    [Nonempty Gr] (pow : E → Gr) (powCost : E → ℕ) (epow : Gr → E → Gr)
    (epowCost : Gr → E → ℕ) (ΔFS ΔPCS : ℕ) (tStar : PMF ℕ)
    (play : ℕ → Gr → OracleAdv.Timed CKAQuery (CKAAns (Gr × E) Gr Gr E) Bool)
    (playCost : ℕ → Gr → ℕ) (ga gb z : Gr) {T q a P X : ℕ}
    (hA : ∀ t g, (play t g).TimeBound T) (hq : ∀ t g, (play t g).erase.IsQueryBound q)
    (ha : ∀ t g, playCost t g ≤ a) (hP : ∀ x, powCost x ≤ P) (hX : ∀ g x, epowCost g x ≤ X) :
    OracleAdv.Timed.StepTimeBound
      (ckaCorruptDDHTreeOf.timed pow powCost epow epowCost ΔFS ΔPCS tStar play playCost ga gb z)
      (T + ∑ j ∈ Finset.range q, ckaSimQueryTime P X j + a + 4 * P + 12) := by
  unfold ckaCorruptDDHTreeOf.timed
  refine (timeBound_rand_rand_bind (K := 10 + a + 4 * P)
    (B := T + ∑ j ∈ Finset.range q, ckaSimQueryTime P X j) _ _ _ _ ?_ ?_).mono (by omega)
  · intro t x₀
    have := ha t ga
    have := ha t (pow x₀)
    have := hP x₀
    split <;> omega
  · intro t x₀
    refine (OracleAdv.Timed.timeBound_simulateHat_inv _ _ _ ckaSimCostInv
      (ckaSimQueryTime P X)
      (fun i ŝ d h => by
        exact ckaCorruptSimImplOf.timed_bound pow powCost epow epowCost ΔFS ΔPCS t ga gb z
          hP hX i _ d _ _ h.1 h.2) (hA t (if t = 1 then ga else pow x₀))
      (hq t (if t = 1 then ga else pow x₀)) 0 _ ?_).mono ?_
    · exact ⟨fun p => le_refl _, fun p => Nat.zero_le _⟩
    · simp only [Nat.zero_add, le_refl]

/-- The oracle of a tree without queries. -/
def emptyOracle (_ : Unit) (d : Empty) : PMF (Unit × Unit) := d.elim

/-- **The DDH reduction** `ckaCorruptDDHRed A`: the tree `ckaCorruptDDHTreeOf` with the
exponentiations of the group, run as a distribution. -/
noncomputable def ckaCorruptDDHRed {G : Type} [CG : CyclicGroup G]
    (A : CKACorruptAdv (G × CG.Exp) G G CG.Exp Bool) : G × G × G → SPComp Bool := fun tr =>
  liftPMF ((OracleAdv.run emptyOracle (ckaCorruptDDHTreeOf CG.pow CyclicGroup.elemPow 2 2
    A.tStar A.play tr.1 tr.2.1 tr.2.2) ()).map Prod.fst)

section DHProof

variable {G : Type} [CG : CyclicGroup G]

theorem dhCritA_one {St Msg : Type} (s : CKAGameSt St Msg) (q : CKAQuery) :
    dhCritA 1 s q = false := by
  cases q <;> simp [dhCritA]

/-- The two eager hops: the exponent of the send of epoch `t - 1` and the exponent and the
group element of the challenge are drawn in advance. -/
theorem run_dhCKAStep_eager (t : ℕ) (ideal : Bool)
    (A : OracleAdv CKAQuery (CKAAns (G × CG.Exp) G G CG.Exp) α) (s : CKAGameSt (G × CG.Exp) G) :
    OracleAdv.run (OracleAdv.nfOracle (dhDraw G)
        (dhCKAStepOf CG.pow CyclicGroup.elemPow 2 2 t ideal)) A s =
      (dhDraw G).bind fun va => (dhDraw G).bind fun vb =>
        OracleAdv.run (OracleAdv.nfOracle (dhDraw G)
          (dhCKAEagerStepOf CG.pow CyclicGroup.elemPow 2 2 t ideal va vb)) A s := by
  rw [OracleAdv.run_nf_eq_eager (dhDraw G) _ (dhCritA t) (dhDoneA t)
    (dhDoneA_crit _ _ _ _ _ _) (dhDoneA_step _ _ _ _ _ _) (dhDoneA_noCrit t)]
  congr 1; funext va
  exact OracleAdv.run_nf_eq_eager (dhDraw G) _ (dhCritB t) (dhDoneB t)
    (dhDoneB_crit _ _ _ _ _ _ va) (dhDoneB_eager _ _ _ _ _ _ va) (dhDoneB_noCrit t) A s

/-- The initial exponent of the eager game: the exponent `a` of the DDH triple at the
challenge epoch `1`, a fresh exponent otherwise. -/
def dhX0 {X : Type} (t : ℕ) (a x₀ : X) : X := if t = 1 then a else x₀

/-- The game of `dhCKA` as the eager game, with the initial exponent `dhX0 t va.1 x₀`. -/
theorem dhCKAGamePMF_eager (t : ℕ) (ideal : Bool)
    (play : G → OracleAdv CKAQuery (CKAAns (G × CG.Exp) G G CG.Exp) α) :
    dhCKAGamePMF 2 2 t ideal play =
      (PMF.uniformFintype CG.Exp).bind fun x₀ => (dhDraw G).bind fun va => (dhDraw G).bind fun vb =>
        (OracleAdv.run (OracleAdv.nfOracle (dhDraw G)
          (dhCKAEagerStepOf CG.pow CyclicGroup.elemPow 2 2 t ideal va vb))
          (play (CG.pow (dhX0 t va.1 x₀)))
          (CKAGameSt.init (CG.pow (dhX0 t va.1 x₀)) (CG.pow (dhX0 t va.1 x₀), dhX0 t va.1 x₀)
            (CG.pow (dhX0 t va.1 x₀), dhX0 t va.1 x₀))).map Prod.fst := by
  unfold dhCKAGamePMF
  by_cases ht : t = 1
  · subst ht
    have hA : ∀ va : CG.Exp × G,
        OracleAdv.eagerStep (dhCKAStepOf CG.pow CyclicGroup.elemPow 2 2 1 ideal) (dhCritA 1) va =
          dhCKAStepOf CG.pow CyclicGroup.elemPow 2 2 1 ideal := by
      intro va; funext s q e
      simp only [OracleAdv.eagerStep, dhCritA_one, Bool.false_eq_true, if_false]
    simp only [dhCKAEagerStepOf, hA, dhX0, if_true, PMF.bind_const]
    rw [dhDraw_bind]
    simp only [PMF.bind_const]
    congr 1; funext x₀
    rw [OracleAdv.run_nf_eq_eager (dhDraw G) _ (dhCritB 1) (dhDoneB 1)
      (fun s q e h => by
        have := dhDoneB_crit CG.pow CyclicGroup.elemPow 2 2 1 ideal (Classical.arbitrary _) s q e h
        rwa [hA] at this)
      (dhDoneB_step _ _ _ _ _ _) (dhDoneB_noCrit 1), PMF.map_bind]
  · simp only [dhX0, ht, if_false, run_dhCKAStep_eager, PMF.map_bind]

/-- The initial states of the eager game and of the simulator are related. -/
theorem dhRel_init (t : ℕ) (a x₀ : CG.Exp) :
    DHRel a t (CKAGameSt.init (CG.pow (dhX0 t a x₀)) (CG.pow (dhX0 t a x₀), dhX0 t a x₀)
        (CG.pow (dhX0 t a x₀), dhX0 t a x₀))
      (CKAGameSt.init (CG.pow (dhX0 t a x₀)) (CG.pow (dhX0 t a x₀), x₀)
        (CG.pow (dhX0 t a x₀), x₀)) := by
  refine ⟨rfl, rfl, fun p => by cases p <;> rfl, ?_, Or.inl rfl, fun _ => rfl, ?_, ?_⟩
  · intro p hp
    by_cases ht : t = 1
    · exfalso; apply hp
      subst ht
      refine ⟨by simp [CKAGameSt.init], ?_⟩
      split <;> simp [CKAGameSt.init]
    · cases p <;> simp [CKAGameSt.init, dhX0, ht]
  · intro p hp
    cases p <;> simp [CKAGameSt.init] at hp
  · intro h1 hlo _
    have ht : t = 1 := by
      have : (CKAGameSt.init (CG.pow (dhX0 t a x₀)) (CG.pow (dhX0 t a x₀), dhX0 t a x₀)
          (CG.pow (dhX0 t a x₀), dhX0 t a x₀) : CKAGameSt (G × CG.Exp) G).t
          (ckaSender t).other = 0 := rfl
      omega
    subst ht
    rfl

/-- **The eager game is the simulation.** -/
theorem dhCKA_eager_eq_sim (t : ℕ) (ideal : Bool) (va vb : CG.Exp × G) (x₀ : CG.Exp)
    (play : G → OracleAdv CKAQuery (CKAAns (G × CG.Exp) G G CG.Exp) α) :
    (OracleAdv.run (OracleAdv.nfOracle (dhDraw G)
        (dhCKAEagerStepOf CG.pow CyclicGroup.elemPow 2 2 t ideal va vb))
        (play (CG.pow (dhX0 t va.1 x₀)))
        (CKAGameSt.init (CG.pow (dhX0 t va.1 x₀)) (CG.pow (dhX0 t va.1 x₀), dhX0 t va.1 x₀)
          (CG.pow (dhX0 t va.1 x₀), dhX0 t va.1 x₀))).map Prod.fst =
      (OracleAdv.run (OracleAdv.nfOracle (dhDraw G)
        (dhCKASimStepOf CG.pow CyclicGroup.elemPow 2 2 t (CG.pow va.1) (CG.pow vb.1)
          (if ideal then vb.2 else CG.pow (CG.expMul va.1 vb.1))))
        (play (CG.pow (dhX0 t va.1 x₀)))
        (CKAGameSt.init (CG.pow (dhX0 t va.1 x₀)) (CG.pow (dhX0 t va.1 x₀), x₀)
          (CG.pow (dhX0 t va.1 x₀), x₀))).map Prod.fst :=
  OracleAdv.run_nf_map_fst_eq_of_rel (dhDraw G) _ _ (DHRel va.1 t)
    (fun s σ h q e => dhRel_step t ideal va vb _ rfl s σ h q e) _ _ _ (dhRel_init t va.1 x₀)

/-- The run of the reduction tree is the run of the adversary against the simulation step. -/
theorem ckaCorruptDDHTreeOf_run (ΔFS ΔPCS : ℕ) (tStar : PMF ℕ)
    (play : ℕ → G → OracleAdv CKAQuery (CKAAns (G × CG.Exp) G G CG.Exp) Bool) (ga gb z : G) :
    (OracleAdv.run emptyOracle (ckaCorruptDDHTreeOf CG.pow CyclicGroup.elemPow ΔFS ΔPCS tStar
        play ga gb z) ()).map Prod.fst =
      tStar.bind fun t => (PMF.uniformFintype CG.Exp).bind fun x₀ =>
        (OracleAdv.run (OracleAdv.nfOracle (dhDraw G)
          (dhCKASimStepOf CG.pow CyclicGroup.elemPow ΔFS ΔPCS t ga gb z))
          (play t (if t = 1 then ga else CG.pow x₀))
          (CKAGameSt.init (if t = 1 then ga else CG.pow x₀) (if t = 1 then ga else CG.pow x₀, x₀)
            (if t = 1 then ga else CG.pow x₀, x₀))).map Prod.fst := by
  unfold ckaCorruptDDHTreeOf
  simp only [OracleAdv.run_rand, PMF.map_bind]
  congr 1; funext t; congr 1; funext x₀
  rw [OracleAdv.run_simulate_fst]
  have hsim : OracleAdv.simOracle (ckaCorruptSimImplOf CG.pow CyclicGroup.elemPow ΔFS ΔPCS t ga
      gb z) emptyOracle = OracleAdv.nfOracle (dhDraw G) (fun σu q e =>
        ((dhCKASimStepOf CG.pow CyclicGroup.elemPow ΔFS ΔPCS t ga gb z σu.1 q e).1,
          ((dhCKASimStepOf CG.pow CyclicGroup.elemPow ΔFS ΔPCS t ga gb z σu.1 q e).2, ()))) := by
    funext σu q
    simp only [OracleAdv.simOracle, ckaCorruptSimImplOf, OracleAdv.run_rand, OracleAdv.run_ret,
      OracleAdv.nfOracle, dhDraw_map, PMF.map_bind, PMF.pure_map]
  rw [hsim]
  exact OracleAdv.run_nf_map_fst_eq_of_rel (dhDraw G) _ _ (fun σu σ => σu.1 = σ)
    (fun σu σ h q e => by subst h; exact ⟨rfl, rfl⟩) _ _ _ rfl

theorem DDH_real_eq_liftPMF :
    DDH_real G = liftPMF ((PMF.uniformFintype CG.Exp).bind fun a =>
      (PMF.uniformFintype CG.Exp).bind fun b =>
        PMF.pure (CG.pow a, CG.pow b, CG.pow (CG.expMul a b))) := by
  simp only [DDH_real, SPComp.monad_bind_eq, SPComp.monad_pure_eq, sample_eq_liftPMF,
    liftPMF_pure, liftPMF_bind_liftPMF]

theorem DDH_ideal_eq_liftPMF :
    DDH_ideal G = liftPMF ((PMF.uniformFintype CG.Exp).bind fun a =>
      (PMF.uniformFintype CG.Exp).bind fun b => (PMF.uniformFintype CG.Exp).bind fun c =>
        PMF.pure (CG.pow a, CG.pow b, CG.pow c)) := by
  simp only [DDH_ideal, SPComp.monad_bind_eq, SPComp.monad_pure_eq, sample_eq_liftPMF,
    liftPMF_pure, liftPMF_bind_liftPMF]

/-- A uniform exponent raised as a power of the generator is a uniform group element. -/
theorem bind_uniform_pow {β : Type} (K : G → PMF β) :
    (PMF.uniformFintype CG.Exp).bind (fun c => K (CG.pow c)) = (PMF.uniformFintype G).bind K := by
  rw [← PMF.uniformFintype_map_equiv (Equiv.ofBijective CG.pow CG.pow_bij), PMF.bind_map]
  rfl

theorem pow_dhX0 (t : ℕ) (a x₀ : CG.Exp) :
    CG.pow (dhX0 t a x₀) = if t = 1 then CG.pow a else CG.pow x₀ := by
  unfold dhX0; split <;> rfl

/-- Reordering of four draws. -/
theorem bind_reorder {X β : Type} (μ : PMF X) (τ : PMF ℕ) (F : ℕ → X → X → X → PMF β) :
    (μ.bind fun a => μ.bind fun b => τ.bind fun t => μ.bind fun x₀ => F t x₀ a b) =
      τ.bind fun t => μ.bind fun x₀ => μ.bind fun a => μ.bind fun b => F t x₀ a b := by
  have h1 : ∀ a, (μ.bind fun b => τ.bind fun t => μ.bind fun x₀ => F t x₀ a b) =
      τ.bind fun t => μ.bind fun x₀ => μ.bind fun b => F t x₀ a b := by
    intro a
    rw [PMF.bind_comm μ τ]
    congr 1; funext t
    exact PMF.bind_comm _ _ _
  simp only [h1]
  rw [PMF.bind_comm μ τ]
  congr 1; funext t
  rw [PMF.bind_comm μ μ]

/-- Reordering of the draws of the ideal games. -/
theorem bind_reorder_ideal {β : Type} (τ : PMF ℕ) (F : ℕ → CG.Exp → CG.Exp → CG.Exp → G → PMF β) :
    (τ.bind fun t => (PMF.uniformFintype CG.Exp).bind fun x₀ =>
      (PMF.uniformFintype CG.Exp).bind fun a => (PMF.uniformFintype CG.Exp).bind fun b =>
        (PMF.uniformFintype G).bind fun u => F t x₀ a b u) =
      (PMF.uniformFintype CG.Exp).bind fun a => (PMF.uniformFintype CG.Exp).bind fun b =>
        (PMF.uniformFintype CG.Exp).bind fun c => τ.bind fun t =>
          (PMF.uniformFintype CG.Exp).bind fun x₀ => F t x₀ a b (CG.pow c) := by
  have h : ∀ a b, ((PMF.uniformFintype CG.Exp).bind fun c => τ.bind fun t =>
      (PMF.uniformFintype CG.Exp).bind fun x₀ => F t x₀ a b (CG.pow c)) =
      τ.bind fun t => (PMF.uniformFintype CG.Exp).bind fun x₀ =>
        (PMF.uniformFintype G).bind fun u => F t x₀ a b u := by
    intro a b
    rw [PMF.bind_comm (PMF.uniformFintype CG.Exp) τ]
    congr 1; funext t
    rw [PMF.bind_comm (PMF.uniformFintype CG.Exp) (PMF.uniformFintype CG.Exp)]
    congr 1; funext x₀
    exact bind_uniform_pow _
  simp only [h]
  exact (bind_reorder _ _ _).symm

/-- **CKA security of `dhCKA` with state corruption and randomness leakage.** For every
adversary `A`, the corruption advantage of `dhCKA` with forward-secrecy delay `2` and
post-compromise delay `2` equals the DDH advantage of the reduction `ckaCorruptDDHRed A`. -/
theorem dhCKA_corrupt_advantage_eq_ddh (A : CKACorruptAdv (G × CG.Exp) G G CG.Exp Bool) :
    CKA_Corrupt_Advantage (dhCKA G) 2 2 A = DDH_Advantage G (ckaCorruptDDHRed A) := by
  unfold CKA_Corrupt_Advantage DDH_Advantage AdvantageA cka_corrupt_real cka_corrupt_ideal
  rw [dhCKA_game_eq, dhCKA_game_eq, DDH_real_eq_liftPMF, DDH_ideal_eq_liftPMF]
  simp only [dhCKAGamePMF_eager]
  simp only [dhCKA_eager_eq_sim]
  unfold ckaCorruptDDHRed
  simp only [liftPMF_bind_liftPMF, PMF.bind_bind, PMF.pure_bind,
    ckaCorruptDDHTreeOf_run, pow_dhX0, dhDraw_bind, PMF.bind_const, Bool.false_eq_true, if_false,
    if_true]
  congr 2
  · exact (bind_reorder _ _ _).symm
  · exact bind_reorder_ideal _ _

end DHProof

end CatCrypt.Crypto.Messaging
