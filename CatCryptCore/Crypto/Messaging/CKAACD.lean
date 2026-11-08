/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.CKACorrupt
import CatCryptCore.Tactics.DeriveTimed

/-!
# The Diffie–Hellman CKA of Alwen, Coretti and Dodis

The continuous key agreement of Alwen, Coretti and Dodis (§4.1) over a cyclic group. A party
state alternates between two forms: the next sender holds the public value `h = g^y` of its
peer, the next receiver holds its own exponent `x`. Sending from `h` samples `x`, sends
`g^x` with the key `h^x` and keeps `x`; receiving `T` with `x` derives `T^x` and keeps `T`,
so that the own exponent is erased by the receive. The scheme `dhCKA` of
`CatCryptCore.Crypto.Messaging.CKA` keeps the own exponent next to the peer's public value
until the next send, and has forward-secrecy delay `2`.

## Security

In the corruption game of `CatCryptCore.Crypto.Messaging.CKACorrupt` with forward-secrecy
delay `1` and post-compromise delay `2`, the advantage of every adversary `A` equals the DDH
advantage of the reduction `acdDDHRed A` (`acdCKA_corrupt_advantage_eq_ddh`). The reduction
draws the challenge epoch `t` from the adversary's distribution, embeds `g^a` as the message of
epoch `t - 1` and `(g^b, z)` as the challenge message and key, and answers every other query
honestly. The proof follows that of `dhCKA_corrupt_advantage_eq_ddh`: the oracle is in normal
form (`acdCKA_oracle_eq`), two eager hops draw the exponent of epoch `t - 1` and the challenge
exponent and key in advance (`OracleAdv.run_nf_eq_eager`), and the eager game and the
simulator give equal outputs under the simulation relation `ACDRel` (`acdRel_step`,
`OracleAdv.run_nf_map_fst_eq_of_rel`). The exponents unknown to the simulator are held only in
short windows (`acdHidden`): `b` by the challenged party `ckaSender t` at counter `t`, until it
receives the message of epoch `t + 1`, and `a` by its peer at counter `t - 1`, until it receives
the challenge message. The gates with `ΔFS = 1`, `ΔPCS = 2` refuse every corruption in these
windows (`not_acdHidden_of_allowCorr`), and the leakage gate refuses the sends of the epochs
`t - 1` and `t`.

Both delays are tight for `acdCKA`: with `ΔFS = 0` the challenged party may be corrupted at
counter `t` and reveals `b`, from which the challenge key is `(g^a)^b`; with `ΔPCS = 1` its
peer may be corrupted after the send of epoch `t - 1` and reveals `a`, and the send of epoch
`t - 1` may leak `a`. In both cases the adversary computes the real key from the transcript
and distinguishes with advantage `1 - 1/|G|`.

The passive game of `CatCryptCore.Crypto.Messaging.CKA` is the corruption game of
`ckaPassiveAdv k m`, so the passive CKA advantage of `acdCKA` is a DDH advantage
(`acdCKA_advantage_eq_ddh`).

## Comparison with the formalisation of the Beneficial AI Foundation

The theorem `ddhCKA.security` of `SecureMessaging/CKA/FromDDH/Security.lean`
(github.com/Beneficial-AI-Foundation/secure-messaging, commit `08ae2d4`) states, for the same
alternating scheme over a module `G` over a finite field `F` with a generator whose scalar
multiplication is bijective, and for game parameters with `ΔFS = 1` and `ΔPCS = 2`,
`|Pr[b' = b] - 1/2| ≤ ddhAdvantage ℬ / 2`. In a bit-guessing game
`|Pr[b' = b] - 1/2|` is half the distance between the games with the real and with the
uniform key, so the two statements bound the same quantity by the same DDH advantage. The
differences:

* the bound here is an equality, `CKA_Corrupt_Advantage (acdCKA G) 1 2 A =
  DDH_Advantage G (acdDDHRed A)`, of which `acdCKA_corrupt_advantage_le` is the inequality;
* the challenge epoch and the challenged party are game parameters fixed before the game in
  the BAIF statement; here the adversary draws the challenge epoch from its own distribution
  before the initialisation and the challenged party is the sender of that epoch, and the
  reduction draws the epoch from the same distribution, without a guess;
* the group is a `CyclicGroup` with an exponent type here, an `F`-module there;
* the reduction here is costed: `derive_timed` derives `acdDDHTreeOf.timed` and its erasure
  theorem, and `acdDDHTreeOf.timeBound_timed` bounds its time by the time of the adversary plus
  a sum over its queries of the cost `acdSimQueryTime` of a simulated query; the BAIF
  efficiency statement `time(ℬ) = time(𝒜) + O(q_𝒜)` is informal.

## Main definitions

* `acdCKA`, `acdCKACoins` — the scheme and its sending algorithm with explicit randomness
* `acdStepOf`, `acdEagerStepOf`, `acdSimStepOf` — the steps of the oracle, of the eager game and
  of the simulator
* `acdHidden`, `ACDRel` — the hidden windows and the simulation relation
* `acdSimImplOf`, `acdDDHTreeOf`, `acdDDHRed`, `acdDDHRedA` — the DDH reduction

## Main results

* `acdCKACoins_sound`, `acdCKA_recv` — soundness of the explicit randomness, correctness
* `acdRel_step` — the simulation step
* `acdCKA_corrupt_advantage_eq_ddh`, `acdCKA_corrupt_advantageA_eq_ddh`,
  `acdCKA_corrupt_advantage_le` — the corruption advantage with `ΔFS = 1`, `ΔPCS = 2` is the DDH
  advantage of the reduction
* `acdCKA_advantage_eq_ddh` — the passive CKA advantage as a DDH advantage
* `acdDDHTreeOf.erase_timed`, `acdDDHTreeOf.timeBound_timed` — the costed reduction and its
  time

## References

* J. Alwen, S. Coretti, Y. Dodis, *The Double Ratchet: Security Notions, Proofs, and
  Modularization for the Signal Protocol*, EUROCRYPT 2019, §4.1 and Theorem 3
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCryptCore.Examples.CyclicGroupDDH
open scoped ENNReal

/-! ## The scheme -/

section Scheme

variable {E Gr : Type}

/-- The public value of a party state: the stored group element `h` of a state `inl h`, and
`pow x` for a state `inr x`, which a party in the alternation never sends from. -/
def acdPubOf (pow : E → Gr) : Gr ⊕ E → Gr
  | .inl h => h
  | .inr x => pow x

/-- The exponent of a party state: the stored exponent `x` of a state `inr x`, and the default
`d` for a state `inl h`, which a party in the alternation never receives in. -/
def acdExpOr (d : E) : Gr ⊕ E → E
  | .inl _ => d
  | .inr x => x

end Scheme

section ACD

variable (G : Type) [CG : CyclicGroup G]

/-- **The Diffie–Hellman CKA of Alwen, Coretti and Dodis** (§4.1). A party state is either the
public value `inl h` of the peer, held by the next sender, or the own exponent `inr x`, held by
the next receiver. The initialisation samples `x₀` and gives the first sender `inl (g^{x₀})` and
the first receiver `inr x₀`. Sending from `inl h` samples `x`, outputs `g^x` with the key `h^x`
and keeps `inr x`; receiving `T` in `inr x` derives `T^x` and keeps `inl T`, erasing `x`. -/
noncomputable def acdCKA : CKADef (G ⊕ CG.Exp) G G where
  init := SPComp.bind (SPComp.sample CG.Exp) fun x =>
    SPComp.pure (CG.pow x, .inl (CG.pow x), .inr x)
  send s := SPComp.bind (SPComp.sample CG.Exp) fun x =>
    SPComp.pure (.inr x, CG.pow x, CyclicGroup.elemPow (acdPubOf CG.pow s) x)
  recv r T := (.inl T, match r with
    | .inl _ => T
    | .inr x => CyclicGroup.elemPow T x)

/-- The sending algorithm of `acdCKA` with its exponent as explicit randomness. -/
noncomputable instance acdCKACoins : CKACoins (acdCKA G) CG.Exp where
  sendR s x := (.inr x, CG.pow x, CyclicGroup.elemPow (acdPubOf CG.pow s) x)

/-- The explicit-randomness sending algorithm of `acdCKA` is its sending algorithm. -/
theorem acdCKACoins_sound : CKACoins.Sound (acdCKA G) := by
  intro s
  simp only [acdCKA, CKACoins.sendR]

variable {G}

/-- **Correctness of `acdCKA`.** The receiver with exponent `y` derives from the message `g^x`
the key `(g^y)^x` of the sender holding the public value `g^y`, and keeps the message. -/
theorem acdCKA_recv (x y : CG.Exp) :
    (acdCKA G).recv (.inr y) (CG.pow x) =
      (.inl (CG.pow x), CyclicGroup.elemPow (acdPubOf CG.pow (.inl (CG.pow y))) x) := by
  simp only [acdCKA, acdPubOf, elemPow_pow_comm]

end ACD

/-! ## The steps of the oracle, of the eager game and of the simulator -/

section ACDSteps

variable {E Gr : Type}

/-- The step of the oracle of the corruption game of `acdCKA` with the exponentiations `pow`
and `epow`, on the drawn exponent `e.1` and the drawn group element `e.2` (the uniform
challenge key of the ideal game). -/
def acdStepOf (pow : E → Gr) (epow : Gr → E → Gr) (ΔFS ΔPCS t : ℕ) (ideal : Bool)
    (s : CKAGameSt (Gr ⊕ E) Gr) (q : CKAQuery) (e : E × Gr) :
    CKAAns (Gr ⊕ E) Gr Gr E × CKAGameSt (Gr ⊕ E) Gr :=
  match q with
  | .send p =>
    if s.canSend p then
      (.out (pow e.1) (epow (acdPubOf pow (s.st p)) e.1), s.sent p (.inr e.1) (pow e.1))
    else (.none, s)
  | .recv p => if s.canRecv p then (.none, s.recvd p (.inl s.msg)) else (.none, s)
  | .chall p =>
    if s.canSend p && s.t p + 1 == t then
      (.out (pow e.1) (if ideal then e.2 else epow (acdPubOf pow (s.st p)) e.1),
        s.sent p (.inr e.1) (pow e.1))
    else (.none, s)
  | .corrupt p => (if ckaAllowCorr ΔFS ΔPCS t s p then .state (s.st p) else .none, s)
  | .sendLeak p =>
    if ckaAllowLeak ΔPCS t s p then
      (.leak (pow e.1) (epow (acdPubOf pow (s.st p)) e.1) e.1, s.sent p (.inr e.1) (pow e.1))
    else (.none, s)

/-- **The step of the simulator** with the DDH triple `(ga, gb, z)`: as `acdStepOf`, except
that the send of epoch `t - 1` has the message `ga` and the key `ga` raised to the exponent of
the receiver, and that the challenge has the message `gb` and the key `z`. The exponent stored
for these sends is the drawn one; the gates never reveal it. -/
def acdSimStepOf (pow : E → Gr) (epow : Gr → E → Gr) (ΔFS ΔPCS t : ℕ) (ga gb z : Gr)
    (s : CKAGameSt (Gr ⊕ E) Gr) (q : CKAQuery) (e : E × Gr) :
    CKAAns (Gr ⊕ E) Gr Gr E × CKAGameSt (Gr ⊕ E) Gr :=
  match q with
  | .send p =>
    if s.canSend p then
      if s.t p + 2 == t then
        (.out ga (epow ga (acdExpOr e.1 (s.st p.other))), s.sent p (.inr e.1) ga)
      else (.out (pow e.1) (epow (acdPubOf pow (s.st p)) e.1), s.sent p (.inr e.1) (pow e.1))
    else (.none, s)
  | .recv p => if s.canRecv p then (.none, s.recvd p (.inl s.msg)) else (.none, s)
  | .chall p =>
    if s.canSend p then
      if s.t p + 1 == t then (.out gb z, s.sent p (.inr e.1) gb) else (.none, s)
    else (.none, s)
  | .corrupt p => (if ckaAllowCorr ΔFS ΔPCS t s p then .state (s.st p) else .none, s)
  | .sendLeak p =>
    if ckaAllowLeak ΔPCS t s p then
      (.leak (pow e.1) (epow (acdPubOf pow (s.st p)) e.1) e.1, s.sent p (.inr e.1) (pow e.1))
    else (.none, s)

/-- The step of the eager game: the send of epoch `t - 1` uses the exponent of `va`, the
challenge the exponent and the group element of `vb`. -/
def acdEagerStepOf (pow : E → Gr) (epow : Gr → E → Gr) (ΔFS ΔPCS t : ℕ) (ideal : Bool)
    (va vb : E × Gr) : CKAGameSt (Gr ⊕ E) Gr → CKAQuery → E × Gr →
      CKAAns (Gr ⊕ E) Gr Gr E × CKAGameSt (Gr ⊕ E) Gr :=
  OracleAdv.eagerStep (OracleAdv.eagerStep (acdStepOf pow epow ΔFS ΔPCS t ideal) (dhCritA t)
    va) (dhCritB t) vb

/-- The done predicates of the eager hops are monotone in the counters. -/
theorem dhDoneA_mono {St Msg : Type} {t : ℕ} {s s' : CKAGameSt St Msg}
    (hA : s.t .A ≤ s'.t .A) (hB : s.t .B ≤ s'.t .B) (h : dhDoneA t s) : dhDoneA t s' := by
  unfold dhDoneA at *; omega

theorem dhDoneB_mono {St Msg : Type} {t : ℕ} {s s' : CKAGameSt St Msg}
    (hA : s.t .A ≤ s'.t .A) (hB : s.t .B ≤ s'.t .B) (h : dhDoneB t s) : dhDoneB t s' := by
  unfold dhDoneB at *; omega

/-- The steps of the game of `acdCKA` do not decrease the counters. -/
theorem acdStepOf_t_le (pow : E → Gr) (epow : Gr → E → Gr) (ΔFS ΔPCS t : ℕ) (ideal : Bool)
    (s : CKAGameSt (Gr ⊕ E) Gr) (q : CKAQuery) (e : E × Gr) (r : CKAParty) :
    s.t r ≤ (acdStepOf pow epow ΔFS ΔPCS t ideal s q e).2.t r := by
  cases q with
  | send p =>
    simp only [acdStepOf]; split
    · exact CKAGameSt.le_sent _ _ _ _ _
    · exact le_refl _
  | recv p =>
    simp only [acdStepOf]; split
    · exact CKAGameSt.le_recvd _ _ _ _
    · exact le_refl _
  | chall p =>
    simp only [acdStepOf]; split
    · exact CKAGameSt.le_sent _ _ _ _ _
    · exact le_refl _
  | corrupt p => exact le_refl _
  | sendLeak p =>
    simp only [acdStepOf]; split
    · exact CKAGameSt.le_sent _ _ _ _ _
    · exact le_refl _

theorem acdDoneA_crit (pow : E → Gr) (epow : Gr → E → Gr) (ΔFS ΔPCS t : ℕ) (ideal : Bool)
    (s : CKAGameSt (Gr ⊕ E) Gr) (q : CKAQuery) (e : E × Gr) (h : dhCritA t s q = true) :
    dhDoneA t (acdStepOf pow epow ΔFS ΔPCS t ideal s q e).2 := by
  cases q with
  | send p =>
    simp only [dhCritA, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hc, ht⟩ := h
    simp only [acdStepOf, hc, ite_true]
    have hs := CKAGameSt.sum_t s p
    have hAB := ((CKAGameSt.canSend_iff s p).1 hc).1
    have h1 := CKAGameSt.t_eq_of_eq hAB p
    have := CKAGameSt.sum_sent s p (.inr e.1) (pow e.1)
    unfold dhDoneA; omega
  | _ => simp [dhCritA] at h

theorem acdDoneB_crit (pow : E → Gr) (epow : Gr → E → Gr) (ΔFS ΔPCS t : ℕ) (ideal : Bool)
    (va : E × Gr) (s : CKAGameSt (Gr ⊕ E) Gr) (q : CKAQuery) (e : E × Gr)
    (h : dhCritB t s q = true) :
    dhDoneB t (OracleAdv.eagerStep (acdStepOf pow epow ΔFS ΔPCS t ideal) (dhCritA t) va
      s q e).2 := by
  cases q with
  | chall p =>
    simp only [dhCritB, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hc, ht⟩ := h
    simp only [OracleAdv.eagerStep, dhCritA, Bool.false_eq_true, ite_false, acdStepOf, hc, ht,
      beq_self_eq_true, Bool.and_self, ite_true]
    have hs := CKAGameSt.sum_t s p
    have hAB := ((CKAGameSt.canSend_iff s p).1 hc).1
    have h1 := CKAGameSt.t_eq_of_eq hAB p
    have := CKAGameSt.sum_sent s p (.inr e.1) (pow e.1)
    unfold dhDoneB; omega
  | _ => simp [dhCritB] at h

theorem acdDoneB_eager (pow : E → Gr) (epow : Gr → E → Gr) (ΔFS ΔPCS t : ℕ) (ideal : Bool)
    (va : E × Gr) (s : CKAGameSt (Gr ⊕ E) Gr) (q : CKAQuery) (e : E × Gr) (h : dhDoneB t s) :
    dhDoneB t (OracleAdv.eagerStep (acdStepOf pow epow ΔFS ΔPCS t ideal) (dhCritA t) va
      s q e).2 := by
  obtain ⟨e', he⟩ := OracleAdv.eagerStep_exists (acdStepOf pow epow ΔFS ΔPCS t ideal)
    (dhCritA t) va s q e
  rw [he]
  exact dhDoneB_mono (acdStepOf_t_le pow epow ΔFS ΔPCS t ideal s q e' .A)
    (acdStepOf_t_le pow epow ΔFS ΔPCS t ideal s q e' .B) h

end ACDSteps

/-! ## The simulation relation -/

/-- The state of party `p` is not determined by the view of the simulator: the challenged
party `ckaSender t` at counter `t`, holding the challenge exponent until it receives, and its
peer at counter `t - 1`, holding the exponent of epoch `t - 1` until it receives the challenge
message. -/
def acdHidden {St Msg : Type} (t : ℕ) (s : CKAGameSt St Msg) (p : CKAParty) : Prop :=
  if p = ckaSender t then s.t p = t else s.t p + 1 = t

/-- A party that the gates with `ΔFS = 1` and `ΔPCS = 2` allow to corrupt is outside its
hidden window. -/
theorem not_acdHidden_of_allowCorr {St Msg : Type} {t : ℕ} {s : CKAGameSt St Msg}
    {p : CKAParty} (h : ckaAllowCorr 1 2 t s p = true) : ¬ acdHidden t s p := by
  intro hh
  have hp : s.t p ≤ max (s.t .A) (s.t .B) := by
    cases p
    · exact le_max_left _ _
    · exact le_max_right _ _
  have h2 : s.t p + 1 ≥ t ∧ s.t p ≤ t := by unfold acdHidden at hh; split at hh <;> omega
  simp only [ckaAllowCorr, Bool.or_eq_true, decide_eq_true_eq] at h
  omega

/-- The sender of the next epoch is outside its hidden window. -/
theorem not_acdHidden_of_canSend {St Msg : Type} {t : ℕ} {s : CKAGameSt St Msg}
    {p : CKAParty} (hc : s.canSend p = true) : ¬ acdHidden t s p := by
  obtain ⟨hAB, hp⟩ := (CKAGameSt.canSend_iff s p).1 hc
  have htp : s.t p = s.t .A := CKAGameSt.t_eq_of_eq hAB p
  intro hh
  unfold acdHidden at hh
  split at hh
  · next hP =>
    have : ckaSender (t + 1) = p := by rw [← hh, htp, hp]
    rw [ckaSender_succ, ← hP] at this
    exact CKAParty.other_ne _ this
  · next hP =>
    exact hP (by rw [← hh, htp, hp])

theorem acdHidden_sent_of_ne {St Msg : Type} (t : ℕ) (s : CKAGameSt St Msg) {p q : CKAParty}
    (hq : q ≠ p) (x : St) (T : Msg) : acdHidden t (s.sent p x T) q ↔ acdHidden t s q := by
  simp only [acdHidden, CKAGameSt.sent_t, hq, ite_false]

theorem acdHidden_recvd_of_ne {St Msg : Type} (t : ℕ) (s : CKAGameSt St Msg) {p q : CKAParty}
    (hq : q ≠ p) (x : St) : acdHidden t (s.recvd p x) q ↔ acdHidden t s q := by
  simp only [acdHidden, CKAGameSt.recvd_t, hq, ite_false]

section ACDRel

variable {G : Type} [CG : CyclicGroup G]

/-- **The simulation relation** between a state `s` of the eager game, in which the send of
epoch `t - 1` used the exponent `a`, and a state `σ` of the simulator: equal counters and
messages, and equal party states outside the hidden windows; and the invariants of the eager
game: the counters are equal or the last sender is one epoch ahead, the next sender holds the
public value of the exponent of its peer, the last sender holds the exponent of the message in
transit, and the peer of the challenged party holds `a` at counter `t - 1`. -/
structure ACDRel (a : CG.Exp) (t : ℕ) (s σ : CKAGameSt (G ⊕ CG.Exp) G) : Prop where
  t_eq : s.t = σ.t
  msg_eq : s.msg = σ.msg
  st_eq : ∀ p, ¬ acdHidden t s p → s.st p = σ.st p
  shape : s.t .A = s.t .B ∨ ∃ p, s.t p = s.t p.other + 1 ∧ ckaSender (s.t p) = p
  inv1 : s.t .A = s.t .B → ∃ y, s.st (ckaSender (s.t .A + 1)).other = .inr y ∧
    s.st (ckaSender (s.t .A + 1)) = .inl (CG.pow y)
  inv2 : ∀ p, s.t p = s.t p.other + 1 → ∃ x, s.st p = .inr x ∧ s.msg = CG.pow x
  inv3 : s.t (ckaSender t).other + 1 = t → s.st (ckaSender t).other = .inr a

namespace ACDRel

variable {a : CG.Exp} {t : ℕ} {s σ : CKAGameSt (G ⊕ CG.Exp) G}

/-- The simulation relation after a send of party `p` with the exponents `x` (eager game) and
`x'` (simulator), equal outside the hidden window. -/
theorem sent (h : ACDRel a t s σ) {p : CKAParty} (hc : s.canSend p = true) (x x' : CG.Exp)
    (T : G) (hT : T = CG.pow x)
    (hx : ¬ acdHidden t (s.sent p (.inr x) T) p → x = x')
    (ha : p = (ckaSender t).other → s.t p + 2 = t → x = a) :
    ACDRel a t (s.sent p (.inr x) T) (σ.sent p (.inr x') T) := by
  rw [CKAGameSt.canSend_iff] at hc
  obtain ⟨hAB, hp⟩ := hc
  have htp : s.t p = s.t .A := CKAGameSt.t_eq_of_eq hAB p
  have hto : s.t p.other = s.t .A := CKAGameSt.t_other_eq_of_eq hAB p
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · funext q
    simp only [CKAGameSt.sent_t, h.t_eq]
  · intro q hq
    by_cases hqp : q = p
    · subst hqp
      simp only [CKAGameSt.sent_st, ite_true]
      rw [hx hq]
    · simp only [CKAGameSt.sent_st, hqp, ite_false]
      exact h.st_eq q ((not_congr (acdHidden_sent_of_ne t s hqp _ _)).1 hq)
  · right
    refine ⟨p, ?_, ?_⟩
    · simp only [CKAGameSt.sent_t, ite_true, CKAParty.other_ne, ite_false]
      omega
    · simp only [CKAGameSt.sent_t, ite_true, htp, hp]
  · intro hAB'
    exfalso
    cases p <;> simp only [CKAGameSt.sent_t, ite_true, reduceCtorEq, ite_false] at hAB' <;>
      simp only [CKAParty.other] at hto <;> omega
  · intro q hq
    by_cases hqp : q = p
    · subst hqp
      exact ⟨x, by simp only [CKAGameSt.sent_st, ite_true], hT⟩
    · exfalso
      have hqo : q = p.other := (CKAParty.eq_or_eq_other q p).resolve_left hqp
      subst hqo
      simp only [CKAGameSt.sent_t, CKAParty.other_other, ite_true, CKAParty.other_ne,
        ite_false] at hq
      omega
  · intro hlo
    by_cases hP : p = (ckaSender t).other
    · subst hP
      simp only [CKAGameSt.sent_st, CKAGameSt.sent_t, ite_true] at hlo ⊢
      rw [ha rfl (by omega)]
    · have hne : (ckaSender t).other ≠ p := fun e => hP e.symm
      simp only [CKAGameSt.sent_st, CKAGameSt.sent_t, hne, ite_false] at hlo ⊢
      exact h.inv3 hlo

/-- The simulation relation after a receive of party `p`. -/
theorem recvd (h : ACDRel a t s σ) {p : CKAParty} (hc : s.canRecv p = true) :
    ACDRel a t (s.recvd p (.inl s.msg)) (σ.recvd p (.inl σ.msg)) := by
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext q
    simp only [CKAGameSt.recvd_t, h.t_eq]
  · simp only [CKAGameSt.recvd_msg, h.msg_eq]
  · intro q hq
    by_cases hqp : q = p
    · subst hqp
      simp only [CKAGameSt.recvd_st, ite_true, h.msg_eq]
    · simp only [CKAGameSt.recvd_st, hqp, ite_false]
      exact h.st_eq q ((not_congr (acdHidden_recvd_of_ne t s hqp _)).1 hq)
  · left
    cases p <;> simp only [CKAGameSt.recvd_t, ite_true, reduceCtorEq, ite_false] <;>
      simp only [CKAParty.other] at hc <;> omega
  · intro _
    have hA : (s.recvd p (.inl s.msg)).t .A + 1 = s.t p.other + 1 := by
      cases p
      · simp only [CKAGameSt.recvd_t, ite_true, CKAParty.other_A] at hc ⊢; omega
      · simp only [CKAGameSt.recvd_t, reduceCtorEq, ite_false, CKAParty.other_B] at hc ⊢
    have hn : ckaSender ((s.recvd p (.inl s.msg)).t .A + 1) = p := by
      rw [hA, ckaSender_succ, hahead, CKAParty.other_other]
    rw [hn]
    obtain ⟨x, hx1, hx2⟩ := h.inv2 p.other (by rw [CKAParty.other_other]; omega)
    refine ⟨x, ?_, ?_⟩
    · simp only [CKAGameSt.recvd_st, CKAParty.other_ne, ite_false, hx1]
    · simp only [CKAGameSt.recvd_st, ite_true, hx2]
  · intro q hq
    exfalso
    cases p <;> cases q <;> simp only [CKAGameSt.recvd_t, ite_true, reduceCtorEq, ite_false,
      CKAParty.other] at hq hc <;> omega
  · intro hlo
    by_cases hP : p = (ckaSender t).other
    · exfalso
      have hsP : ckaSender (s.t p + 1) = p.other := hsnd
      subst hP
      simp only [CKAGameSt.recvd_t, ite_true] at hlo
      have : ckaSender (s.t (ckaSender t).other + 1 + 1) = ckaSender t := by
        rw [show s.t (ckaSender t).other + 1 + 1 = t by omega]
      rw [ckaSender_succ, hsP, CKAParty.other_other] at this
      exact CKAParty.other_ne _ this
    · have hne : (ckaSender t).other ≠ p := fun e => hP e.symm
      simp only [CKAGameSt.recvd_st, CKAGameSt.recvd_t, hne, ite_false] at hlo ⊢
      exact h.inv3 hlo

end ACDRel

/-- **The simulation step.** From related states, the eager game with the exponents `a = va.1`,
`b = vb.1` and the group element `vb.2`, and the simulator with the triple `(g^a, g^b, z)`,
where `z` is `vb.2` in the ideal game and `g^{ab}` in the real one, give equal answers and
related states. -/
theorem acdRel_step (t : ℕ) (ideal : Bool) (va vb : CG.Exp × G) (z : G)
    (hz : z = if ideal then vb.2 else CG.pow (CG.expMul va.1 vb.1))
    (s σ : CKAGameSt (G ⊕ CG.Exp) G) (h : ACDRel va.1 t s σ) (q : CKAQuery)
    (e : CG.Exp × G) :
    (acdEagerStepOf CG.pow CyclicGroup.elemPow 1 2 t ideal va vb s q e).1 =
        (acdSimStepOf CG.pow CyclicGroup.elemPow 1 2 t (CG.pow va.1) (CG.pow vb.1) z σ q
          e).1 ∧
      ACDRel va.1 t (acdEagerStepOf CG.pow CyclicGroup.elemPow 1 2 t ideal va vb s q e).2
        (acdSimStepOf CG.pow CyclicGroup.elemPow 1 2 t (CG.pow va.1) (CG.pow vb.1) z σ q
          e).2 := by
  have hcs := CKAGameSt.canSend_eq_of_t h.t_eq
  have hcr := CKAGameSt.canRecv_eq_of_t h.t_eq
  have hco := CKAGameSt.allowCorr_eq_of_t h.t_eq
  have hcl := CKAGameSt.allowLeak_eq_of_t h.t_eq
  have hσt : σ.t = s.t := h.t_eq.symm
  cases q with
  | send p =>
    simp only [acdEagerStepOf, OracleAdv.eagerStep, dhCritA, dhCritB, Bool.false_eq_true,
      ite_false, acdStepOf, acdSimStepOf, hcs, hσt]
    rcases (Bool.eq_false_or_eq_true (s.canSend p)).symm with hc | hc
    · simp only [hc, ite_false, Bool.false_eq_true]; exact ⟨by trivial, h⟩
    · simp only [hc, ite_true]
      obtain ⟨hAB, hp⟩ := (CKAGameSt.canSend_iff s p).1 hc
      have htp := CKAGameSt.t_eq_of_eq hAB p
      have hto := CKAGameSt.t_other_eq_of_eq hAB p
      have hseq := h.st_eq p (not_acdHidden_of_canSend hc)
      by_cases ht2 : s.t p + 2 = t
      · simp only [ht2, beq_self_eq_true, Bool.and_self, ite_true]
        have hP : ckaSender t = p.other := by
          rw [← ht2, show s.t p + 2 = s.t .A + 1 + 1 by omega, ckaSender_succ, hp]
        have hnh : ¬ acdHidden t s p.other := by
          intro hh; unfold acdHidden at hh; split at hh <;> omega
        obtain ⟨y, hy1, hy2⟩ := h.inv1 hAB
        rw [hp] at hy1 hy2
        refine ⟨?_, h.sent hc va.1 e.1 _ rfl ?_ fun _ _ => rfl⟩
        · rw [hy2, ← h.st_eq _ hnh, hy1]
          simp only [acdPubOf, acdExpOr, elemPow_pow_comm]
        · intro hh; exfalso; apply hh
          unfold acdHidden
          rw [ite_eq_right (by rw [hP]; exact CKAParty.ne_other p)]
          simp only [CKAGameSt.sent_t, ite_true]; omega
      · have hne : (s.t p + 2 == t) = false := by simpa using ht2
        simp only [hne, Bool.and_false, Bool.false_eq_true, ite_false]
        exact ⟨by rw [hseq], h.sent hc e.1 e.1 _ rfl (fun _ => rfl)
          fun _ h2 => absurd h2 ht2⟩
  | recv p =>
    simp only [acdEagerStepOf, OracleAdv.eagerStep, dhCritA, dhCritB, Bool.false_eq_true,
      ite_false, acdStepOf, acdSimStepOf, hcr]
    rcases (Bool.eq_false_or_eq_true (s.canRecv p)).symm with hc | hc
    · simp only [hc, ite_false, Bool.false_eq_true]; exact ⟨by trivial, h⟩
    · simp only [hc, ite_true]; exact ⟨by trivial, h.recvd hc⟩
  | chall p =>
    simp only [acdEagerStepOf, OracleAdv.eagerStep, dhCritA, dhCritB, Bool.false_eq_true,
      ite_false, acdStepOf, acdSimStepOf, hcs, hσt]
    rcases (Bool.eq_false_or_eq_true (s.canSend p && s.t p + 1 == t)).symm with hcb | hcb
    · rcases (Bool.eq_false_or_eq_true (s.canSend p)).symm with hc | hc
      · simp only [hc, ite_false, Bool.false_eq_true]; exact ⟨by trivial, h⟩
      · have ht : (s.t p + 1 == t) = false := by simpa [hc] using hcb
        simp only [hc, ht, ite_true, ite_false, Bool.false_eq_true]; exact ⟨by trivial, h⟩
    · have hcb' := hcb
      simp only [Bool.and_eq_true] at hcb'
      simp only [hcb'.1, hcb'.2, Bool.and_self, ite_true]
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
          simp only [Bool.false_eq_true, ite_false]
          obtain ⟨y, hy1, hy2⟩ := h.inv1 hAB
          rw [hp] at hy1 hy2
          have h3 := h.inv3 (by rw [hP]; omega)
          rw [hP, hy1] at h3
          cases h3
          rw [hy2]
          simp only [acdPubOf, CyclicGroup.elemPow_pow]
      · intro hh; exfalso; apply hh
        unfold acdHidden
        rw [ite_eq_left hP.symm]
        simp only [CKAGameSt.sent_t, ite_true]; omega
      · intro hpP
        exfalso
        rw [hP] at hpP
        exact CKAParty.ne_other p hpP
  | corrupt p =>
    simp only [acdEagerStepOf, OracleAdv.eagerStep, dhCritA, dhCritB, Bool.false_eq_true,
      ite_false, acdStepOf, acdSimStepOf, hco]
    rcases (Bool.eq_false_or_eq_true (ckaAllowCorr 1 2 t s p)).symm with hg | hg
    · simp only [hg, ite_false, Bool.false_eq_true]; exact ⟨by trivial, h⟩
    · simp only [hg, ite_true]
      exact ⟨by rw [h.st_eq p (not_acdHidden_of_allowCorr hg)], h⟩
  | sendLeak p =>
    simp only [acdEagerStepOf, OracleAdv.eagerStep, dhCritA, dhCritB, Bool.false_eq_true,
      ite_false, acdStepOf, acdSimStepOf, hcl]
    rcases (Bool.eq_false_or_eq_true (ckaAllowLeak 2 t s p)).symm with hl | hl
    · simp only [hl, ite_false, Bool.false_eq_true]; exact ⟨by trivial, h⟩
    · simp only [hl, ite_true]
      simp only [ckaAllowLeak, Bool.and_eq_true, decide_eq_true_eq] at hl
      obtain ⟨hc, ht3⟩ := hl
      have hseq := h.st_eq p (not_acdHidden_of_canSend hc)
      exact ⟨by rw [hseq], h.sent hc e.1 e.1 _ rfl (fun _ => rfl) fun _ _ => by omega⟩

end ACDRel

/-! ## The game of `acdCKA` as a probability mass function -/

section ACDGame

variable {G : Type} [CG : CyclicGroup G] {α : Type}

/-- **The oracle of `acdCKA` in normal form.** Each oracle computation of the game of `acdCKA`
is the lifted distribution of the step `acdStepOf` on a draw of `dhDraw`. -/
theorem acdCKA_oracle_eq (ΔFS ΔPCS t : ℕ) (ideal : Bool) (s : CKAGameSt (G ⊕ CG.Exp) G)
    (q : CKAQuery) :
    ckaCorruptOracle (acdCKA G) ΔFS ΔPCS t ideal s q =
      liftPMF ((dhDraw G).map (acdStepOf CG.pow CyclicGroup.elemPow ΔFS ΔPCS t ideal s q)) := by
  rw [dhDraw_map]
  cases q with
  | send p =>
    simp only [ckaCorruptOracle, acdStepOf]
    rcases (Bool.eq_false_or_eq_true (s.canSend p)).symm with hc | hc
    · simp only [hc, Bool.false_eq_true, ite_false, PMF.bind_const, liftPMF_pure]
    · simp only [hc, ite_true, acdCKA, PMF.bind_const,
        sample_eq_liftPMF, liftPMF_pure, liftPMF_bind_liftPMF, PMF.bind_bind, PMF.pure_bind]
  | recv p =>
    simp only [ckaCorruptOracle, acdStepOf, acdCKA]
    rcases (Bool.eq_false_or_eq_true (s.canRecv p)).symm with hc | hc
    · simp only [hc, Bool.false_eq_true, ite_false, PMF.bind_const, liftPMF_pure]
    · simp only [hc, ite_true, PMF.bind_const, liftPMF_pure]
  | chall p =>
    simp only [ckaCorruptOracle, acdStepOf]
    rcases (Bool.eq_false_or_eq_true (s.canSend p && s.t p + 1 == t)).symm with hc | hc
    · simp only [hc, Bool.false_eq_true, ite_false, PMF.bind_const, liftPMF_pure]
    · cases ideal with
      | true =>
        simp only [hc, ite_true, acdCKA,
          sample_eq_liftPMF, liftPMF_pure, liftPMF_bind_liftPMF, PMF.bind_bind, PMF.pure_bind]
      | false =>
        simp only [hc, ite_true, Bool.false_eq_true, ite_false, acdCKA,
          PMF.bind_const, sample_eq_liftPMF, liftPMF_pure,
          liftPMF_bind_liftPMF, PMF.bind_bind, PMF.pure_bind]
  | corrupt p =>
    simp only [ckaCorruptOracle, acdStepOf, PMF.bind_const, liftPMF_pure]
  | sendLeak p =>
    simp only [ckaCorruptOracle, acdStepOf]
    rcases (Bool.eq_false_or_eq_true (ckaAllowLeak ΔPCS t s p)).symm with hc | hc
    · simp only [hc, Bool.false_eq_true, ite_false, PMF.bind_const, liftPMF_pure]
    · simp only [hc, ite_true, CKACoins.sendR, PMF.bind_const, sample_eq_liftPMF, liftPMF_pure,
        liftPMF_bind_liftPMF]

/-- The distribution of the output of the game of `acdCKA` with the challenge epoch `t`. -/
noncomputable def acdGamePMF (ΔFS ΔPCS t : ℕ) (ideal : Bool)
    (play : G → OracleAdv CKAQuery (CKAAns (G ⊕ CG.Exp) G G CG.Exp) α) : PMF α :=
  (PMF.uniformFintype CG.Exp).bind fun x₀ =>
    (OracleAdv.run (OracleAdv.nfOracle (dhDraw G)
      (acdStepOf CG.pow CyclicGroup.elemPow ΔFS ΔPCS t ideal)) (play (CG.pow x₀))
      (CKAGameSt.init (CG.pow x₀) (.inl (CG.pow x₀)) (.inr x₀))).map Prod.fst

/-- The corruption game of `acdCKA` is the lifted distribution `acdGamePMF` after the choice
of the challenge epoch. -/
theorem acdCKA_game_eq (ΔFS ΔPCS : ℕ) (ideal : Bool)
    (A : CKACorruptAdv (G ⊕ CG.Exp) G G CG.Exp α) :
    cka_corrupt_game (acdCKA G) ΔFS ΔPCS ideal A =
      liftPMF (A.tStar.bind fun t => acdGamePMF ΔFS ΔPCS t ideal (A.play t)) := by
  unfold cka_corrupt_game acdGamePMF
  simp only [OracleAdv.runSP_eq_liftPMF _ _ (acdCKA_oracle_eq ΔFS ΔPCS _ ideal)]
  simp only [acdCKA, sample_eq_liftPMF, liftPMF_bind_pure,
    liftPMF_bind_liftPMF, PMF.bind_map]
  rfl

/-- The two eager hops: the exponent of the send of epoch `t - 1` and the exponent and the
group element of the challenge are drawn in advance. -/
theorem run_acdStep_eager (t : ℕ) (ideal : Bool)
    (A : OracleAdv CKAQuery (CKAAns (G ⊕ CG.Exp) G G CG.Exp) α)
    (s : CKAGameSt (G ⊕ CG.Exp) G) :
    OracleAdv.run (OracleAdv.nfOracle (dhDraw G)
        (acdStepOf CG.pow CyclicGroup.elemPow 1 2 t ideal)) A s =
      (dhDraw G).bind fun va => (dhDraw G).bind fun vb =>
        OracleAdv.run (OracleAdv.nfOracle (dhDraw G)
          (acdEagerStepOf CG.pow CyclicGroup.elemPow 1 2 t ideal va vb)) A s := by
  rw [OracleAdv.run_nf_eq_eager (dhDraw G) _ (dhCritA t) (dhDoneA t)
    (acdDoneA_crit _ _ _ _ _ _)
    (fun s q e h => dhDoneA_mono (acdStepOf_t_le _ _ _ _ _ _ s q e .A)
      (acdStepOf_t_le _ _ _ _ _ _ s q e .B) h) (dhDoneA_noCrit t)]
  congr 1; funext va
  exact OracleAdv.run_nf_eq_eager (dhDraw G) _ (dhCritB t) (dhDoneB t)
    (acdDoneB_crit _ _ _ _ _ _ va) (acdDoneB_eager _ _ _ _ _ _ va) (dhDoneB_noCrit t) A s

/-- The game of `acdCKA` as the eager game, with the initial exponent `dhX0 t va.1 x₀`. -/
theorem acdGamePMF_eager (t : ℕ) (ideal : Bool)
    (play : G → OracleAdv CKAQuery (CKAAns (G ⊕ CG.Exp) G G CG.Exp) α) :
    acdGamePMF 1 2 t ideal play =
      (PMF.uniformFintype CG.Exp).bind fun x₀ => (dhDraw G).bind fun va =>
        (dhDraw G).bind fun vb =>
          (OracleAdv.run (OracleAdv.nfOracle (dhDraw G)
            (acdEagerStepOf CG.pow CyclicGroup.elemPow 1 2 t ideal va vb))
            (play (CG.pow (dhX0 t va.1 x₀)))
            (CKAGameSt.init (CG.pow (dhX0 t va.1 x₀)) (.inl (CG.pow (dhX0 t va.1 x₀)))
              (.inr (dhX0 t va.1 x₀)))).map Prod.fst := by
  unfold acdGamePMF
  by_cases ht : t = 1
  · subst ht
    have hA : ∀ va : CG.Exp × G,
        OracleAdv.eagerStep (acdStepOf CG.pow CyclicGroup.elemPow 1 2 1 ideal) (dhCritA 1) va =
          acdStepOf CG.pow CyclicGroup.elemPow 1 2 1 ideal := by
      intro va; funext s q e
      simp only [OracleAdv.eagerStep, dhCritA_one, Bool.false_eq_true, ite_false]
    simp only [acdEagerStepOf, hA, dhX0, ite_true, PMF.bind_const]
    rw [dhDraw_bind]
    simp only [PMF.bind_const]
    congr 1; funext x₀
    rw [OracleAdv.run_nf_eq_eager (dhDraw G) _ (dhCritB 1) (dhDoneB 1)
      (fun s q e h => by
        have := acdDoneB_crit CG.pow CyclicGroup.elemPow 1 2 1 ideal (Classical.arbitrary _)
          s q e h
        rwa [hA] at this)
      (fun s q e h => dhDoneB_mono (acdStepOf_t_le _ _ _ _ _ _ s q e .A)
        (acdStepOf_t_le _ _ _ _ _ _ s q e .B) h) (dhDoneB_noCrit 1), PMF.map_bind]
  · simp only [dhX0, ht, ite_false, run_acdStep_eager, PMF.map_bind]

/-- The initial states of the eager game and of the simulator are related. -/
theorem acdRel_init (t : ℕ) (a x₀ : CG.Exp) :
    ACDRel a t (CKAGameSt.init (CG.pow (dhX0 t a x₀)) (.inl (CG.pow (dhX0 t a x₀)))
        (.inr (dhX0 t a x₀)))
      (CKAGameSt.init (CG.pow (dhX0 t a x₀)) (.inl (CG.pow (dhX0 t a x₀))) (.inr x₀)) := by
  refine ⟨rfl, rfl, ?_, Or.inl rfl, fun _ => ⟨dhX0 t a x₀, rfl, rfl⟩, ?_, ?_⟩
  · intro p hp
    by_cases ht : t = 1
    · subst ht
      cases p
      · rfl
      · exfalso; apply hp
        simp [acdHidden, CKAGameSt.init, ckaSender]
    · cases p <;> simp [CKAGameSt.init, dhX0, ht]
  · intro p hp
    cases p <;> simp [CKAGameSt.init] at hp
  · intro hlo
    have ht : t = 1 := by
      have : (CKAGameSt.init (CG.pow (dhX0 t a x₀)) (.inl (CG.pow (dhX0 t a x₀)))
          (.inr (dhX0 t a x₀)) : CKAGameSt (G ⊕ CG.Exp) G).t (ckaSender t).other = 0 := rfl
      omega
    subst ht
    rfl

/-- **The eager game is the simulation.** -/
theorem acd_eager_eq_sim (t : ℕ) (ideal : Bool) (va vb : CG.Exp × G) (x₀ : CG.Exp)
    (play : G → OracleAdv CKAQuery (CKAAns (G ⊕ CG.Exp) G G CG.Exp) α) :
    (OracleAdv.run (OracleAdv.nfOracle (dhDraw G)
        (acdEagerStepOf CG.pow CyclicGroup.elemPow 1 2 t ideal va vb))
        (play (CG.pow (dhX0 t va.1 x₀)))
        (CKAGameSt.init (CG.pow (dhX0 t va.1 x₀)) (.inl (CG.pow (dhX0 t va.1 x₀)))
          (.inr (dhX0 t va.1 x₀)))).map Prod.fst =
      (OracleAdv.run (OracleAdv.nfOracle (dhDraw G)
        (acdSimStepOf CG.pow CyclicGroup.elemPow 1 2 t (CG.pow va.1) (CG.pow vb.1)
          (if ideal then vb.2 else CG.pow (CG.expMul va.1 vb.1))))
        (play (CG.pow (dhX0 t va.1 x₀)))
        (CKAGameSt.init (CG.pow (dhX0 t va.1 x₀)) (.inl (CG.pow (dhX0 t va.1 x₀)))
          (.inr x₀))).map Prod.fst :=
  OracleAdv.run_nf_map_fst_eq_of_rel (dhDraw G) _ _ (ACDRel va.1 t)
    (fun s σ h q e => acdRel_step t ideal va vb _ rfl s σ h q e) _ _ _ (acdRel_init t va.1 x₀)

end ACDGame

/-! ## The reduction -/

section ACDRed

variable {E Gr : Type} [Fintype E] [Nonempty E] [Fintype Gr] [Nonempty Gr] {α : Type}

/-- The simulator answers a query by drawing an exponent and a group element and running the
simulation step. -/
noncomputable def acdSimImplOf (pow : E → Gr) (epow : Gr → E → Gr) (ΔFS ΔPCS t : ℕ)
    (ga gb z : Gr) (σ : CKAGameSt (Gr ⊕ E) Gr) (q : CKAQuery) :
    OracleAdv Empty Unit (CKAAns (Gr ⊕ E) Gr Gr E × CKAGameSt (Gr ⊕ E) Gr) :=
  .rand (PMF.uniformFintype E) fun x =>
    .rand (PMF.uniformFintype Gr) fun u =>
      .ret (acdSimStepOf pow epow ΔFS ΔPCS t ga gb z σ q (x, u))

/-- **The DDH reduction for `acdCKA`** as an oracle tree without queries. On the triple
`(ga, gb, z)` it draws the challenge epoch `t` of the adversary and an exponent `x₀`; the
public value of the initialisation is `ga` if `t = 1` and `g^{x₀}` otherwise; it runs the
adversary against the simulator `acdSimImplOf` and returns its output. -/
noncomputable def acdDDHTreeOf (pow : E → Gr) (epow : Gr → E → Gr) (ΔFS ΔPCS : ℕ)
    (tStar : PMF ℕ) (play : ℕ → Gr → OracleAdv CKAQuery (CKAAns (Gr ⊕ E) Gr Gr E) α)
    (ga gb z : Gr) : OracleAdv Empty Unit α :=
  .rand tStar fun t =>
    .rand (PMF.uniformFintype E) fun x₀ =>
      (OracleAdv.simulate (acdSimImplOf pow epow ΔFS ΔPCS t ga gb z)
        (play t (if t = 1 then ga else pow x₀))
        (CKAGameSt.init (if t = 1 then ga else pow x₀) (.inl (if t = 1 then ga else pow x₀))
          (.inr x₀))).bind fun r => .ret r.1

end ACDRed

/-! ## The costed reduction -/

derive_timed acdDDHTreeOf

/-- The time of the `i`-th simulated query of `acdSimImplOf`, with exponentiations of costs at
most `P` and `X`. -/
def acdSimQueryTime (P X i : ℕ) : ℕ := 3 * P + X + 21 * i + 51

section ACDTime

variable {E Gr : Type} [Fintype E] [Nonempty E] [Fintype Gr] [Nonempty Gr] {α : Type}

/-- **Time of a simulated query.** From a costed state within the bound `ckaSimCostInv i`, the
costed simulator answers in time at most `acdSimQueryTime P X i` and returns a costed state
within the bound `ckaSimCostInv (i + 1)`. -/
theorem acdSimImplOf.timed_bound (pow : E → Gr) (powCost : E → ℕ) (epow : Gr → E → Gr)
    (epowCost : Gr → E → ℕ) (ΔFS ΔPCS t : ℕ) (ga gb z : Gr) {P X : ℕ}
    (hP : ∀ x, powCost x ≤ P) (hX : ∀ g x, epowCost g x ≤ X) (i : ℕ)
    (σ : CKAGameSt (Gr ⊕ E) Gr) (q : CKAQuery) (stCost tCost : CKAParty → ℕ)
    (hS : ∀ p, stCost p ≤ 1 + 3 * i) (hT : ∀ p, tCost p ≤ 3 * i) :
    OracleAdv.Timed.StepTimeBound
        (OracleAdv.Timed.delay 1 (acdSimImplOf.timed pow powCost epow epowCost ΔFS ΔPCS t
          ga gb z σ q stCost tCost)) (acdSimQueryTime P X i) ∧
      OracleAdv.Timed.AllRet (fun y => ckaSimCostInv (i + 1) y.2)
        (acdSimImplOf.timed pow powCost epow epowCost ΔFS ΔPCS t ga gb z σ q stCost
          tCost).2 := by
  refine ⟨?_, ?_⟩
  · unfold acdSimQueryTime
    refine ⟨by simp [OracleAdv.Timed.delay, acdSimImplOf.timed], ?_⟩
    simp only [OracleAdv.Timed.delay, acdSimImplOf.timed, Nat.add_zero]
    refine ⟨by omega, fun x => ⟨Nat.zero_le _, by dsimp only; omega,
      fun u => ⟨?_, trivial⟩⟩⟩
    have := hP x
    have hpub : ∀ y : Gr ⊕ E, (match y with
        | .inl _ => 0
        | .inr x => 1 + powCost x) ≤ 1 + P := fun y => by
      cases y with
      | inl _ => exact Nat.zero_le _
      | inr x => exact Nat.add_le_add_left (hP x) 1
    cases q with
    | send p =>
      have := hS p; have := hS p.other; have := hT p; have := hT .A; have := hT .B
      have := hX ga (acdExpOr x (σ.st p.other)); have := hX (acdPubOf pow (σ.st p)) x
      have := hpub (σ.st p)
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
      split
      · split <;> omega
      · omega
    | corrupt p =>
      have := hS p; have := hT p; have := hT .A; have := hT .B
      dsimp only
      split <;> omega
    | sendLeak p =>
      have := hS p; have := hT p; have := hT .A; have := hT .B
      have := hX (acdPubOf pow (σ.st p)) x
      have := hpub (σ.st p)
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
      · split
        · exact ⟨hSu p, hTu p⟩
        · exact ⟨hS', hT'⟩
      · exact ⟨hS', hT'⟩
    | corrupt p => exact ⟨hS', hT'⟩
    | sendLeak p =>
      dsimp only [OracleAdv.Timed.AllRet]
      split
      · exact ⟨hSu p, hTu p⟩
      · exact ⟨hS', hT'⟩

end ACDTime

/-- **Time of the DDH reduction.** For an adversary whose costed trees have time at most `T`,
at most `q` queries and call cost at most `a`, and exponentiations of costs at most `P` (of the
generator) and `X` (of a group element), the costed reduction tree has time at most
`T + ∑_{j < q} (3 P + X + 21 j + 51) + a + 4 P + 12`: the adversary, one simulated query per
query, whose cost grows with the closure layers of the simulator state, and the choice of the
initial exponent. -/
theorem acdDDHTreeOf.timeBound_timed {E Gr α : Type} [Fintype E] [Nonempty E] [Fintype Gr]
    [Nonempty Gr] (pow : E → Gr) (powCost : E → ℕ) (epow : Gr → E → Gr)
    (epowCost : Gr → E → ℕ) (ΔFS ΔPCS : ℕ) (tStar : PMF ℕ)
    (play : ℕ → Gr → OracleAdv.Timed CKAQuery (CKAAns (Gr ⊕ E) Gr Gr E) α)
    (playCost : ℕ → Gr → ℕ) (ga gb z : Gr) {T q a P X : ℕ}
    (hA : ∀ t g, (play t g).TimeBound T) (hq : ∀ t g, (play t g).erase.IsQueryBound q)
    (ha : ∀ t g, playCost t g ≤ a) (hP : ∀ x, powCost x ≤ P)
    (hX : ∀ g x, epowCost g x ≤ X) :
    OracleAdv.Timed.StepTimeBound
      (acdDDHTreeOf.timed pow powCost epow epowCost ΔFS ΔPCS tStar play playCost ga gb z)
      (T + ∑ j ∈ Finset.range q, acdSimQueryTime P X j + a + 4 * P + 12) := by
  unfold acdDDHTreeOf.timed
  refine (timeBound_rand_rand_bind (K := 10 + a + 4 * P)
    (B := T + ∑ j ∈ Finset.range q, acdSimQueryTime P X j) _ _ _ _ ?_ ?_).mono (by omega)
  · intro t x₀
    have := ha t ga
    have := ha t (pow x₀)
    have := hP x₀
    split <;> omega
  · intro t x₀
    refine (OracleAdv.Timed.timeBound_simulateHat_inv _ _ _ ckaSimCostInv
      (acdSimQueryTime P X)
      (fun i ŝ d h => by
        exact acdSimImplOf.timed_bound pow powCost epow epowCost ΔFS ΔPCS t ga gb z
          hP hX i _ d _ _ h.1 h.2) (hA t (if t = 1 then ga else pow x₀))
      (hq t (if t = 1 then ga else pow x₀)) 0 _ ?_).mono ?_
    · exact ⟨fun p => le_refl _, fun p => Nat.zero_le _⟩
    · simp only [Nat.zero_add, le_refl]


/-- **The DDH reduction** `acdDDHRed A`: the tree `acdDDHTreeOf` with the exponentiations of
the group and the delays `ΔFS = 1`, `ΔPCS = 2`, run as a distribution. -/
noncomputable def acdDDHRed {G : Type} [CG : CyclicGroup G]
    (A : CKACorruptAdv (G ⊕ CG.Exp) G G CG.Exp Bool) : G × G × G → SPComp Bool := fun tr =>
  liftPMF ((OracleAdv.run emptyOracle (acdDDHTreeOf CG.pow CyclicGroup.elemPow 1 2
    A.tStar A.play tr.1 tr.2.1 tr.2.2) ()).map Prod.fst)

/-- The DDH reduction for an adversary with output in `α` followed by the distinguisher `D`. -/
noncomputable def acdDDHRedA {G : Type} [CG : CyclicGroup G] {α : Type}
    (A : CKACorruptAdv (G ⊕ CG.Exp) G G CG.Exp α) (D : α → SPComp Bool) :
    G × G × G → SPComp Bool := fun tr =>
  SPComp.bind (liftPMF ((OracleAdv.run emptyOracle (acdDDHTreeOf CG.pow
    CyclicGroup.elemPow 1 2 A.tStar A.play tr.1 tr.2.1 tr.2.2) ()).map Prod.fst)) D

/-! ## The costed trees of the reductions -/

/-- The oracle tree without queries of the DDH reduction for an adversary with output in `α`:
on the triple `tr`, the tree `acdDDHTreeOf` with the delays `ΔFS = 1`, `ΔPCS = 2`. The
exponentiations `pow` and `epow` are parameters, so that their costs are parameters of the
derived costed tree. -/
noncomputable def acdDDHRedA.tree {E Gr α : Type} [Fintype E] [Nonempty E] [Fintype Gr]
    [Nonempty Gr] (pow : E → Gr) (epow : Gr → E → Gr) (tStar : PMF ℕ)
    (play : ℕ → Gr → OracleAdv CKAQuery (CKAAns (Gr ⊕ E) Gr Gr E) α) (tr : Gr × Gr × Gr) :
    OracleAdv Empty Unit α :=
  acdDDHTreeOf pow epow 1 2 tStar play tr.1 tr.2.1 tr.2.2

derive_timed acdDDHRedA.tree

/-- The oracle tree without queries of the DDH reduction for a Boolean adversary: the tree
`acdDDHRedA.tree` with output in `Bool`. -/
noncomputable def acdDDHRed.tree {E Gr : Type} [Fintype E] [Nonempty E] [Fintype Gr]
    [Nonempty Gr] (pow : E → Gr) (epow : Gr → E → Gr) (tStar : PMF ℕ)
    (play : ℕ → Gr → OracleAdv CKAQuery (CKAAns (Gr ⊕ E) Gr Gr E) Bool) (tr : Gr × Gr × Gr) :
    OracleAdv Empty Unit Bool :=
  acdDDHRedA.tree pow epow tStar play tr

derive_timed acdDDHRed.tree

/-- The derived costed tree of `acdDDHRed`, at a costed adversary `play` that erases to the
interaction of `A`, runs to `acdDDHRed A`. -/
theorem acdDDHRed.compile_tree {G : Type} [CG : CyclicGroup G]
    (A : CKACorruptAdv (G ⊕ CG.Exp) G G CG.Exp Bool) (powCost : CG.Exp → ℕ)
    (epowCost : G → CG.Exp → ℕ)
    (play : ℕ → G → OracleAdv.Timed CKAQuery (CKAAns (G ⊕ CG.Exp) G G CG.Exp) Bool)
    (playCost : ℕ → G → ℕ) (hplay : ∀ t g, (play t g).erase = A.play t g) (tr : G × G × G) :
    liftPMF ((OracleAdv.run emptyOracle (acdDDHRed.tree.timed CG.pow powCost
      CyclicGroup.elemPow epowCost A.tStar play playCost tr).2.erase ()).map Prod.fst) =
      acdDDHRed A tr := by
  rw [acdDDHRed.tree.erase_timed]
  have h : (fun t g => (play t g).erase) = A.play := funext fun t => funext (hplay t)
  rw [h]
  rfl

/-- **Time of `acdDDHRed`.** For a costed adversary of time at most `T`, at most `q` queries
and call cost at most `a`, and exponentiations of costs at most `P` and `X`, the derived
costed tree of the reduction has time at most
`T + ∑_{j < q} (3 P + X + 21 j + 51) + a + 4 P + 14`. -/
theorem acdDDHRed.timeBound_timed {E Gr : Type} [Fintype E] [Nonempty E] [Fintype Gr]
    [Nonempty Gr] (pow : E → Gr) (powCost : E → ℕ) (epow : Gr → E → Gr)
    (epowCost : Gr → E → ℕ) (tStar : PMF ℕ)
    (play : ℕ → Gr → OracleAdv.Timed CKAQuery (CKAAns (Gr ⊕ E) Gr Gr E) Bool)
    (playCost : ℕ → Gr → ℕ) (tr : Gr × Gr × Gr) {T q a P X : ℕ}
    (hA : ∀ t g, (play t g).TimeBound T) (hq : ∀ t g, (play t g).erase.IsQueryBound q)
    (ha : ∀ t g, playCost t g ≤ a) (hP : ∀ x, powCost x ≤ P) (hX : ∀ g x, epowCost g x ≤ X) :
    OracleAdv.Timed.StepTimeBound
      (acdDDHRed.tree.timed pow powCost epow epowCost tStar play playCost tr)
      (T + ∑ j ∈ Finset.range q, acdSimQueryTime P X j + a + 4 * P + 14) := by
  unfold acdDDHRed.tree.timed acdDDHRedA.tree.timed
  exact (OracleAdv.Timed.stepTimeBound_delay (OracleAdv.Timed.stepTimeBound_delay
    (acdDDHTreeOf.timeBound_timed pow powCost epow epowCost 1 2 tStar play playCost
      tr.1 tr.2.1 tr.2.2 hA hq ha hP hX))).mono (by omega)

/-- The derived costed tree of `acdDDHRedA`, at a costed adversary `play` that erases to the
interaction of `A`, runs and continues with `D` to `acdDDHRedA A D`. -/
theorem acdDDHRedA.compile_tree {G : Type} [CG : CyclicGroup G] {α : Type}
    (A : CKACorruptAdv (G ⊕ CG.Exp) G G CG.Exp α) (D : α → SPComp Bool)
    (powCost : CG.Exp → ℕ) (epowCost : G → CG.Exp → ℕ)
    (play : ℕ → G → OracleAdv.Timed CKAQuery (CKAAns (G ⊕ CG.Exp) G G CG.Exp) α)
    (playCost : ℕ → G → ℕ) (hplay : ∀ t g, (play t g).erase = A.play t g) (tr : G × G × G) :
    SPComp.bind (liftPMF ((OracleAdv.run emptyOracle (acdDDHRedA.tree.timed CG.pow
      powCost CyclicGroup.elemPow epowCost A.tStar play playCost tr).2.erase ()).map
        Prod.fst)) D = acdDDHRedA A D tr := by
  rw [acdDDHRedA.tree.erase_timed]
  have h : (fun t g => (play t g).erase) = A.play := funext fun t => funext (hplay t)
  rw [h]
  rfl

/-- **Time of `acdDDHRedA`.** The bound of `acdDDHRed.timeBound_timed` with one unit less: the
derived costed tree of the reduction, which the distinguisher `D` follows, has time at most
`T + ∑_{j < q} (3 P + X + 21 j + 51) + a + 4 P + 13`. -/
theorem acdDDHRedA.timeBound_timed {E Gr α : Type} [Fintype E] [Nonempty E] [Fintype Gr]
    [Nonempty Gr] (pow : E → Gr) (powCost : E → ℕ) (epow : Gr → E → Gr)
    (epowCost : Gr → E → ℕ) (tStar : PMF ℕ)
    (play : ℕ → Gr → OracleAdv.Timed CKAQuery (CKAAns (Gr ⊕ E) Gr Gr E) α)
    (playCost : ℕ → Gr → ℕ) (tr : Gr × Gr × Gr) {T q a P X : ℕ}
    (hA : ∀ t g, (play t g).TimeBound T) (hq : ∀ t g, (play t g).erase.IsQueryBound q)
    (ha : ∀ t g, playCost t g ≤ a) (hP : ∀ x, powCost x ≤ P) (hX : ∀ g x, epowCost g x ≤ X) :
    OracleAdv.Timed.StepTimeBound
      (acdDDHRedA.tree.timed pow powCost epow epowCost tStar play playCost tr)
      (T + ∑ j ∈ Finset.range q, acdSimQueryTime P X j + a + 4 * P + 13) := by
  unfold acdDDHRedA.tree.timed
  exact (OracleAdv.Timed.stepTimeBound_delay
    (acdDDHTreeOf.timeBound_timed pow powCost epow epowCost 1 2 tStar play playCost
      tr.1 tr.2.1 tr.2.2 hA hq ha hP hX)).mono (by omega)

/-! ## The proof -/

section ACDProof

variable {G : Type} [CG : CyclicGroup G] {α : Type}

/-- The run of the reduction tree is the run of the adversary against the simulation step. -/
theorem acdDDHTreeOf_run (ΔFS ΔPCS : ℕ) (tStar : PMF ℕ)
    (play : ℕ → G → OracleAdv CKAQuery (CKAAns (G ⊕ CG.Exp) G G CG.Exp) α) (ga gb z : G) :
    (OracleAdv.run emptyOracle (acdDDHTreeOf CG.pow CyclicGroup.elemPow ΔFS ΔPCS tStar
        play ga gb z) ()).map Prod.fst =
      tStar.bind fun t => (PMF.uniformFintype CG.Exp).bind fun x₀ =>
        (OracleAdv.run (OracleAdv.nfOracle (dhDraw G)
          (acdSimStepOf CG.pow CyclicGroup.elemPow ΔFS ΔPCS t ga gb z))
          (play t (if t = 1 then ga else CG.pow x₀))
          (CKAGameSt.init (if t = 1 then ga else CG.pow x₀)
            (.inl (if t = 1 then ga else CG.pow x₀)) (.inr x₀))).map Prod.fst := by
  unfold acdDDHTreeOf
  simp only [OracleAdv.run_rand, PMF.map_bind]
  congr 1; funext t; congr 1; funext x₀
  rw [OracleAdv.run_simulate_fst]
  have hsim : OracleAdv.simOracle (acdSimImplOf CG.pow CyclicGroup.elemPow ΔFS ΔPCS t ga
      gb z) emptyOracle = OracleAdv.nfOracle (dhDraw G) (fun σu q e =>
        ((acdSimStepOf CG.pow CyclicGroup.elemPow ΔFS ΔPCS t ga gb z σu.1 q e).1,
          ((acdSimStepOf CG.pow CyclicGroup.elemPow ΔFS ΔPCS t ga gb z σu.1 q e).2, ()))) := by
    funext σu q
    simp only [OracleAdv.simOracle, acdSimImplOf, OracleAdv.run_rand, OracleAdv.run_ret,
      OracleAdv.nfOracle, dhDraw_map, PMF.map_bind, PMF.pure_map]
  rw [hsim]
  exact OracleAdv.run_nf_map_fst_eq_of_rel (dhDraw G) _ _ (fun σu σ => σu.1 = σ)
    (fun σu σ h q e => by subst h; exact ⟨rfl, rfl⟩) _ _ _ rfl

/-- The real game of `acdCKA` with the delays `(1, 2)`, as a distribution, is the real DDH
distribution followed by the reduction tree. -/
theorem acdCKA_real_pmf (A : CKACorruptAdv (G ⊕ CG.Exp) G G CG.Exp α) :
    (A.tStar.bind fun t => acdGamePMF 1 2 t false (A.play t)) =
      ((PMF.uniformFintype CG.Exp).bind fun a => (PMF.uniformFintype CG.Exp).bind fun b =>
        PMF.pure (CG.pow a, CG.pow b, CG.pow (CG.expMul a b))).bind fun tr =>
          (OracleAdv.run emptyOracle (acdDDHTreeOf CG.pow CyclicGroup.elemPow 1 2
            A.tStar A.play tr.1 tr.2.1 tr.2.2) ()).map Prod.fst := by
  simp only [acdGamePMF_eager]
  simp only [acd_eager_eq_sim]
  simp only [PMF.bind_bind, PMF.pure_bind, acdDDHTreeOf_run, pow_dhX0, dhDraw_bind,
    PMF.bind_const, Bool.false_eq_true, ite_false]
  exact (bind_reorder _ _ _).symm

/-- The ideal game of `acdCKA` with the delays `(1, 2)`, as a distribution, is the ideal DDH
distribution followed by the reduction tree. -/
theorem acdCKA_ideal_pmf (A : CKACorruptAdv (G ⊕ CG.Exp) G G CG.Exp α) :
    (A.tStar.bind fun t => acdGamePMF 1 2 t true (A.play t)) =
      ((PMF.uniformFintype CG.Exp).bind fun a => (PMF.uniformFintype CG.Exp).bind fun b =>
        (PMF.uniformFintype CG.Exp).bind fun c =>
          PMF.pure (CG.pow a, CG.pow b, CG.pow c)).bind fun tr =>
          (OracleAdv.run emptyOracle (acdDDHTreeOf CG.pow CyclicGroup.elemPow 1 2
            A.tStar A.play tr.1 tr.2.1 tr.2.2) ()).map Prod.fst := by
  simp only [acdGamePMF_eager]
  simp only [acd_eager_eq_sim]
  simp only [PMF.bind_bind, PMF.pure_bind, acdDDHTreeOf_run, pow_dhX0, dhDraw_bind,
    PMF.bind_const, ite_true]
  exact bind_reorder_ideal _ _

/-- **CKA security of `acdCKA` with state corruption and randomness leakage, with a
distinguisher.** For every adversary `A` with output in `α` and every distinguisher `D`, the
corruption advantage of `acdCKA` with forward-secrecy delay `1` and post-compromise delay `2`
equals the DDH advantage of the reduction `acdDDHRedA A D`. -/
theorem acdCKA_corrupt_advantageA_eq_ddh (A : CKACorruptAdv (G ⊕ CG.Exp) G G CG.Exp α)
    (D : α → SPComp Bool) :
    CKA_Corrupt_AdvantageA (acdCKA G) 1 2 A D = DDH_Advantage G (acdDDHRedA A D) := by
  unfold CKA_Corrupt_AdvantageA DDH_Advantage AdvantageA cka_corrupt_real cka_corrupt_ideal
    acdDDHRedA
  rw [acdCKA_game_eq, acdCKA_game_eq, acdCKA_real_pmf, acdCKA_ideal_pmf, DDH_real_eq_liftPMF,
    DDH_ideal_eq_liftPMF]
  simp only [← SPComp.bind_assoc, liftPMF_bind_liftPMF]

/-- **CKA security of `acdCKA` with state corruption and randomness leakage.** For every
adversary `A`, the corruption advantage of `acdCKA` with forward-secrecy delay `1` and
post-compromise delay `2` equals the DDH advantage of the reduction `acdDDHRed A`. -/
theorem acdCKA_corrupt_advantage_eq_ddh (A : CKACorruptAdv (G ⊕ CG.Exp) G G CG.Exp Bool) :
    CKA_Corrupt_Advantage (acdCKA G) 1 2 A = DDH_Advantage G (acdDDHRed A) := by
  unfold CKA_Corrupt_Advantage DDH_Advantage AdvantageA cka_corrupt_real cka_corrupt_ideal
    acdDDHRed
  rw [acdCKA_game_eq, acdCKA_game_eq, acdCKA_real_pmf, acdCKA_ideal_pmf, DDH_real_eq_liftPMF,
    DDH_ideal_eq_liftPMF]
  simp only [liftPMF_bind_liftPMF]

/-- **CKA security of `acdCKA`**, as a bound: the corruption advantage with forward-secrecy
delay `1` and post-compromise delay `2` is at most the DDH advantage of `acdDDHRed A`. -/
theorem acdCKA_corrupt_advantage_le (A : CKACorruptAdv (G ⊕ CG.Exp) G G CG.Exp Bool) :
    CKA_Corrupt_Advantage (acdCKA G) 1 2 A ≤ DDH_Advantage G (acdDDHRed A) :=
  le_of_eq (acdCKA_corrupt_advantage_eq_ddh A)

/-- **Passive CKA security of `acdCKA`.** The passive CKA advantage of the distinguisher `D` at
the challenge epoch `k + 1` with `m` epochs after it is the DDH advantage of the reduction at
the passive adversary `ckaPassiveAdv k m`, which neither corrupts nor leaks. -/
theorem acdCKA_advantage_eq_ddh (k m : ℕ) (D : CKAView G G → SPComp Bool) :
    CKA_Advantage (acdCKA G) k m D =
      DDH_Advantage G (acdDDHRedA (ckaPassiveAdv (Rand := CG.Exp) k m) D) :=
  (cka_advantage_eq_corrupt (acdCKA G) 1 2 k m D).trans (acdCKA_corrupt_advantageA_eq_ddh _ D)

end ACDProof

end CatCrypt.Crypto.Messaging
