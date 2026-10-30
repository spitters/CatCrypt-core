/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.KeySchedule
public import CatCryptCore.Crypto.UCOracleGame
public import CatCryptCore.Crypto.UCChannel

/-!
# A secure channel from a KEM, a key schedule and an AEAD, as a square

The record layer of `CatCryptCore.Crypto.AKE.KeySchedule` as a reactive system on the
port-typed interface of the ideal channel `FChan` of `CatCryptCore.Crypto.UCChannel`: honest
events `ChanHEv W` on the left port, adversary events `ChanAEv W` on the right port.

The protocol `secReal S side ctx F D N ad` runs the key exchange at the first adversary event:
key generation and encapsulation of the KEM `S`, the side computation `side`, and the traffic key
`F ss (ctx pk c t z)`. The sender keeps the messages sent and not yet delivered or dropped; an
adversary `poll` transmits the next message not yet transmitted, encrypted under the traffic key
with the associated data `ad seq`, where `seq` counts the messages transmitted, and shows the
transcript `(pk, c, t)` with the ciphertext. The wire is authenticated: the adversary delivers
or drops the oldest transmitted message and cannot tamper. On delivery the receiver decrypts the
ciphertext with the associated data of its position and appends the plaintext to its inbox. The
sender transmits at most `N` messages; `ad` is injective below `N`, so every encryption has
fresh associated data.

The protocol is an oracle protocol (`OProt` of `CatCryptCore.Crypto.UCOracleGame`) over the
authenticated-encryption oracles, keyed by the transcript and the traffic key. Every environment
`Z` compiles to the channel adversary `chanAdv N ad Z` of `KeySchedule`, which runs `Z` against
the protocol with the AEAD calls asked as oracle queries; the distance between the protocol over
the real AEAD and the protocol over the ideal AEAD oracles is the channel advantage of
`chanAdv N ad Z` (`adv_secReal_secIdeal`).

Over the ideal oracles, the protocol is the ideal secure channel `FChan ChannelCap.secure ℓ`
behind the simulator `secSim`, the forwarding simulator on the honest port tensored with the
adversary-port simulator `secSimA` of fuel `0`: it samples a transcript at its first activation,
shows a uniform ciphertext for every message the channel lets it observe (at most `N`), and
forwards the delivery or drop of an observed message. The fresh associated data makes every
ideal encryption a uniform ciphertext and every decryption of a transmitted ciphertext the
transmitted plaintext.

## Main definitions

* `SecSt`, `secProg`, `secProt`: the protocol state and its activations as oracle programs.
* `secKeyed`, `secReal`, `idealSys`, `secIdeal`: the protocol over the real and the ideal AEAD
  oracles, with the key exchange run at the first adversary event.
* `AdInj N ad`, `SecInv`: injectivity of the associated data below `N`, and the invariant of the
  protocol state and the log of the ideal oracles.
* `chanAdv N ad Z`: the channel adversary of the environment `Z`.
* `SimSt`, `secSimA`, `secSim`: the adversary-port simulator and its tensor with the forwarding
  simulator.

## Main results

* `adv_secReal_secIdeal`: the advantage of `Z` between the real and the ideal protocol is the
  channel advantage of `chanAdv N ad Z`.
* `idealSys_realizes_secure`: the protocol over the ideal oracles realizes
  `FChan ChannelCap.secure ℓ` behind `secSim` at distance `0`, by a state map on the invariant
  `SecInv`.
* `secReal_realizesSim_secure`: the protocol realizes `FChan ChannelCap.secure ℓ` behind
  `secSim`, with bound at `Z` the KEM IND-CCA advantage of `kemRed`, the dual-PRF advantage of
  `prfRed` and the AEAD advantage of `aeadRed`, each of the channel adversary of `Z`.
* `secRealSalt_realizesSim_secure`: the instance with a single KEM and a transcript-bound salt
  (the key schedule of TLS 1.3).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.ChannelSquare

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open CatCrypt.NonUniform CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent
open CatCrypt.Crypto.KEM.Games CatCrypt.Crypto.PRPPRF CatCrypt.Crypto.AKE.KeySchedule
open CatCrypt.Crypto.Choreography (ChannelCap)
open scoped ENNReal

/-! ## Sampling from a probability mass function -/

section Sampling

variable {α β : Type}

private theorem sampleFrom_ofPMF_pure (a : α) :
    sampleFrom (ofPMF (PMF.pure a)) = SPComp.pure a := by
  rw [ofPMF, PMF.pure_map]
  exact sampleFrom_pure a

private theorem sampleFrom_ofPMF_bind' (p : PMF α) (f : α → PMF β) :
    sampleFrom (ofPMF (p.bind f)) =
      SPComp.bind (sampleFrom (ofPMF p)) fun a => sampleFrom (ofPMF (f a)) := by
  rw [sampleFrom_bind_sampleFrom]
  congr 1
  simp only [ofPMF, CatCrypt.Prob.SDistr.bind, PMF.map_bind, PMF.bind_map, Function.comp_def]

private theorem sampleFrom_ofPMF_map' (p : PMF α) (g : α → β) :
    sampleFrom (ofPMF (p.map g)) =
      SPComp.bind (sampleFrom (ofPMF p)) fun a => SPComp.pure (g a) := by
  rw [← PMF.bind_pure_comp, sampleFrom_ofPMF_bind']
  simp only [Function.comp_apply, sampleFrom_ofPMF_pure]

private theorem sampleFrom_ofPMF_noFail' (μ : PMF α) : SPComp.NoFail (sampleFrom (ofPMF μ)) := by
  intro h
  simp only [sampleFrom_apply, SDistr.bind, PMF.bind_apply]
  refine ENNReal.tsum_eq_zero.2 fun o => ?_
  rcases o with _ | a
  · simp
  · simp [SDistr.pure, PMF.pure_apply]

end Sampling

/-! ## The protocol -/

section Protocol

variable {W Ct Tr : Type}

/-- The state of the secure-channel protocol. -/
structure SecSt (W Ct : Type) where
  /-- The messages sent and not yet delivered or dropped, oldest first; the first
  `wire.length` of them are transmitted. -/
  queue : List W
  /-- The ciphertexts on the wire, oldest first. -/
  wire : List Ct
  /-- The number of messages transmitted. -/
  seq : ℕ
  /-- The received plaintexts not yet read, oldest first. -/
  inbox : List W

/-- The initial state: nothing sent, transmitted or received. -/
def SecSt.init : SecSt W Ct := ⟨[], [], 0, []⟩

/-- The events of the protocol: honest events on the left, adversary events on the right. -/
abbrev SecEv (W : Type) := ChanHEv W ⊕ ChanAEv W

/-- The outputs of the protocol: a poll shows the transcript and a ciphertext. -/
abbrev SecOut (W Tr Ct : Type) := ChanHOut W ⊕ ChanAOut (Tr × Ct) Empty

/-- The queries of the protocol to the AEAD oracles. -/
abbrev SecQ (W Ct : Type) := AEAD_CCA_Query W Ct

/-- The answers of the AEAD oracles. -/
abbrev SecA (W Ct : Type) := AEAD_CCA_Answer W Ct

/-- A step of the honest port: `send` appends to the sender's queue, `recv` takes the oldest
received plaintext. -/
def honStep (t : SecSt W Ct) : ChanHEv W → SecSt W Ct × ChanHOut W
  | .send v => (⟨t.queue ++ [v], t.wire, t.seq, t.inbox⟩, .ok)
  | .recv => (⟨t.queue, t.wire, t.seq, t.inbox.tail⟩, .got t.inbox.head?)

/-- The state after the oldest transmitted message leaves the wire, with `r` appended to the
inbox. -/
def pop (t : SecSt W Ct) (r : Option W) : SecSt W Ct :=
  ⟨t.queue.tail, t.wire.tail, t.seq, t.inbox ++ r.toList⟩

/-- The state and output after an encryption query with answer `a`. -/
def afterEnc (tr : Tr) (t : SecSt W Ct) : SecA W Ct → SecSt W Ct × SecOut W Tr Ct
  | .inl c => (⟨t.queue, t.wire ++ [c], t.seq + 1, t.inbox⟩, .inr (.leak (some (.inl (tr, c)))))
  | .inr _ => (t, .inr (.leak none))

/-- The plaintext of a decryption answer. -/
def decOf : SecA W Ct → Option W
  | .inl _ => none
  | .inr r => r

/-- The next message to transmit: the first message of the queue not yet transmitted, while
fewer than `N` messages have been transmitted. -/
def nextMsg (N : ℕ) (t : SecSt W Ct) : Option W :=
  if t.seq < N then t.queue[t.wire.length]? else none

/-- The associated data of the oldest message on the wire: its position `seq - wire.length`. -/
def headAd (ad : ℕ → W) (t : SecSt W Ct) : W := ad (t.seq - t.wire.length)

/-- One activation of the protocol with transcript `tr` as an oracle program. A `poll`
encrypts the next message with the associated data `ad seq`; a `deliver` decrypts the oldest
ciphertext on the wire; `drop` removes it; `tamper` and `idle` change nothing. -/
def secProg (N : ℕ) (ad : ℕ → W) (tr : Tr) (t : SecSt W Ct) :
    SecEv W → OracleAdv (SecQ W Ct) (SecA W Ct) (SecSt W Ct × SecOut W Tr Ct)
  | .inl e => .ret ((honStep t e).1, .inl (honStep t e).2)
  | .inr .poll => match nextMsg N t with
    | some v => .query (.inl (v, ad t.seq)) fun a => .ret (afterEnc tr t a)
    | none => .ret (t, .inr (.leak none))
  | .inr .deliver => match t.wire with
    | c :: _ => .query (.inr (c, headAd ad t)) fun a => .ret (pop t (decOf a), .inr .ack)
    | [] => .ret (t, .inr .ack)
  | .inr .drop => match t.wire with
    | _ :: _ => .ret (pop t none, .inr .ack)
    | [] => .ret (t, .inr .ack)
  | .inr (.tamper _) => .ret (t, .inr .ack)
  | .inr .idle => .ret (t, .inr .ack)

/-- The protocol with transcript `tr` as an oracle protocol over the AEAD oracles. -/
def secProt (N : ℕ) (ad : ℕ → W) (tr : Tr) :
    OProt (SecSt W Ct) (SecEv W) (SecOut W Tr Ct) (SecQ W Ct) (SecA W Ct) where
  init := SecSt.init
  step := secProg N ad tr

/-- The protocol as a keyed system: with key `k` the programs of `secProt N ad (trOf k)` run
against the oracle `orc k` from the state `s₀`; only the adversary events read the key. -/
noncomputable def secKeyed {K S : Type} (N : ℕ) (ad : ℕ → W) (trOf : K → Tr)
    (orc : K → S → SecQ W Ct → PMF (SecA W Ct × S)) (s₀ : S) :
    KeyedSys K (SecSt W Ct × S) (SecEv W) (SecOut W Tr Ct) where
  init := (SecSt.init, s₀)
  step k := (secProt N ad (trOf k)).plugStep (orc k)
  step₀ t
    | .inl e => SPComp.pure (((honStep t.1 e).1, t.2), .inl (honStep t.1 e).2)
    | .inr _ => SPComp.fail
  uses _ e := e.isRight

/-- The honest activations do not read the key. -/
theorem secKeyed_step_honest {K S : Type} (N : ℕ) (ad : ℕ → W) (trOf : K → Tr)
    (orc : K → S → SecQ W Ct → PMF (SecA W Ct × S)) (s₀ : S) (k : K)
    (t : SecSt W Ct × S) (e : SecEv W) (hu : (secKeyed N ad trOf orc s₀).uses t e = false) :
    (secKeyed N ad trOf orc s₀).step k t e = (secKeyed N ad trOf orc s₀).step₀ t e := by
  rcases e with e | e
  · simp [secKeyed, secProt, secProg, OProt.plugStep, sampleFrom_ofPMF_pure]
  · simp [secKeyed] at hu

/-- The acceptance probability of `Z` against the lazily keyed protocol is the probability that
the reduction of `Z` outputs `true` against the oracle of a key sampled from `μ`. -/
theorem prTrue_view_secKeyed {K S ζ : Type} (N : ℕ) (ad : ℕ → W) (trOf : K → Tr)
    (orc : K → S → SecQ W Ct → PMF (SecA W Ct × S)) (s₀ : S) (μ : PMF K)
    (Zv : Env (Strat ζ (SecEv W) (SecOut W Tr Ct)) ζ) :
    prTrue (SPComp.bind (view ((secKeyed N ad trOf orc s₀).lazy μ) Zv.input) Zv.dist) Zv.heap =
      (μ.bind fun k =>
        (OracleAdv.run (orc k) ((secProt N ad (trOf k)).reduction Zv) s₀).map Prod.fst) true := by
  rw [KeyedSys.view_lazy _ _ (secKeyed_step_honest N ad trOf orc s₀), SPComp.bind_assoc,
    prTrue_bind_sampleFrom, PMF.bind_apply]
  refine tsum_congr fun k => ?_
  rw [ofPMF_apply_some]
  congr 1
  exact (secProt N ad (trOf k)).prTrue_view_plug (orc k) s₀ Zv

end Protocol

/-! ## The protocol over the real and the ideal AEAD -/

section Worlds

variable {W Ct PK SK SS C T Z X : Type} [SampleableType W] [SampleableType Ct]

/-- The distribution of the transcript and the traffic key of the key exchange. -/
noncomputable def realKeyDist (S : Scheme PK SK SS C) (side : PMF (T × Z))
    (ctx : PK → C → T → Z → X) (F : SS → X → W) : PMF ((PK × C × T) × W) :=
  S.keygen.bind fun ks => (S.encaps ks.1).bind fun x => side.bind fun tz =>
    PMF.pure ((ks.1, x.2, tz.1), F x.1 (ctx ks.1 x.2 tz.1 tz.2))

/-- The distribution of the transcript of the key exchange. -/
noncomputable def trDist (S : Scheme PK SK SS C) (side : PMF (T × Z)) : PMF (PK × C × T) :=
  S.keygen.bind fun ks => (S.encaps ks.1).bind fun x => side.bind fun tz =>
    PMF.pure (ks.1, x.2, tz.1)

/-- The protocol over the ideal AEAD oracles with the transcript sampled from `μ` at the first
adversary event. -/
noncomputable def idealSys {Tr : Type} (N : ℕ) (ad : ℕ → W) (μ : PMF Tr) :
    Sys (Option Tr × (SecSt W Ct × List ((W × W) × Ct))) (SecEv W) (SecOut W Tr Ct) :=
  (secKeyed N ad id (fun _ => aeadIdealOracle) []).lazy μ

/-- **The secure-channel protocol**: the key exchange of `S`, `side`, `ctx` and `F` at the first
adversary event, and the record layer under the real AEAD `D` with the traffic key. -/
noncomputable def secReal (S : Scheme PK SK SS C) (side : PMF (T × Z))
    (ctx : PK → C → T → Z → X) (F : SS → X → W) (D : AEADDef W Ct) (N : ℕ) (ad : ℕ → W) :
    Sys (Option ((PK × C × T) × W) × (SecSt W Ct × Unit)) (SecEv W) (SecOut W (PK × C × T) Ct) :=
  (secKeyed N ad Prod.fst (fun k => aeadRealOracle D k.2) ()).lazy (realKeyDist S side ctx F)

/-- The protocol over the ideal AEAD oracles: the transcript of the key exchange at the first
adversary event, and the record layer over `aeadIdealOracle` from the empty log. -/
noncomputable def secIdeal (S : Scheme PK SK SS C) (side : PMF (T × Z)) (N : ℕ) (ad : ℕ → W) :
    Sys (Option (PK × C × T) × (SecSt W Ct × List ((W × W) × Ct))) (SecEv W)
      (SecOut W (PK × C × T) Ct) :=
  idealSys N ad (trDist S side)

/-- **The channel adversary of the environment `Z`**: on the transcript `(pk, c, t)`, the
reduction of `Z` against the protocol with that transcript, which asks the AEAD calls of the
protocol as oracle queries. -/
noncomputable def chanAdv {ζ : Type} (N : ℕ) (ad : ℕ → W)
    (Zv : Env (Strat ζ (SecEv W) (SecOut W (PK × C × T) Ct)) ζ) :
    PK → C → T → AEAD_CCA_Adversary W Ct :=
  fun pk c t => (secProt N ad (pk, c, t)).reduction Zv

omit [SampleableType Ct] in
/-- The acceptance probability of `Z` against the protocol over the real AEAD is the real
channel game of `chanAdv N ad Z`. -/
theorem prTrue_view_secReal {ζ : Type} (S : Scheme PK SK SS C) (side : PMF (T × Z))
    (ctx : PK → C → T → Z → X) (F : SS → X → W) (D : AEADDef W Ct) (N : ℕ) (ad : ℕ → W)
    (Zv : Env (Strat ζ (SecEv W) (SecOut W (PK × C × T) Ct)) ζ) :
    prTrue (SPComp.bind (view (secReal S side ctx F D N ad) Zv.input) Zv.dist) Zv.heap =
      channelReal S side ctx F D (chanAdv N ad Zv) true := by
  rw [secReal, prTrue_view_secKeyed]
  simp [realKeyDist, channelReal, chanAdv, aeadRealRun, PMF.bind_bind, PMF.pure_bind]

/-- The acceptance probability of `Z` against the protocol over the ideal AEAD oracles is the
ideal channel game of `chanAdv N ad Z`. -/
theorem prTrue_view_secIdeal {ζ : Type} (S : Scheme PK SK SS C) (side : PMF (T × Z))
    (N : ℕ) (ad : ℕ → W) (Zv : Env (Strat ζ (SecEv W) (SecOut W (PK × C × T) Ct)) ζ) :
    prTrue (SPComp.bind (view (secIdeal (Ct := Ct) S side N ad) Zv.input) Zv.dist) Zv.heap =
      channelIdeal S side (chanAdv N ad Zv) true := by
  rw [secIdeal, idealSys, prTrue_view_secKeyed]
  simp [trDist, channelIdeal, chanAdv, aeadIdealRun, PMF.bind_bind, PMF.pure_bind]

/-- **Real to ideal AEAD.** The advantage of `Z` between the protocol over the real AEAD and the
protocol over the ideal AEAD oracles is the channel advantage of `chanAdv N ad Z`. -/
theorem adv_secReal_secIdeal {ζ : Type} (S : Scheme PK SK SS C) (side : PMF (T × Z))
    (ctx : PK → C → T → Z → X) (F : SS → X → W) (D : AEADDef W Ct) (N : ℕ) (ad : ℕ → W)
    (Zv : Env (Strat ζ (SecEv W) (SecOut W (PK × C × T) Ct)) ζ) :
    adv (secReal S side ctx F D N ad) (secIdeal S side N ad) Zv =
      channelAdvantage S side ctx F D (chanAdv N ad Zv) := by
  rw [adv_eq, prTrue_view_secReal, prTrue_view_secIdeal, channelAdvantage, Advantage,
    prTrue_liftPMF, prTrue_liftPMF]
  rfl

end Worlds

/-! ## The simulator -/

section Simulator

variable {W Ct Tr Leak : Type} [SampleableType Ct]

/-- The state of the adversary-port simulator: the transcript once sampled, the number of
ciphertexts shown, and the number of shown messages still on the wire. -/
structure SimSt (Tr : Type) where
  /-- The simulated transcript. -/
  tr : Option Tr
  /-- The number of ciphertexts shown. -/
  cnt : ℕ
  /-- The number of shown messages not yet delivered or dropped. -/
  shown : ℕ

/-- The transcript of the simulator: the stored one, or a sample from `μ`. -/
noncomputable def drawTr (μ : PMF Tr) : Option Tr → SPComp Tr
  | some tr => SPComp.pure tr
  | none => sampleFrom (ofPMF μ)

/-- The simulator's decision on an adversary event with the transcript `tr`: forward a poll
while fewer than `N` ciphertexts are shown, forward the delivery or drop of a shown message, and
answer every other event itself. -/
def simDecide (N : ℕ) (tr : Tr) (s : SimSt Tr) :
    ChanAEv W → SimSt Tr × (ChanAEv W ⊕ ChanAOut (Tr × Ct) Empty)
  | .poll => (⟨some tr, s.cnt, s.shown⟩,
      if s.cnt < N then .inl .poll else .inr (.leak none))
  | .deliver => (⟨some tr, s.cnt, s.shown⟩, if 0 < s.shown then .inl .deliver else .inr .ack)
  | .drop => (⟨some tr, s.cnt, s.shown⟩, if 0 < s.shown then .inl .drop else .inr .ack)
  | .tamper _ => (⟨some tr, s.cnt, s.shown⟩, .inr .ack)
  | .idle => (⟨some tr, s.cnt, s.shown⟩, .inr .ack)

/-- The simulator's output from an answer of the secure channel: an observed message becomes a
uniform ciphertext shown with the transcript; an acknowledgement of a delivery or drop removes a
shown message. -/
noncomputable def simFinish (s : SimSt Tr) :
    ChanAOut W Leak → SPComp (SimSt Tr × ChanAOut (Tr × Ct) Empty)
  | .leak (some _) => match s.tr with
    | some tr => SPComp.bind (sampleFrom (ofPMF (PMF.uniformFintype Ct))) fun c =>
        SPComp.pure (⟨s.tr, s.cnt + 1, s.shown + 1⟩, .leak (some (.inl (tr, c))))
    | none => SPComp.pure (s, .leak none)
  | .leak none => SPComp.pure (s, .leak none)
  | .ack => SPComp.pure (⟨s.tr, s.cnt, s.shown - 1⟩, .ack)

/-- `simFinish` never fails. -/
theorem simFinish_noFail (s : SimSt Tr) (o : ChanAOut W Leak) :
    SPComp.NoFail (simFinish (Ct := Ct) s o) := by
  rcases o with _ | (_ | _)
  · exact SPComp.pure_noFail _
  · exact SPComp.pure_noFail _
  · rcases s with ⟨_ | tr, n, m⟩
    · exact SPComp.pure_noFail _
    · simp only [simFinish]
      exact Assumptions.SPComp.bind_noFail (sampleFrom_ofPMF_noFail' _) fun _ =>
        SPComp.pure_noFail _

/-- `drawTr` never fails. -/
theorem drawTr_noFail (μ : PMF Tr) (o : Option Tr) : SPComp.NoFail (drawTr μ o) := by
  rcases o with _ | tr
  · exact sampleFrom_ofPMF_noFail' μ
  · exact SPComp.pure_noFail _

/-- **The adversary-port simulator**, of fuel `0`: it samples the transcript from `μ` at its
first activation, shows a uniform ciphertext for each of the first `N` messages the secure
channel lets it observe, and forwards the delivery or drop of a shown message. -/
noncomputable def secSimA (N : ℕ) (μ : PMF Tr) :
    MultiHybrid (SimSt Tr) (ChanAEv W) (ChanAOut (Tr × Ct) Empty) (ChanAEv W)
      (ChanAOut W Leak) where
  init := ⟨none, 0, 0⟩
  fuel := 0
  start s e := SPComp.bind (drawTr μ s.tr) fun tr => SPComp.pure (simDecide N tr s e)
  resume s o := SPComp.map (fun p => (p.1, .inr p.2)) (simFinish s o)
  finish := simFinish
  start_noFail s _ := Assumptions.SPComp.bind_noFail (drawTr_noFail μ s.tr) fun _ =>
    SPComp.pure_noFail _
  resume_noFail s o := Assumptions.SPComp.bind_noFail (simFinish_noFail s o) fun _ =>
    SPComp.pure_noFail _
  finish_noFail := simFinish_noFail

/-- **The simulator of the secure channel**: the forwarding simulator on the honest port
tensored with `secSimA N μ` on the adversary port. -/
noncomputable def secSim (N : ℕ) (μ : PMF Tr) (ℓ : W → Leak) :
    Simulator (ChanHEv W ⊕ ChanAEv W) (ChanHOut W ⊕ ChanAOut (Tr × Ct) Empty)
      (ChanHEv W ⊕ ChanAEv W) (ChanHOut W ⊕ ChanAOut W Leak)
      ((honView ChannelCap.secure ℓ).sum PubView.eqView)
      ((honView ChannelCap.secure ℓ).sum PubView.eqView) :=
  Simulator.tensor (MultiHybrid.idSim (ChanHEv W) (ChanHOut W)) (secSimA N μ)
    (MultiHybrid.idSim_opaque (honView ChannelCap.secure ℓ)) (secSimA N μ).opaque_eqView

end Simulator

/-! ## Activations over the ideal AEAD oracles -/

section IdealSteps

variable {W Ct Tr : Type} [SampleableType W] [SampleableType Ct]

/-- The log of the ideal AEAD oracles. -/
abbrev Log (W Ct : Type) := List ((W × W) × Ct)

/-- The result of an adversary activation over the ideal AEAD oracles from the protocol state and
log `x`, for every activation except a poll that transmits: a delivery decrypts from the log. -/
def detStep (ad : ℕ → W) (x : SecSt W Ct × Log W Ct) :
    ChanAEv W → (SecSt W Ct × Log W Ct) × SecOut W Tr Ct
  | .deliver => match x.1.wire with
    | c :: _ => ((pop x.1 (aeadLogDecrypt x.2 c (headAd ad x.1)), x.2), .inr .ack)
    | [] => (x, .inr .ack)
  | .drop => match x.1.wire with
    | _ :: _ => ((pop x.1 none, x.2), .inr .ack)
    | [] => (x, .inr .ack)
  | .poll => (x, .inr (.leak none))
  | .tamper _ => (x, .inr .ack)
  | .idle => (x, .inr .ack)

/-- An adversary activation that does not transmit is deterministic over the ideal oracles. -/
theorem plugStep_ideal_det (N : ℕ) (ad : ℕ → W) (tr : Tr) (x : SecSt W Ct × Log W Ct)
    (e : ChanAEv W) (he : e = .poll → nextMsg N x.1 = none) :
    (secProt N ad tr).plugStep aeadIdealOracle x (.inr e) =
      SPComp.pure (detStep ad x e) := by
  rcases x with ⟨t, log⟩
  cases e with
  | poll => simp [OProt.plugStep, secProt, secProg, he rfl, detStep, sampleFrom_ofPMF_pure]
  | deliver =>
    rcases hw : t.wire with _ | ⟨c, cs⟩ <;>
      simp [OProt.plugStep, secProt, secProg, hw, detStep, aeadIdealOracle, decOf,
        sampleFrom_ofPMF_pure]
  | drop =>
    rcases hw : t.wire with _ | ⟨c, cs⟩ <;>
      simp [OProt.plugStep, secProt, secProg, hw, detStep, sampleFrom_ofPMF_pure]
  | tamper v => simp [OProt.plugStep, secProt, secProg, detStep, sampleFrom_ofPMF_pure]
  | idle => simp [OProt.plugStep, secProt, secProg, detStep, sampleFrom_ofPMF_pure]

/-- A poll that transmits the message `v` with fresh associated data samples a uniform
ciphertext and records it in the log. -/
theorem plugStep_ideal_fresh (N : ℕ) (ad : ℕ → W) (tr : Tr) (x : SecSt W Ct × Log W Ct) (v : W)
    (hn : nextMsg N x.1 = some v) (hl : x.2.lookup (v, ad x.1.seq) = none) :
    (secProt N ad tr).plugStep aeadIdealOracle x (.inr .poll) =
      SPComp.bind (sampleFrom (ofPMF (PMF.uniformFintype Ct))) fun c =>
        SPComp.pure ((⟨x.1.queue, x.1.wire ++ [c], x.1.seq + 1, x.1.inbox⟩,
          ((v, ad x.1.seq), c) :: x.2), .inr (.leak (some (.inl (tr, c))))) := by
  rcases x with ⟨t, log⟩
  simp only [OProt.plugStep, secProt, secProg, hn, OracleAdv.run_query, aeadIdealOracle, hl,
    OracleAdv.run_ret, PMF.bind_map, Function.comp_def, afterEnc]
  rw [sampleFrom_ofPMF_bind']
  simp only [sampleFrom_ofPMF_pure, SPComp.bind_assoc, SPComp.pure_bind]

/-- The invariant of the protocol over the ideal oracles: at most `N` messages transmitted;
every logged encryption has the associated data of a transmitted position; and the `j`-th
message on the wire is logged with the associated data of its position, as the only logged
entry with that associated data. -/
def SecInv (N : ℕ) (ad : ℕ → W) (t : SecSt W Ct) (log : Log W Ct) : Prop :=
  t.seq ≤ N ∧ t.wire.length ≤ t.queue.length ∧ t.wire.length ≤ t.seq ∧
  (∀ e ∈ log, ∃ i < t.seq, e.1.2 = ad i) ∧
  ∀ j < t.wire.length, ∃ v c, t.queue[j]? = some v ∧ t.wire[j]? = some c ∧
    ((v, ad (t.seq - t.wire.length + j)), c) ∈ log ∧
    ∀ e ∈ log, e.1.2 = ad (t.seq - t.wire.length + j) →
      e = ((v, ad (t.seq - t.wire.length + j)), c)

/-- The associated data `ad` is injective below `N`. -/
def AdInj (N : ℕ) (ad : ℕ → W) : Prop := ∀ i j, i < N → j < N → ad i = ad j → i = j

/-- The invariant holds initially. -/
theorem secInv_init (N : ℕ) (ad : ℕ → W) : SecInv N ad (SecSt.init : SecSt W Ct) [] := by
  simp [SecInv, SecSt.init]

omit [SampleableType Ct] in
/-- Under the invariant, the associated data of the next transmission is fresh. -/
theorem lookup_fresh {N : ℕ} {ad : ℕ → W} (had : AdInj N ad) {t : SecSt W Ct} {log : Log W Ct}
    (hI : SecInv N ad t log) (hs : t.seq < N) (v : W) :
    log.lookup (v, ad t.seq) = none := by
  rw [List.lookup_eq_none_iff]
  intro e he
  obtain ⟨-, -, -, hlog, -⟩ := hI
  obtain ⟨i, hi, hie⟩ := hlog e he
  grind [AdInj]

/-- Under the invariant, the decryption of the oldest ciphertext on the wire with the associated
data of its position is the oldest message of the queue. -/
theorem logDecrypt_head {N : ℕ} {ad : ℕ → W} {t : SecSt W Ct} {log : Log W Ct}
    (hI : SecInv N ad t log) {c : Ct} {cs : List Ct} (hw : t.wire = c :: cs) :
    aeadLogDecrypt log c (headAd ad t) = t.queue.head? := by
  obtain ⟨-, -, -, -, hdec⟩ := hI
  obtain ⟨v, c', hv, hc, hmem, huniq⟩ := hdec 0 (by simp [hw])
  simp only [hw, List.getElem?_cons_zero, Option.some.injEq, Nat.add_zero] at hc hmem huniq
  subst hc
  have hfind : log.find? (fun e => decide (e.2 = c ∧ e.1.2 = headAd ad t)) =
      some ((v, headAd ad t), c) := by
    have hex : ∃ e ∈ log, (fun e => decide (e.2 = c ∧ e.1.2 = headAd ad t)) e = true :=
      ⟨_, hmem, by simp [headAd, hw]⟩
    obtain ⟨e', he'⟩ := Option.isSome_iff_exists.1 (List.find?_isSome.2 hex)
    have hp := List.find?_some he'
    simp only [decide_eq_true_eq] at hp
    rw [he', huniq e' (List.mem_of_find?_eq_some he') (by simpa [headAd, hw] using hp.2)]
    simp [headAd, hw]
  rw [aeadLogDecrypt, hfind, List.head?_eq_getElem?, hv]
  rfl

omit [SampleableType W] [SampleableType Ct] in
/-- An honest step preserves the invariant. -/
theorem secInv_honStep {N : ℕ} {ad : ℕ → W} {t : SecSt W Ct} {log : Log W Ct}
    (hI : SecInv N ad t log) (e : ChanHEv W) : SecInv N ad (honStep t e).1 log := by
  cases e <;> grind [SecInv, honStep]

omit [SampleableType W] [SampleableType Ct] in
/-- Removing the oldest message from the wire preserves the invariant. -/
theorem secInv_pop {N : ℕ} {ad : ℕ → W} {t : SecSt W Ct} {log : Log W Ct}
    (hI : SecInv N ad t log) (r : Option W) : SecInv N ad (pop t r) log := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hI
  refine ⟨h1, ?_, ?_, h4, fun j hj => ?_⟩
  · simp only [pop, List.length_tail]; omega
  · simp only [pop, List.length_tail]; omega
  · simp only [pop, List.length_tail] at hj ⊢
    obtain ⟨v, c, hv, hc, hm, hu⟩ := h5 (j + 1) (by omega)
    have hidx : t.seq - t.wire.length + (j + 1) = t.seq - (t.wire.length - 1) + j := by omega
    rw [hidx] at hm hu
    exact ⟨v, c, by simpa [List.getElem?_tail] using hv, by simpa [List.getElem?_tail] using hc,
      hm, hu⟩

/-- A transmission with fresh associated data preserves the invariant, for every ciphertext. -/
theorem secInv_transmit {N : ℕ} {ad : ℕ → W} (had : AdInj N ad) {t : SecSt W Ct}
    {log : Log W Ct} (hI : SecInv N ad t log) {v : W} (hn : nextMsg N t = some v) (c : Ct) :
    SecInv N ad ⟨t.queue, t.wire ++ [c], t.seq + 1, t.inbox⟩ (((v, ad t.seq), c) :: log) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hI
  have hs : t.seq < N := by
    by_contra h
    simp [nextMsg, h] at hn
  have hq : t.queue[t.wire.length]? = some v := by simpa [nextMsg, hs] using hn
  have hql : t.wire.length < t.queue.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hq
    exact absurd hq (by simp)
  refine ⟨by dsimp only; omega, by simp; omega, by simp; omega, ?_, fun j hj => ?_⟩
  · dsimp only
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨t.seq, by omega, rfl⟩
    · obtain ⟨i, hi, hie⟩ := h4 e he
      exact ⟨i, by omega, hie⟩
  · simp only [List.length_append, List.length_singleton] at hj ⊢
    have hidx : t.seq + 1 - (t.wire.length + 1) + j = t.seq - t.wire.length + j := by omega
    rw [hidx]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · obtain ⟨w, c', hw, hc, hm, hu⟩ := h5 j hj
      refine ⟨w, c', hw, by rw [List.getElem?_append_left hj]; exact hc,
        List.mem_cons_of_mem _ hm, fun e he hae => ?_⟩
      rcases List.mem_cons.1 he with rfl | he
      · have := had _ _ hs (by omega) hae
        omega
      · exact hu e he hae
    · have hidx' : t.seq - t.wire.length + t.wire.length = t.seq := by omega
      rw [hidx']
      refine ⟨v, c, hq, by simp, List.mem_cons_self .., fun e he hae => ?_⟩
      rcases List.mem_cons.1 he with rfl | he
      · rfl
      · obtain ⟨i, hi, hie⟩ := h4 e he
        have := had _ _ (by omega) hs (hie.symm.trans hae)
        omega

/-- An adversary activation that does not transmit preserves the invariant. -/
theorem secInv_detStep {N : ℕ} {ad : ℕ → W} {t : SecSt W Ct} {log : Log W Ct}
    (hI : SecInv N ad t log) (e : ChanAEv W) :
    SecInv N ad (detStep (Tr := Tr) ad (t, log) e).1.1 (detStep (Tr := Tr) ad (t, log) e).1.2 := by
  cases e with
  | deliver => rcases hw : t.wire with _ | ⟨c, cs⟩ <;> simp [detStep, hw, hI, secInv_pop]
  | drop => rcases hw : t.wire with _ | ⟨c, cs⟩ <;> simp [detStep, hw, hI, secInv_pop]
  | _ => simpa [detStep] using hI

/-- An honest step of the ideal protocol. -/
theorem idealSys_step_inl (N : ℕ) (ad : ℕ → W) (μ : PMF Tr) (k : Option Tr)
    (x : SecSt W Ct × Log W Ct) (h : ChanHEv W) :
    (idealSys N ad μ).step (k, x) (.inl h) =
      SPComp.pure ((k, ((honStep x.1 h).1, x.2)), .inl (honStep x.1 h).2) := by
  rcases k with _ | tr <;>
    simp [idealSys, KeyedSys.lazy, KeyedSys.lazyStep, secKeyed, OProt.plugStep, secProt,
      secProg, sampleFrom_ofPMF_pure]

/-- An adversary step of the ideal protocol: the transcript is drawn, then the program runs
against the ideal oracles. -/
theorem idealSys_step_inr (N : ℕ) (ad : ℕ → W) (μ : PMF Tr) (k : Option Tr)
    (x : SecSt W Ct × Log W Ct) (e : ChanAEv W) :
    (idealSys N ad μ).step (k, x) (.inr e) =
      SPComp.bind (drawTr μ k) fun tr =>
        SPComp.bind ((secProt N ad tr).plugStep aeadIdealOracle x (.inr e)) fun p =>
          SPComp.pure ((some tr, p.1), p.2) := by
  rcases k with _ | tr
  · simp [idealSys, KeyedSys.lazy, KeyedSys.lazyStep, secKeyed, drawTr]
  · simp [idealSys, KeyedSys.lazy, KeyedSys.lazyStep, secKeyed, drawTr]

omit [SampleableType W] [SampleableType Ct] in
/-- A message to transmit exists only while fewer than `N` messages are transmitted. -/
theorem seq_lt_of_nextMsg {N : ℕ} {t : SecSt W Ct} {v : W} (hn : nextMsg N t = some v) :
    t.seq < N := by
  by_contra h
  simp [nextMsg, h] at hn

end IdealSteps

/-! ## The ideal protocol is the simulated secure channel -/

section Realization

variable {W Ct Tr Leak : Type} [SampleableType W] [SampleableType Ct]

/-- The state map from the protocol over the ideal oracles to the simulated secure channel: the
transcript, the number of transmissions and the number of messages on the wire for the
simulator; the queue, the messages on the wire as the shown ones, and the inbox for the
channel. -/
def secMap (p : Option Tr × (SecSt W Ct × Log W Ct)) : (Unit × SimSt Tr) × ChanSt W :=
  (((), ⟨p.1, p.2.1.seq, p.2.1.wire.length⟩), ⟨p.2.1.queue, p.2.1.wire.length, p.2.1.inbox⟩)

/-- **The ideal protocol is the simulated secure channel.** With associated data injective
below `N`, the protocol over the ideal AEAD oracles with the transcript sampled from `μ`
realizes `FChan ChannelCap.secure ℓ` behind `secSim N μ ℓ` at distance `0`. -/
theorem idealSys_realizes_secure {N : ℕ} {ad : ℕ → W} (had : AdInj N ad) (μ : PMF Tr)
    (ℓ : W → Leak) :
    RealizesSim (idealSys (Ct := Ct) N ad μ) (FChan ChannelCap.secure ℓ) (secSim N μ ℓ)
      (fun _ _ => 0) := by
  change Realizes _ (((MultiHybrid.idSim (ChanHEv W) (ChanHOut W)).tensor
    (secSimA N μ)).withSub (FChan ChannelCap.secure ℓ)) (fun _ _ => 0)
  refine realizes_zero_of_stepMap_on _ _ (fun p => SecInv N ad p.2.1 p.2.2) secMap
    (secInv_init N ad) rfl (fun p e hI => ?_) (fun p e hI => ?_)
  · obtain ⟨k, t, log⟩ := p
    rcases e with h | e
    · exact ⟨Unit, SPComp.pure (), fun _ => ((k, ((honStep t h).1, log)), .inl (honStep t h).2),
        by rw [idealSys_step_inl, SPComp.pure_bind], fun _ => secInv_honStep hI h⟩
    · by_cases hf : ∃ v, e = .poll ∧ nextMsg N t = some v
      · obtain ⟨v, rfl, hn⟩ := hf
        refine ⟨Tr × Ct, SPComp.bind (drawTr μ k) fun tr =>
            SPComp.bind (sampleFrom (ofPMF (PMF.uniformFintype Ct))) fun c => SPComp.pure (tr, c),
          fun a => ((some a.1, (⟨t.queue, t.wire ++ [a.2], t.seq + 1, t.inbox⟩,
            ((v, ad t.seq), a.2) :: log)), .inr (.leak (some (.inl a)))), ?_,
          fun a => secInv_transmit had hI hn a.2⟩
        rw [idealSys_step_inr]
        simp only [plugStep_ideal_fresh N ad _ (t, log) v hn
          (lookup_fresh had hI (seq_lt_of_nextMsg hn) v), SPComp.bind_assoc, SPComp.pure_bind]
      · have he : e = .poll → nextMsg N t = none := by
          rintro rfl
          cases hn : nextMsg N t with
          | none => rfl
          | some v => exact absurd ⟨v, rfl, hn⟩ hf
        refine ⟨Tr, drawTr μ k, fun tr => ((some tr, (detStep (Tr := Tr) ad (t, log) e).1),
          (detStep ad (t, log) e).2), ?_, fun _ => secInv_detStep (Tr := Tr) hI e⟩
        rw [idealSys_step_inr]
        simp only [plugStep_ideal_det N ad _ (t, log) e he, SPComp.pure_bind]
  · obtain ⟨k, t, log⟩ := p
    rcases e with h | e
    · rw [idealSys_step_inl, MultiHybrid.tensor_withSub_step_inl _ _ (FChan ChannelCap.secure ℓ)
        FChan.honSys (fun _ _ => rfl), MultiHybrid.idSim_stepFuel]
      cases h <;> simp [secMap, honStep, FChan.honSys, FChan.honStep, SPComp.map]
    · rw [idealSys_step_inr, MultiHybrid.tensor_withSub_step_inr _ _ (FChan ChannelCap.secure ℓ)
        (FChan.advSys ChannelCap.secure ℓ) (fun _ _ => rfl)]
      simp only [secMap, MultiHybrid.stepFuel, secSimA, SPComp.map, SPComp.bind_assoc,
        SPComp.pure_bind]
      congr 1
      funext tr
      have hfuel : max (MultiHybrid.idSim (ChanHEv W) (ChanHOut W)).fuel 0 = 0 := rfl
      rw [hfuel]
      have hI' := hI
      obtain ⟨h1, h2, h3, -, -⟩ := hI
      dsimp only at h1 h2 h3 hI'
      cases e with
      | poll =>
        cases hn : nextMsg N t with
        | some v =>
          have hs := seq_lt_of_nextMsg hn
          have hq : t.queue[t.wire.length]? = some v := by simpa [nextMsg, hs] using hn
          have hql : t.wire.length < t.queue.length := by
            by_contra h
            rw [List.getElem?_eq_none (by omega)] at hq
            exact absurd hq (by simp)
          rw [plugStep_ideal_fresh N ad tr (t, log) v hn (lookup_fresh had hI' hs v)]
          simp [simDecide, hs, MultiHybrid.drive, FChan.advSys, FChan.advStep, FChan.pollLeak,
            List.head?_drop, hq, simFinish, SPComp.bind_assoc, ChannelCap.secure,
            ChannelCap.wireLeak, Nat.min_eq_left (Nat.succ_le_of_lt hql)]
        | none =>
          rw [plugStep_ideal_det N ad tr (t, log) .poll (fun _ => hn)]
          by_cases hs : t.seq < N
          · have hq : t.queue[t.wire.length]? = none := by simpa [nextMsg, hs] using hn
            have hmin : min (t.wire.length + 1) t.queue.length = t.wire.length := by
              have := List.getElem?_eq_none_iff.1 hq
              omega
            simp [simDecide, hs, MultiHybrid.drive, FChan.advSys, FChan.advStep, FChan.pollLeak,
              List.head?_drop, hq, simFinish, detStep, hmin]
          · simp [simDecide, hs, MultiHybrid.drive, detStep]
      | deliver =>
        rcases hw : t.wire with _ | ⟨c, cs⟩
        · simp [simDecide, hw, MultiHybrid.drive, detStep, plugStep_ideal_det]
        · simp [simDecide, hw, MultiHybrid.drive, FChan.advSys, FChan.advStep, FChan.popTo,
            simFinish, detStep, plugStep_ideal_det, pop, logDecrypt_head hI' hw]
      | drop =>
        rcases hw : t.wire with _ | ⟨c, cs⟩ <;>
          simp [simDecide, hw, MultiHybrid.drive, FChan.advSys, FChan.advStep, FChan.popTo,
            simFinish, detStep, plugStep_ideal_det, pop, ChannelCap.secure]
      | tamper v => simp [simDecide, MultiHybrid.drive, detStep, plugStep_ideal_det]
      | idle => simp [simDecide, MultiHybrid.drive, detStep, plugStep_ideal_det]

end Realization

/-! ## The square -/

section Square

variable {W Ct PK SK SS C T Z X Leak : Type} [SampleableType W] [SampleableType Ct]
  [Fintype SS] [Nonempty SS] [DecidableEq C] [DecidableEq X]

/-- **A secure channel from a KEM, a key schedule and an AEAD, as a square** (genuine UC).
With associated data injective below `N`, the protocol `secReal S side ctx F D N ad` realizes
the secure channel `FChan ChannelCap.secure ℓ` behind the simulator `secSim`, the forwarding
simulator on the honest port tensored with the adversary-port simulator `secSimA` that samples
the transcript of the key exchange and shows uniform ciphertexts. The bound at the environment
`Z` is the KEM IND-CCA advantage of `kemRed`, the dual-PRF advantage of `prfRed` against the key
schedule `F` and the AEAD advantage of `aeadRed`, each applied to the channel adversary
`chanAdv N ad Z` of `Z`. -/
theorem secReal_realizesSim_secure (S : Scheme PK SK SS C) (side : PMF (T × Z))
    (ctx : PK → C → T → Z → X) (F : SS → X → W) (D : AEADDef W Ct) {N : ℕ} {ad : ℕ → W}
    (had : AdInj N ad) (ℓ : W → Leak) :
    RealizesSim (secReal S side ctx F D N ad) (FChan ChannelCap.secure ℓ)
      (secSim N (trDist S side) ℓ) fun _ Zv =>
        indccaAdvantage S (kemRed side ctx F D (chanAdv N ad Zv)) +
        DualPRF_Left_Advantage F
          (prfRed S.keygen S.encaps side ctx D.encrypt D.decrypt (chanAdv N ad Zv)) +
        AEAD_CCA_Advantage D (aeadRed S.keygen S.encaps side (chanAdv N ad Zv)) := by
  have h₁ : Realizes (secReal S side ctx F D N ad) (secIdeal S side N ad) fun _ Zv =>
      indccaAdvantage S (kemRed side ctx F D (chanAdv N ad Zv)) +
      DualPRF_Left_Advantage F
        (prfRed S.keygen S.encaps side ctx D.encrypt D.decrypt (chanAdv N ad Zv)) +
      AEAD_CCA_Advantage D (aeadRed S.keygen S.encaps side (chanAdv N ad Zv)) :=
    fun _ Zv => (le_of_eq (adv_secReal_secIdeal S side ctx F D N ad Zv)).trans
      (channelAdvantage_le S side ctx F D _)
  have h₂ := idealSys_realizes_secure (Ct := Ct) had (trDist S side) ℓ
  exact fun ζ => ((h₁.trans h₂) ζ).mono fun _ => by simp

/-- **A secure channel with a transcript-bound salt, as a square** (genuine UC): the instance of
`secReal_realizesSim_secure` with a single KEM and the traffic key `F ss (salt pk c)`, the key
schedule of TLS 1.3 with the handshake salt bound to the public key and the encapsulation. -/
theorem secRealSalt_realizesSim_secure (S : Scheme PK SK SS C) (salt : PK → C → X)
    (F : SS → X → W) (D : AEADDef W Ct) {N : ℕ} {ad : ℕ → W} (had : AdInj N ad)
    (ℓ : W → Leak) :
    RealizesSim (secReal S (PMF.pure ((), ())) (fun pk c _ (_ : Unit) => salt pk c) F D N ad)
      (FChan ChannelCap.secure ℓ) (secSim N (trDist S (PMF.pure ((), ()))) ℓ) fun _ Zv =>
        indccaAdvantage S (kemRed (PMF.pure ((), ())) (fun pk c _ (_ : Unit) => salt pk c) F D
          (chanAdv N ad Zv)) +
        DualPRF_Left_Advantage F (prfRed S.keygen S.encaps (PMF.pure ((), ()))
          (fun pk c _ (_ : Unit) => salt pk c) D.encrypt D.decrypt (chanAdv N ad Zv)) +
        AEAD_CCA_Advantage D (aeadRed S.keygen S.encaps (PMF.pure ((), ())) (chanAdv N ad Zv)) :=
  secReal_realizesSim_secure S _ _ F D had ℓ

end Square

end CatCrypt.Crypto.AKE.ChannelSquare
