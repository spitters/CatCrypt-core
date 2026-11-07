/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SMCorrupt
public import CatCryptCore.Crypto.OracleAdversaryRelabelTimed

/-!
# Secure-messaging schemes and their corruption games

A record `SMScheme` of the party algorithms of a secure-messaging scheme in the shape of the
double ratchet of Alwen, Coretti and Dodis (EUROCRYPT 2019), with the randomness of each
algorithm as an explicit input, the corruption games of
`CatCryptCore.Crypto.Messaging.SMCorrupt` stated over the record, the construction of ACD from
a CKA, a root KDF, a chain generator and an AEAD as an instance (`acdSM`), and the transfer of
the games along a simulation of schemes.

## Schemes

A scheme `M : SMScheme St Pub Rand W Ct Leak` has party states `St`, public values `Pub` of the
epochs, randomness `Rand`, words `W` (a message is a plaintext and associated data in `W × W`),
ciphertexts `Ct` and corruption answers `Leak`:

* `init` — the public value of the initialisation and the initial states of the first sender
  and of the first receiver;
* `ratchet` — the party opens an epoch with the randomness `r`: its next state and the public
  value of the epoch;
* `recv` — the party receives the public value of the epoch opened by its peer;
* `send` — the party encrypts a message in its own epoch; `none` when it holds no sending
  chain;
* `expose` — the answer to a corruption of the party;
* `idealCt` — the distribution of the ciphertext of the challenge in the ideal game.

## The games

`smCorruptGame M ΔFS ΔPCS ideal A` is the game of `sm_corrupt_game` over `M`: the epoch
counters, the gates of the queries and the corruption windows are those of
`CatCryptCore.Crypto.Messaging.SMCorrupt`; the party states, the public value in transit and
the answers are those of the scheme. `smAdaptiveGame` is the game with an adaptive challenge
epoch of `sm_adaptive_game` over `M`.

## The ACD construction

`acdSM C R G D` is the scheme whose party state `SMPartySt` is a CKA state, a root key, a
sending and a receiving chain. Opening an epoch runs the CKA sending algorithm and the root step
on its key; receiving runs the CKA receiving algorithm and the root step on the key the
receiver derives itself; sending runs the chain generator and the AEAD; a corruption reveals
the state. The game `sm_corrupt_game` holds the root output of the epoch in transit and gives it
to the receiver. When the CKA is correct along a relation `J` of the states of the next sender
and the next receiver (`CKACorrect`), the receiver derives the same output, and
`smCorruptGame_acd` proves that `smCorruptGame (acdSM C R G D)` is `sm_corrupt_game` with the
answers relabelled; `smAdaptiveGame_acd` proves the same for the adaptive game. The CKA
`dhCKAOf decE` of `CatCryptCore.Crypto.Messaging.CKACorrupt` is the Diffie–Hellman CKA whose
secret keys are drawn uniformly from a key space `Sk` and act through the exponent map `decE`;
it is correct (`dhCKAOf_correct`).

## Transfer

`SMScheme.Sim M' M Rel encP encC encL encI` states that the scheme `M'` simulates `M` along a
relation `Rel` of party states, with public values encoded by `encP`, ciphertexts by `encC`,
corruption answers by `encL`, and the initial states by `encI`: the initialisation of `M'` is
the encoded initialisation of `M`, and from related states the algorithms on the same
randomness give related states and encoded outputs. `smCorruptGame_sim` proves that the game of
`M'` against an adversary `A` is the game of `M` against `A` with the answers encoded
(`SMSchemeAdv.comap`); `smAdaptiveGame_sim` proves the same for the adaptive game. The theorems
mention no particular scheme: a scheme that simulates `acdSM` inherits every bound of
`CatCryptCore.Crypto.Messaging.SMCorrupt` at the relabelled adversary.

## Main definitions

* `SMScheme`, `SMPartySt`, `SMSchemeAns`, `SMSchemeSt`, `smSchemeOracle`, `SMSchemeAdv`,
  `smCorruptGame`, `SMScheme.corruptAdvantage` — schemes and the corruption game over them
* `smSchemeAdOracle`, `smAdaptiveGame`, `SMScheme.adaptiveAdvantage` — the game with an
  adaptive challenge epoch
* `acdSM`, `CKACorrect`, `dhKeyRel` — the ACD construction, CKA correctness, the correctness
  relation of the Diffie–Hellman CKA over a key space
* `SMScheme.Sim`, `SMSchemeAdv.comap` — simulations of schemes and the relabelled adversary

## Main results

* `OracleAdv.run_map_fst_mapQueryAnswer_of_coupling` — runs against two oracles whose calls
  are coupled along a relation of the states have the same outputs, with the answers of one
  relabelled
* `smCorruptGame_acd`, `smAdaptiveGame_acd`, `acdSM_corruptAdvantage_eq`,
  `acdSM_adaptiveAdvantage_eq` — the games of `acdSM` are those of `SMCorrupt`
* `acdSM_corruptAdvantage_le`, `acdSM_adaptiveAdvantage_le` — the bounds of
  `sm_corrupt_advantage_le` and `sm_adaptive_corrupt_advantage_le` for `acdSM`
* `acdSM_adaptiveAdvantage_le_of_isQueryBound` — for an adversary asking at most `q` queries,
  the bound of `sm_adaptive_corrupt_advantage_le_of_isQueryBound`, a finite sum over the epochs
  `e ≤ q`; `SMSchemeAdv.toSM_play_isQueryBound`, `SMSchemeAdv.comap_play_isQueryBound` — the
  relabellings keep the query bound
* `acdSM_dhCKAOf_adaptiveAdvantage_le_of_isQueryBound` — for the Diffie–Hellman CKA over a key
  space, the CKA terms of each epoch as DDH advantages of `ckaCorruptDDHRedOf`, with the charge
  `(q + 1) * 8 * c.δ` of the sampler certificate `c` over the `q + 1` epochs;
  `SMScheme.Sim.adaptiveAdvantage_le_dhCKAOf_of_isQueryBound` — the same bound for every scheme
  that simulates this construction, at the adversary with encoded answers
* `smCorruptGame_sim`, `smAdaptiveGame_sim`, `SMScheme.Sim.corruptAdvantage_eq`,
  `SMScheme.Sim.adaptiveAdvantage_eq` — the transfer along a simulation
* `dhCKAOf_correct`, `dhInitPOf_rel` — correctness of the Diffie–Hellman CKA over a key
  space
-/

set_option autoImplicit false

@[expose] public section

/-! ## Coupled runs of oracle adversaries -/

namespace CatCrypt.Crypto.OracleAdv

variable {S S' D R R' α : Type}

/-- **Runs related by a coupling of the oracle calls.** Let `Rel` relate the states of `O'` to
those of `O`, and let every call of `O'` from a state related to one of `O` be coupled with the
call of `O`: a distribution `ν` on the pairs of an outcome of `O` and a state of `O'`, whose
first marginal is the call of `O`, whose image under the relabelling `e` of the answer is the
call of `O'`, and whose support keeps the relation. Then the run of `A` against `O'` and the run
of `A` with the answers relabelled by `e` against `O` have the same output distribution. -/
theorem run_map_fst_mapQueryAnswer_of_coupling (O : S → D → PMF (R × S))
    (O' : S' → D → PMF (R' × S')) (e : R → R') (Rel : S' → S → Prop)
    (hO : ∀ s' s d, Rel s' s → ∃ ν : PMF ((R × S) × S'), ν.map Prod.fst = O s d ∧
      ν.map (fun z => (e z.1.1, z.2)) = O' s' d ∧ ∀ z ∈ ν.support, Rel z.2 z.1.2)
    (A : OracleAdv D R' α) (s' : S') (s : S) (hs : Rel s' s) :
    (run O' A s').map Prod.fst = (run O (A.mapQueryAnswer id e) s).map Prod.fst := by
  induction A generalizing s' s with
  | ret a => simp only [mapQueryAnswer, run_ret, PMF.pure_map]
  | rand p k ih =>
    simp only [mapQueryAnswer, run_rand, PMF.map_bind]
    exact congrArg _ (funext fun b => ih b s' s hs)
  | query d k ih =>
    obtain ⟨ν, h1, h2, h3⟩ := hO s' s d hs
    simp only [mapQueryAnswer, run_query, PMF.map_bind, id_eq]
    rw [← h1, ← h2, PMF.bind_map, PMF.bind_map]
    exact PMF.bind_congr_support _ _ _ fun z hz => ih _ z.2 z.1.2 (h3 z hz)

/-- **Runs related by a state map under an invariant, with relabelled answers.** A map `f` of
the states of `O` to those of `O'` that, from the states satisfying an invariant kept by every
call, carries every call of `O`, with the answer relabelled by `e`, to the call of `O'` gives
the same output distributions. -/
theorem run_map_fst_mapQueryAnswer_of_map_state_inv (O : S → D → PMF (R × S))
    (O' : S' → D → PMF (R' × S')) (e : R → R') (f : S → S') (Inv : S → Prop)
    (hInv : ∀ s d, Inv s → ∀ x ∈ (O s d).support, Inv x.2)
    (hO : ∀ s d, Inv s → (O s d).map (fun x => (e x.1, f x.2)) = O' (f s) d)
    (A : OracleAdv D R' α) (s : S) (hs : Inv s) :
    (run O' A (f s)).map Prod.fst = (run O (A.mapQueryAnswer id e) s).map Prod.fst := by
  refine run_map_fst_mapQueryAnswer_of_coupling O O' e (fun s' s => s' = f s ∧ Inv s)
    (fun s' s d h => ⟨(O s d).map fun x => (x, f x.2), ?_, ?_, ?_⟩) A (f s) s ⟨rfl, hs⟩
  · rw [PMF.map_comp]; exact PMF.map_id _
  · rw [h.1, PMF.map_comp, ← hO s d h.2]; rfl
  · intro z hz
    rw [PMF.support_map] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact ⟨rfl, hInv s d h.2 x hx⟩

end CatCrypt.Crypto.OracleAdv

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
  CatCrypt.Crypto.PRPPRF CatCryptCore.Examples.CyclicGroupDDH
open scoped ENNReal

/-! ## Schemes -/

/-- A secure-messaging scheme with party states `St`, public values `Pub`, randomness `Rand`,
words `W`, ciphertexts `Ct` and corruption answers `Leak`. -/
structure SMScheme (St Pub Rand W Ct Leak : Type) where
  /-- The public value of the initialisation and the initial states of the first sender and
  of the first receiver. -/
  init : SPComp (Pub × St × St)
  /-- Opening an epoch with the randomness `r`: the next state and the public value. -/
  ratchet : St → Rand → St × Pub
  /-- Receiving the public value of the epoch opened by the peer. -/
  recv : St → Pub → St
  /-- Encrypting a message (a plaintext and associated data): the next state and the
  ciphertext, or `none`. -/
  send : St → W × W → Option (St × Ct)
  /-- The answer to a corruption. -/
  expose : St → Leak
  /-- The distribution of the challenge ciphertext of the ideal game. -/
  idealCt : PMF Ct

/-- The answers of the oracles of the game over a scheme. -/
inductive SMSchemeAns (Pub Ct Leak : Type) where
  /-- A refused query, or a receive. -/
  | none
  /-- The public value of a new epoch. -/
  | msg (T : Pub)
  /-- A ciphertext. -/
  | ct (c : Ct)
  /-- The answer to a corruption. -/
  | state (σ : Leak)

/-- The answers with the public values, ciphertexts and corruption answers relabelled. -/
def SMSchemeAns.map {Pub Ct Leak Pub' Ct' Leak' : Type} (encP : Pub → Pub') (encC : Ct → Ct')
    (encL : Leak → Leak') : SMSchemeAns Pub Ct Leak → SMSchemeAns Pub' Ct' Leak'
  | .none => .none
  | .msg T => .msg (encP T)
  | .ct c => .ct (encC c)
  | .state σ => .state (encL σ)

/-- The state of the game over a scheme: the party states, the epoch counters and the public
value in transit, and whether the challenge has been asked. -/
structure SMSchemeSt (St Pub : Type) where
  /-- The party states, counters and the public value in transit. -/
  ck : CKAGameSt St Pub
  /-- The challenge has been asked. -/
  done : Bool

namespace SMSchemeSt

variable {St Pub : Type}

/-- The initial state from the initialisation `i`. -/
def init (i : Pub × St × St) : SMSchemeSt St Pub := ⟨CKAGameSt.init i.1 i.2.1 i.2.2, false⟩

/-- Party `p` moved to the state `x` within its epoch; the challenge flag is `d`. -/
def upd (s : SMSchemeSt St Pub) (p : CKAParty) (x : St) (d : Bool) : SMSchemeSt St Pub :=
  ⟨{ s.ck with st := Function.update s.ck.st p x }, d⟩

end SMSchemeSt

section Game

variable {St Pub Rand W Ct Leak : Type} [Fintype Rand] [Nonempty Rand]

/-- The oracle of the corruption game over the scheme `M` with the challenge epoch `t` and the
challenge mode `ideal`: the gates of `smOracleOf`, the algorithms of `M`. -/
noncomputable def smSchemeOracle (M : SMScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS t : ℕ)
    (ideal : Bool) (s : SMSchemeSt St Pub) :
    SMQuery W → PMF (SMSchemeAns Pub Ct Leak × SMSchemeSt St Pub)
  | .ratchet p =>
    if s.ck.canSend p then
      (PMF.uniformFintype Rand).bind fun r =>
        PMF.pure (.msg (M.ratchet (s.ck.st p) r).2,
          ⟨s.ck.sent p (M.ratchet (s.ck.st p) r).1 (M.ratchet (s.ck.st p) r).2, s.done⟩)
    else PMF.pure (.none, s)
  | .recv p =>
    if s.ck.canRecv p then
      PMF.pure (.none, ⟨s.ck.recvd p (M.recv (s.ck.st p) s.ck.msg), s.done⟩)
    else PMF.pure (.none, s)
  | .send p m =>
    if ckaSender (s.ck.t p) == p then
      match M.send (s.ck.st p) m with
      | some x => PMF.pure (.ct x.2, s.upd p x.1 s.done)
      | none => PMF.pure (.none, s)
    else PMF.pure (.none, s)
  | .chall p m =>
    if !s.done && (ckaSender (s.ck.t p) == p) && (s.ck.t p == t) then
      match M.send (s.ck.st p) m with
      | some x =>
        (if ideal then M.idealCt else PMF.pure x.2).bind fun c =>
          PMF.pure (.ct c, s.upd p x.1 true)
      | none => PMF.pure (.none, s)
    else PMF.pure (.none, s)
  | .corrupt p =>
    PMF.pure (if ckaAllowCorr ΔFS ΔPCS t s.ck p then .state (M.expose (s.ck.st p)) else .none, s)

/-- An adversary of the corruption game over a scheme: a distribution `tStar` of the challenge
epoch, and for each challenge epoch and public value of the initialisation an oracle tree. -/
structure SMSchemeAdv (Pub W Ct Leak : Type) : Type 1 where
  /-- The choice of the challenge epoch. -/
  tStar : PMF ℕ
  /-- The interaction with the oracles. -/
  play : ℕ → Pub → OracleAdv (SMQuery W) (SMSchemeAns Pub Ct Leak) Bool

/-- **The corruption game over a scheme**: the adversary chooses the challenge epoch `t`, the
scheme is initialised, and the adversary interacts with `smSchemeOracle`. -/
noncomputable def smCorruptGame (M : SMScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS : ℕ)
    (ideal : Bool) (A : SMSchemeAdv Pub W Ct Leak) : SPComp Bool :=
  SPComp.bind (liftPMF A.tStar) fun t =>
    SPComp.bind M.init fun i =>
      liftPMF ((OracleAdv.run (smSchemeOracle M ΔFS ΔPCS t ideal) (A.play t i.1)
        (SMSchemeSt.init i)).map Prod.fst)

/-- **The advantage of the adversary `A` in the corruption game over `M`.** -/
noncomputable def SMScheme.corruptAdvantage (M : SMScheme St Pub Rand W Ct Leak)
    (ΔFS ΔPCS : ℕ) (A : SMSchemeAdv Pub W Ct Leak) : ℝ≥0∞ :=
  Advantage (smCorruptGame M ΔFS ΔPCS false A) (smCorruptGame M ΔFS ΔPCS true A)

/-- The oracle of the game over the scheme `M` with an adaptive challenge epoch: the epochs,
receives and sends of `smSchemeOracle`; the challenge and the corruptions of `smAdOracle`. -/
noncomputable def smSchemeAdOracle (M : SMScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS : ℕ)
    (ideal : Bool) (x : SMSchemeSt St Pub × SMAdRec) :
    SMQuery W → PMF (SMSchemeAns Pub Ct Leak × (SMSchemeSt St Pub × SMAdRec))
  | .ratchet p =>
    (smSchemeOracle M ΔFS ΔPCS 0 ideal x.1 (.ratchet p)).map fun y => (y.1, (y.2, x.2))
  | .recv p =>
    (smSchemeOracle M ΔFS ΔPCS 0 ideal x.1 (.recv p)).map fun y => (y.1, (y.2, x.2))
  | .send p m =>
    (smSchemeOracle M ΔFS ΔPCS 0 ideal x.1 (.send p m)).map fun y => (y.1, (y.2, x.2))
  | .chall p m =>
    if x.2.cE = none ∧ x.1.done = false ∧ x.2.lo ≤ x.1.ck.t p ∧
        ckaSender (x.1.ck.t p) = p then
      match M.send (x.1.ck.st p) m with
      | some y =>
        (if ideal then M.idealCt else PMF.pure y.2).bind fun c =>
          PMF.pure (.ct c, (x.1.upd p y.1 true, ⟨some (x.1.ck.t p), x.2.lo⟩))
      | none => PMF.pure (.none, x)
    else PMF.pure (.none, x)
  | .corrupt p =>
    match x.2.cE with
    | none =>
      PMF.pure (.state (M.expose (x.1.ck.st p)),
        (x.1, ⟨none, max x.2.lo (max (x.1.ck.t .A) (x.1.ck.t .B) + ΔPCS)⟩))
    | some e =>
      PMF.pure (if e + ΔFS ≤ x.1.ck.t p then .state (M.expose (x.1.ck.st p)) else .none, x)

/-- **The game over a scheme with an adaptive challenge epoch.** -/
noncomputable def smAdaptiveGame (M : SMScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS : ℕ)
    (ideal : Bool) (A : Pub → OracleAdv (SMQuery W) (SMSchemeAns Pub Ct Leak) Bool) :
    SPComp Bool :=
  SPComp.bind M.init fun i =>
    liftPMF ((OracleAdv.run (smSchemeAdOracle M ΔFS ΔPCS ideal) (A i.1)
      (SMSchemeSt.init i, ⟨none, 0⟩)).map Prod.fst)

/-- **The advantage of the adversary `A` in the game over `M` with an adaptive challenge
epoch.** -/
noncomputable def SMScheme.adaptiveAdvantage (M : SMScheme St Pub Rand W Ct Leak)
    (ΔFS ΔPCS : ℕ) (A : Pub → OracleAdv (SMQuery W) (SMSchemeAns Pub Ct Leak) Bool) : ℝ≥0∞ :=
  Advantage (smAdaptiveGame M ΔFS ΔPCS false A) (smAdaptiveGame M ΔFS ΔPCS true A)

end Game

/-! ## The ACD construction -/

/-- The state of a party of the double ratchet of ACD: its CKA state, its root key, its sending
chain and its receiving chain. -/
structure SMPartySt (Sc RK Sa : Type) where
  /-- The CKA state. -/
  ck : Sc
  /-- The root key. -/
  rk : RK
  /-- The sending chain (FS-AEAD sender state). -/
  snd : Option Sa
  /-- The receiving chain (FS-AEAD receiver state). -/
  rcv : Option Sa

section ACD

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [Fintype RK] [Nonempty RK]

/-- **The ACD construction** of a secure-messaging scheme from the CKA `C`, the root KDF `R`,
the chain generator `G` and the AEAD `D`. Both parties start with the initial CKA states and a
uniform root key. Opening an epoch runs the CKA sending algorithm on the randomness and the
root step on its key, which gives the next root key and the sending chain; receiving runs the
CKA receiving algorithm and the root step on the key the receiver derives, which gives the next
root key and the receiving chain; sending encrypts under the next key of the sending chain; a
corruption reveals the state. -/
noncomputable def acdSM (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) :
    SMScheme (SMPartySt Sc RK Sa) Msg Rand W Ct (SMPartySt Sc RK Sa) where
  init := SPComp.bind C.init fun i => SPComp.bind (SPComp.sample RK) fun rk =>
    SPComp.pure (i.1, ⟨i.2.1, rk, none, none⟩, ⟨i.2.2, rk, none, none⟩)
  ratchet x r :=
    (⟨(CKACoins.sendR (C := C) x.ck r).1,
      (R.stretch (x.rk, (CKACoins.sendR (C := C) x.ck r).2.2)).1,
      some (R.stretch (x.rk, (CKACoins.sendR (C := C) x.ck r).2.2)).2, x.rcv⟩,
      (CKACoins.sendR (C := C) x.ck r).2.1)
  recv x T :=
    ⟨(C.recv x.ck T).1, (R.stretch (x.rk, (C.recv x.ck T).2)).1, x.snd,
      some (R.stretch (x.rk, (C.recv x.ck T).2)).2⟩
  send x m := x.snd.map fun sa =>
    (⟨x.ck, x.rk, some (G.stretch sa).2, x.rcv⟩, D.encrypt (G.stretch sa).1 m.1 m.2)
  expose := id
  idealCt := PMF.uniformFintype Ct

/-- **Correctness of a CKA along a relation.** `J s r` relates the state `s` of the next sender
to the state `r` of the next receiver. After a send from `s` with any randomness, the receiver
in `r` derives the key of the sender from the message, and `J` relates the receiver's next
state, the sender of the next epoch, to the sender's next state. -/
structure CKACorrect (C : CKADef Sc Msg Key) [CKACoins C Rand] (J : Sc → Sc → Prop) :
    Prop where
  /-- The receiver derives the key of the sender. -/
  key : ∀ s r x, J s r →
    (C.recv r (CKACoins.sendR (C := C) s x).2.1).2 = (CKACoins.sendR (C := C) s x).2.2
  /-- The relation holds with the roles exchanged. -/
  next : ∀ s r x, J s r →
    J (C.recv r (CKACoins.sendR (C := C) s x).2.1).1 (CKACoins.sendR (C := C) s x).1

/-- The answers of `sm_corrupt_game` as answers of the game over `acdSM`. -/
def SMAns.toScheme : SMAns Sc Msg RK Sa Ct → SMSchemeAns Msg Ct (SMPartySt Sc RK Sa)
  | .none => .none
  | .msg T => .msg T
  | .ct c => .ct c
  | .state γ rk snd rcv => .state ⟨γ, rk, snd, rcv⟩

/-- The state of `sm_corrupt_game` as a state of the game over `acdSM`: the root output in
transit is forgotten. -/
def SMSt.toScheme (s : SMSt Sc Msg RK Sa) : SMSchemeSt (SMPartySt Sc RK Sa) Msg :=
  ⟨⟨fun p => ⟨s.ck.st p, s.loc.rk p, s.loc.snd p, s.loc.rcv p⟩, s.ck.t, s.ck.msg⟩, s.loc.done⟩

/-- An adversary of the game over `acdSM` as an adversary of `sm_corrupt_game`: its answers
are relabelled by `SMAns.toScheme`. -/
def SMSchemeAdv.toSM (A : SMSchemeAdv Msg W Ct (SMPartySt Sc RK Sa)) :
    SMCorruptAdv Sc Msg RK Sa W Ct where
  tStar := A.tStar
  play t T := (A.play t T).mapQueryAnswer id SMAns.toScheme

omit [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct] [Fintype RK]
  [Nonempty RK] in
/-- The relabelled adversary `A.toSM` keeps the query bound of `A`. -/
theorem SMSchemeAdv.toSM_play_isQueryBound {A : SMSchemeAdv Msg W Ct (SMPartySt Sc RK Sa)}
    {q : ℕ} (hA : ∀ t T, (A.play t T).IsQueryBound q) (t : ℕ) (T : Msg) :
    (A.toSM.play t T).IsQueryBound q :=
  OracleAdv.isQueryBound_mapQueryAnswer _ _ (hA t T)

/-- The invariant of `sm_corrupt_game` under which its root output in transit is the one the
receiver derives: the counters are reachable; when a party may send, `J` relates its state to
its peer's and both hold the same root key; when a party may receive, the root output in transit
is the root step at its root key on the key it derives, `J` relates its next state to its
peer's, and the peer holds the root key of that output. -/
structure ACDInv (C : CKADef Sc Msg Key) (R : PRGDef (RK × Key) (RK × Sa)) (J : Sc → Sc → Prop)
    (s : SMSt Sc Msg RK Sa) : Prop where
  /-- The counters are reachable. -/
  reach : ckaReach s.ck
  /-- The state of the next sender. -/
  send : ∀ p, s.ck.canSend p = true →
    J (s.ck.st p) (s.ck.st p.other) ∧ s.loc.rk p.other = s.loc.rk p
  /-- The root output in transit. -/
  recv : ∀ q, s.ck.canRecv q = true →
    s.loc.out = some (R.stretch (s.loc.rk q, (C.recv (s.ck.st q) s.ck.msg).2)) ∧
      J (C.recv (s.ck.st q) s.ck.msg).1 (s.ck.st q.other) ∧
      s.loc.rk q.other = (R.stretch (s.loc.rk q, (C.recv (s.ck.st q) s.ck.msg).2)).1

omit [Fintype RK] [Nonempty RK] in
theorem SMSt.toScheme_opened (s : SMSt Sc Msg RK Sa) (p : CKAParty) (x : Sc) (T : Msg)
    (y : RK × Sa) :
    SMSt.toScheme ⟨s.ck.sent p x T, s.loc.opened p y⟩ =
      ⟨s.toScheme.ck.sent p ⟨x, y.1, some y.2, s.loc.rcv p⟩ T, s.loc.done⟩ := by
  simp only [SMSt.toScheme, SMLoc.opened, CKAGameSt.sent, SMSchemeSt.mk.injEq,
    CKAGameSt.mk.injEq, and_true]
  funext q
  by_cases hq : q = p
  · subst hq; simp
  · simp [Function.update_of_ne hq]

omit [Fintype RK] [Nonempty RK] in
theorem SMSt.toScheme_recvY (s : SMSt Sc Msg RK Sa) (p : CKAParty) (x : Sc) (y : RK × Sa) :
    SMSt.toScheme ⟨s.ck.recvd p x, s.loc.recvY p y⟩ =
      ⟨s.toScheme.ck.recvd p ⟨x, y.1, s.loc.snd p, some y.2⟩, s.loc.done⟩ := by
  simp only [SMSt.toScheme, SMLoc.recvY, CKAGameSt.recvd, SMSchemeSt.mk.injEq,
    CKAGameSt.mk.injEq, and_true]
  funext q
  by_cases hq : q = p
  · subst hq; simp
  · simp [Function.update_of_ne hq]

omit [Fintype RK] [Nonempty RK] in
theorem SMSt.toScheme_advanced (s : SMSt Sc Msg RK Sa) (p : CKAParty) (sa : Sa) :
    SMSt.toScheme ⟨s.ck, s.loc.advanced p sa⟩ =
      s.toScheme.upd p ⟨s.ck.st p, s.loc.rk p, some sa, s.loc.rcv p⟩ s.toScheme.done := by
  simp only [SMSt.toScheme, SMLoc.advanced, SMSchemeSt.upd, SMSchemeSt.mk.injEq,
    CKAGameSt.mk.injEq, and_true]
  funext q
  by_cases hq : q = p
  · subst hq; simp
  · simp [Function.update_of_ne hq]

omit [Fintype RK] [Nonempty RK] in
theorem SMSt.toScheme_advanced_done (s : SMSt Sc Msg RK Sa) (p : CKAParty) (sa : Sa) :
    SMSt.toScheme ⟨s.ck, { s.loc.advanced p sa with done := true }⟩ =
      s.toScheme.upd p ⟨s.ck.st p, s.loc.rk p, some sa, s.loc.rcv p⟩ true := by
  simp only [SMSt.toScheme, SMLoc.advanced, SMSchemeSt.upd, SMSchemeSt.mk.injEq,
    CKAGameSt.mk.injEq, and_true]
  funext q
  by_cases hq : q = p
  · subst hq; simp
  · simp [Function.update_of_ne hq]

omit [Fintype RK] [Nonempty RK] in
theorem SMSt.toScheme_ck_canSend (s : SMSt Sc Msg RK Sa) (p : CKAParty) :
    s.toScheme.ck.canSend p = s.ck.canSend p := rfl

omit [Fintype RK] [Nonempty RK] in
theorem SMSt.toScheme_ck_canRecv (s : SMSt Sc Msg RK Sa) (p : CKAParty) :
    s.toScheme.ck.canRecv p = s.ck.canRecv p := rfl

omit [Fintype RK] [Nonempty RK] in
theorem SMSt.toScheme_ck_t (s : SMSt Sc Msg RK Sa) : s.toScheme.ck.t = s.ck.t := rfl

omit [Fintype RK] [Nonempty RK] in
theorem SMSt.toScheme_ck_st (s : SMSt Sc Msg RK Sa) (p : CKAParty) :
    s.toScheme.ck.st p = ⟨s.ck.st p, s.loc.rk p, s.loc.snd p, s.loc.rcv p⟩ := rfl

omit [Fintype RK] [Nonempty RK] in
theorem SMSt.toScheme_done (s : SMSt Sc Msg RK Sa) : s.toScheme.done = s.loc.done := rfl

omit [Fintype RK] [Nonempty RK] in
theorem SMSt.toScheme_allowCorr (s : SMSt Sc Msg RK Sa) (ΔFS ΔPCS t : ℕ) (p : CKAParty) :
    ckaAllowCorr ΔFS ΔPCS t s.toScheme.ck p = ckaAllowCorr ΔFS ΔPCS t s.ck p := rfl

/-- **The oracle of `sm_corrupt_game` is the oracle over `acdSM`.** Under the invariant
`ACDInv`, each call of `smOracleOf` at the real root step, with its answer and state carried to
the game over `acdSM`, is the call of `smSchemeOracle (acdSM C R G D)`. -/
theorem acd_step (C : CKADef Sc Msg Key) [CKACoins C Rand] (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (J : Sc → Sc → Prop) (ΔFS ΔPCS t : ℕ)
    (ideal : Bool) (s : SMSt Sc Msg RK Sa) (hs : ACDInv C R J s) (q : SMQuery W) :
    (smOracleOf C R G D ΔFS ΔPCS t ideal (realRoot R) s q).map
        (fun x => (SMAns.toScheme x.1, x.2.toScheme)) =
      smSchemeOracle (acdSM C R G D) ΔFS ΔPCS t ideal s.toScheme q := by
  cases q with
  | ratchet p =>
    simp only [smOracleOf, smSchemeOracle, realRoot, ite_self, PMF.pure_bind,
      SMSt.toScheme_ck_canSend]
    by_cases hc : s.ck.canSend p = true
    · simp only [hc, ite_true, PMF.map_bind, PMF.pure_map]
      refine congrArg _ (funext fun r => ?_)
      simp only [SMAns.toScheme, acdSM, SMSt.toScheme_opened]
      rfl
    · simp only [hc, Bool.false_eq_true, ite_false, PMF.pure_map]
      rfl
  | recv p =>
    simp only [smOracleOf, smSchemeOracle, SMSt.toScheme_ck_canRecv]
    by_cases hc : s.ck.canRecv p = true
    · simp only [hc, ite_true, PMF.pure_map, SMLoc.received, (hs.recv p hc).1]
      simp only [SMAns.toScheme, acdSM, SMSt.toScheme_recvY]
      rfl
    · simp only [hc, Bool.false_eq_true, ite_false, PMF.pure_map]
      rfl
  | send p m =>
    simp only [smOracleOf, smSchemeOracle, SMSt.toScheme_ck_t, SMSt.toScheme_ck_st, acdSM]
    cases hsnd : s.loc.snd p with
    | none =>
      simp only [Option.map_none, PMF.pure_map]
      by_cases hc : (ckaSender (s.ck.t p) == p) = true <;>
        simp only [hc, ite_true, Bool.false_eq_true, ite_false] <;> rfl
    | some sa =>
      simp only [Option.map_some]
      by_cases hc : (ckaSender (s.ck.t p) == p) = true
      · simp only [hc, ite_true, PMF.pure_map, SMAns.toScheme, SMSt.toScheme_advanced]
      · simp only [hc, Bool.false_eq_true, ite_false, PMF.pure_map]
        rfl
  | chall p m =>
    simp only [smOracleOf, smSchemeOracle, SMSt.toScheme_ck_t, SMSt.toScheme_ck_st, acdSM,
      SMSt.toScheme_done, challOk]
    cases hsnd : s.loc.snd p with
    | none =>
      simp only [Option.map_none, PMF.pure_map]
      by_cases hc : (!s.loc.done && (ckaSender (s.ck.t p) == p) && (s.ck.t p == t)) = true <;>
        simp only [hc, ite_true, Bool.false_eq_true, ite_false] <;> rfl
    | some sa =>
      simp only [Option.map_some]
      by_cases hc : (!s.loc.done && (ckaSender (s.ck.t p) == p) && (s.ck.t p == t)) = true
      · simp only [hc, ite_true, PMF.map_bind, PMF.pure_map, SMAns.toScheme, challCt,
          SMSt.toScheme_advanced_done]
      · simp only [hc, Bool.false_eq_true, ite_false, PMF.pure_map]
        rfl
  | corrupt p =>
    simp only [smOracleOf, smSchemeOracle, PMF.pure_map, SMSt.toScheme_allowCorr]
    by_cases hc : ckaAllowCorr ΔFS ΔPCS t s.ck p = true <;>
      simp only [hc, ite_true, Bool.false_eq_true, ite_false] <;> rfl

omit [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct] [Fintype RK]
  [Nonempty RK] in
/-- `ACDInv` depends only on the CKA part, the root keys and the root output in transit. -/
theorem ACDInv.of_eq {C : CKADef Sc Msg Key} {R : PRGDef (RK × Key) (RK × Sa)}
    {J : Sc → Sc → Prop} {s s' : SMSt Sc Msg RK Sa} (hs : ACDInv C R J s) (hck : s'.ck = s.ck)
    (hrk : s'.loc.rk = s.loc.rk) (hout : s'.loc.out = s.loc.out) : ACDInv C R J s' := by
  obtain ⟨h1, h2, h3⟩ := hs
  exact ⟨hck ▸ h1, hck ▸ hrk ▸ h2, hck ▸ hrk ▸ hout ▸ h3⟩

omit [Fintype RK] [Nonempty RK] in
/-- **The invariant `ACDInv` is kept** by every call of `smOracleOf` at the real root step,
when the CKA is correct along `J`. -/
theorem acdInv_step (C : CKADef Sc Msg Key) [CKACoins C Rand] (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) {J : Sc → Sc → Prop} (hJ : CKACorrect C J)
    (ΔFS ΔPCS t : ℕ) (ideal : Bool) (s : SMSt Sc Msg RK Sa) (hs : ACDInv C R J s)
    (q : SMQuery W) :
    ∀ x ∈ (smOracleOf C R G D ΔFS ΔPCS t ideal (realRoot R) s q).support, ACDInv C R J x.2 := by
  intro x hx
  cases q with
  | ratchet p =>
    simp only [smOracleOf, realRoot, ite_self, PMF.pure_bind] at hx
    split at hx
    · rename_i hc
      simp only [PMF.support_bind, Set.mem_iUnion, PMF.support_pure, Set.mem_singleton_iff]
        at hx
      obtain ⟨r, -, rfl⟩ := hx
      obtain ⟨hsJ, hsrk⟩ := hs.send p hc
      have ht := CKAGameSt.canSend_iff s.ck p |>.mp hc
      refine ⟨ckaReach_sent hc _ _, fun p' hp' => ?_, fun q' hq' => ?_⟩
      · exfalso
        have := (CKAGameSt.canSend_iff _ p').mp hp'
        cases p <;> simp at this <;> omega
      · have hq : q' = p.other := by
          rw [CKAGameSt.canRecv_iff] at hq'
          rcases CKAParty.eq_or_eq_other q' p with h | h
          · subst h
            cases q' <;> simp at hq' <;> omega
          · exact h
        subst hq
        simp only [CKAGameSt.sent_st, CKAParty.other_ne, ite_false, CKAParty.other_other,
          ite_true, CKAGameSt.sent_msg, SMLoc.opened, Function.update_of_ne (CKAParty.other_ne p),
          Function.update_self, hsrk, hJ.key _ _ r hsJ]
        exact ⟨trivial, hJ.next _ _ r hsJ, trivial⟩
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
      rw [hx]; exact hs
  | recv p =>
    simp only [smOracleOf] at hx
    split at hx
    · rename_i hc
      simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
      subst hx
      obtain ⟨hout, hJn, hrk⟩ := hs.recv p hc
      obtain ⟨ht, hsend⟩ := ckaReach_recv hs.reach hc
      refine ⟨ckaReach_recvd hc _, fun p' hp' => ?_, fun q' hq' => ?_⟩
      · have hp : p' = p := by
          have hA : (s.ck.recvd p (C.recv (s.ck.st p) s.ck.msg).1).t .A = s.ck.t p.other := by
            rw [CKAGameSt.recvd_t]
            cases p
            · simp only [CKAParty.other_A] at ht ⊢; simp; omega
            · simp
          have h := ((CKAGameSt.canSend_iff _ p').mp hp').2
          rw [hA, ckaSender_succ, hsend, CKAParty.other_other] at h
          exact h.symm
        subst hp
        simp only [CKAGameSt.recvd_st, ite_true, CKAParty.other_ne, ite_false, SMLoc.received,
          hout, SMLoc.recvY, Function.update_self, Function.update_of_ne (CKAParty.other_ne p'),
          hrk]
        exact ⟨hJn, trivial⟩
      · exfalso
        rw [CKAGameSt.canRecv_iff] at hq'
        cases p <;> cases q' <;> simp at hq' ht <;> omega
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
      rw [hx]; exact hs
  | send p m =>
    simp only [smOracleOf] at hx
    split at hx
    · split at hx
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
        rw [hx]; exact hs.of_eq rfl rfl rfl
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
        rw [hx]; exact hs
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
      rw [hx]; exact hs
  | chall p m =>
    simp only [smOracleOf] at hx
    split at hx
    · split at hx
      · simp only [PMF.support_bind, Set.mem_iUnion, PMF.support_pure, Set.mem_singleton_iff]
          at hx
        obtain ⟨c, -, rfl⟩ := hx
        exact hs.of_eq rfl rfl rfl
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
        rw [hx]; exact hs
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
      rw [hx]; exact hs
  | corrupt p =>
    simp only [smOracleOf, PMF.support_pure, Set.mem_singleton_iff] at hx
    rw [hx]; exact hs

omit [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct] [Fintype RK]
  [Nonempty RK] in
theorem SMSt.toScheme_smInit (i : Msg × Sc × Sc) (rk : RK) :
    SMSt.toScheme (smInit (Sa := Sa) i rk) =
      SMSchemeSt.init (i.1, ⟨i.2.1, rk, none, none⟩, ⟨i.2.2, rk, none, none⟩) := by
  simp only [SMSt.toScheme, smInit, SMLoc.init, SMSchemeSt.init, CKAGameSt.init,
    SMSchemeSt.mk.injEq, CKAGameSt.mk.injEq, and_true]
  funext q
  cases q <;> rfl

omit [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct] [Fintype RK]
  [Nonempty RK] in
/-- The initial state of `sm_corrupt_game` satisfies `ACDInv` when `J` relates the initial
states. -/
theorem acdInv_smInit (C : CKADef Sc Msg Key) (R : PRGDef (RK × Key) (RK × Sa))
    {J : Sc → Sc → Prop} (i : Msg × Sc × Sc) (hi : J i.2.1 i.2.2) (rk : RK) :
    ACDInv C R J (smInit (Sa := Sa) i rk) := by
  refine ⟨ckaReach_init _ _ _, fun p hp => ?_, fun q hq => ?_⟩
  · have h := ((CKAGameSt.canSend_iff _ p).mp hp).2
    simp only [smInit, CKAGameSt.init, ckaSender, Nat.zero_add, Nat.one_mod, ite_true] at h
    subst h
    exact ⟨hi, rfl⟩
  · exfalso
    rw [CKAGameSt.canRecv_iff] at hq
    simp [smInit, CKAGameSt.init] at hq

/-- **The corruption game over `acdSM` is `sm_corrupt_game`.** For a CKA `C` correct along `J`,
with an initialisation that is the lift of `initP` and initial states related by `J`, the
corruption game over the ACD construction against an adversary `A` is the game
`sm_corrupt_game C R G D` against `A` with the answers relabelled. -/
theorem smCorruptGame_acd (C : CKADef Sc Msg Key) [CKACoins C Rand] {J : Sc → Sc → Prop}
    (hJ : CKACorrect C J) (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (hJi : ∀ i ∈ initP.support, J i.2.1 i.2.2) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (ΔFS ΔPCS : ℕ) (ideal : Bool)
    (A : SMSchemeAdv Msg W Ct (SMPartySt Sc RK Sa)) :
    smCorruptGame (acdSM C R G D) ΔFS ΔPCS ideal A =
      sm_corrupt_game C R G D ΔFS ΔPCS ideal A.toSM := by
  rw [sm_corrupt_game, sm_corrupt_gameOf_eq_liftPMF C initP hinit]
  simp only [smCorruptGame, acdSM, hinit, sample_eq_liftPMF, SPComp.bind_assoc,
    SPComp.pure_bind, liftPMF_bind_liftPMF]
  refine congrArg _ (congrArg _ (funext fun t => ?_))
  refine PMF.bind_congr_support _ _ _ fun i hi => congrArg _ (funext fun rk => ?_)
  rw [← SMSt.toScheme_smInit]
  exact OracleAdv.run_map_fst_mapQueryAnswer_of_map_state_inv _ _ SMAns.toScheme
    SMSt.toScheme (ACDInv C R J) (fun s d hs => acdInv_step C R G D hJ ΔFS ΔPCS t ideal s hs d)
    (fun s d hs => acd_step C R G D J ΔFS ΔPCS t ideal s hs d) _ _
    (acdInv_smInit C R i (hJi i hi) rk)

/-- **The advantage of an adversary against `acdSM`** is the advantage of the relabelled
adversary in `sm_corrupt_game`. -/
theorem acdSM_corruptAdvantage_eq (C : CKADef Sc Msg Key) [CKACoins C Rand]
    {J : Sc → Sc → Prop} (hJ : CKACorrect C J) (initP : PMF (Msg × Sc × Sc))
    (hinit : C.init = liftPMF initP) (hJi : ∀ i ∈ initP.support, J i.2.1 i.2.2)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (A : SMSchemeAdv Msg W Ct (SMPartySt Sc RK Sa)) :
    (acdSM C R G D).corruptAdvantage ΔFS ΔPCS A = SM_Corrupt_Advantage C R G D ΔFS ΔPCS A.toSM := by
  simp only [SMScheme.corruptAdvantage, SM_Corrupt_Advantage,
    smCorruptGame_acd C hJ initP hinit hJi]

/-- **The adaptive oracle of `sm_adaptive_game` is the adaptive oracle over `acdSM`** under
the invariant `ACDInv` of its secure-messaging state. -/
theorem acd_ad_step (C : CKADef Sc Msg Key) [CKACoins C Rand] (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (J : Sc → Sc → Prop) (ΔFS ΔPCS : ℕ)
    (ideal : Bool) (x : SMSt Sc Msg RK Sa × SMAdRec) (hx : ACDInv C R J x.1) (q : SMQuery W) :
    (smAdOracle C R G D ΔFS ΔPCS ideal x q).map
        (fun y => (SMAns.toScheme y.1, (y.2.1.toScheme, y.2.2))) =
      smSchemeAdOracle (acdSM C R G D) ΔFS ΔPCS ideal (x.1.toScheme, x.2) q := by
  have hmap : ∀ q' : SMQuery W,
      ((smOracleOf C R G D ΔFS ΔPCS 0 ideal (realRoot R) x.1 q').map
          fun y => (y.1, (y.2, x.2))).map
        (fun y => (SMAns.toScheme y.1, (y.2.1.toScheme, y.2.2))) =
      (smSchemeOracle (acdSM C R G D) ΔFS ΔPCS 0 ideal x.1.toScheme q').map
        fun y => (y.1, (y.2, x.2)) := fun q' => by
    rw [PMF.map_comp, ← acd_step C R G D J ΔFS ΔPCS 0 ideal x.1 hx q', PMF.map_comp]
    rfl
  cases q with
  | ratchet p => exact hmap _
  | recv p => exact hmap _
  | send p m => exact hmap _
  | chall p m =>
    simp only [smAdOracle, smSchemeAdOracle, SMSt.toScheme_ck_t, SMSt.toScheme_ck_st, acdSM,
      SMSt.toScheme_done]
    cases hsnd : x.1.loc.snd p with
    | none =>
      simp only [Option.map_none, PMF.pure_map]
      by_cases hc : x.2.cE = none ∧ x.1.loc.done = false ∧ x.2.lo ≤ x.1.ck.t p ∧
          ckaSender (x.1.ck.t p) = p <;>
        simp only [hc, and_self, ite_true, ite_false] <;> rfl
    | some sa =>
      simp only [Option.map_some]
      by_cases hc : x.2.cE = none ∧ x.1.loc.done = false ∧ x.2.lo ≤ x.1.ck.t p ∧
          ckaSender (x.1.ck.t p) = p
      · simp only [hc, and_self, ite_true, PMF.map_bind, PMF.pure_map, SMAns.toScheme, challCt,
          SMSt.toScheme_advanced_done]
      · simp only [hc, ite_false, PMF.pure_map]
        rfl
  | corrupt p =>
    simp only [smAdOracle, smSchemeAdOracle, SMSt.toScheme_ck_t, SMSt.toScheme_ck_st, acdSM]
    cases x.2.cE with
    | none => simp only [PMF.pure_map, SMAns.toScheme]; rfl
    | some e =>
      simp only [PMF.pure_map]
      by_cases hc : e + ΔFS ≤ x.1.ck.t p <;> simp only [hc, ite_true, ite_false] <;> rfl

omit [Fintype RK] [Nonempty RK] in
/-- **The invariant `ACDInv` is kept by the adaptive oracle.** -/
theorem acdInv_ad_step (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    {J : Sc → Sc → Prop} (hJ : CKACorrect C J) (ΔFS ΔPCS : ℕ) (ideal : Bool)
    (x : SMSt Sc Msg RK Sa × SMAdRec) (hx : ACDInv C R J x.1) (q : SMQuery W) :
    ∀ y ∈ (smAdOracle C R G D ΔFS ΔPCS ideal x q).support, ACDInv C R J y.2.1 := by
  have hmap : ∀ q' : SMQuery W, ∀ y ∈ ((smOracleOf C R G D ΔFS ΔPCS 0 ideal (realRoot R) x.1
      q').map fun y => (y.1, (y.2, x.2))).support, ACDInv C R J y.2.1 := by
    intro q' y hy
    rw [PMF.support_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact acdInv_step C R G D hJ ΔFS ΔPCS 0 ideal x.1 hx q' z hz
  intro y hy
  cases q with
  | ratchet p => exact hmap _ y hy
  | recv p => exact hmap _ y hy
  | send p m => exact hmap _ y hy
  | chall p m =>
    simp only [smAdOracle] at hy
    split at hy
    · split at hy
      · simp only [PMF.support_bind, Set.mem_iUnion, PMF.support_pure, Set.mem_singleton_iff]
          at hy
        obtain ⟨c, -, rfl⟩ := hy
        exact hx.of_eq rfl rfl rfl
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
        rw [hy]; exact hx
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
      rw [hy]; exact hx
  | corrupt p =>
    simp only [smAdOracle] at hy
    split at hy <;> simp only [PMF.support_pure, Set.mem_singleton_iff] at hy <;> rw [hy] <;>
      exact hx

/-- **The adaptive game over `acdSM` is `sm_adaptive_game`.** For a CKA `C` correct along `J`,
with an initialisation that is the lift of `initP` and initial states related by `J`, the game
with an adaptive challenge epoch over the ACD construction against `A` is `sm_adaptive_game`
against `A` with the answers relabelled. -/
theorem smAdaptiveGame_acd (C : CKADef Sc Msg Key) [CKACoins C Rand] {J : Sc → Sc → Prop}
    (hJ : CKACorrect C J) (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (hJi : ∀ i ∈ initP.support, J i.2.1 i.2.2) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (ΔFS ΔPCS : ℕ) (ideal : Bool)
    (A : Msg → OracleAdv (SMQuery W) (SMSchemeAns Msg Ct (SMPartySt Sc RK Sa)) Bool) :
    smAdaptiveGame (acdSM C R G D) ΔFS ΔPCS ideal A =
      sm_adaptive_game C R G D ΔFS ΔPCS ideal fun T => (A T).mapQueryAnswer id SMAns.toScheme := by
  simp only [smAdaptiveGame, sm_adaptive_game, acdSM, hinit, sample_eq_liftPMF,
    SPComp.bind_assoc, SPComp.pure_bind, liftPMF_bind_liftPMF]
  refine congrArg _ (PMF.bind_congr_support _ _ _ fun i hi => congrArg _ (funext fun rk => ?_))
  have he : (SMSchemeSt.init (i.1, (⟨i.2.1, rk, none, none⟩ : SMPartySt Sc RK Sa),
      (⟨i.2.2, rk, none, none⟩ : SMPartySt Sc RK Sa)), (⟨none, 0⟩ : SMAdRec)) =
      (fun y : SMSt Sc Msg RK Sa × SMAdRec => (y.1.toScheme, y.2)) (smInit i rk, ⟨none, 0⟩) := by
    simp only [SMSt.toScheme_smInit]
  rw [he]
  exact OracleAdv.run_map_fst_mapQueryAnswer_of_map_state_inv _ _ SMAns.toScheme
    (fun y : SMSt Sc Msg RK Sa × SMAdRec => (y.1.toScheme, y.2)) (fun y => ACDInv C R J y.1)
    (fun x d hx => acdInv_ad_step C R G D hJ ΔFS ΔPCS ideal x hx d)
    (fun x d hx => acd_ad_step C R G D J ΔFS ΔPCS ideal x hx d) _ _
    (acdInv_smInit C R i (hJi i hi) rk)

/-- **The advantage of an adversary against `acdSM` with an adaptive challenge epoch** is the
advantage of the relabelled adversary in `sm_adaptive_game`. -/
theorem acdSM_adaptiveAdvantage_eq (C : CKADef Sc Msg Key) [CKACoins C Rand]
    {J : Sc → Sc → Prop} (hJ : CKACorrect C J) (initP : PMF (Msg × Sc × Sc))
    (hinit : C.init = liftPMF initP) (hJi : ∀ i ∈ initP.support, J i.2.1 i.2.2)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ)
    (A : Msg → OracleAdv (SMQuery W) (SMSchemeAns Msg Ct (SMPartySt Sc RK Sa)) Bool) :
    (acdSM C R G D).adaptiveAdvantage ΔFS ΔPCS A =
      SM_Adaptive_Advantage C R G D ΔFS ΔPCS fun T => (A T).mapQueryAnswer id SMAns.toScheme := by
  simp only [SMScheme.adaptiveAdvantage, SM_Adaptive_Advantage,
    smAdaptiveGame_acd C hJ initP hinit hJi]

section ACDBounds

variable [Fintype Key] [Nonempty Key] [Fintype Sa] [Nonempty Sa] [DecidableEq RK]
  [DecidableEq Key]

/-- **The corruption game over `acdSM` from CKA, PRF-PRNG and FS-AEAD security.** For a CKA
correct along `J` with a sound explicit-randomness sending algorithm, and `2 ≤ ΔFS`,
`1 ≤ ΔPCS`, the advantage of every adversary `A` against the ACD construction is the bound of
`sm_corrupt_advantage_le` at the relabelled adversary `A.toSM`. -/
theorem acdSM_corruptAdvantage_le (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (hS : CKACoins.Sound C) {J : Sc → Sc → Prop} (hJ : CKACorrect C J)
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (hJi : ∀ i ∈ initP.support, J i.2.1 i.2.2) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS)
    (hPCS : 1 ≤ ΔPCS) (A : SMSchemeAdv Msg W Ct (SMPartySt Sc RK Sa)) :
    (acdSM C R G D).corruptAdvantage ΔFS ΔPCS A ≤
      ∑ b : Bool, CKA_Corrupt_Advantage C ΔFS ΔPCS (smcCKARed R G D b A.toSM) +
        ∑ b : Bool, PRFPRNG_Advantage R (smcRootRed C R G D ΔFS ΔPCS b initP A.toSM) +
        FSAEAD_Corrupt_Advantage G D (smcFSRed C R G D ΔFS ΔPCS initP A.toSM) := by
  rw [acdSM_corruptAdvantage_eq C hJ initP hinit hJi]
  exact sm_corrupt_advantage_le C hS initP hinit R G D hFS hPCS _

/-- **The game over `acdSM` with an adaptive challenge epoch** from CKA, PRF-PRNG and FS-AEAD
security: the bound of `sm_adaptive_corrupt_advantage_le` at the relabelled adversary. -/
theorem acdSM_adaptiveAdvantage_le (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (hS : CKACoins.Sound C) {J : Sc → Sc → Prop} (hJ : CKACorrect C J)
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (hJi : ∀ i ∈ initP.support, J i.2.1 i.2.2) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS)
    (hPCS : 1 ≤ ΔPCS)
    (A : Msg → OracleAdv (SMQuery W) (SMSchemeAns Msg Ct (SMPartySt Sc RK Sa)) Bool) :
    (acdSM C R G D).adaptiveAdvantage ΔFS ΔPCS A ≤
      ∑' e, (∑ b : Bool, CKA_Corrupt_Advantage C ΔFS ΔPCS
            (smcCKARed R G D b (smGuessAdv ΔFS ΔPCS
              (fun T => (A T).mapQueryAnswer id SMAns.toScheme) e)) +
        ∑ b : Bool, PRFPRNG_Advantage R (smcRootRed C R G D ΔFS ΔPCS b initP
          (smGuessAdv ΔFS ΔPCS (fun T => (A T).mapQueryAnswer id SMAns.toScheme) e)) +
        FSAEAD_Corrupt_Advantage G D (smcFSRed C R G D ΔFS ΔPCS initP
          (smGuessAdv ΔFS ΔPCS (fun T => (A T).mapQueryAnswer id SMAns.toScheme) e))) := by
  rw [acdSM_adaptiveAdvantage_eq C hJ initP hinit hJi]
  exact sm_adaptive_corrupt_advantage_le C hS initP hinit R G D hFS hPCS _

/-- **The game over `acdSM` with an adaptive challenge epoch, for an adversary with a query
bound**: the bound of `sm_adaptive_corrupt_advantage_le_of_isQueryBound` at the relabelled
adversary, which keeps the query bound `q` of `A`; the sum runs over the epochs `e ≤ q`. -/
theorem acdSM_adaptiveAdvantage_le_of_isQueryBound (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (hS : CKACoins.Sound C) {J : Sc → Sc → Prop} (hJ : CKACorrect C J)
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (hJi : ∀ i ∈ initP.support, J i.2.1 i.2.2) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS)
    (hPCS : 1 ≤ ΔPCS) {q : ℕ}
    (A : Msg → OracleAdv (SMQuery W) (SMSchemeAns Msg Ct (SMPartySt Sc RK Sa)) Bool)
    (hA : ∀ T, (A T).IsQueryBound q) :
    (acdSM C R G D).adaptiveAdvantage ΔFS ΔPCS A ≤
      ∑ e ∈ Finset.range (q + 1), (∑ b : Bool, CKA_Corrupt_Advantage C ΔFS ΔPCS
            (smcCKARed R G D b (smGuessAdv ΔFS ΔPCS
              (fun T => (A T).mapQueryAnswer id SMAns.toScheme) e)) +
        ∑ b : Bool, PRFPRNG_Advantage R (smcRootRed C R G D ΔFS ΔPCS b initP
          (smGuessAdv ΔFS ΔPCS (fun T => (A T).mapQueryAnswer id SMAns.toScheme) e)) +
        FSAEAD_Corrupt_Advantage G D (smcFSRed C R G D ΔFS ΔPCS initP
          (smGuessAdv ΔFS ΔPCS (fun T => (A T).mapQueryAnswer id SMAns.toScheme) e))) := by
  rw [acdSM_adaptiveAdvantage_eq C hJ initP hinit hJi]
  exact sm_adaptive_corrupt_advantage_le_of_isQueryBound C hS initP hinit R G D hFS hPCS _
    fun T => OracleAdv.isQueryBound_mapQueryAnswer _ _ (hA T)

end ACDBounds

end ACD

/-! ## The Diffie–Hellman CKA over a key space -/

section DHKeys

variable (G : Type) [CG : CyclicGroup G] {Sk : Type} [Fintype Sk] [Nonempty Sk]

/-- The correctness relation of `dhCKAOf`: the public value held by the next sender is the
public value of the secret key of the next receiver. -/
def dhKeyRel (decE : Sk → CG.Exp) (s r : G × Sk) : Prop := s.1 = CG.pow (decE r.2)

/-- **Correctness of `dhCKAOf`** along `dhKeyRel`. -/
theorem dhCKAOf_correct (decE : Sk → CG.Exp) :
    CKACorrect (dhCKAOf G decE) (dhKeyRel G decE) where
  key s r x h := by
    simp only [dhCKAOf, CKACoins.sendR]
    rw [show s.1 = CG.pow (decE r.2) from h]
    exact elemPow_pow_comm (decE x) (decE r.2)
  next s r x _ := rfl

/-- The initial states of `dhCKAOf` are related by `dhKeyRel`. -/
theorem dhInitPOf_rel (decE : Sk → CG.Exp) :
    ∀ i ∈ (dhInitPOf G decE).support, dhKeyRel G decE i.2.1 i.2.2 := by
  intro i hi
  simp only [dhInitPOf, PMF.support_map, Set.mem_image] at hi
  obtain ⟨x, -, rfl⟩ := hi
  rfl

end DHKeys

section DHBounds

variable (G : Type) [CG : CyclicGroup G] [DecidableEq G] {Sk RK Sa W Ct : Type} [Fintype Sk]
  [Nonempty Sk] [SampleableType W] [SampleableType Ct] [Fintype RK] [Nonempty RK]
  [DecidableEq RK] [Fintype Sa] [Nonempty Sa]

/-- **The Diffie–Hellman ACD construction over a key space with an adaptive challenge epoch,
from DDH.** Let the secret keys of `dhCKAOf G decE` be drawn uniformly from `Sk` and act
through the exponent map `decE`, and let `c` certify the distance of the drawn exponents to
uniform ones. With `2 ≤ ΔFS` and `2 ≤ ΔPCS`, the advantage of every adversary `A` asking at most
`q` queries in the game over `acdSM (dhCKAOf G decE) R F D` with an adaptive challenge epoch is
at most the sum over the epochs `e ≤ q` of the DDH advantages of the reductions
`ckaCorruptDDHRedOf`, the PRF-PRNG terms and the FS-AEAD term at the guessing reduction, plus
`(q + 1) * 8 * c.δ`: the charge `4 * c.δ` of `dhCKAOf_corrupt_advantage_le` for each of the two
CKA terms of each epoch. -/
theorem acdSM_dhCKAOf_adaptiveAdvantage_le_of_isQueryBound (decE : Sk → CG.Exp)
    (c : SamplerCert CG.Exp) (hμ : c.μ = (SDistr.uniform Sk).bind fun x => SDistr.pure (decE x))
    (hν : c.ν = SDistr.uniform CG.Exp) (R : PRGDef (RK × G) (RK × Sa))
    (F : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS)
    (hPCS : 2 ≤ ΔPCS) {q : ℕ}
    (A : G → OracleAdv (SMQuery W) (SMSchemeAns G Ct (SMPartySt (G × Sk) RK Sa)) Bool)
    (hA : ∀ T, (A T).IsQueryBound q) :
    (acdSM (dhCKAOf G decE) R F D).adaptiveAdvantage ΔFS ΔPCS A ≤
      ∑ e ∈ Finset.range (q + 1), (∑ b : Bool, DDH_Advantage G
            (ckaCorruptDDHRedOf (G := G) decE ΔFS ΔPCS (smcCKARed R F D b (smGuessAdv ΔFS ΔPCS
              (fun T => (A T).mapQueryAnswer id SMAns.toScheme) e))) +
        ∑ b : Bool, PRFPRNG_Advantage R (smcRootRed (dhCKAOf G decE) R F D ΔFS ΔPCS b
          (dhInitPOf G decE)
          (smGuessAdv ΔFS ΔPCS (fun T => (A T).mapQueryAnswer id SMAns.toScheme) e)) +
        FSAEAD_Corrupt_Advantage F D (smcFSRed (dhCKAOf G decE) R F D ΔFS ΔPCS
          (dhInitPOf G decE)
          (smGuessAdv ΔFS ΔPCS (fun T => (A T).mapQueryAnswer id SMAns.toScheme) e))) +
        (q + 1) * 8 * c.δ := by
  refine (acdSM_adaptiveAdvantage_le_of_isQueryBound (dhCKAOf G decE)
    (dhCKAOfCoins_sound G decE) (dhCKAOf_correct G decE) (dhInitPOf G decE)
    (dhCKAOf_init_eq G decE) (dhInitPOf_rel G decE) R F D hFS (le_trans (by norm_num) hPCS) A
    hA).trans ?_
  have hc : ((q : ℝ≥0∞) + 1) * 8 * c.δ =
      ∑ e ∈ Finset.range (q + 1), ∑ b : Bool, 4 * c.δ := by
    simp only [Finset.sum_const, Finset.card_range, Finset.card_univ, Fintype.card_bool,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring
  rw [hc, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun e _ => ?_
  have key : ∀ a b x y d : ℝ≥0∞, a ≤ b + d → a + x + y ≤ b + x + y + d := by
    intro a b x y d h
    calc a + x + y ≤ b + d + x + y := by gcongr
      _ = b + x + y + d := by ring
  refine key _ _ _ _ _ ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun b _ => dhCKAOf_corrupt_advantage_le decE c hμ hν hFS hPCS _

end DHBounds

/-! ## Simulations of schemes and the transfer of the games -/

section Sim

variable {St Pub Rand W Ct Leak St' Pub' Ct' Leak' : Type} [Fintype Rand] [Nonempty Rand]

/-- **A simulation of schemes.** The scheme `M'` simulates `M` along the relation `ρ` of
party states, with public values encoded by `encP`, ciphertexts by `encC`, corruption answers
by `encL` and initial states by `encI`: the initialisation of `M'` is that of `M` encoded, the
encoded initial states are related, and from related states opening an epoch on the same
randomness, receiving the encoded public value and sending the same message give related
states and encoded outputs; related states give encoded corruption answers, and the ideal
ciphertexts of `M'` are those of `M` encoded. -/
structure SMScheme.Sim (M' : SMScheme St' Pub' Rand W Ct' Leak')
    (M : SMScheme St Pub Rand W Ct Leak) (ρ : St' → St → Prop) (encP : Pub → Pub')
    (encC : Ct → Ct') (encL : Leak → Leak') (encI : St → St') : Prop where
  /-- The initialisation of `M'` is the encoded initialisation of `M`. -/
  init : M'.init = SPComp.bind M.init fun i => SPComp.pure (encP i.1, encI i.2.1, encI i.2.2)
  /-- The encoded initial states are related. -/
  init_rel : ∀ x, ρ (encI x) x
  /-- Opening an epoch. -/
  ratchet : ∀ x' x r, ρ x' x →
    ρ (M'.ratchet x' r).1 (M.ratchet x r).1 ∧ (M'.ratchet x' r).2 = encP (M.ratchet x r).2
  /-- Receiving. -/
  recv : ∀ x' x T, ρ x' x → ρ (M'.recv x' (encP T)) (M.recv x T)
  /-- Sending. -/
  send : ∀ x' x m, ρ x' x →
    Option.Rel (fun y' y => ρ y'.1 y.1 ∧ y'.2 = encC y.2) (M'.send x' m) (M.send x m)
  /-- Corruption. -/
  expose : ∀ x' x, ρ x' x → M'.expose x' = encL (M.expose x)
  /-- The ideal ciphertexts. -/
  idealCt : M'.idealCt = M.idealCt.map encC

/-- The relation of the game states along a relation of party states: related party states,
the same counters and challenge flag, the encoded public value in transit. -/
structure SMSchemeSt.Related (ρ : St' → St → Prop) (encP : Pub → Pub')
    (s' : SMSchemeSt St' Pub') (s : SMSchemeSt St Pub) : Prop where
  /-- Related party states. -/
  st : ∀ p, ρ (s'.ck.st p) (s.ck.st p)
  /-- The same counters. -/
  t : s'.ck.t = s.ck.t
  /-- The encoded public value in transit. -/
  msg : s'.ck.msg = encP s.ck.msg
  /-- The same challenge flag. -/
  done : s'.done = s.done

/-- An adversary against `M'` as an adversary against `M`: the public value of the
initialisation and the answers are encoded before `A` reads them. -/
def SMSchemeAdv.comap (encP : Pub → Pub') (encC : Ct → Ct') (encL : Leak → Leak')
    (A : SMSchemeAdv Pub' W Ct' Leak') : SMSchemeAdv Pub W Ct Leak where
  tStar := A.tStar
  play t T := (A.play t (encP T)).mapQueryAnswer id (SMSchemeAns.map encP encC encL)

omit [Fintype Rand] [Nonempty Rand] in
/-- The adversary with encoded answers `A.comap encP encC encL` keeps the query bound of
`A`. -/
theorem SMSchemeAdv.comap_play_isQueryBound {encP : Pub → Pub'} {encC : Ct → Ct'}
    {encL : Leak → Leak'} {A : SMSchemeAdv Pub' W Ct' Leak'} {q : ℕ}
    (hA : ∀ t T, (A.play t T).IsQueryBound q) (t : ℕ) (T : Pub) :
    ((A.comap encP encC encL).play t T).IsQueryBound q :=
  OracleAdv.isQueryBound_mapQueryAnswer _ _ (hA t (encP T))

theorem SMSchemeSt.Related.upd {ρ : St' → St → Prop} {encP : Pub → Pub'}
    {s' : SMSchemeSt St' Pub'} {s : SMSchemeSt St Pub} (h : SMSchemeSt.Related ρ encP s' s)
    (p : CKAParty) {x' : St'} {x : St} (hx : ρ x' x) (d : Bool) :
    SMSchemeSt.Related ρ encP (s'.upd p x' d) (s.upd p x d) := by
  refine ⟨fun q => ?_, h.t, h.msg, rfl⟩
  by_cases hq : q = p
  · subst hq; simpa [SMSchemeSt.upd] using hx
  · simpa [SMSchemeSt.upd, Function.update_of_ne hq] using h.st q

/-- A deterministic pair of calls is coupled. -/
theorem coupling_pure {R S S'' R'' : Type} (e : R → R'') (Rel : S'' → S → Prop) (a : R) (s : S)
    (s' : S'') (h : Rel s' s) :
    ∃ ν : PMF ((R × S) × S''), ν.map Prod.fst = PMF.pure (a, s) ∧
      ν.map (fun z => (e z.1.1, z.2)) = PMF.pure (e a, s') ∧ ∀ z ∈ ν.support, Rel z.2 z.1.2 :=
  ⟨PMF.pure ((a, s), s'), by simp [PMF.pure_map], by simp [PMF.pure_map], fun z hz => by
    rw [PMF.mem_support_pure_iff] at hz; subst hz; exact h⟩

/-- Two calls drawing the same value and then deterministic are coupled. -/
theorem coupling_bind {R S S'' R'' β : Type} (e : R → R'') (Rel : S'' → S → Prop) (μ : PMF β)
    (f : β → R × S) (g : β → S'') (h : ∀ b, Rel (g b) (f b).2) :
    ∃ ν : PMF ((R × S) × S''), ν.map Prod.fst = μ.bind (fun b => PMF.pure (f b)) ∧
      ν.map (fun z => (e z.1.1, z.2)) = μ.bind (fun b => PMF.pure (e (f b).1, g b)) ∧
      ∀ z ∈ ν.support, Rel z.2 z.1.2 :=
  ⟨μ.bind fun b => PMF.pure (f b, g b), by simp [PMF.map_bind, PMF.pure_map],
    by simp [PMF.map_bind, PMF.pure_map], fun z hz => by
      simp only [PMF.support_bind, Set.mem_iUnion, PMF.support_pure, Set.mem_singleton_iff]
        at hz
      obtain ⟨b, -, rfl⟩ := hz
      exact h b⟩

/-- **The oracles of simulating schemes are coupled.** From related game states, each call of
the oracle over `M'` is coupled with the call over `M` along the relation of game states, with
the answers of `M` encoded. -/
theorem smScheme_sim_step {M' : SMScheme St' Pub' Rand W Ct' Leak'}
    {M : SMScheme St Pub Rand W Ct Leak} {ρ : St' → St → Prop} {encP : Pub → Pub'}
    {encC : Ct → Ct'} {encL : Leak → Leak'} {encI : St → St'}
    (h : M'.Sim M ρ encP encC encL encI) (ΔFS ΔPCS t : ℕ) (ideal : Bool)
    (s' : SMSchemeSt St' Pub') (s : SMSchemeSt St Pub) (hs : SMSchemeSt.Related ρ encP s' s)
    (q : SMQuery W) :
    ∃ ν : PMF ((SMSchemeAns Pub Ct Leak × SMSchemeSt St Pub) × SMSchemeSt St' Pub'),
      ν.map Prod.fst = smSchemeOracle M ΔFS ΔPCS t ideal s q ∧
      ν.map (fun z => (SMSchemeAns.map encP encC encL z.1.1, z.2)) =
        smSchemeOracle M' ΔFS ΔPCS t ideal s' q ∧
      ∀ z ∈ ν.support, SMSchemeSt.Related ρ encP z.2 z.1.2 := by
  have hcs : ∀ p, s'.ck.canSend p = s.ck.canSend p := fun p => by
    simp only [CKAGameSt.canSend]; rw [hs.t]
  have hcr : ∀ p, s'.ck.canRecv p = s.ck.canRecv p := fun p => by
    simp only [CKAGameSt.canRecv]; rw [hs.t]
  cases q with
  | ratchet p =>
    simp only [smSchemeOracle, hcs]
    by_cases hc : s.ck.canSend p = true
    · simp only [hc, ite_true]
      have := coupling_bind (SMSchemeAns.map encP encC encL) (SMSchemeSt.Related ρ encP)
        (PMF.uniformFintype Rand)
        (fun r => (SMSchemeAns.msg (M.ratchet (s.ck.st p) r).2,
          (⟨s.ck.sent p (M.ratchet (s.ck.st p) r).1 (M.ratchet (s.ck.st p) r).2, s.done⟩ :
            SMSchemeSt St Pub)))
        (fun r => ⟨s'.ck.sent p (M'.ratchet (s'.ck.st p) r).1 (M'.ratchet (s'.ck.st p) r).2,
          s'.done⟩) fun r => by
          obtain ⟨h1, h2⟩ := h.ratchet _ _ r (hs.st p)
          refine ⟨fun q => ?_, ?_, ?_, hs.done⟩
          · by_cases hq : q = p
            · subst hq; simpa using h1
            · simpa [hq] using hs.st q
          · funext q; simp [hs.t]
          · simpa using h2
      obtain ⟨ν, h1, h2, h3⟩ := this
      refine ⟨ν, h1, h2.trans ?_, h3⟩
      refine congrArg _ (funext fun r => ?_)
      simp only [SMSchemeAns.map, (h.ratchet _ _ r (hs.st p)).2]
    · simp only [hc, Bool.false_eq_true, ite_false]
      exact coupling_pure _ _ _ _ _ hs
  | recv p =>
    simp only [smSchemeOracle, hcr]
    by_cases hc : s.ck.canRecv p = true
    · simp only [hc, ite_true, hs.msg]
      refine coupling_pure _ _ _ _ _ ⟨fun q => ?_, ?_, by simpa using hs.msg, hs.done⟩
      · by_cases hq : q = p
        · subst hq; simpa using h.recv _ _ s.ck.msg (hs.st q)
        · simpa [hq] using hs.st q
      · funext q; simp [hs.t]
    · simp only [hc, Bool.false_eq_true, ite_false]
      exact coupling_pure _ _ _ _ _ hs
  | send p m =>
    simp only [smSchemeOracle, hs.t]
    by_cases hc : (ckaSender (s.ck.t p) == p) = true
    · simp only [hc, ite_true]
      have hr := h.send _ _ m (hs.st p)
      cases h1 : M'.send (s'.ck.st p) m <;> cases h2 : M.send (s.ck.st p) m <;>
        rw [h1, h2] at hr <;> cases hr
      · exact coupling_pure _ _ _ _ _ hs
      · rename_i y' y hy
        dsimp only
        rw [hy.2, hs.done]
        exact coupling_pure _ _ _ _ _ (hs.upd p hy.1 _)
    · simp only [hc, Bool.false_eq_true, ite_false]
      exact coupling_pure _ _ _ _ _ hs
  | chall p m =>
    simp only [smSchemeOracle, hs.t, hs.done]
    by_cases hc : (!s.done && (ckaSender (s.ck.t p) == p) && (s.ck.t p == t)) = true
    · simp only [hc, ite_true]
      have hr := h.send _ _ m (hs.st p)
      cases h1 : M'.send (s'.ck.st p) m <;> cases h2 : M.send (s.ck.st p) m <;>
        rw [h1, h2] at hr <;> cases hr
      · exact coupling_pure _ _ _ _ _ hs
      · rename_i y' y hy
        dsimp only
        have hμ : (if ideal then M'.idealCt else PMF.pure y'.2) =
            (if ideal then M.idealCt else PMF.pure y.2).map encC := by
          split_ifs
          · exact h.idealCt
          · rw [hy.2, PMF.pure_map]
        rw [hμ, PMF.bind_map]
        exact coupling_bind _ _ _ (fun c => (SMSchemeAns.ct c, s.upd p y.1 true))
          (fun _ => s'.upd p y'.1 true) fun _ => hs.upd p hy.1 true
    · simp only [hc, Bool.false_eq_true, ite_false]
      exact coupling_pure _ _ _ _ _ hs
  | corrupt p =>
    simp only [smSchemeOracle]
    have hac : ckaAllowCorr ΔFS ΔPCS t s'.ck p = ckaAllowCorr ΔFS ΔPCS t s.ck p := by
      simp only [ckaAllowCorr]; rw [hs.t]
    rw [hac]
    by_cases hc : ckaAllowCorr ΔFS ΔPCS t s.ck p = true
    · simp only [hc, ite_true, h.expose _ _ (hs.st p)]
      exact coupling_pure _ _ _ _ _ hs
    · simp only [hc, Bool.false_eq_true, ite_false]
      exact coupling_pure _ _ _ _ _ hs

/-- The relation of the states of the adaptive games: related game states, the same record. -/
def SMSchemeSt.RelatedAd (ρ : St' → St → Prop) (encP : Pub → Pub')
    (x' : SMSchemeSt St' Pub' × SMAdRec) (x : SMSchemeSt St Pub × SMAdRec) : Prop :=
  SMSchemeSt.Related ρ encP x'.1 x.1 ∧ x'.2 = x.2

/-- **The adaptive oracles of simulating schemes are coupled.** -/
theorem smScheme_sim_ad_step {M' : SMScheme St' Pub' Rand W Ct' Leak'}
    {M : SMScheme St Pub Rand W Ct Leak} {ρ : St' → St → Prop} {encP : Pub → Pub'}
    {encC : Ct → Ct'} {encL : Leak → Leak'} {encI : St → St'}
    (h : M'.Sim M ρ encP encC encL encI) (ΔFS ΔPCS : ℕ) (ideal : Bool)
    (s' : SMSchemeSt St' Pub') (s : SMSchemeSt St Pub) (r : SMAdRec)
    (hs : SMSchemeSt.Related ρ encP s' s) (q : SMQuery W) :
    ∃ ν : PMF ((SMSchemeAns Pub Ct Leak × (SMSchemeSt St Pub × SMAdRec)) ×
        (SMSchemeSt St' Pub' × SMAdRec)),
      ν.map Prod.fst = smSchemeAdOracle M ΔFS ΔPCS ideal (s, r) q ∧
      ν.map (fun z => (SMSchemeAns.map encP encC encL z.1.1, z.2)) =
        smSchemeAdOracle M' ΔFS ΔPCS ideal (s', r) q ∧
      ∀ z ∈ ν.support, SMSchemeSt.RelatedAd ρ encP z.2 z.1.2 := by
  have hbase : ∀ q' : SMQuery W, ∃ ν : PMF ((SMSchemeAns Pub Ct Leak × (SMSchemeSt St Pub ×
        SMAdRec)) × (SMSchemeSt St' Pub' × SMAdRec)),
      ν.map Prod.fst = (smSchemeOracle M ΔFS ΔPCS 0 ideal s q').map (fun y => (y.1, (y.2, r))) ∧
      ν.map (fun z => (SMSchemeAns.map encP encC encL z.1.1, z.2)) =
        (smSchemeOracle M' ΔFS ΔPCS 0 ideal s' q').map (fun y => (y.1, (y.2, r))) ∧
      ∀ z ∈ ν.support, SMSchemeSt.RelatedAd ρ encP z.2 z.1.2 := by
    intro q'
    obtain ⟨ν, h1, h2, h3⟩ := smScheme_sim_step h ΔFS ΔPCS 0 ideal s' s hs q'
    refine ⟨ν.map fun z => ((z.1.1, (z.1.2, r)), (z.2, r)), ?_, ?_, ?_⟩
    · rw [← h1, PMF.map_comp, PMF.map_comp]; rfl
    · rw [← h2, PMF.map_comp, PMF.map_comp]; rfl
    · intro z hz
      rw [PMF.support_map] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact ⟨h3 w hw, rfl⟩
  cases q with
  | ratchet p => exact hbase _
  | recv p => exact hbase _
  | send p m => exact hbase _
  | chall p m =>
    simp only [smSchemeAdOracle, hs.t, hs.done]
    by_cases hc : r.cE = none ∧ s.done = false ∧ r.lo ≤ s.ck.t p ∧ ckaSender (s.ck.t p) = p
    · simp only [hc, and_self, ite_true]
      have hr := h.send _ _ m (hs.st p)
      cases h1 : M'.send (s'.ck.st p) m <;> cases h2 : M.send (s.ck.st p) m <;>
        rw [h1, h2] at hr <;> cases hr
      · exact coupling_pure _ (SMSchemeSt.RelatedAd ρ encP) _ _ _
          ⟨hs, rfl⟩
      · rename_i y' y hy
        dsimp only
        have hμ : (if ideal then M'.idealCt else PMF.pure y'.2) =
            (if ideal then M.idealCt else PMF.pure y.2).map encC := by
          split_ifs
          · exact h.idealCt
          · rw [hy.2, PMF.pure_map]
        rw [hμ, PMF.bind_map]
        exact coupling_bind _ (SMSchemeSt.RelatedAd ρ encP) _
          (fun c => (SMSchemeAns.ct c, (s.upd p y.1 true, (⟨some (s.ck.t p), r.lo⟩ : SMAdRec))))
          (fun _ => (s'.upd p y'.1 true, ⟨some (s.ck.t p), r.lo⟩))
          fun _ => ⟨hs.upd p hy.1 true, rfl⟩
    · simp only [hc, ite_false]
      exact coupling_pure _ (SMSchemeSt.RelatedAd ρ encP) _ _ _
        ⟨hs, rfl⟩
  | corrupt p =>
    simp only [smSchemeAdOracle, hs.t]
    cases r.cE with
    | none =>
      simp only [h.expose _ _ (hs.st p)]
      exact coupling_pure _ (SMSchemeSt.RelatedAd ρ encP) _ _ _
        ⟨hs, rfl⟩
    | some e =>
      by_cases hc : e + ΔFS ≤ s.ck.t p
      · simp only [hc, ite_true, h.expose _ _ (hs.st p)]
        exact coupling_pure _ (SMSchemeSt.RelatedAd ρ encP) _ _ _
          ⟨hs, rfl⟩
      · simp only [hc, ite_false]
        exact coupling_pure _ (SMSchemeSt.RelatedAd ρ encP) _ _ _
          ⟨hs, rfl⟩

omit [Fintype Rand] [Nonempty Rand] in
theorem SMSchemeSt.related_init {ρ : St' → St → Prop} {encP : Pub → Pub'} {encI : St → St'}
    (hI : ∀ x, ρ (encI x) x) (i : Pub × St × St) :
    SMSchemeSt.Related ρ encP (SMSchemeSt.init (encP i.1, encI i.2.1, encI i.2.2))
      (SMSchemeSt.init i) :=
  ⟨fun p => by cases p <;> exact hI _, rfl, rfl, rfl⟩

/-- **Transfer of the corruption game along a simulation.** If `M'` simulates `M`, the
corruption game over `M'` against `A` is the corruption game over `M` against `A` with the
public values, ciphertexts and corruption answers encoded. -/
theorem smCorruptGame_sim {M' : SMScheme St' Pub' Rand W Ct' Leak'}
    {M : SMScheme St Pub Rand W Ct Leak} {ρ : St' → St → Prop} {encP : Pub → Pub'}
    {encC : Ct → Ct'} {encL : Leak → Leak'} {encI : St → St'}
    (h : M'.Sim M ρ encP encC encL encI) (ΔFS ΔPCS : ℕ) (ideal : Bool)
    (A : SMSchemeAdv Pub' W Ct' Leak') :
    smCorruptGame M' ΔFS ΔPCS ideal A =
      smCorruptGame M ΔFS ΔPCS ideal (A.comap encP encC encL) := by
  simp only [smCorruptGame, h.init, SPComp.bind_assoc, SPComp.pure_bind, SMSchemeAdv.comap]
  refine congrArg _ (funext fun t => congrArg _ (funext fun i => congrArg _ ?_))
  exact OracleAdv.run_map_fst_mapQueryAnswer_of_coupling _ _ _ (SMSchemeSt.Related ρ encP)
    (fun s' s d hs => smScheme_sim_step h ΔFS ΔPCS t ideal s' s hs d) _ _ _
    (SMSchemeSt.related_init h.init_rel i)

/-- **Transfer of the game with an adaptive challenge epoch along a simulation.** -/
theorem smAdaptiveGame_sim {M' : SMScheme St' Pub' Rand W Ct' Leak'}
    {M : SMScheme St Pub Rand W Ct Leak} {ρ : St' → St → Prop} {encP : Pub → Pub'}
    {encC : Ct → Ct'} {encL : Leak → Leak'} {encI : St → St'}
    (h : M'.Sim M ρ encP encC encL encI) (ΔFS ΔPCS : ℕ) (ideal : Bool)
    (A : Pub' → OracleAdv (SMQuery W) (SMSchemeAns Pub' Ct' Leak') Bool) :
    smAdaptiveGame M' ΔFS ΔPCS ideal A =
      smAdaptiveGame M ΔFS ΔPCS ideal
        fun T => (A (encP T)).mapQueryAnswer id (SMSchemeAns.map encP encC encL) := by
  simp only [smAdaptiveGame, h.init, SPComp.bind_assoc, SPComp.pure_bind]
  refine congrArg _ (funext fun i => congrArg _ ?_)
  exact OracleAdv.run_map_fst_mapQueryAnswer_of_coupling _ _ _
    (SMSchemeSt.RelatedAd ρ encP)
    (fun x' x d hx => by
      obtain ⟨s', r'⟩ := x'
      obtain ⟨s, r⟩ := x
      obtain ⟨hs, hr⟩ := hx
      dsimp only at hr
      subst hr
      exact smScheme_sim_ad_step h ΔFS ΔPCS ideal s' s r' hs d) _ _ _
    ⟨SMSchemeSt.related_init h.init_rel i, rfl⟩

/-- **The advantage transfers along a simulation.** -/
theorem SMScheme.Sim.corruptAdvantage_eq {M' : SMScheme St' Pub' Rand W Ct' Leak'}
    {M : SMScheme St Pub Rand W Ct Leak} {ρ : St' → St → Prop} {encP : Pub → Pub'}
    {encC : Ct → Ct'} {encL : Leak → Leak'} {encI : St → St'}
    (h : M'.Sim M ρ encP encC encL encI) (ΔFS ΔPCS : ℕ) (A : SMSchemeAdv Pub' W Ct' Leak') :
    M'.corruptAdvantage ΔFS ΔPCS A = M.corruptAdvantage ΔFS ΔPCS (A.comap encP encC encL) := by
  simp only [SMScheme.corruptAdvantage, smCorruptGame_sim h]

/-- **The advantage with an adaptive challenge epoch transfers along a simulation.** -/
theorem SMScheme.Sim.adaptiveAdvantage_eq {M' : SMScheme St' Pub' Rand W Ct' Leak'}
    {M : SMScheme St Pub Rand W Ct Leak} {ρ : St' → St → Prop} {encP : Pub → Pub'}
    {encC : Ct → Ct'} {encL : Leak → Leak'} {encI : St → St'}
    (h : M'.Sim M ρ encP encC encL encI) (ΔFS ΔPCS : ℕ)
    (A : Pub' → OracleAdv (SMQuery W) (SMSchemeAns Pub' Ct' Leak') Bool) :
    M'.adaptiveAdvantage ΔFS ΔPCS A =
      M.adaptiveAdvantage ΔFS ΔPCS
        fun T => (A (encP T)).mapQueryAnswer id (SMSchemeAns.map encP encC encL) := by
  simp only [SMScheme.adaptiveAdvantage, smAdaptiveGame_sim h]

end Sim

section SimDH

variable (G : Type) [CG : CyclicGroup G] [DecidableEq G] {Sk RK Sa W Ct St' Pub' Ct' Leak' : Type}
  [Fintype Sk] [Nonempty Sk] [SampleableType W] [SampleableType Ct] [Fintype RK] [Nonempty RK]
  [DecidableEq RK] [Fintype Sa] [Nonempty Sa]

/-- **A scheme that simulates the Diffie–Hellman ACD construction, with an adaptive challenge
epoch and a query bound, from DDH.** If `M'` simulates `acdSM (dhCKAOf G decE) R F D`, the
advantage of every adversary `A` asking at most `q` queries in the game over `M'` with an
adaptive challenge epoch is the bound of `acdSM_dhCKAOf_adaptiveAdvantage_le_of_isQueryBound` at
`A` with its answers encoded, which asks at most `q` queries: the finite sum over the epochs
`e ≤ q` of the DDH, PRF-PRNG and FS-AEAD terms, plus `(q + 1) * 8 * c.δ`. -/
theorem SMScheme.Sim.adaptiveAdvantage_le_dhCKAOf_of_isQueryBound (decE : Sk → CG.Exp)
    (c : SamplerCert CG.Exp) (hμ : c.μ = (SDistr.uniform Sk).bind fun x => SDistr.pure (decE x))
    (hν : c.ν = SDistr.uniform CG.Exp) (R : PRGDef (RK × G) (RK × Sa))
    (F : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) {M' : SMScheme St' Pub' Sk W Ct' Leak'}
    {ρ : St' → SMPartySt (G × Sk) RK Sa → Prop} {encP : G → Pub'} {encC : Ct → Ct'}
    {encL : SMPartySt (G × Sk) RK Sa → Leak'} {encI : SMPartySt (G × Sk) RK Sa → St'}
    (h : M'.Sim (acdSM (dhCKAOf G decE) R F D) ρ encP encC encL encI) {ΔFS ΔPCS : ℕ}
    (hFS : 2 ≤ ΔFS) (hPCS : 2 ≤ ΔPCS) {q : ℕ}
    (A : Pub' → OracleAdv (SMQuery W) (SMSchemeAns Pub' Ct' Leak') Bool)
    (hA : ∀ T, (A T).IsQueryBound q) :
    M'.adaptiveAdvantage ΔFS ΔPCS A ≤
      ∑ e ∈ Finset.range (q + 1), (∑ b : Bool, DDH_Advantage G
            (ckaCorruptDDHRedOf (G := G) decE ΔFS ΔPCS (smcCKARed R F D b (smGuessAdv ΔFS ΔPCS
              (fun T => ((A (encP T)).mapQueryAnswer id
                (SMSchemeAns.map encP encC encL)).mapQueryAnswer id SMAns.toScheme) e))) +
        ∑ b : Bool, PRFPRNG_Advantage R (smcRootRed (dhCKAOf G decE) R F D ΔFS ΔPCS b
          (dhInitPOf G decE) (smGuessAdv ΔFS ΔPCS
            (fun T => ((A (encP T)).mapQueryAnswer id
              (SMSchemeAns.map encP encC encL)).mapQueryAnswer id SMAns.toScheme) e)) +
        FSAEAD_Corrupt_Advantage F D (smcFSRed (dhCKAOf G decE) R F D ΔFS ΔPCS
          (dhInitPOf G decE) (smGuessAdv ΔFS ΔPCS
            (fun T => ((A (encP T)).mapQueryAnswer id
              (SMSchemeAns.map encP encC encL)).mapQueryAnswer id SMAns.toScheme) e))) +
        (q + 1) * 8 * c.δ := by
  rw [h.adaptiveAdvantage_eq]
  exact acdSM_dhCKAOf_adaptiveAdvantage_le_of_isQueryBound G decE c hμ hν R F D hFS hPCS _
    fun T => OracleAdv.isQueryBound_mapQueryAnswer _ _ (hA (encP T))

end SimDH

end CatCrypt.Crypto.Messaging
