/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.CKACorrupt
public import CatCryptCore.Crypto.Assumptions.DualPRF

/-!
# Secure messaging with state corruption

The secure-messaging game of the double ratchet with state corruption, in the style of the
CKA game with corruption of `CatCryptCore.Crypto.Messaging.CKACorrupt`, and its reduction to the
CKA game with corruption, a PRF-PRNG root step and a forward-secure AEAD (Alwen, Coretti and
Dodis, EUROCRYPT 2019, Sections 4 and 5). The module is in progress; this docstring is completed
with the main theorem.
-/

set_option autoImplicit false

@[expose] public section

/-! ## Runs of oracle adversaries: state maps under an invariant, and eager sampling -/

namespace CatCrypt.Crypto.OracleAdv

open scoped ENNReal

variable {S S' D R V α : Type}

/-- **State maps under an invariant.** A map `f` of oracle states that commutes with every
oracle call from the states satisfying `Inv`, an invariant kept on the support of every call,
commutes with every run from such a state. -/
theorem run_map_state_inv (O : S → D → PMF (R × S)) (O' : S' → D → PMF (R × S'))
    (f : S → S') (Inv : S → Prop)
    (hInv : ∀ s d, Inv s → ∀ x ∈ (O s d).support, Inv x.2)
    (hO : ∀ s d, Inv s → (O s d).map (Prod.map id f) = O' (f s) d)
    (A : OracleAdv D R α) (s : S) (hs : Inv s) :
    (run O A s).map (Prod.map id f) = run O' A (f s) := by
  induction A generalizing s with
  | ret a => simp [PMF.pure_map]
  | rand p k ih =>
    simp only [run_rand, PMF.map_bind]
    congr 1; funext b; exact ih b s hs
  | query d k ih =>
    simp only [run_query, PMF.map_bind]
    rw [← hO s d hs, PMF.bind_map]
    refine PMF.bind_congr_support _ _ _ fun x hx => ?_
    exact ih x.1 x.2 (hInv s d hs x hx)

/-- The outputs of the runs related by a state map under an invariant are equal. -/
theorem run_map_fst_of_map_state_inv (O : S → D → PMF (R × S)) (O' : S' → D → PMF (R × S'))
    (f : S → S') (Inv : S → Prop)
    (hInv : ∀ s d, Inv s → ∀ x ∈ (O s d).support, Inv x.2)
    (hO : ∀ s d, Inv s → (O s d).map (Prod.map id f) = O' (f s) d)
    (A : OracleAdv D R α) (s : S) (hs : Inv s) :
    (run O A s).map Prod.fst = (run O' A (f s)).map Prod.fst := by
  rw [← run_map_state_inv O O' f Inv hInv hO A s hs, PMF.map_comp]
  rfl

/-- After the critical step, the oracle with the value `v` drawn in advance is the lazy one. -/
theorem run_eager_of_done (O : S → D → PMF (R × S)) (Ov : S → D → PMF (R × S))
    (c : S → D → Bool) (hnc : ∀ s d, c s d = false → Ov s d = O s d) (N : S → Prop)
    (h2 : ∀ s d, N s → ∀ x ∈ (O s d).support, N x.2) (h3 : ∀ s d, N s → c s d = false)
    (A : OracleAdv D R α) (s : S) (hs : N s) : run Ov A s = run O A s := by
  induction A generalizing s with
  | ret a => rfl
  | rand p k ih => simp only [run_rand, ih _ s hs]
  | query d k ih =>
    simp only [run_query, hnc s d (h3 s d hs)]
    exact PMF.bind_congr_support _ _ _ fun x hx => ih _ _ (h2 s d hs x hx)

/-- **Eager sampling of a value drawn at a critical step.** Let the oracle `O` draw, at the
critical steps `c s d`, a value from `μ` and continue as the oracle `Ov v`, and agree with
`Ov v` elsewhere. If a critical step leads to the states `N`, which every step keeps and which
admit no critical step, then drawing the value in advance does not change the run. -/
theorem run_eq_bind_eager (O : S → D → PMF (R × S)) (Ov : V → S → D → PMF (R × S))
    (μ : PMF V) (c : S → D → Bool)
    (hc : ∀ s d, c s d = true → O s d = μ.bind fun v => Ov v s d)
    (hnc : ∀ v s d, c s d = false → Ov v s d = O s d) (N : S → Prop)
    (h1 : ∀ v s d, c s d = true → ∀ x ∈ (Ov v s d).support, N x.2)
    (h2 : ∀ s d, N s → ∀ x ∈ (O s d).support, N x.2) (h3 : ∀ s d, N s → c s d = false)
    (A : OracleAdv D R α) (s : S) :
    run O A s = μ.bind fun v => run (Ov v) A s := by
  induction A generalizing s with
  | ret a => simp only [run_ret, PMF.bind_const]
  | rand p k ih =>
    simp only [run_rand, ih]
    exact PMF.bind_comm _ _ _
  | query d k ih =>
    simp only [run_query]
    cases hcs : c s d with
    | true =>
      rw [hc s d hcs, PMF.bind_bind]
      refine congrArg _ (funext fun v => ?_)
      refine PMF.bind_congr_support _ _ _ fun x hx => ?_
      exact (run_eager_of_done O (Ov v) c (hnc v) N h2 h3 _ _ (h1 v s d hcs x hx)).symm
    | false =>
      simp only [hnc _ s d hcs, ih]
      exact PMF.bind_comm _ _ _

end CatCrypt.Crypto.OracleAdv

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
  CatCrypt.Crypto.PRPPRF CatCryptCore.Examples.CyclicGroupDDH
open scoped ENNReal

/-! ## The CKA game as a probability mass function -/

section CKAPMF

variable {St Msg Key Rand : Type}

/-- The oracle of the CKA corruption game of `C` as a probability mass function: the sending
algorithm draws its randomness and runs `CKACoins.sendR`. -/
noncomputable def ckaOracleP (C : CKADef St Msg Key) [CKACoins C Rand] [Fintype Key]
    [Nonempty Key] [Fintype Rand] [Nonempty Rand] (ΔFS ΔPCS t : ℕ) (ideal : Bool)
    (s : CKAGameSt St Msg) : CKAQuery → PMF (CKAAns St Msg Key Rand × CKAGameSt St Msg)
  | .send p =>
    if s.canSend p then
      (PMF.uniformFintype Rand).bind fun r =>
        PMF.pure (.out (CKACoins.sendR (C := C) (s.st p) r).2.1
          (CKACoins.sendR (C := C) (s.st p) r).2.2,
          s.sent p (CKACoins.sendR (C := C) (s.st p) r).1
            (CKACoins.sendR (C := C) (s.st p) r).2.1)
    else PMF.pure (.none, s)
  | .recv p =>
    PMF.pure (if s.canRecv p then (.none, s.recvd p (C.recv (s.st p) s.msg).1) else (.none, s))
  | .chall p =>
    if s.canSend p && s.t p + 1 == t then
      (PMF.uniformFintype Rand).bind fun r =>
        (if ideal then PMF.uniformFintype Key
          else PMF.pure (CKACoins.sendR (C := C) (s.st p) r).2.2).bind fun k =>
          PMF.pure (.out (CKACoins.sendR (C := C) (s.st p) r).2.1 k,
            s.sent p (CKACoins.sendR (C := C) (s.st p) r).1
              (CKACoins.sendR (C := C) (s.st p) r).2.1)
    else PMF.pure (.none, s)
  | .corrupt p =>
    PMF.pure (if ckaAllowCorr ΔFS ΔPCS t s p then .state (s.st p) else .none, s)
  | .sendLeak p =>
    if ckaAllowLeak ΔPCS t s p then
      (PMF.uniformFintype Rand).bind fun r =>
        PMF.pure (.leak (CKACoins.sendR (C := C) (s.st p) r).2.1
          (CKACoins.sendR (C := C) (s.st p) r).2.2 r,
          s.sent p (CKACoins.sendR (C := C) (s.st p) r).1
            (CKACoins.sendR (C := C) (s.st p) r).2.1)
    else PMF.pure (.none, s)

/-- Under the soundness of the explicit-randomness sending algorithm, each oracle computation
of the CKA game is the lifted distribution `ckaOracleP`. -/
theorem ckaCorruptOracle_eq_liftPMF (C : CKADef St Msg Key) [CKACoins C Rand] [Fintype Key]
    [Nonempty Key] [Fintype Rand] [Nonempty Rand] (hS : CKACoins.Sound C) (ΔFS ΔPCS t : ℕ)
    (ideal : Bool) (s : CKAGameSt St Msg) (q : CKAQuery) :
    ckaCorruptOracle C ΔFS ΔPCS t ideal s q = liftPMF (ckaOracleP C ΔFS ΔPCS t ideal s q) := by
  cases q with
  | send p =>
    simp only [ckaCorruptOracle, ckaOracleP]
    split
    · rw [hS]
      simp only [sample_eq_liftPMF, liftPMF_pure,
        liftPMF_bind_liftPMF, PMF.bind_bind, PMF.pure_bind]
    · exact liftPMF_pure _
  | recv p => exact liftPMF_pure _
  | chall p =>
    simp only [ckaCorruptOracle, ckaOracleP]
    split
    · rw [hS]
      cases ideal
      · simp only [sample_eq_liftPMF, liftPMF_pure,
          liftPMF_bind_liftPMF, Bool.false_eq_true, ite_false, PMF.bind_bind, PMF.pure_bind]
      · simp only [sample_eq_liftPMF, liftPMF_pure,
          liftPMF_bind_liftPMF, ite_true, PMF.bind_bind, PMF.pure_bind]
    · exact liftPMF_pure _
  | corrupt p => exact liftPMF_pure _
  | sendLeak p =>
    simp only [ckaCorruptOracle, ckaOracleP]
    split
    · simp only [sample_eq_liftPMF, liftPMF_pure, liftPMF_bind_liftPMF, PMF.bind_bind, PMF.pure_bind]
    · exact liftPMF_pure _

/-- **The CKA corruption game as a lifted distribution.** With an initialisation that is the
lift of `initP` and a sound explicit-randomness sending algorithm, the game is the lift of the
distribution that draws the challenge epoch and the initialisation and runs the adversary
against `ckaOracleP`. -/
theorem cka_corrupt_game_eq_liftPMF (C : CKADef St Msg Key) [CKACoins C Rand] [Fintype Key]
    [Nonempty Key] [Fintype Rand] [Nonempty Rand] (hS : CKACoins.Sound C)
    (initP : PMF (Msg × St × St)) (hinit : C.init = liftPMF initP) (ΔFS ΔPCS : ℕ)
    (ideal : Bool) {α : Type} (A : CKACorruptAdv St Msg Key Rand α) :
    cka_corrupt_game C ΔFS ΔPCS ideal A =
      liftPMF (A.tStar.bind fun t => initP.bind fun i =>
        (OracleAdv.run (ckaOracleP C ΔFS ΔPCS t ideal) (A.play t i.1)
          (CKAGameSt.init i.1 i.2.1 i.2.2)).map Prod.fst) := by
  unfold cka_corrupt_game
  simp only [hinit, OracleAdv.runSP_eq_liftPMF _ _ (ckaCorruptOracle_eq_liftPMF C hS ΔFS ΔPCS _
    ideal), liftPMF_bind_pure, liftPMF_bind_liftPMF, PMF.bind_bind, PMF.pure_bind]

end CKAPMF

/-! ## The secure-messaging game with state corruption -/

/-- The queries of the secure-messaging adversary. -/
inductive SMQuery (W : Type) where
  /-- The party opens a new epoch: it runs the CKA sending algorithm and the root step. -/
  | ratchet (p : CKAParty)
  /-- The party receives the CKA message of the epoch opened by its peer. -/
  | recv (p : CKAParty)
  /-- The party encrypts the message `m` (a plaintext and associated data) in its epoch. -/
  | send (p : CKAParty) (m : W × W)
  /-- As `send`, in the challenge epoch, with a uniform ciphertext in the ideal game. -/
  | chall (p : CKAParty) (m : W × W)
  /-- The full state of the party is returned, if the corruption gate allows it. -/
  | corrupt (p : CKAParty)

/-- The answers of the secure-messaging oracles. -/
inductive SMAns (Sc Msg RK Sa Ct : Type) where
  /-- A refused query, or a receive. -/
  | none
  /-- The CKA message of a new epoch. -/
  | msg (T : Msg)
  /-- A ciphertext. -/
  | ct (c : Ct)
  /-- The state of a corrupted party: CKA state, root key, sending and receiving chain. -/
  | state (γ : Sc) (rk : RK) (snd rcv : Option Sa)

/-- The part of the secure-messaging state outside the CKA: the root keys and the chain states
of the parties, the root output of the last opened epoch, in transit to the receiver, and
whether the challenge has been asked. -/
structure SMLoc (RK Sa : Type) where
  /-- The root keys of the parties. -/
  rk : CKAParty → RK
  /-- The sending chain states (FS-AEAD sender states) of the parties. -/
  snd : CKAParty → Option Sa
  /-- The receiving chain states (FS-AEAD receiver states) of the parties. -/
  rcv : CKAParty → Option Sa
  /-- The root output of the last opened epoch. -/
  out : Option (RK × Sa)
  /-- The challenge has been asked. -/
  done : Bool

namespace SMLoc

variable {RK Sa : Type}

/-- The initial state: both root keys are `rk`, no chains, nothing in transit. -/
def init (rk : RK) : SMLoc RK Sa := ⟨fun _ => rk, fun _ => none, fun _ => none, none, false⟩

/-- Party `p` opened an epoch with root output `y`: the next root key `y.1`, the sending chain
`y.2`, and `y` in transit. -/
def opened (l : SMLoc RK Sa) (p : CKAParty) (y : RK × Sa) : SMLoc RK Sa :=
  { l with rk := Function.update l.rk p y.1, snd := Function.update l.snd p (some y.2),
           out := some y }

/-- Party `p` received the root output `y`: it takes over the root key and the chain. -/
def recvY (l : SMLoc RK Sa) (p : CKAParty) (y : RK × Sa) : SMLoc RK Sa :=
  { l with rk := Function.update l.rk p y.1, rcv := Function.update l.rcv p (some y.2) }

/-- Party `p` received the epoch in transit: it takes over the root key and the chain. -/
def received (l : SMLoc RK Sa) (p : CKAParty) : SMLoc RK Sa :=
  match l.out with
  | some y => l.recvY p y
  | none => l

/-- The sending chain of party `p` moved to the state `sa`. -/
def advanced (l : SMLoc RK Sa) (p : CKAParty) (sa : Sa) : SMLoc RK Sa :=
  { l with snd := Function.update l.snd p (some sa) }

end SMLoc

/-- The state of the secure-messaging game: the CKA game state (party states, epoch counters,
CKA message in transit) and the rest. -/
structure SMSt (Sc Msg RK Sa : Type) where
  /-- The CKA part. -/
  ck : CKAGameSt Sc Msg
  /-- The root keys, chains, root output in transit and challenge flag. -/
  loc : SMLoc RK Sa

section Game

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct]

/-- The challenge of party `p` is allowed in the local state `l` at the counter `e` of `p`. -/
def challOk (l : SMLoc RK Sa) (t e : ℕ) (p : CKAParty) : Bool :=
  !l.done && (ckaSender e == p) && (e == t)

/-- The distribution of the challenge ciphertext under the key `k`: the encryption of `m`, or a
uniform ciphertext in the ideal game. -/
noncomputable def challCt (D : AEADDef W Ct) (ideal : Bool) (k : W) (m : W × W) : PMF Ct :=
  if ideal then PMF.uniformFintype Ct else PMF.pure (D.encrypt k m.1 m.2)

/-- The oracle of the secure-messaging game with the challenge epoch `t`, the challenge mode
`ideal` and the root step `root` at the opening of epoch `t`; every other epoch uses the root
KDF `R`. The real game has `root rk I = pure (R (rk, I))`; the other choices are hybrids. -/
noncomputable def smOracleOf (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t : ℕ) (ideal : Bool) (root : RK → Key → PMF (RK × Sa)) (s : SMSt Sc Msg RK Sa) :
    SMQuery W → PMF (SMAns Sc Msg RK Sa Ct × SMSt Sc Msg RK Sa)
  | .ratchet p =>
    if s.ck.canSend p then
      (PMF.uniformFintype Rand).bind fun r =>
        (if s.ck.t p + 1 == t then root (s.loc.rk p) (CKACoins.sendR (C := C) (s.ck.st p) r).2.2
          else PMF.pure (R.stretch (s.loc.rk p, (CKACoins.sendR (C := C) (s.ck.st p) r).2.2))).bind
          fun y => PMF.pure (.msg (CKACoins.sendR (C := C) (s.ck.st p) r).2.1,
            ⟨s.ck.sent p (CKACoins.sendR (C := C) (s.ck.st p) r).1
              (CKACoins.sendR (C := C) (s.ck.st p) r).2.1, s.loc.opened p y⟩)
    else PMF.pure (.none, s)
  | .recv p =>
    if s.ck.canRecv p then
      PMF.pure (.none, ⟨s.ck.recvd p (C.recv (s.ck.st p) s.ck.msg).1, s.loc.received p⟩)
    else PMF.pure (.none, s)
  | .send p m =>
    match s.loc.snd p with
    | some sa =>
      if ckaSender (s.ck.t p) == p then
        PMF.pure (.ct (D.encrypt (G.stretch sa).1 m.1 m.2), ⟨s.ck, s.loc.advanced p (G.stretch sa).2⟩)
      else PMF.pure (.none, s)
    | none => PMF.pure (.none, s)
  | .chall p m =>
    match s.loc.snd p with
    | some sa =>
      if challOk s.loc t (s.ck.t p) p then
        (challCt D ideal (G.stretch sa).1 m).bind fun c =>
          PMF.pure (.ct c, ⟨s.ck, { s.loc.advanced p (G.stretch sa).2 with done := true }⟩)
      else PMF.pure (.none, s)
    | none => PMF.pure (.none, s)
  | .corrupt p =>
    PMF.pure (if ckaAllowCorr ΔFS ΔPCS t s.ck p then
      .state (s.ck.st p) (s.loc.rk p) (s.loc.snd p) (s.loc.rcv p) else .none, s)

/-- The root step of the real game: the root KDF. -/
noncomputable def realRoot (R : PRGDef (RK × Key) (RK × Sa)) (rk : RK) (I : Key) :
    PMF (RK × Sa) :=
  PMF.pure (R.stretch (rk, I))

/-- The initial state of the game from the CKA initialisation `i` and the root key `rk`. -/
def smInit (i : Msg × Sc × Sc) (rk : RK) : SMSt Sc Msg RK Sa :=
  ⟨CKAGameSt.init i.1 i.2.1 i.2.2, SMLoc.init rk⟩

end Game

/-- A secure-messaging adversary: a distribution `tStar` of the challenge epoch, and for each
challenge epoch and public value of the CKA initialisation an oracle tree. -/
structure SMCorruptAdv (Sc Msg RK Sa W Ct : Type) : Type 1 where
  /-- The choice of the challenge epoch. -/
  tStar : PMF ℕ
  /-- The interaction with the oracles. -/
  play : ℕ → Msg → OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool

section Game

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [Fintype RK] [Nonempty RK]

/-- The secure-messaging game with the root step `root` at the challenge epoch: the adversary
chooses the challenge epoch `t`, the CKA is initialised, both parties get a uniform root key,
and the adversary interacts with the oracle. -/
noncomputable def sm_corrupt_gameOf (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (root : RK → Key → PMF (RK × Sa))
    (A : SMCorruptAdv Sc Msg RK Sa W Ct) : SPComp Bool :=
  SPComp.bind (liftPMF A.tStar) fun t =>
    SPComp.bind C.init fun i =>
      SPComp.bind (SPComp.sample RK) fun rk =>
        liftPMF ((OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS t ideal root) (A.play t i.1)
          (smInit i rk)).map Prod.fst)

/-- The secure-messaging game with state corruption; `ideal` selects the uniform challenge
ciphertext. -/
noncomputable def sm_corrupt_game (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (A : SMCorruptAdv Sc Msg RK Sa W Ct) : SPComp Bool :=
  sm_corrupt_gameOf C R G D ΔFS ΔPCS ideal (realRoot R) A

/-- **Secure-messaging advantage with state corruption** of the adversary `A`. -/
noncomputable def SM_Corrupt_Advantage (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (A : SMCorruptAdv Sc Msg RK Sa W Ct) : ℝ≥0∞ :=
  Advantage (sm_corrupt_game C R G D ΔFS ΔPCS false A) (sm_corrupt_game C R G D ΔFS ΔPCS true A)

end Game

/-! ## The structure of the game: monotone counters and the opening of the challenge epoch -/

section Structure

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct]

/-- The opening of the challenge epoch `t`: a new epoch by a party that may send, whose counter
is one before `t`. -/
def smCrit (t : ℕ) (s : SMSt Sc Msg RK Sa) : SMQuery W → Bool
  | .ratchet p => s.ck.canSend p && (s.ck.t p + 1 == t)
  | _ => false

/-- The challenge epoch `t` has been opened: a counter has reached `t`. -/
def smOpened (t : ℕ) (s : SMSt Sc Msg RK Sa) : Prop := t ≤ s.ck.t .A ∨ t ≤ s.ck.t .B

/-- **Monotone counters.** Every oracle call leaves every epoch counter at least as large. -/
theorem smOracleOf_t_mono (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t : ℕ) (ideal : Bool) (root : RK → Key → PMF (RK × Sa)) (s : SMSt Sc Msg RK Sa)
    (q : SMQuery W) (x) (hx : x ∈ (smOracleOf C R G D ΔFS ΔPCS t ideal root s q).support)
    (P : CKAParty) : s.ck.t P ≤ x.2.ck.t P := by
  cases q with
  | ratchet p =>
    simp only [smOracleOf] at hx
    split at hx
    · simp only [PMF.support_bind, Set.mem_iUnion, PMF.support_pure, Set.mem_singleton_iff]
        at hx
      obtain ⟨r, -, y, -, rfl⟩ := hx
      exact CKAGameSt.le_sent _ _ _ _ _
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
      rw [hx]
  | recv p =>
    simp only [smOracleOf] at hx
    split at hx <;> simp only [PMF.support_pure, Set.mem_singleton_iff] at hx <;> rw [hx]
    exact CKAGameSt.le_recvd _ _ _ _
  | send p m =>
    simp only [smOracleOf] at hx
    split at hx
    · split at hx <;> simp only [PMF.support_pure, Set.mem_singleton_iff] at hx <;> rw [hx]
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
      rw [hx]
  | chall p m =>
    simp only [smOracleOf] at hx
    split at hx
    · split at hx
      · simp only [PMF.support_bind, Set.mem_iUnion, PMF.support_pure, Set.mem_singleton_iff]
          at hx
        obtain ⟨c, -, rfl⟩ := hx
        exact le_refl _
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
        rw [hx]
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
      rw [hx]
  | corrupt p =>
    simp only [smOracleOf, PMF.support_pure, Set.mem_singleton_iff] at hx
    rw [hx]

/-- The opening of the challenge epoch leads to an opened state. -/
theorem smOracleOf_opened_of_crit (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t : ℕ) (ideal : Bool) (root : RK → Key → PMF (RK × Sa)) (s : SMSt Sc Msg RK Sa)
    (q : SMQuery W) (hc : smCrit t s q = true) (x)
    (hx : x ∈ (smOracleOf C R G D ΔFS ΔPCS t ideal root s q).support) : smOpened t x.2 := by
  cases q with
  | ratchet p =>
    simp only [smCrit, Bool.and_eq_true, beq_iff_eq] at hc
    simp only [smOracleOf, hc.1, ite_true] at hx
    simp only [PMF.support_bind, Set.mem_iUnion, PMF.support_pure, Set.mem_singleton_iff] at hx
    obtain ⟨r, -, y, -, rfl⟩ := hx
    cases p
    · exact Or.inl (by simp [CKAGameSt.sent_t, hc.2])
    · exact Or.inr (by simp [CKAGameSt.sent_t, hc.2])
  | _ => simp [smCrit] at hc

/-- An opened state stays opened. -/
theorem smOracleOf_opened (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t : ℕ) (ideal : Bool) (root : RK → Key → PMF (RK × Sa)) (s : SMSt Sc Msg RK Sa)
    (q : SMQuery W) (hs : smOpened t s) (x)
    (hx : x ∈ (smOracleOf C R G D ΔFS ΔPCS t ideal root s q).support) : smOpened t x.2 := by
  rcases hs with h | h
  · exact Or.inl (h.trans (smOracleOf_t_mono C R G D ΔFS ΔPCS t ideal root s q x hx .A))
  · exact Or.inr (h.trans (smOracleOf_t_mono C R G D ΔFS ΔPCS t ideal root s q x hx .B))

/-- An opened state admits no opening of the challenge epoch. -/
theorem smCrit_of_opened (t : ℕ) (s : SMSt Sc Msg RK Sa) (hs : smOpened t s) (q : SMQuery W) :
    smCrit t s q = false := by
  cases q with
  | ratchet p =>
    simp only [smCrit, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
    by_cases hc : s.ck.canSend p = true
    · right
      simp only [CKAGameSt.canSend, Bool.and_eq_true, beq_iff_eq] at hc
      have := hc.1
      cases p <;> rcases hs with h | h <;> omega
    · left; simpa using hc
  | _ => rfl

/-- Away from the opening of the challenge epoch, the oracle does not depend on the root step
at the challenge epoch. -/
theorem smOracleOf_root_congr (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t : ℕ) (ideal : Bool) (root root' : RK → Key → PMF (RK × Sa))
    (s : SMSt Sc Msg RK Sa) (q : SMQuery W) (hc : smCrit t s q = false) :
    smOracleOf C R G D ΔFS ΔPCS t ideal root s q = smOracleOf C R G D ΔFS ΔPCS t ideal root' s q := by
  cases q with
  | ratchet p =>
    simp only [smCrit, Bool.and_eq_false_iff] at hc
    simp only [smOracleOf]
    rcases hc with h | h
    · simp [h]
    · simp [h]
  | _ => rfl

/-- **Eager sampling of the root step at the challenge epoch.** If the root step at the challenge
epoch draws `v` from `μ` and continues as `rootv v`, the run equals the run with `v` drawn in
advance. -/
theorem sm_run_eager (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t : ℕ) (ideal : Bool) {V : Type} (μ : PMF V) (root : RK → Key → PMF (RK × Sa))
    (rootv : V → RK → Key → PMF (RK × Sa))
    (hroot : ∀ rk I, root rk I = μ.bind fun v => rootv v rk I) {α : Type}
    (A : OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) α) (s : SMSt Sc Msg RK Sa) :
    OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS t ideal root) A s =
      μ.bind fun v => OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS t ideal (rootv v)) A s := by
  refine OracleAdv.run_eq_bind_eager _ _ μ (smCrit t) ?_ ?_ (smOpened t) ?_ ?_ ?_ A s
  · intro s q hc
    cases q with
    | ratchet p =>
      simp only [smCrit, Bool.and_eq_true] at hc
      simp only [smOracleOf, hc.1, hc.2, ite_true, hroot, PMF.bind_bind]
      exact PMF.bind_comm _ _ _
    | _ => simp [smCrit] at hc
  · intro v s q hc
    exact smOracleOf_root_congr C R G D ΔFS ΔPCS t ideal _ _ s q hc
  · intro v s q hc x hx
    exact smOracleOf_opened_of_crit C R G D ΔFS ΔPCS t ideal _ s q hc x hx
  · intro s q hs x hx
    exact smOracleOf_opened C R G D ΔFS ΔPCS t ideal _ s q hs x hx
  · intro s q hs
    exact smCrit_of_opened t s hs q

end Structure

/-! ## PRF-PRNGs -/

section PRFPRNG

variable {RK Key Out : Type}

/-- The queries of the PRF-PRNG adversary. -/
inductive PPQuery (RK Key : Type) where
  /-- The root step on the hidden root state and the input `I` of the adversary. -/
  | prng (I : Key)
  /-- The root step on the root state `rk` of the adversary and the hidden input. -/
  | prf (rk : RK)

/-- The state of the PRF-PRNG game: the hidden root state, the hidden input, and the tables of
the two random functions of the ideal game. -/
structure PPSt (RK Key Out : Type) where
  /-- The hidden root state. -/
  rk : RK
  /-- The hidden input. -/
  key : Key
  /-- The table of the random function of the inputs. -/
  tL : List (Key × Out)
  /-- The table of the random function of the root states. -/
  tR : List (RK × Out)

variable [Fintype Out] [Nonempty Out] [DecidableEq RK] [DecidableEq Key]

/-- The oracle of the PRF-PRNG game of the root step `F`: `prng I` is `F rk I` on the hidden
root state `rk` (a lazily sampled random function of `I` if `idealL`), `prf rk'` is `F rk' I`
on the hidden input `I` (a lazily sampled random function of `rk'` if `idealR`). -/
noncomputable def ppOracle (F : RK → Key → Out) (idealL idealR : Bool) (s : PPSt RK Key Out) :
    PPQuery RK Key → PMF (Out × PPSt RK Key Out)
  | .prng I =>
    if idealL then (rfOracle s.tL I).map fun x => (x.1, { s with tL := x.2 })
    else PMF.pure (F s.rk I, s)
  | .prf rk =>
    if idealR then (rfOracle s.tR rk).map fun x => (x.1, { s with tR := x.2 })
    else PMF.pure (F rk s.key, s)

variable [Fintype RK] [Nonempty RK] [Fintype Key] [Nonempty Key]

/-- The PRF-PRNG game: a uniform hidden root state and a uniform hidden input, and the run of
the adversary against `ppOracle`. -/
noncomputable def pp_game (F : RK → Key → Out) (idealL idealR : Bool)
    (A : OracleAdv (PPQuery RK Key) Out Bool) : SPComp Bool :=
  liftPMF ((PMF.uniformFintype RK).bind fun rk => (PMF.uniformFintype Key).bind fun k =>
    (OracleAdv.run (ppOracle F idealL idealR) A ⟨rk, k, [], []⟩).map Prod.fst)

/-- The root step of the root KDF `R` as a function of the root state and the input. -/
def rootFn (R : PRGDef (RK × Key) Out) (rk : RK) (I : Key) : Out := R.stretch (rk, I)

/-- **PRF-PRNG advantage** of the root KDF `R` (Alwen, Coretti and Dodis, §4.2): the distance
between the real game and the game in which both oracles are random functions. The `prng`
oracle is the PRNG property with adversarial inputs (a uniform root state gives pseudorandom
outputs whatever the inputs), the `prf` oracle the PRF property (a uniform input gives
pseudorandom outputs whatever the root state). -/
noncomputable def PRFPRNG_Advantage (R : PRGDef (RK × Key) Out)
    (A : OracleAdv (PPQuery RK Key) Out Bool) : ℝ≥0∞ :=
  Advantage (pp_game (rootFn R) false false A) (pp_game (rootFn R) true true A)

/-- The HKDF-shaped root step: the next root state and the output are `F rk I`, the KDF keyed
by the root state (the HKDF salt) applied to the input (the input keying material). -/
def hkdfRoot (F : RK → Key → Out) : PRGDef (RK × Key) Out where
  stretch x := F x.1 x.2

/-- The simulator of the right dual-PRF reduction with the root state `rk`: `prng` queries are
answered with `F rk`, `prf` queries are forwarded. -/
noncomputable def ppImplR (F : RK → Key → Out) (rk : RK) (u : Unit) (q : PPQuery RK Key) :
    OracleAdv RK Out (Out × Unit) :=
  match q with
  | .prng I => .ret (F rk I, u)
  | .prf r => .query r fun y => .ret (y, u)

/-- **The right dual-PRF reduction** of the PRF-PRNG game: a uniform root state, the `prng`
oracle computed with it, the `prf` oracle forwarded to the dual-PRF game keyed by the input. -/
noncomputable def ppRedR (F : RK → Key → Out) (A : OracleAdv (PPQuery RK Key) Out Bool) :
    OracleAdv RK Out Bool :=
  .rand (PMF.uniformFintype RK) fun rk =>
    (OracleAdv.simulate (ppImplR F rk) A ()).bind fun r => .ret r.1

/-- The simulator of the left dual-PRF reduction, with the table of a random function of the
root states: `prng` queries are forwarded, `prf` queries are answered by the table. -/
noncomputable def ppImplL (σ : List (RK × Out)) (q : PPQuery RK Key) :
    OracleAdv Key Out (Out × List (RK × Out)) :=
  match q with
  | .prng I => .query I fun y => .ret (y, σ)
  | .prf r =>
    match List.lookup r σ with
    | some y => .ret (y, σ)
    | none => .rand (PMF.uniformFintype Out) fun y => .ret (y, (r, y) :: σ)

/-- **The left dual-PRF reduction** of the PRF-PRNG game: the `prng` oracle forwarded to the
dual-PRF game keyed by the root state, the `prf` oracle a lazily sampled random function. -/
noncomputable def ppRedL (A : OracleAdv (PPQuery RK Key) Out Bool) : OracleAdv Key Out Bool :=
  (OracleAdv.simulate (ppImplL (Key := Key)) A []).bind fun r => .ret r.1

derive_timed ppRedR

derive_timed ppRedL

/-- The real PRF-PRNG game is the real right dual-PRF game of `ppRedR`. -/
theorem pp_real_eq (F : RK → Key → Out) (A : OracleAdv (PPQuery RK Key) Out Bool) :
    pp_game F false false A = realGame (Function.swap F) (ppRedR F A) := by
  unfold pp_game realGame ppRedR
  congr 1
  simp only [OracleAdv.run_rand, PMF.map_bind]
  rw [PMF.bind_comm]
  refine congrArg _ (funext fun k => congrArg _ (funext fun rk => ?_))
  rw [OracleAdv.run_simulate_fst]
  refine (OracleAdv.run_map_fst_of_map_state_inv _ _ (fun _ => (⟨rk, k, [], []⟩ : PPSt RK Key Out))
    (fun _ => True) (fun _ _ _ _ _ => trivial) ?_ A ((), ()) trivial).symm
  intro x q _
  cases q with
  | prng I => simp [OracleAdv.simOracle, ppImplR, ppOracle, PMF.pure_map]
  | prf r => simp [OracleAdv.simOracle, ppImplR, ppOracle, keyedOracle, PMF.pure_map]

/-- The PRF-PRNG game with a random function for `prf` is the ideal right dual-PRF game of
`ppRedR`. -/
theorem pp_mid_eq_rf (F : RK → Key → Out) (A : OracleAdv (PPQuery RK Key) Out Bool) :
    pp_game F false true A = rfGame (ppRedR F A) := by
  unfold pp_game rfGame ppRedR
  congr 1
  simp only [OracleAdv.run_rand, PMF.map_bind]
  refine congrArg _ (funext fun rk => ?_)
  rw [OracleAdv.run_simulate_fst]
  have h : ∀ k : Key, (OracleAdv.run (ppOracle F false true) A ⟨rk, k, [], []⟩).map Prod.fst =
      (OracleAdv.run (OracleAdv.simOracle (ppImplR F rk) rfOracle) A ((), [])).map Prod.fst := by
    intro k
    refine (OracleAdv.run_map_fst_of_map_state_inv _ _ (fun x => (⟨rk, k, [], x.2⟩ : PPSt RK Key Out))
      (fun _ => True) (fun _ _ _ _ _ => trivial) ?_ A ((), []) trivial).symm
    intro x q _
    cases q with
    | prng I => simp [OracleAdv.simOracle, ppImplR, ppOracle, PMF.pure_map]
    | prf r =>
      simp only [OracleAdv.simOracle, ppImplR, ppOracle, OracleAdv.run_query,
        OracleAdv.run_ret, ite_true, PMF.map_bind, PMF.bind_map, PMF.pure_map]
      rw [← PMF.bind_pure_comp]
      rfl
  simp only [h, PMF.bind_const]

/-- The PRF-PRNG game with a random function for `prf` is the real left dual-PRF game of
`ppRedL`. -/
theorem pp_mid_eq_real (F : RK → Key → Out) (A : OracleAdv (PPQuery RK Key) Out Bool) :
    pp_game F false true A = realGame F (ppRedL (Key := Key) A) := by
  unfold pp_game realGame ppRedL
  congr 1
  refine congrArg _ (funext fun rk => ?_)
  rw [OracleAdv.run_simulate_fst]
  have h : ∀ k : Key, (OracleAdv.run (ppOracle F false true) A ⟨rk, k, [], []⟩).map Prod.fst =
      (OracleAdv.run (OracleAdv.simOracle ppImplL (keyedOracle F rk)) A ([], ())).map
        Prod.fst := by
    intro k
    refine (OracleAdv.run_map_fst_of_map_state_inv _ _ (fun x => (⟨rk, k, [], x.1⟩ : PPSt RK Key Out))
      (fun _ => True) (fun _ _ _ _ _ => trivial) ?_ A ([], ()) trivial).symm
    intro x q _
    cases q with
    | prng I => simp [OracleAdv.simOracle, ppImplL, ppOracle, keyedOracle, PMF.pure_map]
    | prf r =>
      simp only [OracleAdv.simOracle, ppImplL, ppOracle, rfOracle, ite_true]
      cases List.lookup r x.1 with
      | some y => simp [PMF.pure_map]
      | none =>
        simp only [OracleAdv.run_rand, OracleAdv.run_ret, PMF.map_bind, PMF.pure_map,
          PMF.map_comp]
        rw [← PMF.bind_pure_comp]
        rfl
  simp only [h, PMF.bind_const]

/-- The ideal PRF-PRNG game is the ideal left dual-PRF game of `ppRedL`. -/
theorem pp_ideal_eq_rf (F : RK → Key → Out) (A : OracleAdv (PPQuery RK Key) Out Bool) :
    pp_game F true true A = rfGame (ppRedL (Key := Key) A) := by
  unfold pp_game rfGame ppRedL
  congr 1
  rw [OracleAdv.run_simulate_fst]
  have h : ∀ (rk : RK) (k : Key),
      (OracleAdv.run (ppOracle F true true) A ⟨rk, k, [], []⟩).map Prod.fst =
      (OracleAdv.run (OracleAdv.simOracle ppImplL rfOracle) A ([], [])).map Prod.fst := by
    intro rk k
    refine (OracleAdv.run_map_fst_of_map_state_inv _ _ (fun x => (⟨rk, k, x.2, x.1⟩ : PPSt RK Key Out))
      (fun _ => True) (fun _ _ _ _ _ => trivial) ?_ A ([], []) trivial).symm
    intro x q _
    cases q with
    | prng I =>
      simp only [OracleAdv.simOracle, ppImplL, ppOracle, OracleAdv.run_query,
        OracleAdv.run_ret, ite_true, PMF.map_bind, PMF.bind_map, PMF.pure_map]
      rw [← PMF.bind_pure_comp]
      rfl
    | prf r =>
      simp only [OracleAdv.simOracle, ppImplL, ppOracle, rfOracle, ite_true]
      cases List.lookup r x.1 with
      | some y => simp [PMF.pure_map]
      | none =>
        simp only [OracleAdv.run_rand, OracleAdv.run_ret, PMF.map_bind, PMF.pure_map,
          PMF.map_comp]
        rw [← PMF.bind_pure_comp]
        rfl
  simp only [h, PMF.bind_const]

/-- **The HKDF-shaped root step is a PRF-PRNG under the dual-PRF assumption.** For every
adversary `A`, the PRF-PRNG advantage of `hkdfRoot F` is at most the dual-PRF advantage of `F`
keyed by its right argument at `ppRedR F A` plus the dual-PRF advantage keyed by its left
argument at `ppRedL A`. -/
theorem hkdfRoot_prfprng_le (F : RK → Key → Out) (A : OracleAdv (PPQuery RK Key) Out Bool) :
    PRFPRNG_Advantage (hkdfRoot F) A ≤
      DualPRF_Right_Advantage F (ppRedR F A) + DualPRF_Left_Advantage F (ppRedL (Key := Key) A) := by
  have hF : rootFn (hkdfRoot F) = F := funext fun _ => funext fun _ => rfl
  unfold PRFPRNG_Advantage DualPRF_Right_Advantage DualPRF_Left_Advantage PRF_q_Advantage
  rw [hF]
  refine (advantage_triangle _ (pp_game F false true A) _).trans (add_le_add (le_of_eq ?_)
    (le_of_eq ?_))
  · rw [pp_real_eq, pp_mid_eq_rf]
  · rw [pp_mid_eq_real, pp_ideal_eq_rf]

end PRFPRNG

/-! ## The CKA reduction -/

section CKARed

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [Fintype RK] [Nonempty RK]

/-- The opening of an epoch by party `p` in the CKA simulator: a CKA send, or the CKA challenge
at the epoch `t`, followed by the root step on the returned key. -/
noncomputable def smCKARatchet (R : PRGDef (RK × Key) (RK × Sa)) (t : ℕ)
    (σ : SMLoc RK Sa × CKAGameSt Unit Unit) (p : CKAParty) :
    OracleAdv CKAQuery (CKAAns Sc Msg Key Rand)
      (SMAns Sc Msg RK Sa Ct × (SMLoc RK Sa × CKAGameSt Unit Unit)) :=
  if σ.2.canSend p then
    if σ.2.t p + 1 == t then
      .query (.chall p) fun a =>
        match a with
        | .out T I => .ret (.msg T, (σ.1.opened p (R.stretch (σ.1.rk p, I)), σ.2.sent p () ()))
        | .none => .ret (.none, σ)
        | .state _ => .ret (.none, σ)
        | .leak _ _ _ => .ret (.none, σ)
    else
      .query (.send p) fun a =>
        match a with
        | .out T I => .ret (.msg T, (σ.1.opened p (R.stretch (σ.1.rk p, I)), σ.2.sent p () ()))
        | .none => .ret (.none, σ)
        | .state _ => .ret (.none, σ)
        | .leak _ _ _ => .ret (.none, σ)
  else .ret (.none, σ)

/-- The receive of party `p` in the CKA simulator: a CKA receive. -/
noncomputable def smCKARecvT (σ : SMLoc RK Sa × CKAGameSt Unit Unit) (p : CKAParty) :
    OracleAdv CKAQuery (CKAAns Sc Msg Key Rand)
      (SMAns Sc Msg RK Sa Ct × (SMLoc RK Sa × CKAGameSt Unit Unit)) :=
  if σ.2.canRecv p then
    .query (.recv p) fun _ =>
      match σ.1.out with
      | some y => .ret (.none, (σ.1.recvY p y, σ.2.recvd p ()))
      | none => .ret (.none, (σ.1, σ.2.recvd p ()))
  else .ret (.none, σ)

/-- The send of party `p` in the CKA simulator, computed locally: the encryption of `m` under
the next key of the sending chain, if `p` sends in its epoch. -/
noncomputable def smCKASendT (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (σ : SMLoc RK Sa × CKAGameSt Unit Unit) (p : CKAParty) (m : W × W) :
    OracleAdv CKAQuery (CKAAns Sc Msg Key Rand)
      (SMAns Sc Msg RK Sa Ct × (SMLoc RK Sa × CKAGameSt Unit Unit)) :=
  match σ.1.snd p with
  | some sa =>
    if ckaSender (σ.2.t p) == p then
      .ret (.ct (D.encrypt (G.stretch sa).1 m.1 m.2), (σ.1.advanced p (G.stretch sa).2, σ.2))
    else .ret (.none, σ)
  | none => .ret (.none, σ)

/-- The challenge of party `p` in the CKA simulator, computed locally. -/
noncomputable def smCKAChallT (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (t : ℕ)
    (ideal : Bool) (σ : SMLoc RK Sa × CKAGameSt Unit Unit) (p : CKAParty) (m : W × W) :
    OracleAdv CKAQuery (CKAAns Sc Msg Key Rand)
      (SMAns Sc Msg RK Sa Ct × (SMLoc RK Sa × CKAGameSt Unit Unit)) :=
  match σ.1.snd p with
  | some sa =>
    if challOk σ.1 t (σ.2.t p) p then
      .rand (challCt D ideal (G.stretch sa).1 m) fun c =>
        .ret (.ct c, ({ σ.1.advanced p (G.stretch sa).2 with done := true }, σ.2))
    else .ret (.none, σ)
  | none => .ret (.none, σ)

/-- The corruption of party `p` in the CKA simulator: a CKA corruption, to which the root key
and the chains are added. -/
noncomputable def smCKACorrT (σ : SMLoc RK Sa × CKAGameSt Unit Unit) (p : CKAParty) :
    OracleAdv CKAQuery (CKAAns Sc Msg Key Rand)
      (SMAns Sc Msg RK Sa Ct × (SMLoc RK Sa × CKAGameSt Unit Unit)) :=
  .query (.corrupt p) fun a =>
    match a with
    | .state γ => .ret (.state γ (σ.1.rk p) (σ.1.snd p) (σ.1.rcv p), σ)
    | .none => .ret (.none, σ)
    | .out _ _ => .ret (.none, σ)
    | .leak _ _ _ => .ret (.none, σ)

/-- The simulator of the CKA reduction with the challenge epoch `t`. Its state is the part
`SMLoc` of the secure-messaging state and a shadow of the CKA game state that keeps the epoch
counters. -/
noncomputable def smCKAImplOf (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (t : ℕ) (ideal : Bool)
    (σ : SMLoc RK Sa × CKAGameSt Unit Unit) (q : SMQuery W) :
    OracleAdv CKAQuery (CKAAns Sc Msg Key Rand)
      (SMAns Sc Msg RK Sa Ct × (SMLoc RK Sa × CKAGameSt Unit Unit)) :=
  match q with
  | .ratchet p => smCKARatchet R t σ p
  | .recv p => smCKARecvT σ p
  | .send p m => smCKASendT G D σ p m
  | .chall p m => smCKAChallT G D t ideal σ p m
  | .corrupt p => smCKACorrT σ p

/-- **The CKA reduction** as an oracle tree: on the challenge epoch `t` and the public value
`pub`, it draws a uniform root key and runs the secure-messaging adversary against the
simulator `smCKAImplOf`. -/
noncomputable def smCKATreeOf (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (ideal : Bool)
    (play : ℕ → Msg → OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool) (t : ℕ) (pub : Msg) :
    OracleAdv CKAQuery (CKAAns Sc Msg Key Rand) Bool :=
  .rand (PMF.uniformFintype RK) fun rk =>
    (OracleAdv.simulate (smCKAImplOf R G D t ideal) (play t pub)
      (SMLoc.init rk, CKAGameSt.init () () ())).bind fun r => .ret r.1

derive_timed smCKAImplOf

derive_timed smCKATreeOf

end CKARed

/-! ## The CKA hop -/

section CKAHop

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [Fintype RK] [Nonempty RK] [Fintype Key] [Nonempty Key]

/-- The root step at the challenge epoch of the first hybrid: the root KDF on a uniform key. -/
noncomputable def unifKeyRoot (R : PRGDef (RK × Key) (RK × Sa)) (rk : RK) (_ : Key) :
    PMF (RK × Sa) :=
  (PMF.uniformFintype Key).bind fun k => PMF.pure (R.stretch (rk, k))

/-- The root step at the challenge epoch of the game simulated by the CKA reduction: the real
root step against the real CKA game, the root step on a uniform key against the ideal one. -/
noncomputable def ckaHopRoot (R : PRGDef (RK × Key) (RK × Sa)) (idealK : Bool) :
    RK → Key → PMF (RK × Sa) :=
  if idealK then unifKeyRoot R else realRoot R

/-- The shadow of a CKA game state, which keeps its epoch counters. -/
def ckaShadow (s : CKAGameSt Sc Msg) : CKAGameSt Unit Unit := ⟨fun _ => (), s.t, ()⟩

/-- The state of the CKA reduction and of the CKA game that a secure-messaging state
corresponds to. -/
def smCKAEmb (s : SMSt Sc Msg RK Sa) :
    (SMLoc RK Sa × CKAGameSt Unit Unit) × CKAGameSt Sc Msg :=
  ((s.loc, ckaShadow s.ck), s.ck)

theorem ckaShadow_sent (s : CKAGameSt Sc Msg) (p : CKAParty) (x : Sc) (T : Msg) :
    ckaShadow (s.sent p x T) = (ckaShadow s).sent p () () := by
  simp only [ckaShadow, CKAGameSt.sent]

theorem ckaShadow_recvd (s : CKAGameSt Sc Msg) (p : CKAParty) (x : Sc) :
    ckaShadow (s.recvd p x) = (ckaShadow s).recvd p () := by
  simp only [ckaShadow, CKAGameSt.recvd]

@[simp] theorem ckaShadow_canSend (s : CKAGameSt Sc Msg) (p : CKAParty) :
    (ckaShadow s).canSend p = s.canSend p :=
  CKAGameSt.canSend_eq_of_t rfl p

@[simp] theorem ckaShadow_canRecv (s : CKAGameSt Sc Msg) (p : CKAParty) :
    (ckaShadow s).canRecv p = s.canRecv p :=
  CKAGameSt.canRecv_eq_of_t rfl p

@[simp] theorem ckaShadow_t (s : CKAGameSt Sc Msg) : (ckaShadow s).t = s.t := rfl

/-- **The CKA simulator is the secure-messaging oracle.** Each oracle call of the hybrid game
with the root step `ckaHopRoot R idealK`, mapped to the states of the reduction and of the CKA
game, is the call of the simulator `smCKAImplOf` against the CKA oracle with the challenge mode
`idealK`. -/
theorem smCKA_step (C : CKADef Sc Msg Key) [CKACoins C Rand] (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (ΔFS ΔPCS t : ℕ) (ideal idealK : Bool)
    (s : SMSt Sc Msg RK Sa) (q : SMQuery W) :
    (smOracleOf C R G D ΔFS ΔPCS t ideal (ckaHopRoot R idealK) s q).map
        (Prod.map id smCKAEmb) =
      OracleAdv.simOracle (smCKAImplOf R G D t ideal) (ckaOracleP C ΔFS ΔPCS t idealK)
        (smCKAEmb s) q := by
  cases q with
  | ratchet p =>
    simp only [smOracleOf, OracleAdv.simOracle, smCKAEmb, smCKAImplOf, smCKARatchet]
    by_cases h1 : s.ck.canSend p = true
    · by_cases h2 : (s.ck.t p + 1 == t) = true
      · cases idealK <;> simp [h1, h2, ckaHopRoot, realRoot, unifKeyRoot, ckaOracleP,
          OracleAdv.run_query, PMF.map_bind, PMF.bind_bind, PMF.pure_bind, PMF.pure_map,
          ckaShadow_sent, smCKAEmb]
      · simp [h1, h2, ckaOracleP, OracleAdv.run_query, PMF.map_bind, PMF.bind_bind,
          PMF.pure_bind, PMF.pure_map, ckaShadow_sent, smCKAEmb]
    · simp [h1, PMF.pure_map, smCKAEmb]
  | recv p =>
    simp only [smOracleOf, OracleAdv.simOracle, smCKAEmb, smCKAImplOf, smCKARecvT]
    by_cases h1 : s.ck.canRecv p = true
    · cases ho : s.loc.out <;>
        simp [h1, ho, ckaOracleP, SMLoc.received, PMF.pure_map, ckaShadow_recvd, smCKAEmb]
    · simp [h1, PMF.pure_map, smCKAEmb]
  | send p m =>
    simp only [smOracleOf, OracleAdv.simOracle, smCKAEmb, smCKAImplOf, smCKASendT]
    cases h : s.loc.snd p
    · simp [PMF.pure_map, smCKAEmb]
    · by_cases hc : ckaSender (s.ck.t p) = p <;> simp [hc, PMF.pure_map, smCKAEmb]
  | chall p m =>
    simp only [smOracleOf, OracleAdv.simOracle, smCKAEmb, smCKAImplOf, smCKAChallT]
    cases h : s.loc.snd p
    · simp [PMF.pure_map, smCKAEmb]
    · by_cases hc : challOk s.loc t (s.ck.t p) p = true <;>
        simp [hc, PMF.pure_map, PMF.map_bind, smCKAEmb]
  | corrupt p =>
    simp only [smOracleOf, OracleAdv.simOracle, smCKAEmb, smCKAImplOf, smCKACorrT]
    by_cases h1 : ckaAllowCorr ΔFS ΔPCS t s.ck p = true <;>
      simp [h1, ckaOracleP, PMF.pure_map, smCKAEmb]

theorem ckaShadow_init (pub : Msg) (sA sB : Sc) :
    ckaShadow (CKAGameSt.init pub sA sB) = CKAGameSt.init () () () := by
  simp only [ckaShadow, CKAGameSt.init]

/-- **The CKA reduction** `smcCKARed R G D ideal A`: the CKA adversary that keeps the challenge
epoch of `A` and plays the tree `smCKATreeOf`. -/
noncomputable def smcCKARed (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (ideal : Bool) (A : SMCorruptAdv Sc Msg RK Sa W Ct) :
    CKACorruptAdv Sc Msg Key Rand Bool where
  tStar := A.tStar
  play := smCKATreeOf R G D ideal A.play

omit [Fintype Key] [Nonempty Key] in
/-- The secure-messaging game with the root step `root` at the challenge epoch, as a lifted
distribution when the CKA initialisation is the lift of `initP`. -/
theorem sm_corrupt_gameOf_eq_liftPMF (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (root : RK → Key → PMF (RK × Sa))
    (A : SMCorruptAdv Sc Msg RK Sa W Ct) :
    sm_corrupt_gameOf C R G D ΔFS ΔPCS ideal root A =
      liftPMF (A.tStar.bind fun t => initP.bind fun i => (PMF.uniformFintype RK).bind fun rk =>
        (OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS t ideal root) (A.play t i.1)
          (smInit i rk)).map Prod.fst) := by
  unfold sm_corrupt_gameOf
  simp only [hinit, sample_eq_liftPMF, liftPMF_bind_liftPMF]

/-- **The CKA hop.** The CKA game with challenge mode `idealK` of the reduction `smcCKARed` is
the secure-messaging game with the root step `ckaHopRoot R idealK` at the challenge epoch: the
real game for the real CKA key, the first hybrid for the uniform one. -/
theorem smCKA_game_eq (C : CKADef Sc Msg Key) [CKACoins C Rand] (hS : CKACoins.Sound C)
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal idealK : Bool) (A : SMCorruptAdv Sc Msg RK Sa W Ct) :
    cka_corrupt_game C ΔFS ΔPCS idealK (smcCKARed R G D ideal A) =
      sm_corrupt_gameOf C R G D ΔFS ΔPCS ideal (ckaHopRoot R idealK) A := by
  rw [cka_corrupt_game_eq_liftPMF C hS initP hinit, sm_corrupt_gameOf_eq_liftPMF C initP hinit]
  congr 1
  refine congrArg _ (funext fun t => congrArg _ (funext fun i => ?_))
  simp only [smcCKARed, smCKATreeOf, OracleAdv.run_rand, PMF.map_bind]
  refine congrArg _ (funext fun rk => ?_)
  rw [OracleAdv.run_simulate_fst]
  have he : smCKAEmb (smInit (Sa := Sa) i rk) =
      ((SMLoc.init rk, CKAGameSt.init () () ()), CKAGameSt.init i.1 i.2.1 i.2.2) := by
    simp only [smCKAEmb, smInit, ckaShadow_init]
  rw [← he, ← OracleAdv.run_map_state _ _ smCKAEmb (smCKA_step C R G D ΔFS ΔPCS t ideal idealK),
    PMF.map_comp]
  rfl

end CKAHop

/-! ## The root hop -/

section RootRed

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct]

/-- The opening of an epoch by party `p` in the simulator of the root hop: the CKA sending
algorithm on drawn randomness, and the root step, which at the challenge epoch `t` is a `prf`
query of the PRF-PRNG game at the root key of `p`. -/
noncomputable def smRootRatchet (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (t : ℕ) (s : SMSt Sc Msg RK Sa) (p : CKAParty) :
    OracleAdv (PPQuery RK Key) (RK × Sa) (SMAns Sc Msg RK Sa Ct × SMSt Sc Msg RK Sa) :=
  if s.ck.canSend p then
    if s.ck.t p + 1 == t then
      .rand (PMF.uniformFintype Rand) fun r =>
        .query (.prf (s.loc.rk p)) fun y =>
          .ret (.msg (CKACoins.sendR (C := C) (s.ck.st p) r).2.1,
            ⟨s.ck.sent p (CKACoins.sendR (C := C) (s.ck.st p) r).1
              (CKACoins.sendR (C := C) (s.ck.st p) r).2.1, s.loc.opened p y⟩)
    else
      .rand (PMF.uniformFintype Rand) fun r =>
        .ret (.msg (CKACoins.sendR (C := C) (s.ck.st p) r).2.1,
          ⟨s.ck.sent p (CKACoins.sendR (C := C) (s.ck.st p) r).1
            (CKACoins.sendR (C := C) (s.ck.st p) r).2.1,
            s.loc.opened p (R.stretch (s.loc.rk p, (CKACoins.sendR (C := C) (s.ck.st p) r).2.2))⟩)
  else .ret (.none, s)

/-- The receive of party `p` in the simulator of the root hop. -/
noncomputable def smRootRecv {D' R' : Type} (C : CKADef Sc Msg Key) (s : SMSt Sc Msg RK Sa)
    (p : CKAParty) : OracleAdv D' R' (SMAns Sc Msg RK Sa Ct × SMSt Sc Msg RK Sa) :=
  if s.ck.canRecv p then
    match s.loc.out with
    | some y => .ret (.none, ⟨s.ck.recvd p (C.recv (s.ck.st p) s.ck.msg).1, s.loc.recvY p y⟩)
    | none => .ret (.none, ⟨s.ck.recvd p (C.recv (s.ck.st p) s.ck.msg).1, s.loc⟩)
  else .ret (.none, s)

/-- The send of party `p` in a simulator with the full state. -/
noncomputable def smFullSend {D' R' : Type} (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (s : SMSt Sc Msg RK Sa) (p : CKAParty) (m : W × W) :
    OracleAdv D' R' (SMAns Sc Msg RK Sa Ct × SMSt Sc Msg RK Sa) :=
  match s.loc.snd p with
  | some sa =>
    if ckaSender (s.ck.t p) == p then
      .ret (.ct (D.encrypt (G.stretch sa).1 m.1 m.2), ⟨s.ck, s.loc.advanced p (G.stretch sa).2⟩)
    else .ret (.none, s)
  | none => .ret (.none, s)

/-- The challenge of party `p` in a simulator with the full state. -/
noncomputable def smFullChall {D' R' : Type} (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (t : ℕ) (ideal : Bool) (s : SMSt Sc Msg RK Sa) (p : CKAParty) (m : W × W) :
    OracleAdv D' R' (SMAns Sc Msg RK Sa Ct × SMSt Sc Msg RK Sa) :=
  match s.loc.snd p with
  | some sa =>
    if challOk s.loc t (s.ck.t p) p then
      .rand (challCt D ideal (G.stretch sa).1 m) fun c =>
        .ret (.ct c, ⟨s.ck, { s.loc.advanced p (G.stretch sa).2 with done := true }⟩)
    else .ret (.none, s)
  | none => .ret (.none, s)

/-- The corruption of party `p` in a simulator with the full state. -/
noncomputable def smFullCorr {D' R' : Type} (ΔFS ΔPCS t : ℕ) (s : SMSt Sc Msg RK Sa)
    (p : CKAParty) : OracleAdv D' R' (SMAns Sc Msg RK Sa Ct × SMSt Sc Msg RK Sa) :=
  if ckaAllowCorr ΔFS ΔPCS t s.ck p then
    .ret (.state (s.ck.st p) (s.loc.rk p) (s.loc.snd p) (s.loc.rcv p), s)
  else .ret (.none, s)

/-- The simulator of the root hop with the challenge epoch `t`: the secure-messaging oracle of
the first hybrid, with the root step at the challenge epoch asked to the `prf` oracle of the
PRF-PRNG game. -/
noncomputable def smRootImplOf (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t : ℕ) (ideal : Bool) (s : SMSt Sc Msg RK Sa) (q : SMQuery W) :
    OracleAdv (PPQuery RK Key) (RK × Sa) (SMAns Sc Msg RK Sa Ct × SMSt Sc Msg RK Sa) :=
  match q with
  | .ratchet p => smRootRatchet C R t s p
  | .recv p => smRootRecv C s p
  | .send p m => smFullSend G D s p m
  | .chall p m => smFullChall G D t ideal s p m
  | .corrupt p => smFullCorr ΔFS ΔPCS t s p

/-- **The PRF-PRNG reduction** as an oracle tree: it draws the challenge epoch of the adversary,
the CKA initialisation from `initP` and a uniform root key, and runs the adversary against the
simulator `smRootImplOf`. -/
noncomputable def smRootTreeOf (C : CKADef Sc Msg Key) [CKACoins C Rand] [Fintype RK]
    [Nonempty RK] (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (initP : PMF (Msg × Sc × Sc)) (tStar : PMF ℕ)
    (play : ℕ → Msg → OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool) :
    OracleAdv (PPQuery RK Key) (RK × Sa) Bool :=
  .rand tStar fun t =>
    .rand initP fun i =>
      .rand (PMF.uniformFintype RK) fun rk =>
        (OracleAdv.simulate (smRootImplOf C R G D ΔFS ΔPCS t ideal) (play t i.1)
          (smInit i rk)).bind fun r => .ret r.1

derive_timed smRootTreeOf

end RootRed

/-! ## The root hop: the game simulated by the PRF-PRNG reduction -/

section RootHop

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct]

/-- Away from the opening of the challenge epoch, the simulator of the root hop asks no query
and answers as the secure-messaging oracle with any root step at the challenge epoch. -/
theorem smRoot_step_noncrit (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t : ℕ) (ideal : Bool) (root : RK → Key → PMF (RK × Sa)) {U : Type}
    (O' : U → PPQuery RK Key → PMF ((RK × Sa) × U)) (s : SMSt Sc Msg RK Sa) (u : U)
    (q : SMQuery W) (hc : smCrit t s q = false) :
    OracleAdv.simOracle (smRootImplOf C R G D ΔFS ΔPCS t ideal) O' (s, u) q =
      (smOracleOf C R G D ΔFS ΔPCS t ideal root s q).map fun y => (y.1, (y.2, u)) := by
  cases q with
  | ratchet p =>
    simp only [smCrit, Bool.and_eq_false_iff] at hc
    simp only [OracleAdv.simOracle, smRootImplOf, smRootRatchet, smOracleOf]
    rcases hc with h | h
    · simp [h, PMF.pure_map]
    · by_cases hs : s.ck.canSend p = true <;>
        simp [hs, h, PMF.map_bind, PMF.pure_bind, PMF.pure_map]
  | recv p =>
    simp only [OracleAdv.simOracle, smRootImplOf, smRootRecv, smOracleOf]
    by_cases h : s.ck.canRecv p = true
    · cases ho : s.loc.out <;> simp [h, ho, SMLoc.received, PMF.pure_map]
    · simp [h, PMF.pure_map]
  | send p m =>
    simp only [OracleAdv.simOracle, smRootImplOf, smFullSend, smOracleOf]
    cases h : s.loc.snd p
    · simp [PMF.pure_map]
    · by_cases hc : ckaSender (s.ck.t p) = p <;> simp [hc, PMF.pure_map]
  | chall p m =>
    simp only [OracleAdv.simOracle, smRootImplOf, smFullChall, smOracleOf]
    cases h : s.loc.snd p
    · simp [PMF.pure_map]
    · by_cases hc : challOk s.loc t (s.ck.t p) p = true <;>
        simp [hc, PMF.pure_map, PMF.map_bind]
  | corrupt p =>
    simp only [OracleAdv.simOracle, smRootImplOf, smFullCorr, smOracleOf]
    by_cases h : ckaAllowCorr ΔFS ΔPCS t s.ck p = true <;> simp [h, PMF.pure_map]

variable [Fintype RK] [Nonempty RK] [Fintype Key] [Nonempty Key] [Fintype Sa] [Nonempty Sa]
  [DecidableEq RK] [DecidableEq Key]

/-- The root step at the challenge epoch with the input `k` fixed in advance. -/
noncomputable def fixedKeyRoot (R : PRGDef (RK × Key) (RK × Sa)) (k : Key) (rk : RK) (_ : Key) :
    PMF (RK × Sa) :=
  PMF.pure (R.stretch (rk, k))

/-- The root step at the challenge epoch of the second hybrid: a uniform output. -/
noncomputable def unifRoot (_ : RK) (_ : Key) : PMF (RK × Sa) := PMF.uniformFintype (RK × Sa)

/-- **The simulator against the real PRF-PRNG game.** With the hidden input `k`, each call of
the game with the root step `fixedKeyRoot R k` at the challenge epoch, with the PRF-PRNG state
attached, is the call of the simulator against the real PRF-PRNG oracle. -/
theorem smRoot_step_real (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t : ℕ) (ideal : Bool) (rk' : RK) (k : Key) (s : SMSt Sc Msg RK Sa)
    (q : SMQuery W) :
    (smOracleOf C R G D ΔFS ΔPCS t ideal (fixedKeyRoot R k) s q).map
        (Prod.map id fun s => (s, (⟨rk', k, [], []⟩ : PPSt RK Key (RK × Sa)))) =
      OracleAdv.simOracle (smRootImplOf C R G D ΔFS ΔPCS t ideal)
        (ppOracle (rootFn R) false false) (s, ⟨rk', k, [], []⟩) q := by
  cases hc : smCrit t s q
  · rw [smRoot_step_noncrit C R G D ΔFS ΔPCS t ideal (fixedKeyRoot R k) _ s _ q hc]
    rfl
  · cases q with
    | ratchet p =>
      simp only [smCrit, Bool.and_eq_true] at hc
      simp [OracleAdv.simOracle, smRootImplOf, smRootRatchet, smOracleOf, hc.1, hc.2,
        fixedKeyRoot, ppOracle, rootFn, PMF.map_bind, PMF.pure_bind, PMF.pure_map]
    | _ => simp [smCrit] at hc

/-- **The simulator against the ideal PRF-PRNG game.** From a state whose table of the `prf`
oracle is empty unless the challenge epoch has been opened, each call of the simulator against
the ideal PRF-PRNG oracle, with the PRF-PRNG state dropped, is the call of the game with a
uniform root output at the challenge epoch. -/
theorem smRoot_step_ideal (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t : ℕ) (ideal : Bool) (s : SMSt Sc Msg RK Sa) (u : PPSt RK Key (RK × Sa))
    (hu : u.tR = [] ∨ smOpened t s) (q : SMQuery W) :
    (OracleAdv.simOracle (smRootImplOf C R G D ΔFS ΔPCS t ideal)
        (ppOracle (rootFn R) true true) (s, u) q).map (Prod.map id Prod.fst) =
      smOracleOf C R G D ΔFS ΔPCS t ideal unifRoot s q := by
  cases hc : smCrit t s q
  · rw [smRoot_step_noncrit C R G D ΔFS ΔPCS t ideal unifRoot _ s _ q hc, PMF.map_comp]
    exact PMF.map_id _
  · have hu' : u.tR = [] := by
      rcases hu with h | h
      · exact h
      · rw [smCrit_of_opened t s h q] at hc; exact absurd hc (by decide)
    cases q with
    | ratchet p =>
      simp only [smCrit, Bool.and_eq_true] at hc
      simp only [OracleAdv.simOracle, smRootImplOf, smRootRatchet, smOracleOf, hc.1, hc.2,
        ite_true, ppOracle, rfOracle, hu', List.lookup, OracleAdv.run_rand, OracleAdv.run_query,
        OracleAdv.run_ret, PMF.map_bind, PMF.bind_map, PMF.pure_map, unifRoot]
      simp [Function.comp_def, PMF.pure_map]
    | _ => simp [smCrit] at hc

/-- **The PRF-PRNG reduction** `smcRootRed C R G D ΔFS ΔPCS ideal initP A`: the tree
`smRootTreeOf` at the challenge epoch and the interaction of `A`. -/
noncomputable def smcRootRed (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (initP : PMF (Msg × Sc × Sc))
    (A : SMCorruptAdv Sc Msg RK Sa W Ct) : OracleAdv (PPQuery RK Key) (RK × Sa) Bool :=
  smRootTreeOf C R G D ΔFS ΔPCS ideal initP A.tStar A.play

/-- Running the PRF-PRNG reduction against an oracle is running the adversary against the
composed oracle from the drawn initial state. -/
theorem smcRootRed_run (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (initP : PMF (Msg × Sc × Sc))
    (A : SMCorruptAdv Sc Msg RK Sa W Ct) {U : Type}
    (O' : U → PPQuery RK Key → PMF ((RK × Sa) × U)) (u : U) :
    (OracleAdv.run O' (smcRootRed C R G D ΔFS ΔPCS ideal initP A) u).map Prod.fst =
      A.tStar.bind fun t => initP.bind fun i => (PMF.uniformFintype RK).bind fun rk =>
        (OracleAdv.run (OracleAdv.simOracle (smRootImplOf C R G D ΔFS ΔPCS t ideal) O')
          (A.play t i.1) (smInit i rk, u)).map Prod.fst := by
  simp only [smcRootRed, smRootTreeOf, OracleAdv.run_rand, PMF.map_bind,
    OracleAdv.run_simulate_fst]

/-- **The real side of the root hop.** The real PRF-PRNG game of `smcRootRed` is the first
hybrid: the root step at the challenge epoch on a uniform key. -/
theorem smRoot_real_eq (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (A : SMCorruptAdv Sc Msg RK Sa W Ct) :
    pp_game (rootFn R) false false (smcRootRed C R G D ΔFS ΔPCS ideal initP A) =
      sm_corrupt_gameOf C R G D ΔFS ΔPCS ideal (unifKeyRoot R) A := by
  rw [sm_corrupt_gameOf_eq_liftPMF C initP hinit]
  unfold pp_game
  congr 1
  have h1 : ∀ (rk' : RK) (k : Key),
      (OracleAdv.run (ppOracle (rootFn R) false false) (smcRootRed C R G D ΔFS ΔPCS ideal initP A)
        ⟨rk', k, [], []⟩).map Prod.fst =
      A.tStar.bind fun t => initP.bind fun i => (PMF.uniformFintype RK).bind fun rk =>
        (OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS t ideal (fixedKeyRoot R k)) (A.play t i.1)
          (smInit i rk)).map Prod.fst := by
    intro rk' k
    rw [smcRootRed_run]
    refine congrArg _ (funext fun t => congrArg _ (funext fun i => congrArg _ (funext fun rk => ?_)))
    rw [← OracleAdv.run_map_state _ _ (fun s => (s, (⟨rk', k, [], []⟩ : PPSt RK Key (RK × Sa))))
      (smRoot_step_real C R G D ΔFS ΔPCS t ideal rk' k), PMF.map_comp]
    rfl
  simp only [h1, PMF.bind_const]
  have h2 : ∀ (t : ℕ) (i : Msg × Sc × Sc) (rk : RK),
      (OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS t ideal (unifKeyRoot R)) (A.play t i.1)
        (smInit i rk)).map Prod.fst =
      (PMF.uniformFintype Key).bind fun k =>
        (OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS t ideal (fixedKeyRoot R k)) (A.play t i.1)
          (smInit i rk)).map Prod.fst := by
    intro t i rk
    rw [sm_run_eager C R G D ΔFS ΔPCS t ideal (PMF.uniformFintype Key) (unifKeyRoot R)
      (fixedKeyRoot R) (fun _ _ => rfl), PMF.map_bind]
  simp only [h2]
  rw [PMF.bind_comm]
  refine congrArg _ (funext fun t => ?_)
  rw [PMF.bind_comm]
  refine congrArg _ (funext fun i => ?_)
  rw [PMF.bind_comm]

/-- **The ideal side of the root hop.** The ideal PRF-PRNG game of `smcRootRed` is the second
hybrid: a uniform root output at the challenge epoch. -/
theorem smRoot_ideal_eq (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (A : SMCorruptAdv Sc Msg RK Sa W Ct) :
    pp_game (rootFn R) true true (smcRootRed C R G D ΔFS ΔPCS ideal initP A) =
      sm_corrupt_gameOf C R G D ΔFS ΔPCS ideal unifRoot A := by
  rw [sm_corrupt_gameOf_eq_liftPMF C initP hinit]
  unfold pp_game
  congr 1
  have h1 : ∀ (rk' : RK) (k : Key),
      (OracleAdv.run (ppOracle (rootFn R) true true) (smcRootRed C R G D ΔFS ΔPCS ideal initP A)
        ⟨rk', k, [], []⟩).map Prod.fst =
      A.tStar.bind fun t => initP.bind fun i => (PMF.uniformFintype RK).bind fun rk =>
        (OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS t ideal unifRoot) (A.play t i.1)
          (smInit i rk)).map Prod.fst := by
    intro rk' k
    rw [smcRootRed_run]
    refine congrArg _ (funext fun t => congrArg _ (funext fun i => congrArg _ (funext fun rk => ?_)))
    refine OracleAdv.run_map_fst_of_map_state_inv _ _ Prod.fst
      (fun x => x.2.tR = [] ∨ smOpened t x.1) ?_
      (fun x q hx => smRoot_step_ideal C R G D ΔFS ΔPCS t ideal x.1 x.2 hx q) _ _ (Or.inl rfl)
    intro x q hx y hy
    cases hc : smCrit t x.1 q
    · rw [smRoot_step_noncrit C R G D ΔFS ΔPCS t ideal unifRoot _ x.1 x.2 q hc] at hy
      simp only [PMF.support_map, Set.mem_image] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      rcases hx with h | h
      · exact Or.inl h
      · exact Or.inr (smOracleOf_opened C R G D ΔFS ΔPCS t ideal _ x.1 q h z hz)
    · have hm : (y.1, y.2.1) ∈ (smOracleOf C R G D ΔFS ΔPCS t ideal unifRoot x.1 q).support := by
        rw [← smRoot_step_ideal C R G D ΔFS ΔPCS t ideal x.1 x.2 hx q, PMF.support_map]
        exact ⟨y, hy, rfl⟩
      exact Or.inr (smOracleOf_opened_of_crit C R G D ΔFS ΔPCS t ideal _ x.1 q hc _ hm)
  simp only [h1, PMF.bind_const]

end RootHop

/-! ## Forward-secure AEAD with corruption -/

section FSAEADGame

variable {Sa W Ct : Type} [SampleableType W] [SampleableType Ct]

/-- The queries of the FS-AEAD adversary. -/
inductive FSQuery (W : Type) where
  /-- The sender encrypts the message `m` under the next key of its chain. -/
  | enc (m : W × W)
  /-- As `enc`, once, with a uniform ciphertext in the ideal game. -/
  | chall (m : W × W)
  /-- The state of the sender is returned. -/
  | corrupt

/-- The answers of the FS-AEAD oracles. -/
inductive FSAns (Sa Ct : Type) where
  /-- A refused query. -/
  | none
  /-- A ciphertext. -/
  | ct (c : Ct)
  /-- The state of the sender. -/
  | state (s : Sa)

/-- The state of the FS-AEAD game: the current state of the sender's chain, the initial state
of the epoch (the state of the receiver, which has no oracle in this confidentiality game), and
the flags of the challenge and of the corruption. -/
structure FSSt (Sa : Type) where
  /-- The current state of the sender. -/
  cur : Sa
  /-- The initial state of the epoch, held by the receiver. -/
  init : Sa
  /-- The challenge has been asked. -/
  done : Bool
  /-- The sender has been corrupted. -/
  corr : Bool

/-- The oracle of the FS-AEAD game of the generator `G` and the AEAD `D` (Alwen, Coretti and
Dodis, §4.3): `enc m` encrypts under the next key `(G cur).1` and moves the state to
`(G cur).2`; `chall m` does the same once, with a uniform ciphertext if `ideal`, and is refused
after a corruption; `corrupt` returns the current state. A corruption after the challenge is
allowed: the state has moved past the challenge key (forward secrecy). -/
noncomputable def fsOracle (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (ideal : Bool)
    (s : FSSt Sa) : FSQuery W → PMF (FSAns Sa Ct × FSSt Sa)
  | .enc m => PMF.pure (.ct (D.encrypt (G.stretch s.cur).1 m.1 m.2), { s with cur := (G.stretch s.cur).2 })
  | .chall m =>
    if !s.done && !s.corr then
      (challCt D ideal (G.stretch s.cur).1 m).bind fun c =>
        PMF.pure (.ct c, { s with cur := (G.stretch s.cur).2, done := true })
    else PMF.pure (.none, s)
  | .corrupt => PMF.pure (.state s.cur, { s with corr := true })

variable [Fintype Sa] [Nonempty Sa]

/-- The FS-AEAD game with corruption: a uniform initial state of the epoch, and the run of the
adversary against `fsOracle`. -/
noncomputable def fsaead_corrupt_game (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (ideal : Bool)
    (A : OracleAdv (FSQuery W) (FSAns Sa Ct) Bool) : SPComp Bool :=
  liftPMF ((PMF.uniformFintype Sa).bind fun sa =>
    (OracleAdv.run (fsOracle G D ideal) A ⟨sa, sa, false, false⟩).map Prod.fst)

/-- **FS-AEAD advantage with corruption** of the adversary `A`. -/
noncomputable def FSAEAD_Corrupt_Advantage (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (A : OracleAdv (FSQuery W) (FSAns Sa Ct) Bool) : ℝ≥0∞ :=
  Advantage (fsaead_corrupt_game G D false A) (fsaead_corrupt_game G D true A)

end FSAEADGame

/-! ## The FS-AEAD reduction -/

section FSRed

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct]

/-- Party `p` opened the challenge epoch with the next root key `rk`; its sending chain and the
root output in transit are held by the FS-AEAD game. -/
def SMLoc.openedX (l : SMLoc RK Sa) (p : CKAParty) (rk : RK) : SMLoc RK Sa :=
  { l with rk := Function.update l.rk p rk, snd := Function.update l.snd p none, out := none }

/-- Party `p` received the challenge epoch with the root key `rk`; its receiving chain is held
by the FS-AEAD game. -/
def SMLoc.recvX (l : SMLoc RK Sa) (p : CKAParty) (rk : RK) : SMLoc RK Sa :=
  { l with rk := Function.update l.rk p rk, rcv := Function.update l.rcv p none }

/-- The state of the FS-AEAD reduction: a secure-messaging state, and the marks of the chains
and of the root output that are held by the FS-AEAD game (those of the challenge epoch). -/
structure FSSim (Sc Msg RK Sa : Type) where
  /-- The secure-messaging state, with the held values left out. -/
  s : SMSt Sc Msg RK Sa
  /-- The sending chain of the party is the FS-AEAD sender. -/
  sndX : CKAParty → Bool
  /-- The receiving chain of the party is the initial state of the FS-AEAD game. -/
  rcvX : CKAParty → Bool
  /-- The root output in transit is the root key `rk⋆` with the initial FS-AEAD state. -/
  outX : Bool

/-- The opening of an epoch by party `p` in the FS-AEAD simulator; at the challenge epoch the
next root key is `rkS` and the chain is the FS-AEAD game's. -/
noncomputable def smFSRatchet (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (t : ℕ) (rkS : RK) (x : FSSim Sc Msg RK Sa) (p : CKAParty) :
    OracleAdv (FSQuery W) (FSAns Sa Ct) (SMAns Sc Msg RK Sa Ct × FSSim Sc Msg RK Sa) :=
  if x.s.ck.canSend p then
    .rand (PMF.uniformFintype Rand) fun r =>
      if x.s.ck.t p + 1 == t then
        .ret (.msg (CKACoins.sendR (C := C) (x.s.ck.st p) r).2.1,
          ⟨⟨x.s.ck.sent p (CKACoins.sendR (C := C) (x.s.ck.st p) r).1
            (CKACoins.sendR (C := C) (x.s.ck.st p) r).2.1, x.s.loc.openedX p rkS⟩,
            Function.update x.sndX p true, x.rcvX, true⟩)
      else
        .ret (.msg (CKACoins.sendR (C := C) (x.s.ck.st p) r).2.1,
          ⟨⟨x.s.ck.sent p (CKACoins.sendR (C := C) (x.s.ck.st p) r).1
            (CKACoins.sendR (C := C) (x.s.ck.st p) r).2.1,
            x.s.loc.opened p (R.stretch (x.s.loc.rk p, (CKACoins.sendR (C := C) (x.s.ck.st p) r).2.2))⟩,
            Function.update x.sndX p false, x.rcvX, false⟩)
  else .ret (.none, x)

/-- The receive of party `p` in the FS-AEAD simulator. -/
noncomputable def smFSRecv (C : CKADef Sc Msg Key) (rkS : RK) (x : FSSim Sc Msg RK Sa)
    (p : CKAParty) :
    OracleAdv (FSQuery W) (FSAns Sa Ct) (SMAns Sc Msg RK Sa Ct × FSSim Sc Msg RK Sa) :=
  if x.s.ck.canRecv p then
    if x.outX then
      .ret (.none, ⟨⟨x.s.ck.recvd p (C.recv (x.s.ck.st p) x.s.ck.msg).1, x.s.loc.recvX p rkS⟩,
        x.sndX, Function.update x.rcvX p true, x.outX⟩)
    else
      match x.s.loc.out with
      | some y =>
        .ret (.none, ⟨⟨x.s.ck.recvd p (C.recv (x.s.ck.st p) x.s.ck.msg).1, x.s.loc.recvY p y⟩,
          x.sndX, Function.update x.rcvX p false, x.outX⟩)
      | none =>
        .ret (.none, ⟨⟨x.s.ck.recvd p (C.recv (x.s.ck.st p) x.s.ck.msg).1, x.s.loc⟩,
          x.sndX, x.rcvX, x.outX⟩)
  else .ret (.none, x)

/-- The send of party `p` in the FS-AEAD simulator: forwarded to the FS-AEAD game on the chain
of the challenge epoch, computed locally otherwise. -/
noncomputable def smFSSend (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (x : FSSim Sc Msg RK Sa)
    (p : CKAParty) (m : W × W) :
    OracleAdv (FSQuery W) (FSAns Sa Ct) (SMAns Sc Msg RK Sa Ct × FSSim Sc Msg RK Sa) :=
  if x.sndX p then
    if ckaSender (x.s.ck.t p) == p then
      .query (.enc m) fun a =>
        match a with
        | .ct c => .ret (.ct c, x)
        | .none => .ret (.none, x)
        | .state _ => .ret (.none, x)
    else .ret (.none, x)
  else
    match x.s.loc.snd p with
    | some sa =>
      if ckaSender (x.s.ck.t p) == p then
        .ret (.ct (D.encrypt (G.stretch sa).1 m.1 m.2),
          { x with s := ⟨x.s.ck, x.s.loc.advanced p (G.stretch sa).2⟩ })
      else .ret (.none, x)
    | none => .ret (.none, x)

/-- The challenge of party `p` in the FS-AEAD simulator: forwarded to the FS-AEAD game. -/
noncomputable def smFSChall (t : ℕ) (x : FSSim Sc Msg RK Sa) (p : CKAParty) (m : W × W) :
    OracleAdv (FSQuery W) (FSAns Sa Ct) (SMAns Sc Msg RK Sa Ct × FSSim Sc Msg RK Sa) :=
  if x.sndX p && challOk x.s.loc t (x.s.ck.t p) p then
    .query (.chall m) fun a =>
      match a with
      | .ct c => .ret (.ct c, { x with s := ⟨x.s.ck, { x.s.loc with done := true }⟩ })
      | .none => .ret (.none, x)
      | .state _ => .ret (.none, x)
  else .ret (.none, x)

/-- The corruption of party `p` in the FS-AEAD simulator. -/
noncomputable def smFSCorr (ΔFS ΔPCS t : ℕ) (x : FSSim Sc Msg RK Sa) (p : CKAParty) :
    OracleAdv (FSQuery W) (FSAns Sa Ct) (SMAns Sc Msg RK Sa Ct × FSSim Sc Msg RK Sa) :=
  if ckaAllowCorr ΔFS ΔPCS t x.s.ck p then
    .ret (.state (x.s.ck.st p) (x.s.loc.rk p) (x.s.loc.snd p) (x.s.loc.rcv p), x)
  else .ret (.none, x)

/-- The simulator of the FS-AEAD reduction with the challenge epoch `t` and the root key `rkS`
of the challenge epoch: the secure-messaging oracle of the second hybrid with the root output
`(rkS, sa)` at the challenge epoch, where the FS-AEAD instance of the challenge epoch, from the
initial state `sa`, is the FS-AEAD game's. -/
noncomputable def smFSImplOf (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t : ℕ) (rkS : RK) (x : FSSim Sc Msg RK Sa) (q : SMQuery W) :
    OracleAdv (FSQuery W) (FSAns Sa Ct) (SMAns Sc Msg RK Sa Ct × FSSim Sc Msg RK Sa) :=
  match q with
  | .ratchet p => smFSRatchet C R t rkS x p
  | .recv p => smFSRecv C rkS x p
  | .send p m => smFSSend G D x p m
  | .chall p m => smFSChall t x p m
  | .corrupt p => smFSCorr ΔFS ΔPCS t x p

/-- **The FS-AEAD reduction** as an oracle tree: it draws the challenge epoch, the CKA
initialisation, the initial root key and the root key of the challenge epoch, and runs the
adversary against the simulator `smFSImplOf`. -/
noncomputable def smFSTreeOf (C : CKADef Sc Msg Key) [CKACoins C Rand] [Fintype RK]
    [Nonempty RK] (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (initP : PMF (Msg × Sc × Sc)) (tStar : PMF ℕ)
    (play : ℕ → Msg → OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool) :
    OracleAdv (FSQuery W) (FSAns Sa Ct) Bool :=
  .rand tStar fun t =>
    .rand initP fun i =>
      .rand (PMF.uniformFintype RK) fun rk =>
        .rand (PMF.uniformFintype RK) fun rkS =>
          (OracleAdv.simulate (smFSImplOf C R G D ΔFS ΔPCS t rkS) (play t i.1)
            ⟨smInit i rk, fun _ => false, fun _ => false, false⟩).bind fun r => .ret r.1

derive_timed smFSTreeOf

end FSRed

end CatCrypt.Crypto.Messaging
