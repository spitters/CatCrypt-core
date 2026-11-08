/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SMScheme
import CatCryptCore.Tactics.AutoDispatchExt

/-!
# Authenticity of secure-messaging schemes

The secure-messaging game of Alwen, Coretti and Dodis (EUROCRYPT 2019, §3) with decryption of
ciphertexts chosen by the adversary, stated over a scheme with decryption `SMAuthScheme`, and the
reduction of its advantage to an integrity advantage and the corruption advantage of
`CatCryptCore.Crypto.Messaging.SMScheme`.

## Schemes with decryption

`SMAuthScheme` extends `SMScheme` by the decryption `dec x j ad c` of the ciphertext `c` with
associated data `ad` at the position `j` of the current receiving epoch of a party in state `x`.
The position is the public header of the ciphertext: a receiver decrypts the messages of an
epoch in any order (immediate decryption).

## The game

`smAuthGame M ΔFS ΔPCS idealC idealD A` extends the corruption game `smCorruptGame` by the query
`deliver p j ad c`, which hands the ciphertext `c` with associated data `ad` and position `j` to
party `p` in the epoch it currently receives. The game keeps the log of the honest ciphertexts
(epoch, position, plaintext, associated data, ciphertext) and the counters of every answered
corruption. A delivery is answered only when `p` is the receiver of its current epoch and every
answered corruption leaves that epoch outside the corruption window: the epoch `e` with
`ckaAllowCorr ΔFS ΔPCS e` true at the counters of the corruption, the gate of a challenge in
epoch `e`. The real decryption (`idealD = false`) answers `M.dec`; the ideal decryption answers
from the log, so that every injected ciphertext is rejected. `idealC` selects the uniform
challenge ciphertext of the corruption game.

* `SMAuthScheme.authAdvantage` — the real game against the game with uniform challenge and
  ideal decryption;
* `SMAuthScheme.intAdvantage` — the real game against the game with ideal decryption.

## The bound

The game with ideal decryption is the corruption game of the reduction `smAuthRed`, which keeps
the log and the counters itself and answers every delivery from its log
(`smAuthGame_logDec_eq`). Hence (`SMAuthScheme.authAdvantage_le`)

  `Adv_auth(A) ≤ Adv_int(A) + Adv_corrupt(smAuthRed A)`,

and for the ACD construction with decryption `acdAuthSM`, the corruption term is the bound of
`acdSM_corruptAdvantage_le` at `smAuthRed A` (`acdAuthSM_authAdvantage_le`).

## Main definitions

* `SMAuthScheme`, `SMAuthQuery`, `SMAuthAns`, `SMLogEntry`, `SMAuthAux`, `smAuthOracle`,
  `SMAuthAdv`, `smAuthGame`, `SMAuthScheme.authAdvantage`, `SMAuthScheme.intAdvantage`
* `smAuthImpl`, `smAuthRed` — the reduction to the corruption game
* `chainKey`, `acdAuthSM` — the ACD construction with the decryption of the receiving chain

## Main results

* `smAuthGame_logDec_eq` — the game with ideal decryption is the corruption game of
  `smAuthRed`
* `SMAuthScheme.authAdvantage_le`, `acdAuthSM_authAdvantage_le` — the bounds above
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
  CatCrypt.Crypto.PRPPRF
open scoped ENNReal

/-! ## Schemes with decryption and the game -/

/-- A secure-messaging scheme with decryption: `dec x j ad c` decrypts the ciphertext `c` with
associated data `ad` at the position `j` of the current receiving epoch of a party in state
`x`, and gives the plaintext or `none`. -/
structure SMAuthScheme (St Pub Rand W Ct Leak : Type) extends SMScheme St Pub Rand W Ct Leak where
  /-- Decryption at a position of the current receiving epoch. -/
  dec : St → ℕ → W → Ct → Option W

/-- The queries of the authenticity game: a query of the corruption game, or the delivery of a
ciphertext `c` with associated data `ad` at the position `j` to party `p`. -/
inductive SMAuthQuery (W Ct : Type) where
  /-- A query of the corruption game. -/
  | sm (q : SMQuery W)
  /-- The delivery of a ciphertext to a party. -/
  | deliver (p : CKAParty) (j : ℕ) (ad : W) (c : Ct)

/-- The answers of the authenticity game. -/
inductive SMAuthAns (Pub Ct Leak W : Type) where
  /-- An answer of the corruption game. -/
  | sm (a : SMSchemeAns Pub Ct Leak)
  /-- The answer to a delivery: a plaintext or a rejection. -/
  | dec (m : Option W)

/-- An honest ciphertext: its epoch, its position in the epoch, the plaintext, the associated
data and the ciphertext. -/
structure SMLogEntry (W Ct : Type) where
  /-- The epoch. -/
  e : ℕ
  /-- The position in the epoch. -/
  j : ℕ
  /-- The plaintext. -/
  pt : W
  /-- The associated data. -/
  ad : W
  /-- The ciphertext. -/
  ct : Ct

/-- The bookkeeping of the authenticity game: the log of the honest ciphertexts, and the party
and the epoch counters of every answered corruption. -/
structure SMAuthAux (W Ct : Type) where
  /-- The honest ciphertexts. -/
  log : List (SMLogEntry W Ct)
  /-- The answered corruptions. -/
  corrs : List (CKAParty × CKAGameSt Unit Unit)

namespace SMAuthAux

variable {W Ct Pub Leak : Type}

/-- The empty bookkeeping. -/
def init : SMAuthAux W Ct := ⟨[], []⟩

/-- The position of the next honest ciphertext of epoch `e`. -/
def nextIdx (x : SMAuthAux W Ct) (e : ℕ) : ℕ := x.log.countP fun l => l.e == e

/-- Epoch `e` lies outside the corruption window of every answered corruption. -/
def safe (ΔFS ΔPCS : ℕ) (x : SMAuthAux W Ct) (e : ℕ) : Bool :=
  x.corrs.all fun c => ckaAllowCorr ΔFS ΔPCS e c.2 c.1

/-- The log with the honest ciphertext `c` of the message `m` in epoch `e` added. -/
def record (x : SMAuthAux W Ct) (e : ℕ) (m : W × W) (c : Ct) : SMAuthAux W Ct :=
  { x with log := ⟨e, x.nextIdx e, m.1, m.2, c⟩ :: x.log }

/-- The bookkeeping after the query `q` of the corruption game, answered by `a`, at the epoch
counters `sh` before the query: a ciphertext of a send or a challenge is logged in the epoch
of the sender, an answered corruption is recorded with the counters. -/
def upd (x : SMAuthAux W Ct) (sh : CKAGameSt Unit Unit) :
    SMQuery W → SMSchemeAns Pub Ct Leak → SMAuthAux W Ct
  | .send p m, .ct c => x.record (sh.t p) m c
  | .chall p m, .ct c => x.record (sh.t p) m c
  | .corrupt p, .state _ => { x with corrs := (p, sh) :: x.corrs }
  | _, _ => x

/-- A delivery to party `p` at the epoch counters `sh` is answered: `p` receives in its current
epoch, and the epoch is safe. -/
def canDeliver (ΔFS ΔPCS : ℕ) (x : SMAuthAux W Ct) (sh : CKAGameSt Unit Unit) (p : CKAParty) :
    Bool :=
  (ckaSender (sh.t p) != p) && x.safe ΔFS ΔPCS (sh.t p)

/-- Decryption from the log: the plaintext of the honest ciphertext `c` with associated data
`ad` at the position `j` of epoch `e`, or `none`. -/
def logDec [DecidableEq W] [DecidableEq Ct] (x : SMAuthAux W Ct) (e j : ℕ) (ad : W) (c : Ct) :
    Option W :=
  (x.log.find? fun l => decide (l.e = e ∧ l.j = j ∧ l.ad = ad ∧ l.ct = c)).map SMLogEntry.pt

/-- The ideal answer to a delivery to party `p` at the epoch counters `sh`: decryption from the
log when the delivery is answered, `none` otherwise. -/
def logAns [DecidableEq W] [DecidableEq Ct] (ΔFS ΔPCS : ℕ) (x : SMAuthAux W Ct)
    (sh : CKAGameSt Unit Unit) (p : CKAParty) (j : ℕ) (ad : W) (c : Ct) : Option W :=
  if x.canDeliver ΔFS ΔPCS sh p then x.logDec (sh.t p) j ad c else none

end SMAuthAux

/-- The epoch counters after the query `q` of the corruption game: an epoch is opened when the
party may send, received when it may receive. -/
def ckaShadowStep {W : Type} (sh : CKAGameSt Unit Unit) : SMQuery W → CKAGameSt Unit Unit
  | .ratchet p => if sh.canSend p then sh.sent p () () else sh
  | .recv p => if sh.canRecv p then sh.recvd p () else sh
  | _ => sh

section Game

variable {St Pub Rand W Ct Leak : Type} [Fintype Rand] [Nonempty Rand] [DecidableEq W]
  [DecidableEq Ct]

/-- The oracle of the authenticity game over `M` with the challenge epoch `t`: the queries of
the corruption game are answered by `smSchemeOracle` with the challenge mode `idealC` and
logged; a delivery is answered by `M.dec` (`idealD = false`) or from the log, and only when
`SMAuthAux.canDeliver` allows it. -/
noncomputable def smAuthOracle (M : SMAuthScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS t : ℕ)
    (idealC idealD : Bool) (s : SMSchemeSt St Pub × SMAuthAux W Ct) :
    SMAuthQuery W Ct → PMF (SMAuthAns Pub Ct Leak W × (SMSchemeSt St Pub × SMAuthAux W Ct))
  | .sm q => (smSchemeOracle M.toSMScheme ΔFS ΔPCS t idealC s.1 q).map fun y =>
      (.sm y.1, (y.2, s.2.upd (ckaShadow s.1.ck) q y.1))
  | .deliver p j ad c => PMF.pure (.dec (if idealD then
      s.2.logAns ΔFS ΔPCS (ckaShadow s.1.ck) p j ad c
    else if s.2.canDeliver ΔFS ΔPCS (ckaShadow s.1.ck) p then M.dec (s.1.ck.st p) j ad c
    else none), s)

/-- An adversary of the authenticity game: a distribution of the challenge epoch, and for each
challenge epoch and public value of the initialisation an oracle tree. -/
structure SMAuthAdv (Pub W Ct Leak : Type) : Type 1 where
  /-- The choice of the challenge epoch. -/
  tStar : PMF ℕ
  /-- The interaction with the oracles. -/
  play : ℕ → Pub → OracleAdv (SMAuthQuery W Ct) (SMAuthAns Pub Ct Leak W) Bool

/-- **The authenticity game over a scheme**: the adversary chooses the challenge epoch `t`, the
scheme is initialised, and the adversary interacts with `smAuthOracle`. -/
noncomputable def smAuthGame (M : SMAuthScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS : ℕ)
    (idealC idealD : Bool) (A : SMAuthAdv Pub W Ct Leak) : SPComp Bool :=
  SPComp.bind (liftPMF A.tStar) fun t =>
    SPComp.bind M.init fun i =>
      liftPMF ((OracleAdv.run (smAuthOracle M ΔFS ΔPCS t idealC idealD) (A.play t i.1)
        (SMSchemeSt.init i, SMAuthAux.init)).map Prod.fst)

/-- **The advantage of `A` in the authenticity game over `M`**: the real game against the game
with a uniform challenge ciphertext and decryption from the log. -/
noncomputable def SMAuthScheme.authAdvantage (M : SMAuthScheme St Pub Rand W Ct Leak)
    (ΔFS ΔPCS : ℕ) (A : SMAuthAdv Pub W Ct Leak) : ℝ≥0∞ :=
  Advantage (smAuthGame M ΔFS ΔPCS false false A) (smAuthGame M ΔFS ΔPCS true true A)

/-- **The integrity advantage of `A` over `M`**: the real game against the game with
decryption from the log. -/
noncomputable def SMAuthScheme.intAdvantage (M : SMAuthScheme St Pub Rand W Ct Leak)
    (ΔFS ΔPCS : ℕ) (A : SMAuthAdv Pub W Ct Leak) : ℝ≥0∞ :=
  Advantage (smAuthGame M ΔFS ΔPCS false false A) (smAuthGame M ΔFS ΔPCS false true A)

end Game

/-! ## The reduction to the corruption game -/

section Red

variable {St Pub Rand W Ct Leak : Type} [DecidableEq W] [DecidableEq Ct]

/-- The simulator of the reduction to the corruption game. Its state is the epoch counters and
the bookkeeping of the authenticity game: a query of the corruption game is forwarded and
logged, a delivery is answered from the log. -/
def smAuthImpl (ΔFS ΔPCS : ℕ) (σ : CKAGameSt Unit Unit × SMAuthAux W Ct) :
    SMAuthQuery W Ct → OracleAdv (SMQuery W) (SMSchemeAns Pub Ct Leak)
      (SMAuthAns Pub Ct Leak W × (CKAGameSt Unit Unit × SMAuthAux W Ct))
  | .sm q => .query q fun a => .ret (.sm a, (ckaShadowStep σ.1 q, σ.2.upd σ.1 q a))
  | .deliver p j ad c => .ret (.dec (σ.2.logAns ΔFS ΔPCS σ.1 p j ad c), σ)

/-- **The reduction to the corruption game**: the adversary of `smCorruptGame` that keeps the
challenge epoch of `A` and runs `A` against the simulator `smAuthImpl`. -/
def smAuthRed (ΔFS ΔPCS : ℕ) (A : SMAuthAdv Pub W Ct Leak) : SMSchemeAdv Pub W Ct Leak where
  tStar := A.tStar
  play t pub := (OracleAdv.simulate (smAuthImpl ΔFS ΔPCS) (A.play t pub)
    (CKAGameSt.init () () (), SMAuthAux.init)).bind fun r => .ret r.1

/-- The state of the simulator and of the corruption game that a state of the authenticity game
corresponds to. -/
def smAuthEmb (s : SMSchemeSt St Pub × SMAuthAux W Ct) :
    (CKAGameSt Unit Unit × SMAuthAux W Ct) × SMSchemeSt St Pub :=
  ((ckaShadow s.1.ck, s.2), s.1)

variable [Fintype Rand] [Nonempty Rand]

omit [DecidableEq W] [DecidableEq Ct] in
/-- The epoch counters after a call of `smSchemeOracle` are `ckaShadowStep` of the counters
before it. -/
theorem smSchemeOracle_shadow (M : SMScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS t : ℕ)
    (ideal : Bool) (s : SMSchemeSt St Pub) (q : SMQuery W) :
    ∀ y ∈ (smSchemeOracle M ΔFS ΔPCS t ideal s q).support,
      ckaShadow y.2.ck = ckaShadowStep (ckaShadow s.ck) q := by
  intro y hy
  cases q <;> simp only [smSchemeOracle] at hy <;> split_ifs at hy <;> (try split at hy) <;>
    simp only [PMF.support_bind, PMF.support_pure, PMF.support_uniformFintype, Set.mem_iUnion,
      Set.mem_singleton_iff, exists_prop] at hy <;>
    grind [ckaShadowStep, ckaShadow, SMSchemeSt.upd, ckaShadow_sent, ckaShadow_recvd,
      ckaShadow_canSend, ckaShadow_canRecv]

/-- **The simulator is the oracle with decryption from the log.** Each call of the oracle of
the authenticity game with ideal decryption, mapped to the states of the reduction and of the
corruption game, is the call of `smAuthImpl` against `smSchemeOracle`. -/
theorem smAuth_step (M : SMAuthScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS t : ℕ) (idealC : Bool)
    (s : SMSchemeSt St Pub × SMAuthAux W Ct) (d : SMAuthQuery W Ct) :
    (smAuthOracle M ΔFS ΔPCS t idealC true s d).map (Prod.map id smAuthEmb) =
      OracleAdv.simOracle (smAuthImpl ΔFS ΔPCS) (smSchemeOracle M.toSMScheme ΔFS ΔPCS t idealC)
        (smAuthEmb s) d := by
  cases d with
  | sm q =>
    simp only [smAuthOracle, OracleAdv.simOracle, smAuthImpl, smAuthEmb, OracleAdv.run_query,
      OracleAdv.run_ret, PMF.map_comp, PMF.map_bind, PMF.pure_map]
    exact PMF.bind_congr_support _ _ _ fun y hy => by
      simp [smAuthEmb, smSchemeOracle_shadow _ _ _ _ _ _ _ y hy]
  | deliver p j ad c =>
    simp [smAuthOracle, OracleAdv.simOracle, smAuthImpl, smAuthEmb, PMF.pure_map]

/-- **The game with ideal decryption is the corruption game of the reduction.** -/
theorem smAuthGame_logDec_eq (M : SMAuthScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS : ℕ)
    (idealC : Bool) (A : SMAuthAdv Pub W Ct Leak) :
    smAuthGame M ΔFS ΔPCS idealC true A =
      smCorruptGame M.toSMScheme ΔFS ΔPCS idealC (smAuthRed ΔFS ΔPCS A) := by
  unfold smAuthGame smCorruptGame
  refine congrArg _ (funext fun t => congrArg _ (funext fun i => congrArg _ ?_))
  simp only [smAuthRed]
  rw [OracleAdv.run_simulate_fst]
  have he : smAuthEmb ((SMSchemeSt.init i : SMSchemeSt St Pub), (SMAuthAux.init : SMAuthAux W Ct))
      = ((CKAGameSt.init () () (), SMAuthAux.init), SMSchemeSt.init i) := by
    simp only [smAuthEmb, SMSchemeSt.init, ckaShadow_init]
  rw [← he, ← OracleAdv.run_map_state _ _ smAuthEmb (smAuth_step M ΔFS ΔPCS t idealC),
    PMF.map_comp]
  rfl

/-- **Authenticity from integrity and the corruption game.** For every adversary `A`, the
advantage of `A` in the authenticity game over `M` is at most its integrity advantage plus the
corruption advantage of the reduction `smAuthRed ΔFS ΔPCS A`. -/
theorem SMAuthScheme.authAdvantage_le (M : SMAuthScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS : ℕ)
    (A : SMAuthAdv Pub W Ct Leak) :
    M.authAdvantage ΔFS ΔPCS A ≤
      M.intAdvantage ΔFS ΔPCS A + M.corruptAdvantage ΔFS ΔPCS (smAuthRed ΔFS ΔPCS A) := by
  unfold SMAuthScheme.authAdvantage SMAuthScheme.intAdvantage SMScheme.corruptAdvantage
  rw [← smAuthGame_logDec_eq, ← smAuthGame_logDec_eq]
  exact advantage_triangle _ _ _

end Red

/-! ## The ACD construction with decryption -/

section ACD

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [Fintype RK] [Nonempty RK]

/-- The key at the position `j` of the chain from the state `sa` of the chain generator `G`. -/
def chainKey (G : PRGDef Sa (W × Sa)) (sa : Sa) (j : ℕ) : W :=
  (G.stretch ((fun s => (G.stretch s).2)^[j] sa)).1

/-- **The ACD construction with decryption**: `acdSM C R G D` with the decryption of the
ciphertext at the position `j` under the key at the position `j` of the receiving chain. -/
noncomputable def acdAuthSM (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) :
    SMAuthScheme (SMPartySt Sc RK Sa) Msg Rand W Ct (SMPartySt Sc RK Sa) :=
  { toSMScheme := acdSM C R G D
    dec := fun x j ad c => x.rcv.bind fun sa => D.decrypt (chainKey G sa j) c ad }

variable [Fintype Key] [Nonempty Key] [Fintype Sa] [Nonempty Sa] [DecidableEq RK]
  [DecidableEq Key] [DecidableEq W] [DecidableEq Ct]

/-- **Authenticity of the ACD construction up to integrity.** For a CKA correct along `J` with
a sound explicit-randomness sending algorithm, and `2 ≤ ΔFS`, `1 ≤ ΔPCS`, the authenticity
advantage of every adversary `A` against `acdAuthSM C R G D` is at most its integrity advantage
plus the bound of `acdSM_corruptAdvantage_le` at the reduction `smAuthRed ΔFS ΔPCS A`: the CKA
corruption advantages, the PRF-PRNG advantages of `R` and the FS-AEAD advantage with
corruption of `G` and `D`, each at an explicit reduction. -/
theorem acdAuthSM_authAdvantage_le (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (hS : CKACoins.Sound C) {J : Sc → Sc → Prop} (hJ : CKACorrect C J)
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (hJi : ∀ i ∈ initP.support, J i.2.1 i.2.2) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS)
    (hPCS : 1 ≤ ΔPCS) (A : SMAuthAdv Msg W Ct (SMPartySt Sc RK Sa)) :
    (acdAuthSM C R G D).authAdvantage ΔFS ΔPCS A ≤
      (acdAuthSM C R G D).intAdvantage ΔFS ΔPCS A +
        (∑ b : Bool, CKA_Corrupt_Advantage C ΔFS ΔPCS
            (smcCKARed R G D b (smAuthRed ΔFS ΔPCS A).toSM) +
          ∑ b : Bool, PRFPRNG_Advantage R
            (smcRootRed C R G D ΔFS ΔPCS b initP (smAuthRed ΔFS ΔPCS A).toSM) +
          FSAEAD_Corrupt_Advantage G D
            (smcFSRed C R G D ΔFS ΔPCS initP (smAuthRed ΔFS ΔPCS A).toSM)) := by
  have h := acdSM_corruptAdvantage_le C hS hJ initP hinit hJi R G D hFS hPCS
    (smAuthRed ΔFS ΔPCS A)
  refine (SMAuthScheme.authAdvantage_le (acdAuthSM C R G D) ΔFS ΔPCS A).trans ?_
  exact add_le_add_right h _

end ACD

end CatCrypt.Crypto.Messaging
