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

## The hybrid over the epochs

`smAuthGameAt M ΔFS ΔPCS idealC idealD A` takes the decryption mode per epoch: a delivery into
the epoch `e` is answered from the log when `idealD e`. The hybrid `k` answers the deliveries
into the epochs below `k` from the log. Every query raises each epoch counter by at most one, so
for an adversary asking at most `N` queries every delivery is into an epoch below `N`
(`smAuthGameAt_congr_of_isQueryBound`), and (`SMAuthScheme.intAdvantage_le_sum`)

  `Adv_int(A) ≤ ∑_{k < N} Adv_int,k(A)`,

where `Adv_int,k` (`SMAuthScheme.epochIntAdvantage`) distinguishes the hybrids `k` and `k + 1`,
which differ only at the deliveries into the epoch `k`.

## Identical until a forgery

A forgery at the epoch `k` (`smAuthBadAt`) is an answered delivery into the epoch `k` whose
real decryption differs from the decryption from the log. The hybrids `k` and `k + 1` with a
flag set at a forgery (`smAuthFlagOracle`) agree on every transition that leaves the flag
cleared, so (`SMAuthScheme.epochIntAdvantage_le_bad`)

  `Adv_int,k(A) ≤ Pr[smAuthBadGame k A]`,

the probability of a forgery at the epoch `k` in the hybrid `k + 1`. The truncated game
`smAuthTruncGame` answers every query by a rejection from the first answered corruption with
the epoch `k` in its window on; it has the same output (`smAuthTruncGame_eq`), since after
such a corruption no delivery into the epoch `k` is answered.

## FS-AEAD integrity

`fsaead_int_game G D ideal A` is the integrity game of a single epoch of the chain generator `G`
and the AEAD `D`: encryption under the next key of the chain, with a log of the honest
ciphertexts; decryption at a position under the key of the chain from the initial state, or
from the log in the ideal game, refused after the corruption of the sender.
`FSAEAD_Int_Advantage` is the distance between the two games.

## Main definitions

* `SMAuthScheme`, `SMAuthQuery`, `SMAuthAns`, `SMLogEntry`, `SMAuthAux`, `smAuthOracleAt`,
  `smAuthOracle`, `SMAuthAdv`, `smAuthGameAt`, `smAuthGame`, `SMAuthScheme.authAdvantage`,
  `SMAuthScheme.intAdvantage`, `SMAuthScheme.epochIntAdvantage`
* `smAuthImpl`, `smAuthRed` — the reduction to the corruption game
* `smAuthBadAt`, `smAuthFlagOracle`, `smAuthFlagRun`, `smAuthBadGame`, `smAuthTruncOracle`,
  `smAuthTruncGame` — the forgery event at an epoch and its truncated game
* `chainKey`, `acdAuthSM` — the ACD construction with the decryption of the receiving chain
* `FSIntQuery`, `FSIntAns`, `FSIntSt`, `fsIntOracle`, `fsaead_int_game`,
  `FSAEAD_Int_Advantage` — the FS-AEAD integrity game

## Main results

* `smAuthGame_logDec_eq` — the game with ideal decryption is the corruption game of
  `smAuthRed`
* `SMAuthScheme.authAdvantage_le`, `acdAuthSM_authAdvantage_le` — the bounds above
* `OracleAdv.run_eq_of_agree_level` — runs of oracles that agree below a level of a graded
  invariant, for an adversary with a query bound
* `SMAuthScheme.intAdvantage_le_sum` — the integrity advantage as a sum over the epochs
* `OracleAdv.run_map_eq_of_agree_until_stop` — runs of oracles that agree until a stop after
  which both keep an observation
* `advantage_bind_liftPMF_le_flag` — identical until a flag, through a shared prefix
* `SMAuthScheme.epochIntAdvantage_le_bad`, `smAuthTruncGame_eq` — the bounds above
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.OracleAdv

variable {S D R α : Type}

/-- **Runs of oracles that agree below a level.** Let `L c` be state predicates such that every
call of `O` from a state of `L c` leads to states of `L (c + 1)`, and let `O` and `O'` agree at
the states of `L c` for `c < n`. A run of an adversary asking at most `m` queries from a state
of `L c` with `c + m ≤ n` is the same under both oracles. -/
theorem run_eq_of_agree_level (O O' : S → D → PMF (R × S)) (L : ℕ → S → Prop) (n : ℕ)
    (hO : ∀ c s d, L c s → ∀ x ∈ (O s d).support, L (c + 1) x.2)
    (hagree : ∀ c s d, c < n → L c s → O s d = O' s d) {A : OracleAdv D R α} {m : ℕ}
    (hA : A.IsQueryBound m) (c : ℕ) (s : S) (hs : L c s) (hcm : c + m ≤ n) :
    run O A s = run O' A s := by
  induction A generalizing m c s with
  | ret a => simp only [run_ret]
  | rand p k ih =>
    simp only [run_rand]
    exact congrArg _ (funext fun b => ih b (hA b) c s hs hcm)
  | query d k ih =>
    cases m with
    | zero => exact hA.elim
    | succ m =>
      rw [run_query, run_query, ← hagree c s d (by omega) hs]
      exact PMF.bind_congr_support _ _ _ fun y hy =>
        ih y.1 (hA y.1) (c + 1) y.2 (hO c s d hs y hy) (by omega)

/-- **A frozen observation.** Let every call of `O` from a state of `Fr` lead to states of `Fr`
with the same value of `g`. A run from a state of `Fr` ends with that value of `g`. -/
theorem run_map_eq_pure_of_frozen {β : Type} (O : S → D → PMF (R × S)) (Fr : S → Prop)
    (g : S → β) (hO : ∀ s d, Fr s → ∀ x ∈ (O s d).support, Fr x.2 ∧ g x.2 = g s)
    (A : OracleAdv D R α) (s : S) (hs : Fr s) :
    (run O A s).map (fun x => g x.2) = PMF.pure (g s) := by
  induction A generalizing s with
  | ret a => simp only [run_ret, PMF.pure_map]
  | rand p k ih => simp only [run_rand, PMF.map_bind, fun b => ih b s hs, PMF.bind_const]
  | query d k ih =>
    rw [run_query, PMF.map_bind, PMF.bind_congr_support _ _ (fun _ => PMF.pure (g s))
      fun y hy => by rw [ih y.1 y.2 (hO s d hs y hy).1, (hO s d hs y hy).2]]
    exact PMF.bind_const _ _

/-- **Runs that agree until a stop.** Let `O` and `O'` agree at the states outside `Stop`, and
let every call of either from a state of `Stop` lead to states of `Stop` with the same value of
`g`. The runs of an adversary against `O` and `O'` give the same distribution of the final value
of `g`. -/
theorem run_map_eq_of_agree_until_stop {β : Type} (O O' : S → D → PMF (R × S))
    (Stop : S → Prop) (g : S → β) (hagree : ∀ s d, ¬ Stop s → O s d = O' s d)
    (hO : ∀ s d, Stop s → ∀ x ∈ (O s d).support, Stop x.2 ∧ g x.2 = g s)
    (hO' : ∀ s d, Stop s → ∀ x ∈ (O' s d).support, Stop x.2 ∧ g x.2 = g s)
    (A : OracleAdv D R α) (s : S) :
    (run O A s).map (fun x => g x.2) = (run O' A s).map (fun x => g x.2) := by
  induction A generalizing s with
  | ret a => rfl
  | rand p k ih => simp only [run_rand, PMF.map_bind, fun b => ih b s]
  | query d k ih =>
    by_cases hs : Stop s
    · rw [run_map_eq_pure_of_frozen O Stop g hO _ s hs,
        run_map_eq_pure_of_frozen O' Stop g hO' _ s hs]
    · rw [run_query, run_query, PMF.map_bind, PMF.map_bind, hagree s d hs]
      exact congrArg _ (funext fun y => ih y.1 y.2)

end CatCrypt.Crypto.OracleAdv

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

/-- The oracle of the authenticity game over `M` with the challenge epoch `t` and the
decryption mode `idealD` per epoch: the queries of the corruption game are answered by
`smSchemeOracle` with the challenge mode `idealC` and logged; a delivery into the epoch `e` is
answered by `M.dec` (`idealD e = false`) or from the log, and only when
`SMAuthAux.canDeliver` allows it. -/
noncomputable def smAuthOracleAt (M : SMAuthScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS t : ℕ)
    (idealC : Bool) (idealD : ℕ → Bool) (s : SMSchemeSt St Pub × SMAuthAux W Ct) :
    SMAuthQuery W Ct → PMF (SMAuthAns Pub Ct Leak W × (SMSchemeSt St Pub × SMAuthAux W Ct))
  | .sm q => (smSchemeOracle M.toSMScheme ΔFS ΔPCS t idealC s.1 q).map fun y =>
      (.sm y.1, (y.2, s.2.upd (ckaShadow s.1.ck) q y.1))
  | .deliver p j ad c => PMF.pure (.dec (if idealD ((ckaShadow s.1.ck).t p) then
      s.2.logAns ΔFS ΔPCS (ckaShadow s.1.ck) p j ad c
    else if s.2.canDeliver ΔFS ΔPCS (ckaShadow s.1.ck) p then M.dec (s.1.ck.st p) j ad c
    else none), s)

/-- The oracle of the authenticity game over `M` with the challenge epoch `t`: `smAuthOracleAt`
with the same decryption mode `idealD` in every epoch. -/
noncomputable def smAuthOracle (M : SMAuthScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS t : ℕ)
    (idealC idealD : Bool) (s : SMSchemeSt St Pub × SMAuthAux W Ct) :
    SMAuthQuery W Ct → PMF (SMAuthAns Pub Ct Leak W × (SMSchemeSt St Pub × SMAuthAux W Ct)) :=
  smAuthOracleAt M ΔFS ΔPCS t idealC (fun _ => idealD) s

/-- An adversary of the authenticity game: a distribution of the challenge epoch, and for each
challenge epoch and public value of the initialisation an oracle tree. -/
structure SMAuthAdv (Pub W Ct Leak : Type) : Type 1 where
  /-- The choice of the challenge epoch. -/
  tStar : PMF ℕ
  /-- The interaction with the oracles. -/
  play : ℕ → Pub → OracleAdv (SMAuthQuery W Ct) (SMAuthAns Pub Ct Leak W) Bool

/-- The authenticity game over a scheme with the decryption mode `idealD` per epoch: the
adversary chooses the challenge epoch `t`, the scheme is initialised, and the adversary
interacts with `smAuthOracleAt`. -/
noncomputable def smAuthGameAt (M : SMAuthScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS : ℕ)
    (idealC : Bool) (idealD : ℕ → Bool) (A : SMAuthAdv Pub W Ct Leak) : SPComp Bool :=
  SPComp.bind (liftPMF A.tStar) fun t =>
    SPComp.bind M.init fun i =>
      liftPMF ((OracleAdv.run (smAuthOracleAt M ΔFS ΔPCS t idealC idealD) (A.play t i.1)
        (SMSchemeSt.init i, SMAuthAux.init)).map Prod.fst)

/-- **The authenticity game over a scheme**: the adversary chooses the challenge epoch `t`, the
scheme is initialised, and the adversary interacts with `smAuthOracle`. -/
noncomputable def smAuthGame (M : SMAuthScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS : ℕ)
    (idealC idealD : Bool) (A : SMAuthAdv Pub W Ct Leak) : SPComp Bool :=
  smAuthGameAt M ΔFS ΔPCS idealC (fun _ => idealD) A

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
    simp only [smAuthOracle, smAuthOracleAt, OracleAdv.simOracle, smAuthImpl, smAuthEmb,
      OracleAdv.run_query,
      OracleAdv.run_ret, PMF.map_comp, PMF.map_bind, PMF.pure_map]
    exact PMF.bind_congr_support _ _ _ fun y hy => by
      simp [smAuthEmb, smSchemeOracle_shadow _ _ _ _ _ _ _ y hy]
  | deliver p j ad c =>
    simp [smAuthOracle, smAuthOracleAt, OracleAdv.simOracle, smAuthImpl, smAuthEmb,
      PMF.pure_map]

/-- **The game with ideal decryption is the corruption game of the reduction.** -/
theorem smAuthGame_logDec_eq (M : SMAuthScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS : ℕ)
    (idealC : Bool) (A : SMAuthAdv Pub W Ct Leak) :
    smAuthGame M ΔFS ΔPCS idealC true A =
      smCorruptGame M.toSMScheme ΔFS ΔPCS idealC (smAuthRed ΔFS ΔPCS A) := by
  unfold smAuthGame smAuthGameAt smCorruptGame
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

/-! ## The hybrid over the epochs -/

section Hybrid

variable {St Pub Rand W Ct Leak : Type} [Fintype Rand] [Nonempty Rand] [DecidableEq W]
  [DecidableEq Ct]

/-- The epoch counters of the state `s` of the authenticity game are at most `c`. -/
def smAuthLevel (c : ℕ) (s : SMSchemeSt St Pub × SMAuthAux W Ct) : Prop := ∀ p, s.1.ck.t p ≤ c

omit [DecidableEq W] in
/-- A query of the corruption game raises each epoch counter by at most one. -/
theorem ckaShadowStep_t_le (sh : CKAGameSt Unit Unit) (q : SMQuery W) (p : CKAParty) :
    (ckaShadowStep sh q).t p ≤ sh.t p + 1 := by
  cases q <;> simp only [ckaShadowStep] <;> (try split) <;>
    (try simp only [CKAGameSt.sent, CKAGameSt.recvd]) <;> grind [Function.update_apply]

/-- A call of the oracle of the authenticity game raises each epoch counter by at most one. -/
theorem smAuthOracleAt_level (M : SMAuthScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS t : ℕ)
    (idealC : Bool) (idealD : ℕ → Bool) (c : ℕ) (s : SMSchemeSt St Pub × SMAuthAux W Ct)
    (d : SMAuthQuery W Ct) (hs : smAuthLevel c s) :
    ∀ x ∈ (smAuthOracleAt M ΔFS ΔPCS t idealC idealD s d).support, smAuthLevel (c + 1) x.2 := by
  intro x hx p
  cases d with
  | sm q =>
    simp only [smAuthOracleAt, PMF.support_map, Set.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h := congrArg (fun z => z.t p)
      (smSchemeOracle_shadow M.toSMScheme ΔFS ΔPCS t idealC s.1 q y hy)
    have h' := ckaShadowStep_t_le (ckaShadow s.1.ck) q p
    have h'' := hs p
    simp only [ckaShadow] at h h'
    grind
  | deliver p' j ad c' =>
    simp only [smAuthOracleAt, PMF.support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact (hs p).trans (Nat.le_succ _)

/-- **Decryption modes that agree below the horizon.** For an adversary asking at most `N`
queries, every delivery is into an epoch below `N`, so two decryption modes that agree on the
epochs below `N` give the same game. -/
theorem smAuthGameAt_congr_of_isQueryBound (M : SMAuthScheme St Pub Rand W Ct Leak)
    (ΔFS ΔPCS : ℕ) (idealC : Bool) {idealD idealD' : ℕ → Bool} {N : ℕ}
    (h : ∀ e < N, idealD e = idealD' e) (A : SMAuthAdv Pub W Ct Leak)
    (hA : ∀ t pub, (A.play t pub).IsQueryBound N) :
    smAuthGameAt M ΔFS ΔPCS idealC idealD A = smAuthGameAt M ΔFS ΔPCS idealC idealD' A := by
  unfold smAuthGameAt
  refine congrArg _ (funext fun t => congrArg _ (funext fun i => congrArg _ ?_))
  rw [OracleAdv.run_eq_of_agree_level _ (smAuthOracleAt M ΔFS ΔPCS t idealC idealD')
    smAuthLevel N (smAuthOracleAt_level M ΔFS ΔPCS t idealC idealD) ?_ (hA t i.1) 0 _ ?_
    (by omega)]
  · intro c s d hc hs
    cases d with
    | sm q => rfl
    | deliver p j ad c' =>
      have hp := hs p
      simp only [smAuthOracleAt]
      rw [h ((ckaShadow s.1.ck).t p) (by simp only [ckaShadow]; omega)]
  · intro p
    simp [SMSchemeSt.init, CKAGameSt.init]

/-- **The integrity advantage at the epoch `k`**: the game with decryption from the log in the
epochs below `k` and real decryption from the epoch `k` on, against the game with decryption
from the log in the epochs up to `k`. -/
noncomputable def SMAuthScheme.epochIntAdvantage (M : SMAuthScheme St Pub Rand W Ct Leak)
    (ΔFS ΔPCS k : ℕ) (A : SMAuthAdv Pub W Ct Leak) : ℝ≥0∞ :=
  Advantage (smAuthGameAt M ΔFS ΔPCS false (fun e => decide (e < k)) A)
    (smAuthGameAt M ΔFS ΔPCS false (fun e => decide (e < k + 1)) A)

/-- **Integrity as a sum over the epochs.** For an adversary asking at most `N` queries, the
integrity advantage is at most the sum over the epochs `k < N` of the integrity advantages at
the epoch `k`. -/
theorem SMAuthScheme.intAdvantage_le_sum (M : SMAuthScheme St Pub Rand W Ct Leak)
    (ΔFS ΔPCS N : ℕ) (A : SMAuthAdv Pub W Ct Leak)
    (hA : ∀ t pub, (A.play t pub).IsQueryBound N) :
    M.intAdvantage ΔFS ΔPCS A ≤
      ∑ k ∈ Finset.range N, M.epochIntAdvantage ΔFS ΔPCS k A := by
  have h0 : smAuthGame M ΔFS ΔPCS false false A =
      smAuthGameAt M ΔFS ΔPCS false (fun e => decide (e < 0)) A := by
    simp only [smAuthGame, Nat.not_lt_zero, decide_false]
  have hN : smAuthGame M ΔFS ΔPCS false true A =
      smAuthGameAt M ΔFS ΔPCS false (fun e => decide (e < N)) A :=
    smAuthGameAt_congr_of_isQueryBound M ΔFS ΔPCS false (fun e he => by simp [he]) A hA
  unfold SMAuthScheme.intAdvantage SMAuthScheme.epochIntAdvantage
  rw [h0, hN]
  exact HybridArgument.advantage_hybrid_dep_bool
    (fun k => smAuthGameAt M ΔFS ΔPCS false (fun e => decide (e < k)) A) N

end Hybrid

/-! ## Identical until a forgery at the epoch `k` -/

section UntilBad

/-- **Identical until a flag, through a shared prefix.** Let the flagged distributions `p₁ t i`
and `p₂ t i` agree on every outcome with the flag cleared. The games that draw `t` from `T` and
`i` from `I` and output the first component of `p₁ t i` and of `p₂ t i` are distinguished with
at most the probability of the flag in the second game. -/
theorem advantage_bind_liftPMF_le_flag {τ X σ : Type} (T : PMF τ) (I : SPComp X)
    (p₁ p₂ : τ → X → PMF (Bool × σ × Bool))
    (h : ∀ t i a s, p₁ t i (a, (s, false)) = p₂ t i (a, (s, false))) :
    Advantage
        (SPComp.bind (liftPMF T) fun t => SPComp.bind I fun i => liftPMF ((p₁ t i).map Prod.fst))
        (SPComp.bind (liftPMF T) fun t => SPComp.bind I fun i => liftPMF ((p₂ t i).map Prod.fst))
      ≤ prTrue (SPComp.bind (liftPMF T) fun t => SPComp.bind I fun i =>
          liftPMF ((p₂ t i).map fun x => x.2.2)) Heap.empty := by
  have h₁ : prTrue (SPComp.bind (liftPMF T) fun t => SPComp.bind I fun i =>
      liftPMF ((p₁ t i).map Prod.fst)) Heap.empty ≤
      prTrue (SPComp.bind (liftPMF T) fun t => SPComp.bind I fun i =>
        liftPMF ((p₂ t i).map Prod.fst)) Heap.empty +
      prTrue (SPComp.bind (liftPMF T) fun t => SPComp.bind I fun i =>
        liftPMF ((p₂ t i).map fun x => x.2.2)) Heap.empty := by
    refine ForkingLemma.prTrue_bind_le_add _ _ _ _ _ fun t _ => ?_
    refine ForkingLemma.prTrue_bind_le_add _ _ _ _ _ fun i _ => ?_
    simp only [PRPPRF.prTrue_liftPMF_map]
    simpa only [Set.mem_singleton_iff] using
      Constructions.ECBCPRF.toOuterMeasure_le_add_flag (p₁ t i) (p₂ t i) (h t i) {true}
  have h₂ : prTrue (SPComp.bind (liftPMF T) fun t => SPComp.bind I fun i =>
      liftPMF ((p₂ t i).map Prod.fst)) Heap.empty ≤
      prTrue (SPComp.bind (liftPMF T) fun t => SPComp.bind I fun i =>
        liftPMF ((p₁ t i).map Prod.fst)) Heap.empty +
      prTrue (SPComp.bind (liftPMF T) fun t => SPComp.bind I fun i =>
        liftPMF ((p₂ t i).map fun x => x.2.2)) Heap.empty := by
    refine ForkingLemma.prTrue_bind_le_add _ _ _ _ _ fun t _ => ?_
    refine ForkingLemma.prTrue_bind_le_add _ _ _ _ _ fun i _ => ?_
    simp only [PRPPRF.prTrue_liftPMF_map]
    rw [← Constructions.ECBCPRF.toOuterMeasure_flag_eq (p₁ t i) (p₂ t i) (h t i)]
    simpa only [Set.mem_singleton_iff] using
      Constructions.ECBCPRF.toOuterMeasure_le_add_flag (p₂ t i) (p₁ t i)
        (fun a s => (h t i a s).symm) {true}
  exact max_le (tsub_le_iff_left.mpr h₁) (tsub_le_iff_left.mpr h₂)

variable {St Pub Rand W Ct Leak : Type} [Fintype Rand] [Nonempty Rand] [DecidableEq W]
  [DecidableEq Ct]

/-- **A forgery at the epoch `k`**: the query `d` from the state `s` is a delivery into the
epoch `k` that is answered and whose real decryption differs from the decryption from the
log. -/
def smAuthBadAt (M : SMAuthScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS k : ℕ)
    (s : SMSchemeSt St Pub × SMAuthAux W Ct) : SMAuthQuery W Ct → Bool
  | .sm _ => false
  | .deliver p j ad c => decide ((ckaShadow s.1.ck).t p = k) &&
      s.2.canDeliver ΔFS ΔPCS (ckaShadow s.1.ck) p &&
      (M.dec (s.1.ck.st p) j ad c != s.2.logDec ((ckaShadow s.1.ck).t p) j ad c)

/-- The oracle `smAuthOracleAt` with a flag that is set at a forgery at the epoch `k`. -/
noncomputable def smAuthFlagOracle (M : SMAuthScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS t : ℕ)
    (idealC : Bool) (idealD : ℕ → Bool) (k : ℕ)
    (s : (SMSchemeSt St Pub × SMAuthAux W Ct) × Bool) (d : SMAuthQuery W Ct) :
    PMF (SMAuthAns Pub Ct Leak W × ((SMSchemeSt St Pub × SMAuthAux W Ct) × Bool)) :=
  (smAuthOracleAt M ΔFS ΔPCS t idealC idealD s.1 d).map fun y =>
    (y.1, (y.2, s.2 || smAuthBadAt M ΔFS ΔPCS k s.1 d))

/-- The run of `A` against the flagged oracle `smAuthFlagOracle` at the challenge epoch `t`
from the initial state `i` of the scheme. -/
noncomputable def smAuthFlagRun (M : SMAuthScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS : ℕ)
    (idealC : Bool) (idealD : ℕ → Bool) (k : ℕ) (A : SMAuthAdv Pub W Ct Leak) (t : ℕ)
    (i : Pub × St × St) :
    PMF (Bool × ((SMSchemeSt St Pub × SMAuthAux W Ct) × Bool)) :=
  OracleAdv.run (smAuthFlagOracle M ΔFS ΔPCS t idealC idealD k) (A.play t i.1)
    ((SMSchemeSt.init i, SMAuthAux.init), false)

/-- **The forgery event at the epoch `k`**: the game that runs `A` in the hybrid `k + 1` and
outputs whether a forgery at the epoch `k` was delivered. -/
noncomputable def smAuthBadGame (M : SMAuthScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS k : ℕ)
    (A : SMAuthAdv Pub W Ct Leak) : SPComp Bool :=
  SPComp.bind (liftPMF A.tStar) fun t => SPComp.bind M.init fun i =>
    liftPMF ((smAuthFlagRun M ΔFS ΔPCS false (fun e => decide (e < k + 1)) k A t i).map
      fun x => x.2.2)

/-- The output of the flagged run is the output of the run against `smAuthOracleAt`. -/
theorem smAuthFlagRun_map_fst (M : SMAuthScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS : ℕ)
    (idealC : Bool) (idealD : ℕ → Bool) (k : ℕ) (A : SMAuthAdv Pub W Ct Leak) (t : ℕ)
    (i : Pub × St × St) :
    (smAuthFlagRun M ΔFS ΔPCS idealC idealD k A t i).map Prod.fst =
      (OracleAdv.run (smAuthOracleAt M ΔFS ΔPCS t idealC idealD) (A.play t i.1)
        (SMSchemeSt.init i, SMAuthAux.init)).map Prod.fst := by
  have hstep : ∀ s d, (smAuthFlagOracle M ΔFS ΔPCS t idealC idealD k s d).map
      (Prod.map id Prod.fst) = smAuthOracleAt M ΔFS ΔPCS t idealC idealD s.1 d := by
    intro s d
    rw [smAuthFlagOracle, PMF.map_comp]
    exact PMF.map_id _
  have h := OracleAdv.run_map_state _ _ Prod.fst hstep (A.play t i.1)
    ((SMSchemeSt.init i, SMAuthAux.init), false)
  dsimp only at h
  rw [smAuthFlagRun, ← h, PMF.map_comp]
  rfl

/-- Without a forgery at the epoch `k`, the hybrids `k` and `k + 1` answer a delivery alike. -/
theorem smAuthOracleAt_deliver_agree (M : SMAuthScheme St Pub Rand W Ct Leak)
    (ΔFS ΔPCS t : ℕ) (idealC : Bool) (k : ℕ) (s : SMSchemeSt St Pub × SMAuthAux W Ct)
    (p : CKAParty) (j : ℕ) (ad : W) (c : Ct)
    (h : smAuthBadAt M ΔFS ΔPCS k s (.deliver p j ad c) = false) :
    smAuthOracleAt M ΔFS ΔPCS t idealC (fun e => decide (e < k)) s (.deliver p j ad c) =
      smAuthOracleAt M ΔFS ΔPCS t idealC (fun e => decide (e < k + 1)) s
        (.deliver p j ad c) := by
  simp only [smAuthBadAt] at h
  simp only [smAuthOracleAt]
  grind [SMAuthAux.logAns]

/-- The flag of `smAuthFlagOracle` stays set. -/
theorem smAuthFlagOracle_sticky (M : SMAuthScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS t : ℕ)
    (idealC : Bool) (idealD : ℕ → Bool) (k : ℕ) (s : SMSchemeSt St Pub × SMAuthAux W Ct)
    (d : SMAuthQuery W Ct) (r : SMAuthAns Pub Ct Leak W)
    (s' : SMSchemeSt St Pub × SMAuthAux W Ct) :
    smAuthFlagOracle M ΔFS ΔPCS t idealC idealD k (s, true) d (r, (s', false)) = 0 := by
  refine (PMF.apply_eq_zero_iff _ _).mpr ?_
  simp [smAuthFlagOracle]

/-- The flagged hybrids `k` and `k + 1` agree on every transition that leaves the flag
cleared. -/
theorem smAuthFlagOracle_agree (M : SMAuthScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS t : ℕ)
    (idealC : Bool) (k : ℕ) (s : (SMSchemeSt St Pub × SMAuthAux W Ct) × Bool)
    (d : SMAuthQuery W Ct) (r : SMAuthAns Pub Ct Leak W)
    (s' : SMSchemeSt St Pub × SMAuthAux W Ct) :
    smAuthFlagOracle M ΔFS ΔPCS t idealC (fun e => decide (e < k)) k s d (r, (s', false)) =
      smAuthFlagOracle M ΔFS ΔPCS t idealC (fun e => decide (e < k + 1)) k s d
        (r, (s', false)) := by
  by_cases hb : (s.2 || smAuthBadAt M ΔFS ΔPCS k s.1 d) = true
  · rw [(PMF.apply_eq_zero_iff _ _).mpr, (PMF.apply_eq_zero_iff _ _).mpr] <;>
      simp [smAuthFlagOracle, hb]
  · cases d with
    | sm q => rfl
    | deliver p j ad c =>
      simp only [Bool.or_eq_true, not_or] at hb
      simp only [smAuthFlagOracle]
      rw [smAuthOracleAt_deliver_agree M ΔFS ΔPCS t idealC k s.1 p j ad c (by simpa using hb.2)]

/-- **Identical until a forgery.** The integrity advantage at the epoch `k` is at most the
probability of a forgery at the epoch `k` in the hybrid `k + 1`. -/
theorem SMAuthScheme.epochIntAdvantage_le_bad (M : SMAuthScheme St Pub Rand W Ct Leak)
    (ΔFS ΔPCS k : ℕ) (A : SMAuthAdv Pub W Ct Leak) :
    M.epochIntAdvantage ΔFS ΔPCS k A ≤ prTrue (smAuthBadGame M ΔFS ΔPCS k A) Heap.empty := by
  have hg : ∀ idealD, smAuthGameAt M ΔFS ΔPCS false idealD A =
      SPComp.bind (liftPMF A.tStar) fun t => SPComp.bind M.init fun i =>
        liftPMF ((smAuthFlagRun M ΔFS ΔPCS false idealD k A t i).map Prod.fst) := by
    intro idealD
    simp only [smAuthGameAt, smAuthFlagRun_map_fst]
  unfold SMAuthScheme.epochIntAdvantage smAuthBadGame
  rw [hg, hg]
  exact advantage_bind_liftPMF_le_flag _ _
    (fun t i => smAuthFlagRun M ΔFS ΔPCS false (fun e => decide (e < k)) k A t i)
    (fun t i => smAuthFlagRun M ΔFS ΔPCS false (fun e => decide (e < k + 1)) k A t i)
    fun t i a s => OracleAdv.run_apply_flag_false_eq _ _
      (smAuthFlagOracle_sticky M ΔFS ΔPCS t false _ k)
      (smAuthFlagOracle_sticky M ΔFS ΔPCS t false _ k)
      (smAuthFlagOracle_agree M ΔFS ΔPCS t false k) _ _ a s

omit [DecidableEq W] [DecidableEq Ct] in
/-- An epoch outside the safe epochs stays outside them. -/
theorem SMAuthAux.safe_upd_of_false (ΔFS ΔPCS k : ℕ) (x : SMAuthAux W Ct)
    (sh : CKAGameSt Unit Unit) (q : SMQuery W) (a : SMSchemeAns Pub Ct Leak)
    (h : x.safe ΔFS ΔPCS k = false) : (x.upd sh q a).safe ΔFS ΔPCS k = false := by
  cases q <;> cases a <;> simp_all [SMAuthAux.upd, SMAuthAux.record, SMAuthAux.safe]

/-- **The oracle truncated at the corruption of the epoch `k`**: the flagged oracle, which from
the first answered corruption with the epoch `k` in its window on answers every query by a
rejection and keeps its state. -/
noncomputable def smAuthTruncOracle (M : SMAuthScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS t : ℕ)
    (idealC : Bool) (idealD : ℕ → Bool) (k : ℕ)
    (s : (SMSchemeSt St Pub × SMAuthAux W Ct) × Bool) (d : SMAuthQuery W Ct) :
    PMF (SMAuthAns Pub Ct Leak W × ((SMSchemeSt St Pub × SMAuthAux W Ct) × Bool)) :=
  if s.1.2.safe ΔFS ΔPCS k then smAuthFlagOracle M ΔFS ΔPCS t idealC idealD k s d
  else PMF.pure (.dec none, s)

/-- **The truncated forgery game at the epoch `k`**: `smAuthBadGame` with the oracle truncated
at the first corruption that falls in the window of the epoch `k`. -/
noncomputable def smAuthTruncGame (M : SMAuthScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS k : ℕ)
    (A : SMAuthAdv Pub W Ct Leak) : SPComp Bool :=
  SPComp.bind (liftPMF A.tStar) fun t => SPComp.bind M.init fun i =>
    liftPMF ((OracleAdv.run
      (smAuthTruncOracle M ΔFS ΔPCS t false (fun e => decide (e < k + 1)) k) (A.play t i.1)
      ((SMSchemeSt.init i, SMAuthAux.init), false)).map fun x => x.2.2)

/-- After a corruption in the window of the epoch `k`, the flagged oracle keeps the flag and
the epoch outside the safe epochs. -/
theorem smAuthFlagOracle_stopped (M : SMAuthScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS t : ℕ)
    (idealC : Bool) (idealD : ℕ → Bool) (k : ℕ)
    (s : (SMSchemeSt St Pub × SMAuthAux W Ct) × Bool) (hs : s.1.2.safe ΔFS ΔPCS k = false)
    (d : SMAuthQuery W Ct) :
    ∀ x ∈ (smAuthFlagOracle M ΔFS ΔPCS t idealC idealD k s d).support,
      x.2.1.2.safe ΔFS ΔPCS k = false ∧ x.2.2 = s.2 := by
  intro x hx
  simp only [smAuthFlagOracle, PMF.support_map, Set.mem_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  cases d with
  | sm q =>
    simp only [smAuthOracleAt, PMF.support_map, Set.mem_image] at hy
    obtain ⟨z, -, rfl⟩ := hy
    exact ⟨SMAuthAux.safe_upd_of_false _ _ _ _ _ _ _ hs, by simp [smAuthBadAt]⟩
  | deliver p j ad c =>
    simp only [smAuthOracleAt, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    refine ⟨hs, ?_⟩
    simp only [smAuthBadAt, SMAuthAux.canDeliver]
    grind

/-- **Every forgery precedes the corruption of its epoch.** The truncated forgery game at the
epoch `k` is the forgery game at the epoch `k`: after a corruption in the window of the epoch
`k`, no delivery into the epoch `k` is answered. -/
theorem smAuthTruncGame_eq (M : SMAuthScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS k : ℕ)
    (A : SMAuthAdv Pub W Ct Leak) :
    smAuthTruncGame M ΔFS ΔPCS k A = smAuthBadGame M ΔFS ΔPCS k A := by
  unfold smAuthTruncGame smAuthBadGame smAuthFlagRun
  refine congrArg _ (funext fun t => congrArg _ (funext fun i => congrArg _ ?_))
  refine OracleAdv.run_map_eq_of_agree_until_stop _ _
    (fun s : (SMSchemeSt St Pub × SMAuthAux W Ct) × Bool => s.1.2.safe ΔFS ΔPCS k = false)
    (fun s => s.2) ?_ ?_ ?_ _ _
  · intro s d hs
    simp [smAuthTruncOracle, hs]
  · intro s d hs x hx
    simp only [smAuthTruncOracle, hs, Bool.false_eq_true, ite_false, PMF.support_pure,
      Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨hs, rfl⟩
  · exact fun s d hs => smAuthFlagOracle_stopped M ΔFS ΔPCS t false _ k s hs d

end UntilBad

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

/-! ## Forward-secure AEAD integrity -/

section FSInt

variable {Sa W Ct : Type} [SampleableType W] [SampleableType Ct] [DecidableEq W]
  [DecidableEq Ct]

/-- The queries of the FS-AEAD integrity adversary. -/
inductive FSIntQuery (W Ct : Type) where
  /-- The sender encrypts the message `m` under the next key of its chain. -/
  | enc (m : W × W)
  /-- The receiver decrypts the ciphertext `c` with associated data `ad` at the position `j`. -/
  | dec (j : ℕ) (ad : W) (c : Ct)
  /-- The state of the sender is returned; later decryptions are refused. -/
  | corrupt

/-- The answers of the FS-AEAD integrity oracle. -/
inductive FSIntAns (Sa Ct W : Type) where
  /-- A ciphertext. -/
  | ct (c : Ct)
  /-- A plaintext or a rejection. -/
  | dec (m : Option W)
  /-- The state of the sender. -/
  | state (s : Sa)

/-- The state of the FS-AEAD integrity game: the current state of the sender's chain, the
initial state of the epoch (the state of the receiver), the log of the honest ciphertexts
(position, plaintext, associated data, ciphertext) and the flag of the corruption. -/
structure FSIntSt (Sa W Ct : Type) where
  /-- The current state of the sender. -/
  cur : Sa
  /-- The initial state of the epoch, held by the receiver. -/
  init : Sa
  /-- The honest ciphertexts: position, plaintext, associated data, ciphertext. -/
  log : List (ℕ × W × W × Ct)
  /-- The sender has been corrupted. -/
  corr : Bool

omit [SampleableType W] [SampleableType Ct] in
/-- Decryption from the log of the FS-AEAD integrity game: the plaintext of the honest
ciphertext `c` with associated data `ad` at the position `j`, or `none`. -/
def FSIntSt.logDec (s : FSIntSt Sa W Ct) (j : ℕ) (ad : W) (c : Ct) : Option W :=
  (s.log.find? fun l => decide (l.1 = j ∧ l.2.2.1 = ad ∧ l.2.2.2 = c)).map fun l => l.2.1

/-- The oracle of the FS-AEAD integrity game of the generator `G` and the AEAD `D` (the
authenticity part of the FS-AEAD security of Alwen, Coretti and Dodis, §4.3, with immediate
decryption): `enc m` encrypts under the next key `(G cur).1`, logs the ciphertext at the next
position and moves the state to `(G cur).2`; `dec j ad c` decrypts under the key at the position
`j` of the chain from the initial state (`ideal = false`) or from the log (`ideal = true`), and
is refused after a corruption; `corrupt` returns the current state of the sender. -/
noncomputable def fsIntOracle (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (ideal : Bool)
    (s : FSIntSt Sa W Ct) : FSIntQuery W Ct → PMF (FSIntAns Sa Ct W × FSIntSt Sa W Ct)
  | .enc m =>
    PMF.pure (.ct (D.encrypt (G.stretch s.cur).1 m.1 m.2),
      { s with cur := (G.stretch s.cur).2,
               log := (s.log.length, m.1, m.2, D.encrypt (G.stretch s.cur).1 m.1 m.2) :: s.log })
  | .dec j ad c => PMF.pure (.dec (if s.corr then none
      else if ideal then s.logDec j ad c else D.decrypt (chainKey G s.init j) c ad), s)
  | .corrupt => PMF.pure (.state s.cur, { s with corr := true })

variable [Fintype Sa] [Nonempty Sa]

/-- **The FS-AEAD integrity game**: a uniform initial state of the epoch, and the run of the
adversary against `fsIntOracle`. -/
noncomputable def fsaead_int_game (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (ideal : Bool)
    (A : OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool) : SPComp Bool :=
  liftPMF ((PMF.uniformFintype Sa).bind fun sa =>
    (OracleAdv.run (fsIntOracle G D ideal) A ⟨sa, sa, [], false⟩).map Prod.fst)

/-- **FS-AEAD integrity advantage** of the adversary `A`: real decryption against decryption
from the log. -/
noncomputable def FSAEAD_Int_Advantage (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (A : OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool) : ℝ≥0∞ :=
  Advantage (fsaead_int_game G D false A) (fsaead_int_game G D true A)

end FSInt

end CatCrypt.Crypto.Messaging
