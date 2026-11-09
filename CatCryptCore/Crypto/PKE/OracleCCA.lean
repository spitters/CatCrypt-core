/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PKE.Games

/-!
# The IND-CCA game in oracle form

The IND-CCA game of a public-key scheme `P` in the oracle form of Bellare, Desai, Pointcheval and
Rogaway (CRYPTO 1998): the adversary is one `OracleAdv` over the queries `pk` (the public key),
`dec c` (decryption) and `chal m₀ m₁` (the challenge, answered once). The challenger samples the
key pair from `P.keygen` and the coins of the challenge encryption uniformly in advance; the
state of the oracle is the pair of challenge messages once the challenge has been asked, and a
decryption after the challenge refuses only the challenge ciphertext.

The adversary of the oracle game keeps its state across the challenge as the continuation of an
`OracleAdv`, which lives in `Type 1`. Every two-stage IND-CCA adversary `A`
(`INDCCAAdversary`, whose state passed across the challenge is a `Type`) is an oracle adversary
`indccaOracleReduction A.choose A.guess` with the same advantage, so the oracle game is at least
as strong as the two-stage game. The converse construction would pass the continuation of an
oracle adversary after its challenge query as the state of a two-stage adversary, which is not a
`Type`.

## Main definitions

* `INDCCAQuery`, `INDCCAAns` — queries and answers of the oracle game.
* `ccaOracle` — the oracle with challenge bit `b`, key pair `ks` and challenge coins `r`;
  `ccaDecOracle` — its decryption queries as an oracle on ciphertexts.
* `indccaOracleGame`, `indccaOracleAdvantage` — the game and its advantage.
* `decStage` — a stage of a two-stage adversary with each decryption query asked as `dec`.
* `indccaOracleReduction` — the stages of a two-stage IND-CCA adversary as an oracle adversary:
  it asks the public key, runs the first stage through `decStage`, asks the challenge on the
  two messages, and runs the second stage through `decStage` on the challenge ciphertext.

## Main results

* `indccaGame_eq_indccaOracleGame` —
  `indccaGame P A b = indccaOracleGame P (indccaOracleReduction A.choose A.guess) b`.
* `indccaAdvantage_eq_indccaOracleAdvantage` —
  `indccaAdvantage P A = indccaOracleAdvantage P (indccaOracleReduction A.choose A.guess)`.
* `isQueryBound_indccaOracleReduction` — the oracle adversary of a two-stage adversary with
  `q₁` and `q₂` decryption queries asks at most `q₁ + q₂ + 2` queries.

## References

* M. Bellare, A. Desai, D. Pointcheval, P. Rogaway, *Relations among notions of security for
  public-key encryption schemes*, CRYPTO 1998.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.PKE.Games

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

/-- Queries of the IND-CCA oracle game: the public key, a decryption, the challenge. -/
inductive INDCCAQuery (M C : Type)
  /-- The public key. -/
  | pk
  /-- Decryption of a ciphertext. -/
  | dec (c : C)
  /-- The challenge on two messages. -/
  | chal (m₀ m₁ : M)

/-- Answers of the IND-CCA oracle game. -/
inductive INDCCAAns (PK M C : Type)
  /-- A public key. -/
  | pk (p : PK)
  /-- A decryption result. -/
  | dec (o : Option M)
  /-- A ciphertext. -/
  | chal (c : C)
  /-- A refused query. -/
  | refused

/-- The decryption result an answer stands for: the result of a decryption answer, `none` for
every other answer. -/
def INDCCAAns.decOut {PK M C : Type} : INDCCAAns PK M C → Option M
  | .dec o => o
  | _ => none

variable {PK SK M C R : Type} (P : Scheme PK SK M C R)

/-- The challenge ciphertext of the logged challenge messages `m` under bit `b`, public key `pk`
and coins `r`. -/
def chalCt (b : Bool) (pk : PK) (r : R) (m : M × M) : C :=
  P.enc pk (if b then m.1 else m.2) r

/-! ## Two-stage adversaries as oracle adversaries -/

/-- A stage of a two-stage adversary as an adversary of the oracle game: each decryption query
`c` is asked as `dec c`, and each answer is read as its decryption result. -/
abbrev decStage {α : Type} (W : OracleAdv C (Option M) α) :
    OracleAdv (INDCCAQuery M C) (INDCCAAns PK M C) α :=
  W.mapQueryAnswer INDCCAQuery.dec INDCCAAns.decOut

/-- The second half of `indccaOracleReduction`: the challenge on the messages chosen by the first
stage, then the second stage on the challenge ciphertext. -/
def indccaOracleChal {St : Type} (guess : St → C → OracleAdv C (Option M) Bool)
    (x : M × M × St) : OracleAdv (INDCCAQuery M C) (INDCCAAns PK M C) Bool :=
  .query (.chal x.1 x.2.1) fun
    | .chal c => decStage (guess x.2.2 c)
    | _ => .ret false

/-- **A two-stage IND-CCA adversary as an oracle adversary.** For the stages `choose` and
`guess` of a two-stage adversary, it asks the public key, runs `choose` with each decryption
query asked as `dec`, asks the challenge on the two chosen messages, and runs `guess` on the
challenge ciphertext. -/
def indccaOracleReduction {St : Type} (choose : PK → OracleAdv C (Option M) (M × M × St))
    (guess : St → C → OracleAdv C (Option M) Bool) :
    OracleAdv (INDCCAQuery M C) (INDCCAAns PK M C) Bool :=
  .query .pk fun
    | .pk pk => (decStage (choose pk)).bind (indccaOracleChal guess)
    | _ => .ret false

/-- The oracle adversary of a two-stage adversary with `q₁` and `q₂` decryption queries asks at
most `q₁ + q₂ + 2` queries. -/
theorem isQueryBound_indccaOracleReduction {q₁ q₂ : ℕ} (A : INDCCAAdversary PK M C q₁ q₂) :
    (indccaOracleReduction A.choose A.guess).IsQueryBound (q₁ + q₂ + 2) := by
  rw [show q₁ + q₂ + 2 = q₁ + (q₂ + 1) + 1 by omega]
  intro a
  cases a with
  | pk pk =>
    refine OracleAdv.isQueryBound_bind
      (OracleAdv.isQueryBound_mapQueryAnswer _ _ (A.isQueryBound₁ pk)) fun x a => ?_
    cases a with
    | chal c => exact OracleAdv.isQueryBound_mapQueryAnswer _ _ (A.isQueryBound₂ _ _)
    | _ => trivial
  | _ => trivial

/-- The decryption oracle before the challenge, on the one-point state. -/
noncomputable def decOracle₀ (sk : SK) (_ : Unit) (c : C) : PMF (Option M × Unit) :=
  PMF.pure (P.dec sk c, ())

/-! ## The oracle game -/

variable [DecidableEq C]

/-- **The oracle of the IND-CCA game** with challenge bit `b`, key pair `ks` and challenge coins
`r`. The state is the pair of challenge messages once the challenge has been asked. The public
key is always answered; a decryption before the challenge is answered, after the challenge it
is refused on the challenge ciphertext only; the challenge is answered once. -/
noncomputable def ccaOracle (b : Bool) (ks : PK × SK) (r : R) :
    Option (M × M) → INDCCAQuery M C → PMF (INDCCAAns PK M C × Option (M × M))
  | s, .pk => PMF.pure (.pk ks.1, s)
  | none, .dec c => PMF.pure (.dec (P.dec ks.2 c), none)
  | some m, .dec c =>
    PMF.pure (if c = chalCt P b ks.1 r m then .refused else .dec (P.dec ks.2 c), some m)
  | none, .chal m₀ m₁ => PMF.pure (.chal (chalCt P b ks.1 r (m₀, m₁)), some (m₀, m₁))
  | some m, .chal _ _ => PMF.pure (.refused, some m)

/-- The decryption queries of a stage answered by `ccaOracle`: the query `dec c`, its answer
read as its decryption result. -/
noncomputable def ccaDecOracle (b : Bool) (ks : PK × SK) (r : R) (s : Option (M × M)) (c : C) :
    PMF (Option M × Option (M × M)) :=
  (ccaOracle P b ks r s (.dec c)).map fun x => (x.1.decOut, x.2)

/-- Answering decryption queries by `ccaOracle` from a state before the challenge is the
decryption oracle on the one-point state. -/
theorem run_ccaDecOracle_none {α : Type} (b : Bool) (ks : PK × SK) (r : R)
    (W : OracleAdv C (Option M) α) :
    (OracleAdv.run (decOracle₀ P ks.2) W ()).map (Prod.map id fun _ => none) =
      OracleAdv.run (ccaDecOracle P b ks r) W none :=
  OracleAdv.run_map_state _ _ _ (fun _ d => by
    simp [decOracle₀, ccaDecOracle, ccaOracle, INDCCAAns.decOut, PMF.pure_map]) W ()

/-- The stateful decryption oracle of `indccaGame` from the state before the challenge is the
decryption oracle on the one-point state. -/
theorem run_decOracle_none {α : Type} (sk : SK) (W : OracleAdv C (Option M) α) :
    (OracleAdv.run (decOracle₀ P sk) W ()).map (Prod.map id fun _ => none) =
      OracleAdv.run (decOracle P sk) W none :=
  OracleAdv.run_map_state _ _ _ (fun _ d => by
    simp [decOracle₀, decOracle, PMF.pure_map]) W ()

/-- Answering decryption queries by `ccaOracle`, with the logged messages read as the challenge
ciphertext, is the stateful decryption oracle of `indccaGame`. -/
theorem run_ccaDecOracle_map (b : Bool) (ks : PK × SK) (r : R) {α : Type}
    (W : OracleAdv C (Option M) α) (s : Option (M × M)) :
    (OracleAdv.run (ccaDecOracle P b ks r) W s).map
        (Prod.map id (Option.map (chalCt P b ks.1 r))) =
      OracleAdv.run (decOracle P ks.2) W (s.map (chalCt P b ks.1 r)) := by
  refine OracleAdv.run_map_state _ _ _ (fun s d => ?_) W s
  cases s with
  | none => simp [decOracle, ccaDecOracle, ccaOracle, INDCCAAns.decOut, PMF.pure_map]
  | some m =>
    by_cases h : d = chalCt P b ks.1 r m
    · simp [decOracle, ccaDecOracle, ccaOracle, INDCCAAns.decOut, PMF.pure_map, h]
    · simp [decOracle, ccaDecOracle, ccaOracle, INDCCAAns.decOut, PMF.pure_map, h, Ne.symm h]

/-- The run of the oracle adversary of the stages `choose`, `guess` against `ccaOracle` is the
run of `choose` against the decryption oracle, then the run of `guess` against the stateful
decryption oracle of `indccaGame` from the challenge ciphertext. -/
theorem run_indccaOracleReduction {St : Type} (choose : PK → OracleAdv C (Option M) (M × M × St))
    (guess : St → C → OracleAdv C (Option M) Bool) (b : Bool) (ks : PK × SK) (r : R) :
    (OracleAdv.run (ccaOracle P b ks r) (indccaOracleReduction choose guess) none).map
        Prod.fst =
      (OracleAdv.run (decOracle₀ P ks.2) (choose ks.1) ()).bind fun x =>
        (OracleAdv.run (decOracle P ks.2) (guess x.1.2.2 (chalCt P b ks.1 r (x.1.1, x.1.2.1)))
          (some (chalCt P b ks.1 r (x.1.1, x.1.2.1)))).map Prod.fst := by
  have hd : (fun s d => (ccaOracle P b ks r s (INDCCAQuery.dec d)).map
      fun x => (x.1.decOut, x.2)) = ccaDecOracle P b ks r := rfl
  simp only [indccaOracleReduction, OracleAdv.run_query, ccaOracle, PMF.pure_bind]
  simp only [decStage, OracleAdv.run_bind, OracleAdv.run_mapQueryAnswer, hd,
    ← run_ccaDecOracle_none P b ks r, PMF.bind_map, PMF.map_bind]
  refine congrArg (PMF.bind _) (funext fun x => ?_)
  have h := run_ccaDecOracle_map P b ks r
    (guess x.1.2.2 (chalCt P b ks.1 r (x.1.1, x.1.2.1))) (some (x.1.1, x.1.2.1))
  simp only [Option.map_some] at h
  simp only [Function.comp_apply, Prod.map, indccaOracleChal, OracleAdv.run_query, ccaOracle,
    PMF.pure_bind]
  simp only [decStage, OracleAdv.run_mapQueryAnswer, hd, ← h, PMF.map_comp]
  rfl

variable [Fintype R] [Nonempty R]

/-- **The IND-CCA oracle game** with challenge bit `b`: a key pair from `P.keygen`, uniform
challenge coins, and the run of `B` against `ccaOracle` from the state before the challenge. -/
noncomputable def indccaOracleGame (B : OracleAdv (INDCCAQuery M C) (INDCCAAns PK M C) Bool)
    (b : Bool) : PMF Bool :=
  P.keygen.bind fun ks => (PMF.uniformFintype R).bind fun r =>
    (OracleAdv.run (ccaOracle P b ks r) B none).map Prod.fst

/-- The IND-CCA oracle advantage: the distance between the two challenge bits. -/
noncomputable def indccaOracleAdvantage (B : OracleAdv (INDCCAQuery M C) (INDCCAAns PK M C) Bool) :
    ℝ≥0∞ :=
  Advantage (liftPMF (indccaOracleGame P B true)) (liftPMF (indccaOracleGame P B false))

/-- **The IND-CCA game is the oracle game of the oracle adversary.** For every two-stage
adversary `A` and bit `b`,
`indccaGame P A b = indccaOracleGame P (indccaOracleReduction A.choose A.guess) b`. -/
theorem indccaGame_eq_indccaOracleGame {q₁ q₂ : ℕ} (A : INDCCAAdversary PK M C q₁ q₂)
    (b : Bool) :
    indccaGame P A b = indccaOracleGame P (indccaOracleReduction A.choose A.guess) b := by
  simp only [indccaGame, indccaOracleGame, run_indccaOracleReduction]
  refine congrArg (PMF.bind _) (funext fun ks => ?_)
  rw [PMF.bind_comm]
  simp only [← run_decOracle_none, PMF.bind_map, Scheme.encDist]
  refine congrArg (PMF.bind _) (funext fun x => ?_)
  simp only [Function.comp_apply, Prod.map, chalCt]
  rfl

/-- **The oracle game is at least as strong as the two-stage game.** For every two-stage
IND-CCA adversary `A`,
`indccaAdvantage P A = indccaOracleAdvantage P (indccaOracleReduction A.choose A.guess)`. -/
theorem indccaAdvantage_eq_indccaOracleAdvantage {q₁ q₂ : ℕ}
    (A : INDCCAAdversary PK M C q₁ q₂) :
    indccaAdvantage P A = indccaOracleAdvantage P (indccaOracleReduction A.choose A.guess) := by
  simp only [indccaAdvantage, indccaOracleAdvantage, indccaGame_eq_indccaOracleGame]

end CatCrypt.Crypto.PKE.Games
