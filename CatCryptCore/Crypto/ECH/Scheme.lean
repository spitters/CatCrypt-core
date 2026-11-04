/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.HPKE.BaseCCA
public import CatCryptCore.Crypto.OracleAdversaryTimed
public import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Tactics.DeriveReduction

/-!
# Encrypted Client Hello (ECH): scheme and client-hello privacy game

Encrypted Client Hello (draft-ietf-tls-esni) hides the inner ClientHello, which carries the
real server name, from the network. The client-facing server publishes an `ECHConfig` with
an HPKE public key; the client encodes the inner ClientHello (`EncodedClientHelloInner`,
§5.1 of the draft, with padding), seals the encoding with HPKE Base mode under the config's
public key with the `ClientHelloOuterAAD` as associated data, and sends the encapsulation
and the ciphertext in the outer ClientHello. The client-facing server decapsulates, opens
and decodes.

`ECHScheme` is an HPKE Base mode scheme `HPKE.BaseCCA.HPKEBase` (a KEM in the random-oracle
model, the HPKE key schedule and a one-time AEAD) together with the client's encoding
`encode : I → M` of inner ClientHellos into plaintexts.

## The game

`echGame E A b` is client-hello privacy against an active network adversary: the adversary
receives the config's public key, has the random oracle and the client-facing server as a
decryption oracle (it answers each outer ClientHello it is sent with the opened plaintext
or `none`), chooses two inner ClientHellos and the outer associated data, and guesses which
of the two the challenge outer ClientHello carries; the decryption oracle refuses the
challenge. The experiment is the IND-CCA experiment `HPKE.BaseCCA.hpkeGame` run on
`echReduction E.encode A`, the HPKE adversary that applies the client's encoding to the two
inner ClientHellos, so the challenger seals `E.encode ch_b`.

## Main definitions

* `ECHScheme`, `ECHAdversary`, `echChoose`, `echReduction`, `echGame`, `echAdvantage`
* `echChoose.timed` (derived by `derive_timed`)
* `echReduction.timed : … → HPKEAdversary.Timed …` (derived by `derive_reduction` over the
  costed mirror `HPKEAdversary.Timed` of `derive_timed_structure`)

## Main results

* `echChoose.timeBound_timed` — with the first stage of the ECH adversary of time at most `T`
  built at cost at most `a`, and the encoding of cost at most `e`, the costed `echChoose`
  takes time at most `a + T + 2 * e + 3`.
* `echReduction.timeBound_timed` — the first stage of the costed `echReduction` takes time at
  most `a + T + 2 * e + 4`; for a second stage of the ECH adversary of time at most `T'` built
  at cost at most `a'`, the second stage of the costed `echReduction` takes time at most
  `a' + T' + 1`.
* `echReduction.erase_timed` — the costed form erases to `echReduction` at the ECH adversary
  whose stages are the erasures of the costed stages.

## References

* E. Rescorla, K. Oku, N. Sullivan, C. A. Wood, *TLS Encrypted Client Hello*,
  draft-ietf-tls-esni.
* R. Barnes, K. Bhargavan, B. Lipp, C. Wood, *Hybrid Public Key Encryption*, RFC 9180.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.ECH.Scheme

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.KEM.Games CatCrypt.Crypto.HPKE.BaseCCA
open CatCrypt.Crypto.PRPPRF
open scoped ENNReal

variable {PK SK K C D H Kd AD I M CT : Type}

/-! ## Scheme -/

variable (PK SK K C D H Kd AD I M CT) in
/-- ECH over HPKE Base mode: the HPKE scheme of the client-facing server's `ECHConfig`
and the client's encoding of inner ClientHellos (`I`) into HPKE plaintexts (`M`). -/
structure ECHScheme where
  /-- HPKE Base mode: KEM, key schedule and AEAD of the ECH config's cipher suite. -/
  hpke : HPKEBase PK SK K C D H Kd AD M CT
  /-- The encoding `EncodedClientHelloInner` of an inner ClientHello, with padding. -/
  encode : I → M

/-! ## Adversaries -/

variable (PK C D H AD I M CT) in
/-- A two-stage client-hello privacy adversary against ECH with at most `qH` random-oracle
queries and `qD` queries to the client-facing server in each stage. Its first stage
receives the config's public key and returns two inner ClientHellos, the outer associated
data and a state; its second stage receives the challenge encapsulation and ciphertext. -/
structure ECHAdversary (qH qD : ℕ) : Type 1 where
  /-- The state passed from the first to the second stage. -/
  St : Type
  /-- The first stage on the public key. -/
  choose : PK → OracleAdv (D ⊕ (C × AD × CT)) (H ⊕ Option M) (I × I × AD × St)
  /-- The second stage on the challenge encapsulation and ciphertext. -/
  guess : St → C × CT → OracleAdv (D ⊕ (C × AD × CT)) (H ⊕ Option M) Bool
  /-- The first-stage random-oracle query bound. -/
  isQueryBoundH₁ : ∀ pk, (choose pk).IsQueryBoundBy (Sum.elim (fun _ => 1) fun _ => 0) qH
  /-- The first-stage decryption query bound. -/
  isQueryBoundD₁ : ∀ pk, (choose pk).IsQueryBoundBy (Sum.elim (fun _ => 0) fun _ => 1) qD
  /-- The second-stage random-oracle query bound. -/
  isQueryBoundH₂ : ∀ st c, (guess st c).IsQueryBoundBy (Sum.elim (fun _ => 1) fun _ => 0) qH
  /-- The second-stage decryption query bound. -/
  isQueryBoundD₂ : ∀ st c, (guess st c).IsQueryBoundBy (Sum.elim (fun _ => 0) fun _ => 1) qD

/-! ## The reduction to HPKE -/

section Reduction

/-- The first stage of the HPKE adversary built from the first stage `choose` of an ECH
adversary: it runs `choose pk` and encodes the two inner ClientHellos with `encode`. -/
def echChoose {Q R St : Type} (encode : I → M) (choose : PK → OracleAdv Q R (I × I × AD × St))
    (pk : PK) : OracleAdv Q R (M × M × AD × St) :=
  (choose pk).bind fun x => .ret (encode x.1, encode x.2.1, x.2.2.1, x.2.2.2)

/-- **The HPKE IND-CCA adversary of an ECH adversary.** Its first stage is `echChoose`: it
runs the first stage of `A` and encodes the two inner ClientHellos; its second stage is
the second stage of `A`. Queries are passed through unchanged. -/
def echReduction {qH qD : ℕ} (encode : I → M) (A : ECHAdversary PK C D H AD I M CT qH qD) :
    HPKEAdversary PK C D H AD M CT qH qD where
  St := A.St
  choose := echChoose encode A.choose
  guess := A.guess
  isQueryBoundH₁ pk :=
    (OracleAdv.isQueryBoundBy_bind (b := 0) (A.isQueryBoundH₁ pk) fun _ => by trivial).mono
      (Nat.add_zero _).le
  isQueryBoundD₁ pk :=
    (OracleAdv.isQueryBoundBy_bind (b := 0) (A.isQueryBoundD₁ pk) fun _ => by trivial).mono
      (Nat.add_zero _).le
  isQueryBoundH₂ := A.isQueryBoundH₂
  isQueryBoundD₂ := A.isQueryBoundD₂

end Reduction

/-! ## The client-hello privacy game -/

section Game

variable [DecidableEq D] [Fintype H] [Nonempty H]
  [DecidableEq C] [DecidableEq AD] [DecidableEq CT]
  (E : ECHScheme PK SK K C D H Kd AD I M CT)

/-- The client-hello privacy experiment of ECH with challenge bit `b`: the HPKE IND-CCA
challenger of the config's scheme on `echReduction E.encode A`, which seals the encoding
of the first inner ClientHello (`b = true`) or of the second (`b = false`). -/
noncomputable def echGame {qH qD : ℕ} (A : ECHAdversary PK C D H AD I M CT qH qD) (b : Bool) :
    PMF Bool :=
  hpkeGame E.hpke (echReduction E.encode A) b

/-- The client-hello privacy advantage of `A` against ECH. -/
noncomputable def echAdvantage {qH qD : ℕ} (A : ECHAdversary PK C D H AD I M CT qH qD) : ℝ≥0∞ :=
  Advantage (liftPMF (echGame E A true)) (liftPMF (echGame E A false))

end Game

/-! ## Running time of the reduction -/

derive_timed echChoose

section Time

open OracleAdv.Timed

variable {Q R St : Type}

/-- **Time of the first stage of `echReduction`.** With the first stage `choose` of the ECH
adversary of time at most `T` and built at cost at most `a`, and the encoding of cost at
most `e`, the costed `echChoose` takes time at most `a + T + 2 * e + 3`: one step and the
cost of building `choose pk`, the run of `choose pk`, and two encodings of one step each. -/
theorem echChoose.timeBound_timed (encode : I → M) (encodeCost : I → ℕ)
    (choose : PK → OracleAdv.Timed Q R (I × I × AD × St)) (chooseCost : PK → ℕ)
    {a e T : ℕ} (he : ∀ x, encodeCost x ≤ e) (hc : ∀ pk, chooseCost pk ≤ a)
    (hA : ∀ pk, (choose pk).TimeBound T) (pk : PK) :
    StepTimeBound (echChoose.timed encode encodeCost choose chooseCost pk)
      (a + T + 2 * e + 3) := by
  unfold echChoose.timed
  refine (stepTimeBound_delay (timeBound_bind (n := 2 + 2 * e)
    (f := fun x => (1 + encodeCost x.1 + (1 + encodeCost x.2.1),
      ret (encode x.1, encode x.2.1, x.2.2.1, x.2.2.2))) (hA pk) fun x =>
    ⟨?_, trivial⟩)).mono ?_
  · grind
  · grind

end Time

derive_timed_structure HPKEAdversary

derive_reduction echReduction

section ReductionTime

open OracleAdv.Timed

/-- **Time of `echReduction`**: with the first stage `choose` of the ECH adversary of time at
most `T` and built at cost at most `a`, and the encoding of cost at most `e`, the first stage
of the costed `echReduction` takes time at most `a + T + 2 * e + 4`, the bound of
`echChoose.timeBound_timed` and one step for the call of `echChoose`; with the second stage
`guess` of time at most `T'` and built at cost at most `a'`, the second stage takes time at
most `a' + T' + 1`. -/
theorem echReduction.timeBound_timed {C D H CT : Type} {qH qD : ℕ} (encode : I → M)
    (encodeCost : I → ℕ) (A : ECHAdversary PK C D H AD I M CT qH qD)
    (choose : PK → OracleAdv.Timed (D ⊕ (C × AD × CT)) (H ⊕ Option M) (I × I × AD × A.St))
    (chooseCost : PK → ℕ)
    (guess : A.St → C × CT → OracleAdv.Timed (D ⊕ (C × AD × CT)) (H ⊕ Option M) Bool)
    (guessCost : A.St → C × CT → ℕ) {a e T a' T' : ℕ} (he : ∀ x, encodeCost x ≤ e)
    (hc : ∀ pk, chooseCost pk ≤ a) (hA : ∀ pk, (choose pk).TimeBound T)
    (hgc : ∀ st c, guessCost st c ≤ a') (hg : ∀ st c, (guess st c).TimeBound T') :
    (echReduction.timed encode encodeCost A choose chooseCost guess guessCost).TimeBound
      (a + T + 2 * e + 4) (a' + T' + 1) := by
  refine ⟨fun pk => ?_, fun st c => ?_⟩
  · show StepTimeBound (echReduction.choose.tree.timed encode encodeCost A choose chooseCost
      guess guessCost pk) (a + T + 2 * e + 4)
    exact (stepTimeBound_delay (c := 1)
      (echChoose.timeBound_timed encode encodeCost choose chooseCost he hc hA pk)).mono
      (by omega)
  · show StepTimeBound (echReduction.guess.tree.timed encode encodeCost A choose chooseCost
      guess guessCost st c) (a' + T' + 1)
    have := hgc st c
    exact ⟨by simp only [echReduction.guess.tree.timed]; omega,
      (hg st c).mono (by simp only [echReduction.guess.tree.timed]; omega)⟩

end ReductionTime

end CatCrypt.Crypto.ECH.Scheme
