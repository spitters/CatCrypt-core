/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PKE.Games
public import CatCryptCore.Crypto.OracleAdversaryRelabelTimed

/-!
# Sealed Sender: sender anonymity from IND-CCA public-key encryption

Signal's Sealed Sender (Signal, 2018; libsignal `sealed_sender.rs`, versions 1 and 2) hides
the sender of a message from the server that routes it. The sender encrypts the pair
(sender certificate, inner ciphertext) to the recipient's identity key; the server sees the
recipient, by which it routes, and the envelope. In libsignal the encryption is an ECIES-style
KEM-DEM: an ephemeral X25519 Diffie–Hellman with the identity key, a key derivation and an
authenticated cipher.

This file models the envelope as encryption under an arbitrary public-key scheme
`P : Scheme PK SK (Cert × Inner) C R` of the plaintext `(cert, inner)` to the recipient key
(`envelope`). The recipient accepts an envelope when it decrypts and the decrypted pair
passes the check `valid` (in libsignal the validation of the sender certificate against the
server's trust root); `accepts` is that predicate.

## The sender-anonymity game

The adversary is the server. Its first stage receives the recipient public key and chooses two
sender certificates `cert₀`, `cert₁`, an inner ciphertext `m` and a state; it receives the
envelope of `(cert_b, m)` and outputs a guess. In both stages it may submit envelopes to the
recipient and learn whether the recipient accepts (`acceptOracle`); this is the information a
server obtains from the recipient's reaction to an envelope it forges (a delivery receipt or
the absence of one). The oracle answers `false` on the challenge envelope after the challenge,
as the decryption oracle of IND-CCA answers `none` on it: the server knows that the challenge
was sent by one of the two senders, and accepting it carries no information about `b`. The
model therefore has a decryption-validity oracle, and the reduction is to IND-CCA. Recipient
anonymity is not modelled: the server routes by recipient.

## Main definitions

* `envelope`, `accepts`, `acceptOracle`
* `SenderAnonAdversary`, `senderAnonGame`, `senderAnonAdvantage`
* `acceptAnswer`, `senderAnonReduction` — the IND-CCA adversary that runs the sender-anonymity
  adversary and answers each acceptance query by one decryption query

## Main results

* `senderAnonGame_eq` — the sender-anonymity game with bit `b` is the IND-CCA game of
  `senderAnonReduction valid A` with bit `b`
* `senderAnon_le_indcca` — for every adversary `A`,
  `senderAnonAdvantage P valid A ≤ indccaAdvantage P (senderAnonReduction valid A)`
  (with equality, `senderAnonAdvantage_eq`)

## References

* Signal, *Technology preview: Sealed sender for Signal*, 2018.
* libsignal, `rust/protocol/src/sealed_sender.rs`.
* D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the Fujisaki–Okamoto
  Transformation*, TCC 2017, Section 2.1 (the IND-CCA game).
* M. Bellare, A. Boldyreva, A. Desai, D. Pointcheval, *Key-Privacy in Public-Key
  Encryption*, ASIACRYPT 2001 (anonymity notions for public-key encryption).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Messaging.SealedSender

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.PKE.Games
open scoped ENNReal

variable {PK SK Cert Inner C R : Type} [Fintype R] [Nonempty R]

/-! ## Envelopes and the recipient -/

/-- The sealed envelope of the sender certificate `cert` and the inner ciphertext `m` to the
recipient key `pk`: the encryption of `(cert, m)` under fresh coins. -/
noncomputable def envelope (P : Scheme PK SK (Cert × Inner) C R) (pk : PK) (cert : Cert)
    (m : Inner) : PMF C :=
  P.encDist pk (cert, m)

/-- The answer of the recipient to a decryption result: it accepts when the envelope decrypts
to a pair that passes `valid`. -/
def acceptAnswer (valid : Cert × Inner → Bool) (r : Option (Cert × Inner)) : Bool :=
  r.any valid

/-- The recipient with secret key `sk` accepts the envelope `c`. -/
def accepts (P : Scheme PK SK (Cert × Inner) C R) (valid : Cert × Inner → Bool) (sk : SK)
    (c : C) : Bool :=
  acceptAnswer valid (P.dec sk c)

/-- The acceptance oracle of the recipient with secret key `sk`. The state is the challenge
envelope (`none` before the challenge); the oracle answers `false` on it. -/
noncomputable def acceptOracle [DecidableEq C] (P : Scheme PK SK (Cert × Inner) C R)
    (valid : Cert × Inner → Bool) (sk : SK) (st : Option C) (c : C) : PMF (Bool × Option C) :=
  PMF.pure (if st = some c then false else accepts P valid sk c, st)

/-! ## The sender-anonymity game -/

variable (PK Cert Inner C) in
/-- A two-stage sender-anonymity adversary (the server) with at most `q₁` acceptance queries
in the first stage and `q₂` in the second. -/
structure SenderAnonAdversary (q₁ q₂ : ℕ) : Type 1 where
  /-- The state passed from the first to the second stage. -/
  St : Type
  /-- The first stage on the recipient key: two sender certificates, the inner ciphertext and
  a state. -/
  choose : PK → OracleAdv C Bool (Cert × Cert × Inner × St)
  /-- The second stage on the challenge envelope. -/
  guess : St → C → OracleAdv C Bool Bool
  /-- The first-stage query bound. -/
  isQueryBound₁ : ∀ pk, (choose pk).IsQueryBound q₁
  /-- The second-stage query bound. -/
  isQueryBound₂ : ∀ st c, (guess st c).IsQueryBound q₂

variable [DecidableEq C] (P : Scheme PK SK (Cert × Inner) C R) (valid : Cert × Inner → Bool)

/-- The sender-anonymity experiment with challenge bit `b`: the challenge is the envelope of
`(cert₀, m)` when `b = true` and of `(cert₁, m)` when `b = false`. -/
noncomputable def senderAnonGame {q₁ q₂ : ℕ} (A : SenderAnonAdversary PK Cert Inner C q₁ q₂)
    (b : Bool) : PMF Bool :=
  P.keygen.bind fun ks =>
    (OracleAdv.run (acceptOracle P valid ks.2) (A.choose ks.1) none).bind fun x =>
      (envelope P ks.1 (if b then x.1.1 else x.1.2.1) x.1.2.2.1).bind fun c =>
        (OracleAdv.run (acceptOracle P valid ks.2) (A.guess x.1.2.2.2 c) (some c)).map
          Prod.fst

/-- The sender-anonymity advantage: the distance between the two challenge bits. -/
noncomputable def senderAnonAdvantage {q₁ q₂ : ℕ}
    (A : SenderAnonAdversary PK Cert Inner C q₁ q₂) : ℝ≥0∞ :=
  Advantage (liftPMF (senderAnonGame P valid A true)) (liftPMF (senderAnonGame P valid A false))

/-! ## The reduction to IND-CCA -/

/-- The plaintexts of the IND-CCA challenge for the choice `x` of the sender-anonymity
adversary: `(cert₀, m)` and `(cert₁, m)`, and the state. -/
def chalPair {St : Type} (x : Cert × Cert × Inner × St) :
    (Cert × Inner) × (Cert × Inner) × St :=
  ((x.1, x.2.2.1), (x.2.1, x.2.2.1), x.2.2.2)

omit [Fintype R] [Nonempty R] [DecidableEq C] in
/-- The IND-CCA adversary built from the sender-anonymity adversary `A`: it runs both stages of
`A` once, asks each acceptance query as a decryption query and answers it by
`acceptAnswer valid` of the decryption; the first stage returns the two plaintexts
`(cert₀, m)` and `(cert₁, m)`. -/
def senderAnonReduction {q₁ q₂ : ℕ} (A : SenderAnonAdversary PK Cert Inner C q₁ q₂) :
    INDCCAAdversary PK (Cert × Inner) C q₁ q₂ where
  St := A.St
  choose pk := ((A.choose pk).mapQueryAnswer id (acceptAnswer valid)).bind fun x =>
    .ret (chalPair x)
  guess st c := (A.guess st c).mapQueryAnswer id (acceptAnswer valid)
  isQueryBound₁ pk := by
    simpa using OracleAdv.isQueryBound_bind
      (OracleAdv.isQueryBound_mapQueryAnswer id (acceptAnswer valid) (A.isQueryBound₁ pk))
      (f := fun x => OracleAdv.ret (chalPair x)) (n := 0) fun _ => trivial
  isQueryBound₂ st c :=
    OracleAdv.isQueryBound_mapQueryAnswer id (acceptAnswer valid) (A.isQueryBound₂ st c)

omit [Fintype R] [Nonempty R] in
/-- The decryption oracle read through `acceptAnswer valid` is the acceptance oracle. -/
theorem decOracle_map_eq (sk : SK) (st : Option C) (c : C) :
    (decOracle P sk st (id c)).map (fun x => (acceptAnswer valid x.1, x.2)) =
      acceptOracle P valid sk st c := by
  simp only [decOracle, acceptOracle, accepts, PMF.pure_map, id]
  split_ifs <;> rfl

omit [Fintype R] [Nonempty R] in
/-- Running a relabelled stage against the decryption oracle is running it against the
acceptance oracle. -/
theorem run_decOracle_mapQueryAnswer {α : Type} (sk : SK) (W : OracleAdv C Bool α)
    (st : Option C) :
    OracleAdv.run (decOracle P sk) (W.mapQueryAnswer id (acceptAnswer valid)) st =
      OracleAdv.run (acceptOracle P valid sk) W st := by
  rw [OracleAdv.run_mapQueryAnswer]
  exact congrArg (fun O => OracleAdv.run O W st)
    (funext fun s => funext fun c => decOracle_map_eq P valid sk s c)

/-- **The sender-anonymity game is an IND-CCA game.** For every adversary `A` and bit `b`,
`senderAnonGame P valid A b = indccaGame P (senderAnonReduction valid A) b`. -/
theorem senderAnonGame_eq {q₁ q₂ : ℕ} (A : SenderAnonAdversary PK Cert Inner C q₁ q₂)
    (b : Bool) : senderAnonGame P valid A b = indccaGame P (senderAnonReduction valid A) b := by
  simp only [senderAnonGame, indccaGame, senderAnonReduction, OracleAdv.run_bind,
    OracleAdv.run_ret, run_decOracle_mapQueryAnswer, PMF.bind_bind, PMF.pure_bind]
  refine congrArg _ (funext fun ks => congrArg _ (funext fun x => ?_))
  cases b <;> rfl

/-- The sender-anonymity advantage is the IND-CCA advantage of `senderAnonReduction`. -/
theorem senderAnonAdvantage_eq {q₁ q₂ : ℕ} (A : SenderAnonAdversary PK Cert Inner C q₁ q₂) :
    senderAnonAdvantage P valid A = indccaAdvantage P (senderAnonReduction valid A) := by
  simp only [senderAnonAdvantage, indccaAdvantage, senderAnonGame_eq]

/-- **Sealed Sender is sender-anonymous if the envelope encryption is IND-CCA secure.** For
every public-key scheme `P` of the envelope, recipient check `valid` and sender-anonymity
adversary `A` (the server, with an acceptance oracle in both stages),
`senderAnonAdvantage P valid A ≤ indccaAdvantage P (senderAnonReduction valid A)`.
The reduction runs both stages of `A` once and asks one decryption query per acceptance
query of `A`. -/
theorem senderAnon_le_indcca {q₁ q₂ : ℕ} (A : SenderAnonAdversary PK Cert Inner C q₁ q₂) :
    senderAnonAdvantage P valid A ≤ indccaAdvantage P (senderAnonReduction valid A) :=
  (senderAnonAdvantage_eq P valid A).le

end CatCrypt.Crypto.Messaging.SealedSender
