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

## Real and ideal worlds

In namespace `F_SealedSender`, the server is an adversary `FAdversary` with the recipient key
and the acceptance oracle in both stages; its first stage chooses the sender certificate and
the inner ciphertext, its second stage receives an envelope and outputs a bit. In the real
world (`sealedSender_real`) the envelope seals the chosen sender; in the ideal world
(`sealedSender_ideal P valid cert₀`) it seals the fixed sender `cert₀`, so the view of the
server does not depend on the sender. The ideal world is the envelope of a fixed sender, not
a uniform envelope: the scheme is not assumed to have pseudorandom ciphertexts. The inner
ciphertext is chosen by the server and is not hidden by this statement. For the eavesdropping
server, which asks no acceptance query, `sealedSenderView P cert m` is the view
`(pk, envelope)`.

## Main definitions

* `envelope`, `accepts`, `acceptOracle`
* `SenderAnonAdversary`, `senderAnonGame`, `senderAnonAdvantage`
* `acceptAnswer`, `senderAnonReduction` — the IND-CCA adversary that runs the sender-anonymity
  adversary and answers each acceptance query by one decryption query
* `F_SealedSender.FAdversary`, `sealedSenderExp`, `sealedSender_real`, `sealedSender_ideal`
* `F_SealedSender.fixSenderReduction` — the sender-anonymity adversary that runs an
  `FAdversary` and names its chosen sender and `cert₀` as the two candidate senders
* `F_SealedSender.sealedSenderView`, `viewReduction` — the view of an eavesdropping server and
  the sender-anonymity adversary that runs a distinguisher of two views

## Main results

* `senderAnonGame_eq` — the sender-anonymity game with bit `b` is the IND-CCA game of
  `senderAnonReduction valid A` with bit `b`
* `senderAnon_le_indcca` — for every adversary `A`,
  `senderAnonAdvantage P valid A ≤ indccaAdvantage P (senderAnonReduction valid A)`
  (with equality, `senderAnonAdvantage_eq`)
* `F_SealedSender.sealedSender_advantage_le` — the distance of the real and ideal worlds is at
  most `indccaAdvantage P (senderAnonReduction valid (fixSenderReduction cert₀ A))`
* `F_SealedSender.sealedSenderView_advantage_le` — the distance of the views of the senders
  `cert` and `cert₀` is at most
  `indccaAdvantage P (senderAnonReduction valid (viewReduction cert cert₀ m D))`

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

/-! ## Real and ideal worlds -/

namespace CatCrypt.Crypto.Signal.SealedSender.F_SealedSender

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.PKE.Games
open CatCrypt.Crypto.Messaging.SealedSender
open scoped ENNReal

variable {PK SK Cert Inner C R : Type} [Fintype R] [Nonempty R]

/-! ## The real and ideal worlds -/

variable (PK Cert Inner C) in
/-- A two-stage server with at most `q₁` acceptance queries in the first stage and `q₂` in the
second. The first stage chooses the sender certificate and the inner ciphertext. -/
structure FAdversary (q₁ q₂ : ℕ) : Type 1 where
  /-- The state passed from the first to the second stage. -/
  St : Type
  /-- The first stage on the recipient key. -/
  choose : PK → OracleAdv C Bool (Cert × Inner × St)
  /-- The second stage on the envelope. -/
  guess : St → C → OracleAdv C Bool Bool
  /-- The first-stage query bound. -/
  isQueryBound₁ : ∀ pk, (choose pk).IsQueryBound q₁
  /-- The second-stage query bound. -/
  isQueryBound₂ : ∀ st c, (guess st c).IsQueryBound q₂

variable [DecidableEq C] (P : Scheme PK SK (Cert × Inner) C R) (valid : Cert × Inner → Bool)

/-- The experiment of the server `A` in which the envelope seals the sender `sel cert` for the
chosen sender `cert`. -/
noncomputable def sealedSenderExp (sel : Cert → Cert) {q₁ q₂ : ℕ}
    (A : FAdversary PK Cert Inner C q₁ q₂) : PMF Bool :=
  P.keygen.bind fun ks =>
    (OracleAdv.run (acceptOracle P valid ks.2) (A.choose ks.1) none).bind fun x =>
      (envelope P ks.1 (sel x.1.1) x.1.2.1).bind fun c =>
        (OracleAdv.run (acceptOracle P valid ks.2) (A.guess x.1.2.2 c) (some c)).map Prod.fst

/-- The real world: the envelope seals the chosen sender. -/
noncomputable abbrev sealedSender_real {q₁ q₂ : ℕ} (A : FAdversary PK Cert Inner C q₁ q₂) :
    PMF Bool :=
  sealedSenderExp P valid id A

/-- The ideal world: the envelope seals the fixed sender `cert₀`. -/
noncomputable abbrev sealedSender_ideal (cert₀ : Cert) {q₁ q₂ : ℕ}
    (A : FAdversary PK Cert Inner C q₁ q₂) : PMF Bool :=
  sealedSenderExp P valid (fun _ => cert₀) A

omit [Fintype R] [Nonempty R] [DecidableEq C] in
/-- The sender-anonymity adversary of the server `A` and the fixed sender `cert₀`: it runs `A`
and names the sender chosen by `A` and `cert₀` as the two candidate senders. -/
def fixSenderReduction (cert₀ : Cert) {q₁ q₂ : ℕ} (A : FAdversary PK Cert Inner C q₁ q₂) :
    SenderAnonAdversary PK Cert Inner C q₁ q₂ where
  St := A.St
  choose pk := (A.choose pk).bind fun x => .ret (x.1, cert₀, x.2.1, x.2.2)
  guess := A.guess
  isQueryBound₁ pk := by
    simpa using OracleAdv.isQueryBound_bind (A.isQueryBound₁ pk)
      (f := fun x => OracleAdv.ret (x.1, cert₀, x.2.1, x.2.2)) (n := 0) fun _ => trivial
  isQueryBound₂ := A.isQueryBound₂

/-- The experiment is the sender-anonymity game of `fixSenderReduction cert₀ A` with the bit
selecting the sealed sender. -/
theorem sealedSenderExp_eq (cert₀ : Cert) {q₁ q₂ : ℕ} (A : FAdversary PK Cert Inner C q₁ q₂)
    (b : Bool) :
    sealedSenderExp P valid (fun cert => if b then cert else cert₀) A =
      senderAnonGame P valid (fixSenderReduction cert₀ A) b := by
  simp only [sealedSenderExp, senderAnonGame, fixSenderReduction, OracleAdv.run_bind,
    OracleAdv.run_ret, PMF.bind_bind, PMF.pure_bind]

/-- **The real and ideal worlds of Sealed Sender are indistinguishable if the envelope
encryption is IND-CCA secure.** For every scheme `P`, recipient check `valid`, fixed sender
`cert₀` and server `A`, the distance of `sealedSender_real P valid A` and
`sealedSender_ideal P valid cert₀ A` is at most the IND-CCA advantage of
`senderAnonReduction valid (fixSenderReduction cert₀ A)`. -/
theorem sealedSender_advantage_le (cert₀ : Cert) {q₁ q₂ : ℕ}
    (A : FAdversary PK Cert Inner C q₁ q₂) :
    Advantage (liftPMF (sealedSender_real P valid A))
        (liftPMF (sealedSender_ideal P valid cert₀ A)) ≤
      indccaAdvantage P (senderAnonReduction valid (fixSenderReduction cert₀ A)) := by
  have h₁ := sealedSenderExp_eq P valid cert₀ A true
  have h₀ := sealedSenderExp_eq P valid cert₀ A false
  simp only [ite_true, Bool.false_eq_true, ite_false] at h₁ h₀
  have e : (fun cert : Cert => cert) = id := rfl
  rw [e] at h₁
  rw [sealedSender_real, sealedSender_ideal, h₁, h₀]
  exact senderAnon_le_indcca P valid _

/-! ## The view of an eavesdropping server -/

/-- The view of a server that asks no acceptance queries: the recipient key and the envelope of
the sender `cert` and the inner ciphertext `m`. -/
noncomputable def sealedSenderView (cert : Cert) (m : Inner) : PMF (PK × C) :=
  P.keygen.bind fun ks => (envelope P ks.1 cert m).map fun c => (ks.1, c)

omit [Fintype R] [Nonempty R] [DecidableEq C] in
/-- The sender-anonymity adversary of a distinguisher `D` of views: it names `cert` and `cert₀`
with the inner ciphertext `m`, asks no acceptance query, and outputs `D` on the recipient key
and the challenge envelope. -/
def viewReduction (cert cert₀ : Cert) (m : Inner) (D : PK × C → PMF Bool) :
    SenderAnonAdversary PK Cert Inner C 0 0 where
  St := PK
  choose pk := .ret (cert, cert₀, m, pk)
  guess pk c := .rand (D (pk, c)) .ret
  isQueryBound₁ _ := trivial
  isQueryBound₂ _ _ := fun _ => trivial

/-- The sender-anonymity game of `viewReduction` is the view of the selected sender followed
by the distinguisher. -/
theorem senderAnonGame_viewReduction (cert cert₀ : Cert) (m : Inner) (D : PK × C → PMF Bool)
    (b : Bool) :
    senderAnonGame P valid (viewReduction cert cert₀ m D) b =
      (sealedSenderView P (if b then cert else cert₀) m).bind D := by
  simp only [senderAnonGame, sealedSenderView, viewReduction, OracleAdv.run_ret,
    OracleAdv.run_rand, PMF.pure_bind, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  refine congrArg _ (funext fun ks => ?_)
  cases b <;> simp [PMF.map_bind, PMF.pure_map, PMF.bind_pure]

/-- **The views of two senders are indistinguishable if the envelope encryption is IND-CCA
secure.** For every distinguisher `D`, the distance of the views of the senders `cert` and
`cert₀` with the inner ciphertext `m` is at most the IND-CCA advantage of
`senderAnonReduction valid (viewReduction cert cert₀ m D)`. -/
theorem sealedSenderView_advantage_le (cert cert₀ : Cert) (m : Inner) (D : PK × C → PMF Bool) :
    Advantage (liftPMF ((sealedSenderView P cert m).bind D))
        (liftPMF ((sealedSenderView P cert₀ m).bind D)) ≤
      indccaAdvantage P (senderAnonReduction valid (viewReduction cert cert₀ m D)) := by
  have h₁ := senderAnonGame_viewReduction P valid cert cert₀ m D true
  have h₀ := senderAnonGame_viewReduction P valid cert cert₀ m D false
  simp only [ite_true, Bool.false_eq_true, ite_false] at h₁ h₀
  rw [← h₁, ← h₀]
  exact senderAnon_le_indcca P valid _

end CatCrypt.Crypto.Signal.SealedSender.F_SealedSender
