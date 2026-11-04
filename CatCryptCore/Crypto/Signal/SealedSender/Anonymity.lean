/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SealedSender
public import CatCryptCore.Crypto.HPKE.BaseCCADHKEM

/-!
# Sealed Sender over an ECIES envelope: sender anonymity under strong Diffie–Hellman

libsignal's Sealed Sender envelope (`sealed_sender.rs`, versions 1 and 2) encrypts the pair
(sender certificate, inner ciphertext) to the recipient's identity key by an ephemeral X25519
Diffie–Hellman, a key derivation and an authenticated cipher: an ECIES / DHIES KEM-DEM. This
file instantiates the sender-anonymity statement of `Messaging.SealedSender` over a scheme in the
random-oracle model with that KEM-DEM in the form of HPKE Base mode single-shot encryption
(`HPKE.BaseCCA.HPKEBase`: a KEM in the random-oracle model, a key schedule and a one-time AEAD),
as the labelled scheme `HPKE.BaseCCA.hpkePKE` whose label is the associated data. Its instance
with DHKEM over a Diffie–Hellman group (`HPKE.BaseCCADHKEM.hpkeDHKEM`) is ECIES with the key
derivation as a random oracle.

## The game

`senderAnonAdvantage S valid A` is the advantage `senderAnonROMAdvantage valid (hpkePKE S) A`
of `Messaging.SealedSender`: the server receives the recipient key, has the random oracle and
the recipient as an acceptance oracle (it answers each envelope `(enc, ad, ct)` with whether it
decapsulates, opens and passes the check `valid`, and `false` on the challenge envelope after
the challenge), chooses two sender certificates, an inner ciphertext and the associated data,
and guesses which certificate the challenge envelope carries. Challenger, adversary and
recipient share one lazily sampled random-oracle table. The model has the acceptance oracle,
so the reduction is to IND-CCA. Recipient anonymity is not modelled.

## Main definitions

* `SenderAnonAdversary`, `senderAnonAdvantage` — the adversary and the advantage at
  `hpkePKE S`
* `senderAnonReduction` — the HPKE IND-CCA adversary of a sender-anonymity adversary:
  `labelCCAReduction` of `senderAnonROMReduction`

## Main results

* `senderAnon_le_hpke` — `senderAnonAdvantage S valid A ≤ hpkeAdvantage S
  (senderAnonReduction valid A)`
* `senderAnon_le_dhkem` — for the ECIES instance `hpkeDHKEM G sched aead`, the advantage is at
  most the strong-DH advantages of two reductions, the key-schedule and one-time INT-CTXT
  advantages for both challenge bits and one one-time IND-CPA advantage, by
  `HPKE.BaseCCADHKEM.hpke_base_indcca_dhkem`

## References

* Signal, *Technology preview: Sealed sender for Signal*, 2018.
* libsignal, `rust/protocol/src/sealed_sender.rs`.
* M. Abdalla, M. Bellare, P. Rogaway, *The Oracle Diffie–Hellman Assumptions and an Analysis
  of DHIES*, CT-RSA 2001.
* J. Alwen, B. Blanchet, E. Hauck, E. Kiltz, B. Lipp, D. Riepel, *Analysing the HPKE
  Standard*, EUROCRYPT 2021.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.SealedSender.Anonymity

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.HPKE.BaseCCA CatCrypt.Crypto.HPKE.DHKEM CatCrypt.Crypto.HPKE.BaseCCADHKEM
open CatCrypt.Crypto.Messaging.SealedSender
open scoped ENNReal

variable {PK SK K C D H Kd AD Cert Inner CT : Type}

/-- A two-stage sender-anonymity adversary (the server) against Sealed Sender over HPKE Base
mode, with at most `qH` random-oracle queries and `qD` acceptance queries in each stage: an
adversary of the random-oracle game with envelopes `(enc, ad, ct)` and the associated data as
the label. -/
abbrev SenderAnonAdversary (PK C D H AD Cert Inner CT : Type) (qH qD : ℕ) : Type 1 :=
  SenderAnonROMAdversary PK AD Cert Inner (C × AD × CT) D H qH qD qD

variable [DecidableEq D] [Fintype H] [Nonempty H] [DecidableEq C] [DecidableEq AD]
  [DecidableEq CT] (S : HPKEBase PK SK K C D H Kd AD (Cert × Inner) CT)
  (valid : Cert × Inner → Bool)

/-- The sender-anonymity advantage of `A` against Sealed Sender over HPKE Base mode. -/
noncomputable abbrev senderAnonAdvantage {qH qD : ℕ}
    (A : SenderAnonAdversary PK C D H AD Cert Inner CT qH qD) : ℝ≥0∞ :=
  senderAnonROMAdvantage valid (hpkePKE S) A

omit [DecidableEq D] [Fintype H] [Nonempty H] [DecidableEq C] [DecidableEq AD]
  [DecidableEq CT] in
/-- **The HPKE IND-CCA adversary of a sender-anonymity adversary.** It runs both stages of `A`
once, passes the random-oracle queries on, asks each acceptance query as a decryption query and
answers it by `acceptAnswer valid` of the decryption; the first stage returns the two plaintexts
`(cert₀, m)` and `(cert₁, m)` with the associated data. -/
def senderAnonReduction {qH qD : ℕ} (A : SenderAnonAdversary PK C D H AD Cert Inner CT qH qD) :
    HPKEAdversary PK C D H AD (Cert × Inner) CT qH qD :=
  labelCCAReduction (senderAnonROMReduction valid A)

/-- **Sealed Sender over HPKE Base mode is sender-anonymous if HPKE is IND-CCA secure.** For
every adversary `A`, `senderAnonAdvantage S valid A ≤ hpkeAdvantage S
(senderAnonReduction valid A)`. -/
theorem senderAnon_le_hpke {qH qD : ℕ} (A : SenderAnonAdversary PK C D H AD Cert Inner CT qH qD) :
    senderAnonAdvantage S valid A ≤ hpkeAdvantage S (senderAnonReduction valid A) :=
  (senderAnonROM_le valid (hpkePKE S) A).trans_eq (romLabelCCAAdvantage_hpkePKE S _)

end CatCrypt.Crypto.Signal.SealedSender.Anonymity

namespace CatCrypt.Crypto.Signal.SealedSender.Anonymity

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.KEM.Games CatCrypt.Crypto.HPKE.BaseCCA CatCrypt.Crypto.HPKE.DHKEM
open CatCrypt.Crypto.HPKE.BaseCCADHKEM
open scoped ENNReal

variable {Sc P K Kd AD Cert Inner CT : Type} [Fintype Sc] [Nonempty Sc] [DecidableEq P]
  [Fintype P] [Fintype K] [Nonempty K] [Fintype Kd] [Nonempty Kd] [DecidableEq AD]
  [DecidableEq CT]

/-- **Sealed Sender with the ECIES envelope is sender-anonymous under strong Diffie–Hellman.**
For the envelope `hpkeDHKEM G sched aead` (an ephemeral Diffie–Hellman over the group `G` with
the recipient key, the key derivation as a random oracle, the key schedule `sched` and the AEAD
`aead`), every recipient check `valid` and every sender-anonymity adversary `A`, with
`B = senderAnonReduction valid A` and `S = hpkeDHKEM G sched aead`, the advantage is at most
the strong-DH advantages of `dhkemReduction (kemReduction S B b)`, the key-schedule advantages
of `schedReduction S B b` and the one-time INT-CTXT advantages of `ctxtReduction S B b` for both
bits `b`, plus the one-time IND-CPA advantage of `cpaReduction S B`. -/
theorem senderAnon_le_dhkem (G : DHGroup Sc P) (sched : K → Kd)
    (aead : OTAEAD Kd AD (Cert × Inner) CT) (valid : Cert × Inner → Bool) {qH qD : ℕ}
    (A : SenderAnonAdversary P P (KDFDom P) K AD Cert Inner CT qH qD) :
    senderAnonAdvantage (hpkeDHKEM G sched aead) valid A ≤
      stdhAdvantage G (dhkemReduction
          (kemReduction (hpkeDHKEM G sched aead) (senderAnonReduction valid A) true)) +
        schedAdvantage sched
          (schedReduction (hpkeDHKEM G sched aead) (senderAnonReduction valid A) true) +
        otctxtAdvantage aead
          (ctxtReduction (hpkeDHKEM G sched aead) (senderAnonReduction valid A) true) +
        otcpaAdvantage aead (cpaReduction (hpkeDHKEM G sched aead) (senderAnonReduction valid A)) +
        otctxtAdvantage aead
          (ctxtReduction (hpkeDHKEM G sched aead) (senderAnonReduction valid A) false) +
        schedAdvantage sched
          (schedReduction (hpkeDHKEM G sched aead) (senderAnonReduction valid A) false) +
        stdhAdvantage G (dhkemReduction
          (kemReduction (hpkeDHKEM G sched aead) (senderAnonReduction valid A) false)) :=
  (senderAnon_le_hpke _ valid A).trans (hpke_base_indcca_dhkem G sched aead _)

end CatCrypt.Crypto.Signal.SealedSender.Anonymity
