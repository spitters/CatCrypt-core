/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.HPKE.DHKEM
public import CatCryptCore.Crypto.HPKE.BaseCCA

/-!
# HPKE Base mode with DHKEM is IND-CCA secure under strong Diffie–Hellman

`hpkeDHKEM G sched aead` is HPKE Base mode single-shot encryption with DHKEM over the
Diffie–Hellman group `G` (key derivation as a random oracle), the key schedule `sched`
and the AEAD `aead`. Combining `BaseCCA.hpke_base_indcca` with `DHKEM.dhkem_correct` and
`DHKEM.dhkem_indcca` bounds its IND-CCA advantage by strong-DH advantages of two
reductions, key-schedule advantages, one-time INT-CTXT advantages and a one-time
IND-CPA advantage. `BaseCCA.hkdfSched_advantage_le` bounds the key-schedule terms for
the HKDF key schedule by HKDF-Extract and HKDF-Expand PRF advantages.

## Main results

* `hpke_base_indcca_dhkem`

## References

* J. Alwen, B. Blanchet, E. Hauck, E. Kiltz, B. Lipp, D. Riepel, *Analysing the
  HPKE Standard*, EUROCRYPT 2021, ePrint 2020/1499.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.HPKE.BaseCCADHKEM

open CatCrypt.Crypto CatCrypt.Crypto.KEM.Games
open CatCrypt.Crypto.HPKE.DHKEM CatCrypt.Crypto.HPKE.BaseCCA
open scoped ENNReal

variable {Sc P K Kd AD M CT : Type} [Fintype Sc] [Nonempty Sc] [DecidableEq P] [Fintype P]
  [Fintype K] [Nonempty K] [Fintype Kd] [Nonempty Kd] [DecidableEq AD] [DecidableEq CT]

/-- HPKE Base mode with DHKEM over `G`, the key schedule `sched` and the AEAD `aead`. -/
noncomputable abbrev hpkeDHKEM (G : DHGroup Sc P) (sched : K → Kd) (aead : OTAEAD Kd AD M CT) :
    HPKEBase P Sc K P (KDFDom P) K Kd AD M CT :=
  ⟨dhkem G, sched, aead⟩

/-- **HPKE Base mode with DHKEM is IND-CCA secure** (Alwen–Blanchet–Hauck–Kiltz–Lipp–
Riepel, EUROCRYPT 2021). For every Diffie–Hellman group `G`, key schedule `sched`, AEAD
`aead` and two-stage adversary `A` with the public key, the random oracle and a
decryption oracle, the IND-CCA advantage is at most the strong-DH advantages of
`dhkemReduction (kemReduction S A b)`, the key-schedule advantages of
`schedReduction S A b` and the one-time INT-CTXT advantages of `ctxtReduction S A b` for
both challenge bits `b`, plus the one-time IND-CPA advantage of `cpaReduction S A`.
Each reduction runs both stages of `A` once. -/
theorem hpke_base_indcca_dhkem (G : DHGroup Sc P) (sched : K → Kd) (aead : OTAEAD Kd AD M CT)
    {qH qD : ℕ} (A : HPKEAdversary P P (KDFDom P) K AD M CT qH qD) :
    hpkeAdvantage (hpkeDHKEM G sched aead) A ≤
      stdhAdvantage G (dhkemReduction (kemReduction (hpkeDHKEM G sched aead) A true)) +
        schedAdvantage sched (schedReduction (hpkeDHKEM G sched aead) A true) +
        otctxtAdvantage aead (ctxtReduction (hpkeDHKEM G sched aead) A true) +
        otcpaAdvantage aead (cpaReduction (hpkeDHKEM G sched aead) A) +
        otctxtAdvantage aead (ctxtReduction (hpkeDHKEM G sched aead) A false) +
        schedAdvantage sched (schedReduction (hpkeDHKEM G sched aead) A false) +
        stdhAdvantage G (dhkemReduction (kemReduction (hpkeDHKEM G sched aead) A false)) :=
  (hpke_base_indcca (hpkeDHKEM G sched aead) (dhkem_correct G) A).trans
    (add_le_add
      (add_le_add (add_le_add (add_le_add (add_le_add
        (add_le_add (dhkem_indcca G _) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl)
      (dhkem_indcca G _))

end CatCrypt.Crypto.HPKE.BaseCCADHKEM
