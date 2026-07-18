/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.Encryption
import CatCryptCore.Crypto.Advantage
import CatCryptCore.Crypto.ShallowModule
import CatCryptCore.Relational.Rules
import CatCryptCore.Tactics.Basic
import CatCryptCore.Tactics.BindAlign
import CatCryptCore.Tactics.Sim
import CatCryptCore.Prob.XorBij

set_option linter.unusedSectionVars false

/-!
# KEM-DEM Composition (Hybrid Encryption)

The KEM-DEM construction is the standard recipe for hybrid public-key
encryption: a *key encapsulation mechanism* (KEM) ships a fresh symmetric key
under the public key, and a *data encapsulation mechanism* (DEM) encrypts the
payload under that key. This file builds the composition as a core `PKEScheme`
and proves its security by a three-hop hybrid argument.

This is the proof-ladders "asymmetric" benchmark (Rosulek, *The Joy of
Cryptography*, hybrid encryption): a secure KEM composed with a secure DEM
yields a secure public-key scheme.

## Overview

To encrypt `m` under `pk`:
1. `(k, ek) ← KEM.encap pk`  — encapsulate a fresh symmetric key `k`
2. `c := DEM.enc k m`          — encrypt the payload under `k`
3. output `(ek, c)`

To decrypt `(ek, c)` under `sk`: recover `k := KEM.decap sk ek`, then
`m := DEM.dec k c`.

## Security

These are IND-CPA games: the real game encrypts the actual message and the ideal
game encrypts a null message, and the adversary sees only `(pk, ek, c)` — there is
no decryption oracle, so the statement is confidentiality (CPA), not CCA.

The distinguishing advantage against the composed PKE-CPA game is bounded by

  Adv_PKE ≤ Adv_KEM + Adv_DEM + Adv_KEM,

via three game hops (`pke_security`): swap the encapsulated key for a random
key (KEM), swap the payload for a null message (DEM), swap the random key back
(KEM). When both components are *perfectly* secure the composition is perfectly
secure (`pke_perfect_security`): every advantage collapses to `0`.

As a concrete headline, `BoolXorDEM` (the one-time-pad DEM over `Bool`) is
perfectly DEM-secure via the XOR bijection coupling, so composing it with any
perfectly-secure KEM gives a perfectly-secure hybrid PKE
(`xorHybrid_perfect_security`).

## Main definitions

* `KEMScheme`, `DEMScheme`, `PKEScheme` — the component and target interfaces.
* `HybridPKE` — the KEM-DEM composition as a `PKEScheme`.
* `BoolXorDEM` — the XOR (one-time-pad) DEM over `Bool`.

## Main results

* `hybridPKE_correct` — correctness of the composition from component correctness.
* `pke_security` — the three-term hybrid bound `Adv_PKE ≤ Adv_KEM + Adv_DEM + Adv_KEM`.
* `pke_perfect_security` — perfect KEM + perfect DEM ⇒ perfect PKE.
* `boolXorDEM_perfect` — the XOR DEM is perfectly DEM-secure (XOR-bijection coupling).
* `xorHybrid_perfect_security` — perfect hybrid PKE from a perfect KEM and the XOR DEM.

## References

* [Rosulek, The Joy of Cryptography — hybrid (KEM-DEM) encryption]
* [Cramer & Shoup, Design and Analysis of Practical Public-Key Encryption Schemes]
* [Brzuska et al., State-Separating Proofs, ASIACRYPT 2018: https://eprint.iacr.org/2018/306]
-/

namespace CatCrypt.Examples.KEMDEM

open CatCrypt.Core
open CatCrypt.Crypto
open CatCrypt.Prob
open CatCrypt.Prob.XorBij
open CatCrypt.Relational
open scoped ENNReal

/-! ## KEM Scheme

A Key Encapsulation Mechanism generates a fresh symmetric key and encapsulates
it under the public key; the key is recovered from the encapsulation using the
secret key.
-/

/-- A Key Encapsulation Mechanism (KEM) scheme.

Type parameters: `PKey` public key, `SKey` secret key, `Key` symmetric key,
`EKey` encapsulation (KEM ciphertext). -/
structure KEMScheme (PKey SKey Key EKey : Type) where
  /-- Key generation: produces a public/secret key pair. -/
  kgen : SPComp (PKey × SKey)
  /-- Encapsulation: from a public key, a symmetric key and its encapsulation. -/
  encap : PKey → SPComp (Key × EKey)
  /-- Decapsulation: deterministically recovers the symmetric key. -/
  decap : SKey → EKey → Key

namespace KEMScheme

variable {PKey SKey Key EKey : Type}
variable (KEM : KEMScheme PKey SKey Key EKey)

/-- KEM correctness: decapsulation inverts encapsulation for generated key pairs. -/
def Correct : Prop :=
  ∀ pk sk h h' k ek h'',
    ((pk, sk), h') ∈ (KEM.kgen h).support →
    ((k, ek), h'') ∈ (KEM.encap pk h').support →
    KEM.decap sk ek = k

end KEMScheme

/-! ## DEM Scheme

A Data Encapsulation Mechanism is a deterministic symmetric cipher.
-/

/-- A Data Encapsulation Mechanism (DEM): deterministic encryption/decryption. -/
structure DEMScheme (Key Plain Cipher : Type) where
  /-- Deterministic encryption. -/
  enc : Key → Plain → Cipher
  /-- Deterministic decryption. -/
  dec : Key → Cipher → Plain

namespace DEMScheme

variable {Key Plain Cipher : Type}
variable (DEM : DEMScheme Key Plain Cipher)

/-- DEM correctness: decryption inverts encryption. -/
def Correct : Prop :=
  ∀ k m, DEM.dec k (DEM.enc k m) = m

end DEMScheme

/-! ## PKE Scheme

The target interface implemented by the KEM-DEM composition.
-/

/-- A Public Key Encryption (PKE) scheme.

The ciphertext is a pair `(EKey × Cipher)` of the KEM encapsulation and the
DEM ciphertext. -/
structure PKEScheme (PKey SKey Plain EKey Cipher : Type) where
  /-- Key generation: produces a public/secret key pair. -/
  kgen : SPComp (PKey × SKey)
  /-- Encryption: public key and plaintext to a ciphertext pair. -/
  enc : PKey → Plain → SPComp (EKey × Cipher)
  /-- Decryption: deterministic, secret key and ciphertext pair to plaintext. -/
  dec : SKey → EKey × Cipher → Plain

/-! ## KEM-DEM Hybrid Construction -/

/-- The KEM-DEM hybrid encryption scheme built from a KEM and a DEM. -/
noncomputable def HybridPKE
    {PKey SKey Key EKey Plain Cipher : Type}
    (KEM : KEMScheme PKey SKey Key EKey)
    (DEM : DEMScheme Key Plain Cipher) :
    PKEScheme PKey SKey Plain EKey Cipher where
  kgen := KEM.kgen
  enc := fun pk m => do
    let (k, ek) ← KEM.encap pk
    let c := DEM.enc k m
    return (ek, c)
  dec := fun sk (ek, c) =>
    let k := KEM.decap sk ek
    DEM.dec k c

/-! ## Correctness -/

/-- Correctness of the hybrid scheme from KEM and DEM correctness. -/
theorem hybridPKE_correct
    {PKey SKey Key EKey Plain Cipher : Type}
    (KEM : KEMScheme PKey SKey Key EKey)
    (DEM : DEMScheme Key Plain Cipher)
    (hKEM : KEM.Correct)
    (hDEM : DEM.Correct) :
    ∀ pk sk h h' m ek c h'',
      ((pk, sk), h') ∈ (KEM.kgen h).support →
      ((ek, c), h'') ∈ ((HybridPKE KEM DEM).enc pk m h').support →
      (HybridPKE KEM DEM).dec sk (ek, c) = m := by
  intro pk sk h h' m ek c h'' hkgen henc
  simp only [HybridPKE] at henc ⊢
  simp only [SPComp.monad_bind_eq, SPComp.bind_def] at henc
  rw [SDistr.mem_support_iff] at henc
  simp only [SDistr.bind, PMF.bind_apply, ne_eq] at henc
  by_contra hdec_ne
  apply henc
  rw [ENNReal.tsum_eq_zero]
  intro oa
  cases oa with
  | none =>
    simp only [SDistr.fail, PMF.pure_apply, reduceCtorEq, ite_false, mul_zero]
  | some a =>
    obtain ⟨⟨k, ek'⟩, h'''⟩ := a
    simp only []
    show (KEM.encap pk h') (some ((k, ek'), h''')) *
         (SPComp.pure (ek', DEM.enc k m) h''') (some ((ek, c), h'')) = 0
    simp only [SPComp.pure_def, SDistr.pure, PMF.pure_apply]
    by_cases heq : (some (((ek', DEM.enc k m), h'''))) = (some ((ek, c), h''))
    · simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨⟨hek_eq, hc_eq⟩, hh_eq⟩ := heq
      by_cases hencap_nz : (KEM.encap pk h') (some ((k, ek'), h''')) = 0
      · simp only [hencap_nz, zero_mul]
      · have hencap_supp : ((k, ek'), h''') ∈ (KEM.encap pk h').support := by
          rw [SDistr.mem_support_iff]
          exact hencap_nz
        have hKEM_dec := hKEM pk sk h h' k ek' h''' hkgen hencap_supp
        have hdec_works : DEM.dec (KEM.decap sk ek) c = m := by
          rw [← hek_eq, hKEM_dec, ← hc_eq, hDEM]
        exact absurd hdec_works hdec_ne
    · have hcond : ¬ (some ((ek, c), h'') = some ((ek', DEM.enc k m), h''')) := by
        intro heq'
        apply heq
        exact heq'.symm
      simp only [hcond, ite_false, mul_zero]

/-! ## KEM-CPA Security Game

  Real: the challenge key is the encapsulated key.
  Ideal: the challenge key is fresh and independent of the encapsulation.
-/

section KEM_CPA

variable {PKey SKey Key EKey : Type}
variable [Fintype Key] [Nonempty Key]
variable [Fintype EKey] [Nonempty EKey]

/-- KEM-CPA real game: return `(pk, ek, k)` for the actual encapsulated key `k`. -/
noncomputable def KEM_CPA_real
    (KEM : KEMScheme PKey SKey Key EKey) :
    SPComp (PKey × EKey × Key) := do
  let (pk, _sk) ← KEM.kgen
  let (k, ek) ← KEM.encap pk
  return (pk, ek, k)

/-- KEM-CPA ideal game: return `(pk, ek, k')` for a fresh random key `k'`. -/
noncomputable def KEM_CPA_ideal
    (KEM : KEMScheme PKey SKey Key EKey) :
    SPComp (PKey × EKey × Key) := do
  let (pk, _sk) ← KEM.kgen
  let (_k, ek) ← KEM.encap pk
  let k' ← SPComp.sample Key
  return (pk, ek, k')

/-- KEM-CPA advantage. -/
noncomputable def KEM_CPA_Advantage
    (KEM : KEMScheme PKey SKey Key EKey)
    (A : PKey × EKey × Key → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (KEM_CPA_real KEM) (KEM_CPA_ideal KEM) A

/-- Perfect KEM-CPA security: the real and ideal games are perfectly coupled. -/
def PerfectKEM_CPA (KEM : KEMScheme PKey SKey Key EKey) : Prop :=
  rHoare eqPre (KEM_CPA_real KEM) (KEM_CPA_ideal KEM) eqPost

end KEM_CPA

/-! ## DEM-CPA Security Game

  Real: encrypt the actual message. Ideal: encrypt a fixed null message.
-/

section DEM_CPA

variable {Key Plain Cipher : Type}
variable [Fintype Key] [Nonempty Key]
variable [Fintype Cipher] [Nonempty Cipher]

/-- DEM-CPA real game: sample a key, encrypt the actual message. -/
noncomputable def DEM_CPA_real
    (DEM : DEMScheme Key Plain Cipher)
    (m : Plain) :
    SPComp Cipher := do
  let k ← SPComp.sample Key
  return DEM.enc k m

/-- DEM-CPA ideal game: sample a key, encrypt the null message. -/
noncomputable def DEM_CPA_ideal
    (DEM : DEMScheme Key Plain Cipher)
    (nullPlain : Plain)
    (_m : Plain) :
    SPComp Cipher := do
  let k ← SPComp.sample Key
  return DEM.enc k nullPlain

/-- DEM-CPA advantage. -/
noncomputable def DEM_CPA_Advantage
    (DEM : DEMScheme Key Plain Cipher)
    (nullPlain : Plain)
    (m : Plain)
    (A : Cipher → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (DEM_CPA_real DEM m) (DEM_CPA_ideal DEM nullPlain m) A

/-- Perfect DEM-CPA security: real and ideal games are perfectly coupled. -/
def PerfectDEM_CPA (DEM : DEMScheme Key Plain Cipher) (nullPlain : Plain) : Prop :=
  ∀ m, rHoare eqPre (DEM_CPA_real DEM m) (DEM_CPA_ideal DEM nullPlain m) eqPost

end DEM_CPA

/-! ## PKE-CPA Security Game (for the hybrid scheme) -/

section PKE_CPA

variable {PKey SKey Key EKey Plain Cipher : Type}
variable [Fintype Key] [Nonempty Key]
variable [Fintype EKey] [Nonempty EKey]
variable [Fintype Cipher] [Nonempty Cipher]

/-- PKE-CPA real game: return `(pk, ek, c)` encrypting the actual message. -/
noncomputable def PKE_CPA_real
    (PKE : PKEScheme PKey SKey Plain EKey Cipher)
    (m : Plain) :
    SPComp (PKey × EKey × Cipher) := do
  let (pk, _sk) ← PKE.kgen
  let (ek, c) ← PKE.enc pk m
  return (pk, ek, c)

/-- PKE-CPA ideal game: return `(pk, ek, c)` encrypting the null message. -/
noncomputable def PKE_CPA_ideal
    (PKE : PKEScheme PKey SKey Plain EKey Cipher)
    (nullPlain : Plain)
    (_m : Plain) :
    SPComp (PKey × EKey × Cipher) := do
  let (pk, _sk) ← PKE.kgen
  let (ek, c) ← PKE.enc pk nullPlain
  return (pk, ek, c)

/-- PKE-CPA advantage. -/
noncomputable def PKE_CPA_Advantage
    (PKE : PKEScheme PKey SKey Plain EKey Cipher)
    (nullPlain : Plain)
    (m : Plain)
    (A : PKey × EKey × Cipher → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (PKE_CPA_real PKE m) (PKE_CPA_ideal PKE nullPlain m) A

/-- Perfect PKE-CPA security. -/
def PerfectPKE_CPA (PKE : PKEScheme PKey SKey Plain EKey Cipher) (nullPlain : Plain) : Prop :=
  ∀ m, rHoare eqPre (PKE_CPA_real PKE m) (PKE_CPA_ideal PKE nullPlain m) eqPost

end PKE_CPA

/-! ## Hybrid Games for the Security Reduction

Game 0 (PKE real) → Game 1 (random key) → Game 2 (random key + null) →
Game 3 (PKE ideal).
-/

section HybridGames

variable {PKey SKey Key EKey Plain Cipher : Type}
variable [Fintype Key] [Nonempty Key]
variable [Fintype EKey] [Nonempty EKey]
variable [Fintype Cipher] [Nonempty Cipher]

variable (KEM : KEMScheme PKey SKey Key EKey)
variable (DEM : DEMScheme Key Plain Cipher)
variable (nullPlain : Plain)

/-- Hybrid Game 1: encrypt the actual message under a *random* key. -/
noncomputable def HybridGame1 (m : Plain) : SPComp (PKey × EKey × Cipher) := do
  let (pk, _sk) ← KEM.kgen
  let (_k, ek) ← KEM.encap pk
  let k' ← SPComp.sample Key
  return (pk, ek, DEM.enc k' m)

/-- Hybrid Game 2: encrypt the null message under a random key. -/
noncomputable def HybridGame2 (_m : Plain) : SPComp (PKey × EKey × Cipher) := do
  let (pk, _sk) ← KEM.kgen
  let (_k, ek) ← KEM.encap pk
  let k' ← SPComp.sample Key
  return (pk, ek, DEM.enc k' nullPlain)

end HybridGames

/-! ## Security Reductions -/

section Reductions

variable {PKey SKey Key EKey Plain Cipher : Type}
variable [Fintype Key] [Nonempty Key]
variable [Fintype EKey] [Nonempty EKey]
variable [Fintype Cipher] [Nonempty Cipher]

variable (KEM : KEMScheme PKey SKey Key EKey)
variable (DEM : DEMScheme Key Plain Cipher)
variable (nullPlain : Plain)
variable (m : Plain)

/-- Reduction to KEM-CPA (first hop): receive `(pk, ek, k)`, DEM-encrypt `m`, run `A`. -/
noncomputable def ReductionKEM1
    (A : PKey × EKey × Cipher → SPComp Bool)
    (challenge : PKey × EKey × Key) : SPComp Bool :=
  let (pk, ek, k) := challenge
  let c := DEM.enc k m
  A (pk, ek, c)

/-- Reduction to DEM-CPA (second hop): run KEM, receive `c`, run `A`. -/
noncomputable def ReductionDEM
    (A : PKey × EKey × Cipher → SPComp Bool)
    (c : Cipher) : SPComp Bool := do
  let (pk, _sk) ← KEM.kgen
  let (_k, ek) ← KEM.encap pk
  A (pk, ek, c)

/-- Reduction to KEM-CPA (third hop): as `ReductionKEM1` but on `nullPlain`. -/
noncomputable def ReductionKEM2
    (A : PKey × EKey × Cipher → SPComp Bool)
    (challenge : PKey × EKey × Key) : SPComp Bool :=
  let (pk, ek, k) := challenge
  let c := DEM.enc k nullPlain
  A (pk, ek, c)

end Reductions

/-! ## Game Equivalences

Each consecutive pair of games equals a component game composed with a reduction.
-/

section GameEquivalences

variable {PKey SKey Key EKey Plain Cipher : Type}
variable [Fintype Key] [Nonempty Key]
variable [Fintype EKey] [Nonempty EKey]
variable [Fintype Cipher] [Nonempty Cipher]

variable (KEM : KEMScheme PKey SKey Key EKey)
variable (DEM : DEMScheme Key Plain Cipher)
variable (nullPlain : Plain)
variable (m : Plain)

/-- PKE-CPA real, post-composed with `A`, equals KEM-CPA real ∘ `ReductionKEM1`. -/
theorem pke_real_eq_kem_real_bind (A : PKey × EKey × Cipher → SPComp Bool) :
    (PKE_CPA_real (HybridPKE KEM DEM) m).bind A =
    (KEM_CPA_real KEM).bind (ReductionKEM1 DEM m A) := by
  unfold PKE_CPA_real HybridPKE KEM_CPA_real ReductionKEM1
  ssprove_proc

/-- HybridGame1 ∘ `A` equals KEM-CPA ideal ∘ `ReductionKEM1`. -/
theorem hybrid1_eq_kem_ideal_bind (A : PKey × EKey × Cipher → SPComp Bool) :
    (HybridGame1 KEM DEM m).bind A =
    (KEM_CPA_ideal KEM).bind (ReductionKEM1 DEM m A) := by
  unfold HybridGame1 KEM_CPA_ideal ReductionKEM1
  ssprove_proc

/-- HybridGame1 ∘ `A` equals DEM-CPA real ∘ `ReductionDEM`.

Uses `SDistr.bind_comm` to commute the (independent) uniform key sampling past
the KEM operations. -/
theorem hybrid1_eq_dem_real_bind (A : PKey × EKey × Cipher → SPComp Bool) :
    (HybridGame1 KEM DEM m).bind A =
    (DEM_CPA_real DEM m).bind (ReductionDEM KEM A) := by
  funext h
  unfold HybridGame1 DEM_CPA_real ReductionDEM
  simp only [SPComp.monad_bind_eq, SPComp.bind_def]
  ssprove_distr_simp
  show ((KEM.kgen h).bind fun a ↦
      (KEM.encap a.1.1 a.2).bind fun a_1 ↦
        (SDistr.uniform Key).bind fun a_2 ↦
          (SDistr.pure ((a.1.1, a_1.1.2, DEM.enc a_2 m), a_1.2)).bind fun x ↦ A x.1 x.2) =
    (SDistr.uniform Key).bind fun a ↦
      (SDistr.pure ((DEM.enc a m), h)).bind fun x ↦
        (KEM.kgen x.2).bind fun x_1 ↦ (KEM.encap x_1.1.1 x_1.2).bind fun x_2 ↦ A (x_1.1.1, x_2.1.2, x.1) x_2.2
  simp only [SDistr.pure_bind]
  conv_lhs =>
    arg 2; ext a
    rw [SDistr.bind_comm (KEM.encap a.1.1 a.2) (SDistr.uniform Key)]
  rw [SDistr.bind_comm (KEM.kgen h) (SDistr.uniform Key)]

/-- HybridGame2 ∘ `A` equals DEM-CPA ideal ∘ `ReductionDEM`. -/
theorem hybrid2_eq_dem_ideal_bind (A : PKey × EKey × Cipher → SPComp Bool) :
    (HybridGame2 KEM DEM nullPlain m).bind A =
    (DEM_CPA_ideal DEM nullPlain m).bind (ReductionDEM KEM A) := by
  funext h
  unfold HybridGame2 DEM_CPA_ideal ReductionDEM
  simp only [SPComp.monad_bind_eq, SPComp.bind_def]
  ssprove_distr_simp
  show ((KEM.kgen h).bind fun a ↦
      (KEM.encap a.1.1 a.2).bind fun a_1 ↦
        (SDistr.uniform Key).bind fun a_2 ↦
          (SDistr.pure ((a.1.1, a_1.1.2, DEM.enc a_2 nullPlain), a_1.2)).bind fun x ↦ A x.1 x.2) =
    (SDistr.uniform Key).bind fun a ↦
      (SDistr.pure ((DEM.enc a nullPlain), h)).bind fun x ↦
        (KEM.kgen x.2).bind fun x_1 ↦ (KEM.encap x_1.1.1 x_1.2).bind fun x_2 ↦ A (x_1.1.1, x_2.1.2, x.1) x_2.2
  simp only [SDistr.pure_bind]
  conv_lhs =>
    arg 2; ext a
    rw [SDistr.bind_comm (KEM.encap a.1.1 a.2) (SDistr.uniform Key)]
  rw [SDistr.bind_comm (KEM.kgen h) (SDistr.uniform Key)]

/-- HybridGame2 ∘ `A` equals KEM-CPA ideal ∘ `ReductionKEM2`. -/
theorem hybrid2_eq_kem_ideal_bind2 (A : PKey × EKey × Cipher → SPComp Bool) :
    (HybridGame2 KEM DEM nullPlain m).bind A =
    (KEM_CPA_ideal KEM).bind (ReductionKEM2 DEM nullPlain A) := by
  unfold HybridGame2 KEM_CPA_ideal ReductionKEM2
  ssprove_proc

/-- PKE-CPA ideal ∘ `A` equals KEM-CPA real ∘ `ReductionKEM2`. -/
theorem pke_ideal_eq_kem_real_bind2 (A : PKey × EKey × Cipher → SPComp Bool) :
    (PKE_CPA_ideal (HybridPKE KEM DEM) nullPlain m).bind A =
    (KEM_CPA_real KEM).bind (ReductionKEM2 DEM nullPlain A) := by
  unfold PKE_CPA_ideal HybridPKE KEM_CPA_real ReductionKEM2
  ssprove_proc

end GameEquivalences

/-! ## Main Security Theorem -/

/-- **KEM-DEM security**: the hybrid PKE-CPA advantage is bounded by two KEM-CPA
advantages and one DEM-CPA advantage,

  `Adv_PKE(A) ≤ Adv_KEM(A₁) + Adv_DEM(A₂) + Adv_KEM(A₃)`,

where `A₁ = ReductionKEM1`, `A₂ = ReductionDEM`, `A₃ = ReductionKEM2`. Proved by
the triangle inequality over the three hybrid games and the game equivalences. -/
theorem pke_security
    {PKey SKey Key EKey Plain Cipher : Type}
    [Fintype Key] [Nonempty Key]
    [Fintype EKey] [Nonempty EKey]
    [Fintype Cipher] [Nonempty Cipher]
    (KEM : KEMScheme PKey SKey Key EKey)
    (DEM : DEMScheme Key Plain Cipher)
    (nullPlain : Plain)
    (m : Plain)
    (A : PKey × EKey × Cipher → SPComp Bool)
    : PKE_CPA_Advantage (HybridPKE KEM DEM) nullPlain m A ≤
      KEM_CPA_Advantage KEM (ReductionKEM1 DEM m A) +
      DEM_CPA_Advantage DEM nullPlain m (ReductionDEM KEM A) +
      KEM_CPA_Advantage KEM (ReductionKEM2 DEM nullPlain A)
    := by
  have hop1 : AdvantageA (PKE_CPA_real (HybridPKE KEM DEM) m) (HybridGame1 KEM DEM m) A
      = KEM_CPA_Advantage KEM (ReductionKEM1 DEM m A) := by
    unfold KEM_CPA_Advantage AdvantageA
    rw [pke_real_eq_kem_real_bind KEM DEM m A, hybrid1_eq_kem_ideal_bind KEM DEM m A]
  have hop2 : AdvantageA (HybridGame1 KEM DEM m) (HybridGame2 KEM DEM nullPlain m) A
      = DEM_CPA_Advantage DEM nullPlain m (ReductionDEM KEM A) := by
    unfold DEM_CPA_Advantage AdvantageA
    rw [hybrid1_eq_dem_real_bind KEM DEM m A, hybrid2_eq_dem_ideal_bind KEM DEM nullPlain m A]
  have hop3 : AdvantageA (HybridGame2 KEM DEM nullPlain m)
      (PKE_CPA_ideal (HybridPKE KEM DEM) nullPlain m) A
      = KEM_CPA_Advantage KEM (ReductionKEM2 DEM nullPlain A) := by
    unfold KEM_CPA_Advantage AdvantageA
    rw [hybrid2_eq_kem_ideal_bind2 KEM DEM nullPlain m A,
        pke_ideal_eq_kem_real_bind2 KEM DEM nullPlain m A]
    unfold Advantage; rw [max_comm]
  have hbound := ShallowModule.hybrid_boundA₃
    (PKE_CPA_real (HybridPKE KEM DEM) m) (HybridGame1 KEM DEM m)
    (HybridGame2 KEM DEM nullPlain m) (PKE_CPA_ideal (HybridPKE KEM DEM) nullPlain m) A
  rw [hop1, hop2, hop3] at hbound
  unfold PKE_CPA_Advantage
  exact hbound

/-! ## Corollary: Perfect Security

If both components are perfectly secure, so is the composition.
-/

/-- `eqPost`-coupling implies `Eq`-coupling on `α × Heap` pairs. -/
private theorem eqPost_to_eq {α : Type*} {d₁ d₂ : SDistr (α × Heap)}
    (h : d₁ ⟨fun p₁ p₂ => eqPost p₁.1 p₁.2 p₂.1 p₂.2⟩# d₂) :
    d₁ ⟨Eq⟩# d₂ := by
  apply liftR_mono _ h
  intro ⟨a₁, h₁⟩ ⟨a₂, h₂⟩ heqpost
  simp only [eqPost] at heqpost
  exact Prod.ext heqpost.1 heqpost.2

/-- `Eq`-coupling implies `eqPost`-coupling on `α × Heap` pairs. -/
private theorem eq_to_eqPost {α : Type*} {d₁ d₂ : SDistr (α × Heap)}
    (h : d₁ ⟨Eq⟩# d₂) :
    d₁ ⟨fun p₁ p₂ => eqPost p₁.1 p₁.2 p₂.1 p₂.2⟩# d₂ := by
  apply liftR_mono _ h
  intro ⟨a₁, h₁⟩ ⟨a₂, h₂⟩ heq
  simp only [Prod.mk.injEq] at heq
  simp only [eqPost]
  exact heq

private theorem pke_real_eq_hybrid1
    {PKey SKey Key EKey Plain Cipher : Type}
    [Fintype Key] [Nonempty Key]
    [Fintype EKey] [Nonempty EKey]
    [Fintype Cipher] [Nonempty Cipher]
    (KEM : KEMScheme PKey SKey Key EKey)
    (DEM : DEMScheme Key Plain Cipher)
    (m : Plain)
    (hKEM : PerfectKEM_CPA KEM) :
    rHoare eqPre (PKE_CPA_real (HybridPKE KEM DEM) m) (HybridGame1 KEM DEM m) eqPost := by
  intro h₁ h₂ hheq
  simp only [eqPre] at hheq
  subst hheq
  have hkem_eq := liftR_eq_implies_eq (eqPost_to_eq (hKEM h₁ h₁ rfl))
  have h_prog_eq : (PKE_CPA_real (HybridPKE KEM DEM) m) h₁ = (HybridGame1 KEM DEM m) h₁ := by
    have h1 : (PKE_CPA_real (HybridPKE KEM DEM) m) h₁ =
        (KEM_CPA_real KEM h₁).bind (fun ⟨⟨pk, ek, k⟩, h⟩ => SDistr.pure ((pk, ek, DEM.enc k m), h)) := by
      unfold PKE_CPA_real HybridPKE KEM_CPA_real
      simp only [SPComp.monad_bind_eq, SPComp.bind_def, SDistr.bind_assoc]
      bind_align
      simp [SPComp.pure, SDistr.pure_bind]
    have h2 : (HybridGame1 KEM DEM m) h₁ =
        (KEM_CPA_ideal KEM h₁).bind (fun ⟨⟨pk, ek, k⟩, h⟩ => SDistr.pure ((pk, ek, DEM.enc k m), h)) := by
      unfold HybridGame1 KEM_CPA_ideal
      simp only [SPComp.monad_bind_eq, SPComp.bind_def, SDistr.bind_assoc]
      bind_align
      simp [SPComp.pure, SDistr.pure_bind]
    rw [h1, h2, hkem_eq]
  rw [h_prog_eq]
  apply eq_to_eqPost
  exact liftR_refl _

private theorem hybrid1_eq_hybrid2
    {PKey SKey Key EKey Plain Cipher : Type}
    [Fintype Key] [Nonempty Key]
    [Fintype EKey] [Nonempty EKey]
    [Fintype Cipher] [Nonempty Cipher]
    (KEM : KEMScheme PKey SKey Key EKey)
    (DEM : DEMScheme Key Plain Cipher)
    (nullPlain : Plain)
    (m : Plain)
    (hDEM : PerfectDEM_CPA DEM nullPlain) :
    rHoare eqPre (HybridGame1 KEM DEM m) (HybridGame2 KEM DEM nullPlain m) eqPost := by
  intro h₁ h₂ hheq
  simp only [eqPre] at hheq
  subst hheq
  have h_prog_eq : (HybridGame1 KEM DEM m) h₁ = (HybridGame2 KEM DEM nullPlain m) h₁ := by
    have h1 : (HybridGame1 KEM DEM m) h₁ =
        (KEM.kgen h₁).bind (fun ⟨⟨pk, _sk⟩, h⟩ =>
          (KEM.encap pk h).bind (fun ⟨⟨_, ek⟩, h'⟩ =>
            ((DEM_CPA_real DEM m) h').bind (fun ⟨cipher, h''⟩ =>
              SDistr.pure ((pk, ek, cipher), h'')))) := by
      unfold HybridGame1 DEM_CPA_real
      simp only [SPComp.monad_bind_eq, SPComp.bind_def, SDistr.bind_assoc]
      bind_align
      simp [SPComp.pure, SDistr.pure_bind]
    have h2 : (HybridGame2 KEM DEM nullPlain m) h₁ =
        (KEM.kgen h₁).bind (fun ⟨⟨pk, _sk⟩, h⟩ =>
          (KEM.encap pk h).bind (fun ⟨⟨_, ek⟩, h'⟩ =>
            ((DEM_CPA_ideal DEM nullPlain m) h').bind (fun ⟨cipher, h''⟩ =>
              SDistr.pure ((pk, ek, cipher), h'')))) := by
      unfold HybridGame2 DEM_CPA_ideal
      simp only [SPComp.monad_bind_eq, SPComp.bind_def, SDistr.bind_assoc]
      bind_align
      simp [SPComp.pure, SDistr.pure_bind]
    have hdem_eq_all : ∀ h, (DEM_CPA_real DEM m) h = (DEM_CPA_ideal DEM nullPlain m) h := by
      intro h
      exact liftR_eq_implies_eq (eqPost_to_eq ((hDEM m) h h rfl))
    rw [h1, h2]
    congr 1; funext ⟨⟨pk, sk⟩, h⟩
    simp only []
    congr 1; funext ⟨⟨kval, ek⟩, h'⟩
    simp only []
    rw [hdem_eq_all h']
  rw [h_prog_eq]
  apply eq_to_eqPost
  exact liftR_refl _

private theorem hybrid2_eq_pke_ideal
    {PKey SKey Key EKey Plain Cipher : Type}
    [Fintype Key] [Nonempty Key]
    [Fintype EKey] [Nonempty EKey]
    [Fintype Cipher] [Nonempty Cipher]
    (KEM : KEMScheme PKey SKey Key EKey)
    (DEM : DEMScheme Key Plain Cipher)
    (nullPlain : Plain)
    (m : Plain)
    (hKEM : PerfectKEM_CPA KEM) :
    rHoare eqPre (HybridGame2 KEM DEM nullPlain m) (PKE_CPA_ideal (HybridPKE KEM DEM) nullPlain m) eqPost := by
  intro h₁ h₂ hheq
  simp only [eqPre] at hheq
  subst hheq
  have hkem_eq_all : ∀ h, (KEM_CPA_real KEM) h = (KEM_CPA_ideal KEM) h := by
    intro h
    exact liftR_eq_implies_eq (eqPost_to_eq (hKEM h h rfl))
  have h_prog_eq : (HybridGame2 KEM DEM nullPlain m) h₁ = (PKE_CPA_ideal (HybridPKE KEM DEM) nullPlain m) h₁ := by
    have h1 : (HybridGame2 KEM DEM nullPlain m) h₁ =
        (KEM_CPA_ideal KEM h₁).bind (fun ⟨⟨pk, ek, k⟩, h⟩ =>
          SDistr.pure ((pk, ek, DEM.enc k nullPlain), h)) := by
      unfold HybridGame2 KEM_CPA_ideal
      simp only [SPComp.monad_bind_eq, SPComp.bind_def, SDistr.bind_assoc]
      bind_align
      simp [SPComp.pure, SDistr.pure_bind]
    have h2 : (PKE_CPA_ideal (HybridPKE KEM DEM) nullPlain m) h₁ =
        (KEM_CPA_real KEM h₁).bind (fun ⟨⟨pk, ek, k⟩, h⟩ =>
          SDistr.pure ((pk, ek, DEM.enc k nullPlain), h)) := by
      unfold PKE_CPA_ideal HybridPKE KEM_CPA_real
      simp only [SPComp.monad_bind_eq, SPComp.bind_def, SDistr.bind_assoc]
      bind_align
      simp [SPComp.pure, SDistr.pure_bind]
    rw [h1, h2, hkem_eq_all h₁]
  rw [h_prog_eq]
  apply eq_to_eqPost
  exact liftR_refl _

/-- **Perfect KEM-DEM security**: if the KEM and DEM are perfectly secure, then
the hybrid PKE is perfectly secure. Proved by transitivity through the hybrid
games `PKE_real ≈ Hybrid1 ≈ Hybrid2 ≈ PKE_ideal`. -/
theorem pke_perfect_security
    {PKey SKey Key EKey Plain Cipher : Type}
    [Fintype Key] [Nonempty Key]
    [Fintype EKey] [Nonempty EKey]
    [Fintype Cipher] [Nonempty Cipher]
    (KEM : KEMScheme PKey SKey Key EKey)
    (DEM : DEMScheme Key Plain Cipher)
    (nullPlain : Plain)
    (hKEM : PerfectKEM_CPA KEM)
    (hDEM : PerfectDEM_CPA DEM nullPlain)
    : PerfectPKE_CPA (HybridPKE KEM DEM) nullPlain := by
  intro m
  apply rHoare_trans _ (HybridGame1 KEM DEM m)
  · exact pke_real_eq_hybrid1 KEM DEM m hKEM
  · apply rHoare_trans _ (HybridGame2 KEM DEM nullPlain m)
    · exact hybrid1_eq_hybrid2 KEM DEM nullPlain m hDEM
    · exact hybrid2_eq_pke_ideal KEM DEM nullPlain m hKEM

/-! ## XOR-DEM Instantiation: Perfect Security

The one-time-pad DEM over `Bool` (`enc k m = k ⊕ m`) is perfectly DEM-secure:
encrypting the real message and encrypting the null message `false` are both
uniform over the sampled key, so they couple through the XOR bijection
(`Prob/XorBij`). Composed with any perfectly-secure KEM, the hybrid PKE has
advantage exactly `0`.
-/

/-- The XOR (one-time-pad) DEM over `Bool`: `enc k m = k ⊕ m`, `dec k c = k ⊕ c`. -/
def BoolXorDEM : DEMScheme Bool Bool Bool where
  enc := fun k m => xor k m
  dec := fun k c => xor k c

/-- The XOR DEM is correct: `dec k (enc k m) = m`. -/
theorem boolXorDEM_correct : BoolXorDEM.Correct := by
  simp [BoolXorDEM, DEMScheme.Correct]

/-- **The XOR DEM is perfectly DEM-secure** (null message `false`).

For every message `m`, encrypting `m` and encrypting `false` under a uniform key
are equidistributed: mapping the real key `k` to `k ⊕ m` is a bijection
(`boolXorBij`) under which the real ciphertext `k ⊕ m` equals the ideal
ciphertext `(k ⊕ m) ⊕ false`. -/
theorem boolXorDEM_perfect : PerfectDEM_CPA BoolXorDEM false := by
  intro m
  simp only [DEM_CPA_real, DEM_CPA_ideal, BoolXorDEM, SPComp.monad_bind_eq,
    SPComp.monad_pure_eq]
  ssprove_couple_bij (boolXorBij m)

/-- **Perfect hybrid PKE from the XOR DEM**: composing any perfectly-secure KEM
with the one-time-pad DEM over `Bool` yields a perfectly-secure hybrid PKE —
every distinguisher has advantage exactly `0`. -/
theorem xorHybrid_perfect_security
    {PKey SKey EKey : Type}
    [Fintype EKey] [Nonempty EKey]
    (KEM : KEMScheme PKey SKey Bool EKey)
    (hKEM : PerfectKEM_CPA KEM) :
    PerfectPKE_CPA (HybridPKE KEM BoolXorDEM) false :=
  pke_perfect_security KEM BoolXorDEM false hKEM boolXorDEM_perfect

/-- The XOR-hybrid PKE is perfectly indistinguishable, so **every adversary's
distinguishing advantage is exactly `0`**. -/
theorem xorHybrid_advantage_zero
    {PKey SKey EKey : Type}
    [Fintype EKey] [Nonempty EKey]
    (KEM : KEMScheme PKey SKey Bool EKey)
    (hKEM : PerfectKEM_CPA KEM)
    (m : Bool)
    (A : PKey × EKey × Bool → SPComp Bool) :
    PKE_CPA_Advantage (HybridPKE KEM BoolXorDEM) false m A = 0 :=
  advantage_zero_of_rHoare _ _ (xorHybrid_perfect_security KEM hKEM m) A

end CatCrypt.Examples.KEMDEM
