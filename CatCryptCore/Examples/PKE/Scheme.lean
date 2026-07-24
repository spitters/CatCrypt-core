/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Core.Code
import CatCryptCore.Crypto.Advantage
import CatCryptCore.Crypto.HybridArgument
import CatCryptCore.Relational.Rules

/-!
# Abstract Public-Key Encryption Scheme and CPA Games

This file defines an abstract public-key encryption (PKE) scheme and the
CPA$ security games, following the framework from "Mechanizing Nested Hybrid
Arguments" (Larsen & Schurmann, CSF 2025, Fig. 5).

## Overview

The CPA$ game (ciphertext indistinguishability) has two variants:
- **Real** (b = true): Encrypt the queried message
- **Ideal** (b = false): Return a random ciphertext

This is equivalent to the standard IND-CPA definition but more convenient
for hybrid arguments, as each encryption query can be independently switched.

## Main Definitions

* `PKEScheme` - Abstract PKE scheme record
* `OT_CPA_real` / `OT_CPA_ideal` - One-time CPA$ games (single query)
* `OT_CPA_Advantage` - One-time CPA$ advantage
* `MT_CPA_real` / `MT_CPA_ideal` - Many-time CPA$ games (q queries)
* `hybrid_game` - Hybrid game indexed by switch position
* `MT_CPA_bound` - Main reduction: MT-CPA advantage ≤ q * OT-CPA advantage

## References

* [Larsen & Schurmann, Mechanizing Nested Hybrid Arguments, CSF 2025, Fig. 5-9]
* [Bellare et al., Relations Among Notions of Security for PKE]
-/

namespace CatCrypt.Examples.PKE

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.HybridArgument
open scoped ENNReal

/-! ## PKE Scheme Definition -/

/-- Abstract public-key encryption scheme.

    Following the CSF 2025 paper (Fig. 5):
    - `keygen` produces a (secret key, public key) pair
    - `enc` encrypts a message under a public key (probabilistic)
    - `dec` decrypts a ciphertext under a secret key
    - `sampleCip` samples a random ciphertext (for the ideal CPA$ game) -/
structure PKEScheme where
  /-- Secret key type -/
  SK : Type
  /-- Public key type -/
  PK : Type
  /-- Message type -/
  M : Type
  /-- Ciphertext type -/
  C : Type
  /-- Secret keys are finite -/
  [finSK : Fintype SK]
  /-- Secret keys are nonempty -/
  [neSK : Nonempty SK]
  /-- Public keys are finite -/
  [finPK : Fintype PK]
  /-- Public keys are nonempty -/
  [nePK : Nonempty PK]
  /-- Messages are finite -/
  [finM : Fintype M]
  /-- Messages are nonempty -/
  [neM : Nonempty M]
  /-- Ciphertexts are finite -/
  [finC : Fintype C]
  /-- Ciphertexts are nonempty -/
  [neC : Nonempty C]
  /-- Probabilistic key generation -/
  keygen : SPComp (SK × PK)
  /-- Probabilistic encryption -/
  enc : PK → M → SPComp C
  /-- Decryption (may fail) -/
  dec : SK → C → SPComp (Option M)
  /-- Random ciphertext sampling (for CPA$ ideal game) -/
  sampleCip : SPComp C

attribute [instance] PKEScheme.finSK PKEScheme.neSK PKEScheme.finPK PKEScheme.nePK
  PKEScheme.finM PKEScheme.neM PKEScheme.finC PKEScheme.neC

variable (P : PKEScheme)

/-! ## Correctness -/

/-- Perfect correctness: decryption always recovers the message. -/
def PKEScheme.Correct : Prop :=
  ∀ (h : Heap) (sk : P.SK) (pk : P.PK) (m : P.M) (c : P.C) (h' : Heap),
    (c, h') ∈ (P.enc pk m h).support →
      ∀ (result : Option P.M) (h'' : Heap),
        (result, h'') ∈ (P.dec sk c h').support → result = some m

/-! ## One-Time CPA$ Games -/

/-- One-time CPA$ real game: encrypt the message under the public key. -/
noncomputable def OT_CPA_real (pk : P.PK) (m : P.M) : SPComp P.C :=
  P.enc pk m

/-- One-time CPA$ ideal game: return a random ciphertext. -/
noncomputable def OT_CPA_ideal (_pk : P.PK) (_m : P.M) : SPComp P.C :=
  P.sampleCip

/-- One-time CPA$ advantage for a fixed public key and message. -/
noncomputable def OT_CPA_Advantage (pk : P.PK) (m : P.M)
    (A : P.C → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (OT_CPA_real P pk m) (OT_CPA_ideal P pk m) A

/-! ## Hybrid Games (SLIDE Construction)

    The hybrid game at index `i` samples random ciphertexts for positions `< i`
    and encrypts the real message for positions `≥ i`. This is the SLIDE construction
    from the CSF 2025 paper (Fig. 9).

    We define this recursively with an explicit position counter. -/

/-- Helper: process messages with position counter.
    For position `j`: if `j < i` then sample random, else encrypt. -/
noncomputable def hybridLoop (pk : P.PK) (i : ℕ) :
    ℕ → List P.M → SPComp (List P.C)
  | _, [] => SPComp.pure []
  | j, m :: ms => do
    let c ← if j < i then P.sampleCip else P.enc pk m
    let cs ← hybridLoop pk i (j + 1) ms
    SPComp.pure (c :: cs)

/-- Hybrid game: first `i` ciphertexts are random, remaining are encrypted.

    - `hybrid_game pk msgs 0` = all encrypted (real game)
    - `hybrid_game pk msgs msgs.length` = all random (ideal game) -/
noncomputable def hybrid_game (pk : P.PK) (msgs : List P.M) (i : ℕ) :
    SPComp (List P.C) :=
  hybridLoop P pk i 0 msgs

/-! ## Many-Time CPA$ Games

    The many-time game allows `q` encryption queries (one per message in the list).
    These are defined recursively to match `hybridLoop`'s structure. -/

/-- Many-time CPA$ real game: encrypt all messages under the public key. -/
noncomputable def MT_CPA_real (pk : P.PK) : List P.M → SPComp (List P.C)
  | [] => SPComp.pure []
  | m :: ms => do
    let c ← P.enc pk m
    let cs ← MT_CPA_real pk ms
    SPComp.pure (c :: cs)

/-- Many-time CPA$ ideal game: return random ciphertexts for all queries. -/
noncomputable def MT_CPA_ideal : List P.M → SPComp (List P.C)
  | [] => SPComp.pure []
  | _ :: ms => do
    let c ← P.sampleCip
    let cs ← MT_CPA_ideal ms
    SPComp.pure (c :: cs)

/-- Many-time CPA$ advantage. -/
noncomputable def MT_CPA_Advantage (pk : P.PK) (msgs : List P.M)
    (A : List P.C → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (MT_CPA_real P pk msgs) (MT_CPA_ideal P msgs) A

/-! ## Boundary Conditions -/

/-- Helper: hybridLoop with threshold 0 equals MT_CPA_real. -/
private theorem hybridLoop_zero_eq_real (pk : P.PK) (j : ℕ) (msgs : List P.M) :
    hybridLoop P pk 0 j msgs = MT_CPA_real P pk msgs := by
  induction msgs generalizing j with
  | nil => simp [hybridLoop, MT_CPA_real]
  | cons m ms ih =>
    simp only [hybridLoop, Nat.not_lt_zero, ↓reduceIte, MT_CPA_real]
    congr 1; funext c
    rw [ih (j + 1)]

/-- Boundary: hybrid at 0 = all encrypted (real game). -/
theorem hybrid_game_zero (pk : P.PK) (msgs : List P.M) :
    hybrid_game P pk msgs 0 = MT_CPA_real P pk msgs := by
  unfold hybrid_game
  exact hybridLoop_zero_eq_real P pk 0 msgs

/-- Helper: hybridLoop at full length equals MT_CPA_ideal. -/
private theorem hybridLoop_length_eq_ideal (pk : P.PK) (j : ℕ) (msgs : List P.M) :
    hybridLoop P pk (j + msgs.length) j msgs = MT_CPA_ideal P msgs := by
  induction msgs generalizing j with
  | nil => simp [hybridLoop, MT_CPA_ideal]
  | cons m ms ih =>
    simp only [hybridLoop, List.length_cons, MT_CPA_ideal]
    have hlt : j < j + (ms.length + 1) := by omega
    simp only [hlt, ↓reduceIte]
    congr 1; funext c
    rw [show j + (ms.length + 1) = (j + 1) + ms.length from by omega, ih (j + 1)]

/-- Boundary: hybrid at length = all random (ideal game). -/
theorem hybrid_game_length (pk : P.PK) (msgs : List P.M) :
    hybrid_game P pk msgs msgs.length = MT_CPA_ideal P msgs := by
  unfold hybrid_game
  rw [show msgs.length = 0 + msgs.length from by omega]
  exact hybridLoop_length_eq_ideal P pk 0 msgs

/-! ## Adjacent Hybrid Lemmas -/

/-! ### Key structural lemma: adjacent hybrids differ only at position i.

    For positions `j < i`: both games sample random (identical).
    For position `j = i`: game i encrypts, game i+1 samples random.
    For positions `j > i`: both games encrypt (identical).

    This means the advantage between adjacent hybrids reduces to a single
    OT-CPA$ query at position i. -/

/-- Helper: hybridLoop agrees on positions where the condition is the same. -/
private theorem hybridLoop_agree_prefix (pk : P.PK) (i j : ℕ) (msgs : List P.M)
    (hj : j + msgs.length ≤ i) :
    hybridLoop P pk i j msgs = hybridLoop P pk (i + 1) j msgs := by
  induction msgs generalizing j with
  | nil => simp [hybridLoop]
  | cons m ms ih =>
    simp only [hybridLoop, List.length_cons] at hj ⊢
    have hlt_i : j < i := by omega
    have hlt_i1 : j < i + 1 := by omega
    simp only [hlt_i, hlt_i1, ↓reduceIte]
    congr 1; funext c
    rw [ih (j + 1) (by omega)]

/-- Helper: hybridLoop agrees on positions after the switch point. -/
private theorem hybridLoop_agree_suffix (pk : P.PK) (i j : ℕ) (msgs : List P.M)
    (hj : i < j) :
    hybridLoop P pk i j msgs = hybridLoop P pk (i + 1) j msgs := by
  induction msgs generalizing j with
  | nil => simp [hybridLoop]
  | cons m ms ih =>
    simp only [hybridLoop]
    have hlt_i : ¬(j < i) := by omega
    have hlt_i1 : ¬(j < i + 1) := by omega
    simp only [hlt_i, hlt_i1, ↓reduceIte]
    congr 1; funext c
    rw [ih (j + 1) (by omega)]

/-! ## Pure PKE Schemes -/

/-- A PKE scheme is pure if its encryption and random ciphertext sampling
    don't depend on or modify the heap. -/
structure PKEScheme.IsPure (P : PKEScheme) : Prop where
  enc_isPure : ∀ pk m, SPComp.IsPure (P.enc pk m)
  sampleCip_isPure : SPComp.IsPure P.sampleCip

/-! ## IsPure for Many-Time Games -/

/-- Many-time CPA$ real game is pure when the scheme is pure. -/
theorem MT_CPA_real_isPure (hP : P.IsPure) (pk : P.PK) :
    ∀ msgs : List P.M, SPComp.IsPure (MT_CPA_real P pk msgs)
  | [] => SPComp.pure_isPure []
  | m :: ms => by
    show SPComp.IsPure (SPComp.bind (P.enc pk m) fun c =>
      SPComp.bind (MT_CPA_real P pk ms) fun cs => SPComp.pure (c :: cs))
    exact SPComp.bind_isPure (hP.enc_isPure pk m) (fun c =>
      SPComp.bind_isPure (MT_CPA_real_isPure hP pk ms) (fun cs =>
        SPComp.pure_isPure (c :: cs)))

/-- Many-time CPA$ ideal game is pure when the scheme is pure. -/
theorem MT_CPA_ideal_isPure (hP : P.IsPure) :
    ∀ msgs : List P.M, SPComp.IsPure (MT_CPA_ideal P msgs)
  | [] => SPComp.pure_isPure []
  | _ :: ms => by
    show SPComp.IsPure (SPComp.bind P.sampleCip fun c =>
      SPComp.bind (MT_CPA_ideal P ms) fun cs => SPComp.pure (c :: cs))
    exact SPComp.bind_isPure hP.sampleCip_isPure (fun c =>
      SPComp.bind_isPure (MT_CPA_ideal_isPure hP ms) (fun cs =>
        SPComp.pure_isPure (c :: cs)))

/-- The hybrid game is pure when the scheme is pure. -/
theorem hybridLoop_isPure (hP : P.IsPure) (pk : P.PK) (i j : ℕ) :
    ∀ msgs : List P.M, SPComp.IsPure (hybridLoop P pk i j msgs)
  | [] => SPComp.pure_isPure []
  | m :: ms => by
    simp only [hybridLoop, SPComp.monad_bind_eq]
    split <;> exact SPComp.bind_isPure
      (by first | exact hP.sampleCip_isPure | exact hP.enc_isPure pk m)
      (fun c => SPComp.bind_isPure (hybridLoop_isPure hP pk i (j + 1) ms)
        (fun cs => SPComp.pure_isPure (c :: cs)))

theorem hybrid_game_isPure (hP : P.IsPure) (pk : P.PK) (msgs : List P.M) (i : ℕ) :
    SPComp.IsPure (hybrid_game P pk msgs i) :=
  hybridLoop_isPure P hP pk i 0 msgs

/-! ## Main Reduction Theorem -/

/-- **Many-time to one-time CPA$ reduction** (CSF 2025, Theorem 1).

    The many-time CPA$ advantage is bounded by `q * ε` where `q = msgs.length`
    and ε bounds each per-step hybrid advantage.

    This uses the general `advantage_hybrid_uniform` theorem from
    `HybridArgument.lean`. -/
theorem MT_CPA_bound (pk : P.PK) (msgs : List P.M)
    (A : List P.C → SPComp Bool) (ε : ℝ≥0∞)
    (hstep : ∀ i, i < msgs.length →
      AdvantageA (hybrid_game P pk msgs i) (hybrid_game P pk msgs (i + 1)) A ≤ ε) :
    MT_CPA_Advantage P pk msgs A ≤ msgs.length * ε := by
  unfold MT_CPA_Advantage
  rw [← hybrid_game_zero P pk msgs, ← hybrid_game_length P pk msgs]
  exact advantage_hybrid_uniform (hybrid_game P pk msgs) A msgs.length ε hstep

/-- **Many-time to one-time CPA$ reduction with dependent bounds**.

    When per-step bounds differ, the total advantage is bounded by their sum. -/
theorem MT_CPA_dep_bound (pk : P.PK) (msgs : List P.M)
    (A : List P.C → SPComp Bool) (ε : ℕ → ℝ≥0∞)
    (hstep : ∀ i, i < msgs.length →
      AdvantageA (hybrid_game P pk msgs i) (hybrid_game P pk msgs (i + 1)) A ≤ ε i) :
    MT_CPA_Advantage P pk msgs A ≤ ∑ i ∈ Finset.range msgs.length, ε i := by
  unfold MT_CPA_Advantage
  rw [← hybrid_game_zero P pk msgs, ← hybrid_game_length P pk msgs]
  exact advantage_hybrid_dep_bound
    (hybrid_game P pk msgs 0) (hybrid_game P pk msgs msgs.length)
    (hybrid_game P pk msgs) A msgs.length ε rfl rfl hstep

/-- **Perfect security for many-time CPA$**: when all hybrid steps are
    perfectly indistinguishable, the many-time advantage is 0. -/
theorem MT_CPA_perfect (pk : P.PK) (msgs : List P.M)
    (hperf : ∀ i, i < msgs.length →
      rHoare eqPre (hybrid_game P pk msgs i) (hybrid_game P pk msgs (i + 1)) eqPost)
    (A : List P.C → SPComp Bool) :
    MT_CPA_Advantage P pk msgs A = 0 := by
  unfold MT_CPA_Advantage
  rw [← hybrid_game_zero P pk msgs, ← hybrid_game_length P pk msgs]
  exact advantage_hybrid_zero (hybrid_game P pk msgs) msgs.length hperf A

end CatCrypt.Examples.PKE
