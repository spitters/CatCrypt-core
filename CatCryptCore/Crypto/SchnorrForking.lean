/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.SchnorrSigma
public import CatCryptCore.Crypto.ForkingLemma

/-!
# Schnorr EUF-CMA → DL Reduction via Forking Lemma

This file provides a computationally meaningful reduction from Schnorr signature
forgery (EUF-CMA) to the Discrete Logarithm (DL) problem using the Forking Lemma.

## Overview

In the Random Oracle Model (ROM), the Fiat-Shamir hash H(m, a) is replaced by
a random oracle. A forger making a single hash query decomposes into:
1. **Coins**: Choose message m, commitment a (probabilistic)
2. **Respond**: Given challenge e from the oracle, compute response z (deterministic)

The forking algorithm replays the adversary with the same coins but a fresh
challenge, producing two accepting transcripts with different challenges.
Special soundness then extracts the discrete logarithm.

## Main Results

* `SchnorrROMForger` — Decomposed Schnorr forger for ROM model
* `schnorr_extract_dl` — Two ROM-accepting transcripts with different challenges yield DL
* `dlFromForking` — DL adversary via forking + special soundness extraction

## References

* `CatCrypt.Examples.Schnorr` for the underlying protocol and special soundness
* `CatCrypt.Crypto.ForkingLemma` for the general forking lemma
-/

@[expose] public section

namespace CatCrypt.Crypto.SchnorrForking

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Examples.Schnorr
open CatCrypt.Crypto.ForkingLemma
open scoped ENNReal

variable (gp : GroupParam)

/-! ## ROM-Model Verification -/

/-- Schnorr verification in the Random Oracle Model.
    Takes the challenge `e` as an explicit parameter (from the oracle)
    instead of computing it from a hash function. -/
def schnorrVerifyROM (pk : gp.G) (a : gp.G) (e z : gp.Scalar) : Bool :=
  schnorrVerifyGP gp pk (gp.scalarZero, a) e z

theorem schnorrVerifyROM_unfold (pk a : gp.G) (e z : gp.Scalar) :
    schnorrVerifyROM gp pk a e z = (gp.exp z == gp.groupMul a (gp.groupExp pk e)) := rfl

/-! ## Decomposed Forger -/

/-- A Schnorr ROM forger decomposed into a probabilistic coins phase and
    a deterministic respond phase. The coins produce internal state, message,
    and commitment `a`. The respond function computes the signature response `z`
    given the internal state and challenge `e`.

    This captures the structure of a Fiat-Shamir adversary making a single
    hash query `H(m, a)` to the random oracle. -/
structure SchnorrROMForger (gp : GroupParam) (MsgType : Type) (S : Type) where
  /-- Probabilistic phase: produce state, message, and commitment a -/
  coins : gp.G → SPComp (S × MsgType × gp.G)
  /-- Deterministic phase: given state and challenge e, produce response z -/
  respond : S → gp.Scalar → gp.Scalar

variable {gp}
variable {MsgType S : Type}

/-- Convert a SchnorrROMForger to a ForkableAdversary.

    The output type includes the commitment `a`, challenge `e`, and response `z`
    so that the acceptance predicate can check ROM verification. -/
noncomputable def SchnorrROMForger.toForkable (A : SchnorrROMForger gp MsgType S) :
    ForkableAdversary gp.G (S × MsgType × gp.G) gp.Scalar (gp.G × gp.Scalar × gp.Scalar) where
  coins := A.coins
  respond := fun _pk c e => (c.2.2, e, A.respond c.1 e)

/-- ROM acceptance predicate: checks Schnorr verification for a given public key. -/
def romAccept (gp : GroupParam) (pk : gp.G) : (gp.G × gp.Scalar × gp.Scalar) → Bool :=
  fun ⟨a, e, z⟩ => schnorrVerifyROM gp pk a e z

/-! ## Fork-to-Extraction Bridge -/

/-- Core extraction theorem: from two Schnorr ROM-accepting transcripts with the
    same commitment but different challenges, extract the discrete logarithm.

    Given:
    - `gp.exp z₁ = a · pk^e₁` (verification 1)
    - `gp.exp z₂ = a · pk^e₂` (verification 2)
    - `e₁ ≠ e₂`

    Then `pk = gp.exp((z₁ - z₂)/(e₁ - e₂))`, i.e., the discrete log is extracted.

    This is `GroupParam.exp_extract_eq` stated in terms of ROM verification. -/
theorem schnorr_extract_dl (pk a : gp.G) (e₁ e₂ z₁ z₂ : gp.Scalar)
    (hv₁ : schnorrVerifyROM gp pk a e₁ z₁ = true)
    (hv₂ : schnorrVerifyROM gp pk a e₂ z₂ = true)
    (hne : e₁ ≠ e₂) :
    pk = gp.exp (gp.scalarDiv (gp.scalarSub z₁ z₂) (gp.scalarSub e₁ e₂)) := by
  simp only [schnorrVerifyROM, schnorrVerifyGP, beq_eq_decide, decide_eq_true_eq] at hv₁ hv₂
  exact (gp.exp_extract_eq pk a e₁ e₂ z₁ z₂ hv₁ hv₂ hne).symm

/-- The extractor returns `some w` when challenges differ. -/
theorem schnorrExtractor_some (pk a : gp.G) (e₁ e₂ z₁ z₂ : gp.Scalar)
    (hne : e₁ ≠ e₂) :
    schnorrExtractor gp pk (gp.scalarZero, a) e₁ e₂ z₁ z₂ =
      some (gp.scalarDiv (gp.scalarSub z₁ z₂) (gp.scalarSub e₁ e₂)) := by
  simp [schnorrExtractor, beq_eq_decide, hne]

/-! ## DL Adversary Construction -/

/-- DL adversary constructed via forking + special soundness extraction.

    Given public key `pk`:
    1. Run the coins phase to get `(s, m, a)`
    2. Sample two independent challenges `e₁, e₂`
    3. Compute responses `z₁ = respond(s, e₁)` and `z₂ = respond(s, e₂)`
    4. If both verify and `e₁ ≠ e₂`: extract DL via `(z₁ - z₂)/(e₁ - e₂)`
    5. Otherwise: output a random scalar -/
noncomputable def dlFromForking (A : SchnorrROMForger gp MsgType S) :
    gp.G → SPComp gp.Scalar := fun pk => do
  let (s, _m, a) ← A.coins pk
  let e₁ ← SPComp.sample gp.Scalar
  let z₁ := A.respond s e₁
  let e₂ ← SPComp.sample gp.Scalar
  let z₂ := A.respond s e₂
  if schnorrVerifyROM gp pk a e₁ z₁ && schnorrVerifyROM gp pk a e₂ z₂ &&
      decide (e₁ ≠ e₂) then
    SPComp.pure (gp.scalarDiv (gp.scalarSub z₁ z₂) (gp.scalarSub e₁ e₂))
  else
    SPComp.sample gp.Scalar

/-- When the fork succeeds, the DL adversary extracts the correct discrete log.

    This connects the forking algorithm's success to correct DL extraction:
    if both ROM-verification checks pass and `e₁ ≠ e₂`, then the extracted
    scalar `w = (z₁ - z₂)/(e₁ - e₂)` satisfies `gp.exp w = pk`. -/
theorem dlFromForking_correct (A : SchnorrROMForger gp MsgType S)
    (pk a : gp.G) (s : S) (_m : MsgType) (e₁ e₂ : gp.Scalar)
    (hv₁ : schnorrVerifyROM gp pk a e₁ (A.respond s e₁) = true)
    (hv₂ : schnorrVerifyROM gp pk a e₂ (A.respond s e₂) = true)
    (hne : e₁ ≠ e₂) :
    gp.exp (gp.scalarDiv (gp.scalarSub (A.respond s e₁) (A.respond s e₂))
            (gp.scalarSub e₁ e₂)) = pk :=
  (schnorr_extract_dl pk a e₁ e₂ _ _ hv₁ hv₂ hne).symm

end CatCrypt.Crypto.SchnorrForking
