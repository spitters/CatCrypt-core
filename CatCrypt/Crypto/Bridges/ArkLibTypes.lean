/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Core.Code
import CatCrypt.Crypto.Advantage
import CatCrypt.Crypto.SDist
import CatCrypt.Prob.SDistr

/-!
# ArkLib Bridge Types

Shared types and bridge lemmas for connecting CatCrypt's computational security
framework with ArkLib's Interactive Oracle Reduction (IOR) framework.

## Overview

ArkLib (Verified-zkEVM/ArkLib) formalizes IORs for SNARK verification:
```
IOR ──BCS(commitment)──▶ IR ──Fiat-Shamir(ROM)──▶ Non-interactive argument
```

This file defines abstract soundness predicates that mirror ArkLib's
`Security/Basic.lean`, plus reduction composition lemmas.

## Main definitions

* `ArgumentSoundness` — all adversaries succeed with prob ≤ ε
* `KnowledgeSoundness` — ∃ universal extractor. ∀ adversary. extraction fails ≤ ε
* Reduction composition: `argumentSoundness_reduce`, `argumentSoundness_add_reduce`,
  `argumentSoundness_amplify`

## Design Notes

* ArkLib uses `ℝ≥0` (NNReal) for error bounds; CatCrypt uses `ℝ≥0∞` (ENNReal).
  The coercion `(↑· : ℝ≥0 → ℝ≥0∞)` is monotone, so bounds transfer.
* `KnowledgeSoundness` uses ∃E ∀A (universal extractor) matching ArkLib's form.

## References

* [Ben-Sasson, Chiesa, Spooner — Interactive Oracle Proofs, TCC 2016]
* [Verified-zkEVM/ArkLib — Security/Basic.lean]
-/

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

namespace CatCrypt.Crypto.Bridges.ArkLib

/-! ## Abstract Soundness Predicates -/

/-- Abstract soundness: all adversaries succeed with prob ≤ ε.
    Mirrors ArkLib's `Verifier.soundness`. -/
def ArgumentSoundness {Adv : Type} (ε : ℝ≥0∞)
    (game : Adv → SPComp Bool) : Prop :=
  ∀ A, prTrue (game A) Heap.empty ≤ ε

/-- Knowledge soundness with **universal** extractor: ∃E ∀A.
    Matches ArkLib's `Verifier.knowledgeSoundness` quantifier order.
    Stronger than the per-adversary form (∀A ∃E). -/
def KnowledgeSoundness {Adv Extractor : Type} (ε : ℝ≥0∞)
    (game : Adv → Extractor → SPComp Bool) : Prop :=
  ∃ E, ∀ A, prTrue (game A E) Heap.empty ≤ ε

/-- Weak knowledge soundness: per-adversary extractor (∀A ∃E).
    Strictly weaker than `KnowledgeSoundness`. -/
def WeakKnowledgeSoundness {Adv Extractor : Type} (ε : ℝ≥0∞)
    (game : Adv → Extractor → SPComp Bool) : Prop :=
  ∀ A, ∃ E, prTrue (game A E) Heap.empty ≤ ε

/-- Universal extractor implies per-adversary extractor. -/
theorem KnowledgeSoundness.toWeak {Adv Extractor : Type} {ε : ℝ≥0∞}
    {game : Adv → Extractor → SPComp Bool}
    (h : KnowledgeSoundness ε game) : WeakKnowledgeSoundness ε game :=
  fun A => ⟨h.choose, h.choose_spec A⟩

/-! ## Monotonicity -/

@[aesop safe apply]
theorem argumentSoundness_mono {Adv : Type} {g : Adv → SPComp Bool}
    {ε₁ ε₂ : ℝ≥0∞} (h : ε₁ ≤ ε₂) (hs : ArgumentSoundness ε₁ g) :
    ArgumentSoundness ε₂ g :=
  fun A => le_trans (hs A) h

theorem knowledgeSoundness_mono {Adv Extractor : Type}
    {g : Adv → Extractor → SPComp Bool}
    {ε₁ ε₂ : ℝ≥0∞} (h : ε₁ ≤ ε₂) (hs : KnowledgeSoundness ε₁ g) :
    KnowledgeSoundness ε₂ g :=
  ⟨hs.choose, fun A => le_trans (hs.choose_spec A) h⟩

/-! ## Reduction Composition

These lemmas are the workhorses for composing security proofs across
the SNARK pipeline. They replace axioms with hypothesis-taking theorems
where the user provides concrete reduction functions and bounds. -/

/-- Reduction composition: if game B reduces to game A via `reduce`,
    then soundness of A implies soundness of B. -/
@[aesop safe apply]
theorem argumentSoundness_reduce {Adv₁ Adv₂ : Type}
    {game₁ : Adv₁ → SPComp Bool} {game₂ : Adv₂ → SPComp Bool}
    (ε : ℝ≥0∞) (reduce : Adv₂ → Adv₁)
    (h_reduce : ∀ A, prTrue (game₂ A) Heap.empty ≤ prTrue (game₁ (reduce A)) Heap.empty)
    (h : ArgumentSoundness ε game₁) :
    ArgumentSoundness ε game₂ :=
  fun A => le_trans (h_reduce A) (h (reduce A))

/-- Additive composition via reductions: game reduces to sum of two sub-games.
    This captures BCS-style composition (IOR error + binding error). -/
@[aesop safe apply]
theorem argumentSoundness_add_reduce {Adv Adv₁ Adv₂ : Type}
    {game : Adv → SPComp Bool} {game₁ : Adv₁ → SPComp Bool} {game₂ : Adv₂ → SPComp Bool}
    {ε₁ ε₂ : ℝ≥0∞}
    (reduce₁ : Adv → Adv₁) (reduce₂ : Adv → Adv₂)
    (h_sum : ∀ A, prTrue (game A) Heap.empty ≤
      prTrue (game₁ (reduce₁ A)) Heap.empty + prTrue (game₂ (reduce₂ A)) Heap.empty)
    (h₁ : ArgumentSoundness ε₁ game₁)
    (h₂ : ArgumentSoundness ε₂ game₂) :
    ArgumentSoundness (ε₁ + ε₂) game :=
  fun A => le_trans (h_sum A) (add_le_add (h₁ _) (h₂ _))

/-- Multiplicative amplification via reduction: game reduces to q copies
    of a sub-game. This captures Fiat-Shamir-style amplification. -/
@[aesop safe apply]
theorem argumentSoundness_amplify {Adv₁ Adv₂ : Type}
    {game₁ : Adv₁ → SPComp Bool} {game₂ : Adv₂ → SPComp Bool}
    {ε : ℝ≥0∞} (q : ℝ≥0∞)
    (reduce : Adv₂ → Adv₁)
    (h_amp : ∀ A, prTrue (game₂ A) Heap.empty ≤ q * prTrue (game₁ (reduce A)) Heap.empty)
    (h : ArgumentSoundness ε game₁) :
    ArgumentSoundness (q * ε) game₂ :=
  fun A => le_trans (h_amp A) (by gcongr; exact h _)

/-! ## NNReal ↔ ENNReal Bridge

ArkLib uses `ℝ≥0` (NNReal) for error bounds. These lemmas convert
ArkLib-style NNReal bounds to CatCrypt's ENNReal bounds. -/

/-- Transfer an NNReal bound to ENNReal. -/
theorem argumentSoundness_coe {Adv : Type} {game : Adv → SPComp Bool}
    {ε : NNReal} (h : ∀ A, prTrue (game A) Heap.empty ≤ (↑ε : ℝ≥0∞)) :
    ArgumentSoundness (↑ε : ℝ≥0∞) game := h

#print axioms argumentSoundness_mono
#print axioms argumentSoundness_reduce
#print axioms argumentSoundness_add_reduce
#print axioms argumentSoundness_amplify

end CatCrypt.Crypto.Bridges.ArkLib
