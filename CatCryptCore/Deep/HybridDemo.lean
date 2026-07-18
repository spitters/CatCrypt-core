/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Deep.Package

/-!
# Hybrid Argument Demonstration using Deep Embedding

This file demonstrates how the deep embedding of CatCrypt enables cleaner and more
structured hybrid argument proofs in cryptography.

## Overview

A hybrid argument is a proof technique where we show two games are equivalent by
constructing a sequence of intermediate games:

    Game0 ~ Game1 ~ Game2 ~ ... ~ GameN

where each adjacent pair differs in a small, analyzable way. The deep embedding
provides several advantages for such proofs:

1. **Structural Induction**: We can analyze games by their syntactic structure
   using `RawCode.inductionOn`, rather than semantic simulation.

2. **Separation Reasoning**: The location set structure provides automatic
   reasoning about disjoint state through `DeepPackage.sep`.

3. **Compositional Reasoning**: Package composition (`link`, `par`) preserves
   separation properties.

## Comparison with Shallow Embedding

In the **shallow embedding** (standard CatCrypt), games are represented as
Lean functions. Proving equivalence requires manual tracking of state invariants,
explicit coupling constructions, and complex simulation arguments.

In the **deep embedding**, games are syntax trees that allow structural induction
on syntax, automatic support/disjointness reasoning, and compositional separation
properties.

## References

* [Larsen and Schürmann, *Nominal State-Separating Proofs*](https://eprint.iacr.org/2025/598)
* [Haselwarter et al., *SSProve: A Foundational Framework for Modular
  Cryptographic Proofs in Coq*](https://doi.org/10.1145/3594735)
* SSProve Rocq: `theories/Crypt/examples/PRF_example.v`
-/

namespace CatCrypt.Deep.HybridDemo

open CatCrypt.Deep
open CatCrypt.Core

/-! ## Example Interfaces -/

/-- Simple interface with one operation: query : Unit -> Nat -/
def queryInterface : DeepInterface :=
  ⟨[(0, Unit, Nat)]⟩

/-! ## Behavioral Equivalence -/

/-- Behavioral equivalence of deep packages based on export interface equality.

    In a full development, this would compare implementations via denotational
    semantics. Here we use a simplified definition based on exports. -/
def BehavioralEquiv (p₁ p₂ : DeepPackage) : Prop :=
  p₁.exports = p₂.exports

notation:50 p₁ " ≈ᵇ " p₂ => BehavioralEquiv p₁ p₂

/-! ## Transitivity of Equivalence -/

/-- Behavioral equivalence is reflexive -/
theorem BehavioralEquiv.refl (p : DeepPackage) : p ≈ᵇ p := rfl

/-- Behavioral equivalence is symmetric -/
theorem BehavioralEquiv.symm {p₁ p₂ : DeepPackage} (h : p₁ ≈ᵇ p₂) : p₂ ≈ᵇ p₁ :=
  Eq.symm h

/-- Behavioral equivalence is transitive -/
theorem BehavioralEquiv.trans {p₁ p₂ p₃ : DeepPackage}
    (h₁₂ : p₁ ≈ᵇ p₂) (h₂₃ : p₂ ≈ᵇ p₃) : p₁ ≈ᵇ p₃ :=
  Eq.trans h₁₂ h₂₃

/-! ## Separation Properties Demo -/

/-- Demonstration: two packages with disjoint location ids are separated. -/
theorem sep_of_disjoint_locs (p₁ p₂ : DeepPackage)
    (h : Disjoint p₁.locs p₂.locs) : DeepPackage.sep p₁ p₂ := h

/-- The empty package is separated from any package -/
example (p : DeepPackage) : DeepPackage.sep DeepPackage.empty p :=
  DeepPackage.sep_empty_left p

/-- Any package is separated from the empty package -/
example (p : DeepPackage) : DeepPackage.sep p DeepPackage.empty :=
  DeepPackage.sep_empty_right p

/-! ## Hybrid Sequence Structure -/

/-- A hybrid argument is a sequence of games with adjacent equivalences. -/
structure HybridSequence where
  /-- The games in the sequence -/
  games : List DeepPackage
  /-- Non-empty sequence -/
  nonempty : games ≠ []

/-- The first and last games in a hybrid sequence are equivalent
    if all adjacent pairs are equivalent.

    This is the key theorem for hybrid arguments: we can chain
    together local equivalences to get global equivalence. -/
theorem hybrid_transitivity (games : List DeepPackage) (h_nonempty : games ≠ [])
    (h_adj : ∀ i, i + 1 < games.length →
      games.getD i DeepPackage.empty ≈ᵇ games.getD (i+1) DeepPackage.empty) :
    games.head h_nonempty ≈ᵇ games.getLast h_nonempty := by
  induction games with
  | nil => exact absurd rfl h_nonempty
  | cons g gs ih =>
    cases gs with
    | nil => exact BehavioralEquiv.refl g
    | cons g' gs' =>
      have h_adj' : ∀ i, i + 1 < (g' :: gs').length →
        (g' :: gs').getD i DeepPackage.empty ≈ᵇ (g' :: gs').getD (i+1) DeepPackage.empty := by
        intro i hi
        have := h_adj (i+1) (by simp only [List.length_cons] at hi ⊢; omega)
        simp only [List.getD_cons_succ] at this
        exact this
      have h_first := h_adj 0 (by simp only [List.length_cons]; omega)
      simp only [List.getD_cons_zero, List.getD_cons_succ, List.getD_cons_zero] at h_first
      have h_rest := ih (List.cons_ne_nil g' gs') h_adj'
      simp only [List.head_cons] at h_rest ⊢
      exact BehavioralEquiv.trans h_first h_rest

/-! ## Documentation: Benefits of Deep Embedding for Hybrid Arguments

### Key Advantages

1. **Explicit Syntax Trees**
   - Games are data structures, not opaque functions
   - We can pattern match on code structure
   - Transformations are explicit and verifiable

2. **Structural Induction**
   - `RawCode.inductionOn` provides a principled way to analyze all code paths
   - No need for complex simulation relations
   - Proof follows the syntax structure

3. **Separation via Location Sets**
   - `DeepPackage.sep p1 p2` captures state disjointness
   - Composition preserves separation (`par_sep_left`, `par_sep_right`)

4. **Compositional Reasoning**
   - Link and parallel composition have algebraic properties
   - Separation is compositional

### Comparison: Shallow vs Deep

| Aspect | Shallow | Deep |
|--------|---------|------|
| Games | Functions | Syntax trees |
| Equivalence | Coupling/simulation | Structural + semantic |
| State separation | Manual invariants | Automatic via `sep` |
| Induction | Semantic domain | Syntax structure |

### When to Use Deep Embedding

The deep embedding is particularly beneficial when:
- The proof involves multiple games with similar structure
- State separation is a key reasoning principle
- You want to apply program transformations

For simple proofs where semantic reasoning suffices, the shallow
embedding may be more direct.

-/

end CatCrypt.Deep.HybridDemo
