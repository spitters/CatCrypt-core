/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Deep.Package
import Mathlib.Tactic.SimpRw

/-!
# Tactics for Deep Embedding Reasoning

This file provides tactics for working with the deep embedding of
CatCrypt computations, particularly for separation reasoning.

## Main definitions

* `sep_solve` - Tactic for solving separation goals (`DeepPackage.sep p₁ p₂`)
* `disj_solve` - Tactic for solving disjointness goals

## Usage

```lean
-- Proving separation of packages
example (p₁ p₂ : DeepPackage) (h : Disjoint p₁.locs p₂.locs) : DeepPackage.sep p₁ p₂ := by sep_solve
```

## References

* [Larsen and Schürmann, *Nominal State-Separating Proofs*](https://eprint.iacr.org/2025/598)
* SSProve Rocq: `theories/Crypt/Package.v` (package tactics)
-/

namespace CatCrypt

open CatCrypt.Deep

/-! ## Separation tactic -/

/-- Tactic for solving separation goals.

    The `sep_solve` tactic attempts to prove goals of the form `DeepPackage.sep p₁ p₂`
    (i.e., `Disjoint p₁.locs p₂.locs`) by:

    1. Unfolding `sep` to `Disjoint` on location sets
    2. Simplifying location set definitions
    3. Using `Finset.disjoint_*` lemmas

    **Example:**
    ```lean
    example (p : DeepPackage) : DeepPackage.sep DeepPackage.empty p := by sep_solve
    ``` -/
macro "sep_solve" : tactic => `(tactic|
  first
  | exact DeepPackage.sep_empty_left _
  | exact DeepPackage.sep_empty_right _
  | simp only [DeepPackage.sep, DeepPackage.empty,
               Finset.disjoint_empty_left, Finset.disjoint_empty_right] <;>
    first
    | trivial
    | decide
    | assumption
    | (apply Finset.disjoint_left.mpr; intro a ha hb; simp_all)
    | (apply Finset.disjoint_right.mpr; intro a ha hb; simp_all)
  | assumption)

/-! ## Disjointness tactic -/

/-- Tactic for solving disjointness goals on location sets.

    The `disj_solve` tactic attempts to prove goals of the form
    `Disjoint s₁ s₂` for finite sets of Nats by:

    1. Converting to membership conditions
    2. Numeric reasoning with omega

    **Example:**
    ```lean
    example (s : Finset Nat) : Disjoint ∅ s := by disj_solve
    ``` -/
macro "disj_solve" : tactic => `(tactic|
  first
  | exact Finset.disjoint_empty_left _
  | exact Finset.disjoint_empty_right _
  | (rw [Finset.disjoint_iff_ne]; intro a ha b hb heq; subst heq; omega)
  | (apply disjoint_comm.mp; exact Finset.disjoint_empty_left _)
  | (apply disjoint_comm.mp; exact Finset.disjoint_empty_right _)
  | assumption)

/-! ## Combined automation -/

/-- Combined tactic for separation and disjointness reasoning.

    The `sep_auto` tactic combines separation and disjointness
    automation to handle common goals in CatCrypt proofs.

    It tries, in order:
    1. `sep_solve` for separation goals
    2. `disj_solve` for disjointness goals
    3. General simplification and automation

    **Example:**
    ```lean
    example (p : DeepPackage) : DeepPackage.sep DeepPackage.empty p := by sep_auto
    ``` -/
macro "sep_auto" : tactic => `(tactic|
  first
  | sep_solve
  | disj_solve
  | (simp only [DeepPackage.sep, DeepPackage.empty,
                Finset.disjoint_empty_left, Finset.disjoint_empty_right,
                Finset.union_empty, Finset.empty_union] <;>
    first | trivial | decide | assumption | omega | aesop))

/-! ## Nominal Tactics -/

open CatCrypt.Nominal

/-- Tactic for solving atom separation goals.

    The `atom_sep_solve` tactic attempts to prove goals of the form
    `NomPackage.atomSep p₁ p₂` (i.e., `Disjoint p₁.atoms p₂.atoms`) by:

    1. Unfolding `atomSep` to `Disjoint` on atom sets
    2. Using `Finset.disjoint_*` lemmas
    3. Applying freshness reasoning

    **Example:**
    ```lean
    example (p : NomPackage) : NomPackage.atomSep NomPackage.empty p := by atom_sep_solve
    ``` -/
macro "atom_sep_solve" : tactic => `(tactic|
  first
  | exact NomPackage.atomSep_empty_left _
  | exact NomPackage.atomSep_empty_right _
  | simp only [NomPackage.atomSep, NomPackage.empty, NomPackage.atoms,
               Finset.disjoint_empty_left, Finset.disjoint_empty_right] <;>
    first
    | trivial
    | decide
    | assumption
  | assumption)

/-- Tactic for solving freshness goals.

    The `fresh_solve` tactic attempts to prove goals involving freshness
    of atoms for elements in nominal sets. It uses the `Fresh` predicate
    from the nominal sets library.

    **Example:**
    ```lean
    example (a : Atom) (s : Finset Atom) (h : a ∉ s) : Fresh a s := by fresh_solve
    ``` -/
macro "fresh_solve" : tactic => `(tactic|
  first
  | exact Atom.fresh_not_mem _
  | exact freshFor_not_in_supp_left _ _
  | exact freshFor_not_in_supp_right _ _
  | simp only [Fresh, NomSet.supp] <;> (first | assumption | decide)
  | assumption)

/-- Tactic for nominal separation automation.

    The `nom_auto` tactic combines nominal tactics to handle common
    goals in nominal CatCrypt proofs:

    1. Package separation (both location-based and atom-based)
    2. Disjointness of atom sets
    3. Freshness goals

    **Example:**
    ```lean
    example (p : NomPackage) : NomPackage.atomSep NomPackage.empty p := by nom_auto
    ``` -/
macro "nom_auto" : tactic => `(tactic|
  first
  | sep_solve
  | atom_sep_solve
  | fresh_solve
  | disj_solve
  | (simp only [NomPackage.atomSep, NomPackage.atoms, NomPackage.empty,
                DeepPackage.sep, DeepPackage.empty,
                Finset.disjoint_empty_left, Finset.disjoint_empty_right,
                Finset.union_empty, Finset.empty_union] <;>
    first | trivial | decide | assumption | omega | aesop))

/-! ## Documentation

### Tactic Summary

| Tactic | Purpose | Typical Goal |
|--------|---------|--------------|
| `sep_solve` | Prove package separation | `DeepPackage.sep p₁ p₂` |
| `disj_solve` | Prove set disjointness | `Disjoint s₁ s₂` |
| `sep_auto` | Combined automation | Any of the above |
| `atom_sep_solve` | Prove atom separation | `NomPackage.atomSep p₁ p₂` |
| `fresh_solve` | Prove freshness | `Fresh a x` |
| `nom_auto` | Full nominal automation | Any nominal goal |

### Key Lemmas Used

The tactics use these key lemmas:
- `DeepPackage.sep`: Package separation definition
- `DeepPackage.sep_empty_left`, `sep_empty_right`: Empty package separation
- `NomPackage.atomSep`: Atom-based separation
- `NomPackage.sep_of_atomSep`: Atom separation implies location separation
- `Finset.disjoint_*`: Finset disjointness lemmas
- `Fresh`, `freshFor`: Freshness predicates

### Integration with Hybrid Arguments

These tactics are designed to support hybrid argument proofs in cryptography.
The key workflow is:

1. Define a sequence of games as `DeepPackage` or `NomPackage` values
2. Use `sep_solve` or `atom_sep_solve` to show games have disjoint state
3. Use `nom_auto` for automatic nominal reasoning
4. Use structural induction on `RawCode` to relate game behaviors

-/

end CatCrypt
