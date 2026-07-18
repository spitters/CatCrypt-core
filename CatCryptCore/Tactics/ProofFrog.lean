/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Lean
import CatCryptCore.Relational.Rules
import CatCryptCore.Tactics.Basic
import CatCryptCore.Tactics.Sync

/-!
# ProofFrog-Inspired Tactics

This file provides tactics inspired by ProofFrog's automatic game transformations.
ProofFrog is a Python-based cryptographic proof verifier that uses AST canonicalization
and SMT solving for automatic equivalence proofs.

## Main Tactics

* `ssprove_copy_propagate` - Substitute known values for variables
* `ssprove_dead_code` - Eliminate unused computations
* `ssprove_unreachable` - Prove unreachable code paths
* `ssprove_canonicalize` - Put code into canonical form
* `ssprove_auto_pf` - Apply all ProofFrog-style simplifications

## Comparison with ProofFrog

| Feature | ProofFrog | CatCrypt (these tactics) |
|---------|-----------|-------------------------|
| Inlining | Automatic | `ssprove_code_simpl` |
| Copy propagation | Automatic | `ssprove_copy_propagate` |
| Dead code elimination | Automatic | `ssprove_dead_code` |
| Unreachable code | Z3 | `ssprove_unreachable` (decide/omega) |
| Canonicalization | AST-based | `ssprove_canonicalize` |

## Implementation Notes

Unlike ProofFrog which operates on ASTs externally, these tactics work within
Lean's type system. This provides full soundness guarantees but requires
explicit lemmas for each transformation.

## References

* ProofFrog: https://prooffrog.github.io/ (source: https://github.com/ProofFrog/ProofFrog)
* [Barbosa et al., "Mechanizing Proofs about Adversaries"]
-/

initialize Lean.registerTraceClass `ssprove.tactics

namespace CatCrypt.Tactics

open Lean Elab Tactic Meta
open CatCrypt.Relational CatCrypt.Core CatCrypt.Prob

/-! ## Dead Code Elimination

These tactics eliminate computations whose results are not used.
-/

/-- `ssprove_dead_sample_lhs` eliminates an unused sample on the left side.

Rewrites `let _ ← sample α; k` to `k` when the sample result is not used.

Example:
```
theorem example : rHoare Φ (do let _ ← SPComp.sample Bool; k) c₂ Ψ := by
  ssprove_dead_sample_lhs
  -- Goal is now: rHoare Φ k c₂ Ψ
```
-/
macro "ssprove_dead_sample_lhs" : tactic => `(tactic| (
  apply rHoare_rewrite_lhs
  · rw [dead_sample]
))

/-- `ssprove_dead_sample_rhs` eliminates an unused sample on the right side. -/
macro "ssprove_dead_sample_rhs" : tactic => `(tactic| (
  apply rHoare_rewrite_rhs
  · rw [dead_sample]
))

/-- `ssprove_dead_get_lhs` eliminates an unused get on the left side.

Rewrites `let _ ← get l; k` to `k` when the get result is not used.
-/
macro "ssprove_dead_get_lhs" : tactic => `(tactic| (
  apply rHoare_rewrite_lhs
  · rw [dead_get]
))

/-- `ssprove_dead_get_rhs` eliminates an unused get on the right side. -/
macro "ssprove_dead_get_rhs" : tactic => `(tactic| (
  apply rHoare_rewrite_rhs
  · rw [dead_get]
))

/-- `ssprove_dead_pure_lhs` eliminates an unused pure on the left side.

Rewrites `let _ ← pure v; k` to `k`.
-/
macro "ssprove_dead_pure_lhs" : tactic => `(tactic| (
  apply rHoare_rewrite_lhs
  · rw [dead_pure]
))

/-- `ssprove_dead_pure_rhs` eliminates an unused pure on the right side. -/
macro "ssprove_dead_pure_rhs" : tactic => `(tactic| (
  apply rHoare_rewrite_rhs
  · rw [dead_pure]
))

/-- `ssprove_dead_code` attempts to eliminate all dead code on both sides.

This tactic repeatedly applies dead code elimination rules until no more
simplifications are possible. It handles:
- Unused samples
- Unused gets
- Unused pure values

Example:
```
theorem example : rHoare Φ
    (do let _ ← SPComp.sample Bool; let _ ← SPComp.get l; k)
    (do let _ ← SPComp.sample Nat; k')
    Ψ := by
  ssprove_dead_code
  -- Goal is now: rHoare Φ k k' Ψ
```
-/
macro "ssprove_dead_code" : tactic => `(tactic| (
  repeat (first
    | ssprove_dead_sample_lhs
    | ssprove_dead_sample_rhs
    | ssprove_dead_get_lhs
    | ssprove_dead_get_rhs
    | ssprove_dead_pure_lhs
    | ssprove_dead_pure_rhs
  )
))

/-! ## Copy Propagation

These tactics substitute known values for variables, propagating
information from earlier computations to later uses.
-/

/-- `ssprove_copy_propagate_get_lhs` propagates a known value from get.

After `x ← get l`, if we know the heap value at `l`, we can substitute
that value for `x` in subsequent code.

Currently implemented as a rewrite using `get_value_eq`.
-/
macro "ssprove_copy_propagate_get_lhs" : tactic => `(tactic| (
  conv => arg 2; rw [get_value_eq]
))

/-- `ssprove_copy_propagate_get_rhs` propagates a known value on the right side. -/
macro "ssprove_copy_propagate_get_rhs" : tactic => `(tactic| (
  conv => arg 3; rw [get_value_eq]
))

/-- `ssprove_copy_propagate_set_get_lhs` propagates the set value to subsequent get.

After `set l v`, a `get l` returns `v`. This tactic combines set and get
into the known value.
-/
macro "ssprove_copy_propagate_set_get_lhs" : tactic => `(tactic| (
  apply rHoare_rewrite_lhs
  · rw [set_get_same]
))

/-- `ssprove_copy_propagate_set_get_rhs` propagates on the right side. -/
macro "ssprove_copy_propagate_set_get_rhs" : tactic => `(tactic| (
  apply rHoare_rewrite_rhs
  · rw [set_get_same]
))

/-- `ssprove_copy_propagate` attempts to propagate all known values.

This tactic combines:
1. Propagating set values to subsequent gets
2. Inlining pure values via pure_bind
3. Simplifying with known equalities

Example:
```
theorem example : rHoare Φ
    (do SPComp.set l 42; let x ← SPComp.get l; f x)
    c₂ Ψ := by
  ssprove_copy_propagate
  -- Goal uses f 42 instead of f x
```
-/
macro "ssprove_copy_propagate" : tactic => `(tactic| (
  repeat (first
    | ssprove_copy_propagate_set_get_lhs
    | ssprove_copy_propagate_set_get_rhs
    | (apply rHoare_rewrite_lhs; rw [SPComp.pure_bind])
    | (apply rHoare_rewrite_rhs; rw [SPComp.pure_bind])
  )
))

/-! ## Unreachable Code Detection

These tactics identify and eliminate unreachable code paths using
Lean's decision procedures.
-/

/-- `ssprove_unreachable` proves a goal when the precondition is false.

This handles cases where the precondition is contradictory, meaning
the code path is unreachable.

Example:
```
theorem example : rHoare (fun _ _ => False) c₁ c₂ Ψ := by
  ssprove_unreachable
```
-/
macro "ssprove_unreachable" : tactic => `(tactic| (
  first
  | apply rHoare_false
  | (intro h₁ h₂ hFalse; exact False.elim hFalse)
  | (intro h₁ h₂ hFalse; omega)
  | (intro h₁ h₂ hFalse; simp_all)
))

/-- `ssprove_unreachable_branch` eliminates an unreachable if-branch.

When an if-condition is provably false, the else branch is taken.
-/
macro "ssprove_unreachable_branch_lhs" : tactic => `(tactic| (
  apply rHoare_rewrite_lhs
  · simp only [ite_false, ite_true, decide_True, decide_False]
))

macro "ssprove_unreachable_branch_rhs" : tactic => `(tactic| (
  apply rHoare_rewrite_rhs
  · simp only [ite_false, ite_true, decide_True, decide_False]
))

/-! ## Canonicalization

These tactics put code into a canonical form for easier comparison
and automated reasoning.
-/

/-- `ssprove_canonicalize_lhs` puts the left-side code into canonical form.

Canonical form has:
1. Binds associated to the right: `((a >>= f) >>= g)` → `(a >>= (f >=> g))`
2. Pure values inlined: `pure x >>= f` → `f x`
3. Trivial binds removed: `a >>= pure` → `a`
-/
macro "ssprove_canonicalize_lhs" : tactic => `(tactic| (
  repeat (apply rHoare_rewrite_lhs; first
    | rw [bind_assoc_lr]
    | rw [pure_bind_lr]
    | rw [bind_pure_lr]
  )
))

/-- `ssprove_canonicalize_rhs` puts the right-side code into canonical form. -/
macro "ssprove_canonicalize_rhs" : tactic => `(tactic| (
  repeat (apply rHoare_rewrite_rhs; first
    | rw [bind_assoc_lr]
    | rw [pure_bind_lr]
    | rw [bind_pure_lr]
  )
))

/-- `ssprove_canonicalize` puts both sides into canonical form. -/
macro "ssprove_canonicalize" : tactic => `(tactic| (
  ssprove_canonicalize_lhs
  ssprove_canonicalize_rhs
))

/-! ## Contract Rules (Enhanced)

Enhanced versions of contract rules that combine multiple optimizations.
-/

/-- `ssprove_contract_all_lhs` applies all contraction rules on the left side.

This combines:
- Duplicate get elimination
- Duplicate put elimination
- Put-get contraction
-/
macro "ssprove_contract_all_lhs" : tactic => `(tactic| (
  repeat (first
    | ssprove_contract_get_lhs
    | ssprove_contract_put_lhs
    | ssprove_contract_put_get_lhs
  )
))

/-- `ssprove_contract_all_rhs` applies all contraction rules on the right side. -/
macro "ssprove_contract_all_rhs" : tactic => `(tactic| (
  repeat (first
    | ssprove_contract_get_rhs
    | ssprove_contract_put_rhs
    | ssprove_contract_put_get_rhs
  )
))

/-- `ssprove_contract_all` applies all contraction rules on both sides. -/
macro "ssprove_contract_all" : tactic => `(tactic| (
  ssprove_contract_all_lhs
  ssprove_contract_all_rhs
))

/-! ## Comprehensive Automation

The main tactic that combines all ProofFrog-style optimizations.
-/

/-- `ssprove_auto_pf` applies all ProofFrog-style simplifications automatically.

The `_pf` suffix marks ProofFrog provenance, parallel to the `_ec` suffix on the
EasyCrypt automation verb `ssprove_auto_ec`; the two are distinct tactics.

This tactic performs the following optimizations in order:
1. Canonicalization (normalize bind structure)
2. Dead code elimination (remove unused computations)
3. Copy propagation (substitute known values)
4. Contraction (eliminate redundant operations)

After these optimizations, the goal should be in a normalized form
that makes equivalence proofs easier.

Example:
```
theorem game_equiv : rHoare eqPre
    (do let _ ← SPComp.sample Bool;  -- dead
        SPComp.set l 42;
        let x ← SPComp.get l;        -- copy propagate to 42
        let y ← SPComp.get l;        -- contract with previous get
        f x y)
    (do SPComp.set l 42;
        f 42 42)
    eqPost := by
  ssprove_auto_pf
  ssprove_sync_eq
```
-/
macro "ssprove_auto_pf" : tactic => `(tactic| (
  -- First canonicalize the structure
  try ssprove_canonicalize
  -- Eliminate dead code
  try ssprove_dead_code
  -- Propagate known values
  try ssprove_copy_propagate
  -- Contract redundant operations
  try ssprove_contract_all
  -- Simplify any remaining structure
  try ssprove_code_simpl
))

/-- `ssprove_auto_pf!` is a more aggressive version that also tries sync rules.

This adds:
- Attempting reflexivity for identical code
- Attempting sync rules for matching operations
- Using simp for remaining simplifications
-/
macro "ssprove_auto_pf!" : tactic => `(tactic| (
  ssprove_auto_pf
  first
  | (apply rHoare_refl)
  | ssprove_sync
  | ssprove_sync_eq
  | skip
))

/-! ## Game Transformation Helpers

These tactics help with common game transformation patterns.
-/

/-- `ssprove_inline_lhs` inlines a definition on the left side.

Use this when you want to expand a named computation for further
simplification.
-/
macro "ssprove_inline_lhs" def_name:ident : tactic => `(tactic| (
  apply rHoare_rewrite_lhs
  · unfold $def_name; rfl
))

/-- `ssprove_inline_rhs` inlines a definition on the right side. -/
macro "ssprove_inline_rhs" def_name:ident : tactic => `(tactic| (
  apply rHoare_rewrite_rhs
  · unfold $def_name; rfl
))

/-- `ssprove_rewrite_lhs` rewrites using an equality lemma on the left side. -/
macro "ssprove_rewrite_lhs" eq:term : tactic => `(tactic| (
  apply rHoare_rewrite_lhs
  · exact $eq
))

/-- `ssprove_rewrite_rhs` rewrites using an equality lemma on the right side. -/
macro "ssprove_rewrite_rhs" eq:term : tactic => `(tactic| (
  apply rHoare_rewrite_rhs
  · exact $eq
))

end CatCrypt.Tactics
