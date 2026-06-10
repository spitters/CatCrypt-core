/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Tactics.Basic
import CatCrypt.Tactics.Sync
import CatCrypt.Tactics.Invariant
import CatCrypt.Tactics.ProofFrog
import CatCrypt.Tactics.Restore
import CatCrypt.Tactics.LazySampling
import CatCrypt.Tactics.Conditional
import CatCrypt.Tactics.Call
import CatCrypt.Tactics.Proc
import CatCrypt.Tactics.WP
import CatCrypt.Tactics.RSpec
import CatCrypt.Tactics.Sim
import CatCrypt.Tactics.Auto
import CatCrypt.Tactics.SP
import CatCrypt.Tactics.LeOfSum
import CatCrypt.Tactics.BridgeGen
import CatCrypt.Tactics.SumCases
import CatCrypt.Tactics.SPNormalize
import CatCrypt.Tactics.Remember
import CatCrypt.Tactics.Triangle
import CatCrypt.Tactics.CryptoAuto

/-!
# CatCrypt Tactics Module

This module provides tactic automation for CatCrypt proofs.

## Submodules

* `CatCrypt.Tactics.Basic` - Basic tactics (ssprove_valid, ssprove_code_simpl)
* `CatCrypt.Tactics.Sync` - Synchronization tactics (ssprove_sync, ssprove_sync_eq)
* `CatCrypt.Tactics.Invariant` - Invariant tactics (ssprove_invariant, ssprove_restore)
* `CatCrypt.Tactics.ProofFrog` - ProofFrog-inspired automation (copy propagation, dead code elimination)
* `CatCrypt.Tactics.Restore` - Invariant restoration after put operations (ssprove_restore_pre, ssprove_restore_mem)
* `CatCrypt.Tactics.LazySampling` - Lazy/eager sampling infrastructure for PRF proofs
* `CatCrypt.Tactics.Proc` - Procedure unfolding (ssprove_proc)
* `CatCrypt.Tactics.WP` - Weakest precondition (ssprove_wp)
* `CatCrypt.Tactics.Sim` - Automated bisimulation (ssprove_sim)
* `CatCrypt.Tactics.Auto` - EasyCrypt-style auto (ssprove_auto_ec)
* `CatCrypt.Tactics.SP` - Strongest postcondition (ssprove_sp)
* `CatCrypt.Tactics.SumCases` - Sum-type case explosion (sum_cases, pkg_coherence_lite)
* `CatCrypt.Tactics.SPNormalize` - SPComp bind-chain normalization
* `CatCrypt.Tactics.Remember` - Remembered-value reasoning (ssprove_remember, ssprove_forget)
* `CatCrypt.Tactics.Triangle` - Advantage triangle-inequality chaining
* `CatCrypt.Tactics.CryptoAuto` - Crypto-goal automation on top of Auto

## Overview

The CatCrypt tactic library provides automation for:

### Code Validity
- `ssprove_valid` - Prove ValidCode goals for well-formed code
- `ssprove_code_simpl` - Simplify and normalize code expressions

### Relational Proofs
- `ssprove_sync` - Apply synchronous rules for matching operations
- `ssprove_sync_eq` - Synchronous rules with equality postconditions

### Invariant Reasoning
- `ssprove_invariant` - Prove invariant preservation
- `ssprove_restore` - Restore invariants after writes
- `ssprove_restore_pre` - Restore precondition after put operations (from set_lhs/set_rhs)
- `ssprove_restore_mem` - Restore precondition including remembered values

### EasyCrypt-Style Tactics
- `ssprove_proc [d₁, d₂, ...]` - Unfold game/oracle definitions (EasyCrypt's `proc`)
- `ssprove_wp` - Weakest precondition for deterministic tails (EasyCrypt's `wp`)
- `ssprove_sim` - Automated bisimulation for structural matching (EasyCrypt's `sim`)
- `ssprove_auto_ec` - Meta-tactic chaining wp + sync + skip (EasyCrypt's `auto`)

### Strongest Postcondition
- `ssprove_sp` - Process deterministic prefix forwards (EasyCrypt's `sp`)
- `ssprove_sp_step` - Process one sp step from the head

### One-Sided Sampling
- `ssprove_rnd_lhs` - Consume left-side sampling (EasyCrypt's `rnd{1}`)
- `ssprove_rnd_rhs` - Consume right-side sampling (EasyCrypt's `rnd{2}`)

### ProofFrog-Inspired Automation
- `ssprove_dead_code` - Eliminate unused computations (samples, gets, pure values)
- `ssprove_copy_propagate` - Substitute known values (e.g., after set/get)
- `ssprove_contract_all` - Apply all contraction rules (duplicate get/put elimination)
- `ssprove_canonicalize` - Normalize code structure (bind association, pure inlining)
- `ssprove_auto` - Apply all ProofFrog-style simplifications
- `ssprove_auto!` - Aggressive automation including sync rules

## Usage

Import this module to get access to all CatCrypt tactics:

```lean
import CatCrypt.Tactics

example : rHoare eqPre (sample α) (sample α) (fun a h₁ b h₂ => eqPre h₁ h₂ ∧ a = b) := by
  ssprove_sync
```

## See Also

* `CatCrypt.Tactic.Basic` - Lower-level pRHL tactics (rsame, rbind, etc.)

## References

* [Benton et al., *Nominal SSProve*](https://eprint.iacr.org/2025/598)
-/

namespace CatCrypt.Tactics

-- Re-export tactics from submodules
-- All tactics are available via the imports above

end CatCrypt.Tactics
