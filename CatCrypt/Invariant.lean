/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Invariant.Basic
import CatCrypt.Invariant.Coupling
import CatCrypt.Invariant.SemiInvariant
import CatCrypt.Invariant.PerfectIndist

/-!
# Invariant System

This module provides the invariant system infrastructure for CatCrypt.
Invariants are predicates on heap pairs used for proving perfect indistinguishability.

## Main submodules

* `CatCrypt.Invariant.Basic` - Basic invariant definitions
* `CatCrypt.Invariant.Coupling` - Location couplings (syncs, rem_lhs, rem_rhs)
* `CatCrypt.Invariant.SemiInvariant` - Semi-invariants and combination
* `CatCrypt.Invariant.PerfectIndist` - Perfect indistinguishability lemmas

## Usage

The typical workflow for proving `G₀ ≈₀ G₁`:

1. Choose an invariant (often `heapEq`, `heapIgnore L`, or custom)
2. Apply `eq_rel_perf_ind` with the invariant
3. For each procedure:
   - Use `simplify_eq_rel` to get relational judgments
   - Use pRHL rules and location couplings to prove them

## References

* [Benton et al., *Nominal CatCrypt*](https://eprint.iacr.org/2025/598)
-/

namespace CatCrypt.Invariant

-- The submodules define things in the CatCrypt.Invariant namespace directly,
-- so we don't need exports. They are all available via the imports.

end CatCrypt.Invariant
