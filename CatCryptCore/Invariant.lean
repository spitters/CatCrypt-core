/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Invariant.Basic
import CatCryptCore.Invariant.Coupling
import CatCryptCore.Invariant.SemiInvariant
import CatCryptCore.Invariant.EqUpToInv

/-!
# Invariant System

This module provides the invariant system infrastructure for CatCrypt.
Invariants are predicates on heap pairs used for relational reasoning about
packages.

## Main submodules

* `CatCrypt.Invariant.Basic` - Basic invariant definitions
* `CatCrypt.Invariant.Coupling` - Location couplings (syncs, rem_lhs, rem_rhs)
* `CatCrypt.Invariant.SemiInvariant` - Semi-invariants and combination
* `CatCrypt.Invariant.EqUpToInv` - equality up to an invariant (`eq_up_to_inv`)

## Usage

To relate two packages up to an invariant:

1. Choose an invariant (often `heapEq`, `heapIgnore L`, or custom)
2. Establish `eq_up_to_inv` via `simplify_eq_rel_intro`
3. For each procedure, discharge the `rHoare` judgment with pRHL rules and
   location couplings

A security bound (a zero or bounded `Advantage`) is proved in the deep embedding:
`DeepNomAdvantage` / `NomPkgSecure` in `CatCrypt.Crypto.NomAdvantage`.

## References

* [Larsen and Schürmann, *Nominal State-Separating Proofs*](https://eprint.iacr.org/2025/598)
-/

namespace CatCrypt.Invariant

-- The submodules define things in the CatCrypt.Invariant namespace directly,
-- so we don't need exports. They are all available via the imports.

end CatCrypt.Invariant
