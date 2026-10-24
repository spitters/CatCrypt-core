/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoBase
public import CatCryptCore.Tactics.AutoSets
public import CatCryptCore.Tactics.BindVcgen
public import CatCryptCore.Tactics.BindSwap
public import CatCryptCore.Tactics.Triangle
public import CatCryptCore.Crypto.SDist

/-!
# `catcrypt_auto` with the arms of the automation sets

The dispatcher `catcrypt_auto` (`CatCryptCore.Tactics.AutoDispatchCore`) with the
registrations of the modules this module imports: the shapes and the Lean-core arms of
`CatCryptCore.Tactics.AutoBase`, the arms of `CatCryptCore.Tactics.AutoArms`,
`CatCryptCore.Tactics.BindSwap` (`advantage_eq_nf`, `bind_swap_nf`) and
`CatCryptCore.Tactics.BindVcgen` (`bind_vcgen`), the distances `sdist`, `Advantage` and
`AdvantageA` registered with `@[hop_metric]` in `CatCryptCore.Crypto.SDist`,
`CatCryptCore.Crypto.Advantage` and `CatCryptCore.Tactics.Triangle`, and the sets and arms
of `CatCryptCore.Tactics.AutoSets`. The module registers nothing. The arms of the
normalised stage, in order:

| Shape | Arms, in order |
|---|---|
| `*` (each non-proof term argument `t`) | `exact t`; `apply t <;> (first \| assumption \| catcrypt_grind)` |
| side condition | `aesop` over `CatCryptRel`; `solve_by_elim` over the `IsPure` and the `NoFail` combinators |
| relational | `aesop` over `CatCryptRel`; `ssprove_crypto`; `ssprove_crypto_grind` |
| distance inequality | `hop_chain`; `sum_atoms_le`; `gcongr <;> catcrypt_grind`; `catcrypt_grind`; `bound` (a quarter of the budget; skipped when a `∀`-quantified inequality is in context) |
| monotonicity | `gcongr_unfold`; `gcongr`; `gcongr <;> catcrypt_grind`; `sum_atoms_le` (on `≤`); `simp_all`; `grind` |
| advantage equality | `advantage_eq_nf [p₁, …]` |
| heap read | `grind [Heap.get_set_same, Heap.get_set_other]` |
| game equality | `bind_swap_nf [p₁, …]`; `catcrypt_grind`; `bind_vcgen` |
| other | `sum_atoms_le` (on `≤`); `simp_all`; `grind` |
| premises | `solve_by_elim [p₁, …]` |
-/

