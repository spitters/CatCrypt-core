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
public import CatCryptCore.Tactics.AutoMetrics

/-!
# `catcrypt_auto` with the arms of the automation sets

The dispatcher `catcrypt_auto` (`CatCryptCore.Tactics.AutoDispatchCore`) with the
registrations of `CatCryptCore.Tactics.AutoBase`, `CatCryptCore.Tactics.AutoArms`
(through `CatCryptCore.Tactics.AutoMetrics`, which also registers the distances `sdist`,
`Advantage` and `AdvantageA` with `@[hop_metric]`) and `CatCryptCore.Tactics.AutoSets`,
the shape `advantage equality` (an equality one of whose sides is an application of
`AdvantageA` or `Advantage`) with the arm `advantage_eq_nf`, and the arms `bind_swap_nf`
(`CatCryptCore.Tactics.BindSwap`) and `bind_vcgen` registered here. The arms of the
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

public section

catcrypt_auto_shape "advantage equality" priority 85 :=
  any [arg Eq/3 at 1 (app CatCrypt.Crypto.AdvantageA), arg Eq/3 at 1 (app CatCrypt.Crypto.Advantage),
    arg Eq/3 at 2 (app CatCrypt.Crypto.AdvantageA), arg Eq/3 at 2 (app CatCrypt.Crypto.Advantage)]

catcrypt_auto_arm "advantage equality" order 5 := "advantage_eq_nf%GRIND"
catcrypt_auto_arm "SPComp equality" order 5 := "bind_swap_nf%GRIND"
catcrypt_auto_arm "SPComp equality" order 20 := "bind_vcgen"
