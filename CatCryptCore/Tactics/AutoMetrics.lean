/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoArms
public import CatCryptCore.Crypto.SDist
public import CatCryptCore.Crypto.Advantage
public import CatCryptCore.Tactics.Triangle

/-!
# The standard distances of `hop_chain`

Imports the modules that register with `@[hop_metric]`
(`CatCryptCore.Tactics.AutoHopRegistry`) the triangle and symmetry lemmas of the three
distances of game proofs, each beside its lemmas:

* `sdist` (`sdist_triangle`, `sdist_sym`) in `CatCryptCore.Crypto.SDist`;
* `Advantage` (`advantage_triangle`, `Advantage_sym`) in `CatCryptCore.Crypto.Advantage`;
* `AdvantageA` at a fixed adversary (`advantageA_triangle`, `AdvantageA_sym`) in
  `CatCryptCore.Tactics.Triangle`.

The module registers nothing.
-/
