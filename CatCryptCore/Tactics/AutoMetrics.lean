/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoArms
public import CatCryptCore.Crypto.SDist
public import CatCryptCore.Crypto.Advantage

/-!
# The standard distances of `hop_chain`

Registers with `@[hop_metric]` (`CatCryptCore.Tactics.AutoArms`) the triangle and
symmetry lemmas of the three distances of game proofs:

* `sdist` (`sdist_triangle`, `sdist_sym`);
* `Advantage` (`advantage_triangle`, `Advantage_sym`);
* `AdvantageA` at a fixed adversary (`advantageA_triangle`, `AdvantageA_sym`).

`catcrypt_auto` imports this module, so its `hop_chain` arm covers these distances.
-/

public section

open CatCrypt.Crypto

attribute [hop_metric] sdist_triangle sdist_sym advantage_triangle Advantage_sym
  advantageA_triangle AdvantageA_sym
