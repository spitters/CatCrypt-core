/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoDispatch
public import CatCryptCore.XDijkstra.Rel.XCombinedAutomation
public import CatCryptCore.XDijkstra.XMvcgenReg

/-!
# `catcrypt_auto` shapes and arms for the XDijkstra judgments and zero advantage

Registrations with the registry of `CatCryptCore.Tactics.AutoDispatchCore`: shapes of the
direct stage, read on the goal as stated before the normalisation, each with its arms.
When every arm of the direct stage fails, the normalised stage of `catcrypt_auto` runs;
on a hybrid advantage goal its arms include `hop_chain`.

| Shape | Detected head | Arms, in order |
|---|---|---|
| coupling | `XRelTripleQ0 _ _ _ _`, `RelSpecTriple _ _ _ _` | `relmvcgen!?` |
| hybrid advantage | `AdvantageA _ _ _ ≤ _` | `advmvcgen!?`; `advmvcgen_dep` with the leaf cascade of `advmvcgen!?` |
| zero advantage | `AdvantageA _ _ _ = 0`, possibly under `∀ A` | `prob_to_rHoare`; `advantage_zero_of_rHoare` with `catcrypt_auto` on the `rHoare` premise |
| extended triple | mentions `XTriple`, `XPT` or `XRelTriple` | `xmvcgen!`, then `omega`, `le_rfl`, `assumption`, `simp_all` or `grind` on each residual |

The registrations are active where this module is imported.
-/

public section

catcrypt_auto_shape "coupling" direct priority 100 :=
  any [app CatCrypt.XDijkstra.XRelTripleQ0, app CatCrypt.XDijkstra.RelSpecTriple]

catcrypt_auto_shape "hybrid advantage" direct priority 90 :=
  arg LE.le/4 at 2 (app CatCrypt.Crypto.AdvantageA)

catcrypt_auto_shape "zero advantage" direct priority 80 :=
  any [arg Eq/3 at 1 (app CatCrypt.Crypto.AdvantageA),
    under_forall (arg Eq/3 at 1 (app CatCrypt.Crypto.AdvantageA))]

catcrypt_auto_shape "extended triple" direct priority 70 :=
  mentions [CatCrypt.XDijkstra.XTriple, CatCrypt.XDijkstra.XPT, CatCrypt.XDijkstra.XRelTriple]

catcrypt_auto_arm "coupling" order 10 := "relmvcgen!?"

catcrypt_auto_arm "hybrid advantage" order 10 := "advmvcgen!?"
catcrypt_auto_arm "hybrid advantage" order 20 :=
  "(advmvcgen_dep <;> (try (first | assumption | exact le_rfl | gcongr | norm_num | grind)))"

catcrypt_auto_arm "zero advantage" order 10 := "prob_to_rHoare"
catcrypt_auto_arm "zero advantage" order 20 :=
  "first
    | exact CatCrypt.Crypto.advantage_zero_of_rHoare _ _ (by catcrypt_auto) _
    | (intro _; exact CatCrypt.Crypto.advantage_zero_of_rHoare _ _ (by catcrypt_auto) _)"

catcrypt_auto_arm "extended triple" order 10 :=
  "(xmvcgen! <;> (first | omega | exact le_rfl | assumption | (simp_all; done) | grind))"
