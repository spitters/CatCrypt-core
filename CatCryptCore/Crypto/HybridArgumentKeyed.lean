/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.HybridArgument
public import CatCryptCore.Crypto.SPCompPMF
public import CatCryptCore.Crypto.UCOracleGame

/-!
# The hybrid argument for keyed games

For a sequence of keyed games `K i` over the same oracle interface, the advantage of an oracle
adversary `B` between `K 0` and `K n` is at most the sum of its advantages between neighbouring
games. The acceptance probability of `B` in a keyed game is the probability of `true` of a
heap-independent game (`KeyedGame.acceptGame`), so the bound is the hybrid argument
`HybridArgument.advantage_hybrid_dep_bool` for these games.

## Main results

* `KeyedGame.acceptGame`, `KeyedGame.advantage_eq_advantage_acceptGame` — the acceptance of `B`
  as a game, and the advantage of keyed games as the advantage of these games.
* `KeyedGame.advantage_hybrid` — the hybrid argument for keyed games.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent.KeyedGame

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

variable {Q A : Type}

/-- The output bit of the adversary `B` in the keyed game `G`, as a heap-independent game. -/
noncomputable def acceptGame (G : KeyedGame Q A) (B : OracleAdv Q A Bool) : SPComp Bool :=
  liftPMF (G.keyDist.bind fun k => (OracleAdv.run (G.oracle k) B G.init).map Prod.fst)

/-- The advantage of `B` between two keyed games is the advantage between its acceptance
games. -/
theorem advantage_eq_advantage_acceptGame (G₀ G₁ : KeyedGame Q A) (B : OracleAdv Q A Bool) :
    advantage G₀ G₁ B = Advantage (G₀.acceptGame B) (G₁.acceptGame B) := by
  unfold advantage Advantage acceptGame
  rw [prTrue_liftPMF, prTrue_liftPMF]
  rfl

/-- **The hybrid argument for keyed games.** The advantage of `B` between `K 0` and `K n` is at
most the sum of its advantages between `K i` and `K (i + 1)` for `i < n`. -/
theorem advantage_hybrid (K : ℕ → KeyedGame Q A) (B : OracleAdv Q A Bool) (n : ℕ) :
    advantage (K 0) (K n) B ≤ ∑ i ∈ Finset.range n, advantage (K i) (K (i + 1)) B := by
  simp only [advantage_eq_advantage_acceptGame]
  exact HybridArgument.advantage_hybrid_dep_bool (fun i => (K i).acceptGame B) n

end CatCrypt.Crypto.UCTransparent.KeyedGame
