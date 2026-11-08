/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Assumptions.DDHSampledHops
import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
public import CatCryptCore.Tactics.StdCosts

/-!
# Running time of the DDH hop reductions

`derive_reduction` reflects `ddhRed₀` and `ddhRed` into computation trees and derives their
costed forms `R.tree.timed`, with the compilation theorems `R.compile_tree` and the erasure
theorems `R.tree.erase_timed`. The continuations (`k`, `pre`, `mid`) and the distinguisher `A`
are costed inputs with call-cost companions.

## Main results

With the continuation of time at most `K` and call cost at most `c`, and the distinguisher of
time at most `T` and call cost at most `a`:

* `ddhRed₀.tree.timeBound_timed` — time at most `K + c + T + a + 2`;
* `ddhRed.tree.timeBound_timed` — with `mid` of time at most `M` and call cost at most `m`,
  time at most `pre.time + (M + m + K + c + T + a + 3)`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Assumptions

open CatCrypt.Core

derive_reduction ddhRed

derive_reduction ddhRed₀

variable {W : Type} {α : Type} {K c T a : ℕ}

/-- **Time of the DH hop reduction with no prefix**: as `contRed.tree.timeBound_timed`. -/
theorem ddhRed₀.tree.timeBound_timed (k : W → W → W → SPTree.Timed α) (kCost : W → W → W → ℕ)
    (A : α → SPTree.Timed Bool) (ACost : α → ℕ) (hk : ∀ x y z, (k x y z).time ≤ K)
    (hkc : ∀ x y z, kCost x y z ≤ c) (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a)
    (ga gb z : W) :
    SPTree.Timed.stepTime (ddhRed₀.tree.timed k kCost A ACost ga gb z) ≤
      K + c + T + a + 2 := by
  unfold ddhRed₀.tree.timed
  rw [SPTree.Timed.stepTime_delay]
  have h := SPTree.Timed.stepTime_bind_le (k ga gb z) (fun x => (1 + ACost x, A x)) (T + a + 1)
    fun x => by simp only [SPTree.Timed.stepTime]; have := hA x; have := hAc x; omega
  have := hk ga gb z; have := hkc ga gb z; omega

/-- **Time of the DH hop reduction**: the prefix `pre`, one call of `mid` of time at most `M`
and call cost at most `m`, then the continuation and `A` as in
`contRed.tree.timeBound_timed`. -/
theorem ddhRed.tree.timeBound_timed {P Q : Type} (pre : SPTree.Timed P)
    (mid : P → W → SPTree.Timed Q) (midCost : P → W → ℕ) (k : P → Q → W → W → W → SPTree.Timed α)
    (kCost : P → Q → W → W → W → ℕ) (A : α → SPTree.Timed Bool) (ACost : α → ℕ) {M m : ℕ}
    (hm : ∀ p y, (mid p y).time ≤ M) (hmc : ∀ p y, midCost p y ≤ m)
    (hk : ∀ p q x y z, (k p q x y z).time ≤ K) (hkc : ∀ p q x y z, kCost p q x y z ≤ c)
    (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a) (ga gb z : W) :
    SPTree.Timed.stepTime (ddhRed.tree.timed pre mid midCost k kCost A ACost ga gb z) ≤
      pre.time + (M + m + K + c + T + a + 3) := by
  unfold ddhRed.tree.timed
  refine SPTree.Timed.stepTime_bind_le pre _ _ fun p => ?_
  rw [SPTree.Timed.stepTime_delay]
  have h := SPTree.Timed.stepTime_bind_le (mid p gb)
    (fun q => SPTree.Timed.delay (1 + kCost p q ga gb z)
      ((k p q ga gb z).bind fun x => (1 + ACost x, A x))) (K + c + T + a + 2) fun q => by
    rw [SPTree.Timed.stepTime_delay]
    have h' := SPTree.Timed.stepTime_bind_le (k p q ga gb z) (fun x => (1 + ACost x, A x))
      (T + a + 1) fun x => by
        simp only [SPTree.Timed.stepTime]; have := hA x; have := hAc x; omega
    have := hk p q ga gb z; have := hkc p q ga gb z; omega
  have := hm p gb; have := hmc p gb; omega

end CatCrypt.Crypto.Assumptions
