/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.SampledGame
import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
import CatCryptCore.Tactics.AutoTime
public import CatCryptCore.Tactics.AutoTime.Basic
public import CatCryptCore.Tactics.StdCosts

/-!
# Costed forms of the encoding reductions

`derive_reduction` reflects `encodedRed` and `searchRed` into computation trees and derives
their costed forms `R.tree.timed`, with the compilation theorems `R.compile_tree` and the
erasure theorems `R.tree.erase_timed`. The encoding `enc` (and the decoding `decS`) is a
primitive of the reduction, a parameter of its costed tree with its cost companion.

## Main results

With the adversary's `run` of time at most `T` and call cost at most `a`, and the encoding of
cost at most `c`:

* `encodedRed.tree.timeBound_timed` — time at most `T + a + c + 2`;
* `searchRed.tree.timeBound_timed` — with the decoding of cost at most `d`, time at most
  `T + a + c + d + 3`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto

open CatCrypt.Core

derive_reduction encodedRed

derive_reduction searchRed

/-- **Time of the encoding reduction**: one encoding of cost at most `c` and one call of the
adversary of time at most `T` and call cost at most `a`. -/
theorem encodedRed.tree.timeBound_timed {V W : Type} (enc : V → W) (encCost : V → ℕ)
    (run : W → SPTree.Timed Bool) (runCost : W → ℕ) (v : V) {T a c : ℕ}
    (hA : ∀ w, (run w).time ≤ T) (hAc : ∀ w, runCost w ≤ a) (hc : ∀ v, encCost v ≤ c) :
    SPTree.Timed.stepTime (encodedRed.tree.timed enc encCost run runCost v) ≤ T + a + c + 2 := by
  time_bound

/-- **Time of the decoding reduction**: one encoding of the view of cost at most `c`, one call
of the adversary of time at most `T` and call cost at most `r`, and one decoding of the answer
of cost at most `d`. -/
theorem searchRed.tree.timeBound_timed {V W S T' : Type} (encV : V → W) (encCost : V → ℕ)
    (decS : T' → S) (decCost : T' → ℕ) (run : W → SPTree.Timed T') (runCost : W → ℕ) (v : V)
    {T r c d : ℕ} (hA : ∀ w, (run w).time ≤ T) (hAc : ∀ w, runCost w ≤ r)
    (hc : ∀ v, encCost v ≤ c) (hd : ∀ t, decCost t ≤ d) :
    SPTree.Timed.stepTime (searchRed.tree.timed encV encCost decS decCost run runCost v) ≤
      T + r + c + d + 3 := by
  time_bound

end CatCrypt.Crypto
