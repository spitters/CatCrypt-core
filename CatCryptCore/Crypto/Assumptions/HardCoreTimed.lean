/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Assumptions.HardCore
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound

/-!
# Time certificate of the hop reduction of the hard-core game for `m` points

`derive_reduction` gives the costed form of `hcHybRed` of `HardCore.lean` over a costed
distinguisher, with its erasure theorem; `time_bound` gives its time.

## Main results

* `hcHybRed.tree.timed`, `hcHybRed.tree.erase_timed`, `hcHybRed.tree.timeBound_timed`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Assumptions.HardCore

open CatCrypt.Core

derive_reduction hcHybRed

/-- **Time of the hop reduction.** Over a distinguisher of time at most `t` and call cost at most
`c`, the reduction of the hop `i` runs in time at most `t + c + 4`. -/
theorem hcHybRed.tree.timeBound_timed {R TK EK D M : Type} [Fintype D] [Nonempty D]
    [AddCommGroup M] [Fintype M] {m : ℕ} (T : TDP R TK EK D M)
    (A : EK × (Fin m → D × M) → SPTree.Timed Bool) (ACost : EK × (Fin m → D × M) → ℕ)
    (i : Fin m) (ch : EK × D × M) {t c : ℕ} (hA : ∀ x, (A x).time ≤ t)
    (hc : ∀ x, ACost x ≤ c) :
    SPTree.Timed.stepTime (hcHybRed.tree.timed T A ACost i ch) ≤ t + c + 4 := by
  time_bound

end CatCrypt.Crypto.Assumptions.HardCore
