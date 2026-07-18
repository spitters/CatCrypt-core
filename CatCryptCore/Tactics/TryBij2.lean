/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Relational.Rules

/-!
# `ssprove_try_bij₂` — two-sample bijection coupling

`ssprove_try_bij` handles a single-sample coupling `(sample α).bind k`. Encryption
games that draw *two* samples — a shared value (IV / randomness `r`) then a key
whose bijection **depends on the first sample** — do not fit it: the outer sample
must be *synchronised* (`rHoare_same_step`) and only the inner sample
bijection-coupled (`rHoare_bij_step (f r)`).

`ssprove_try_bij₂ f` runs that scaffold — sync the outer sample, bijection-couple
the inner one with the family `f`, step through `rHoare_ret`, and discharge the
heap plumbing — leaving only the residual **value equation** for a domain closer.

Usage (CBC / CPA-from-PRF): after the games are in `sample _ >>= fun r => sample _
>>= fun k => pure …` form,
```
ssprove_try_bij₂ (fun r => C.keyEquiv r m₀ m₁)
-- ⊢  <value equation in the reindexed key/message>
rw [← C.coh, …]; simp [C.keyEquiv, …]
```
Here `f : α → (β ≃ β)` is the outer-sample-indexed bijection on the inner sample.
-/

namespace CatCrypt.Tactics

open CatCrypt.Relational

/-- Two-sample bijection coupling: sync the outer sample, bijection-couple the
inner one via `f` (indexed by the outer sample), then reduce through `rHoare_ret`
to the residual value equation. See the module docstring. -/
macro "ssprove_try_bij₂ " f:term : tactic =>
  `(tactic|
    (apply rHoare_same_step
     intro a
     apply rHoare_bij_step ($f a)
     intro b
     apply rHoare_ret
     intro h₁ h₂ hpre
     refine ⟨?_, hpre⟩))

end CatCrypt.Tactics
