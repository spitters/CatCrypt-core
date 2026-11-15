/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleAdversaryTimed

/-!
# Node counts of composed oracle programs

The node count of the composition `B.bind f` of oracle programs, `ofAdv_bind_nodeCount_le`: at
most the sum of the node count of `B` and a common bound on the node counts of the
continuations `f a`.
-/

@[expose] public section

namespace CatCrypt.Crypto.OracleAdv.Timed

/-- The node count of a composition is at most the sum of the node counts. -/
theorem ofAdv_bind_nodeCount_le {D R α β : Type} (B : OracleAdv D R α)
    (f : α → OracleAdv D R β) {m n : ℕ} (hB : (ofAdv B).TimeBound m)
    (hf : ∀ a, (ofAdv (f a)).TimeBound n) : (ofAdv (B.bind f)).TimeBound (m + n) := by
  induction B generalizing m with
  | ret a => exact (hf a).mono (Nat.le_add_left n m)
  | rand p k ih =>
    obtain ⟨h1, hk⟩ := hB
    refine ⟨by omega, fun b => ⟨Nat.zero_le _, ?_⟩⟩
    rw [show m + n - 1 - 0 = (m - 1 - 0) + n by omega]
    exact ih b (hk b).2
  | query d k ih =>
    obtain ⟨h1, hk⟩ := hB
    refine ⟨by omega, fun r => ⟨Nat.zero_le _, ?_⟩⟩
    rw [show m + n - 1 - 0 = (m - 1 - 0) + n by omega]
    exact ih r (hk r).2

end CatCrypt.Crypto.OracleAdv.Timed
