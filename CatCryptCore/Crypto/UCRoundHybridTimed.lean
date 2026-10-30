/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCRoundHybrid
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound

/-!
# Running time of the session reductions

`derive_reduction sessRed` builds the costed form of the session reduction
`KeyedGame.sessRed`, the multi-session adversary with every session other than `i` simulated
and session `i` forwarded to the oracle, and of the hop reduction `KeyedGame.sessReduction`,
`sessRed` over the session oracles of the hybrid world `i`.

No module imports this file.

## Main definitions

* `KeyedGame.sessRed.timed` — the costed reduction, over the session oracles `orc` with their
  cost companion `orcCost` and the costed adversary `B`
* `KeyedGame.sessReduction.timed` — the costed hop reduction, over the costs of the oracles of
  `G₀` and `G₁` and the costed adversary `B`

## Main results

* `KeyedGame.sessRed.erase_timed` — the costed reduction erases to `sessRed orc i s₀ B.erase`
* `KeyedGame.sessReduction.erase_timed` — the costed hop reduction erases to
  `sessReduction G₀ G₁ i B.erase`
* `KeyedGame.sessRed.timeBound_timed` — the costed reduction over an adversary of time `T`
  with at most `q` queries takes `T + q * (c + 8)` when the session oracles cost at most `c`
* `KeyedGame.sessReduction.timeBound_timed` — the costed hop reduction over such an adversary
  takes `1 + (T + q * (c + 13 + 8))` when the oracles of `G₀` and `G₁` cost at most `c`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent.KeyedGame

open CatCrypt.Core OracleAdv.Timed

derive_reduction sessRed
derive_reduction sessReduction

/-- **Time of the session reduction.** The costed session reduction runs an adversary of time
`T` with at most `q` queries in time `T + q * (c + 8)` when the session oracles cost at most
`c`. -/
theorem sessRed.timeBound_timed {Q A S : Type} (orc : ℕ → S → Q → PMF (A × S))
    (orcCost : ℕ → S → Q → ℕ) {c : ℕ} (hc : ∀ j s q, orcCost j s q ≤ c) (i : ℕ) (s₀ : S)
    (B : OracleAdv.Timed (ℕ × Q) A Bool) {T q : ℕ} (hB : B.TimeBound T)
    (hq : B.erase.IsQueryBound q) :
    StepTimeBound (sessRed.timed orc orcCost i s₀ B) (T + q * (c + 8)) := by
  have h := timeBound_simulateHat (t := c + 8) (fun y : (ℕ → S) × (ℕ → ℕ) => y.1)
    (fun y => (fun x => y x, fun _ => 0))
    (fun m d => delay 1 (sessImpl.timed orc orcCost i m.1 m.2 d))
    (fun s d => by time_bound) (fun s d => by allret_bound) hB hq (fun _ => s₀)
  beta_reduce at h
  unfold sessRed.timed
  refine (stepTimeBound_delay (timeBound_bind (n := 0) h.2 fun _ => ?_)).mono ?_
  exacts [⟨le_rfl, trivial⟩, by have := h.1; omega]

/-- A bound on both branches of a case split on a decided Boolean bounds the split. -/
private theorem casesOn_reflects_le {p : Prop} {X Y : Type} (b : Bool) (hb : b.Reflects p)
    (F : false.Reflects p → X → Y → ℕ) (G : true.Reflects p → X → Y → ℕ) {n : ℕ}
    (hF : ∀ h x y, F h x y ≤ n) (hG : ∀ h x y, G h x y ≤ n) (x : X) (y : Y) :
    Bool.casesOn (motive := fun z => z.Reflects p → X → Y → ℕ) b F G hb x y ≤ n := by
  cases b
  · exact hF hb x y
  · exact hG hb x y

/-- **Time of the session hop reduction.** Over an adversary of time `T` with at most `q`
queries, the costed hop reduction takes `1 + (T + q * (c + 13 + 8))` when the oracles of `G₀` and
`G₁` cost at most `c`. -/
theorem sessReduction.timeBound_timed {Q A : Type} (G₀ G₁ : KeyedGame Q A) (i : ℕ)
    (B : OracleAdv.Timed (ℕ × Q) A Bool) (cost₀ : G₀.Key → G₀.State → Q → ℕ)
    (cost₁ : G₁.Key → G₁.State → Q → ℕ) {c : ℕ} (hc₀ : ∀ k t q, cost₀ k t q ≤ c)
    (hc₁ : ∀ k t q, cost₁ k t q ≤ c) {T q : ℕ} (hB : B.TimeBound T)
    (hq : B.erase.IsQueryBound q) :
    StepTimeBound (sessReduction.timed G₀ G₁ i B cost₀ cost₁) (1 + (T + q * (c + 13 + 8))) := by
  unfold sessReduction.timed
  refine stepTimeBound_delay (sessRed.timeBound_timed _ _ ?_ i _ B hB hq)
  intro j s d
  refine (Nat.add_le_add_left (casesOn_reflects_le (n := c + 8) _ _ _ _ ?_ ?_ s d) 5).trans
    (by omega)
  · rintro - ⟨_ | ⟨k, t⟩, _⟩ q' <;> grind
  · rintro - ⟨_, _ | ⟨k, t⟩⟩ q' <;> grind

end CatCrypt.Crypto.UCTransparent.KeyedGame
