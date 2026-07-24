/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Unary.QueryBound
import CatCryptCore.Crypto.BadEvent

/-!
# Up-to-Bad Game Kit: Guessing Bound and Value-Carrying Output Games

Protocol-agnostic machinery for oracle-rejection and up-to-bad arguments, on top of the
failure-event query bound `prBad_induction` (`Unary/QueryBound`).

## Main results

* `prTrue_uniform_mem` / `prTrue_uniform_mem_le` — a uniform group element lands in a fixed
  set with probability `|S|/|G|` (at most `n/|G|`). The guessing bound behind a `q`-query
  union.
* `prTrue_bind_le` — a bind returns `true` with probability at most `ε` when every reachable
  continuation does (weighted-average bound).
* `prEvent_sample_bind` — bad-event mass of a uniform sample as the average, over the sampled
  value, of the continuation's bad mass.
* `gameOut` / `gameOut_apply` / `gameOut_iub_general` — a game whose Bool output is a function
  `F : W → Bool` of an arbitrary shared state `W`. Two such games with outputs agreeing on
  every non-bad state are identical-until-bad (`IdenticalUntilBad`), so an up-to-bad advantage
  bound covers a distinguisher reading any value carried in `W`, not only a leak indicator.
-/

namespace CatCrypt.Unary

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

variable {G : Type} [Fintype G] [Nonempty G] [DecidableEq G]

/-- Bad-event mass of a uniform sample followed by a continuation: the average, over the
    sampled value, of the continuation's bad-event mass. -/
theorem prEvent_sample_bind {β : Type} (k : G → SPComp β) (h₀ : Heap)
    (E : β → Heap → Prop) :
    prEvent ((SPComp.bind (SPComp.sample G) k) h₀) E =
    ∑ v : G, (Fintype.card G : ℝ≥0∞)⁻¹ * prEvent (k v h₀) E := by
  have hsb : (SPComp.bind (SPComp.sample G) k) h₀ = (SDistr.uniform G).bind (fun a => k a h₀) := by
    simp only [SPComp.bind_def, SPComp.sample]
    rw [SDistr.bind_assoc]; congr 1; funext a; rw [SDistr.pure_bind]
  rw [hsb]
  unfold prEvent
  have pull : ∀ (C : Prop) [Decidable C] (f : Option G → ℝ≥0∞),
      (if C then ∑' i, f i else 0) = ∑' i, (if C then f i else 0) := by
    intro C _ f; split <;> simp
  simp only [SDistr.bind, PMF.bind_apply, pull]
  rw [ENNReal.tsum_comm, tsum_fintype, Fintype.sum_option]
  simp only [SDistr.uniform_apply_none, SDistr.uniform_apply_some, SDistr.fail_apply_some,
    zero_mul, ite_self, tsum_zero, zero_add]
  apply Finset.sum_congr rfl; intro v _
  rw [← ENNReal.tsum_mul_left]; apply tsum_congr; intro p
  by_cases hE : E p.1 p.2 <;> simp [hE]

/-! ## Guessing bound -/

/-- A uniform group element lands in a fixed set `S` with probability `|S|/|G|`. -/
theorem prTrue_uniform_mem (S : Finset G) (h₀ : Heap) :
    prTrue (SPComp.bind (SPComp.sample G) (fun v => SPComp.pure (decide (v ∈ S)))) h₀
    = (S.card : ℝ≥0∞) / (Fintype.card G : ℝ≥0∞) := by
  rw [prTrue_bind_sample]
  have hpt : ∀ v : G, prTrue (SPComp.pure (decide (v ∈ S))) h₀ = if v ∈ S then 1 else 0 := by
    intro v
    unfold prTrue
    by_cases hv : v ∈ S
    · simp only [hv, decide_true]
      rw [tsum_eq_single h₀]
      · simp [SPComp.pure, SDistr.pure_apply_some]
      · intro h' hh'
        simp [SPComp.pure, SDistr.pure_apply_some, Prod.ext_iff, hh'.symm]
    · simp only [hv, decide_false, if_false]
      apply ENNReal.tsum_eq_zero.mpr
      intro h'
      simp [SPComp.pure, SDistr.pure_apply_some]
  simp_rw [hpt]
  rw [← Finset.mul_sum, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter,
    mul_comm, ← div_eq_mul_inv]

/-- A uniform group element lands in a set of size at most `n` with probability at most
    `n/|G|`. The union bound behind a `q`-query oracle-rejection term. -/
theorem prTrue_uniform_mem_le (S : Finset G) (n : ℕ) (hS : S.card ≤ n) (h₀ : Heap) :
    prTrue (SPComp.bind (SPComp.sample G) (fun v => SPComp.pure (decide (v ∈ S)))) h₀
    ≤ (n : ℝ≥0∞) / (Fintype.card G : ℝ≥0∞) := by
  rw [prTrue_uniform_mem]
  exact ENNReal.div_le_div_right (by exact_mod_cast hS) _

/-- Weighted-average bind bound: if every reachable continuation returns `true` with
    probability at most `ε`, so does the whole bind. -/
theorem prTrue_bind_le {α : Type} (c : SPComp α) (f : α → SPComp Bool) (h₀ : Heap) (ε : ℝ≥0∞)
    (hf : ∀ (a : α) (h : Heap), (c h₀) (some (a, h)) ≠ 0 → prTrue (f a) h ≤ ε) :
    prTrue (SPComp.bind c f) h₀ ≤ ε := by
  unfold prTrue
  rw [SPComp.bind_def]
  calc ∑' h, ((c h₀).bind (fun p => f p.1 p.2)) (some (true, h))
      = ∑' h, ∑' a : α × Heap, (c h₀) (some a) * (f a.1 a.2) (some (true, h)) := by
        apply tsum_congr; intro h; rw [SDistr_bind_apply_some]
    _ = ∑' a : α × Heap, (c h₀) (some a) * ∑' h, (f a.1 a.2) (some (true, h)) := by
        rw [ENNReal.tsum_comm]; apply tsum_congr; intro a; rw [ENNReal.tsum_mul_left]
    _ ≤ ∑' a : α × Heap, (c h₀) (some a) * ε := by
        apply ENNReal.tsum_le_tsum; intro a
        by_cases hz : (c h₀) (some a) = 0
        · simp [hz]
        · exact mul_le_mul' le_rfl (hf a.1 a.2 hz)
    _ = (∑' a : α × Heap, (c h₀) (some a)) * ε := by rw [ENNReal.tsum_mul_right]
    _ ≤ 1 * ε := mul_le_mul' (by rw [tsum_some_eq_mass]; exact sdistr_mass_le_one _) le_rfl
    _ = ε := one_mul ε

/-! ## Value-carrying output games -/

variable {W : Type}

/-- A game whose Bool output is a function `F` of the shared state produced by `shared`. -/
noncomputable def gameOut (shared : SPComp W) (F : W → Bool) : SPComp Bool :=
  SPComp.bind shared (fun w => SPComp.pure (F w))

/-- Output-apply: the mass on `(b, h')` is the shared-state mass reaching `h'` weighted by
    whether `F` yields `b`. -/
theorem gameOut_apply (shared : SPComp W) (F : W → Bool) (b : Bool) (h h' : Heap) :
    (gameOut shared F h) (some (b, h'))
    = ∑' w : W, (shared h) (some (w, h')) * (if F w = b then 1 else 0) := by
  unfold gameOut
  rw [SPComp.bind_def, SDistr_bind_apply_some, ENNReal.tsum_prod']
  apply tsum_congr; intro w
  rw [tsum_eq_single h']
  · simp only [SPComp.pure_def, SDistr.pure_apply_some, Prod.mk.injEq]
    by_cases hFb : F w = b <;> simp [hFb]
  · intro hp hph
    simp only [SPComp.pure_def, SDistr.pure_apply_some, Prod.mk.injEq]
    rw [if_neg (fun hc => hph hc.2), mul_zero]

/-- **Up-to-bad for arbitrary outputs.** Two games with outputs `F₀`, `F₁` agreeing on every
    non-bad state (`badP w = false`) are identical-until-bad. `F₀`/`F₁` may read a value
    carried in `W`, so this covers a distinguisher using that value, not only the bad
    indicator. -/
theorem gameOut_iub_general (shared : SPComp W) (F₀ F₁ badP : W → Bool)
    (hFF : ∀ w : W, badP w = false → F₀ w = F₁ w) :
    BadEvent.IdenticalUntilBad (gameOut shared F₀) (gameOut shared F₁) (gameOut shared badP) := by
  constructor
  intro h b h'
  rw [gameOut_apply, gameOut_apply, gameOut_apply, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum; intro w
  rw [← mul_add]
  apply mul_le_mul' le_rfl
  by_cases hbad : badP w = true
  · rw [if_pos hbad]
    exact le_trans (by split_ifs <;> simp) le_add_self
  · have hbf : badP w = false := by simpa using hbad
    have h0 : (if badP w = true then (1 : ℝ≥0∞) else 0) = 0 := by rw [hbf]; simp
    rw [h0, add_zero, hFF w hbf]

end CatCrypt.Unary
