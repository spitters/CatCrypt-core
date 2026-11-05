/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.SDistTV
public import CatCryptCore.NonUniform.Product

/-!
# Statistical hops through the total variation distance

The total variation distance `tvDist` between sub-distributions satisfies the triangle
inequality and does not grow under a common continuation (data processing); `n` independent
draws from `μ` and from `ν` are at distance at most `n * tvDist μ ν`. Replacing one draw from
`μ` by a draw from `ν` anywhere inside a game, after any common prefix, changes the advantage
of any distinguisher by at most `tvDist μ ν`.

## Main results

* `SDistr.tsum_bind_mul` — the expectation of a test function under `d.bind K`, split at the
  failure of `d`
* `tvDist_triangle` — `tvDist P R ≤ tvDist P Q + tvDist Q R`
* `tvDist_bind_le` — `tvDist (d₁.bind K) (d₂.bind K) ≤ tvDist d₁ d₂`
* `tvDist_bind_right_le` — a common prefix and continuations at distance at most `ε`
* `tvDist_bind_bind_le` — both together, `tvDist d₁ d₂ + ε`
* `tvDist_replicateFin_le` — `tvDist (replicateFin n μ) (replicateFin n ν) ≤ n * tvDist μ ν`
* `advantageA_sampleFrom_swap_le` — one draw from `μ` after a common prefix replaced by a draw
  from `ν`, at the cost `tvDist μ ν`
* `advantageA_sampleFrom_le` — the same for a draw made first
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto

open CatCrypt.Core CatCrypt.Prob CatCrypt.NonUniform
open scoped ENNReal

/-- The expectation of a test function `f` under `d.bind K` is the failure mass of `d` times
`f none` plus the `d`-average of the expectations under `K`. -/
theorem SDistr.tsum_bind_mul {α β : Type*} (d : SDistr α) (K : α → SDistr β)
    (f : Option β → ℝ≥0∞) :
    ∑' y, (d.bind K) y * f y = d none * f none + ∑' a, d (some a) * ∑' y, K a y * f y := by
  simp only [SDistr.bind, PMF.bind_apply]
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm, SDistr.tsum_option_eq_add]
  simp_rw [mul_assoc, ENNReal.tsum_mul_left]
  congr 2
  rw [SDistr.tsum_option_eq_add]
  simp [SDistr.fail_apply_none, SDistr.fail_apply_some]

/-- An expectation of a test function bounded by `1` is at most `1`. -/
private theorem tsum_mul_le_one {γ : Type*} (p : PMF γ) (f : γ → ℝ≥0∞) (hf : ∀ x, f x ≤ 1) :
    ∑' y, p y * f y ≤ 1 :=
  calc ∑' y, p y * f y ≤ ∑' y, p y := ENNReal.tsum_le_tsum fun y =>
        mul_le_of_le_one_right' (hf y)
    _ = 1 := p.tsum_coe

/-- `absDiff a b ≤ ε` from the two one-sided bounds. -/
private theorem absDiff_le_of_le_add {a b ε : ℝ≥0∞} (h₁ : a ≤ b + ε) (h₂ : b ≤ a + ε) :
    absDiff a b ≤ ε :=
  max_le (tsub_le_iff_right.2 (by rwa [add_comm])) (tsub_le_iff_right.2 (by rwa [add_comm]))

/-- The triangle inequality for the total variation distance. -/
theorem tvDist_triangle {α : Type*} (P Q R : SDistr α) :
    tvDist P R ≤ tvDist P Q + tvDist Q R :=
  iSup₂_le fun f hf => (absDiff_triangle _ _ _).trans
    (add_le_add (le_iSup₂_of_le f hf le_rfl) (le_iSup₂_of_le f hf le_rfl))

/-- Data processing: a common continuation does not increase the total variation distance. -/
theorem tvDist_bind_le {α β : Type*} (d₁ d₂ : SDistr α) (K : α → SDistr β) :
    tvDist (d₁.bind K) (d₂.bind K) ≤ tvDist d₁ d₂ := by
  refine iSup₂_le fun f hf => ?_
  rw [SDistr.tsum_bind_mul, SDistr.tsum_bind_mul]
  let g : Option α → ℝ≥0∞ := fun x => x.elim (f none) fun a => ∑' y, K a y * f y
  have hg : ∀ x, g x ≤ 1 := fun x => by
    cases x with
    | none => exact hf none
    | some a => exact tsum_mul_le_one (K a) f hf
  have e : ∀ d : SDistr α,
      d none * f none + ∑' a, d (some a) * ∑' y, K a y * f y = ∑' x, d x * g x :=
    fun d => (SDistr.tsum_option_eq_add (fun x => d x * g x)).symm
  rw [e d₁, e d₂]
  exact le_iSup₂_of_le g hg le_rfl

/-- A common prefix followed by continuations at total variation distance at most `ε` gives
distributions at distance at most `ε`. -/
theorem tvDist_bind_right_le {α β : Type*} (d : SDistr α) (K₁ K₂ : α → SDistr β) (ε : ℝ≥0∞)
    (h : ∀ a, tvDist (K₁ a) (K₂ a) ≤ ε) :
    tvDist (d.bind K₁) (d.bind K₂) ≤ ε := by
  refine iSup₂_le fun f hf => ?_
  rw [SDistr.tsum_bind_mul, SDistr.tsum_bind_mul]
  have hk : ∀ a, absDiff (∑' y, K₁ a y * f y) (∑' y, K₂ a y * f y) ≤ ε :=
    fun a => (le_iSup₂_of_le f hf le_rfl).trans (h a)
  have hw : ∑' a, d (some a) ≤ 1 :=
    (ENNReal.tsum_comp_le_tsum_of_injective (Option.some_injective α) d).trans_eq d.tsum_coe
  have hsum : absDiff (∑' a, d (some a) * ∑' y, K₁ a y * f y)
      (∑' a, d (some a) * ∑' y, K₂ a y * f y) ≤ ε :=
    absDiff_le_of_le_add
      (weighted_bound _ _ _ ε (fun a => le_add_of_absDiff_le (hk a)) hw)
      (weighted_bound _ _ _ ε
        (fun a => le_add_of_absDiff_le ((absDiff_comm _ _).trans_le (hk a))) hw)
  refine le_trans (max_le ?_ ?_) hsum
  · exact (add_tsub_add_le_tsub_add_tsub).trans (by rw [tsub_self, zero_add]; exact le_max_left _ _)
  · exact (add_tsub_add_le_tsub_add_tsub).trans
      (by rw [tsub_self, zero_add]; exact le_max_right _ _)

/-- Different prefixes and continuations: the distance of the prefixes plus a bound on the
distance of the continuations. -/
theorem tvDist_bind_bind_le {α β : Type*} (d₁ d₂ : SDistr α) (K₁ K₂ : α → SDistr β)
    (ε : ℝ≥0∞) (h : ∀ a, tvDist (K₁ a) (K₂ a) ≤ ε) :
    tvDist (d₁.bind K₁) (d₂.bind K₂) ≤ tvDist d₁ d₂ + ε :=
  (tvDist_triangle _ (d₂.bind K₁) _).trans
    (add_le_add (tvDist_bind_le d₁ d₂ K₁) (tvDist_bind_right_le d₂ K₁ K₂ ε h))

/-- `n` independent draws from `μ` and from `ν` are at total variation distance at most
`n * tvDist μ ν`. -/
theorem tvDist_replicateFin_le {α : Type*} (n : ℕ) (μ ν : SDistr α) :
    tvDist (replicateFin n μ) (replicateFin n ν) ≤ n * tvDist μ ν := by
  induction n with
  | zero => simp [replicateFin, tvDist_self]
  | succ n ih =>
    have hs : ∀ d : SDistr α, replicateFin (n + 1) d =
        d.bind fun a => (replicateFin n d).bind fun f => SDistr.pure (Fin.cons a f) :=
      fun _ => rfl
    rw [hs, hs]
    refine (tvDist_bind_bind_le _ _ _ _ _ fun a =>
      (tvDist_bind_le _ _ _).trans ih).trans (le_of_eq ?_)
    push_cast
    ring

/-- One draw from `μ`, after any common prefix, inside any game, replaced by a draw from `ν`:
the advantage of `A` against a fixed game `H` changes by at most `tvDist μ ν`. -/
theorem advantageA_sampleFrom_swap_le {S X V : Type} (pre : SPComp S)
    (post : S → X → SPComp V) (H : SPComp V) (A : V → SPComp Bool) (μ ν : SDistr X) :
    AdvantageA (pre.bind fun s => (sampleFrom μ).bind (post s)) H A ≤
      AdvantageA (pre.bind fun s => (sampleFrom ν).bind (post s)) H A + tvDist μ ν := by
  have hA : ∀ G : SPComp V, AdvantageA G H A =
      absDiff (prTrue (G.bind A) Heap.empty) (prTrue (H.bind A) Heap.empty) := fun _ => rfl
  rw [hA, hA, add_comm]
  refine (absDiff_triangle _ _ _).trans (add_le_add_left ?_ _)
  refine (absDiff_prTrue_bind_le_tvDist_gen _ _ A Heap.empty).trans ?_
  refine tvDist_bind_right_le (pre Heap.empty) _ _ _ fun p => ?_
  obtain ⟨s, h⟩ := p
  change tvDist (((sampleFrom μ).bind (post s)) h) (((sampleFrom ν).bind (post s)) h) ≤ _
  rw [sampleFrom_bind_apply, sampleFrom_bind_apply]
  exact tvDist_bind_le μ ν _

/-- A first draw from `μ` replaced by a draw from `ν` changes the advantage of `A` against a
fixed game `H` by at most `tvDist μ ν`. -/
theorem advantageA_sampleFrom_le {X V : Type} (k : X → SPComp V) (H : SPComp V)
    (A : V → SPComp Bool) (μ ν : SDistr X) :
    AdvantageA ((sampleFrom μ).bind k) H A ≤
      AdvantageA ((sampleFrom ν).bind k) H A + tvDist μ ν := by
  have h := advantageA_sampleFrom_swap_le (SPComp.pure ()) (fun _ => k) H A μ ν
  simpa only [SPComp.pure_bind] using h

end CatCrypt.Crypto
