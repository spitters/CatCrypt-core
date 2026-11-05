/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.TV

/-!
# Cross-Validation: sdist ↔ tvDist

This file proves that the distinguisher-supremum distance (`sdist`) and the
total variation distance (`tvDist`) agree on Kleisli morphisms of `SPComp`.

## Main results

* `sdist_le_tvDist_sup` — `sdist f g ≤ ⨆ a h₀, tvDist (f a h₀) (g a h₀)`
* `tvDist_sup_le_sdist` — `⨆ a h₀, tvDist (f a h₀) (g a h₀) ≤ sdist f g`
* `sdist_eq_tvDist_sup` — the two are equal

## Significance

The two formulations of statistical distance are both standard in the literature:
1. **Distinguisher supremum** (`sdist`): natural for game-hopping and PPL arguments
2. **Test function supremum** (`tvDist`): natural for coupling and data-processing arguments

Proving they agree cross-validates both definitions and allows free switching
between the two perspectives in proofs.

## Architecture

The ≤ direction follows immediately from the generalized PPL
(`absDiff_prTrue_bind_le_tvDist_gen`):
any distinguisher induces a bounded test function on the intermediate distribution.

The ≥ direction requires constructing, for each bounded test function, a
corresponding SPComp distinguisher (via `SPComp.bernoulli`) that achieves the
same expectation. The key technique is a convex decomposition that splits test
functions into a `none`-vanishing part and its complement, then uses Bernoulli
realization for both parts and the complement identity for `absDiff`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto

open CatCrypt.Core CatCrypt.Prob

open scoped ENNReal

/-! ## Generalized PPL for Arbitrary Output Types -/

/-- Generalized weighted sum decomposition: `prTrue(bind c D, h₀)` as a weighted
    sum over the intermediate distribution, for arbitrary output type `β`.
    This generalizes `prTrue_bind_as_weighted_sum` from `TV.lean` (which is
    specialized to `Bool`). -/
theorem prTrue_bind_eq_weighted_gen {β : Type*}
    (c : SPComp β) (D : β → SPComp Bool) (h₀ : Heap) :
    prTrue (SPComp.bind c D) h₀ =
      ∑' (p : Option (β × Heap)), (c h₀ : PMF _) p *
        (match p with | some ⟨b, h'⟩ => prTrue (D b) h' | none => 0) :=
  by grind [prTrue_bind_eq_weighted]

/-- Generalized Post-Processing Lemma: for any output type `β`,
    post-processing cannot increase the TV distance.

    This generalizes `absDiff_prTrue_bind_le_tvDist` from `TV.lean` (which
    requires `c₁, c₂ : SPComp Bool`) to arbitrary `SPComp β`. -/
theorem absDiff_prTrue_bind_le_tvDist_gen {β : Type*} (c₁ c₂ : SPComp β)
    (D : β → SPComp Bool) (h₀ : Heap) :
    absDiff (prTrue (SPComp.bind c₁ D) h₀) (prTrue (SPComp.bind c₂ D) h₀) ≤
    tvDist (c₁ h₀) (c₂ h₀) := by
  -- Construct the test function and show the bound directly
  unfold tvDist
  apply le_iSup_of_le (fun x => match x with | some ⟨b, h'⟩ => prTrue (D b) h' | none => 0)
  apply le_iSup_of_le (fun x => by cases x with
    | none => exact zero_le
    | some p => exact prTrue_le_one (D p.1) p.2)
  rw [prTrue_bind_eq_weighted_gen c₁ D h₀, prTrue_bind_eq_weighted_gen c₂ D h₀]

/-! ## sdist ≤ tvDist Supremum -/

/-- The distinguisher-supremum distance is bounded by the supremum of TV distances.

    For any distinguisher `D`, the advantage `|prTrue(f a >>= D, h₀) - prTrue(g a >>= D, h₀)|`
    is bounded by `tvDist(f a h₀, g a h₀)` via the generalized PPL. Taking the
    supremum over `D, a, h₀` on both sides gives the result. -/
theorem sdist_le_tvDist_sup {α β : Type*} (f g : α → SPComp β) :
    sdist f g ≤ ⨆ (a : α) (h₀ : Heap), tvDist (f a h₀) (g a h₀) := by
  apply iSup_le; intro D; apply iSup_le; intro a; apply iSup_le; intro h₀
  calc absDiff (prTrue (SPComp.bind (f a) D) h₀) (prTrue (SPComp.bind (g a) D) h₀)
      ≤ tvDist (f a h₀) (g a h₀) := absDiff_prTrue_bind_le_tvDist_gen (f a) (g a) D h₀
    _ ≤ ⨆ (a : α) (h₀ : Heap), tvDist (f a h₀) (g a h₀) :=
        le_iSup_of_le a (le_iSup_of_le h₀ le_rfl)

/-! ## tvDist Supremum ≤ sdist -/

/-- The underlying function for the Bernoulli PMF. -/
noncomputable def bernoulli_fn (p : ℝ≥0∞) (h' : Heap) : Option (Bool × Heap) → ℝ≥0∞
  | some (true, h) => if h = h' then p else 0
  | none => 1 - p
  | _ => 0

@[simp] theorem bernoulli_fn_some_true (p : ℝ≥0∞) (h' h : Heap) :
    bernoulli_fn p h' (some (true, h)) = if h = h' then p else 0 := rfl

@[simp] theorem bernoulli_fn_none (p : ℝ≥0∞) (h' : Heap) :
    bernoulli_fn p h' none = 1 - p := rfl

/-- Bernoulli SPComp: returns `true` with probability `p`, keeping the heap.
    Constructed as a PMF on `Option (Bool × Heap)` with mass `p` at `some(true, h')`
    and `1 - p` at `none` (representing "failure" / false outcome). -/
noncomputable def SPComp.bernoulli (p : ℝ≥0∞) (hp : p ≤ 1) (h' : Heap) :
    SDistr (Bool × Heap) :=
  ⟨bernoulli_fn p h', by
    have key : bernoulli_fn p h' =
        (fun x => if x = some (true, h') then p else 0) +
        (fun x => if x = none then (1 - p) else 0) := by
      funext x; simp only [Pi.add_apply, bernoulli_fn]
      rcases x with _ | ⟨b, hh⟩
      · simp
      · cases b <;> simp [eq_comm]
    rw [key]
    suffices h : HasSum _ (p + (1 - p)) by rwa [add_tsub_cancel_of_le hp] at h
    exact (hasSum_ite_eq _ p).add (hasSum_ite_eq _ (1 - p))⟩

/-- `prTrue` of the Bernoulli SPComp equals `p`. -/
theorem prTrue_bernoulli (p : ℝ≥0∞) (hp : p ≤ 1) (h' : Heap) :
    prTrue (fun _ => SPComp.bernoulli p hp h') h' = p := by
  unfold prTrue SPComp.bernoulli
  exact tsum_ite_eq h' (fun _ => p)

/-- Shifting lemma: `absDiff(a + c, b + c) = absDiff(a, b)` for finite `c`. -/
theorem absDiff_add_right (a b c : ℝ≥0∞) (hc : c ≠ ⊤) :
    absDiff (a + c) (b + c) = absDiff a b := by
  simp only [absDiff]
  rw [ENNReal.add_sub_add_eq_sub_right hc, ENNReal.add_sub_add_eq_sub_right hc]

/-- Homogeneity: `absDiff(k*a, k*b) = k * absDiff(a, b)` for finite `k`. -/
theorem absDiff_mul_left (k a b : ℝ≥0∞) (hk : k ≠ ⊤) :
    absDiff (k * a) (k * b) = k * absDiff a b := by
  simp only [absDiff,
    show k * a - k * b = k * (a - b) from (ENNReal.mul_sub (fun _ _ => hk)).symm,
    show k * b - k * a = k * (b - a) from (ENNReal.mul_sub (fun _ _ => hk)).symm]
  exact max_mul_mul_left k (a - b) (b - a)

/-- Additive triangle inequality for `absDiff`. -/
theorem absDiff_add_le (a₁ a₂ b₁ b₂ : ℝ≥0∞)
    (ha₂ : a₂ ≠ ⊤) (hb₁ : b₁ ≠ ⊤) :
    absDiff (a₁ + a₂) (b₁ + b₂) ≤ absDiff a₁ b₁ + absDiff a₂ b₂ := by
  calc absDiff (a₁ + a₂) (b₁ + b₂)
      ≤ absDiff (a₁ + a₂) (b₁ + a₂) + absDiff (b₁ + a₂) (b₁ + b₂) :=
        absDiff_triangle _ _ _
    _ = absDiff a₁ b₁ + absDiff (b₁ + a₂) (b₁ + b₂) := by
        rw [absDiff_add_right a₁ b₁ a₂ ha₂]
    _ = absDiff a₁ b₁ + absDiff a₂ b₂ := by
        congr 1; rw [show b₁ + a₂ = a₂ + b₁ from add_comm ..,
          show b₁ + b₂ = b₂ + b₁ from add_comm .., absDiff_add_right a₂ b₂ b₁ hb₁]

/-- Complement identity: `absDiff(1-a, 1-b) = absDiff(a, b)` for `a, b ≤ 1`. -/
theorem ennreal_sub_sub_eq (a b : ℝ≥0∞) (hab : a ≤ b) (hb : b ≤ 1) :
    (1 - a) - (1 - b) = b - a := by
  calc (1 - a) - (1 - b)
      = (1 - b + (b - a)) - (1 - b) := by rw [tsub_add_tsub_cancel hb hab]
    _ = (b - a) + (1 - b) - (1 - b) := by rw [add_comm]
    _ = b - a := ENNReal.add_sub_cancel_right
        (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)

theorem absDiff_one_sub (a b : ℝ≥0∞) (ha : a ≤ 1) (hb : b ≤ 1) :
    absDiff (1 - a) (1 - b) = absDiff a b := by
  simp only [absDiff]
  rcases le_total a b with hab | hab
  · rw [ennreal_sub_sub_eq a b hab hb,
        tsub_eq_zero_of_le (tsub_le_tsub_left hab 1),
        tsub_eq_zero_of_le hab, sup_comm]
  · rw [ennreal_sub_sub_eq b a hab ha,
        tsub_eq_zero_of_le (tsub_le_tsub_left hab 1),
        tsub_eq_zero_of_le hab, sup_comm]

/-- Bernoulli realization: a test function `t` with `t(none) = 0` is realizable
    by a Bernoulli distinguisher, so its `absDiff` is bounded by `sdist`. -/
theorem bernoulli_realization {α β : Type*} (f g : α → SPComp β)
    (t : Option (β × Heap) → ℝ≥0∞) (ht : ∀ x, t x ≤ 1)
    (ht_none : t none = 0) (a : α) (h₀ : Heap) :
    absDiff (∑' x, (f a h₀ : PMF _) x * t x) (∑' x, (g a h₀ : PMF _) x * t x) ≤
    sdist f g := by
  -- Construct distinguisher D using Bernoulli
  let D : β → SPComp Bool := fun b h' =>
    SPComp.bernoulli (t (some (b, h'))) (ht (some (b, h'))) h'
  -- Show prTrue(f a >>= D, h₀) = ∑ P * t
  have hD_eq : ∀ (c : SPComp β),
      prTrue (SPComp.bind c D) h₀ = ∑' x, (c h₀ : PMF _) x * t x := by
    intro c
    rw [prTrue_bind_eq_weighted_gen]
    congr 1; funext x; congr 1
    cases x with
    | none => simp [ht_none]
    | some bh =>
      show prTrue (D bh.1) bh.2 = t (some bh)
      unfold prTrue
      simp only [D, SPComp.bernoulli]
      exact tsum_ite_eq bh.2 (fun _ => t (some bh))
  rw [← hD_eq (f a), ← hD_eq (g a)]
  exact le_iSup₂_of_le D a (le_iSup_of_le h₀ le_rfl)

/-- The supremum of TV distances is bounded by the distinguisher-supremum distance.

    **Proof strategy:** For each test function `t`, define two restricted test
    functions `t₁` (same as `t` on `some`, zero at `none`) and `t₂` (complement).
    Express `∑ P*t` as a convex combination `(1-c) * ∑P*t₁ + c * (1-∑P*t₂)`,
    use the convexity of `absDiff` and Bernoulli realization of `t₁, t₂`. -/
theorem tvDist_sup_le_sdist {α β : Type*} (f g : α → SPComp β) :
    (⨆ (a : α) (h₀ : Heap), tvDist (f a h₀) (g a h₀)) ≤ sdist f g := by
  apply iSup_le; intro a; apply iSup_le; intro h₀
  unfold tvDist
  apply iSup_le; intro t; apply iSup_le; intro ht
  -- Abbreviations
  set P := (f a h₀ : PMF _) with hP_def
  set Q := (g a h₀ : PMF _) with hQ_def
  set c := t none with hc_def
  have hc_le : c ≤ 1 := ht none
  have hc_ne_top : c ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hc_le
  have h1c_ne_top : (1 - c) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  -- Step 1: Define restricted test functions t₁ and t₂ with t_i(none) = 0
  let t₁ : Option (β × Heap) → ℝ≥0∞ :=
    fun x => match x with | none => 0 | some bh => t (some bh)
  let t₂ : Option (β × Heap) → ℝ≥0∞ :=
    fun x => match x with | none => 0 | some bh => 1 - t (some bh)
  have ht₁_le : ∀ x, t₁ x ≤ 1 := by
    intro x; cases x with | none => exact zero_le | some _ => exact ht _
  have ht₂_le : ∀ x, t₂ x ≤ 1 := by
    intro x; cases x with | none => exact zero_le | some _ => exact tsub_le_self
  -- Step 2: Bernoulli realization — both t₁, t₂ give absDiff ≤ sdist
  have h_t₁ := bernoulli_realization f g t₁ ht₁_le rfl a h₀
  have h_t₂ := bernoulli_realization f g t₂ ht₂_le rfl a h₀
  -- Step 3: Tsum decomposition
  -- ∑ P*t = (∑' bh, P(some bh) * t(some bh)) + P(none) * c
  -- ∑ P*t₁ = ∑' bh, P(some bh) * t(some bh)  (since t₁(none) = 0)
  set A := ∑' x, P x * t₁ x; set B := ∑' x, Q x * t₁ x
  set A' := ∑' x, P x * t₂ x; set B' := ∑' x, Q x * t₂ x
  set p := P none; set q := Q none
  have hPt : ∑' x, P x * t x = A + p * c := by
    rw [show A = ∑' x, P x * t₁ x from rfl]
    rw [SDistr.tsum_option_eq_add (fun x => P x * t x),
      SDistr.tsum_option_eq_add (fun x => P x * t₁ x)]
    simp only [t₁, mul_zero, zero_add]
    grind
  have hQt : ∑' x, Q x * t x = B + q * c := by
    rw [show B = ∑' x, Q x * t₁ x from rfl]
    rw [SDistr.tsum_option_eq_add (fun x => Q x * t x),
      SDistr.tsum_option_eq_add (fun x => Q x * t₁ x)]
    simp only [t₁, mul_zero, zero_add]
    grind
  -- Step 4: Complementarity — A + p = 1 - A' (and B + q = 1 - B')
  -- Helper: ∑ P*t₁ + ∑ P*t₂ = ∑ P(some bh)
  have sum_t12_P : A + A' = ∑' (bh : β × Heap), P (some bh) := by
    rw [show A = ∑' x, P x * t₁ x from rfl, show A' = ∑' x, P x * t₂ x from rfl]
    rw [SDistr.tsum_option_none_zero (fun x => P x * t₁ x) (by simp [t₁]),
        SDistr.tsum_option_none_zero (fun x => P x * t₂ x) (by simp [t₂])]
    rw [← ENNReal.tsum_add]
    congr 1; funext bh
    show P (some bh) * t (some bh) + P (some bh) * (1 - t (some bh)) = P (some bh)
    rw [← mul_add, add_tsub_cancel_of_le (ht (some bh)), mul_one]
  have sum_t12_Q : B + B' = ∑' (bh : β × Heap), Q (some bh) := by
    rw [show B = ∑' x, Q x * t₁ x from rfl, show B' = ∑' x, Q x * t₂ x from rfl]
    rw [SDistr.tsum_option_none_zero (fun x => Q x * t₁ x) (by simp [t₁]),
        SDistr.tsum_option_none_zero (fun x => Q x * t₂ x) (by simp [t₂])]
    rw [← ENNReal.tsum_add]
    congr 1; funext bh
    show Q (some bh) * t (some bh) + Q (some bh) * (1 - t (some bh)) = Q (some bh)
    rw [← mul_add, add_tsub_cancel_of_le (ht (some bh)), mul_one]
  -- ∑ P(some bh) + P(none) = 1  (PMF property)
  have pmf_P : (∑' (bh : β × Heap), P (some bh)) + p = 1 := by
    rw [show p = P none from rfl]
    rw [add_comm, ← SDistr.tsum_option_eq_add (fun x => P x)]
    exact (P : PMF _).tsum_coe
  have pmf_Q : (∑' (bh : β × Heap), Q (some bh)) + q = 1 := by
    rw [show q = Q none from rfl]
    rw [add_comm, ← SDistr.tsum_option_eq_add (fun x => Q x)]
    exact (Q : PMF _).tsum_coe
  -- A' ≤ 1 (since A + A' + p = 1, so A' ≤ 1)
  have hAA'_le_pre : A + A' ≤ 1 :=
    sum_t12_P ▸ le_of_le_of_eq (le_add_right le_rfl) pmf_P
  have hBB'_le_pre : B + B' ≤ 1 :=
    sum_t12_Q ▸ le_of_le_of_eq (le_add_right le_rfl) pmf_Q
  have hA'_ne_top : A' ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans (le_add_left le_rfl) hAA'_le_pre)
  have hB'_ne_top : B' ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans (le_add_left le_rfl) hBB'_le_pre)
  have hAp : A + p = 1 - A' := by
    have h4 : A + A' + p = 1 := by rw [sum_t12_P, pmf_P]
    have h5 : A' + (A + p) = 1 := by rw [← add_assoc, add_comm A' A]; exact h4
    calc A + p = A' + (A + p) - A' := (ENNReal.add_sub_cancel_left hA'_ne_top).symm
      _ = 1 - A' := by rw [h5]
  have hBq : B + q = 1 - B' := by
    have h4 : B + B' + q = 1 := by rw [sum_t12_Q, pmf_Q]
    have h5 : B' + (B + q) = 1 := by rw [← add_assoc, add_comm B' B]; exact h4
    calc B + q = B' + (B + q) - B' := (ENNReal.add_sub_cancel_left hB'_ne_top).symm
      _ = 1 - B' := by rw [h5]
  -- Step 5: Convex decomposition
  -- ∑P*t = A + p*c = (1-c)*A + c*(A+p) = (1-c)*A + c*(1-A')
  have hPt_conv : ∑' x, P x * t x = (1 - c) * A + c * (1 - A') := by
    rw [hPt, ← hAp, mul_add, ← add_assoc, ← add_mul, tsub_add_cancel_of_le hc_le, one_mul]
    grind
  have hQt_conv : ∑' x, Q x * t x = (1 - c) * B + c * (1 - B') := by
    rw [hQt, ← hBq, mul_add, ← add_assoc, ← add_mul, tsub_add_cancel_of_le hc_le, one_mul]
    grind
  -- Step 6: Apply additive triangle + homogeneity + complement identity
  -- For absDiff_add_le we need a₂ = c*(1-A') ≠ ⊤ and b₁ = (1-c)*B ≠ ⊤
  have hcA'_ne_top : c * (1 - A') ≠ ⊤ :=
    ENNReal.mul_ne_top hc_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
  have hA_le_one : A ≤ 1 := le_trans (le_add_right le_rfl) hAA'_le_pre
  have hB_le_one : B ≤ 1 := le_trans (le_add_right le_rfl) hBB'_le_pre
  have h1cB_ne_top : (1 - c) * B ≠ ⊤ :=
    ENNReal.mul_ne_top h1c_ne_top
      (ne_top_of_le_ne_top ENNReal.one_ne_top hB_le_one)
  rw [hPt_conv, hQt_conv]
  calc absDiff ((1 - c) * A + c * (1 - A')) ((1 - c) * B + c * (1 - B'))
      ≤ absDiff ((1 - c) * A) ((1 - c) * B) + absDiff (c * (1 - A')) (c * (1 - B')) :=
        absDiff_add_le _ _ _ _ hcA'_ne_top h1cB_ne_top
    _ = (1 - c) * absDiff A B + c * absDiff (1 - A') (1 - B') := by
        rw [absDiff_mul_left _ _ _ h1c_ne_top, absDiff_mul_left _ _ _ hc_ne_top]
    _ = (1 - c) * absDiff A B + c * absDiff A' B' := by
        rw [absDiff_one_sub A' B'
          (le_trans (le_add_left le_rfl) hAA'_le_pre)
          (le_trans (le_add_left le_rfl) hBB'_le_pre)]
    _ ≤ (1 - c) * sdist f g + c * sdist f g := by gcongr
    _ = ((1 - c) + c) * sdist f g := by rw [add_mul]
    _ = sdist f g := by rw [tsub_add_cancel_of_le hc_le, one_mul]

/-! ## Equality -/

/-- Statistical distance equals the supremum of total variation distances.

    This shows the two standard formulations of statistical distance agree:
    * `sdist f g = sup_{D,a,h₀} |prTrue(f a >>= D, h₀) - prTrue(g a >>= D, h₀)|`
    * `sdist f g = sup_{a,h₀} tvDist(f a h₀, g a h₀)`

    The ≤ direction follows from the generalized PPL (each distinguisher induces
    a bounded test function). The ≥ direction requires constructing randomized
    distinguishers from test functions (Bernoulli sampling). -/
theorem sdist_eq_tvDist_sup {α β : Type*} (f g : α → SPComp β) :
    sdist f g = ⨆ (a : α) (h₀ : Heap), tvDist (f a h₀) (g a h₀) :=
  by grind [le_antisymm, sdist_le_tvDist_sup, tvDist_sup_le_sdist]

end CatCrypt.Crypto
