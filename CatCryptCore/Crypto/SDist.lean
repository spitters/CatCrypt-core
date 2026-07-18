/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.Advantage
import CatCryptCore.Category.KlSPComp
import Mathlib.Topology.EMetricSpace.Defs

/-!
# Statistical Distance on Kleisli Morphisms

This file defines statistical distance (`sdist`) between Kleisli morphisms of `SPComp`,
based on a distinguisher-supremum formulation. This avoids needing TV distance on `SDistr`
and directly reuses the existing `prTrue` infrastructure.

## Main definitions

* `absDiff` — unsigned difference in `ℝ≥0∞`
* `sdist` — statistical distance between Kleisli morphisms

## Main results

* `sdist_self`, `sdist_sym`, `sdist_triangle` — pseudometric properties
* `sdist_comp_right` — right post-processing lemma (PPL, post-composition)
* `sdist_comp_left` — left post-processing lemma (PPL, pre-composition)
* `sdist_wkR_le`, `sdist_wkL_le` — tensor doesn't increase distance
* `sdist_comp_add` — composition of ε-close morphisms

## Sub-SMC structure

The composition bound `sdist_comp_add` and the tensor bound `sdist_mapSum_le` (in `RC.lean`)
together establish that sdist-bounded pairs form a **wide sub-SMC** of `Kl(SPComp)`:

* **Objects**: all types (same as `Kl(SPComp)`)
* **Morphisms** from `α` to `β`: pairs `(f, g)` with `sdist f g ≤ ε`
* **Composition**: `sdist_comp_add` — `(ε₁, ε₂)` compose to `ε₁ + ε₂`
* **Tensor**: `sdist_mapSum_le` — `(ε₁, ε₂)` tensor to `max(ε₁, ε₂)`
* **Identity**: `sdist_self` — `(id, id)` has distance `0`

This sub-SMC is the semantic foundation for game-hopping proofs: each hop replaces
one morphism with an ε-close one, and the total distance is bounded by the sum of hops.

## Design: distinguisher-supremum formulation

We define `sdist` via `⨆ D a h₀, absDiff(prTrue(bind(f a) D, h₀), prTrue(bind(g a) D, h₀))`
rather than via TV distance on `SDistr`. This makes the right PPL trivial (compose D with g
to get a new distinguisher) and matches the game-hopping methodology directly.
The left PPL requires a convexity/weighted-average argument (`absDiff_prTrue_bind_le`).
-/

namespace CatCrypt.Crypto

open CatCrypt.Core CatCrypt.Prob

open scoped ENNReal

/-! ## Absolute Difference -/

/-- Unsigned difference in `ℝ≥0∞`: `absDiff a b = max(a - b, b - a)`. -/
noncomputable def absDiff (a b : ℝ≥0∞) : ℝ≥0∞ := (a - b) ⊔ (b - a)

@[simp] theorem absDiff_self (a : ℝ≥0∞) : absDiff a a = 0 := by
  simp [absDiff, tsub_self]

@[simp] theorem absDiff_comm (a b : ℝ≥0∞) : absDiff a b = absDiff b a := by
  simp [absDiff, max_comm]

theorem absDiff_triangle (a b c : ℝ≥0∞) :
    absDiff a c ≤ absDiff a b + absDiff b c := by
  simp only [absDiff]
  apply max_le
  · calc a - c ≤ (a - b) + (b - c) := tsub_le_tsub_add_tsub
      _ ≤ ((a - b) ⊔ (b - a)) + ((b - c) ⊔ (c - b)) :=
        add_le_add (le_max_left _ _) (le_max_left _ _)
  · calc c - a ≤ (c - b) + (b - a) := tsub_le_tsub_add_tsub
      _ ≤ ((c - b) ⊔ (b - c)) + ((b - a) ⊔ (a - b)) :=
        add_le_add (le_max_left _ _) (le_max_left _ _)
      _ = ((a - b) ⊔ (b - a)) + ((b - c) ⊔ (c - b)) := by
        rw [max_comm (c - b), max_comm (b - a), add_comm]

/-! ## Statistical Distance -/

/-- Statistical distance between Kleisli morphisms, defined as the supremum
    over all distinguishers, inputs, and initial heaps of the absolute difference
    in probability of returning `true`. -/
noncomputable def sdist {α β : Type*} (f g : α → SPComp β) : ℝ≥0∞ :=
  ⨆ (D : β → SPComp Bool) (a : α) (h₀ : Heap),
    absDiff (prTrue (SPComp.bind (f a) D) h₀) (prTrue (SPComp.bind (g a) D) h₀)

/-! ## Pseudometric Properties -/

@[simp] theorem sdist_self {α β : Type*} (f : α → SPComp β) : sdist f f = 0 := by
  simp [sdist, absDiff_self]

theorem sdist_sym {α β : Type*} (f g : α → SPComp β) : sdist f g = sdist g f := by
  simp only [sdist]
  congr 1; funext D; congr 1; funext a; congr 1; funext h₀
  exact absDiff_comm _ _

@[grind] theorem sdist_triangle {α β : Type*} (f g h : α → SPComp β) :
    sdist f h ≤ sdist f g + sdist g h := by
  apply iSup_le; intro D
  apply iSup_le; intro a
  apply iSup_le; intro h₀
  calc absDiff (prTrue (SPComp.bind (f a) D) h₀) (prTrue (SPComp.bind (h a) D) h₀)
      ≤ absDiff (prTrue (SPComp.bind (f a) D) h₀) (prTrue (SPComp.bind (g a) D) h₀) +
        absDiff (prTrue (SPComp.bind (g a) D) h₀) (prTrue (SPComp.bind (h a) D) h₀) :=
        absDiff_triangle _ _ _
    _ ≤ sdist f g + sdist g h := by
        apply add_le_add
        · exact le_iSup₂_of_le D a (le_iSup_of_le h₀ le_rfl)
        · exact le_iSup₂_of_le D a (le_iSup_of_le h₀ le_rfl)

/-! ## Post-Processing Lemmas -/

/-- Pre-composition with a pure function doesn't increase sdist.
    The sup over `h(a)` for `a : α` is ≤ the sup over all `b : β`. -/
@[grind] theorem sdist_precomp_le {α β γ : Type*} (f g : β → SPComp γ) (h : α → β) :
    sdist (f ∘ h) (g ∘ h) ≤ sdist f g := by
  apply iSup_le; intro D
  apply iSup_le; intro a
  apply iSup_le; intro h₀
  exact le_iSup₂_of_le D (h a) (le_iSup_of_le h₀ le_rfl)

/-- Right PPL: post-composition doesn't increase distance.
    This is immediate because `D ∘ g` is just another distinguisher. -/
theorem sdist_comp_right {α β γ : Type*} (f₁ f₂ : α → SPComp β)
    (g : β → SPComp γ) :
    sdist (fun a => SPComp.bind (f₁ a) g) (fun a => SPComp.bind (f₂ a) g) ≤ sdist f₁ f₂ := by
  apply iSup_le; intro D
  apply iSup_le; intro a
  apply iSup_le; intro h₀
  -- D' = D ∘ₖ g is a distinguisher for the original f₁, f₂
  let D' : β → SPComp Bool := fun b => SPComp.bind (g b) D
  have eq1 : SPComp.bind (SPComp.bind (f₁ a) g) D =
    SPComp.bind (f₁ a) D' := by
    simp [D', SPComp.bind_assoc]
  have eq2 : SPComp.bind (SPComp.bind (f₂ a) g) D =
    SPComp.bind (f₂ a) D' := by
    simp [D', SPComp.bind_assoc]
  rw [eq1, eq2]
  exact le_iSup₂_of_le D' a (le_iSup_of_le h₀ le_rfl)

/-- Auxiliary: `absDiff a b ≤ ε` implies `a ≤ b + ε`. -/
theorem le_add_of_absDiff_le {a b ε : ℝ≥0∞} (h : absDiff a b ≤ ε) :
    a ≤ b + ε := by
  have hab : a - b ≤ ε := le_trans (le_max_left _ _) h
  calc a ≤ a - b + b := le_tsub_add
    _ ≤ ε + b := by gcongr
    _ = b + ε := add_comm _ _

/-- Auxiliary: weighted average bound for ENNReal.
    If `∀ i, f i ≤ g i + ε` and `∑ w i ≤ 1`, then `∑ w i * f i ≤ ∑ w i * g i + ε`. -/
theorem weighted_bound {ι : Type*} (w f g : ι → ℝ≥0∞) (ε : ℝ≥0∞)
    (hfg : ∀ i, f i ≤ g i + ε) (hw : ∑' i, w i ≤ 1) :
    ∑' i, w i * f i ≤ (∑' i, w i * g i) + ε := by
  calc ∑' i, w i * f i
      ≤ ∑' i, w i * (g i + ε) := by
        apply ENNReal.tsum_le_tsum; intro i
        gcongr; exact hfg i
    _ = ∑' i, (w i * g i + w i * ε) := by
        congr 1; funext i; ring
    _ = (∑' i, w i * g i) + ∑' i, w i * ε := ENNReal.tsum_add
    _ = (∑' i, w i * g i) + (∑' i, w i) * ε := by
        congr 1; rw [ENNReal.tsum_mul_right]
    _ ≤ (∑' i, w i * g i) + 1 * ε := by gcongr
    _ = (∑' i, w i * g i) + ε := by ring

/-- Representation: `prTrue(bind c k, h₀) = ∑' p, (c h₀)(p) * val(p)`.
    This lemma factors out the weighted-sum structure of `prTrue(bind ...)`. -/
theorem prTrue_bind_eq_weighted {α : Type*}
    (c : SPComp α) (k : α → SPComp Bool) (h₀ : Heap) :
    prTrue (SPComp.bind c k) h₀ =
      ∑' (p : Option (α × Heap)), (c h₀ : PMF _) p *
        (match p with | some ⟨a, h'⟩ => prTrue (k a) h' | none => 0) := by
  unfold prTrue SPComp.bind SDistr.bind
  simp only [PMF.bind_apply]
  rw [ENNReal.tsum_comm]
  congr 1; funext p; rw [ENNReal.tsum_mul_left]; congr 1
  cases p with
  | none => simp [SDistr.fail, PMF.pure_apply]
  | some pp => rfl

/-- Helper for left PPL: weighted average of ε-close values is ε-close.
    Uses `prTrue_bind_eq_weighted` to reduce to a weighted-sum inequality. -/
theorem absDiff_prTrue_bind_le {α : Type*}
    (c : SPComp α) (k₁ k₂ : α → SPComp Bool) (h₀ : Heap) (ε : ℝ≥0∞)
    (hk : ∀ a h', prTrue (k₁ a) h' ≤ prTrue (k₂ a) h' + ε)
    (hk' : ∀ a h', prTrue (k₂ a) h' ≤ prTrue (k₁ a) h' + ε) :
    absDiff (prTrue (SPComp.bind c k₁) h₀) (prTrue (SPComp.bind c k₂) h₀) ≤ ε := by
  rw [prTrue_bind_eq_weighted c k₁ h₀, prTrue_bind_eq_weighted c k₂ h₀]
  have hv : ∀ p : Option (α × Heap),
      (match p with | some ⟨a, h'⟩ => prTrue (k₁ a) h' | none => 0) ≤
      (match p with | some ⟨a, h'⟩ => prTrue (k₂ a) h' | none => 0) + ε := by
    intro p; cases p with
    | none => exact zero_le
    | some pp => exact hk pp.1 pp.2
  have hv' : ∀ p : Option (α × Heap),
      (match p with | some ⟨a, h'⟩ => prTrue (k₂ a) h' | none => 0) ≤
      (match p with | some ⟨a, h'⟩ => prTrue (k₁ a) h' | none => 0) + ε := by
    intro p; cases p with
    | none => exact zero_le
    | some pp => exact hk' pp.1 pp.2
  have hw : ∑' p, (c h₀ : PMF _) p ≤ 1 := le_of_eq (c h₀).tsum_coe
  simp only [absDiff]
  apply max_le
  · rw [tsub_le_iff_right]
    exact le_trans (weighted_bound _ _ _ ε hv hw) (le_of_eq (add_comm _ _))
  · rw [tsub_le_iff_right]
    exact le_trans (weighted_bound _ _ _ ε hv' hw) (le_of_eq (add_comm _ _))

/-- Helper: absDiff of common-prefix bind.
    If the continuations differ by at most ε pointwise, then the bound propagates
    through a shared computation prefix. -/
theorem absDiff_bind_common {X : Type} (c : SPComp X)
    (k₁ k₂ : X → SPComp Bool) (h₀ : Heap) (ε : ℝ≥0∞)
    (hk : ∀ x h', absDiff (prTrue (k₁ x) h') (prTrue (k₂ x) h') ≤ ε) :
    absDiff (prTrue (c.bind k₁) h₀) (prTrue (c.bind k₂) h₀) ≤ ε :=
  absDiff_prTrue_bind_le c k₁ k₂ h₀ ε
    (fun x h' => le_add_of_absDiff_le (hk x h'))
    (fun x h' => le_add_of_absDiff_le (by rw [absDiff_comm]; exact hk x h'))

/-- Left PPL: pre-composition doesn't increase distance.
    The proof uses the weighted average argument via `absDiff_prTrue_bind_le`. -/
theorem sdist_comp_left {α β γ : Type*} (f : α → SPComp β)
    (g₁ g₂ : β → SPComp γ) :
    sdist (fun a => SPComp.bind (f a) g₁) (fun a => SPComp.bind (f a) g₂) ≤ sdist g₁ g₂ := by
  apply iSup_le; intro D
  apply iSup_le; intro a
  apply iSup_le; intro h₀
  have eq1 : SPComp.bind (SPComp.bind (f a) g₁) D =
    SPComp.bind (f a) (fun b => SPComp.bind (g₁ b) D) := SPComp.bind_assoc _ _ _
  have eq2 : SPComp.bind (SPComp.bind (f a) g₂) D =
    SPComp.bind (f a) (fun b => SPComp.bind (g₂ b) D) := SPComp.bind_assoc _ _ _
  rw [eq1, eq2]
  set ε := sdist g₁ g₂
  apply absDiff_prTrue_bind_le (f a) _ _ h₀ ε
  · intro b h'
    exact le_add_of_absDiff_le (le_iSup₂_of_le D b (le_iSup_of_le h' le_rfl))
  · intro b h'
    exact le_add_of_absDiff_le
      (by rw [absDiff_comm]; exact le_iSup₂_of_le D b (le_iSup_of_le h' le_rfl))


/-- Two-level `sdist_comp_left`: pre-composition with two nested binds
    (shared across both sides) does not increase sdist. Derives from
    a single `sdist_comp_left` by collapsing the two binds via associativity. -/
theorem sdist_comp_left_two {α β₁ β₂ γ : Type*}
    (f : α → SPComp β₁) (h : β₁ → SPComp β₂)
    (g₁ g₂ : β₂ → SPComp γ) :
    sdist (fun a => SPComp.bind (f a) (fun b₁ => SPComp.bind (h b₁) g₁))
          (fun a => SPComp.bind (f a) (fun b₁ => SPComp.bind (h b₁) g₂))
      ≤ sdist g₁ g₂ := by
  have eq₁ : (fun a : α => SPComp.bind (f a) (fun b₁ => SPComp.bind (h b₁) g₁)) =
             (fun a : α => SPComp.bind (SPComp.bind (f a) h) g₁) := by
    funext a; rw [SPComp.bind_assoc]
  have eq₂ : (fun a : α => SPComp.bind (f a) (fun b₁ => SPComp.bind (h b₁) g₂)) =
             (fun a : α => SPComp.bind (SPComp.bind (f a) h) g₂) := by
    funext a; rw [SPComp.bind_assoc]
  rw [eq₁, eq₂]
  exact sdist_comp_left (fun a => SPComp.bind (f a) h) g₁ g₂

/-- **Dependent two-level `sdist_comp_left`** (uniform bound variant):
    if the innermost continuations `g₁ b₁, g₂ b₁` are pointwise-`ε`-close
    for every intermediate value `b₁`, then the full two-bind composition
    is also `ε`-close.

    The dependent version is needed when the continuation depends on both
    the intermediate bind value and the sampled one — e.g., when routing
    ciphertext-output `p.1` from an outer epoch ratchet into the final
    output while an inner `sample W` supplies the next epoch's chain key. -/
theorem sdist_comp_left_two_dep {α β₁ β₂ γ : Type*}
    (f : α → SPComp β₁) (h : β₁ → SPComp β₂)
    (g₁ g₂ : β₁ → β₂ → SPComp γ) (ε : ℝ≥0∞)
    (hbound : ∀ b₁, sdist (g₁ b₁) (g₂ b₁) ≤ ε) :
    sdist (fun a => SPComp.bind (f a) (fun b₁ => SPComp.bind (h b₁) (g₁ b₁)))
          (fun a => SPComp.bind (f a) (fun b₁ => SPComp.bind (h b₁) (g₂ b₁)))
      ≤ ε := by
  -- Peel `f` via sdist_comp_left; reduce to a sdist over `β₁ → SPComp γ`.
  refine le_trans
    (sdist_comp_left f (fun b₁ => SPComp.bind (h b₁) (g₁ b₁))
                       (fun b₁ => SPComp.bind (h b₁) (g₂ b₁))) ?_
  -- Remaining goal: sdist (fun b₁ => h b₁ >>= g₁ b₁) (fun b₁ => h b₁ >>= g₂ b₁) ≤ ε.
  -- For each specific b₁, the pointwise bound
  --   sdist (fun _ : Unit => h b₁ >>= g₁ b₁) (fun _ => h b₁ >>= g₂ b₁) ≤ ε
  -- follows from sdist_comp_left on (fun _ => h b₁) and (hbound b₁).
  -- The outer sdist then bounds as the sup over b₁ of the per-b₁ ones.
  apply iSup_le; intro D
  apply iSup_le; intro b₁
  apply iSup_le; intro heap
  -- target: absDiff (prTrue ((h b₁ >>= g₁ b₁) >>= D) heap)
  --                 (prTrue ((h b₁ >>= g₂ b₁) >>= D) heap) ≤ ε
  have hPerB :
      sdist (fun (_ : Unit) => SPComp.bind (h b₁) (g₁ b₁))
            (fun (_ : Unit) => SPComp.bind (h b₁) (g₂ b₁)) ≤ ε := by
    refine le_trans (sdist_comp_left (fun (_ : Unit) => h b₁)
                      (g₁ b₁) (g₂ b₁)) ?_
    exact hbound b₁
  -- Specialize hPerB at D, (), heap: unfold sdist to extract absDiff bound.
  have hSingle :
      absDiff (prTrue (SPComp.bind (SPComp.bind (h b₁) (g₁ b₁)) D) heap)
              (prTrue (SPComp.bind (SPComp.bind (h b₁) (g₂ b₁)) D) heap)
      ≤ sdist (fun (_ : Unit) => SPComp.bind (h b₁) (g₁ b₁))
              (fun (_ : Unit) => SPComp.bind (h b₁) (g₂ b₁)) := by
    unfold sdist
    apply le_trans _ (le_iSup_of_le D le_rfl)
    apply le_trans _ (le_iSup_of_le (() : Unit) le_rfl)
    exact le_iSup (fun hp : Heap =>
      absDiff (prTrue (SPComp.bind (SPComp.bind (h b₁) (g₁ b₁)) D) hp)
              (prTrue (SPComp.bind (SPComp.bind (h b₁) (g₂ b₁)) D) hp)) heap
  exact le_trans hSingle hPerB

/-! ## Tensor (Coproduct) Distance Bounds -/

/-- Distance of right-whiskered morphisms. On `.inl`, only `f` runs; on `.inr`, distance is 0. -/
@[grind] theorem sdist_wkR_le {α₁ α₂ : Type} (f₁ f₂ : α₁ → SPComp α₂) (Y : Type) :
    sdist (KlSPComp.wkR f₁ Y) (KlSPComp.wkR f₂ Y) ≤ sdist f₁ f₂ := by
  apply iSup_le; intro D
  apply iSup_le; intro x
  apply iSup_le; intro h₀
  rcases x with a | c
  · -- .inl a: wkR f Y (.inl a) = SPComp.map Sum.inl (f a)
    simp only [KlSPComp.wkR]
    -- SPComp.map Sum.inl (f a) = SPComp.bind (f a) (fun b => SPComp.pure (Sum.inl b))
    simp only [SPComp.map]
    -- Now: absDiff (prTrue (bind (bind (f₁ a) (pure ∘ inl)) D) h₀)
    --              (prTrue (bind (bind (f₂ a) (pure ∘ inl)) D) h₀)
    -- By bind_assoc: = absDiff (prTrue (bind (f₁ a) D') h₀) (prTrue (bind (f₂ a) D') h₀)
    -- where D' b = bind (pure (inl b)) D = D (inl b)
    have eq1 : SPComp.bind (SPComp.bind (f₁ a) fun b => SPComp.pure (Sum.inl b)) D =
      SPComp.bind (f₁ a) (fun b => D (Sum.inl b)) := by
      rw [SPComp.bind_assoc]; congr 1; funext b; simp
    have eq2 : SPComp.bind (SPComp.bind (f₂ a) fun b => SPComp.pure (Sum.inl b)) D =
      SPComp.bind (f₂ a) (fun b => D (Sum.inl b)) := by
      rw [SPComp.bind_assoc]; congr 1; funext b; simp
    rw [eq1, eq2]
    exact le_iSup₂_of_le (fun b => D (Sum.inl b)) a (le_iSup_of_le h₀ le_rfl)
  · -- .inr c: both sides are SPComp.pure (Sum.inr c), so distance is 0
    simp only [KlSPComp.wkR, absDiff_self]
    exact zero_le

/-- Distance of left-whiskered morphisms. On `.inr`, only `g` runs; on `.inl`, distance is 0. -/
@[grind] theorem sdist_wkL_le (X : Type) {β₁ β₂ : Type} (g₁ g₂ : β₁ → SPComp β₂) :
    sdist (KlSPComp.wkL X g₁) (KlSPComp.wkL X g₂) ≤ sdist g₁ g₂ := by
  apply iSup_le; intro D
  apply iSup_le; intro x
  apply iSup_le; intro h₀
  rcases x with a | c
  · -- .inl a: both sides are SPComp.pure (Sum.inl a), so distance is 0
    simp only [KlSPComp.wkL, absDiff_self]
    exact zero_le
  · -- .inr c: wkL X g (.inr c) = SPComp.map Sum.inr (g c)
    simp only [KlSPComp.wkL, SPComp.map]
    have eq1 : SPComp.bind (SPComp.bind (g₁ c) fun b => SPComp.pure (Sum.inr b)) D =
      SPComp.bind (g₁ c) (fun b => D (Sum.inr b)) := by
      rw [SPComp.bind_assoc]; congr 1; funext b; simp
    have eq2 : SPComp.bind (SPComp.bind (g₂ c) fun b => SPComp.pure (Sum.inr b)) D =
      SPComp.bind (g₂ c) (fun b => D (Sum.inr b)) := by
      rw [SPComp.bind_assoc]; congr 1; funext b; simp
    rw [eq1, eq2]
    exact le_iSup₂_of_le (fun b => D (Sum.inr b)) c (le_iSup_of_le h₀ le_rfl)

/-! ## Composition Bound -/

/-- Two ε-close morphisms compose to give (ε₁+ε₂)-close morphisms. -/
theorem sdist_comp_add {α β γ : Type*} (f₁ f₂ : α → SPComp β)
    (g₁ g₂ : β → SPComp γ) {ε₁ ε₂ : ℝ≥0∞}
    (hf : sdist f₁ f₂ ≤ ε₁) (hg : sdist g₁ g₂ ≤ ε₂) :
    sdist (fun a => SPComp.bind (f₁ a) g₁) (fun a => SPComp.bind (f₂ a) g₂) ≤ ε₁ + ε₂ := by
  calc sdist (fun a => SPComp.bind (f₁ a) g₁) (fun a => SPComp.bind (f₂ a) g₂)
      ≤ sdist (fun a => SPComp.bind (f₁ a) g₁) (fun a => SPComp.bind (f₂ a) g₁) +
        sdist (fun a => SPComp.bind (f₂ a) g₁) (fun a => SPComp.bind (f₂ a) g₂) :=
        sdist_triangle _ _ _
    _ ≤ sdist f₁ f₂ + sdist g₁ g₂ :=
        add_le_add (sdist_comp_right f₁ f₂ g₁) (sdist_comp_left f₂ g₁ g₂)
    _ ≤ ε₁ + ε₂ := add_le_add hf hg

/-! ## Monotonicity -/

/-- If `sdist f g ≤ ε`, then for any specific distinguisher, input, and heap,
    the distinguishing advantage is bounded by `ε`. -/
theorem sdist_le_of_forall {α β : Type*} {f g : α → SPComp β} {ε : ℝ≥0∞}
    (h : sdist f g ≤ ε) (D : β → SPComp Bool) (a : α) (h₀ : Heap) :
    absDiff (prTrue (SPComp.bind (f a) D) h₀)
            (prTrue (SPComp.bind (g a) D) h₀) ≤ ε := by
  have : absDiff (prTrue (SPComp.bind (f a) D) h₀) (prTrue (SPComp.bind (g a) D) h₀)
    ≤ sdist f g := by
    unfold sdist
    apply le_trans _ (le_iSup_of_le D le_rfl)
    apply le_trans _ (le_iSup_of_le a le_rfl)
    exact le_iSup (fun h₀ => absDiff (prTrue (SPComp.bind (f a) D) h₀)
      (prTrue (SPComp.bind (g a) D) h₀)) h₀
  exact le_trans this h

/-! ## IsPure Bridge: Advantage → sdist -/

/-- For IsPure computations, `SPComp.bind c D` at heap `h₀` equals
    `d.bind (fun a => D a h₀)` where `d` is the pure distribution witness.
    This removes the dependence on `h₀` through `c`, leaving it only through `D`. -/
private theorem isPure_bind_expand {α β : Type*} {c : SPComp α} {d : SDistr α}
    (hc : ∀ h, c h = d.bind (fun a => SDistr.pure (a, h)))
    (D : α → SPComp β) (h₀ : Heap) :
    (SPComp.bind c D) h₀ = d.bind (fun a => D a h₀) := by
  simp only [SPComp.bind, hc h₀, SDistr.bind_assoc, SDistr.pure_bind]

/-- For IsPure computations, sdist can be bounded using only `Heap.empty`.

    When `f` and `g` are heap-independent, `prTrue(f a >>= D, h₀)` depends on `h₀`
    only through `D`. By "shifting" the distinguisher to absorb `h₀`, we reduce
    the supremum over all heaps to evaluation at `Heap.empty` alone.

    This bridges the gap between `Advantage` (defined at `Heap.empty`) and
    `sdist` (which takes the supremum over ALL initial heaps). -/
theorem sdist_isPure_le {α β : Type*} {f g : α → SPComp β} {ε : ℝ≥0∞}
    (hf : ∀ a, SPComp.IsPure (f a)) (hg : ∀ a, SPComp.IsPure (g a))
    (hε : ∀ (D : β → SPComp Bool) (a : α),
      absDiff (prTrue (SPComp.bind (f a) D) Heap.empty)
              (prTrue (SPComp.bind (g a) D) Heap.empty) ≤ ε) :
    sdist f g ≤ ε := by
  apply iSup_le; intro D; apply iSup_le; intro a; apply iSup_le; intro h₀
  obtain ⟨df, hdf⟩ := hf a
  obtain ⟨dg, hdg⟩ := hg a
  -- Shifted distinguisher: D' b ignores its heap argument and uses h₀
  let D' : β → SPComp Bool := fun b => fun _ => D b h₀
  -- prTrue(f a >>= D, h₀) = prTrue(f a >>= D', Heap.empty)
  -- because both reduce to ∑' h, (df.bind (fun b => D b h₀))(some(true, h))
  have heq_f : prTrue (SPComp.bind (f a) D) h₀ =
               prTrue (SPComp.bind (f a) D') Heap.empty := by
    unfold prTrue; congr 1; funext h; congr 1
    rw [isPure_bind_expand hdf D h₀, isPure_bind_expand hdf D' Heap.empty]
  have heq_g : prTrue (SPComp.bind (g a) D) h₀ =
               prTrue (SPComp.bind (g a) D') Heap.empty := by
    unfold prTrue; congr 1; funext h; congr 1
    rw [isPure_bind_expand hdg D h₀, isPure_bind_expand hdg D' Heap.empty]
  rw [heq_f, heq_g]
  exact hε D' a

/-! ## AdvantageA Bridge

`sdist_isPure_le` takes arguments in `(D, a)` order, but security hypotheses
are typically stated in `(a, D)` order: `∀ x D, AdvantageA (f x) (g x) D ≤ ε`.
These variants eliminate the manual argument swapping. -/

/-- Bridge `sdist` from per-input `AdvantageA` bounds.

    This is the most common pattern in protocol security proofs:
    given IsPure games and a per-input advantage bound, derive sdist.

    Compared to `sdist_isPure_le`, the advantage hypothesis uses `(a, D)` order
    matching the convention in security definitions.

    **Example usage:**
    ```
    exact sdist_of_isPure_advantageA foo_real_isPure foo_ideal_isPure hAdv
    ```
    replaces the 4-line pattern:
    ```
    apply sdist_isPure_le
    · intro x; exact foo_real_isPure x
    · intro x; exact foo_ideal_isPure x
    · intro D x; exact hAdv x D
    ``` -/
theorem sdist_of_isPure_advantageA {α β : Type*} {f g : α → SPComp β} {ε : ℝ≥0∞}
    (hf : ∀ a, SPComp.IsPure (f a)) (hg : ∀ a, SPComp.IsPure (g a))
    (hAdv : ∀ a (D : β → SPComp Bool), AdvantageA (f a) (g a) D ≤ ε) :
    sdist f g ≤ ε :=
  sdist_isPure_le hf hg (fun D a => hAdv a D)

/-- Variant of `sdist_of_isPure_advantageA` with raw `absDiff` instead of `AdvantageA`.

    For proofs where the advantage bound is stated as raw `absDiff (prTrue ...)`,
    with `(a, D)` argument order. -/
theorem sdist_of_isPure_absDiff {α β : Type*} {f g : α → SPComp β} {ε : ℝ≥0∞}
    (hf : ∀ a, SPComp.IsPure (f a)) (hg : ∀ a, SPComp.IsPure (g a))
    (hAdv : ∀ a (D : β → SPComp Bool),
      absDiff (prTrue (SPComp.bind (f a) D) Heap.empty)
              (prTrue (SPComp.bind (g a) D) Heap.empty) ≤ ε) :
    sdist f g ≤ ε :=
  sdist_isPure_le hf hg (fun D a => hAdv a D)

/-! ## Oracle-Game sdist Bridge

For oracle-based games where the game just passes an oracle record to the
adversary (`G b A = A (oracles_b)`), we can compute `sdist` from `Advantage`.

The key observations:
1. **D-absorption**: For Bool-valued output, any post-distinguisher D can be
   absorbed into the adversary: `A(o) >>= D = A'(o)` where `A' o = A o >>= D`.
2. **Heap absorption**: The adversary controls the heap via `initHeap`.
   For any initial heap `h₀`, define `A'(o) = initHeap h₀ >> A(o)`.
   Then `G b A' at Heap.empty = G b A at h₀`.

Together these show: `sdist G_real G_ideal = ⨆_A Advantage(G_real A, G_ideal A)`. -/

/-- Replace the current heap with `h₀`, discarding the old heap.
    `(initHeap h₀ >> c) h = c h₀` for any `h`. -/
noncomputable def SPComp.initHeap (h₀ : Heap) : SPComp Unit :=
  fun _ => SDistr.pure ((), h₀)

/-- Running `initHeap h₀ >> c` from any heap yields `c h₀`. -/
theorem SPComp.initHeap_bind {α : Type*} (h₀ : Heap) (c : SPComp α) (h : Heap) :
    SPComp.bind (SPComp.initHeap h₀) (fun _ => c) h = c h₀ := by
  simp [SPComp.bind, SPComp.initHeap, SDistr.pure_bind]

/-- For games of the form `G A = A record` (game is pure function application),
    `sdist` equals the supremum of `Advantage` over all adversaries.

    This bridges oracle-game security (`∀ A, Advantage ≤ ε`) to the categorical
    `sdist` framework, giving access to PPLs, composition, and tensor bounds.

    The hypotheses state that `G_real` and `G_ideal` are pure application:
    `G_real A h = A real_oracles h` and `G_ideal A h = A ideal_oracles h`. -/
theorem sdist_oracleGame_le {OracleIf : Type*}
    {G_real G_ideal : (OracleIf → SPComp Bool) → SPComp Bool}
    {or_real or_ideal : OracleIf}
    (hR : ∀ A, G_real A = A or_real)
    (hI : ∀ A, G_ideal A = A or_ideal)
    {ε : ℝ≥0∞}
    (hAdv : ∀ A, Advantage (G_real A) (G_ideal A) ≤ ε) :
    sdist G_real G_ideal ≤ ε := by
  apply iSup_le; intro D; apply iSup_le; intro A; apply iSup_le; intro h₀
  -- Step 1: Absorb D into the adversary
  -- Define A' o = A o >>= D. Then G_real A >>= D = G_real A' (since G applies A to oracles)
  let A' : OracleIf → SPComp Bool := fun o => SPComp.bind (A o) D
  have hD_real : SPComp.bind (G_real A) D = G_real A' := by
    rw [hR A, hR A']
  have hD_ideal : SPComp.bind (G_ideal A) D = G_ideal A' := by
    rw [hI A, hI A']
  -- Step 2: Absorb h₀ into the adversary
  -- Define A'' o = initHeap h₀ >> A' o. Then G_real A'' at empty = G_real A' at h₀
  let A'' : OracleIf → SPComp Bool := fun o =>
    SPComp.bind (SPComp.initHeap h₀) (fun _ => A' o)
  have hH_real : G_real A'' Heap.empty = G_real A' h₀ := by
    rw [hR A'', hR A']
    exact SPComp.initHeap_bind h₀ (A' or_real) Heap.empty
  have hH_ideal : G_ideal A'' Heap.empty = G_ideal A' h₀ := by
    rw [hI A'', hI A']
    exact SPComp.initHeap_bind h₀ (A' or_ideal) Heap.empty
  -- Step 3: Combine — prTrue at h₀ with D = prTrue at empty for A''
  have eq_real : prTrue (SPComp.bind (G_real A) D) h₀ =
      prTrue (G_real A'') Heap.empty := by
    simp only [prTrue]; congr 1; funext h
    show (SPComp.bind (G_real A) D) h₀ _ = G_real A'' Heap.empty _
    rw [hD_real, hH_real]
  have eq_ideal : prTrue (SPComp.bind (G_ideal A) D) h₀ =
      prTrue (G_ideal A'') Heap.empty := by
    simp only [prTrue]; congr 1; funext h
    show (SPComp.bind (G_ideal A) D) h₀ _ = G_ideal A'' Heap.empty _
    rw [hD_ideal, hH_ideal]
  rw [eq_real, eq_ideal]
  -- Step 4: Apply the advantage bound for A''
  exact hAdv A''

/-! ## PseudoEMetricSpace Instance

The pseudometric properties `sdist_self`, `sdist_sym`, `sdist_triangle` are exactly
the axioms of Mathlib's `PseudoEMetricSpace`. We register this instance on a wrapper
type `KlMorph α β` to make `sdist` available as `edist`, gaining automatic
triangle-inequality chaining, `edist_comm`, metric space topology, etc. -/

/-- Wrapper type for Kleisli morphisms `α → SPComp β`.
    This is a thin wrapper that exists solely to carry the `PseudoEMetricSpace`
    instance using `sdist` as the extended distance function. -/
def KlMorph (α β : Type*) := α → SPComp β

/-- Wrap a Kleisli morphism into `KlMorph`. -/
def KlMorph.mk {α β : Type*} (f : α → SPComp β) : KlMorph α β := f

/-- Unwrap a `KlMorph` to the underlying Kleisli morphism. -/
def KlMorph.run {α β : Type*} (f : KlMorph α β) : α → SPComp β := f

noncomputable instance {α β : Type*} : EDist (KlMorph α β) where
  edist f g := sdist f.run g.run

/-- `sdist` equals `edist` on `KlMorph`. -/
@[simp] theorem sdist_eq_edist {α β : Type*} (f g : KlMorph α β) :
    sdist f.run g.run = edist f g := rfl

/-- Kleisli morphisms `α → SPComp β` form a pseudo-extended-metric space
    under statistical distance. This is a pseudometric (not a metric) because
    `sdist f g = 0` does not imply `f = g` — two computationally different
    programs can have identical output distributions. -/
noncomputable instance {α β : Type*} : PseudoEMetricSpace (KlMorph α β) where
  edist_self f := sdist_self f.run
  edist_comm f g := sdist_sym f.run g.run
  edist_triangle f g h := sdist_triangle f.run g.run h.run

end CatCrypt.Crypto
