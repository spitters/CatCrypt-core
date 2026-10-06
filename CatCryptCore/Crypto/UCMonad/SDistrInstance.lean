/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCMonad
public import CatCryptCore.Prob.SDistr

/-!
# SDistr Instance of UCMonad

This file provides the `UCMonad SDistr` instance, connecting the generic
typeclass to the heap-free sub-probability distribution monad.

This is the "pure" counterpart to `UCMonad/SPCompInstance.lean`: while `SPComp`
models stateful probabilistic computations (with heap), `SDistr` models
pure probabilistic computations (no heap). The `SDistr` instance is useful
for compositional reasoning where heap state is unnecessary.

## Main results

* `UCMonad SDistr` — the instance
* `mapSumD` — parallel composition on `Sum` for SDistr
* `sdistD` — statistical distance for SDistr Kleisli morphisms

## Design

The instance fields:
- `ucMapSum` → `mapSumD` (defined here)
- `ucFail` → `SDistr.fail`
- `ucSdist` → `sdistD` (defined here)

The `sdistD` definition mirrors `sdist` from `SDist.lean` but without the
heap quantifier, since `SDistr` computations are heap-free.
-/

@[expose] public section

namespace UCMonad.SDistrUC

open CatCrypt.Prob
open CatCrypt.Prob.SDistr
open scoped ENNReal

/-! ## Parallel Composition on Sum -/

/-- Parallel composition on `Sum` for SDistr: apply `f` on `.inl`, `g` on `.inr`. -/
noncomputable def mapSumD {α β γ δ : Type} (f : α → SDistr β) (g : γ → SDistr δ) :
    (α ⊕ γ) → SDistr (β ⊕ δ)
  | .inl a => SDistr.bind (f a) (fun b => SDistr.pure (.inl b))
  | .inr c => SDistr.bind (g c) (fun d => SDistr.pure (.inr d))

@[simp]
theorem mapSumD_inl {α β γ δ : Type} (f : α → SDistr β) (g : γ → SDistr δ) (a : α) :
    mapSumD f g (.inl a) = SDistr.bind (f a) (fun b => SDistr.pure (.inl b)) := rfl

@[simp]
theorem mapSumD_inr {α β γ δ : Type} (f : α → SDistr β) (g : γ → SDistr δ) (c : γ) :
    mapSumD f g (.inr c) = SDistr.bind (g c) (fun d => SDistr.pure (.inr d)) := rfl

/-- `mapSumD pure pure = pure` (identity on Sum). -/
theorem mapSumD_pure_pure {α β : Type} :
    mapSumD (SDistr.pure (α := α)) (SDistr.pure (α := β)) = SDistr.pure := by
  funext x; rcases x with a | b
  · simp [mapSumD, SDistr.pure_bind]
  · simp [mapSumD, SDistr.pure_bind]

/-- Kleisli functoriality: `(id ⊕ f) ∘ₖ (id ⊕ g) = id ⊕ (f ∘ₖ g)`. -/
theorem mapSumD_pure_kleisli {α β γ δ : Type} (f : β → SDistr γ) (g : γ → SDistr δ) :
    (fun x : α ⊕ β => SDistr.bind (mapSumD SDistr.pure f x) (mapSumD SDistr.pure g))
    = mapSumD SDistr.pure (fun b => SDistr.bind (f b) g) := by
  funext x; rcases x with a | b
  · simp [mapSumD, SDistr.pure_bind]
  · simp [mapSumD, SDistr.pure_bind, SDistr.bind_assoc]

/-! ## Statistical Distance -/

/-- Absolute difference for ℝ≥0∞. -/
noncomputable def absDiffD (a b : ℝ≥0∞) : ℝ≥0∞ := (a - b) ⊔ (b - a)

theorem absDiffD_self (a : ℝ≥0∞) : absDiffD a a = 0 := by
  simp [absDiffD, tsub_self]

theorem absDiffD_comm (a b : ℝ≥0∞) : absDiffD a b = absDiffD b a := by
  simp [absDiffD, max_comm]

theorem absDiffD_triangle (a b c : ℝ≥0∞) :
    absDiffD a c ≤ absDiffD a b + absDiffD b c := by
  simp only [absDiffD]
  apply max_le
  · calc a - c ≤ (a - b) + (b - c) := tsub_le_tsub_add_tsub
      _ ≤ ((a - b) ⊔ (b - a)) + ((b - c) ⊔ (c - b)) :=
        add_le_add (le_max_left _ _) (le_max_left _ _)
  · calc c - a ≤ (c - b) + (b - a) := tsub_le_tsub_add_tsub
      _ ≤ ((c - b) ⊔ (b - c)) + ((b - a) ⊔ (a - b)) :=
        add_le_add (le_max_left _ _) (le_max_left _ _)
      _ = ((a - b) ⊔ (b - a)) + ((b - c) ⊔ (c - b)) := by
        rw [max_comm (c - b), max_comm (b - a), add_comm]

/-- Probability of `true` in a Bool sub-distribution. -/
noncomputable def prTrueD (d : SDistr Bool) : ℝ≥0∞ := d (some true)

/-- Statistical distance between SDistr Kleisli morphisms.

    `sdistD f g = sup_{D,a} |Pr[f(a) >>= D => true] - Pr[g(a) >>= D => true]|`

    This is the heap-free analogue of `sdist` from `SDist.lean`. -/
noncomputable def sdistD {α β : Type} (f g : α → SDistr β) : ℝ≥0∞ :=
  ⨆ (D : β → SDistr Bool) (a : α),
    absDiffD (prTrueD (SDistr.bind (f a) D)) (prTrueD (SDistr.bind (g a) D))

/-! ## Pseudometric Properties -/

theorem sdistD_self {α β : Type} (f : α → SDistr β) : sdistD f f = 0 := by
  simp [sdistD, absDiffD_self]

theorem sdistD_sym {α β : Type} (f g : α → SDistr β) : sdistD f g = sdistD g f := by
  simp only [sdistD, absDiffD_comm]

theorem sdistD_triangle {α β : Type} (f g h : α → SDistr β) :
    sdistD f h ≤ sdistD f g + sdistD g h := by
  apply iSup_le; intro D; apply iSup_le; intro a
  calc absDiffD (prTrueD (SDistr.bind (f a) D)) (prTrueD (SDistr.bind (h a) D))
      ≤ absDiffD (prTrueD (SDistr.bind (f a) D)) (prTrueD (SDistr.bind (g a) D))
        + absDiffD (prTrueD (SDistr.bind (g a) D)) (prTrueD (SDistr.bind (h a) D)) :=
        absDiffD_triangle _ _ _
    _ ≤ sdistD f g + sdistD g h := add_le_add
        (le_iSup_of_le D (le_iSup_of_le a le_rfl))
        (le_iSup_of_le D (le_iSup_of_le a le_rfl))

/-! ## Post-Processing Lemmas -/

/-- Right PPL: post-composition doesn't increase distance. -/
theorem sdistD_comp_right {α β γ : Type} (f g : α → SDistr β) (k : β → SDistr γ) :
    sdistD (fun a => SDistr.bind (f a) k) (fun a => SDistr.bind (g a) k) ≤ sdistD f g := by
  apply iSup_le; intro D; apply iSup_le; intro a
  have hf : SDistr.bind (SDistr.bind (f a) k) D =
      SDistr.bind (f a) (fun b => SDistr.bind (k b) D) :=
    SDistr.bind_assoc _ _ _
  have hg : SDistr.bind (SDistr.bind (g a) k) D =
      SDistr.bind (g a) (fun b => SDistr.bind (k b) D) :=
    SDistr.bind_assoc _ _ _
  rw [hf, hg]
  exact le_iSup_of_le (fun b => SDistr.bind (k b) D) (le_iSup_of_le a le_rfl)

/-- `absDiffD a b ≤ ε` implies `a ≤ b + ε`. -/
theorem le_add_of_absDiffD_le {a b ε : ℝ≥0∞} (h : absDiffD a b ≤ ε) :
    a ≤ b + ε := by
  have hab : a - b ≤ ε := le_trans (le_max_left _ _) h
  calc a ≤ a - b + b := le_tsub_add
    _ ≤ ε + b := by gcongr
    _ = b + ε := add_comm _ _

/-- Weighted average bound: if `∀ i, f i ≤ g i + ε` and `∑ w i ≤ 1`,
    then `∑ w i * f i ≤ (∑ w i * g i) + ε`. -/
theorem weighted_bound {ι : Type} (w f g : ι → ℝ≥0∞) (ε : ℝ≥0∞)
    (hfg : ∀ i, f i ≤ g i + ε) (hw : ∑' i, w i ≤ 1) :
    ∑' i, w i * f i ≤ (∑' i, w i * g i) + ε := by
  calc ∑' i, w i * f i
      ≤ ∑' i, w i * (g i + ε) := by
        apply ENNReal.tsum_le_tsum; intro i; gcongr; exact hfg i
    _ = ∑' i, (w i * g i + w i * ε) := by congr 1; funext i; ring
    _ = (∑' i, w i * g i) + ∑' i, w i * ε := ENNReal.tsum_add
    _ = (∑' i, w i * g i) + (∑' i, w i) * ε := by
        congr 1; rw [ENNReal.tsum_mul_right]
    _ ≤ (∑' i, w i * g i) + 1 * ε := by gcongr
    _ = (∑' i, w i * g i) + ε := by ring

/-- Representation: `prTrueD(bind c k) = ∑' p, c(p) * val(p, k)`.
    Factors out the weighted-sum structure of `prTrueD(bind ...)`. -/
theorem prTrueD_bind_eq_weighted {α : Type}
    (c : SDistr α) (k : α → SDistr Bool) :
    prTrueD (SDistr.bind c k) =
      ∑' (p : Option α), c p *
        (match p with | some a => prTrueD (k a) | none => 0) := by
  unfold prTrueD SDistr.bind SDistr.fail
  simp only [PMF.bind_apply]
  congr 1; funext p; cases p with
  | none => simp [PMF.pure_apply]
  | some a => rfl

/-- Left PPL helper: weighted average of ε-close values is ε-close. -/
theorem absDiffD_prTrueD_bind_le {α : Type}
    (c : SDistr α) (k₁ k₂ : α → SDistr Bool) (ε : ℝ≥0∞)
    (hk : ∀ a, prTrueD (k₁ a) ≤ prTrueD (k₂ a) + ε)
    (hk' : ∀ a, prTrueD (k₂ a) ≤ prTrueD (k₁ a) + ε) :
    absDiffD (prTrueD (SDistr.bind c k₁)) (prTrueD (SDistr.bind c k₂)) ≤ ε := by
  rw [prTrueD_bind_eq_weighted c k₁, prTrueD_bind_eq_weighted c k₂]
  have hv : ∀ p : Option α,
      (match p with | some a => prTrueD (k₁ a) | none => 0) ≤
      (match p with | some a => prTrueD (k₂ a) | none => 0) + ε := by
    intro p; cases p with
    | none => exact zero_le
    | some a => exact hk a
  have hv' : ∀ p : Option α,
      (match p with | some a => prTrueD (k₂ a) | none => 0) ≤
      (match p with | some a => prTrueD (k₁ a) | none => 0) + ε := by
    intro p; cases p with
    | none => exact zero_le
    | some a => exact hk' a
  have hw : ∑' p, c p ≤ 1 := le_of_eq c.tsum_coe
  simp only [absDiffD]
  apply max_le
  · rw [tsub_le_iff_right]
    exact le_trans (weighted_bound _ _ _ ε hv hw) (le_of_eq (add_comm _ _))
  · rw [tsub_le_iff_right]
    exact le_trans (weighted_bound _ _ _ ε hv' hw) (le_of_eq (add_comm _ _))

/-- Left PPL: pre-composition with shared prefix doesn't increase distance. -/
theorem sdistD_comp_left {α β γ : Type} (f : α → SDistr β) (g₁ g₂ : β → SDistr γ) :
    sdistD (fun a => SDistr.bind (f a) g₁) (fun a => SDistr.bind (f a) g₂) ≤ sdistD g₁ g₂ := by
  apply iSup_le; intro D; apply iSup_le; intro a
  have eq1 : SDistr.bind (SDistr.bind (f a) g₁) D =
    SDistr.bind (f a) (fun b => SDistr.bind (g₁ b) D) := SDistr.bind_assoc _ _ _
  have eq2 : SDistr.bind (SDistr.bind (f a) g₂) D =
    SDistr.bind (f a) (fun b => SDistr.bind (g₂ b) D) := SDistr.bind_assoc _ _ _
  rw [eq1, eq2]
  set ε := sdistD g₁ g₂
  apply absDiffD_prTrueD_bind_le (f a) _ _ ε
  · intro b
    exact le_add_of_absDiffD_le (le_iSup_of_le D (le_iSup_of_le b le_rfl))
  · intro b
    exact le_add_of_absDiffD_le
      (by rw [absDiffD_comm]; exact le_iSup_of_le D (le_iSup_of_le b le_rfl))

/-! ## Affine Property -/

theorem sdistr_bind_fail {α β : Type} (c : SDistr α) :
    SDistr.bind c (fun _ => (SDistr.fail : SDistr β)) = SDistr.fail := by
  simp only [SDistr.bind, SDistr.fail]
  calc PMF.bind c _ = PMF.bind c (fun _ => PMF.pure (none : Option β)) := by
        congr 1; funext oa; cases oa <;> rfl
    _ = PMF.pure none := PMF.bind_const _ _

/-! ## The UCMonad Instance -/

noncomputable instance : UCMonad SDistr where
  ucMapSum := @mapSumD
  ucMapSum_inl := fun _f _g _a => rfl
  ucMapSum_inr := fun _f _g _c => rfl
  ucMapSum_pure_pure := mapSumD_pure_pure
  ucMapSum_pure_kleisli := fun f g => mapSumD_pure_kleisli f g
  ucFail := SDistr.fail
  ucBind_fail := fun c => sdistr_bind_fail c
  ucSdist := @sdistD
  ucSdist_self := sdistD_self
  ucSdist_sym := sdistD_sym
  ucSdist_triangle := sdistD_triangle
  ucSdist_comp_right := sdistD_comp_right
  ucSdist_comp_left := sdistD_comp_left

end UCMonad.SDistrUC
