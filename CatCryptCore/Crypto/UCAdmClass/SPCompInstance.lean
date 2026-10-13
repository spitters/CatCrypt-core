/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UC
public import CatCryptCore.Crypto.UCLevels
public import CatCryptCore.Crypto.UCMonad.SPCompInstance

/-!
# SPComp Instance of UCAdmClass and UCMonadCompDist

This file provides the concrete `UCMonadCompDist SPComp` instance with
**trivial admissibility** (everything is admissible), connecting the
computational security framework to the existing `SPComp` infrastructure.

## Design: Trivial Admissibility

With `adm := fun _ => True`, every Kleisli arrow is admissible. This means:
- `ucCdist = ucSdist` (restricted sup = unrestricted sup)
- Level 2 = Level 1
- Level 3 = Level 1 (since all simulators are admissible)

This is the correct instance for information-theoretic security.
For genuine computational security (Level 2 ≠ Level 1), one would provide
a different `UCAdmClass SPComp` instance with `adm` restricting to
polynomial-time Kleisli arrows (requires a cost model not currently in CatCrypt).

## Main results

* `UCAdmClass SPComp` — trivial admissibility instance
* `UCMonadCompDist SPComp` — per-distinguisher decomposition instance
* `ucCdist_eq_ucSdist_trivial` — `ucCdist = ucSdist` with trivial adm
* `L2_iff_L1_trivial` — Level 2 ↔ Level 1 equivalence
-/

@[expose] public section

namespace UCMonad

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto

open scoped ENNReal

/-! ## Section 1: Trivial Admissibility -/

/-- Trivial admissibility: everything is admissible.
    Makes `ucCdist = ucSdist` and Level 2 = Level 1. -/
noncomputable instance : UCAdmClass SPComp where
  adm := fun _ => True
  adm_pure := trivial
  adm_bind := fun _ _ => trivial
  adm_mapSum := fun _ _ => trivial
  adm_precomp := fun _ _ => trivial

/-! ## Section 2: Per-Distinguisher Decomposition -/

/-- Per-distinguisher distance component for SPComp:
    `ucDistComp f g D = ⨆ (a : α) (h₀ : Heap), absDiff(prTrue(f a >>= D, h₀), ...)` -/
noncomputable def spcomp_distComp {α β : Type}
    (f g : α → SPComp β) (D : β → SPComp Bool) : ℝ≥0∞ :=
  ⨆ (a : α) (h₀ : Heap),
    absDiff (prTrue (SPComp.bind (f a) D) h₀) (prTrue (SPComp.bind (g a) D) h₀)

theorem spcomp_distComp_self {α β : Type}
    (f : α → SPComp β) (D : β → SPComp Bool) :
    spcomp_distComp f f D = 0 := by
  simp [spcomp_distComp, absDiff_self]

theorem spcomp_distComp_comm {α β : Type}
    (f g : α → SPComp β) (D : β → SPComp Bool) :
    spcomp_distComp f g D = spcomp_distComp g f D := by
  simp only [spcomp_distComp]
  congr 1; funext a; congr 1; funext h₀
  exact absDiff_comm _ _

theorem spcomp_distComp_triangle {α β : Type}
    (f g h : α → SPComp β) (D : β → SPComp Bool) :
    spcomp_distComp f h D ≤ spcomp_distComp f g D + spcomp_distComp g h D := by
  apply iSup_le; intro a
  apply iSup_le; intro h₀
  calc absDiff (prTrue (SPComp.bind (f a) D) h₀)
               (prTrue (SPComp.bind (h a) D) h₀)
      ≤ absDiff (prTrue (SPComp.bind (f a) D) h₀)
                 (prTrue (SPComp.bind (g a) D) h₀) +
        absDiff (prTrue (SPComp.bind (g a) D) h₀)
                 (prTrue (SPComp.bind (h a) D) h₀) :=
        absDiff_triangle _ _ _
    _ ≤ spcomp_distComp f g D + spcomp_distComp g h D := by
        apply add_le_add
        · exact le_iSup₂_of_le a h₀ le_rfl
        · exact le_iSup₂_of_le a h₀ le_rfl

theorem spcomp_sdist_eq_iSup {α β : Type}
    (f g : α → SPComp β) :
    sdist f g = ⨆ D, spcomp_distComp f g D := by
  simp only [sdist, spcomp_distComp]

theorem spcomp_distComp_bind_right {α β γ : Type}
    (f g : α → SPComp β) (k : β → SPComp γ) (D : γ → SPComp Bool) :
    spcomp_distComp (fun a => SPComp.bind (f a) k) (fun a => SPComp.bind (g a) k) D =
    spcomp_distComp f g (fun b => SPComp.bind (k b) D) := by
  simp only [spcomp_distComp]
  congr 1; funext a; congr 1; funext h₀
  congr 1
  · congr 1; exact SPComp.bind_assoc (f a) k D
  · congr 1; exact SPComp.bind_assoc (g a) k D

/-- Left PPL at per-distinguisher level for SPComp.
    Uses the convexity argument: `absDiff` of weighted averages ≤ sup of pointwise `absDiff`. -/
theorem spcomp_distComp_bind_left {α β γ : Type}
    (f : α → SPComp β) (g₁ g₂ : β → SPComp γ) (D : γ → SPComp Bool) :
    spcomp_distComp (fun a => SPComp.bind (f a) g₁) (fun a => SPComp.bind (f a) g₂) D ≤
    spcomp_distComp g₁ g₂ D := by
  apply iSup_le; intro a
  apply iSup_le; intro h₀
  have eq1 : SPComp.bind (SPComp.bind (f a) g₁) D =
    SPComp.bind (f a) (fun b => SPComp.bind (g₁ b) D) := SPComp.bind_assoc _ _ _
  have eq2 : SPComp.bind (SPComp.bind (f a) g₂) D =
    SPComp.bind (f a) (fun b => SPComp.bind (g₂ b) D) := SPComp.bind_assoc _ _ _
  rw [eq1, eq2]
  set ε := spcomp_distComp g₁ g₂ D
  apply absDiff_prTrue_bind_le (f a) _ _ h₀ ε
  · intro b h'
    exact le_add_of_absDiff_le (le_iSup₂_of_le b h' le_rfl)
  · intro b h'
    exact le_add_of_absDiff_le
      (by rw [absDiff_comm]; exact le_iSup₂_of_le b h' le_rfl)

/-- Per-distinguisher decomposition of `mapSum` for SPComp.
    Case-splits on the sum input; each component absorbs `pure ∘ inl/inr` via `bind_assoc`. -/
theorem spcomp_distComp_mapSum {α₁ β₁ α₂ β₂ : Type}
    (f₁ f₂ : α₁ → SPComp β₁) (g₁ g₂ : α₂ → SPComp β₂) (D : β₁ ⊕ β₂ → SPComp Bool) :
    spcomp_distComp (mapSum f₁ g₁) (mapSum f₂ g₂) D ≤
    spcomp_distComp f₁ f₂ (fun b => D (Sum.inl b)) ⊔
    spcomp_distComp g₁ g₂ (fun d => D (Sum.inr d)) := by
  apply iSup_le; intro x
  apply iSup_le; intro h₀
  rcases x with a | c
  · -- .inl a: only f runs
    simp only [mapSum_inl, SPComp.map]
    have eq1 : SPComp.bind (SPComp.bind (f₁ a) fun b => SPComp.pure (Sum.inl b)) D =
      SPComp.bind (f₁ a) (fun b => D (Sum.inl b)) := by
      rw [SPComp.bind_assoc]; congr 1; funext b; simp
    have eq2 : SPComp.bind (SPComp.bind (f₂ a) fun b => SPComp.pure (Sum.inl b)) D =
      SPComp.bind (f₂ a) (fun b => D (Sum.inl b)) := by
      rw [SPComp.bind_assoc]; congr 1; funext b; simp
    rw [eq1, eq2]
    exact le_sup_left.trans' (le_iSup₂_of_le a h₀ le_rfl)
  · -- .inr c: only g runs
    simp only [mapSum_inr, SPComp.map]
    have eq1 : SPComp.bind (SPComp.bind (g₁ c) fun d => SPComp.pure (Sum.inr d)) D =
      SPComp.bind (g₁ c) (fun d => D (Sum.inr d)) := by
      rw [SPComp.bind_assoc]; congr 1; funext d; simp
    have eq2 : SPComp.bind (SPComp.bind (g₂ c) fun d => SPComp.pure (Sum.inr d)) D =
      SPComp.bind (g₂ c) (fun d => D (Sum.inr d)) := by
      rw [SPComp.bind_assoc]; congr 1; funext d; simp
    rw [eq1, eq2]
    exact le_sup_right.trans' (le_iSup₂_of_le c h₀ le_rfl)

/-- The `UCMonadCompDist SPComp` instance with trivial admissibility. -/
noncomputable instance : UCMonadCompDist SPComp where
  ucDistComp := spcomp_distComp
  ucSdist_eq_iSup_distComp := spcomp_sdist_eq_iSup
  ucDistComp_bind_right := spcomp_distComp_bind_right
  ucDistComp_bind_left := spcomp_distComp_bind_left
  ucDistComp_self := spcomp_distComp_self
  ucDistComp_comm := spcomp_distComp_comm
  ucDistComp_triangle := spcomp_distComp_triangle
  ucDistComp_mapSum := spcomp_distComp_mapSum

/-! ## Section 3: Bridge Lemmas -/

/-- With trivial admissibility, `ucCdist = ucSdist`.
    Proof: `⨆ {D | True} = ⨆ D`. -/
theorem ucCdist_eq_ucSdist_trivial {α β : Type}
    (f g : α → SPComp β) :
    ucCdist f g = UCMonadMetric.ucSdist (T := SPComp) f g := by
  apply le_antisymm
  · exact ucCdist_le_ucSdist f g
  · rw [UCMonadCompDist.ucSdist_eq_iSup_distComp]
    apply iSup_le; intro D
    exact le_iSup₂ (f := fun D _ => UCMonadCompDist.ucDistComp f g D) D trivial

/-- With trivial admissibility, Level 2 is equivalent to Level 1. -/
theorem L2_iff_L1_trivial {hon out leak sim_if view : Type} {ε : ℝ≥0∞}
    (π : hon → SPComp (out ⊕ leak))
    (F : hon → SPComp (out ⊕ sim_if)) :
    UCEmulatesL2 (T := SPComp) (view := view) ε π F ↔
    UCEmulates (T := SPComp) (view := view) ε π F := by
  constructor
  · intro h A
    obtain ⟨S, hS⟩ := h A
    exact ⟨S, by rwa [ucCdist_eq_ucSdist_trivial] at hS⟩
  · exact UCEmulatesL2_of_L1

/-- With trivial admissibility, Level 3 is equivalent to Level 1.
    Since all arrows are admissible, the `adm S` requirement is trivially satisfied. -/
theorem L3_iff_L1_trivial {hon out leak sim_if view : Type} {ε : ℝ≥0∞}
    (π : hon → SPComp (out ⊕ leak))
    (F : hon → SPComp (out ⊕ sim_if)) :
    UCEmulatesL3 (T := SPComp) (view := view) ε π F ↔
    UCEmulates (T := SPComp) (view := view) ε π F := by
  constructor
  · intro h A
    obtain ⟨S, _, hS⟩ := h A
    exact ⟨S, by rw [ucCdist_eq_ucSdist_trivial] at hS; exact hS⟩
  · intro h A
    obtain ⟨S, hS⟩ := h A
    exact ⟨S, trivial, by rw [ucCdist_eq_ucSdist_trivial]; exact hS⟩

end UCMonad
