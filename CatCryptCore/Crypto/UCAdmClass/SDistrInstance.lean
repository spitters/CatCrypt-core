/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCLevels
public import CatCryptCore.Crypto.UCMonad.SDistrInstance

/-!
# SDistr Instance of UCAdmClass and UCMonadCompDist

This file provides the concrete `UCMonadCompDist SDistr` instance with
**trivial admissibility** (everything is admissible), connecting the
computational security framework to the heap-free sub-probability monad.

## Design: Trivial Admissibility

With `adm := fun _ => True`, every Kleisli arrow is admissible. This means:
- `ucCdist = ucSdist` (restricted sup = unrestricted sup)
- Level 2 = Level 1
- Level 3 = Level 1 (since all simulators are admissible)

This mirrors the `SPComp` instance in `UCAdmClass/SPCompInstance.lean`.

## Main results

* `UCAdmClass SDistr` — trivial admissibility instance
* `UCMonadCompDist SDistr` — per-distinguisher decomposition instance
* `ucCdist_eq_ucSdist_trivial_sdistr` — `ucCdist = ucSdist` with trivial adm
* `L2_iff_L1_trivial_sdistr` — Level 2 ↔ Level 1 equivalence
-/

@[expose] public section

namespace UCMonad

open CatCrypt.Prob
open UCMonad.SDistrUC
open scoped ENNReal

/-! ## Section 1: Trivial Admissibility -/

/-- Trivial admissibility for SDistr: everything is admissible.
    Makes `ucCdist = ucSdist` and Level 2 = Level 1. -/
noncomputable instance : UCAdmClass SDistr where
  adm := fun _ => True
  adm_pure := trivial
  adm_bind := fun _ _ => trivial
  adm_mapSum := fun _ _ => trivial
  adm_precomp := fun _ _ => trivial

/-! ## Section 2: Per-Distinguisher Decomposition -/

/-- Per-distinguisher distance component for SDistr:
    `sdistr_distComp f g D = ⨆ (a : α), absDiffD(prTrueD(f a >>= D), ...)` -/
noncomputable def sdistr_distComp {α β : Type}
    (f g : α → SDistr β) (D : β → SDistr Bool) : ℝ≥0∞ :=
  ⨆ (a : α),
    absDiffD (prTrueD (SDistr.bind (f a) D)) (prTrueD (SDistr.bind (g a) D))

/-- A sub-distribution is at distance zero from itself for every distinguisher. -/
theorem sdistr_distComp_self {α β : Type}
    (f : α → SDistr β) (D : β → SDistr Bool) :
    sdistr_distComp f f D = 0 := by
  simp [sdistr_distComp, absDiffD_self]

/-- The per-distinguisher distance is symmetric. -/
theorem sdistr_distComp_comm {α β : Type}
    (f g : α → SDistr β) (D : β → SDistr Bool) :
    sdistr_distComp f g D = sdistr_distComp g f D := by
  simp only [sdistr_distComp]
  congr 1; funext a
  exact absDiffD_comm _ _

/-- The per-distinguisher distance satisfies the triangle inequality. -/
theorem sdistr_distComp_triangle {α β : Type}
    (f g h : α → SDistr β) (D : β → SDistr Bool) :
    sdistr_distComp f h D ≤ sdistr_distComp f g D + sdistr_distComp g h D := by
  apply iSup_le; intro a
  calc absDiffD (prTrueD (SDistr.bind (f a) D))
               (prTrueD (SDistr.bind (h a) D))
      ≤ absDiffD (prTrueD (SDistr.bind (f a) D))
                 (prTrueD (SDistr.bind (g a) D)) +
        absDiffD (prTrueD (SDistr.bind (g a) D))
                 (prTrueD (SDistr.bind (h a) D)) :=
        absDiffD_triangle _ _ _
    _ ≤ sdistr_distComp f g D + sdistr_distComp g h D := by
        apply add_le_add
        · exact le_iSup_of_le a le_rfl
        · exact le_iSup_of_le a le_rfl

/-- The statistical distance `sdistD` is the supremum of the per-distinguisher distances. -/
theorem sdistr_sdistD_eq_iSup {α β : Type}
    (f g : α → SDistr β) :
    sdistD f g = ⨆ D, sdistr_distComp f g D := by
  simp only [sdistD, sdistr_distComp]

/-- Post-composing both arrows with `k` is the same as pre-composing the distinguisher with `k`. -/
theorem sdistr_distComp_bind_right {α β γ : Type}
    (f g : α → SDistr β) (k : β → SDistr γ) (D : γ → SDistr Bool) :
    sdistr_distComp (fun a => SDistr.bind (f a) k) (fun a => SDistr.bind (g a) k) D =
    sdistr_distComp f g (fun b => SDistr.bind (k b) D) := by
  simp only [sdistr_distComp]
  congr 1; funext a
  congr 1
  · congr 1; exact SDistr.bind_assoc (f a) k D
  · congr 1; exact SDistr.bind_assoc (g a) k D

/-- Left PPL at per-distinguisher level for SDistr.
    Uses the convexity argument: `absDiffD` of weighted averages ≤ sup of pointwise `absDiffD`. -/
theorem sdistr_distComp_bind_left {α β γ : Type}
    (f : α → SDistr β) (g₁ g₂ : β → SDistr γ) (D : γ → SDistr Bool) :
    sdistr_distComp (fun a => SDistr.bind (f a) g₁) (fun a => SDistr.bind (f a) g₂) D ≤
    sdistr_distComp g₁ g₂ D := by
  apply iSup_le; intro a
  have eq1 : SDistr.bind (SDistr.bind (f a) g₁) D =
    SDistr.bind (f a) (fun b => SDistr.bind (g₁ b) D) := SDistr.bind_assoc _ _ _
  have eq2 : SDistr.bind (SDistr.bind (f a) g₂) D =
    SDistr.bind (f a) (fun b => SDistr.bind (g₂ b) D) := SDistr.bind_assoc _ _ _
  rw [eq1, eq2]
  set ε := sdistr_distComp g₁ g₂ D
  apply absDiffD_prTrueD_bind_le (f a) _ _ ε
  · intro b
    exact le_add_of_absDiffD_le (le_iSup_of_le b le_rfl)
  · intro b
    exact le_add_of_absDiffD_le
      (by rw [absDiffD_comm]; exact le_iSup_of_le b le_rfl)

/-- Per-distinguisher decomposition of `mapSum` for SDistr.
    Case-splits on the sum input; each component absorbs `pure ∘ inl/inr` via `bind_assoc`. -/
theorem sdistr_distComp_mapSum {α₁ β₁ α₂ β₂ : Type}
    (f₁ f₂ : α₁ → SDistr β₁) (g₁ g₂ : α₂ → SDistr β₂)
    (D : β₁ ⊕ β₂ → SDistr Bool) :
    sdistr_distComp (mapSumD f₁ g₁) (mapSumD f₂ g₂) D ≤
    sdistr_distComp f₁ f₂ (fun b => D (Sum.inl b)) ⊔
    sdistr_distComp g₁ g₂ (fun d => D (Sum.inr d)) := by
  apply iSup_le; intro x
  rcases x with a | c
  · -- .inl a: only f runs
    simp only [mapSumD_inl]
    have eq1 : SDistr.bind (SDistr.bind (f₁ a) fun b => SDistr.pure (.inl b)) D =
      SDistr.bind (f₁ a) (fun b => D (.inl b)) := by
      rw [SDistr.bind_assoc]; congr 1; funext b; simp [SDistr.pure_bind]
    have eq2 : SDistr.bind (SDistr.bind (f₂ a) fun b => SDistr.pure (.inl b)) D =
      SDistr.bind (f₂ a) (fun b => D (.inl b)) := by
      rw [SDistr.bind_assoc]; congr 1; funext b; simp [SDistr.pure_bind]
    rw [eq1, eq2]
    exact le_sup_left.trans' (le_iSup_of_le a le_rfl)
  · -- .inr c: only g runs
    simp only [mapSumD_inr]
    have eq1 : SDistr.bind (SDistr.bind (g₁ c) fun d => SDistr.pure (.inr d)) D =
      SDistr.bind (g₁ c) (fun d => D (.inr d)) := by
      rw [SDistr.bind_assoc]; congr 1; funext d; simp [SDistr.pure_bind]
    have eq2 : SDistr.bind (SDistr.bind (g₂ c) fun d => SDistr.pure (.inr d)) D =
      SDistr.bind (g₂ c) (fun d => D (.inr d)) := by
      rw [SDistr.bind_assoc]; congr 1; funext d; simp [SDistr.pure_bind]
    rw [eq1, eq2]
    exact le_sup_right.trans' (le_iSup_of_le c le_rfl)

/-- The `UCMonadCompDist SDistr` instance with trivial admissibility. -/
noncomputable instance : UCMonadCompDist SDistr where
  ucDistComp := sdistr_distComp
  ucSdist_eq_iSup_distComp := sdistr_sdistD_eq_iSup
  ucDistComp_bind_right := sdistr_distComp_bind_right
  ucDistComp_bind_left := sdistr_distComp_bind_left
  ucDistComp_self := sdistr_distComp_self
  ucDistComp_comm := sdistr_distComp_comm
  ucDistComp_triangle := sdistr_distComp_triangle
  ucDistComp_mapSum := sdistr_distComp_mapSum

/-! ## Section 3: Bridge Lemmas -/

/-- With trivial admissibility, `ucCdist = ucSdist` for SDistr.
    Proof: `⨆ {D | True} = ⨆ D`. -/
theorem ucCdist_eq_ucSdist_trivial_sdistr {α β : Type}
    (f g : α → SDistr β) :
    ucCdist f g = UCMonadMetric.ucSdist (T := SDistr) f g := by
  apply le_antisymm
  · exact ucCdist_le_ucSdist f g
  · rw [UCMonadCompDist.ucSdist_eq_iSup_distComp]
    apply iSup_le; intro D
    exact le_iSup₂ (f := fun D _ => UCMonadCompDist.ucDistComp f g D) D trivial

/-- With trivial admissibility, Level 2 is equivalent to Level 1 for SDistr. -/
theorem L2_iff_L1_trivial_sdistr {hon out leak sim_if view : Type} {ε : ℝ≥0∞}
    (π : hon → SDistr (out ⊕ leak))
    (F : hon → SDistr (out ⊕ sim_if)) :
    UCEmulatesL2 (T := SDistr) (view := view) ε π F ↔
    UCEmulates (T := SDistr) (view := view) ε π F := by
  constructor
  · intro h A
    obtain ⟨S, hS⟩ := h A
    exact ⟨S, by rwa [ucCdist_eq_ucSdist_trivial_sdistr] at hS⟩
  · exact UCEmulatesL2_of_L1

/-- With trivial admissibility, Level 3 is equivalent to Level 1 for SDistr.
    Since all arrows are admissible, the `adm S` requirement is trivially satisfied. -/
theorem L3_iff_L1_trivial_sdistr {hon out leak sim_if view : Type} {ε : ℝ≥0∞}
    (π : hon → SDistr (out ⊕ leak))
    (F : hon → SDistr (out ⊕ sim_if)) :
    UCEmulatesL3 (T := SDistr) (view := view) ε π F ↔
    UCEmulates (T := SDistr) (view := view) ε π F := by
  constructor
  · intro h A
    obtain ⟨S, _, hS⟩ := h A
    exact ⟨S, by rw [ucCdist_eq_ucSdist_trivial_sdistr] at hS; exact hS⟩
  · intro h A
    obtain ⟨S, hS⟩ := h A
    exact ⟨S, trivial, by rw [ucCdist_eq_ucSdist_trivial_sdistr]; exact hS⟩

end UCMonad
