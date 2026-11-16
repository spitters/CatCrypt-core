/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleAdversary

/-!
# Identical until bad, through state maps

Two stateful oracles that agree, read through maps of their states to a common space, at the
outcomes that are not bad, from states with equal images that are not bad, and whose bad states
stay bad, give runs of every adversary that agree at every outcome whose final image is not
bad.

## Main results

* `OracleAdv.tsum_map_mul` — a sum against the image of a distribution.
* `OracleAdv.run_map_eq_off_bad` — identical until bad, through state maps.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OracleAdv

open scoped ENNReal

variable {D R α S₁ S₂ T : Type}

open Classical in
/-- A sum against the image of a distribution is the sum against the distribution of the
composite. -/
theorem tsum_map_mul {X Y : Type} (p : PMF X) (g : X → Y) (H : Y → ℝ≥0∞) :
    ∑' w, (p.map g) w * H w = ∑' z, p z * H (g z) := by
  simp only [PMF.map_apply]
  calc ∑' w, (∑' z, if w = g z then p z else 0) * H w
        = ∑' w, ∑' z, (if w = g z then p z else 0) * H w := by
          simp only [ENNReal.tsum_mul_right]
      _ = ∑' z, ∑' w, (if w = g z then p z else 0) * H w := ENNReal.tsum_comm
      _ = ∑' z, p z * H (g z) := by
          refine tsum_congr fun z => ?_
          simp only [ite_mul, zero_mul]
          rw [tsum_ite_eq]

/-- **Identical until bad, through state maps.** Two stateful oracles whose calls, read through
maps `f₁`, `f₂` to a common space, agree at the outcomes that are not bad from states with equal
images that are not bad, and whose bad states stay bad, give runs that agree, read through the
maps, at every outcome whose final image is not bad. -/
theorem run_map_eq_off_bad (O₁ : S₁ → D → PMF (R × S₁)) (O₂ : S₂ → D → PMF (R × S₂))
    (f₁ : S₁ → T) (f₂ : S₂ → T) (bad : T → Bool)
    (hmono₁ : ∀ s d, bad (f₁ s) = true → ∀ z ∈ (O₁ s d).support, bad (f₁ z.2) = true)
    (hmono₂ : ∀ s d, bad (f₂ s) = true → ∀ z ∈ (O₂ s d).support, bad (f₂ z.2) = true)
    (hstep : ∀ s₁ s₂ d, f₁ s₁ = f₂ s₂ → bad (f₁ s₁) = false → ∀ (r : R) (u : T),
      bad u = false →
        (O₁ s₁ d).map (Prod.map id f₁) (r, u) = (O₂ s₂ d).map (Prod.map id f₂) (r, u))
    (A : OracleAdv D R α) :
    ∀ (s₁ : S₁) (s₂ : S₂), f₁ s₁ = f₂ s₂ → ∀ (a : α) (t : T), bad t = false →
      (run O₁ A s₁).map (Prod.map id f₁) (a, t) = (run O₂ A s₂).map (Prod.map id f₂) (a, t) := by
  have hbad₁ : ∀ (B : OracleAdv D R α) s, bad (f₁ s) = true → ∀ a t, bad t = false →
      (run O₁ B s).map (Prod.map id f₁) (a, t) = 0 := by
    intro B s hs a t ht
    rw [PMF.apply_eq_zero_iff, PMF.support_map]
    rintro ⟨z, hz, hzt⟩
    have := run_support_inv O₁ (fun s => bad (f₁ s) = true) (fun s d x h hx => hmono₁ s d h x hx)
      B s hs z hz
    simp only [Prod.map, Prod.mk.injEq] at hzt
    rw [hzt.2] at this
    simp_all
  have hbad₂ : ∀ (B : OracleAdv D R α) s, bad (f₂ s) = true → ∀ a t, bad t = false →
      (run O₂ B s).map (Prod.map id f₂) (a, t) = 0 := by
    intro B s hs a t ht
    rw [PMF.apply_eq_zero_iff, PMF.support_map]
    rintro ⟨z, hz, hzt⟩
    have := run_support_inv O₂ (fun s => bad (f₂ s) = true) (fun s d x h hx => hmono₂ s d h x hx)
      B s hs z hz
    simp only [Prod.map, Prod.mk.injEq] at hzt
    rw [hzt.2] at this
    simp_all
  induction A with
  | ret b =>
    intro s₁ s₂ hs a t _
    simp only [run_ret, PMF.pure_map, Prod.map, id, hs]
  | rand p k ih =>
    intro s₁ s₂ hs a t ht
    simp only [run_rand, PMF.map_bind, PMF.bind_apply]
    exact tsum_congr fun b => by rw [ih b s₁ s₂ hs a t ht]
  | query d k ih =>
    intro s₁ s₂ hs a t ht
    cases hb : bad (f₁ s₁)
    · have hmap := hstep s₁ s₂ d hs hb
      simp only [run_query, PMF.map_bind, PMF.bind_apply]
      set F₁ : R × S₁ → ℝ≥0∞ := fun z => (run O₁ (k z.1) z.2).map (Prod.map id f₁) (a, t)
      set F₂ : R × S₂ → ℝ≥0∞ := fun z => (run O₂ (k z.1) z.2).map (Prod.map id f₂) (a, t)
      classical
      let H : R × T → ℝ≥0∞ := fun w =>
        if h : ∃ z ∈ (O₂ s₂ d).support, Prod.map id f₂ z = w then F₂ h.choose else 0
      have hex₂ : ∀ z ∈ (O₁ s₁ d).support, bad (f₁ z.2) = false →
          ∃ z' ∈ (O₂ s₂ d).support, Prod.map id f₂ z' = Prod.map id f₁ z := by
        intro z hz hzb
        have h1 : Prod.map id f₁ z ∈ ((O₁ s₁ d).map (Prod.map id f₁)).support := by
          rw [PMF.support_map]
          exact ⟨z, hz, rfl⟩
        have : Prod.map id f₁ z ∈ ((O₂ s₂ d).map (Prod.map id f₂)).support := by
          rw [PMF.mem_support_iff] at h1 ⊢
          grind
        rw [PMF.support_map] at this
        exact this
      have hex₁ : ∀ z ∈ (O₂ s₂ d).support, bad (f₂ z.2) = false →
          ∃ z' ∈ (O₁ s₁ d).support, Prod.map id f₁ z' = Prod.map id f₂ z := by
        intro z hz hzb
        have h1 : Prod.map id f₂ z ∈ ((O₂ s₂ d).map (Prod.map id f₂)).support := by
          rw [PMF.support_map]
          exact ⟨z, hz, rfl⟩
        have : Prod.map id f₂ z ∈ ((O₁ s₁ d).map (Prod.map id f₁)).support := by
          rw [PMF.mem_support_iff] at h1 ⊢
          grind
        rw [PMF.support_map] at this
        exact this
      have hH0 : ∀ w : R × T, bad w.2 = true → H w = 0 := by
        intro w hw
        simp only [H]
        split_ifs with h
        · have he := h.choose_spec.2
          simp only [Prod.map, id] at he
          simp only [F₂]
          refine hbad₂ _ _ ?_ a t ht
          rw [← he] at hw
          exact hw
        · rfl
      have hF : ∀ z₁ z₂, Prod.map id f₁ z₁ = Prod.map id f₂ z₂ → F₁ z₁ = F₂ z₂ := by
        intro z₁ z₂ he
        simp only [Prod.map, id, Prod.mk.injEq] at he
        obtain ⟨h1, h2⟩ := he
        cases hz : bad (f₁ z₁.2)
        · simp only [F₁, F₂, h1]
          exact ih z₂.1 z₁.2 z₂.2 h2 a t ht
        · simp only [F₁, F₂]
          rw [hbad₁ _ _ hz a t ht, hbad₂ _ _ (h2 ▸ hz) a t ht]
      have h₁ : ∀ z ∈ (O₁ s₁ d).support, F₁ z = H (Prod.map id f₁ z) := by
        intro z hz
        cases hzb : bad (f₁ z.2)
        swap
        · rw [hH0 _ hzb]
          exact hbad₁ _ _ hzb a t ht
        obtain ⟨z', hz', he⟩ := hex₂ z hz hzb
        have hh : ∃ z'' ∈ (O₂ s₂ d).support, Prod.map id f₂ z'' = Prod.map id f₁ z :=
          ⟨z', hz', he⟩
        simp only [H, dite_eq_left hh]
        exact hF _ _ hh.choose_spec.2.symm
      have h₂ : ∀ z ∈ (O₂ s₂ d).support, F₂ z = H (Prod.map id f₂ z) := by
        intro z hz
        cases hzb : bad (f₂ z.2)
        swap
        · rw [hH0 _ hzb]
          exact hbad₂ _ _ hzb a t ht
        have hh : ∃ z'' ∈ (O₂ s₂ d).support, Prod.map id f₂ z'' = Prod.map id f₂ z :=
          ⟨z, hz, rfl⟩
        simp only [H, dite_eq_left hh]
        obtain ⟨z₁, -, he⟩ := hex₁ z hz hzb
        rw [← hF z₁ z he, hF z₁ _ (he.trans hh.choose_spec.2.symm)]
      calc ∑' z, (O₁ s₁ d) z * F₁ z = ∑' z, (O₁ s₁ d) z * H (Prod.map id f₁ z) := by
            refine tsum_congr fun z => ?_
            by_cases hz : z ∈ (O₁ s₁ d).support
            · rw [h₁ z hz]
            · rw [(PMF.apply_eq_zero_iff _ _).2 hz, zero_mul, zero_mul]
        _ = ∑' w, ((O₁ s₁ d).map (Prod.map id f₁)) w * H w := (tsum_map_mul _ _ _).symm
        _ = ∑' w, ((O₂ s₂ d).map (Prod.map id f₂)) w * H w := by
            refine tsum_congr fun w => ?_
            cases hw : bad w.2
            · rw [hmap w.1 w.2 hw]
            · rw [hH0 w hw, mul_zero, mul_zero]
        _ = ∑' z, (O₂ s₂ d) z * H (Prod.map id f₂ z) := tsum_map_mul _ _ _
        _ = ∑' z, (O₂ s₂ d) z * F₂ z := by
            refine tsum_congr fun z => ?_
            by_cases hz : z ∈ (O₂ s₂ d).support
            · rw [h₂ z hz]
            · rw [(PMF.apply_eq_zero_iff _ _).2 hz, zero_mul, zero_mul]
    · rw [hbad₁ _ s₁ hb a t ht, hbad₂ _ s₂ (hs ▸ hb) a t ht]

end CatCrypt.Crypto.OracleAdv
