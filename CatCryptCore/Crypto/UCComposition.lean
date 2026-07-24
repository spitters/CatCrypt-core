/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.RC

/-!
# UC Subroutine Composition

This file proves the UC subroutine composition theorem: if protocol π
is sdist-close to functionality F, and subroutine ρ_real is sdist-close to ρ_ideal,
then the compiled protocol `compile π ρ_real` is sdist-close to `compile F ρ_ideal`
with error ε₁ + ε₂. UC emulation follows via `UCEmulates_of_sdist`.

## Main results

* `sdist_compile` — compile preserves sdist bounds additively
* `sdist_compile_same` — compile with same subroutine preserves sdist
* `UCEmulates_compile` — UC composition via compile + sdist
* `UCEmulates_seq` — sequential composition (re-export of `UCEmulates_trans`)
* `UCEmulates_par` — parallel composition (re-export of `UCEmulates_mapSum_of_sdist`)

## Proof strategy

The proof uses the triangle inequality:
1. `sdist(compile π ρ_real, compile π ρ_ideal) ≤ ε₂` by left PPL on subroutine
2. `sdist(compile π ρ_ideal, compile F ρ_ideal) ≤ ε₁` by right PPL on protocol

## References

* Canetti, Universally Composable Security, 2001
* Patrignani et al., UC is RC, TOPLAS 2024
-/

namespace CatCrypt.Crypto.UCComposition

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

/-! ## Compile Distance Bounds -/

/-- **Compile with same subroutine**: sdist is preserved. -/
theorem sdist_compile_same
    {α β γ δ : Type*}
    {ε : ℝ≥0∞}
    (π F : α → SPComp (β ⊕ γ))
    (ρ : γ → SPComp δ)
    (hπ : sdist π F ≤ ε) :
    sdist (compile π ρ) (compile F ρ) ≤ ε := by
  show sdist (fun a => SPComp.bind (π a) (mapSum SPComp.pure ρ))
      (fun a => SPComp.bind (F a) (mapSum SPComp.pure ρ)) ≤ ε
  exact le_trans (sdist_comp_right π F _) hπ

/-- **Compile with different subroutines**: sdist bounds are additive.

Triangle through `compile π ρ_ideal`:
- `sdist(compile π ρ_real, compile π ρ_ideal) ≤ ε₂` (subroutine swap)
- `sdist(compile π ρ_ideal, compile F ρ_ideal) ≤ ε₁` (protocol swap) -/
theorem sdist_compile
    {α β γ δ : Type*}
    {ε₁ ε₂ : ℝ≥0∞}
    (π F : α → SPComp (β ⊕ γ))
    (ρ_real ρ_ideal : γ → SPComp δ)
    (hπ : sdist π F ≤ ε₁)
    (hρ : sdist ρ_real ρ_ideal ≤ ε₂) :
    sdist (compile π ρ_real) (compile F ρ_ideal) ≤ ε₁ + ε₂ := by
  -- Triangle through compile π ρ_ideal
  calc sdist (compile π ρ_real) (compile F ρ_ideal)
      ≤ sdist (compile π ρ_real) (compile π ρ_ideal) +
        sdist (compile π ρ_ideal) (compile F ρ_ideal) := sdist_triangle _ _ _
    _ ≤ ε₂ + ε₁ := by
        apply add_le_add
        · -- Subroutine swap: same protocol π, different subroutines
          show sdist (fun a => SPComp.bind (π a) (mapSum SPComp.pure ρ_real))
              (fun a => SPComp.bind (π a) (mapSum SPComp.pure ρ_ideal)) ≤ ε₂
          have h1 := sdist_comp_left π (mapSum SPComp.pure ρ_real) (mapSum SPComp.pure ρ_ideal)
          have h2 : sdist (mapSum (SPComp.pure (α := β)) ρ_real)
              (mapSum (SPComp.pure (α := β)) ρ_ideal)
              ≤ sdist ρ_real ρ_ideal := by
            calc sdist (mapSum SPComp.pure ρ_real) (mapSum SPComp.pure ρ_ideal)
                ≤ sdist (SPComp.pure (α := β)) SPComp.pure ⊔ sdist ρ_real ρ_ideal :=
                  sdist_mapSum_le _ _ _ _ le_rfl le_rfl
              _ = 0 ⊔ sdist ρ_real ρ_ideal := by rw [sdist_self]
              _ = sdist ρ_real ρ_ideal := by simp
          exact le_trans h1 (le_trans h2 hρ)
        · -- Protocol swap: different protocols, same subroutine
          exact sdist_compile_same π F ρ_ideal hπ
    _ = ε₁ + ε₂ := add_comm ε₂ ε₁

/-! ## UC Emulation via Compile -/

/-- **UC Subroutine Composition** (same-interface).

The compiled protocol `compile π ρ_real` UC-emulates `compile F ρ_ideal`
with error `ε₁ + ε₂`, using `leak = sim_if = δ` (same adversary interface).

Since `compile` outputs `α → SPComp (β ⊕ δ)`, the natural UC spec has
`out = β` and `leak = sim_if = δ`. -/
theorem UCEmulates_compile
    {α β γ δ : Type*} {V : Type*}
    {ε₁ ε₂ : ℝ≥0∞}
    (π F : α → SPComp (β ⊕ γ))
    (ρ_real ρ_ideal : γ → SPComp δ)
    (hπ : sdist π F ≤ ε₁)
    (hρ : sdist ρ_real ρ_ideal ≤ ε₂) :
    UCEmulates (ε₁ + ε₂) ⟨α, β, δ, δ, V⟩
      (compile π ρ_real) (compile F ρ_ideal) :=
  UCEmulates_of_sdist _ _ _ (sdist_compile π F ρ_real ρ_ideal hπ hρ)

/-- **Same subroutine UC**: compile with same subroutine preserves UC bound. -/
theorem UCEmulates_compile_same_sub
    {α β γ δ : Type*} {V : Type*}
    {ε : ℝ≥0∞}
    (π F : α → SPComp (β ⊕ γ))
    (ρ : γ → SPComp δ)
    (hπ : sdist π F ≤ ε) :
    UCEmulates ε ⟨α, β, δ, δ, V⟩ (compile π ρ) (compile F ρ) :=
  UCEmulates_of_sdist _ _ _ (sdist_compile_same π F ρ hπ)

/-- **Perfect subroutine**: when ρ_real = ρ_ideal, only protocol gap matters. -/
theorem UCEmulates_compile_perfect
    {α β γ δ : Type*} {V : Type*}
    {ε : ℝ≥0∞}
    (π F : α → SPComp (β ⊕ γ))
    (ρ : γ → SPComp δ)
    (hπ : sdist π F ≤ ε) :
    UCEmulates ε ⟨α, β, δ, δ, V⟩ (compile π ρ) (compile F ρ) :=
  UCEmulates_compile_same_sub π F ρ hπ

/-! ## Sequential and Parallel Composition -/

/-- Sequential composition: if π₁ → π₂ (ε₁) and π₂ → π₃ (ε₂),
    then π₁ → π₃ (ε₁ + ε₂). Re-exported from `UCEmulates_trans`. -/
theorem UCEmulates_seq {hon out leak view : Type*} {ε₁ ε₂ : ℝ≥0∞}
    {π₁ π₂ π₃ : hon → SPComp (out ⊕ leak)}
    (h₁ : UCEmulates ε₁ ⟨hon, out, leak, leak, view⟩ π₁ π₂)
    (h₂ : UCEmulates ε₂ ⟨hon, out, leak, leak, view⟩ π₂ π₃) :
    UCEmulates (ε₁ + ε₂) ⟨hon, out, leak, leak, view⟩ π₁ π₃ :=
  UCEmulates_trans h₁ h₂

/-- Parallel composition: max(ε₁, ε₂) bound on coproduct.
    Re-exported from `UCEmulates_mapSum_of_sdist`. -/
theorem UCEmulates_par
    {α₁ β₁ α₂ β₂ V : Type*}
    {ε₁ ε₂ : ℝ≥0∞}
    (π₁ F₁ : α₁ → SPComp β₁) (π₂ F₂ : α₂ → SPComp β₂)
    (h₁ : sdist π₁ F₁ ≤ ε₁) (h₂ : sdist π₂ F₂ ≤ ε₂) :
    UCEmulates (ε₁ ⊔ ε₂)
      ⟨α₁ ⊕ α₂, Unit, β₁ ⊕ β₂, β₁ ⊕ β₂, V⟩
      (fun x => SPComp.bind (mapSum π₁ π₂ x) (fun o => SPComp.pure (Sum.inr o)))
      (fun x => SPComp.bind (mapSum F₁ F₂ x) (fun o => SPComp.pure (Sum.inr o))) :=
  UCEmulates_mapSum_of_sdist π₁ F₁ π₂ F₂ h₁ h₂

end CatCrypt.Crypto.UCComposition
