/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCryptCore.Crypto.UCMonad
public import CatCryptCore.Quantum.Instrument

/-!
# Quantum UC via the UCMonad Framework

This file defines a `UCMonad (QComp d)` instance for every Hilbert space
dimension `d`.

## Architecture

The quantum computation monad `QComp d` (from `CatCryptCore.Quantum.Instrument`)
represents quantum instruments with classical outcomes on a `d`-dimensional
Hilbert space. Each `QComp d α` value is a family of completely positive
linear maps `{E_a}_{a∈α}` on `d×d` complex matrices.

The `UCMonad` instance provides:
- **Coproducts** (A1): `QComp.mapSum` — controlled quantum operations
- **Failure** (A2): `QComp.qfail` — abort/discard channel
- **Pseudometric** (A3): `qdist` — distinguisher-supremum distance with PPL
- **Monad laws** (A4): from `LawfulMonad (QComp d)`

## Statistical Distance (induced distinguishability distance)

The distance `qdist` is defined as:
```
qdist f g = sup_{D,a,ρ} |prTrue_Q(bind(f a)(D), ρ) - prTrue_Q(bind(g a)(D), ρ)|
```
where the supremum ranges over:
- `D : β → QComp d Bool` (quantum distinguisher)
- `a : α` (input)
- `ρ : DensityMatrix d` (input quantum state)

The input `ρ` is a state on dimension `d` with no reference register, so
`qdist` is the distinguishing distance without a reference register. The
diamond (completely-bounded) distance, which adds a reference register of
arbitrary dimension, is `qdistDiamond` in
`CatCryptCore.Crypto.UCMonad.DiamondNorm`.
-/

@[expose] public section

open scoped ENNReal
open CatCrypt.Quantum

namespace UCMonad.QuantumUC

variable {d : ℕ}

/-! ## Section 1: Statistical Distance for QComp -/

/-- Statistical distance between QComp Kleisli morphisms. -/
noncomputable def qdist {α β : Type} (f g : α → QComp d β) : ℝ≥0∞ :=
  ⨆ (D : β → QComp d Bool) (a : α) (ρ : DensityMatrix d),
    absDiff (prTrue_Q (QComp.qbind (f a) D) ρ)
            (prTrue_Q (QComp.qbind (g a) D) ρ)

/-! ## Section 2: Pseudometric Properties -/

theorem qdist_self {α β : Type} (f : α → QComp d β) : qdist f f = 0 := by
  simp [qdist, absDiff_self]

theorem qdist_sym {α β : Type} (f g : α → QComp d β) :
    qdist f g = qdist g f := by
  simp only [qdist, absDiff_comm]

theorem qdist_triangle {α β : Type} (f g h : α → QComp d β) :
    qdist f h ≤ qdist f g + qdist g h := by
  apply iSup_le; intro D; apply iSup_le; intro a; apply iSup_le; intro ρ
  calc absDiff (prTrue_Q (QComp.qbind (f a) D) ρ)
               (prTrue_Q (QComp.qbind (h a) D) ρ)
      ≤ absDiff (prTrue_Q (QComp.qbind (f a) D) ρ)
                 (prTrue_Q (QComp.qbind (g a) D) ρ)
        + absDiff (prTrue_Q (QComp.qbind (g a) D) ρ)
                   (prTrue_Q (QComp.qbind (h a) D) ρ) :=
        absDiff_triangle _ _ _
    _ ≤ qdist f g + qdist g h := add_le_add
        (le_iSup_of_le D (le_iSup_of_le a (le_iSup_of_le ρ le_rfl)))
        (le_iSup_of_le D (le_iSup_of_le a (le_iSup_of_le ρ le_rfl)))

/-! ## Section 3: Post-Processing Lemmas -/

/-- Right PPL: post-composition doesn't increase distance. -/
theorem qdist_comp_right {α β γ : Type} (f g : α → QComp d β)
    (k : β → QComp d γ) :
    qdist (fun a => QComp.qbind (f a) k) (fun a => QComp.qbind (g a) k)
    ≤ qdist f g := by
  apply iSup_le; intro D; apply iSup_le; intro a; apply iSup_le; intro ρ
  have hf : QComp.qbind (QComp.qbind (f a) k) D =
      QComp.qbind (f a) (fun b => QComp.qbind (k b) D) :=
    QComp.qbind_assoc (f a) k D
  have hg : QComp.qbind (QComp.qbind (g a) k) D =
      QComp.qbind (g a) (fun b => QComp.qbind (k b) D) :=
    QComp.qbind_assoc (g a) k D
  rw [hf, hg]
  exact le_iSup_of_le (fun b => QComp.qbind (k b) D)
    (le_iSup_of_le a (le_iSup_of_le ρ le_rfl))

/-- Auxiliary: `absDiff a b ≤ ε` implies `a ≤ b + ε` (quantum namespace). -/
theorem le_add_of_absDiff_le {a b ε : ℝ≥0∞} (h : absDiff a b ≤ ε) :
    a ≤ b + ε := by
  have hab : a - b ≤ ε := le_trans (le_max_left _ _) h
  calc a ≤ a - b + b := le_tsub_add
    _ ≤ ε + b := by gcongr
    _ = b + ε := add_comm _ _

/-- Left PPL: pre-composition with shared prefix doesn't increase distance. -/
theorem qdist_comp_left {α β γ : Type} (f : α → QComp d β)
    (g₁ g₂ : β → QComp d γ) :
    qdist (fun a => QComp.qbind (f a) g₁)
          (fun a => QComp.qbind (f a) g₂)
    ≤ qdist g₁ g₂ := by
  apply iSup_le; intro D; apply iSup_le; intro a; apply iSup_le; intro ρ
  have eq1 : QComp.qbind (QComp.qbind (f a) g₁) D =
    QComp.qbind (f a) (fun b => QComp.qbind (g₁ b) D) :=
    QComp.qbind_assoc (f a) g₁ D
  have eq2 : QComp.qbind (QComp.qbind (f a) g₂) D =
    QComp.qbind (f a) (fun b => QComp.qbind (g₂ b) D) :=
    QComp.qbind_assoc (f a) g₂ D
  rw [eq1, eq2]
  apply absDiff_prTrue_Q_qbind_le (f a) _ _ ρ (qdist g₁ g₂)
  intro b ρ'
  exact le_iSup_of_le D (le_iSup_of_le b (le_iSup_of_le ρ' le_rfl))

/-! ## Section 4: UCMonad Instance -/

noncomputable instance : UCMonad (QComp d) where
  ucMapSum := @QComp.mapSum d
  ucMapSum_inl := QComp.mapSum_inl
  ucMapSum_inr := QComp.mapSum_inr
  ucMapSum_pure_pure := QComp.mapSum_pure_pure
  ucMapSum_pure_kleisli := fun f g => QComp.mapSum_pure_kleisli f g
  ucFail := QComp.qfail
  ucBind_fail := fun c => QComp.qbind_fail c
  ucSdist := @qdist d
  ucSdist_self := qdist_self
  ucSdist_sym := qdist_sym
  ucSdist_triangle := qdist_triangle
  ucSdist_comp_right := qdist_comp_right
  ucSdist_comp_left := qdist_comp_left

/-! ## Section 5: Demonstration — Generic Theorems Applied to QComp d -/

example {hon out leak : Type} (π : hon → QComp d (out ⊕ leak)) :
    UCEmulates (T := QComp d) (view := out ⊕ leak) 0 π π :=
  UCEmulates_refl π

example {hon out leak : Type} {ε₁ ε₂ : ℝ≥0∞}
    {π₁ π₂ π₃ : hon → QComp d (out ⊕ leak)}
    (h₁ : UCEmulates (T := QComp d) (view := out ⊕ leak) ε₁ π₁ π₂)
    (h₂ : UCEmulates (T := QComp d) (view := out ⊕ leak) ε₂ π₂ π₃) :
    UCEmulates (T := QComp d) (view := out ⊕ leak) (ε₁ + ε₂) π₁ π₃ :=
  UCEmulates_trans h₁ h₂

example {hon out : Type} {P Q R : ProtObj (QComp d) hon out} {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : approxFact ε₁ P Q) (h₂ : approxFact ε₂ Q R) :
    approxFact (ε₁ + ε₂) P R :=
  approxFact_trans h₁ h₂

example {hon out : Type} {P Q : ProtObj (QComp d) hon out}
    {view : Type} {ε : ℝ≥0∞} (h : approxFact ε P Q) :
    UCEmulates (T := QComp d) (view := view) ε P.prot Q.prot :=
  approxFact_implies_UCEmulates h

example {hon out leak : Type} {ε₁ ε₂ : ℝ≥0∞} {view : Type}
    {π₁ π₂ π₃ : hon → QComp d (out ⊕ leak)}
    {Sim₁ Sim₂ : SimConstruction (QComp d) leak leak view}
    (h₁ : UCEmulatesAlg (T := QComp d) ε₁ π₁ π₂ Sim₁)
    (h₂ : UCEmulatesAlg (T := QComp d) ε₂ π₂ π₃ Sim₂) :
    UCEmulatesAlg (T := QComp d) (ε₁ + ε₂) π₁ π₃ (Sim₂ ∘ Sim₁) :=
  UCEmulatesAlg.trans h₁ h₂

end UCMonad.QuantumUC
