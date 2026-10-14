/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCMonad.QuantumUC
public import CatCryptCore.Quantum.TensorProduct

/-!
# Diamond norm for the quantum instrument monad

The diamond (completely-bounded) distance on `QComp d` Kleisli morphisms.
`qdist` takes input states on dimension `d` only; `qdistDiamond` takes input
states on `d ⊗ r` for a reference register of arbitrary dimension `r`, applying
the channel on register 1 (`localOp₁`) and the identity on the reference:

```
qdistDiamond f g = ⨆ r, qdist (f ⊗ id_r) (g ⊗ id_r)
```

This is the stabilized distance `‖Φ_f − Φ_g‖_⋄ = sup_r ‖(Φ_f − Φ_g) ⊗ id_r‖`.

Each channel branch is required to be completely positive (`IsCPMap`), as
`localOp₁` requires; positivity alone is not preserved by tensoring with an
identity (the transpose map is the counterexample).

## Main results

* `qdistDiamond` — the diamond distance, `⨆ r, qdist (f ⊗ id_r) (g ⊗ id_r)`.
* `qdistDiamond_self` / `qdistDiamond_sym` / `qdistDiamond_triangle` — the
  pseudometric laws.
* `QUCEmulatesDiamond ε f g` — the bound `qdistDiamond f g ≤ ε`, with
  reflexivity, monotonicity in `ε`, symmetry and transitivity.

The domination of the CP-restricted distance `qdistCP ≤ qdistDiamond` is in
`CatCryptCore.Crypto.UCMonad.DiamondDominates`; stability of `qdistDiamond`
under tensoring with an identity register is in
`CatCryptCore.Crypto.UCMonad.DiamondTensorStable`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCMonad.DiamondNorm

open CatCrypt.Quantum
open CatCrypt.Quantum.TensorProduct
open UCMonad.QuantumUC
open scoped ENNReal

variable {d : ℕ} {α β : Type}

/-- A Kleisli morphism `f : α → QComp d β` is a completely-positive channel if
every branch is a CP map (the condition `localOp₁` needs to tensor it with an
identity reference). -/
def IsCPChannel (f : α → QComp d β) : Prop :=
  ∀ a b, IsCPMap ((f a).branch b)

/-- `f` extended with an `r`-dimensional reference register: apply `f` on
register 1, identity on the reference. -/
noncomputable def withRef (r : ℕ) (f : α → QComp d β) (hf : IsCPChannel f) :
    α → QComp (d * r) β :=
  fun a => localOp₁ (d₂ := r) (f a) (hf a)

/-! ## The diamond distance -/

/-- **Diamond distance.** The supremum, over all reference-register sizes `r`,
of the induced distance between the reference-extended channels. This is the
completely-bounded / diamond norm `‖Φ_f − Φ_g‖_⋄`, the stabilized distance that
includes an ancilla the bare `qdist` omits. -/
noncomputable def qdistDiamond (f g : α → QComp d β)
    (hf : IsCPChannel f) (hg : IsCPChannel g) : ℝ≥0∞ :=
  ⨆ r : ℕ, qdist (withRef r f hf) (withRef r g hg)

/-! ## Pseudometric laws -/

/-- Reflexivity: the diamond distance of a channel to itself is `0`. -/
theorem qdistDiamond_self (f : α → QComp d β) (hf : IsCPChannel f) :
    qdistDiamond f f hf hf = 0 := by
  simp only [qdistDiamond, qdist_self, iSup_const]

/-- Symmetry. -/
theorem qdistDiamond_sym (f g : α → QComp d β)
    (hf : IsCPChannel f) (hg : IsCPChannel g) :
    qdistDiamond f g hf hg = qdistDiamond g f hg hf := by
  simp only [qdistDiamond]
  exact iSup_congr (fun r => qdist_sym _ _)

/-- Triangle inequality. -/
theorem qdistDiamond_triangle (f g h : α → QComp d β)
    (hf : IsCPChannel f) (hg : IsCPChannel g) (hh : IsCPChannel h) :
    qdistDiamond f h hf hh ≤ qdistDiamond f g hf hg + qdistDiamond g h hg hh := by
  simp only [qdistDiamond]
  apply iSup_le
  intro r
  calc qdist (withRef r f hf) (withRef r h hh)
      ≤ qdist (withRef r f hf) (withRef r g hg)
        + qdist (withRef r g hg) (withRef r h hh) := qdist_triangle _ _ _
    _ ≤ (⨆ s, qdist (withRef s f hf) (withRef s g hg))
        + (⨆ s, qdist (withRef s g hg) (withRef s h hh)) :=
        add_le_add (le_iSup (fun s => qdist (withRef s f hf) (withRef s g hg)) r)
          (le_iSup (fun s => qdist (withRef s g hg) (withRef s h hh)) r)

/-! ## Diamond-distance emulation

`QUCEmulatesDiamond ε f g` is the bound `qdistDiamond f g ≤ ε`. It quantifies
over distinguishers acting on the channel output together with a reference
register of arbitrary dimension; it has no simulator quantifier. -/

/-- `f` and `g` are within diamond distance `ε`: `qdistDiamond f g ≤ ε`. -/
def QUCEmulatesDiamond (ε : ℝ≥0∞) (f g : α → QComp d β)
    (hf : IsCPChannel f) (hg : IsCPChannel g) : Prop :=
  qdistDiamond f g hf hg ≤ ε

/-- Reflexivity: every channel emulates itself at any `ε`. -/
theorem QUCEmulatesDiamond.refl (ε : ℝ≥0∞) (f : α → QComp d β)
    (hf : IsCPChannel f) : QUCEmulatesDiamond ε f f hf hf := by
  unfold QUCEmulatesDiamond; rw [qdistDiamond_self]; exact zero_le

/-- Monotonicity in the error bound. -/
theorem QUCEmulatesDiamond.mono {ε₁ ε₂ : ℝ≥0∞} {f g : α → QComp d β}
    {hf : IsCPChannel f} {hg : IsCPChannel g}
    (h : QUCEmulatesDiamond ε₁ f g hf hg) (hle : ε₁ ≤ ε₂) :
    QUCEmulatesDiamond ε₂ f g hf hg :=
  le_trans h hle

/-- Symmetry. -/
theorem QUCEmulatesDiamond.symm {ε : ℝ≥0∞} {f g : α → QComp d β}
    {hf : IsCPChannel f} {hg : IsCPChannel g}
    (h : QUCEmulatesDiamond ε f g hf hg) : QUCEmulatesDiamond ε g f hg hf := by
  unfold QUCEmulatesDiamond; rw [qdistDiamond_sym]; exact h

/-- Transitivity with additive error. -/
theorem QUCEmulatesDiamond.trans {ε₁ ε₂ : ℝ≥0∞} {f g h : α → QComp d β}
    {hf : IsCPChannel f} {hg : IsCPChannel g} {hh : IsCPChannel h}
    (h₁ : QUCEmulatesDiamond ε₁ f g hf hg)
    (h₂ : QUCEmulatesDiamond ε₂ g h hg hh) :
    QUCEmulatesDiamond (ε₁ + ε₂) f h hf hh :=
  le_trans (qdistDiamond_triangle f g h hf hg hh) (add_le_add h₁ h₂)

end CatCrypt.Crypto.UCMonad.DiamondNorm
