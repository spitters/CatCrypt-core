/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.NonUniform.Limit
public import CatCryptCore.Core.Code

/-!
# The ω-complete partial order on sub-distributions and stateful computations

`SDistr α` is ordered as sub-probability measures: `d₁ ≤ d₂` when every value
receives at most as much weight under `d₁` as under `d₂`. The failure weight is
not compared; it is determined by the weights of the values.

Every monotone chain has a supremum, the limit `NonUniform.mlim` of the chain,
which assigns to each value the supremum of its weights. This makes `SDistr α`
an `OmegaCompletePartialOrder`, and `SPComp α = Heap → SDistr (α × Heap)` one
pointwise. `bind` is ω-Scott-continuous in each argument, for `SDistr` and for
`SPComp`.

## Main results

* `SDistr.le_def` — the order is pointwise on the weights of values
* `SDistr.bind_mono_left`, `SDistr.bind_mono_right` — `bind` is monotone
* `SDistr.ωSup_apply_some`, `SDistr.mass_ωSup` — the weights and the mass of a supremum
* `SDistr.ωScottContinuous_bind_left`, `SDistr.ωScottContinuous_bind_right`
* `SPComp.ωSup_apply`, `SPComp.ωScottContinuous_bind_left`,
  `SPComp.ωScottContinuous_bind_right`
-/

@[expose] public section

set_option autoImplicit false

open OmegaCompletePartialOrder
open scoped ENNReal

namespace CatCrypt.Prob

namespace SDistr

variable {α β : Type*}

/-- The sub-probability order on `SDistr α`: every value receives at most as much
weight on the left as on the right. -/
instance instPartialOrder : PartialOrder (SDistr α) where
  le d₁ d₂ := ∀ a, d₁ (some a) ≤ d₂ (some a)
  le_refl _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ a := (h₁ a).trans (h₂ a)
  le_antisymm _ _ h₁ h₂ := eq_of_some_eq fun a => le_antisymm (h₁ a) (h₂ a)

/-- The order on `SDistr α` compares the weights of values. -/
theorem le_def {d₁ d₂ : SDistr α} : d₁ ≤ d₂ ↔ ∀ a, d₁ (some a) ≤ d₂ (some a) := Iff.rfl

/-- A monotone sequence of sub-distributions is a `NonUniform.MonoSeq`. -/
theorem monoSeq_of_monotone {f : ℕ → SDistr α} (hf : Monotone f) :
    NonUniform.MonoSeq f :=
  fun _ _ hnm a => hf hnm a

/-- `bind` is monotone in the distribution. -/
theorem bind_mono_left {d₁ d₂ : SDistr α} (h : d₁ ≤ d₂) (g : α → SDistr β) :
    d₁.bind g ≤ d₂.bind g := fun b => by
  simp only [NonUniform.bind_apply_some]
  exact ENNReal.tsum_le_tsum fun a => mul_le_mul' (h a) le_rfl

/-- `bind` is monotone in the continuation. -/
theorem bind_mono_right (d : SDistr α) {f g : α → SDistr β} (h : f ≤ g) :
    d.bind f ≤ d.bind g := fun b => by
  simp only [NonUniform.bind_apply_some]
  exact ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl (h a b)

/-- The supremum of a monotone chain of sub-distributions is its limit. -/
noncomputable instance instOmegaCompletePartialOrder :
    OmegaCompletePartialOrder (SDistr α) where
  ωSup c := NonUniform.mlim (fun n => c n) (monoSeq_of_monotone c.monotone)
  le_ωSup c i a := NonUniform.apply_some_le_mlim _ _ i a
  ωSup_le c _ h a := by
    rw [NonUniform.mlim_apply_some]
    exact iSup_le fun n => h n a

/-- Unfolding lemma of `ωSup`: the supremum of a chain is the limit
`NonUniform.mlim` of the chain. -/
theorem ωSup_eq_mlim (c : Chain (SDistr α)) :
    ωSup c = NonUniform.mlim (fun n => c n) (monoSeq_of_monotone c.monotone) := rfl

/-- The weight of a value under the supremum of a chain is the supremum of its
weights. -/
@[simp]
theorem ωSup_apply_some (c : Chain (SDistr α)) (a : α) :
    ωSup c (some a) = ⨆ n, c n (some a) := rfl

/-- The mass of the supremum of a chain is the supremum of the masses. -/
theorem mass_ωSup (c : Chain (SDistr α)) : mass (ωSup c) = ⨆ n, mass (c n) :=
  NonUniform.mass_mlim _ _

/-- `bind` is ω-Scott-continuous in the distribution. -/
theorem ωScottContinuous_bind_left (g : α → SDistr β) :
    ωScottContinuous fun d : SDistr α => d.bind g :=
  ωScottContinuous.of_monotone_map_ωSup
    ⟨fun _ _ h => bind_mono_left h g, fun _ => NonUniform.mlim_bind _ _ g⟩

/-- `bind` is ω-Scott-continuous in the continuation. -/
theorem ωScottContinuous_bind_right (d : SDistr α) :
    ωScottContinuous fun f : α → SDistr β => d.bind f :=
  ωScottContinuous.of_monotone_map_ωSup
    ⟨fun _ _ h => bind_mono_right d h, fun c => NonUniform.bind_mlim d (fun n => c n) _⟩

/-- Binding the supremum of a chain is the supremum of the binds. -/
theorem ωSup_bind (c : Chain (SDistr α)) (g : α → SDistr β) :
    (ωSup c).bind g = ωSup (c.map ⟨fun d => d.bind g, fun _ _ h => bind_mono_left h g⟩) :=
  NonUniform.mlim_bind _ _ g

/-- Binding into the supremum of a chain of continuations is the supremum of the
binds. -/
theorem bind_ωSup (d : SDistr α) (c : Chain (α → SDistr β)) :
    d.bind (ωSup c) = ωSup (c.map ⟨fun f => d.bind f, fun _ _ h => bind_mono_right d h⟩) :=
  NonUniform.bind_mlim d (fun n => c n) _

end SDistr

end CatCrypt.Prob

namespace CatCrypt.Core

namespace SPComp

open CatCrypt.Prob

variable {α β : Type*}

/-- The pointwise ω-complete partial order on `SPComp α = Heap → SDistr (α × Heap)`. -/
noncomputable instance instOmegaCompletePartialOrder :
    OmegaCompletePartialOrder (SPComp α) :=
  inferInstanceAs (OmegaCompletePartialOrder (Heap → SDistr (α × Heap)))

/-- The order on `SPComp α` is pointwise in the initial heap. -/
theorem le_def {c₁ c₂ : SPComp α} : c₁ ≤ c₂ ↔ ∀ h, c₁ h ≤ c₂ h := Iff.rfl

/-- The supremum of a chain of computations, run from a heap, is the supremum of
the runs. -/
theorem ωSup_apply (c : Chain (SPComp α)) (h : Heap) :
    ωSup c h = ωSup (c.map ⟨fun x => x h, fun _ _ hle => hle h⟩) := rfl

/-- `bind` is monotone in the first computation. -/
theorem bind_mono_left {c₁ c₂ : SPComp α} (hc : c₁ ≤ c₂) (f : α → SPComp β) :
    c₁.bind f ≤ c₂.bind f := fun h =>
  SDistr.bind_mono_left (hc h) _

/-- `bind` is monotone in the continuation. -/
theorem bind_mono_right (c : SPComp α) {f g : α → SPComp β} (hfg : f ≤ g) :
    c.bind f ≤ c.bind g := fun h =>
  SDistr.bind_mono_right (c h) fun ah => hfg ah.1 ah.2

/-- `bind` is ω-Scott-continuous in the first computation. -/
theorem ωScottContinuous_bind_left (f : α → SPComp β) :
    ωScottContinuous fun c : SPComp α => c.bind f :=
  ωScottContinuous.of_monotone_map_ωSup
    ⟨fun _ _ hc => bind_mono_left hc f, fun c => funext fun h =>
      NonUniform.mlim_bind _ (SDistr.monoSeq_of_monotone (c.map (Pi.evalOrderHom h)).monotone)
        _⟩

/-- `bind` is ω-Scott-continuous in the continuation. -/
theorem ωScottContinuous_bind_right (c : SPComp α) :
    ωScottContinuous fun f : α → SPComp β => c.bind f :=
  ωScottContinuous.of_monotone_map_ωSup
    ⟨fun _ _ hfg => bind_mono_right c hfg, fun C => funext fun h =>
      NonUniform.bind_mlim (c h) (fun n ah => C n ah.1 ah.2)
        fun ah => SDistr.monoSeq_of_monotone fun _ _ hnm => C.monotone hnm ah.1 ah.2⟩

end SPComp

end CatCrypt.Core
