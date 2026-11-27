/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Basic.ENNReal.Basic
public import Std.Internal.Order.Lemmas

/-!
# The `Lean.Order` complete lattice of `ℝ≥0∞`

Lean's `Lean.Order.CompleteLattice` is the order structure of the toolchain's predicate
transformers (`Std.WP`). A Mathlib complete lattice gives one, with `⊑` the order `≤` and the
supremum of a predicate the `sSup` of its extension (`CompleteLattice.toLeanOrder`). This
module states it for `ℝ≥0∞` and its order dual, the carriers of expectations, and identifies
the `Lean.Order` bottom, top, binary meet and suprema of `ℝ≥0∞` with those of Mathlib. The meet
with a fixed element preserves suprema, because `ℝ≥0∞` is a frame.

## Main definitions

* `CompleteLattice.toLeanOrder`: the `Lean.Order` complete lattice of a Mathlib complete
  lattice.
* The `Lean.Order.CompleteLattice` and `Lean.Order.CCPO` instances on `ℝ≥0∞` and `ℝ≥0∞ᵒᵈ`.

## Main results

* `ENNReal.leanOrder_bot_eq_zero`, `ENNReal.leanOrder_top_eq_top`,
  `ENNReal.leanOrder_meet_eq_min`, `ENNReal.leanOrder_sup_eq_sSup`,
  `ENNReal.leanOrder_iSup_eq_iSup`: the `Lean.Order` operations are Mathlib's.
* `ENNReal.instPreservesSupLeanOrderMeet`: the meet with a fixed element preserves suprema.

## Search words

complete lattice, chain-complete partial order, extended nonnegative reals, expectation,
predicate transformer, meet, supremum, frame
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal

/-- The `Lean.Order` complete lattice of a Mathlib complete lattice: `⊑` is `≤` and the
supremum of a predicate is the `sSup` of its extension. -/
abbrev CompleteLattice.toLeanOrder (α : Type) [CompleteLattice α] :
    Lean.Order.CompleteLattice α where
  rel a b := a ≤ b
  rel_refl := le_refl _
  rel_trans := le_trans
  rel_antisymm := le_antisymm
  has_sup c :=
    ⟨sSup {x | c x}, fun _ => ⟨fun hsup _ hcy => le_trans (le_sSup hcy) hsup, sSup_le⟩⟩

namespace ENNReal

noncomputable instance instLeanOrderCompleteLattice : Lean.Order.CompleteLattice ℝ≥0∞ :=
  CompleteLattice.toLeanOrder ℝ≥0∞

noncomputable instance instLeanOrderCompleteLatticeDual : Lean.Order.CompleteLattice ℝ≥0∞ᵒᵈ :=
  CompleteLattice.toLeanOrder ℝ≥0∞ᵒᵈ

/-- The chain-complete partial order of `ℝ≥0∞` induced by its complete lattice; it supplies
the bottom `Lean.Order.bot`. -/
noncomputable instance instLeanOrderCCPO : Lean.Order.CCPO ℝ≥0∞ where
  has_csup {c} _ := Lean.Order.CompleteLattice.has_sup c

/-- The chain-complete partial order of `ℝ≥0∞ᵒᵈ` induced by its complete lattice. -/
noncomputable instance instLeanOrderCCPODual : Lean.Order.CCPO ℝ≥0∞ᵒᵈ where
  has_csup {c} _ := Lean.Order.CompleteLattice.has_sup c

/-- The `Lean.Order` relation on `ℝ≥0∞` is `≤`: the unfolding lemma of the instance. -/
@[simp] theorem leanOrder_rel_iff_le (a b : ℝ≥0∞) :
    Lean.Order.PartialOrder.rel a b ↔ a ≤ b := Iff.rfl

/-- The `Lean.Order` relation on `ℝ≥0∞ᵒᵈ` is the reversed `≤` of `ℝ≥0∞`: the unfolding lemma
of the instance. -/
@[simp] theorem leanOrder_rel_dual_iff (a b : ℝ≥0∞ᵒᵈ) :
    Lean.Order.PartialOrder.rel a b ↔ OrderDual.ofDual b ≤ OrderDual.ofDual a := Iff.rfl

/-- The `Lean.Order` bottom of `ℝ≥0∞` is `0`. -/
theorem leanOrder_bot_eq_zero : (Lean.Order.bot : ℝ≥0∞) = 0 :=
  le_antisymm (Lean.Order.bot_le (0 : ℝ≥0∞)) zero_le

/-- The `Lean.Order` top of `ℝ≥0∞` is `⊤`. -/
theorem leanOrder_top_eq_top : (Lean.Order.top : ℝ≥0∞) = ⊤ :=
  le_antisymm le_top (Lean.Order.le_top (⊤ : ℝ≥0∞))

/-- The binary meet of `Lean.Order` on `ℝ≥0∞` is `min`. -/
theorem leanOrder_meet_eq_min (x y : ℝ≥0∞) : Lean.Order.meet x y = min x y :=
  le_antisymm (le_min (Lean.Order.meet_le_left x y) (Lean.Order.meet_le_right x y))
    (Lean.Order.le_meet (min x y) x y (min_le_left x y) (min_le_right x y))

/-- The supremum of `Lean.Order` on `ℝ≥0∞` is `sSup`. -/
theorem leanOrder_sup_eq_sSup (s : ℝ≥0∞ → Prop) :
    Lean.Order.CompleteLattice.sup s = sSup {x | s x} :=
  le_antisymm (Lean.Order.sup_le s fun _ hy => le_sSup hy)
    (sSup_le fun _ hy => Lean.Order.le_sup s hy)

/-- The indexed supremum of `Lean.Order` on `ℝ≥0∞` is `⨆`. -/
theorem leanOrder_iSup_eq_iSup {ι : Type} (f : ι → ℝ≥0∞) : Lean.Order.iSup f = ⨆ i, f i :=
  le_antisymm (Lean.Order.iSup_le f (⨆ i, f i) fun i => le_iSup f i)
    (iSup_le fun i => Lean.Order.le_iSup f i)

/-- The meet with a fixed `x : ℝ≥0∞` in `Lean.Order` preserves suprema. -/
instance instPreservesSupLeanOrderMeet (x : ℝ≥0∞) :
    Lean.Order.PreservesSup (Lean.Order.meet x) where
  map_sup s := by
    simp only [leanOrder_meet_eq_min, leanOrder_sup_eq_sSup]
    refine le_antisymm ?_ (sSup_le ?_)
    · rw [inf_sSup_eq]
      exact iSup₂_le fun y hy => le_sSup ⟨y, hy, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact min_le_min le_rfl (le_sSup hy)

end ENNReal
