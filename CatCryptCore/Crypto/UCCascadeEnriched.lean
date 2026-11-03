/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCCascade
public import Mathlib.CategoryTheory.Enriched.Basic

/-!
# Reactive systems as a category enriched in Lawvere metric spaces

The distance `Cell1.dist f g` between two classes of lossless systems with the same interface is
the infimum of the statistical bounds at which `f` realizes `g`, that is, of the bounds of the
2-cells `f ⟶ g` of `RSysBicat.bicategory`. Realization at a statistical bound is a closed
condition in the bound, so the infimum is attained: `dist f g ≤ ε` holds exactly when `f`
realizes `g` at bound `ε` (`Cell1.dist_le_iff`).

Each hom-type `Cell1 E O` is a Lawvere metric space: `dist f f = 0` and
`dist f h ≤ dist f g + dist g h`. The cascade is non-expansive for the sum distance on pairs,
`dist (f.seq g) (f'.seq g') ≤ dist f f' + dist g g'`. The category whose objects are types of
ports and whose morphisms are classes of lossless systems under the cascade is thereby a
category enriched in Lawvere metric spaces with the `ℓ¹` tensor product; its underlying ordinary
category is the part at distance `0`, the 2-cells of bound `0` (`Cell1.dist_eq_zero_iff`).

Lawvere's value category is `([0,∞], ≥, +, 0)`: the type `LawvereV`, the order dual of `ℝ≥0∞`
as a thin category with tensor `+` and unit `0` (`LawvereV.monoidal`). Each `Cell1 E O` is a
category enriched in `LawvereV` in the sense of `CategoryTheory.EnrichedCategory`
(`Cell1.enriched`). The enrichment of the category of ports in Lawvere metric spaces is stated
by the theorems on `Cell1.dist`; Mathlib has no monoidal category of Lawvere metric spaces in
which to state it as an `EnrichedCategory` instance.

The distance needs bounds independent of the environment. Under the cascade, a bound that
depends on the environment is evaluated at the environments reduced through the other component
(`realizes_seq`), so two such bounds do not compose to a single number per pair of classes.

## Main definitions

* `LawvereV`, `LawvereV.monoidal`: the monoidal preorder `([0,∞], ≥, +, 0)`.
* `Cell1.dist`: the realization distance between classes of lossless systems.
* `Cell1.enriched`: a hom-type of `RSysBicat` as a `LawvereV`-enriched category.

## Main results

* `Cell1.dist_le_iff`, `Cell1.dist_le_iff_hom`: the distance is the least realization bound.
* `Cell1.dist_self`, `Cell1.dist_triangle`: each hom-type is a Lawvere metric space.
* `Cell1.dist_seq_le`: the cascade is non-expansive.
* `Cell1.dist_eq_zero_iff`: distance `0` is realization at bound `0`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CategoryTheory MonoidalCategory
open scoped ENNReal

/-- Lawvere's value category `([0,∞], ≥, +, 0)`: the order dual of `ℝ≥0∞`, a thin category with
a morphism `a ⟶ b` exactly when `b ≤ a` in `ℝ≥0∞`. -/
def LawvereV : Type := (ℝ≥0∞)ᵒᵈ

namespace LawvereV

/-- The order of `LawvereV`, the reverse of the order of `ℝ≥0∞`. -/
instance : Preorder LawvereV := inferInstanceAs (Preorder (ℝ≥0∞)ᵒᵈ)

/-- The element of `LawvereV` of a value in `ℝ≥0∞`. -/
def of (a : ℝ≥0∞) : LawvereV := OrderDual.toDual a

/-- The value in `ℝ≥0∞` of an element of `LawvereV`. -/
def val (a : LawvereV) : ℝ≥0∞ := OrderDual.ofDual a

/-- Unfolding lemma of `val` at `of a`. -/
@[simp] theorem val_of (a : ℝ≥0∞) : (of a).val = a := rfl

/-- A morphism of `LawvereV` from `a` to `b` is the inequality `b.val ≤ a.val`. -/
theorem le_iff {a b : LawvereV} : a ≤ b ↔ b.val ≤ a.val := Iff.rfl

/-- The morphism of `LawvereV` of an inequality of values. -/
def homOf {a b : LawvereV} (h : b.val ≤ a.val) : a ⟶ b := homOfLE h

/-- The inequality of values of a morphism of `LawvereV`. -/
theorem val_le {a b : LawvereV} (h : a ⟶ b) : b.val ≤ a.val := leOfHom h

/-- `LawvereV` is a monoidal category with tensor `+` and unit `0`; all coherence conditions
hold because the category is thin. -/
instance monoidal : MonoidalCategory LawvereV where
  tensorObj a b := of (a.val + b.val)
  whiskerLeft a _ _ h := homOf (add_le_add_right (val_le h) a.val)
  whiskerRight h b := homOf (add_le_add_left (val_le h) b.val)
  tensorHom h₁ h₂ := homOf (add_le_add (val_le h₁) (val_le h₂))
  tensorUnit := of 0
  associator a b c := eqToIso (congrArg of (add_assoc a.val b.val c.val))
  leftUnitor a := eqToIso (congrArg of (zero_add a.val))
  rightUnitor a := eqToIso (congrArg of (add_zero a.val))
  tensorHom_def _ _ := Subsingleton.elim _ _
  id_tensorHom_id _ _ := Subsingleton.elim _ _
  tensorHom_comp_tensorHom _ _ _ _ := Subsingleton.elim _ _
  whiskerLeft_id _ _ := Subsingleton.elim _ _
  id_whiskerRight _ _ := Subsingleton.elim _ _
  associator_naturality _ _ _ := Subsingleton.elim _ _
  leftUnitor_naturality _ := Subsingleton.elim _ _
  rightUnitor_naturality _ := Subsingleton.elim _ _
  pentagon _ _ _ _ := Subsingleton.elim _ _
  triangle _ _ := Subsingleton.elim _ _

/-- The value of a tensor product in `LawvereV` is the sum of the values. -/
@[simp] theorem val_tensor (a b : LawvereV) : (a ⊗ b).val = a.val + b.val := rfl

/-- The value of the tensor unit of `LawvereV` is `0`. -/
@[simp] theorem val_unit : (𝟙_ LawvereV).val = 0 := rfl

end LawvereV

namespace Cell1

variable {E O P : Type}

/-- Realization at a statistical bound is monotone in the bound. -/
theorem holds_mono {f g : Cell1 E O} {ε δ : ℝ≥0∞} (h : Holds f g ε) (hle : ε ≤ δ) :
    Holds f g δ := by
  induction f using Quotient.inductionOn
  induction g using Quotient.inductionOn
  exact fun ζ Z => le_trans (h ζ Z) hle

/-- Realization at a statistical bound is closed: realization at every bound above `ε` is
realization at `ε`. -/
theorem holds_of_forall_lt {f g : Cell1 E O} {ε : ℝ≥0∞} (h : ∀ δ, ε < δ → Holds f g δ) :
    Holds f g ε := by
  induction f using Quotient.inductionOn
  induction g using Quotient.inductionOn
  exact fun ζ Z => le_of_forall_gt_imp_ge_of_dense fun δ hδ => h δ hδ ζ Z

/-- The realization distance from `f` to `g`: the infimum of the bounds of the 2-cells
`f ⟶ g`, the statistical bounds at which `f` realizes `g`. -/
noncomputable def dist (f g : Cell1 E O) : ℝ≥0∞ := ⨅ η : f ⟶ g, η.1

/-- The distance is at most `ε` exactly when `f` realizes `g` at bound `ε`; the infimum is
attained. -/
theorem dist_le_iff {f g : Cell1 E O} {ε : ℝ≥0∞} : dist f g ≤ ε ↔ Holds f g ε := by
  constructor
  · intro h
    refine holds_of_forall_lt fun δ hδ => ?_
    obtain ⟨η, hη⟩ := iInf_lt_iff.1 (lt_of_le_of_lt h hδ)
    exact holds_mono η.2 hη.le
  · intro h
    exact iInf_le_of_le ⟨ε, h⟩ le_rfl

/-- `f` realizes `g` at the bound `dist f g`. -/
theorem holds_dist (f g : Cell1 E O) : Holds f g (dist f g) := dist_le_iff.1 le_rfl

/-- The distance is at most `ε` exactly when there is a 2-cell `f ⟶ g` of bound `ε`. -/
theorem dist_le_iff_hom {f g : Cell1 E O} {ε : ℝ≥0∞} :
    dist f g ≤ ε ↔ ∃ η : f ⟶ g, η.1 = ε :=
  dist_le_iff.trans ⟨fun h => ⟨⟨ε, h⟩, rfl⟩, fun ⟨η, hη⟩ => hη ▸ η.2⟩

/-- The distance from a class to itself is `0`. -/
theorem dist_self (f : Cell1 E O) : dist f f = 0 :=
  nonpos_iff_eq_zero.1 (dist_le_iff.2 (holds_refl f))

/-- The triangle inequality of the realization distance. -/
theorem dist_triangle (f g h : Cell1 E O) : dist f h ≤ dist f g + dist g h :=
  dist_le_iff.2 (holds_trans (holds_dist f g) (holds_dist g h))

/-- The cascade is non-expansive for the sum distance on pairs. -/
theorem dist_seq_le (f f' : Cell1 E O) (g g' : Cell1 O P) :
    dist (f.seq g) (f'.seq g') ≤ dist f f' + dist g g' :=
  dist_le_iff.2 (holds_trans (holds_seq_left g (holds_dist f f'))
    (holds_seq_right f' (holds_dist g g')))

/-- Distance `0` is realization at bound `0`, a 2-cell of bound `0`. -/
theorem dist_eq_zero_iff {f g : Cell1 E O} : dist f g = 0 ↔ Holds f g 0 :=
  nonpos_iff_eq_zero.symm.trans dist_le_iff

/-- A hom-type of `RSysBicat` as a category enriched in `LawvereV`: the hom-object from `f` to
`g` is `dist f g`, the identities are `dist_self` and the composition is `dist_triangle`. -/
noncomputable instance enriched (E O : Type) : EnrichedCategory LawvereV (Cell1 E O) where
  Hom f g := LawvereV.of (dist f g)
  id f := LawvereV.homOf (by simp [dist_self])
  comp f g h := LawvereV.homOf (by simpa using dist_triangle f g h)
  id_comp _ _ := Subsingleton.elim _ _
  comp_id _ _ := Subsingleton.elim _ _
  assoc _ _ _ _ := Subsingleton.elim _ _

/-- The hom-object of `Cell1.enriched` is the realization distance. -/
@[simp] theorem enriched_hom_val (f g : Cell1 E O) :
    (EnrichedCategory.Hom (V := LawvereV) f g).val = dist f g := rfl

end Cell1

end CatCrypt.Crypto.UCTransparent
