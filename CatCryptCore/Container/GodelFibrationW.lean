/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.DNLogic
public import CatCryptCore.Container.DNBang

/-!
# The weighted Gödel fibration and weighted soundness with expected use counts

The fibre `WPred I` over an index set `I` has the Dialectica predicates on `I` (`DPred I`) as
objects. An entailment `φ ⟶ ψ` (`DPred.WHom`) has a forward map on witnesses and a backward map
sending a counter-witness of `ψ` to a finitely supported measure with weights in `ℝ≥0` on the
counter-witnesses of `φ`, its expected demand; a witness withstanding every counter-witness in the
support withstands the counter-witness of `ψ`. Composition is the bind of finitely supported
measures, `Finsupp.linearCombination`. On total containers an entailment is a morphism with
expected demands (`EDNLens`), a lens out of the weighted exponential `bangW ℝ≥0`
(`DPred.WHom.toBangWLens`), and composition is the co-Kleisli composite of that exponential
(`DPred.WHom.toBangWLens_comp`).

Reindexing, conjunction, the quantifiers `DPred.sigma`, `DPred.pi` and the Beck–Chevalley
isomorphisms are those of `Container/GodelFibration.lean`; implication `DPred.wimp` has weighted
backward maps as witnesses, and the adjunctions `∃ ⊣ reindex ⊣ ∀` and `∧ ⊣ →` hold. The
Diller–Nahm fibration embeds by reading a finite multiset as a measure with natural weights
(`WMeasure.ofMultiset`, `DPred.toWFunctor`), and the mass of a set under the embedded demand is
the number of its elements in the multiset (`DPred.Hom.mass_toW`).

The formulas of `Container/DNLogic.lean` have a weighted interpretation `Form.wdn`, and weighted
derivations (`WDeriv`) have the rules of `Deriv`, with a realized axiom whose backward map has
total weight at most `N : ℝ≥0`: a hypothesis used `1 / p` times in expectation, as by a retry
loop with success probability `p`. The soundness theorem `WDeriv.realize` sends a weighted
derivation to an entailment of the fibre from the context to the conclusion, and its expected
demand on hypothesis `k` is at most the weighted use count (`WDeriv.mass_back_le`). For an oracle
hypothesis `∀ x, ∃ y, a (x, y)` the expected queries of the program have total weight at most the
weighted use count (`WDeriv.wqueries_total_le`), and their expected price at most that count times
the largest price of a call (`WDeriv.wqueryPrice_le`).

## Main definitions

* `WMeasure.mass`, `WMeasure.total`, `WMeasure.filterMap`, `WMeasure.ofMultiset` — finitely
  supported measures with weights in `ℝ≥0`;
* `DPred.WHom`, `WPred` and its `Category` instance; `DPred.WHom.toEDNLens`,
  `DPred.WHom.toBangWLens`;
* `DPred.wreindexFunctor`, `DPred.wimp`, `DPred.wsigmaAdj`, `DPred.wpiAdj`, `DPred.wimpAdj`,
  `DPred.wreindexSigmaIso`, `DPred.wreindexPiIso`;
* `DPred.Hom.toW`, `DPred.toWFunctor`, `DPred.impToW` — the embedding of the Diller–Nahm fibre;
* `DPred.wip`, `DPred.wmarkov` — independence of premise and Markov's principle;
* `DNLogic.Form.wdn`, `DNLogic.wctx`, `DNLogic.WDeriv`, `DNLogic.WDeriv.realize`,
  `DNLogic.WDeriv.wuseCount`.

## Main results

* `DPred.WHom.holds` — an entailment preserves the meaning;
* `DPred.WHom.toEDNLens_comp`, `DPred.WHom.toBangWLens_comp` — composition is the composite
  with expected demands, the co-Kleisli composite of `bangW ℝ≥0`;
* `DPred.Hom.mass_toW`, `DNLogic.Deriv.mass_toW_le` — the embedding preserves demand counts and
  use counts;
* `DNLogic.WDeriv.mass_back_le` — weighted soundness: the expected demand on a hypothesis is at
  most its weighted use count;
* `DNLogic.WDeriv.holds_wdn`, `DNLogic.WDeriv.wquery_sound`, `DNLogic.WDeriv.wqueries_total_le`,
  `DNLogic.WDeriv.wqueryPrice_le`.

## References

* S. Moss, T. von Glehn, *Dialectica models of type theory*, LICS 2018, §8.
* P. Hofstra, *The dialectica monad and its cousins*, in Models, Logics, and Higher-Dimensional
  Categories, CRM Proceedings 53 (2011).
* J. Diller, W. Nahm, *Eine Variante zur Dialectica-Interpretation der Heyting-Arithmetik
  endlicher Typen*, Archiv für mathematische Logik 16 (1974).
* A. Wald, *On cumulative sums of random variables*, Ann. Math. Statist. 15 (1944).
* B. L. Kaminski, J.-P. Katoen, C. Matheja, F. Olmedo, *Weakest precondition reasoning for
  expected runtimes of randomized algorithms*, J. ACM 65(5) (2018).

Search words: weighted Gödel fibration, expected demand, finitely supported measure, Dialectica,
Diller–Nahm, weighted exponential, expected use count, rewinding, retry loop, forking lemma,
soundness, quantitative soundness.
-/

set_option autoImplicit false

@[expose] public section

open scoped NNReal ENNReal

universe u

namespace CatCrypt.Container

open CategoryTheory

/-! ## Finitely supported measures -/

namespace WMeasure

variable {α β : Type*}

/-- The mass of the set `P` under the finitely supported measure `μ`. -/
noncomputable def mass (μ : α →₀ ℝ≥0) (P : α → Prop) [DecidablePred P] : ℝ≥0 :=
  Finsupp.linearCombination ℝ≥0 (fun x => if P x then 1 else 0) μ

/-- The total mass of a finitely supported measure. -/
noncomputable def total (μ : α →₀ ℝ≥0) : ℝ≥0 := mass μ fun _ => True

/-- The kernel of a partial map: a point goes to the unit mass at its image, if it has one. -/
noncomputable def optK (g : α → Option β) (y : α) : β →₀ ℝ≥0 :=
  (g y).elim 0 fun x => Finsupp.single x 1

/-- The pushforward of a finitely supported measure along a partial map. -/
noncomputable def filterMap (μ : α →₀ ℝ≥0) (g : α → Option β) : β →₀ ℝ≥0 :=
  Finsupp.linearCombination ℝ≥0 (optK g) μ

/-- A finite multiset as a finitely supported measure with natural weights. -/
noncomputable def ofMultiset (m : Multiset α) : α →₀ ℝ≥0 :=
  (m.map fun x => Finsupp.single x 1).sum

/-- A point in the support of a bind lies in the support of the kernel at a point of the support
of the measure. -/
theorem mem_support_linearCombination {κ : α → β →₀ ℝ≥0} {μ : α →₀ ℝ≥0} {x : β}
    (hx : x ∈ (Finsupp.linearCombination ℝ≥0 κ μ).support) :
    ∃ y ∈ μ.support, x ∈ (κ y).support := by
  classical
  rw [Finsupp.linearCombination_apply] at hx
  obtain ⟨y, hy, hx⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hx)
  exact ⟨y, hy, Finsupp.support_smul hx⟩

/-- The support of a bind contains the support of the kernel at each point of the support of the
measure: weights in `ℝ≥0` do not cancel. -/
theorem mem_support_linearCombination_of {κ : α → β →₀ ℝ≥0} {μ : α →₀ ℝ≥0} {x : β} {y : α}
    (hy : y ∈ μ.support) (hx : x ∈ (κ y).support) :
    x ∈ (Finsupp.linearCombination ℝ≥0 κ μ).support := by
  rw [Finsupp.mem_support_iff] at hx hy ⊢
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finsetSum_apply]
  refine ne_of_gt (lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun y => (μ y • κ y) x)
    (fun _ _ => by positivity) (Finsupp.mem_support_iff.2 hy)))
  simp [pos_iff_ne_zero, hy, hx]

/-- A point lies in the support of its unit point mass. -/
theorem mem_support_single_one (x : α) : x ∈ (Finsupp.single x (1 : ℝ≥0)).support := by
  simp

/-- The support of a sum contains the support of its left summand. -/
theorem mem_support_add_left {μ ν : α →₀ ℝ≥0} {x : α} (hx : x ∈ μ.support) :
    x ∈ (μ + ν).support := by
  simp_all [Finsupp.mem_support_iff]

/-- The support of a sum contains the support of its right summand. -/
theorem mem_support_add_right {μ ν : α →₀ ℝ≥0} {x : α} (hx : x ∈ ν.support) :
    x ∈ (μ + ν).support := by
  simp_all [Finsupp.mem_support_iff]

/-- A bind is monotone in the kernel. -/
theorem linearCombination_mono {p q : α → ℝ≥0} (h : ∀ y, p y ≤ q y) (μ : α →₀ ℝ≥0) :
    Finsupp.linearCombination ℝ≥0 p μ ≤ Finsupp.linearCombination ℝ≥0 q μ := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul]
  exact Finset.sum_le_sum fun y _ => by gcongr; exact h y

/-- The expectation of a function bounded by `B` is at most the total mass times `B`. -/
theorem linearCombination_le_total_mul {q : α → ℝ≥0} {B : ℝ≥0∞} (h : ∀ y, (q y : ℝ≥0∞) ≤ B)
    (μ : α →₀ ℝ≥0) : (Finsupp.linearCombination ℝ≥0 q μ : ℝ≥0∞) ≤ total μ * B := by
  simp only [total, mass, Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul,
    ↓reduceIte, mul_one, ENNReal.ofNNReal_finsetSum, ENNReal.coe_mul, Finset.sum_mul]
  exact Finset.sum_le_sum fun y _ => by gcongr; exact h y

/-- The mass of a sum is the sum of the masses. -/
theorem mass_add (μ ν : α →₀ ℝ≥0) (P : α → Prop) [DecidablePred P] :
    mass (μ + ν) P = mass μ P + mass ν P := by
  simp only [mass, map_add]

/-- The mass of the zero measure is zero. -/
@[simp] theorem mass_zero (P : α → Prop) [DecidablePred P] : mass (0 : α →₀ ℝ≥0) P = 0 := by
  simp [mass]

/-- The mass of a point mass. -/
theorem mass_single (x : α) (a : ℝ≥0) (P : α → Prop) [DecidablePred P] :
    mass (Finsupp.single x a) P = if P x then a else 0 := by
  simp [mass, Finsupp.linearCombination_single]

/-- The total mass of a unit point mass is one. -/
@[simp] theorem total_single_one (x : α) : total (Finsupp.single x (1 : ℝ≥0)) = 1 := by
  simp [total, mass_single]

/-- The mass of a bind is at most the total mass of the outer measure times a bound on the masses
of the kernel. -/
theorem mass_linearCombination_le {κ : α → β →₀ ℝ≥0} (μ : α →₀ ℝ≥0) (P : β → Prop)
    [DecidablePred P] {B : ℝ≥0∞} (h : ∀ y, (mass (κ y) P : ℝ≥0∞) ≤ B) :
    (mass (Finsupp.linearCombination ℝ≥0 κ μ) P : ℝ≥0∞) ≤ total μ * B := by
  rw [mass, Finsupp.linearCombination_linearCombination]
  exact linearCombination_le_total_mul h μ

/-- The support of a pushforward along a partial map consists of images of the support. -/
theorem mem_support_filterMap {g : α → Option β} {μ : α →₀ ℝ≥0} {x : β}
    (hx : x ∈ (filterMap μ g).support) : ∃ y ∈ μ.support, g y = some x := by
  classical
  obtain ⟨y, hy, hx⟩ := mem_support_linearCombination hx
  refine ⟨y, hy, ?_⟩
  unfold optK at hx
  cases h : g y with
  | none => simp [h] at hx
  | some x' =>
    rw [h, Option.elim_some, Finsupp.mem_support_iff, Finsupp.single_apply] at hx
    split_ifs at hx with hxx
    · rw [hxx]
    · exact absurd rfl hx

/-- The image of a point of the support lies in the support of the pushforward. -/
theorem mem_support_filterMap_of {g : α → Option β} {μ : α →₀ ℝ≥0} {x : β} {y : α}
    (hy : y ∈ μ.support) (hx : g y = some x) : x ∈ (filterMap μ g).support :=
  mem_support_linearCombination_of hy (by simp [optK, hx])

/-- The mass of a pushforward along a partial map is at most the mass of the preimages. -/
theorem mass_filterMap_le (g : α → Option β) (P : β → Prop) [DecidablePred P] (Q : α → Prop)
    [DecidablePred Q] (h : ∀ y x, g y = some x → P x → Q y) (μ : α →₀ ℝ≥0) :
    mass (filterMap μ g) P ≤ mass μ Q := by
  rw [mass, filterMap, Finsupp.linearCombination_linearCombination]
  refine linearCombination_mono (fun y => ?_) μ
  unfold optK
  cases hy : g y with
  | none => simp
  | some x =>
    simp only [Option.elim_some, Finsupp.linearCombination_single, smul_eq_mul, one_mul]
    by_cases hx : P x
    · simp [hx, h y x hy hx]
    · simp [hx]

/-- The measure of a multiset at a point is its multiplicity. -/
theorem ofMultiset_apply [DecidableEq α] (m : Multiset α) (x : α) :
    ofMultiset m x = m.count x := by
  induction m using Multiset.induction_on with
  | empty => simp [ofMultiset]
  | cons y m ih =>
    have hc : ofMultiset (y ::ₘ m) = Finsupp.single y 1 + ofMultiset m := by
      simp [ofMultiset]
    rw [hc, Finsupp.add_apply, ih, Finsupp.single_apply, Multiset.count_cons]
    by_cases h : y = x
    · subst h
      simp [add_comm]
    · simp [h, Ne.symm h]

/-- The support of the measure of a multiset is the set of its elements. -/
theorem mem_support_ofMultiset {m : Multiset α} {x : α} : x ∈ (ofMultiset m).support ↔ x ∈ m := by
  classical
  rw [Finsupp.mem_support_iff, ofMultiset_apply]
  simp

/-- The measure of a sum of multisets is the sum of their measures. -/
theorem ofMultiset_add (m m' : Multiset α) : ofMultiset (m + m') = ofMultiset m + ofMultiset m' :=
  by simp [ofMultiset]

/-- The measure of a singleton multiset is the unit point mass. -/
theorem ofMultiset_singleton (x : α) : ofMultiset {x} = Finsupp.single x 1 := by
  simp [ofMultiset]

/-- The measure of a bind of multisets is the bind of measures. -/
theorem ofMultiset_bind (m : Multiset α) (f : α → Multiset β) :
    ofMultiset (m.bind f) =
      Finsupp.linearCombination ℝ≥0 (fun x => ofMultiset (f x)) (ofMultiset m) := by
  induction m using Multiset.induction_on with
  | empty => simp [ofMultiset]
  | cons x m ih =>
    rw [Multiset.cons_bind, ofMultiset_add, ih, ← Multiset.singleton_add, ofMultiset_add,
      ofMultiset_singleton, map_add, Finsupp.linearCombination_single, one_smul]

/-- The mass of a set under the measure of a multiset is the number of its elements in the
multiset. -/
theorem mass_ofMultiset (m : Multiset α) (P : α → Prop) [DecidablePred P] :
    mass (ofMultiset m) P = m.countP P := by
  induction m using Multiset.induction_on with
  | empty => simp [ofMultiset]
  | cons x m ih =>
    rw [← Multiset.singleton_add, ofMultiset_add, mass_add, ofMultiset_singleton, mass_single, ih,
      Multiset.singleton_add, Multiset.countP_cons]
    split_ifs <;> simp [add_comm]

end WMeasure

open WMeasure

/-! ## Weighted entailments -/

namespace DPred

variable {I J : Type u}

/-- Weighted entailment in the fibre over `I`: a forward map on witnesses, and a backward map from
a counter-witness of the conclusion to a finitely supported measure on the counter-witnesses of
the premise, its expected demand, such that a witness withstanding every counter-witness in the
support withstands the counter-witness of the conclusion. -/
structure WHom (φ ψ : DPred I) : Type u where
  /-- The forward map on witnesses. -/
  fwd : ∀ i, φ.W i → ψ.W i
  /-- The backward map: the expected demand of a counter-witness of the conclusion. -/
  back : ∀ i w, ψ.C i (fwd i w) → (φ.C i w →₀ ℝ≥0)
  /-- Equation (9) of Moss and von Glehn on the support of the demand. -/
  sound : ∀ i w c, (∀ x ∈ (back i w c).support, φ.mat i w x) → ψ.mat i (fwd i w) c

namespace WHom

variable {φ ψ χ : DPred I}

/-- Weighted entailments with equal forward maps and backward maps equal over them are equal. -/
theorem ext {f g : φ.WHom ψ} (hA : ∀ i w, f.fwd i w = g.fwd i w)
    (hB : ∀ i w c, f.back i w c = g.back i w (hA i w ▸ c)) : f = g := by
  obtain ⟨fA, fB, fS⟩ := f
  obtain ⟨gA, gB, gS⟩ := g
  obtain rfl : fA = gA := funext fun i => funext (hA i)
  obtain rfl : fB = gB := funext fun i => funext fun w => funext (hB i w)
  rfl

/-- The identity: a counter-witness demands itself with weight one. -/
protected noncomputable def id (φ : DPred I) : φ.WHom φ where
  fwd _ w := w
  back _ _ c := Finsupp.single c 1
  sound _ _ c h := h c (mem_support_single_one c)

/-- The composite: the backward maps compose by the bind of finitely supported measures. -/
noncomputable def comp (f : φ.WHom ψ) (g : ψ.WHom χ) : φ.WHom χ where
  fwd i w := g.fwd i (f.fwd i w)
  back i w c := Finsupp.linearCombination ℝ≥0 (f.back i w) (g.back i (f.fwd i w) c)
  sound i w c h := g.sound i _ c fun y hy =>
    f.sound i w y fun x hx => h x (mem_support_linearCombination_of hy hx)

/-- A weighted entailment preserves the meaning. -/
theorem holds (f : φ.WHom ψ) (i : I) : φ.holds i → ψ.holds i := fun ⟨w, hw⟩ =>
  ⟨f.fwd i w, fun c => f.sound i w c fun x _ => hw x⟩

/-- The identity is a left unit. -/
theorem id_comp (f : φ.WHom ψ) : (WHom.id φ).comp f = f :=
  ext (fun _ _ => rfl) fun i w c => by
    change Finsupp.linearCombination ℝ≥0 (fun x => Finsupp.single x (1 : ℝ≥0)) (f.back i w c) = _
    rw [Finsupp.linearCombination_apply]
    simp only [Finsupp.smul_single_one, Finsupp.sum_single]

/-- The identity is a right unit. -/
theorem comp_id (f : φ.WHom ψ) : f.comp (WHom.id ψ) = f :=
  ext (fun _ _ => rfl) fun i w c => by
    exact (Finsupp.linearCombination_single ℝ≥0 (v := f.back i w) 1 c).trans (one_smul _ _)

/-- Composition is associative. -/
theorem comp_assoc {ω : DPred I} (f : φ.WHom ψ) (g : ψ.WHom χ) (h : χ.WHom ω) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  ext (fun _ _ => rfl) fun _ _ _ => by
    simp only [comp, Finsupp.linearCombination_linearCombination]

/-- A weighted entailment as a morphism with expected demands of the total containers. -/
def toEDNLens (f : φ.WHom ψ) : EDNLens φ.total ψ.total where
  toFunA x := ⟨x.1, f.fwd x.1 x.2⟩
  toFunB x c := f.back x.1 x.2 c

/-- A weighted entailment as a lens out of the weighted exponential `bangW ℝ≥0`. -/
def toBangWLens (f : φ.WHom ψ) : PFunctor.Lens (bangW NNReal φ.total) ψ.total :=
  f.toEDNLens.toBangWLens

/-- The identity is the identity with expected demands. -/
theorem toEDNLens_id (φ : DPred I) : (WHom.id φ).toEDNLens = EDNLens.id φ.total :=
  EDNLens.ext (fun _ => rfl) fun _ _ => rfl

/-- The composite is the composite with expected demands. -/
theorem toEDNLens_comp (f : φ.WHom ψ) (g : ψ.WHom χ) :
    (f.comp g).toEDNLens = EDNLens.comp g.toEDNLens f.toEDNLens :=
  EDNLens.ext (fun _ => rfl) fun _ _ => rfl

/-- The identity is the counit of the weighted exponential. -/
theorem toBangWLens_id (φ : DPred I) : (WHom.id φ).toBangWLens = bangWCounit NNReal φ.total := by
  rw [toBangWLens, toEDNLens_id, EDNLens.toBangWLens_id]

/-- The composite is the co-Kleisli composite of the weighted exponential. -/
theorem toBangWLens_comp (f : φ.WHom ψ) (g : ψ.WHom χ) :
    (f.comp g).toBangWLens = PFunctor.Lens.comp g.toBangWLens
      (PFunctor.Lens.comp (bangWMap f.toBangWLens) (bangWComult NNReal φ.total)) := by
  rw [toBangWLens, toEDNLens_comp, EDNLens.toBangWLens_comp]
  rfl

end WHom

end DPred

/-- The fibre over `I` of the weighted Gödel fibration: Dialectica predicates with weighted
entailments. -/
def WPred (I : Type u) : Type (u + 1) := DPred I

/-- A Dialectica predicate as an object of the weighted fibre. -/
def WPred.of {I : Type u} (φ : DPred I) : WPred I := φ

/-- The weighted fibre over `I`. -/
noncomputable instance {I : Type u} : Category (WPred I) where
  Hom φ ψ := DPred.WHom (I := I) φ ψ
  id φ := DPred.WHom.id (I := I) φ
  comp f g := DPred.WHom.comp f g
  id_comp f := DPred.WHom.id_comp f
  comp_id f := DPred.WHom.comp_id f
  assoc f g h := DPred.WHom.comp_assoc f g h

namespace DPred

variable {I J : Type u}

/-- Unfolding lemma of the `Category` instance: composition in the weighted fibre is
`WHom.comp`. -/
theorem wcomp_eq {φ ψ χ : WPred I} (f : φ ⟶ ψ) (g : ψ ⟶ χ) : f ≫ g = WHom.comp f g := rfl

/-! ## Reindexing -/

/-- Reindexing of a weighted entailment. -/
def WHom.reindex (h : J → I) {φ ψ : DPred I} (f : φ.WHom ψ) :
    (φ.reindex h).WHom (ψ.reindex h) where
  fwd j w := f.fwd (h j) w
  back j w c := f.back (h j) w c
  sound j w c hc := f.sound (h j) w c hc

/-- Reindexing as a functor between weighted fibres. -/
noncomputable def wreindexFunctor (h : J → I) : WPred I ⥤ WPred J where
  obj φ := WPred.of (DPred.reindex h φ)
  map f := WHom.reindex h f
  map_id _ := rfl
  map_comp _ _ := rfl

/-! ## Implication and the adjunctions -/

/-- Weighted implication: a witness is a weighted entailment of the fibres at `i`, a forward map
and a backward map into finitely supported measures; a counter-witness is a witness of the
premise and a counter-witness of the conclusion at its image. -/
def wimp (φ ψ : DPred I) : DPred I where
  W i := Σ f : φ.W i → ψ.W i, ∀ w, ψ.C i (f w) → (φ.C i w →₀ ℝ≥0)
  C i F := Σ w : φ.W i, ψ.C i (F.1 w)
  mat i F c := (∀ x ∈ (F.2 c.1 c.2).support, φ.mat i c.1 x) → ψ.mat i (F.1 c.1) c.2

/-- A witness of a weighted implication sends the meaning of the premise to that of the
conclusion. -/
theorem holds_wimp (φ ψ : DPred I) (i : I) (h : (wimp φ ψ).holds i) (hφ : φ.holds i) :
    ψ.holds i := by
  obtain ⟨F, hF⟩ := h
  obtain ⟨w, hw⟩ := hφ
  exact ⟨F.1 w, fun c => hF ⟨w, c⟩ fun x _ => hw x⟩

section Quantifiers

variable {K : I → Type u}

/-- `∃ ⊣ reindex` in the weighted fibration. -/
def wsigmaAdj (φ : DPred (Σ i, K i)) (ψ : DPred I) :
    (sigma φ).WHom ψ ≃ φ.WHom (ψ.reindex Sigma.fst) where
  toFun f :=
    { fwd x w := f.fwd x.1 ⟨x.2, w⟩
      back x w c := f.back x.1 ⟨x.2, w⟩ c
      sound x w c h := f.sound x.1 ⟨x.2, w⟩ c h }
  invFun g :=
    { fwd i w := g.fwd ⟨i, w.1⟩ w.2
      back i w c := g.back ⟨i, w.1⟩ w.2 c
      sound i w c h := g.sound ⟨i, w.1⟩ w.2 c h }
  left_inv _ := rfl
  right_inv _ := rfl

/-- `reindex ⊣ ∀` in the weighted fibration. -/
def wpiAdj (ψ : DPred I) (φ : DPred (Σ i, K i)) :
    ψ.WHom (pi φ) ≃ (ψ.reindex Sigma.fst).WHom φ where
  toFun f :=
    { fwd x w := f.fwd x.1 w x.2
      back x w c := f.back x.1 w ⟨x.2, c⟩
      sound x w c h := f.sound x.1 w ⟨x.2, c⟩ h }
  invFun g :=
    { fwd i w k := g.fwd ⟨i, k⟩ w
      back i w c := g.back ⟨i, c.1⟩ w c.2
      sound i w c h := g.sound ⟨i, c.1⟩ w c.2 h }
  left_inv _ := rfl
  right_inv _ := rfl

/-- Beck–Chevalley for `∃` in the weighted fibration, strictly. -/
noncomputable def wreindexSigmaIso (h : J → I) (φ : DPred (Σ i, K i)) :
    WPred.of ((sigma φ).reindex h) ≅
      WPred.of (sigma (K := fun j => K (h j)) (φ.reindex fun x => ⟨h x.1, x.2⟩)) :=
  Iso.refl _

/-- Beck–Chevalley for `∀` in the weighted fibration, strictly. -/
noncomputable def wreindexPiIso (h : J → I) (φ : DPred (Σ i, K i)) :
    WPred.of ((pi φ).reindex h) ≅
      WPred.of (pi (K := fun j => K (h j)) (φ.reindex fun x => ⟨h x.1, x.2⟩)) :=
  Iso.refl _

end Quantifiers

/-- `∧ ⊣ →` in the weighted fibration: the expected demand of an entailment out of a conjunction
is split into its left and right parts. -/
noncomputable def wimpAdj (χ φ ψ : DPred I) : (DPred.and χ φ).WHom ψ ≃ χ.WHom (wimp φ ψ) where
  toFun h :=
    { fwd i x := ⟨fun w => h.fwd i (x, w),
        fun w c => (Finsupp.sumFinsuppEquivProdFinsupp (h.back i (x, w) c)).2⟩
      back i x c := (Finsupp.sumFinsuppEquivProdFinsupp (h.back i (x, c.1) c.2)).1
      sound i x c hx hz := h.sound i (x, c.1) c.2 fun y hy => by
        cases y with
        | inl a =>
          have h' := Finsupp.mem_support_iff.1 hy
          exact hx a (Finsupp.mem_support_iff.2 h')
        | inr b =>
          have h' := Finsupp.mem_support_iff.1 hy
          exact hz b (Finsupp.mem_support_iff.2 h') }
  invFun g :=
    { fwd i w := (g.fwd i w.1).1 w.2
      back i w c := Finsupp.sumFinsuppEquivProdFinsupp.symm
        (g.back i w.1 ⟨w.2, c⟩, (g.fwd i w.1).2 w.2 c)
      sound i w c hy := g.sound i w.1 ⟨w.2, c⟩
        (fun a ha => by
          have h' := Finsupp.mem_support_iff.1 ha
          exact hy (.inl a) (Finsupp.mem_support_iff.2 h'))
        (fun b hb => by
          have h' := Finsupp.mem_support_iff.1 hb
          exact hy (.inr b) (Finsupp.mem_support_iff.2 h')) }
  left_inv h := WHom.ext (fun _ _ => rfl) fun _ _ _ =>
    Finsupp.sumFinsuppEquivProdFinsupp.symm_apply_apply _
  right_inv g := by
    refine WHom.ext (fun i x => Sigma.ext rfl (heq_of_eq (funext fun w => funext fun c =>
      congrArg Prod.snd (Equiv.apply_symm_apply _ _)))) fun i x c => ?_
    refine (congrArg Prod.fst (Equiv.apply_symm_apply _ _)).trans ?_
    change g.back i x ⟨c.1, c.2⟩ = _
    congr 1
    change c = _
    grind

/-! ## The embedding of the Diller–Nahm fibration -/

/-- A Diller–Nahm entailment as a weighted entailment: a multiset of counter-witnesses is a
measure with natural weights. -/
noncomputable def Hom.toW {φ ψ : DPred I} (f : φ.Hom ψ) : φ.WHom ψ where
  fwd := f.fwd
  back i w c := ofMultiset (f.back i w c)
  sound i w c h := f.sound i w c fun x hx => h x (mem_support_ofMultiset.2 hx)

/-- **The embedding preserves demand counts.** The mass of a set under the embedded demand is the
number of its elements in the multiset demand. -/
theorem Hom.mass_toW {φ ψ : DPred I} (f : φ.Hom ψ) (i : I) (w : φ.W i) (c : ψ.C i (f.fwd i w))
    (P : φ.C i w → Prop) [DecidablePred P] :
    mass (f.toW.back i w c) P = (f.back i w c).countP P :=
  mass_ofMultiset _ P

/-- The embedding of the Diller–Nahm fibre into the weighted fibre: the identity on objects. -/
noncomputable def toWFunctor : DPred I ⥤ WPred I where
  obj φ := WPred.of φ
  map f := Hom.toW f
  map_id _ := WHom.ext (fun _ _ => rfl) fun _ _ c => ofMultiset_singleton c
  map_comp _ _ := WHom.ext (fun _ _ => rfl) fun _ _ _ => ofMultiset_bind _ _

/-- The comparison of implications: a Diller–Nahm implication gives a weighted implication. -/
noncomputable def impToW (φ ψ : DPred I) : (imp φ ψ).WHom (wimp φ ψ) where
  fwd _ F := ⟨F.1, fun w c => ofMultiset (F.2 w c)⟩
  back _ _ c := Finsupp.single c 1
  sound _ _ c h hx := h c (mem_support_single_one _) fun x hxm =>
    hx x (mem_support_ofMultiset.2 hxm)

/-! ## Independence of premise and Markov's principle -/

section Principles

variable {K : I → Type u}

/-- Independence of premise for a universal premise, weighted form. -/
noncomputable def wip {L : I → Type u} (p : (Σ i, K i) → Prop) (ψ : DPred (Σ i, L i)) :
    (wimp (pi (ofProp p)) (sigma ψ)).WHom
      (sigma (wimp ((pi (ofProp p)).reindex Sigma.fst) ψ)) where
  fwd i F := ⟨(F.1 (unitW K i)).1, fun _ => (F.1 (unitW K i)).2, fun _ c => F.2 (unitW K i) c⟩
  back i _ c := Finsupp.single ⟨unitW K i, c.2⟩ 1
  sound i _ c h hx := h ⟨unitW K i, c.2⟩ (mem_support_single_one _) hx

/-- Markov's principle, weighted form: the candidates are the support of the demand. -/
noncomputable def wmarkov (p : (Σ i, K i) → Prop) (q : I → Prop) :
    (wimp (pi (ofProp p)) (ofProp q)).WHom
      (sigma (K := fun i => Multiset (K i)) (ofProp fun x => (∀ k ∈ x.2, p ⟨x.1, k⟩) → q x.1)) where
  fwd i F := ⟨(F.2 (unitW K i) PUnit.unit).support.val.map Sigma.fst, PUnit.unit⟩
  back i _ _ := Finsupp.single ⟨unitW K i, PUnit.unit⟩ 1
  sound i _ _ h hk := h ⟨unitW K i, PUnit.unit⟩ (mem_support_single_one _) fun _ hx =>
    hk _ (Multiset.mem_map_of_mem _ hx)

/-- The expected demand of the choice isomorphism has total weight at most one. -/
theorem total_choice_toW_back_le {L : (Σ i, K i) → Type u} (φ : DPred (Σ x : Σ i, K i, L x)) :
    ∀ i w c, WMeasure.total ((choice φ).hom.toW.back i w c) ≤ 1 := fun _ _ c =>
  (congrArg WMeasure.total (ofMultiset_singleton c)).trans_le (total_single_one c).le

/-- The expected demand of independence of premise has total weight at most one. -/
theorem total_wip_back_le {L : I → Type u} (p : (Σ i, K i) → Prop) (ψ : DPred (Σ i, L i)) :
    ∀ i w c, WMeasure.total ((wip p ψ).back i w c) ≤ 1 := fun _ _ _ =>
  (total_single_one _).le

/-- The expected demand of Markov's principle has total weight at most one. -/
theorem total_wmarkov_back_le (p : (Σ i, K i) → Prop) (q : I → Prop) :
    ∀ i w c, WMeasure.total ((wmarkov p q).back i w c) ≤ 1 := fun _ _ _ =>
  (total_single_one _).le

end Principles

end DPred

/-! ## Weighted soundness of positive many-sorted logic -/

namespace DNLogic

open DPred

/-- The weighted interpretation of a formula: implication is weighted implication. -/
def Form.wdn : {I : Type u} → Form I → DPred I
  | _, .atom p => DPred.ofProp p
  | _, .top => DPred.top
  | _, .and φ ψ => DPred.and φ.wdn ψ.wdn
  | _, .or φ ψ => DPred.or φ.wdn ψ.wdn
  | _, .imp φ ψ => DPred.wimp φ.wdn ψ.wdn
  | _, .all φ => DPred.pi φ.wdn
  | _, .ex φ => DPred.sigma φ.wdn
  | _, .sub h φ => φ.wdn.reindex h

variable {I : Type u} {n : ℕ}

/-- The weighted interpretation of a context: a witness of every hypothesis, and a
counter-witness of one hypothesis. -/
def wctx (Γ : Fin n → Form I) : DPred I where
  W i := ∀ k, (Γ k).wdn.W i
  C i w := Σ k, (Γ k).wdn.C i (w k)
  mat i w c := (Γ c.1).wdn.mat i (w c.1) c.2

/-- The meaning of a context is the meaning of each hypothesis. -/
theorem holds_wctx (Γ : Fin n → Form I) (i : I) :
    (wctx Γ).holds i ↔ ∀ k, (Γ k).wdn.holds i := by
  constructor
  · rintro ⟨w, hw⟩ k
    exact ⟨w k, fun c => hw ⟨k, c⟩⟩
  · intro h
    choose w hw using h
    exact ⟨w, fun c => hw c.1 c.2⟩

section WCons

variable {φ : Form I} {Γ : Fin n → Form I}

/-- A witness of an extended context. -/
def wconsW (i : I) (a : φ.wdn.W i) (w : (wctx Γ).W i) : (wctx (consF φ Γ)).W i := fun
  | ⟨0, _⟩ => a
  | ⟨j + 1, h⟩ => w ⟨j, Nat.lt_of_succ_lt_succ h⟩

/-- The counter-witness of the new hypothesis, if it is one. -/
def wheadC? {i : I} {a : φ.wdn.W i} {w : (wctx Γ).W i} :
    (wctx (consF φ Γ)).C i (wconsW i a w) → Option (φ.wdn.C i a)
  | ⟨⟨0, _⟩, c⟩ => some c
  | ⟨⟨_ + 1, _⟩, _⟩ => none

/-- The counter-witness of an old hypothesis, if it is one. -/
def wtailC? {i : I} {a : φ.wdn.W i} {w : (wctx Γ).W i} :
    (wctx (consF φ Γ)).C i (wconsW i a w) → Option ((wctx Γ).C i w)
  | ⟨⟨0, _⟩, _⟩ => none
  | ⟨⟨j + 1, h⟩, c⟩ => some ⟨⟨j, Nat.lt_of_succ_lt_succ h⟩, c⟩

/-- A counter-witness of an extended context is withstood when its part in the new hypothesis
and its part in the old ones are. -/
theorem wctx_cons_mat {i : I} {a : φ.wdn.W i} {w : (wctx Γ).W i}
    (y : (wctx (consF φ Γ)).C i (wconsW i a w))
    (hh : ∀ c, wheadC? y = some c → φ.wdn.mat i a c)
    (ht : ∀ c, wtailC? y = some c → (wctx Γ).mat i w c) :
    (wctx (consF φ Γ)).mat i (wconsW i a w) y := by
  obtain ⟨⟨_ | j, hj⟩, c⟩ := y
  · exact hh c rfl
  · exact ht _ rfl

/-- `wheadC?` selects the counter-witnesses at position `0`. -/
theorem wheadC?_fst {i : I} {a : φ.wdn.W i} {w : (wctx Γ).W i}
    (y : (wctx (consF φ Γ)).C i (wconsW i a w)) (c : φ.wdn.C i a) (h : wheadC? y = some c) :
    y.1 = 0 := by
  obtain ⟨⟨_ | j, hj⟩, c'⟩ := y
  · exact Fin.ext (by simp)
  · simp [wheadC?] at h

/-- `wtailC?` sends a counter-witness at position `k + 1` to one at position `k`. -/
theorem wtailC?_fst {i : I} {a : φ.wdn.W i} {w : (wctx Γ).W i}
    (y : (wctx (consF φ Γ)).C i (wconsW i a w)) (c : (wctx Γ).C i w) (h : wtailC? y = some c) :
    y.1 = c.1.succ := by
  obtain ⟨⟨_ | j, hj⟩, c'⟩ := y
  · simp [wtailC?] at h
  · simp only [wtailC?] at h
    cases h
    rfl

end WCons

/-- A counter-witness of the weighted context reindexed along `Sigma.fst`, at `⟨i, x⟩`, is a
counter-witness of the weighted context at `i`. -/
def wctxSubC {K : I → Type u} (Γ : Fin n → Form I) (i : I) (x : K i) (w : (wctx Γ).W i)
    (c : (wctx fun k => (Γ k).sub Sigma.fst).C ⟨i, x⟩ w) : (wctx Γ).C i w := c

/-- `wtailC?` followed by `wctxSubC` sends a counter-witness at position `k + 1` to one at
position `k`. -/
theorem wtailC?_map_fst {K : I → Type u} {Γ : Fin n → Form I} {φ : Form (Σ i, K i)} {i : I}
    {x : K i} {a : φ.wdn.W ⟨i, x⟩} {w : (wctx Γ).W i}
    (y : (wctx (consF φ fun k => (Γ k).sub Sigma.fst)).C ⟨i, x⟩ (wconsW _ a w))
    (z : (wctx Γ).C i w) (h : (wtailC? y).map (wctxSubC Γ i x w) = some z) :
    y.1 = z.1.succ := by
  cases ht : wtailC? y with
  | none => simp [ht] at h
  | some z' =>
    simp only [ht, Option.map_some, Option.some.injEq] at h
    subst h
    exact wtailC?_fst y z' ht

/-- Weighted natural deduction derivations of positive many-sorted logic: the rules of `Deriv`,
with a realized axiom whose expected demand has total weight at most `N : ℝ≥0`. -/
inductive WDeriv : {I : Type u} → {n : ℕ} → (Fin n → Form I) → Form I → Type (u + 1)
  /-- A hypothesis. -/
  | hyp {I : Type u} {n : ℕ} {Γ : Fin n → Form I} (k : Fin n) : WDeriv Γ (Γ k)
  /-- `⊤`-introduction. -/
  | topI {I : Type u} {n : ℕ} {Γ : Fin n → Form I} : WDeriv Γ .top
  /-- `∧`-introduction. -/
  | andI {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {φ ψ : Form I} (d : WDeriv Γ φ)
      (e : WDeriv Γ ψ) : WDeriv Γ (.and φ ψ)
  /-- `∧`-elimination, left. -/
  | andE₁ {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {φ ψ : Form I} (d : WDeriv Γ (.and φ ψ)) :
      WDeriv Γ φ
  /-- `∧`-elimination, right. -/
  | andE₂ {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {φ ψ : Form I} (d : WDeriv Γ (.and φ ψ)) :
      WDeriv Γ ψ
  /-- `→`-introduction: the premise becomes the hypothesis at position `0`. -/
  | impI {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {φ ψ : Form I} (d : WDeriv (consF φ Γ) ψ) :
      WDeriv Γ (.imp φ ψ)
  /-- `→`-elimination. -/
  | impE {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {φ ψ : Form I} (d : WDeriv Γ (.imp φ ψ))
      (e : WDeriv Γ φ) : WDeriv Γ ψ
  /-- `∀`-introduction: a derivation over the extended sort context. -/
  | allI {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {K : I → Type u} {s : ∀ i, K i → ℕ}
      {φ : Form (Σ i, K i)}
      (d : WDeriv (fun k => (Γ k).sub Sigma.fst) φ) : WDeriv Γ (.all (sz := s) φ)
  /-- `∀`-elimination at a term `t`. -/
  | allE {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {K : I → Type u} {s : ∀ i, K i → ℕ}
      {φ : Form (Σ i, K i)}
      (t : ∀ i, K i) (d : WDeriv Γ (.all (sz := s) φ)) : WDeriv Γ (φ.sub fun i => ⟨i, t i⟩)
  /-- `∃`-introduction at a term `t`. -/
  | exI {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {K : I → Type u} {s : ∀ i, K i → ℕ}
      {φ : Form (Σ i, K i)}
      (t : ∀ i, K i) (d : WDeriv Γ (φ.sub fun i => ⟨i, t i⟩)) : WDeriv Γ (.ex (sz := s) φ)
  /-- `∃`-elimination: the body becomes the hypothesis at position `0` over the extended sort
  context. -/
  | exE {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {K : I → Type u} {s : ∀ i, K i → ℕ}
      {φ : Form (Σ i, K i)}
      {ψ : Form I} (d : WDeriv Γ (.ex (sz := s) φ))
      (e : WDeriv (consF φ fun k => (Γ k).sub Sigma.fst) (ψ.sub Sigma.fst)) : WDeriv Γ ψ
  /-- The axiom of choice: `∀ k ∃ l, φ` gives `∃ f ∀ k, φ (k, f k)`. The size `sF` of the
  functions is free. -/
  | ac {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {K : I → Type u} {L : (Σ i, K i) → Type u}
      {sK : ∀ i, K i → ℕ} {sL : ∀ x, L x → ℕ} {sF : ∀ i, (∀ k : K i, L ⟨i, k⟩) → ℕ}
      {φ : Form (Σ x : Σ i, K i, L x)} (d : WDeriv Γ (.all (sz := sK) (.ex (sz := sL) φ))) :
      WDeriv Γ (.ex (K := fun i => ∀ k : K i, L ⟨i, k⟩) (sz := sF)
        (.all (K := fun p => K p.1) (sz := fun p => sK p.1)
          (φ.sub fun y => ⟨⟨y.1.1, y.2⟩, y.1.2 y.2⟩)))
  /-- Independence of a universal premise. -/
  | ip {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {K L : I → Type u} (p : (Σ i, K i) → Prop)
      {sK : ∀ i, K i → ℕ} {sL : ∀ i, L i → ℕ}
      {ψ : Form (Σ i, L i)}
      (d : WDeriv Γ (.imp (.all (sz := sK) (.atom p)) (.ex (sz := sL) ψ))) :
      WDeriv Γ (.ex (sz := sL) (.imp ((Form.all (sz := sK) (.atom p)).sub Sigma.fst) ψ))
  /-- Markov's principle, Diller–Nahm form: finitely many candidates suffice. The size `sM` of
  the finite multisets of candidates is free. -/
  | markov {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {K : I → Type u} (p : (Σ i, K i) → Prop)
      {sK : ∀ i, K i → ℕ} {sM : ∀ i, Multiset (K i) → ℕ}
      (q : I → Prop) (d : WDeriv Γ (.imp (.all (sz := sK) (.atom p)) (.atom q))) :
      WDeriv Γ (.ex (K := fun i => Multiset (K i)) (sz := sM)
        (.atom fun x => (∀ k ∈ x.2, p ⟨x.1, k⟩) → q x.1))
  /-- A realized axiom: a weighted entailment `f` of the weighted meanings whose expected demand
  on the premise has total weight at most `N`. -/
  | hom {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {φ ψ : Form I} (f : φ.wdn.WHom ψ.wdn)
      (N : ℝ≥0) (hN : ∀ i w c, total (f.back i w c) ≤ N) (d : WDeriv Γ φ) : WDeriv Γ ψ
  /-- An atom entailed by two atoms: its counter-witness demands one of each premise. -/
  | atom₂ {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {p q s : I → Prop}
      (h : ∀ i, p i → q i → s i) (d : WDeriv Γ (.atom p)) (e : WDeriv Γ (.atom q)) :
      WDeriv Γ (.atom s)

namespace WDeriv

/-- **Weighted soundness.** A weighted derivation gives a weighted entailment of the fibre from
the context to the conclusion: the forward map is the realizer, the backward map the expected
demand on the hypotheses. -/
noncomputable def realize : {I : Type u} → {n : ℕ} → {Γ : Fin n → Form I} → {φ : Form I} →
    WDeriv Γ φ → (wctx Γ).WHom φ.wdn
  | _, _, Γ, .(Γ k), .hyp k =>
    { fwd := fun _ w => w k
      back := fun _ _ c => Finsupp.single ⟨k, c⟩ 1
      sound := fun _ _ c h => h ⟨k, c⟩ (mem_support_single_one _) }
  | _, _, _, _, .topI =>
    { fwd := fun _ _ => PUnit.unit
      back := fun _ _ _ => 0
      sound := fun _ _ _ _ => trivial }
  | _, _, _, _, .andI d e =>
    { fwd := fun i w => (d.realize.fwd i w, e.realize.fwd i w)
      back := fun i w c => Sum.elim (d.realize.back i w) (e.realize.back i w) c
      sound := fun i w c h => by
        cases c with
        | inl c => exact d.realize.sound i w c h
        | inr c => exact e.realize.sound i w c h }
  | _, _, _, _, .andE₁ d =>
    { fwd := fun i w => (d.realize.fwd i w).1
      back := fun i w c => d.realize.back i w (.inl c)
      sound := fun i w c h => d.realize.sound i w (.inl c) h }
  | _, _, _, _, .andE₂ d =>
    { fwd := fun i w => (d.realize.fwd i w).2
      back := fun i w c => d.realize.back i w (.inr c)
      sound := fun i w c h => d.realize.sound i w (.inr c) h }
  | _, _, _, _, .impI d =>
    { fwd := fun i w => ⟨fun a => d.realize.fwd i (wconsW i a w),
        fun a c => filterMap (d.realize.back i (wconsW i a w) c) wheadC?⟩
      back := fun i w c => filterMap (d.realize.back i (wconsW i c.1 w) c.2) wtailC?
      sound := fun i w c hw ha => d.realize.sound i _ c.2 fun y hy =>
        wctx_cons_mat y (fun x hx => ha x (mem_support_filterMap_of hy hx))
          (fun x hx => hw x (mem_support_filterMap_of hy hx)) }
  | _, _, _, _, .impE d e =>
    { fwd := fun i w => (d.realize.fwd i w).1 (e.realize.fwd i w)
      back := fun i w c => d.realize.back i w ⟨e.realize.fwd i w, c⟩ +
        Finsupp.linearCombination ℝ≥0 (e.realize.back i w)
          ((d.realize.fwd i w).2 (e.realize.fwd i w) c)
      sound := fun i w c h => d.realize.sound i w ⟨e.realize.fwd i w, c⟩
        (fun x hx => h x (mem_support_add_left hx))
        (fun x hx => e.realize.sound i w x fun y hy =>
          h y (mem_support_add_right (mem_support_linearCombination_of hx hy))) }
  | _, _, _, _, .allI d =>
    { fwd := fun i w x => d.realize.fwd ⟨i, x⟩ w
      back := fun i w c => d.realize.back ⟨i, c.1⟩ w c.2
      sound := fun i w c h => d.realize.sound ⟨i, c.1⟩ w c.2 h }
  | _, _, _, _, .allE t d =>
    { fwd := fun i w => d.realize.fwd i w (t i)
      back := fun i w c => d.realize.back i w ⟨t i, c⟩
      sound := fun i w c h => d.realize.sound i w ⟨t i, c⟩ h }
  | _, _, _, _, .exI t d =>
    { fwd := fun i w => ⟨t i, d.realize.fwd i w⟩
      back := fun i w c => d.realize.back i w c
      sound := fun i w c h => d.realize.sound i w c h }
  | _, _, _, _, .exE (Γ := Γ) d e =>
    { fwd := fun i w => e.realize.fwd ⟨i, (d.realize.fwd i w).1⟩
        (wconsW _ (d.realize.fwd i w).2 w)
      back := fun i w c =>
        filterMap
            (e.realize.back ⟨i, (d.realize.fwd i w).1⟩ (wconsW _ (d.realize.fwd i w).2 w) c)
            (fun y => (wtailC? y).map (wctxSubC Γ i _ w)) +
          Finsupp.linearCombination ℝ≥0 (d.realize.back i w)
            (filterMap
              (e.realize.back ⟨i, (d.realize.fwd i w).1⟩ (wconsW _ (d.realize.fwd i w).2 w) c)
              wheadC?)
      sound := fun i w c h => e.realize.sound ⟨i, (d.realize.fwd i w).1⟩
        (wconsW _ (d.realize.fwd i w).2 w) c fun y hy =>
        wctx_cons_mat y
          (fun a ha => d.realize.sound i w a fun z hz => h z (mem_support_add_right
            (mem_support_linearCombination_of (mem_support_filterMap_of hy ha) hz)))
          (fun x hx => h x (mem_support_add_left
            (mem_support_filterMap_of hy (by rw [hx]; rfl)))) }
  | _, _, _, _, .ac (φ := φ) d => WHom.comp d.realize (DPred.choice φ.wdn).hom.toW
  | _, _, _, _, .ip p (ψ := ψ) d => WHom.comp d.realize (DPred.wip p ψ.wdn)
  | _, _, _, _, .markov p q d => WHom.comp d.realize (DPred.wmarkov p q)
  | _, _, _, _, .hom f _ _ d => WHom.comp d.realize f
  | _, _, _, _, .atom₂ h d e =>
    { fwd := fun _ _ => PUnit.unit
      back := fun i w _ => d.realize.back i w PUnit.unit + e.realize.back i w PUnit.unit
      sound := fun i w _ hw => h i
        (d.realize.sound i w PUnit.unit fun x hx => hw x (mem_support_add_left hx))
        (e.realize.sound i w PUnit.unit fun x hx => hw x (mem_support_add_right hx)) }

/-- The weighted use counts of a derivation: the expected uses of each hypothesis (one at a leaf,
the maximum at `∧`-introduction, `N` times the uses of its premise at a realized axiom, and at a
cut the product of the uses of the cut formula with the uses in the derivation of the cut
formula), and the expected uses of the premise by a derivation of an implication. -/
noncomputable def wuses : {I : Type u} → {n : ℕ} → {Γ : Fin n → Form I} → {φ : Form I} →
    WDeriv Γ φ → (Fin n → ℝ≥0∞) × ℝ≥0∞
  | _, _, Γ, .(Γ k), .hyp k => (fun j => if j = k then 1 else 0, ⊤)
  | _, _, _, _, .topI => (fun _ => 0, ⊤)
  | _, _, _, _, .andI d e => (fun j => max (d.wuses.1 j) (e.wuses.1 j), ⊤)
  | _, _, _, _, .andE₁ d => (d.wuses.1, ⊤)
  | _, _, _, _, .andE₂ d => (d.wuses.1, ⊤)
  | _, _, _, _, .impI d => (fun j => d.wuses.1 j.succ, d.wuses.1 0)
  | _, _, _, _, .impE d e => (fun j => d.wuses.1 j + d.wuses.2 * e.wuses.1 j, ⊤)
  | _, _, _, _, .allI d => (d.wuses.1, ⊤)
  | _, _, _, _, .allE _ d => (d.wuses.1, ⊤)
  | _, _, _, _, .exI _ d => (d.wuses.1, ⊤)
  | _, _, _, _, .exE d e => (fun j => e.wuses.1 j.succ + e.wuses.1 0 * d.wuses.1 j, ⊤)
  | _, _, _, _, .ac d => (d.wuses.1, ⊤)
  | _, _, _, _, .ip _ d => (d.wuses.1, ⊤)
  | _, _, _, _, .markov _ _ d => (d.wuses.1, ⊤)
  | _, _, _, _, .hom _ N _ d => (fun j => (N : ℝ≥0∞) * d.wuses.1 j, ⊤)
  | _, _, _, _, .atom₂ _ d e => (fun j => d.wuses.1 j + e.wuses.1 j, ⊤)

/-- The expected number of uses of hypothesis `k` in a weighted derivation. -/
noncomputable def wuseCount {Γ : Fin n → Form I} {φ : Form I} (d : WDeriv Γ φ) (k : Fin n) : ℝ≥0∞ :=
  d.wuses.1 k

/-- The expected number of uses of the premise by a weighted derivation of an implication. -/
noncomputable def wargUses {Γ : Fin n → Form I} {φ : Form I} (d : WDeriv Γ φ) : ℝ≥0∞ := d.wuses.2

end WDeriv

/-- For a weighted entailment into an implication, the bound `b` on the total weight of the
demand on the premise that its witnesses make; true for other conclusions. -/
def WArgBound {Γ : Fin n → Form I} : {χ : Form I} → (wctx Γ).WHom χ.wdn → ℝ≥0∞ → Prop
  | .imp _ _, f, b => ∀ i w a c, (total ((f.fwd i w).2 a c) : ℝ≥0∞) ≤ b
  | _, _, _ => True

/-- Every weighted entailment satisfies the bound `⊤`. -/
theorem wargBound_top {Γ : Fin n → Form I} {χ : Form I} (f : (wctx Γ).WHom χ.wdn) :
    WArgBound f ⊤ := by
  cases χ <;> simp [WArgBound]

namespace WDeriv

/-- A composite whose second factor demands total weight at most `N` demands at most `N` times
the bound on the first factor. -/
theorem mass_comp_le {Γ : Fin n → Form I} {χ : DPred I} {ψ : DPred I}
    (f : (wctx Γ).WHom χ) (g : χ.WHom ψ) (k : Fin n) (B : ℝ≥0∞) (N : ℝ≥0)
    (hf : ∀ i w c, (mass (f.back i w c) (fun x => x.1 = k) : ℝ≥0∞) ≤ B)
    (hg : ∀ i w c, total (g.back i w c) ≤ N) (i : I) (w : (wctx Γ).W i)
    (c : ψ.C i ((f.comp g).fwd i w)) :
    (mass ((f.comp g).back i w c) (fun x => x.1 = k) : ℝ≥0∞) ≤ N * B :=
  (mass_linearCombination_le _ _ (hf i w)).trans
    (mul_le_mul_left (ENNReal.coe_le_coe.2 (hg i _ c)) B)

/-- The demand bounds of a weighted derivation: on each hypothesis by its weighted use count,
and on the premise of an implication by `wargUses`. -/
theorem bounds {Γ : Fin n → Form I} {φ : Form I} (d : WDeriv Γ φ) :
    (∀ k i w c, (mass (d.realize.back i w c) (fun x => x.1 = k) : ℝ≥0∞) ≤ d.wuseCount k) ∧
      WArgBound d.realize d.wargUses := by
  induction d with
  | hyp j =>
    refine ⟨fun k i w c => ?_, wargBound_top _⟩
    change ((mass (Finsupp.single (⟨j, c⟩ : (wctx _).C i w) 1) fun x => x.1 = k : ℝ≥0) : ℝ≥0∞) ≤
      if k = j then 1 else 0
    rw [mass_single]
    split_ifs <;> simp_all
  | topI => exact ⟨fun k i w c => by simp [realize], wargBound_top _⟩
  | andI d e ihd ihe =>
    refine ⟨fun k i w c => ?_, wargBound_top _⟩
    cases c with
    | inl c => exact (ihd.1 k i w c).trans (le_max_left _ _)
    | inr c => exact (ihe.1 k i w c).trans (le_max_right _ _)
  | andE₁ d ih => exact ⟨fun k i w c => ih.1 k i w _, wargBound_top _⟩
  | andE₂ d ih => exact ⟨fun k i w c => ih.1 k i w _, wargBound_top _⟩
  | impI d ih =>
    refine ⟨fun k i w c => ?_, fun i w a c => ?_⟩
    · change ((mass (filterMap (d.realize.back i (wconsW i c.1 w) c.2) wtailC?)
        fun x => x.1 = k : ℝ≥0) : ℝ≥0∞) ≤ d.wuseCount k.succ
      exact le_trans (ENNReal.coe_le_coe.2 (mass_filterMap_le wtailC? (fun x => x.1 = k)
        (fun y => y.1 = k.succ) (fun y x hx hp => by rw [wtailC?_fst y x hx, hp]) _))
        (ih.1 k.succ i _ c.2)
    · change ((total (filterMap (d.realize.back i (wconsW i a w) c) wheadC?) : ℝ≥0) : ℝ≥0∞) ≤
        d.wuseCount 0
      exact le_trans (ENNReal.coe_le_coe.2 (mass_filterMap_le wheadC? (fun _ => True)
        (fun y => y.1 = 0) (fun y x hx _ => wheadC?_fst y x hx) _)) (ih.1 0 i _ c)
  | impE d e ihd ihe =>
    refine ⟨fun k i w c => ?_, wargBound_top _⟩
    change ((mass (d.realize.back i w ⟨e.realize.fwd i w, c⟩ +
        Finsupp.linearCombination ℝ≥0 (e.realize.back i w)
          ((d.realize.fwd i w).2 (e.realize.fwd i w) c)) fun x => x.1 = k : ℝ≥0) : ℝ≥0∞) ≤
      d.wuseCount k + d.wargUses * e.wuseCount k
    rw [mass_add, ENNReal.coe_add]
    exact add_le_add (ihd.1 k i w _) ((mass_linearCombination_le _ _ fun x => ihe.1 k i w x).trans
      (mul_le_mul_left (ihd.2 i w _ c) _))
  | allI d ih => exact ⟨fun k i w c => ih.1 k ⟨i, c.1⟩ w c.2, wargBound_top _⟩
  | allE t d ih => exact ⟨fun k i w c => ih.1 k i w _, wargBound_top _⟩
  | exI t d ih => exact ⟨fun k i w c => ih.1 k i w _, wargBound_top _⟩
  | exE d e ihd ihe =>
    refine ⟨fun k i w c => ?_, wargBound_top _⟩
    change ((mass (filterMap
        (e.realize.back ⟨i, (d.realize.fwd i w).1⟩ (wconsW _ (d.realize.fwd i w).2 w) c)
        (fun y => (wtailC? y).map (wctxSubC _ i _ w)) +
      Finsupp.linearCombination ℝ≥0 (d.realize.back i w) (filterMap
        (e.realize.back ⟨i, (d.realize.fwd i w).1⟩ (wconsW _ (d.realize.fwd i w).2 w) c)
        wheadC?)) fun x => x.1 = k : ℝ≥0) : ℝ≥0∞) ≤
      e.wuseCount k.succ + e.wuseCount 0 * d.wuseCount k
    rw [mass_add, ENNReal.coe_add]
    refine add_le_add ?_ ?_
    · have he := ihe.1 k.succ ⟨i, (d.realize.fwd i w).1⟩ (wconsW _ (d.realize.fwd i w).2 w) c
      refine le_trans ?_ he
      refine ENNReal.coe_le_coe.2 (mass_filterMap_le _ _ _ ?_ _)
      intro y z hz hp
      rw [wtailC?_map_fst y z hz, hp]
    refine (mass_linearCombination_le _ _ fun x => ihd.1 k i w x).trans (mul_le_mul_left ?_ _)
    exact le_trans (ENNReal.coe_le_coe.2 (mass_filterMap_le wheadC? (fun _ => True)
      (fun y => y.1 = 0) (fun y x hx _ => wheadC?_fst y x hx) _))
      (ihe.1 0 ⟨i, (d.realize.fwd i w).1⟩ (wconsW _ (d.realize.fwd i w).2 w) c)
  | ac d ih =>
    refine ⟨fun k i w c => ?_, wargBound_top _⟩
    exact (mass_comp_le _ _ k _ 1 (ih.1 k) (fun i w c => total_choice_toW_back_le _ i w c) i w
      c).trans (le_of_eq (one_mul _))
  | ip p d ih =>
    refine ⟨fun k i w c => ?_, wargBound_top _⟩
    exact (mass_comp_le _ _ k _ 1 (ih.1 k) (fun i w c => total_wip_back_le p _ i w c) i w
      c).trans (le_of_eq (one_mul _))
  | markov p q d ih =>
    refine ⟨fun k i w c => ?_, wargBound_top _⟩
    exact (mass_comp_le _ _ k _ 1 (ih.1 k) (fun i w c => total_wmarkov_back_le p q i w c) i w
      c).trans (le_of_eq (one_mul _))
  | hom f N hN d ih =>
    exact ⟨fun k i w c => mass_comp_le _ _ k _ N (ih.1 k) hN i w c, wargBound_top _⟩
  | atom₂ h d e ihd ihe =>
    refine ⟨fun k i w c => ?_, wargBound_top _⟩
    change ((mass (d.realize.back i w PUnit.unit + e.realize.back i w PUnit.unit)
      fun x => x.1 = k : ℝ≥0) : ℝ≥0∞) ≤ d.wuseCount k + e.wuseCount k
    rw [mass_add, ENNReal.coe_add]
    exact add_le_add (ihd.1 k i w _) (ihe.1 k i w _)

/-- **Weighted quantitative soundness.** The realizer of a weighted derivation demands
hypothesis `k` at most `wuseCount d k` times in expectation. -/
theorem mass_back_le {Γ : Fin n → Form I} {φ : Form I} (d : WDeriv Γ φ) (k : Fin n) (i : I)
    (w : (wctx Γ).W i) (c : φ.wdn.C i (d.realize.fwd i w)) :
    (mass (d.realize.back i w c) (fun x => x.1 = k) : ℝ≥0∞) ≤ d.wuseCount k :=
  d.bounds.1 k i w c

/-- **Weighted soundness for the Dialectica meaning.** -/
theorem holds_wdn {Γ : Fin n → Form I} {φ : Form I} (d : WDeriv Γ φ) (i : I)
    (h : ∀ k, (Γ k).wdn.holds i) : φ.wdn.holds i :=
  d.realize.holds i ((holds_wctx Γ i).2 h)

/-- Unfolding equation of `wuseCount` at a hypothesis: it is used once. -/
@[simp] theorem wuseCount_hyp {Γ : Fin n → Form I} (k j : Fin n) :
    (hyp (Γ := Γ) k).wuseCount j = if j = k then 1 else 0 := rfl

/-- Unfolding equation of `wuseCount` at a realized axiom: the expected uses of its premise times
its total weight bound. -/
@[simp] theorem wuseCount_hom {Γ : Fin n → Form I} {φ ψ : Form I} (f : φ.wdn.WHom ψ.wdn)
    (N : ℝ≥0) (hN : ∀ i w c, total (f.back i w c) ≤ N) (d : WDeriv Γ φ) (k : Fin n) :
    (hom f N hN d).wuseCount k = N * d.wuseCount k := rfl

/-! ## Expected queries to an oracle hypothesis -/

section Oracle

variable {X : I → Type u} {Y : (Σ i, X i) → Type u} {a : (Σ x : Σ i, X i, Y x) → Prop}
  {X' : I → Type u} {Z : (Σ i, X' i) → Type u} {r : (Σ x : Σ i, X' i, Z x) → Prop}

/-- The witness of the hypothesis `∀ x, ∃ y, a (x, y)` given by an oracle `g`. -/
def woracleW (a : (Σ x : Σ i, X i, Y x) → Prop) (g : ∀ i (x : X i), Y ⟨i, x⟩) (i : I) :
    (wctx fun _ : Fin 1 => Deriv.allEx 0 0 a).W i :=
  fun _ x => ⟨g i x, PUnit.unit⟩

/-- The program of a weighted derivation of `∀ x', ∃ z, r (x', z)` from `∀ x, ∃ y, a (x, y)`. -/
noncomputable def wprogram (d : WDeriv (fun _ : Fin 1 => Deriv.allEx 0 0 a) (Deriv.allEx 0 0 r))
    (g : ∀ i (x : X i), Y ⟨i, x⟩) (i : I) (x' : X' i) : Z ⟨i, x'⟩ :=
  (d.realize.fwd i (woracleW a g i) x').1

/-- The expected queries of the program at `x'`: a finitely supported measure on the arguments of
the oracle. -/
noncomputable def wqueries (d : WDeriv (fun _ : Fin 1 => Deriv.allEx 0 0 a) (Deriv.allEx 0 0 r))
    (g : ∀ i (x : X i), Y ⟨i, x⟩) (i : I) (x' : X' i) : X i →₀ ℝ≥0 :=
  filterMap (d.realize.back i (woracleW a g i) ⟨x', PUnit.unit⟩) fun c => some c.2.1

/-- **Expected query bound.** The expected number of oracle queries of the program is at most
`wuseCount d 0`. -/
theorem wqueries_total_le (d : WDeriv (fun _ : Fin 1 => Deriv.allEx 0 0 a) (Deriv.allEx 0 0 r))
    (g : ∀ i (x : X i), Y ⟨i, x⟩) (i : I) (x' : X' i) :
    (total (d.wqueries g i x') : ℝ≥0∞) ≤ d.wuseCount 0 :=
  by
  have h := d.mass_back_le 0 i (woracleW a g i) ⟨x', PUnit.unit⟩
  refine le_trans ?_ h
  exact ENNReal.coe_le_coe.2 (mass_filterMap_le _ _ _ (fun y _ _ _ => Subsingleton.elim _ _) _)

/-- **Correctness from the queries.** The answer of the program at `x'` satisfies `r` whenever
the oracle satisfies `a` on the support of the expected queries. -/
theorem wquery_sound (d : WDeriv (fun _ : Fin 1 => Deriv.allEx 0 0 a) (Deriv.allEx 0 0 r))
    (g : ∀ i (x : X i), Y ⟨i, x⟩) (i : I) (x' : X' i)
    (h : ∀ x ∈ (d.wqueries g i x').support, a ⟨⟨i, x⟩, g i x⟩) :
    r ⟨⟨i, x'⟩, d.wprogram g i x'⟩ :=
  d.realize.sound i (woracleW a g i) ⟨x', PUnit.unit⟩ fun y hy =>
    h y.2.1 (mem_support_filterMap_of hy rfl)

/-- The expected price of the queries of the program at `x'`, under a price `t` of an oracle
call. -/
noncomputable def wqueryPrice (d : WDeriv (fun _ : Fin 1 => Deriv.allEx 0 0 a) (Deriv.allEx 0 0 r))
    (g : ∀ i (x : X i), Y ⟨i, x⟩) (t : ∀ i, X i → ℝ≥0) (i : I) (x' : X' i) : ℝ≥0 :=
  Finsupp.linearCombination ℝ≥0 (t i) (d.wqueries g i x')

/-- **Expected price bound.** When each oracle call costs at most `T`, the queries of the program
cost at most `wuseCount d 0 * T` in expectation. -/
theorem wqueryPrice_le (d : WDeriv (fun _ : Fin 1 => Deriv.allEx 0 0 a) (Deriv.allEx 0 0 r))
    (g : ∀ i (x : X i), Y ⟨i, x⟩) (t : ∀ i, X i → ℝ≥0) (T : ℝ≥0) (ht : ∀ i x, t i x ≤ T)
    (i : I) (x' : X' i) : (d.wqueryPrice g t i x' : ℝ≥0∞) ≤ d.wuseCount 0 * T :=
  (linearCombination_le_total_mul (fun x => ENNReal.coe_le_coe.2 (ht i x)) _).trans
    (mul_le_mul_left (d.wqueries_total_le g i x') _)

end Oracle

end WDeriv

/-! ## Use counts of the embedded Diller–Nahm realizer -/

/-- **The embedding preserves use counts.** The realizer of a Diller–Nahm derivation, read as a
weighted entailment, demands hypothesis `k` at most `useCount d k` times in expectation. -/
theorem Deriv.mass_toW_le {Γ : Fin n → Form I} {φ : Form I} (d : Deriv Γ φ) (k : Fin n) (i : I)
    (w : (ctx Γ).W i) (c : φ.dn.C i (d.realize.fwd i w)) :
    (mass (d.realize.toW.back i w c) (fun x => x.1 = k) : ℝ≥0∞) ≤ d.useCount k := by
  rw [Hom.mass_toW]
  have h := d.card_back_le k i w c
  calc (((((d.realize.back i w c).countP fun x => x.1 = k : ℕ) : ℝ≥0)) : ℝ≥0∞)
      = ((((d.realize.back i w c).countP fun x => x.1 = k : ℕ) : ℕ∞) : ℝ≥0∞) := by simp
    _ ≤ d.useCount k := ENat.toENNReal_le.2 h

end DNLogic

end CatCrypt.Container
