/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Core.Heap
public import Iris.Instances.Classical.Instance

/-!
# Heap algebra: CatCrypt heaps inside iris-lean's Classical state model

This file connects the heap model of `CatCryptCore.Core.Heap` (a partial
finite map `Finmap (fun _ : Nat => Nat)`) with iris-lean's Classical
separation-logic state model (`Iris.Instances.Data.State Nat`, a total map
`Nat → StateResult Nat` with `unknown`/`result`/`conflict` and a partial
commutative union).

## Main definitions

* `Heap.toIState` — embedding of a CatCrypt heap as an iris Classical state
  (`result` on the domain, `unknown` off it; never `conflict`)
* `Heap.union`, `Heap.disj` — Finmap-level union and key-disjointness on heaps
* `hSep` (`⋆`, scoped) — separating conjunction on heap predicates
  `Heap → Prop`, defined by disjoint Finmap splitting

## Main results

* `Heap.toIState_injective` — the embedding is injective
* `toIState_union` / `toIState_disjoint_iff` — the embedding maps disjoint
  Finmap union to iris state union, and reflects disjointness
* `realize_of_finite` — any conflict-free iris state whose `result` positions
  lie in a finite set is the image of a heap
* `split_realize` — any disjoint iris-state splitting of a heap image is
  the image of a disjoint Finmap splitting; the single point where iris's
  function-level states are pulled back to Finmap surgery

## References

* O'Hearn, Reynolds, Yang, *Local Reasoning about Programs that Alter Data
  Structures*, CSL 2001 (the heap-splitting model of `∗`)
* Lars König et al., iris-lean `Iris.Instances.Classical`
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.IrisBridge

open CatCrypt.Core
open Iris.Instances.Data

/-- iris-lean Classical state over `Nat`-encoded values: a total map
`Nat → StateResult Nat`. -/
abbrev IState := Iris.Instances.Data.State Nat

/-- iris-lean Classical heap propositions over `IState` — a full (non-affine)
`BI` whose `∗` is disjoint state splitting. -/
abbrev HProp := Iris.Instances.Classical.HeapProp Nat

/-! ## The embedding `Heap → IState` -/

/-- Embed a CatCrypt heap (partial finite map) as an iris Classical state:
`result` with the stored encoding on the heap's domain, `unknown` off it.
The image never contains `conflict`. -/
def _root_.CatCrypt.Core.Heap.toIState (h : Heap) : IState :=
  fun i => match h.data.lookup i with
  | some n => .result n
  | none => .unknown

namespace HeapAlgebra

theorem toIState_result_iff {h : Heap} {i n : Nat} :
    h.toIState i = .result n ↔ h.data.lookup i = some n := by
  unfold Heap.toIState
  cases hl : h.data.lookup i <;> simp

theorem toIState_unknown_iff {h : Heap} {i : Nat} :
    h.toIState i = .unknown ↔ h.data.lookup i = none := by
  unfold Heap.toIState
  cases hl : h.data.lookup i <;> simp

theorem toIState_ne_conflict (h : Heap) (i : Nat) :
    h.toIState i ≠ .conflict := by
  unfold Heap.toIState
  cases hl : h.data.lookup i <;> simp

/-- The embedding is injective: an iris state determines the heap's lookup
function. -/
theorem toIState_injective : Function.Injective Heap.toIState := by
  intro h₁ h₂ heq
  apply Heap.ext_lookup
  intro i
  have hi := congrFun heq i
  cases hl₁ : h₁.data.lookup i with
  | some n =>
    have h2 : h₂.toIState i = .result n := by
      rw [← hi]; exact toIState_result_iff.mpr hl₁
    exact (toIState_result_iff.mp h2).symm
  | none =>
    have h2 : h₂.toIState i = .unknown := by
      rw [← hi]; exact toIState_unknown_iff.mpr hl₁
    exact (toIState_unknown_iff.mp h2).symm

/-- Pointwise evaluation of iris state union, as an explicit match.
Used in transfer proofs: rewrite with this, then rewrite the
scrutinees. -/
theorem istate_union_apply (σ₁ σ₂ : IState) (i : Nat) :
    (σ₁ ∪ σ₂) i = (match σ₁ i, σ₂ i with
      | .unknown , .unknown  => .unknown
      | .result x, .unknown  => .result x
      | .unknown , .result y => .result y
      | _        , _         => .conflict) := by
  show Union.union σ₁ σ₂ i = _
  simp only [Union.union]
  cases σ₁ i <;> cases σ₂ i <;> rfl

/-- Inserting one binding, seen through the embedding. -/
theorem toIState_insert_apply (h : Heap) (a n i : Nat) :
    (⟨h.data.insert a n⟩ : Heap).toIState i =
      if i = a then .result n else h.toIState i := by
  by_cases hi : i = a
  · subst hi
    rw [ite_eq_left rfl]
    exact toIState_result_iff.mpr (Finmap.lookup_insert _)
  · rw [ite_eq_right hi]
    cases hl : h.data.lookup i with
    | some m =>
      rw [toIState_result_iff.mpr hl]
      exact toIState_result_iff.mpr ((Finmap.lookup_insert_of_ne _ hi).trans hl)
    | none =>
      rw [toIState_unknown_iff.mpr hl]
      exact toIState_unknown_iff.mpr ((Finmap.lookup_insert_of_ne _ hi).trans hl)

/-! ## Union and disjointness on heaps -/

/-- Union of heaps (left-biased Finmap union; on disjoint heaps the bias is
irrelevant). -/
def _root_.CatCrypt.Core.Heap.union (h₁ h₂ : Heap) : Heap :=
  ⟨h₁.data ∪ h₂.data⟩

/-- Key-disjointness of heaps. -/
def _root_.CatCrypt.Core.Heap.disj (h₁ h₂ : Heap) : Prop :=
  h₁.data.Disjoint h₂.data

theorem disj_comm {h₁ h₂ : Heap} : h₁.disj h₂ ↔ h₂.disj h₁ :=
  Finmap.Disjoint.symm_iff _ _

/-- The embedding reflects and preserves disjointness: key-disjointness of
the Finmaps is exactly iris's pointwise `unknown`-disjointness of the
images. -/
theorem toIState_disjoint_iff {h₁ h₂ : Heap} :
    (h₁.toIState || h₂.toIState) ↔ h₁.disj h₂ := by
  constructor
  · intro hd i hi₁ hi₂
    rcases hd i with hu | hu
    · exact Finmap.lookup_eq_none.mp (toIState_unknown_iff.mp hu) hi₁
    · exact Finmap.lookup_eq_none.mp (toIState_unknown_iff.mp hu) hi₂
  · intro hd i
    by_cases hi : i ∈ h₁.data
    · exact Or.inr (toIState_unknown_iff.mpr (Finmap.lookup_eq_none.mpr (hd i hi)))
    · exact Or.inl (toIState_unknown_iff.mpr (Finmap.lookup_eq_none.mpr hi))

/-- On disjoint heaps the embedding maps Finmap union to iris state union. -/
theorem toIState_union {h₁ h₂ : Heap} (hd : h₁.disj h₂) :
    (h₁.union h₂).toIState = h₁.toIState ∪ h₂.toIState := by
  funext i
  rw [istate_union_apply]
  by_cases hi : i ∈ h₁.data
  · obtain ⟨n, hn⟩ := Finmap.mem_iff.mp hi
    have e₁ : h₁.toIState i = .result n := toIState_result_iff.mpr hn
    have e₂ : h₂.toIState i = .unknown :=
      toIState_unknown_iff.mpr (Finmap.lookup_eq_none.mpr (hd i hi))
    have eu : (h₁.union h₂).toIState i = .result n :=
      toIState_result_iff.mpr (by
        show (h₁.data ∪ h₂.data).lookup i = some n
        rw [Finmap.lookup_union_left hi]; exact hn)
    rw [eu, e₁, e₂]
  · have e₁ : h₁.toIState i = .unknown :=
      toIState_unknown_iff.mpr (Finmap.lookup_eq_none.mpr hi)
    have hu : (h₁.union h₂).data.lookup i = h₂.data.lookup i := by
      show (h₁.data ∪ h₂.data).lookup i = _
      exact Finmap.lookup_union_right hi
    rw [e₁]
    cases hl₂ : h₂.data.lookup i with
    | some m =>
      rw [toIState_result_iff.mpr (hu.trans hl₂), toIState_result_iff.mpr hl₂]
    | none =>
      rw [toIState_unknown_iff.mpr (hu.trans hl₂), toIState_unknown_iff.mpr hl₂]

/-! ## IState conveniences -/

theorem istate_union_empty (σ : IState) : σ ∪ (∅ : IState) = σ := by
  rw [Iris.Instances.Data.union_comm]
  exact (Iris.Instances.Data.empty_union).symm

theorem istate_disjoint_empty (σ : IState) : σ || (∅ : IState) :=
  (Iris.Instances.Data.disjoint_comm).mp Iris.Instances.Data.empty_disjoint

theorem empty_toIState : Heap.empty.toIState = (∅ : IState) := by
  funext i
  exact toIState_unknown_iff.mpr (by simp [Heap.empty])

/-! ## Realization: pulling iris states back to heaps -/

/-- A state is conflict-free if no position carries `conflict`. Heap images
are conflict-free; sub-states of a conflict-free disjoint union are
conflict-free. -/
def ConflictFree (σ : IState) : Prop := ∀ i, σ i ≠ .conflict

/-- The `result` positions of `σ` lie in the finite set `s`. -/
def ResultsIn (σ : IState) (s : Finset Nat) : Prop :=
  ∀ i n, σ i = .result n → i ∈ s

/-- Any conflict-free state with finitely many `result` positions is the
image of a heap. Proved by induction on the covering finite set, peeling one
position at a time into a `Finmap.insert`. -/
theorem realize_of_finite (s : Finset Nat) :
    ∀ σ : IState, ConflictFree σ → ResultsIn σ s →
      ∃ h : Heap, h.toIState = σ := by
  induction s using Finset.induction_on with
  | empty =>
    intro σ hcf hres
    refine ⟨Heap.empty, funext fun i => ?_⟩
    rw [empty_toIState]
    cases hσ : σ i with
    | unknown => rfl
    | result n => exact absurd (hres i n hσ) (Finset.notMem_empty i)
    | conflict => exact absurd hσ (hcf i)
  | insert a s' _ ih =>
    intro σ hcf hres
    -- Peel position `a` off: the rest of σ is covered by s'.
    have hcf' : ConflictFree (fun i => if i = a then .unknown else σ i) := by
      intro i
      dsimp only
      by_cases hi : i = a
      · rw [ite_eq_left hi]; exact fun h => nomatch h
      · rw [ite_eq_right hi]; exact hcf i
    have hres' : ResultsIn (fun i => if i = a then .unknown else σ i) s' := by
      intro i n hin
      dsimp only at hin
      by_cases hi : i = a
      · rw [ite_eq_left hi] at hin; exact nomatch hin
      · rw [ite_eq_right hi] at hin
        rcases Finset.mem_insert.mp (hres i n hin) with h | h
        · exact absurd h hi
        · exact h
    obtain ⟨h', hh'⟩ := ih _ hcf' hres'
    have hh'i : ∀ i, h'.toIState i = if i = a then .unknown else σ i :=
      fun i => congrFun hh' i
    cases hσa : σ a with
    | unknown =>
      refine ⟨h', funext fun i => ?_⟩
      rw [hh'i i]
      by_cases hi : i = a
      · rw [ite_eq_left hi, hi, hσa]
      · rw [ite_eq_right hi]
    | result n =>
      refine ⟨⟨h'.data.insert a n⟩, funext fun i => ?_⟩
      rw [toIState_insert_apply]
      by_cases hi : i = a
      · rw [ite_eq_left hi, hi, hσa]
      · rw [ite_eq_right hi, hh'i i, ite_eq_right hi]
    | conflict => exact absurd hσa (hcf a)

/-- **Sub-state realization.** Any disjoint iris-state splitting of a
heap image arises from a disjoint Finmap splitting of the heap. This is the
one place function-level iris states are pulled back to Finmap data; all
other transfer lemmas go forward along `toIState`. -/
theorem split_realize {hT : Heap} {σ₁ σ₂ : IState}
    (hu : hT.toIState = σ₁ ∪ σ₂) (hd : σ₁ || σ₂) :
    ∃ h₁ h₂ : Heap,
      σ₁ = h₁.toIState ∧ σ₂ = h₂.toIState ∧ h₁.disj h₂ ∧ hT = h₁.union h₂ := by
  have hcf₁ : ConflictFree σ₁ := by
    intro i hin
    apply toIState_ne_conflict hT i
    rw [congrFun hu i, istate_union_apply, hin]
  have hcf₂ : ConflictFree σ₂ := by
    intro i hin
    apply toIState_ne_conflict hT i
    rw [congrFun hu i, istate_union_apply, hin]
    cases σ₁ i <;> rfl
  -- σ₁'s entries are determined by hT (σ₂ is unknown there by disjointness).
  have hval₁ : ∀ i n, σ₁ i = .result n → hT.toIState i = .result n := by
    intro i n hin
    have h₂u : σ₂ i = .unknown := by
      rcases hd i with h | h
      · rw [hin] at h; exact nomatch h
      · exact h
    rw [congrFun hu i, istate_union_apply, hin, h₂u]
  have hval₂ : ∀ i n, σ₂ i = .result n → hT.toIState i = .result n := by
    intro i n hin
    have h₁u : σ₁ i = .unknown := by
      rcases hd i with h | h
      · exact h
      · rw [hin] at h; exact nomatch h
    rw [congrFun hu i, istate_union_apply, hin, h₁u]
  have hres₁ : ResultsIn σ₁ hT.data.keys := fun i n hin =>
    Finmap.mem_keys.mpr (Finmap.mem_iff.mpr
      ⟨n, toIState_result_iff.mp (hval₁ i n hin)⟩)
  have hres₂ : ResultsIn σ₂ hT.data.keys := fun i n hin =>
    Finmap.mem_keys.mpr (Finmap.mem_iff.mpr
      ⟨n, toIState_result_iff.mp (hval₂ i n hin)⟩)
  obtain ⟨h₁, hh₁⟩ := realize_of_finite hT.data.keys σ₁ hcf₁ hres₁
  obtain ⟨h₂, hh₂⟩ := realize_of_finite hT.data.keys σ₂ hcf₂ hres₂
  have hdisj : h₁.disj h₂ := toIState_disjoint_iff.mp (by rw [hh₁, hh₂]; exact hd)
  refine ⟨h₁, h₂, hh₁.symm, hh₂.symm, hdisj, toIState_injective ?_⟩
  rw [toIState_union hdisj, hh₁, hh₂, hu]

/-! ## Separating conjunction on heap predicates -/

/-- Separating conjunction on heap predicates: `(P ⋆ Q) h` iff `h`
splits as a disjoint Finmap union with `P` on one part and `Q` on the
other. -/
def hSep (P Q : Heap → Prop) : Heap → Prop :=
  fun h => ∃ h₁ h₂, h₁.disj h₂ ∧ h = h₁.union h₂ ∧ P h₁ ∧ Q h₂

@[inherit_doc] scoped infixr:55 " ⋆ " => hSep

theorem hSep_intro {P Q : Heap → Prop} {h₁ h₂ : Heap}
    (hd : h₁.disj h₂) (hP : P h₁) (hQ : Q h₂) :
    (P ⋆ Q) (h₁.union h₂) :=
  ⟨h₁, h₂, hd, rfl, hP, hQ⟩

end HeapAlgebra

end CatCrypt.Crypto.IrisBridge
