/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.XDijkstra.XPostShape


@[expose] public section
set_option autoImplicit false

/-!
# `XHeapSoundness`: a separation-logic heap model and a machine-monad soundness instance

Two ingredients that make the extended-PostShape Dijkstra framework
(`XPostShape.lean`) sound for a concrete machine:

1. **A bunched-implication carrier `XBI (HProp V)`** over a concrete heap
   `Heap V := Nat → Option V`. Separating conjunction `hsep` is disjoint-heap
   splitting — `∃ h₁ h₂, h = h₁ ⊎ h₂ ∧ h₁ ⟂ h₂ ∧ P h₁ ∧ Q h₂` — so `∗` is
   sub-structural: `pointsTo ℓ v ∗ pointsTo ℓ v` is **unsatisfiable**
   (`pointsTo_sep_self_empty`), distinguishing `∗` from `∧`. Over this carrier
   `xframe` is the frame rule; `heap_framed_triple` frames a points-to on a
   disjoint cell (the extended-framework analogue of
   `JStateSepLogic.sbb_framed_triple`).

2. **A soundness `XWP` instance for the total state monad `StateM σ`.** The
   observation `stateWP` reads a program by its operational run: its weakest
   precondition at post `Q` is `fun s => Q (x.run s).1 (x.run s).2`.
   `stateWP_triple_iff` shows the extended `XTriple` over `StateM` is the
   ordinary state Hoare triple `∀ s, P s → Q (run s)`.
-/

namespace CatCrypt.XDijkstra

/-! ## 1. A soundness `XWP` instance for `StateM σ` (carrier `Ω := Prop`)

`StateM σ = StateT σ Id` is total and Mathlib-only. Its natural `XPostShape` is
`.arg σ .pure` (one state layer over the pure base), and at carrier `Prop` an
assertion `XAssertion (.arg σ .pure) Prop` is a state predicate `σ → Prop`. The
observation reads a program by its run. -/

/-- The `XPostShape` of `StateM σ`: a single state layer over the pure base. -/
abbrev psState (σ : Type) : XPostShape.{0} := .arg σ .pure

/-- **The `StateM` weakest-precondition observation.** A program is read by its
operational run: the WP at post `Q` requires the success barrel `Q.1` to hold of
the returned value and final state `x.run s`. Grade is trivial (the shape has no
grade layer). Monotonicity is pointwise in the state. -/
def stateWP {σ α : Type} (x : StateM σ α) : XPredTrans (psState σ) Prop α where
  apply Q := fun s => Q.1 (x.run s).1 (x.run s).2
  grade := PUnit.unit
  mono h := fun s => h.1 (x.run s).1 (x.run s).2

@[simp] theorem stateWP_apply {σ α : Type} (x : StateM σ α)
    (Q : XPostCond α (psState σ) Prop) :
    (stateWP x).apply Q = fun s => Q.1 (x.run s).1 (x.run s).2 := rfl

/-- `StateM σ` observed as an extended predicate transformer over `Prop`. -/
instance instXWPStateM {σ : Type} : XWP (StateM σ) (psState σ) Prop where
  xwp := stateWP

/-- **Soundness characterization.** The extended `XTriple` over `StateM σ` *is* the
ordinary state Hoare triple: `⦃P⦄ x ⦃Q⦄` in the framework holds iff for every
initial state satisfying `P`, the returned value and final state of the run satisfy
`Q`. Definitional — the observation was built to match the run. -/
theorem stateWP_triple_iff {σ α : Type} (P : σ → Prop) (Qf : α → σ → Prop)
    (x : StateM σ α) :
    XTriple (m := StateM σ) (ps := psState σ) (Ω := Prop) P x (Qf, PUnit.unit)
      ↔ ∀ s, P s → Qf (x.run s).1 (x.run s).2 :=
  Iff.rfl

/-! ### A worked triple over the machine monad -/

/-- A concrete `StateM ℕ` program: increment the state. -/
def incr : StateM Nat Unit := modify (· + 1)

/-- **A worked `StateM` triple**, discharged through the soundness characterization:
`⦃s = n⦄ incr ⦃_ s ↦ s = n + 1⦄`. The framework's Hoare triple over a runnable
machine monad, proved by evaluating the operational run. -/
theorem incr_triple (n : Nat) :
    XTriple (m := StateM Nat) (ps := psState Nat) (Ω := Prop)
      (fun s => s = n) incr (fun _ s => s = n + 1, PUnit.unit) :=
  (stateWP_triple_iff _ _ _).mpr (by intro s hs; subst hs; rfl)

/-! ## 2. A separation-logic carrier `XBI (HProp V)`

A concrete heap `Heap V := Nat → Option V`; a heap predicate `HProp V := Heap V →
Prop`. Entailment is pointwise implication (its own `Preorder`, so the framework's
`≤` on assertions is heap-entailment). `hsep` is disjoint splitting — the
separating `∗`, not `∧`. -/

/-- A concrete heap: a partial map from cell indices to values. -/
def Heap (V : Type) : Type := Nat → Option V

/-- A heap predicate — the separation-logic assertion carrier. -/
def HProp (V : Type) : Type := Heap V → Prop

/-- Heap entailment as a preorder: pointwise implication. This is the `≤` the
extended framework reads as assertion entailment on this carrier. -/
instance instPreorderHProp (V : Type) : Preorder (HProp V) where
  le P Q := ∀ h, P h → Q h
  le_refl _ _ hp := hp
  le_trans _ _ _ hpq hqr h hp := hqr h (hpq h hp)

/-- The empty heap (undefined everywhere). -/
def emptyHeap (V : Type) : Heap V := fun _ => none

/-- Union of two heaps, left-biased (well-defined on disjoint heaps). -/
def hunion {V : Type} (h₁ h₂ : Heap V) : Heap V :=
  fun ℓ => match h₁ ℓ with | some v => some v | none => h₂ ℓ

/-- Two heaps are disjoint when no cell is defined in both. -/
def hDisjoint {V : Type} (h₁ h₂ : Heap V) : Prop :=
  ∀ ℓ, h₁ ℓ = none ∨ h₂ ℓ = none

/-- The singleton heap `ℓ ↦ v`. -/
def single {V : Type} (ℓ : Nat) (v : V) : Heap V :=
  fun k => if k = ℓ then some v else none

/-- **Separating conjunction.** `P ∗ Q` holds of `h` when `h` splits into
*disjoint* sub-heaps `h₁ ⊎ h₂` with `P h₁` and `Q h₂` — heap separation, not `∧`. -/
def hsep {V : Type} (P Q : HProp V) : HProp V :=
  fun h => ∃ h₁ h₂ : Heap V, h = hunion h₁ h₂ ∧ hDisjoint h₁ h₂ ∧ P h₁ ∧ Q h₂

/-- The separation-logic unit: the empty heap holds. -/
def hemp (V : Type) : HProp V := fun h => h = emptyHeap V

/-- The points-to assertion `ℓ ↦ v`: the heap is exactly the singleton `ℓ ↦ v`. -/
def pointsTo {V : Type} (ℓ : Nat) (v : V) : HProp V := fun h => h = single ℓ v

/-- **The bunched-implication instance.** `∗ := hsep` (disjoint splitting),
`emp := hemp`, and `∗` is monotone in its left argument — the property `xframe`
needs. Framing over this carrier is the frame rule. -/
instance instXBIHProp (V : Type) : XBI (HProp V) where
  sep := hsep
  emp := hemp V
  sep_mono_left := fun {_ _} _ hab h hh => by
    obtain ⟨h₁, h₂, hu, hd, ha, hr⟩ := hh
    exact ⟨h₁, h₂, hu, hd, hab h₁ ha, hr⟩

/-! ### `∗` is sub-structural — witnesses that it is not `∧` -/

/-- **Separation is realizable.** For distinct cells `ℓ₁ ≠ ℓ₂`, the
two-cell heap `single ℓ₁ v₁ ⊎ single ℓ₂ v₂` satisfies `ℓ₁ ↦ v₁ ∗ ℓ₂ ↦ v₂`. A
concrete inhabitant of `∗`. -/
theorem pointsTo_sep_disjoint {V : Type} (ℓ₁ ℓ₂ : Nat) (v₁ v₂ : V)
    (hne : ℓ₁ ≠ ℓ₂) :
    hsep (pointsTo ℓ₁ v₁) (pointsTo ℓ₂ v₂) (hunion (single ℓ₁ v₁) (single ℓ₂ v₂)) :=
  ⟨single ℓ₁ v₁, single ℓ₂ v₂, rfl,
    fun ℓ => by
      simp only [single]
      by_cases hc : ℓ = ℓ₁
      · subst hc; exact Or.inr (if_neg hne)
      · exact Or.inl (if_neg hc),
    rfl, rfl⟩

/-- **`∗` is non-idempotent, distinguishing it from `∧`.**
`pointsTo ℓ v ∗ pointsTo ℓ v` is *unsatisfiable*: no heap splits into two disjoint
copies of the same non-empty cell. Over `∧` this would reduce to `pointsTo ℓ v`;
the failure witnesses that this carrier is separating. -/
theorem pointsTo_sep_self_empty {V : Type} (ℓ : Nat) (v : V) (h : Heap V) :
    ¬ hsep (pointsTo ℓ v) (pointsTo ℓ v) h := by
  rintro ⟨h₁, h₂, -, hd, rfl, rfl⟩
  rcases hd ℓ with h' | h' <;> · simp only [single, if_true] at h'; nomatch h'

/-! ## 3. The frame rule on the concrete heap — a framed points-to triple

The extended-framework frame rule `xframe` applied over `XBI (HProp V)`. We frame a
points-to on a disjoint cell onto a local step — the extended-framework analogue of
`JStateSepLogic.sbb_framed_triple`, with `∗` disjoint-heap separation. -/

/-- The demo postcondition: return `()`, asserting the heap holds `ℓ' ↦ w`. -/
def demoPost {V : Type} (ℓ' : Nat) (w : V) : XPostCond Unit .pure (HProp V) :=
  (fun _ => pointsTo ℓ' w, PUnit.unit)

/-- **A framed points-to triple over the heap.** From the reflexive triple
`⦃ℓ' ↦ w⦄ (pure ()) ⦃_ ↦ ℓ' ↦ w⦄`, the frame rule frames a disjoint points-to
`ℓ ↦ v`, giving `⦃(ℓ' ↦ w) ∗ (ℓ ↦ v)⦄ (pure ()) ⦃_ ↦ (ℓ' ↦ w) ∗ (ℓ ↦ v)⦄` over
the separating conjunction. When `ℓ ≠ ℓ'` the precondition is realized by a
concrete two-cell heap (`pointsTo_sep_disjoint`), so this frames a points-to on a
disjoint cell. -/
theorem heap_framed_triple {V : Type} (ℓ ℓ' : Nat) (v w : V) :
    XPT (ps := .pure)
      (XAssertion.sep .pure ((demoPost ℓ' w).1 ()) (pointsTo ℓ v))
      (xpure (Ω := HProp V) (ps := .pure) ())
      ((demoPost ℓ' w).frameSep (pointsTo ℓ v)) :=
  xframe (xpure_local ()) (XAssertion.le_refl .pure ((demoPost ℓ' w).1 ()))

end CatCrypt.XDijkstra
