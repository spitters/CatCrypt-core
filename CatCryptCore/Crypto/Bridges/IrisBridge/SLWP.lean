/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Core.Code
public import CatCryptCore.Core.StdDoBridge
public import CatCryptCore.Prob.Support
public import CatCryptCore.Crypto.Bridges.IrisBridge.Embedding
public import CatCryptCore.Crypto.Bridges.IrisBridge.OwnWP

/-!
# A separation-logic weakest precondition for `SPComp` in iris-lean's BI

The support weakest precondition `supportWP c Q e` of `SPComp α = Heap → SDistr (α × Heap)` holds
at a heap `h` when every outcome `(a, h')` in the support of `c h` satisfies `Q a h'` and, if `c h`
has failure mass, the failure postcondition `e : Prop` holds. It is a weakest precondition monad
over heap predicates (`supportWPMonad`). At `e = True` it is of partial correctness; at
`e = False` it is of total correctness: it also requires the failure mass to be `0`.

`slWP c Φ` is the framed lifted weakest precondition (`ownFWP`) of the support weakest precondition
at the embedding `Heap.toIState` of heaps into iris-lean's partial states, at `e = True`. Its
values are iris-lean's classical heap propositions `HProp`. At a partial state `σ` it runs the
program on every total heap extending `σ` by a disjoint frame `σf`, and requires every support
outcome to restore the frame untouched (`slWP_apply`), in the frame-quantified style of Yang and
O'Hearn and of Charguéraud. It is of partial correctness: `slWP_fail` holds at every
postcondition. `slWPTotal` is the same construction at `e = False`, of total correctness: it
requires the failure mass to be `0` (`slWPTotal_noFail`).

`SPComp` runs on total heaps (`Heap.get` returns `default` off the domain), so locality does not
follow for an arbitrary computation. Quantifying over the frame inside the weakest precondition
makes the frame rule `slWP_frame` hold with no side condition on `c`. `slWP_bind` holds as an
entailment only, because an arbitrary `SPComp` need not admit a local intermediate state.

## Main definitions and results

* `Realizable σ`: `σ` is the image of a heap.
* `supportWP`, `supportWPMonad`: the support weakest precondition with a failure postcondition.
* `slWP`: the framed lifted support weakest precondition; `slWP_apply` unfolds it.
* structural laws: `slWP_mono`, `slWP_pure_intro`/`slWP_pure` (strict on realizable states),
  `slWP_bind` (lax), `slWP_fail`, `slWP_sample`, `slWP_get`, `slWP_set`.
* `slWP_frame`: the frame rule `slWP c Φ ∗ R ⊢ slWP c (Φ · ∗ R)`, with no side condition on `c`.
* `slWPTotal`: the total correctness version, with `slWPTotal_noFail`, `slWPTotal_le_slWP` and its
  structural laws.

## References

* Yang, O'Hearn, *A Semantic Basis for Local Reasoning*, FoSSaCS 2002
  (the tight interpretation)
* Charguéraud, *Separation Logic for Sequential Programs*, ICFP 2020
  (the ∀-frame wp formulation)
* Calcagno, O'Hearn, Yang, *Local Action and Abstract Separation Logic*,
  LICS 2007 (locality as frame preservation)
* Jung et al., *Iris from the ground up*, JFP 2018
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.IrisBridge

open CatCrypt.Core CatCrypt.Prob
open Iris.Instances.Data
open HeapAlgebra
open Std.Internal.Order

universe u

/-! ## Realizable states -/

/-- A state is realizable if it is the image of a heap: conflict-free with
finitely many owned positions. Sub-states of realizable states are
realizable (`realize_of_finite`). -/
def Realizable (σ : IState) : Prop := ∃ h : Heap, σ = h.toIState

theorem realizable_toIState (h : Heap) : Realizable h.toIState := ⟨h, rfl⟩

/-! ## The support weakest precondition -/

/-- The support weakest precondition of `SPComp` with failure postcondition `e`: from the heap
`h`, every outcome `(a, h')` in the support of `c h` satisfies `Q a h'` (`SPComp.wpProp`), and
nonzero failure mass of `c h` implies `e`. -/
def supportWP {α : Type u} (c : SPComp α) (Q : α → Heap → Prop) (e : Prop) : Heap → Prop :=
  fun h => SPComp.wpProp c Q h ∧ ((c h) none ≠ 0 → e)

/-- The failure mass of a bind: nonzero failure mass of `c >>= f` at `h` comes from the failure
mass of `c h` or from that of a continuation at a support outcome. This is the forward direction
of `SPComp.bind_apply_none_ne_zero_iff` at result types in every universe. -/
theorem spcomp_bind_none_ne_zero {α β : Type u} {c : SPComp α} {f : α → SPComp β} {h : Heap}
    (hn : (SPComp.bind c f h) none ≠ 0) :
    (c h) none ≠ 0 ∨ ∃ a h', (c h) (some (a, h')) ≠ 0 ∧ (f a h') none ≠ 0 := by
  rw [SPComp.bind_def, SDistr.bind_apply_none] at hn
  by_contra hc
  push Not at hc
  apply hn
  rw [hc.1, zero_add]
  refine tsum_eq_zero_iff.2 fun ⟨a, h'⟩ => ?_
  by_cases h0 : (c h) (some (a, h')) = 0 <;> simp [h0, hc.2 a h']

/-- The support weakest precondition is monotone in both postconditions. -/
theorem supportWP_monotone {α : Type u} {c : SPComp α} {Q Q' : α → Heap → Prop} {e e' : Prop}
    (hQ : ∀ a h, Q a h → Q' a h) (he : e → e') (h : Heap) :
    supportWP c Q e h → supportWP c Q' e' h :=
  fun ⟨hs, hf⟩ => ⟨fun a h' hp => hQ a h' (hs a h' hp), fun hn => he (hf hn)⟩

/-- Return for the support weakest precondition. -/
theorem le_supportWP_pure {α : Type u} (x : α) (Q : α → Heap → Prop) (e : Prop) (h : Heap)
    (hQ : Q x h) : supportWP (SPComp.pure x) Q e h := by
  refine ⟨fun a h' hp => ?_, fun hn => ?_⟩
  · have hmem : (a, h') ∈ (SDistr.pure (x, h)).support := hp
    rw [SDistr.mem_support_pure_iff] at hmem
    cases hmem
    exact hQ
  · exact absurd (SDistr.pure_apply_none (x, h)) hn

/-- Lax bind for the support weakest precondition. -/
theorem supportWP_bind_le {α β : Type u} (c : SPComp α) (f : α → SPComp β)
    (Q : β → Heap → Prop) (e : Prop) (h : Heap)
    (hc : supportWP c (fun a => supportWP (f a) Q e) e h) :
    supportWP (SPComp.bind c f) Q e h := by
  obtain ⟨hs, hf⟩ := hc
  refine ⟨fun b h'' hp => ?_, fun hn => ?_⟩
  · rw [SPComp.bind_def] at hp
    obtain ⟨a, h', hca, hfa⟩ := SDistr.bind_support_witness_pair hp
    exact (hs a h' hca).1 b h'' hfa
  · rcases spcomp_bind_none_ne_zero hn with hn | ⟨a, h', hca, hfa⟩
    · exact hf hn
    · exact (hs a h' hca).2 hfa

/-- The support weakest precondition as a weakest precondition monad over heap predicates, with
failure postconditions in `Prop`. It is a definition and not an instance, since `SPComp` has
weakest precondition interpretations at other carriers. -/
@[instance_reducible] def supportWPMonad : Std.WP.WPMonad SPComp.{u} (Heap → Prop) Prop where
  toLawfulMonad := inferInstance
  toWP _ :=
    { trans := fun c => ⟨supportWP c⟩
      trans_monotone := fun _ _ _ _ _ he hQ h => supportWP_monotone hQ he h }
  pure_le_wp_pure x Q e := le_supportWP_pure x Q e
  bind_le_wp_bind c f Q e := supportWP_bind_le c f Q e

/-! ## The framed lifted support weakest precondition -/

/-- Separation-logic weakest precondition for `SPComp`: the framed lifted weakest precondition
`ownFWP` of `supportWPMonad` at the embedding `Heap.toIState`, of partial correctness. -/
noncomputable def slWP {α : Type u} (c : SPComp α) (Φ : α → HProp) : HProp :=
  ownFWP (W := supportWPMonad) Heap.toIState c Φ True

/-- `slWP` at a partial state: from any total heap `hT` realizing `σ` together with a disjoint
frame `σf`, every support outcome `(a, h')` of `c hT` splits `h'` back into a part satisfying
`Φ a` and the untouched frame `σf`. -/
theorem slWP_apply {α : Type u} (c : SPComp α) (Φ : α → HProp) (σ : IState) :
    slWP c Φ σ ↔ ∀ (σf : IState) (hT : Heap), (σ || σf) → σ ∪ σf = hT.toIState →
      ∀ (a : α) (h' : Heap), (c hT) (some (a, h')) ≠ 0 →
        ∃ σ' : IState, (σ' || σf) ∧ σ' ∪ σf = h'.toIState ∧ Φ a σ' := by
  unfold slWP
  rw [ownFWP_apply (W := supportWPMonad)]
  constructor
  · intro h σf hT hd hu a h' hs
    obtain ⟨hsup, -⟩ := h (fun τ => τ = σf) σf hd rfl hT hu.symm
    obtain ⟨σ₁, σ₂, he, hd', hΦ, rfl⟩ := hsup a h' hs
    exact ⟨σ₁, hd', he.symm, hΦ⟩
  · intro h F σf hd hF hT hu
    refine ⟨fun a h' hs => ?_, fun _ => trivial⟩
    obtain ⟨σ', hd', hu', hΦ⟩ := h σf hT hd hu.symm a h' hs
    exact ⟨σ', σf, hu'.symm, hd', hΦ, hF⟩

/-! ## Structural laws -/

theorem slWP_mono {α : Type u} {c : SPComp α} {Φ Ψ : α → HProp}
    (h : ∀ a, Φ a ⊢ Ψ a) : slWP c Φ ⊢ slWP c Ψ :=
  ownFWP_monotone (W := supportWPMonad) Heap.toIState (fun a => h a)
    Lean.Order.PartialOrder.rel_refl

/-- `pure` introduction: unconditional. -/
theorem slWP_pure_intro {α : Type u} (a : α) (Φ : α → HProp) :
    Φ a ⊢ slWP (SPComp.pure a) Φ :=
  le_ownFWP_pure (W := supportWPMonad) Heap.toIState a Φ True

/-- `pure` elimination, on realizable states: take the empty frame. On
non-realizable states (`conflict` positions, infinite ownership) `slWP`
holds vacuously — there is no extending total heap — so the unrestricted
bi-entailment fails; realizability is exactly the missing hypothesis. -/
theorem slWP_pure_elim {α : Type u} {a : α} {Φ : α → HProp} {σ : IState}
    (hr : Realizable σ) (hwp : slWP (SPComp.pure a) Φ σ) : Φ a σ := by
  rw [slWP_apply] at hwp
  obtain ⟨h, rfl⟩ := hr
  obtain ⟨σ', hd', hu', hΦ⟩ :=
    hwp ∅ h (istate_disjoint_empty _) (istate_union_empty _) a h
      (by
        have : (a, h) ∈ (SDistr.pure (a, h)).support :=
          (SDistr.mem_support_pure_iff _ _).mpr rfl
        exact this)
  have : σ' = h.toIState := by rw [← istate_union_empty σ', hu']
  exact this ▸ hΦ

/-- `pure` is strict on realizable states: the wp of `pure a` is exactly
`Φ a`. -/
theorem slWP_pure {α : Type u} (a : α) (Φ : α → HProp) {σ : IState}
    (hr : Realizable σ) : slWP (SPComp.pure a) Φ σ ↔ Φ a σ :=
  ⟨slWP_pure_elim hr, fun hΦ => slWP_pure_intro a Φ σ hΦ⟩

/-- `bind` is lax: sequencing is sound, as an entailment only. The
converse would require extracting a local intermediate state from an
arbitrary `SPComp`, which the total-heap semantics does not provide. -/
theorem slWP_bind {α β : Type u} (c : SPComp α) (f : α → SPComp β)
    (Φ : β → HProp) :
    slWP c (fun a => slWP (f a) Φ) ⊢ slWP (SPComp.bind c f) Φ :=
  ownFWP_bind_le (W := supportWPMonad) Heap.toIState c f Φ True

/-- `fail` satisfies every wp: the support is empty. -/
theorem slWP_fail {α : Type u} (Φ : α → HProp) (σ : IState) :
    slWP (SPComp.fail : SPComp α) Φ σ := by
  rw [slWP_apply]
  intro σf hT _ _ a h' hsupp
  exact absurd (SDistr.fail_apply_some (a, h')) hsupp

/-- `sample` rule: the heap is untouched, the result is any element. -/
theorem slWP_sample (A : Type) [Fintype A] [Nonempty A] (Φ : A → HProp) :
    term(((fun σ => ∀ a : A, Φ a σ) : HProp)) ⊢ slWP (SPComp.sample A) Φ := by
  intro σ hΦ
  rw [slWP_apply]
  intro σf hT hd hu a h' hsupp
  obtain ⟨a₀, _, hpure⟩ := SDistr.bind_support_witness hsupp
  have hmem : (a, h') ∈ (SDistr.pure (a₀, hT)).support := hpure
  rw [SDistr.mem_support_pure_iff] at hmem
  cases hmem
  exact ⟨σ, hd, hu, hΦ _⟩

/-- `get` rule: owning `ℓ ↦ₜ v` forces the read on *any* frame-extended
total heap to return `v`; the state is untouched. -/
theorem slWP_get (ℓ : Location) (v : ℓ.ty) :
    (ℓ ↦ₜ v : HProp) ⊢
      slWP (SPComp.get ℓ) (fun r => iprop(⌜r = v⌝ ∧ ℓ ↦ₜ v)) := by
  intro σ hown
  rw [slWP_apply]
  intro σf hT hd hu a h' hsupp
  -- The total heap stores v's encoding at ℓ.id.
  have hframe : σf ℓ.id = .unknown := by
    rcases hd ℓ.id with h | h
    · rw [hown] at h; exact nomatch h
    · exact h
  have htot : (ℓ ↦ₜ v : HProp) hT.toIState := by
    change hT.toIState ℓ.id = _
    rw [← hu, istate_union_apply, hown, hframe]
  -- The read returns v with the heap unchanged.
  have hmem : (a, h') ∈ (SDistr.pure (hT.get ℓ, hT)).support := hsupp
  rw [SDistr.mem_support_pure_iff] at hmem
  cases hmem
  exact ⟨σ, hd, hu, ptsTo_get htot, hown⟩

/-- `set` rule: writing needs (any-value) ownership of the location and
transfers it to the written value. The local state is updated in place; the
frame is untouched. -/
theorem slWP_set (ℓ : Location) (v : ℓ.ty) :
    ptsToAny ℓ ⊢ slWP (SPComp.set ℓ v) (fun _ => (ℓ ↦ₜ v : HProp)) := by
  intro σ hown
  rw [slWP_apply]
  intro σf hT hd hu a h' hsupp
  obtain ⟨v₀, hv₀⟩ := hown
  have hframe : σf ℓ.id = .unknown := by
    rcases hd ℓ.id with h | h
    · rw [hv₀] at h; exact nomatch h
    · exact h
  have hmem : (a, h') ∈ (SDistr.pure ((), hT.set ℓ v)).support := hsupp
  rw [SDistr.mem_support_pure_iff] at hmem
  cases hmem
  -- Updated local state: σ with ℓ.id overwritten.
  refine ⟨fun i => if i = ℓ.id then .result (Heap.encode v) else σ i,
    ?_, ?_, ?_⟩
  · intro i
    dsimp only
    by_cases hi : i = ℓ.id
    · rw [ite_eq_left hi, hi]; exact Or.inr hframe
    · rw [ite_eq_right hi]; exact hd i
  · funext i
    rw [istate_union_apply]
    by_cases hi : i = ℓ.id
    · subst hi
      rw [ite_eq_left rfl, hframe]
      rw [show hT.set ℓ v = (⟨hT.data.insert ℓ.id (Heap.encode v)⟩ : Heap)
          from rfl,
        toIState_insert_apply, ite_eq_left rfl]
    · rw [ite_eq_right hi]
      have : (hT.set ℓ v).toIState i = hT.toIState i := by
        rw [show hT.set ℓ v = (⟨hT.data.insert ℓ.id (Heap.encode v)⟩ : Heap)
            from rfl,
          toIState_insert_apply, ite_eq_right hi]
      rw [this, ← hu, istate_union_apply]
  · change (if ℓ.id = ℓ.id then _ else _) = _
    rw [ite_eq_left rfl]

/-! ## The frame rule -/

/-- **Frame rule.** `slWP c Φ ∗ R ⊢ slWP c (fun a => Φ a ∗ R)` for
every `SPComp`, with no locality side condition. The frame quantification
inside `slWP` absorbs the new frame `R` into the frame of the weakest precondition. -/
theorem slWP_frame {α : Type u} (c : SPComp α) (Φ : α → HProp) (R : HProp) :
    slWP c Φ ∗ R ⊢ slWP c (fun a => iprop(Φ a ∗ R)) :=
  ownFWP_frame (W := supportWPMonad) Heap.toIState c Φ True R

/-! ## Total correctness -/

/-- The total correctness separation-logic weakest precondition for `SPComp`: the framed lifted
weakest precondition of `supportWPMonad` at the failure postcondition `False`. -/
noncomputable def slWPTotal {α : Type u} (c : SPComp α) (Φ : α → HProp) : HProp :=
  ownFWP (W := supportWPMonad) Heap.toIState c Φ False

/-- Total correctness excludes failure: at the image of a heap `hT`, `slWPTotal c Φ` forces the
failure mass of `c hT` to be `0`. -/
theorem slWPTotal_noFail {α : Type u} {c : SPComp α} {Φ : α → HProp} {hT : Heap}
    (h : slWPTotal c Φ hT.toIState) : (c hT) none = 0 := by
  have h1 := (ownFWP_apply (W := supportWPMonad) Heap.toIState c Φ False hT.toIState).1 h
    (fun τ => τ = ∅) ∅ (istate_disjoint_empty _) rfl hT (istate_union_empty _).symm
  obtain ⟨-, hf⟩ := h1
  by_contra hne
  exact hf hne

/-- Total correctness entails partial correctness. -/
theorem slWPTotal_le_slWP {α : Type u} (c : SPComp α) (Φ : α → HProp) :
    slWPTotal c Φ ⊢ slWP c Φ :=
  ownFWP_monotone (W := supportWPMonad) Heap.toIState (fun _ => Lean.Order.PartialOrder.rel_refl)
    (fun h => h.elim)

/-- Monotonicity of `slWPTotal`. -/
theorem slWPTotal_mono {α : Type u} {c : SPComp α} {Φ Ψ : α → HProp}
    (h : ∀ a, Φ a ⊢ Ψ a) : slWPTotal c Φ ⊢ slWPTotal c Ψ :=
  ownFWP_monotone (W := supportWPMonad) Heap.toIState (fun a => h a)
    Lean.Order.PartialOrder.rel_refl

/-- `pure` introduction for `slWPTotal`. -/
theorem slWPTotal_pure_intro {α : Type u} (a : α) (Φ : α → HProp) :
    Φ a ⊢ slWPTotal (SPComp.pure a) Φ :=
  le_ownFWP_pure (W := supportWPMonad) Heap.toIState a Φ False

/-- Lax `bind` for `slWPTotal`. -/
theorem slWPTotal_bind {α β : Type u} (c : SPComp α) (f : α → SPComp β) (Φ : β → HProp) :
    slWPTotal c (fun a => slWPTotal (f a) Φ) ⊢ slWPTotal (SPComp.bind c f) Φ :=
  ownFWP_bind_le (W := supportWPMonad) Heap.toIState c f Φ False

/-- Frame rule for `slWPTotal`, with no side condition on `c`. -/
theorem slWPTotal_frame {α : Type u} (c : SPComp α) (Φ : α → HProp) (R : HProp) :
    slWPTotal c Φ ∗ R ⊢ slWPTotal c (fun a => iprop(Φ a ∗ R)) :=
  ownFWP_frame (W := supportWPMonad) Heap.toIState c Φ False R

end CatCrypt.Crypto.IrisBridge
