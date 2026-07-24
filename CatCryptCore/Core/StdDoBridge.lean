/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Std.Do.Triple
import Std.Tactic.Do
import CatCryptCore.Unary.Judgment
import CatCryptCore.Crypto.NomPkgBridge

set_option autoImplicit false

/-!
# `Std.Do` / `mvcgen` bridge for `SPComp`

Support-level `Std.Do` view of `SPComp`: a `Std.Do.WP`/`Std.Do.WPMonad`
instance whose weakest precondition is *almost-sure* (support-level)
satisfaction of the postcondition. This makes `mvcgen` usable for
functional-correctness goals about `SPComp` do-blocks. Quantitative bounds
(`sdist`, advantage) live outside `PredTrans` — expectation transformers are
monotone but not conjunctive, so they cannot inhabit
`PredTrans.conjunctiveRaw`; they belong to the `Advantage`/`sdist` layer.

The design mirrors VCVio's proposition-level bridge for `OracleComp`
(`VCVio/ProgramLogic/Unary/StdDoBridge.lean`).

## Post shape

`SPComp α = Heap → SDistr (α × Heap)` is the monad
`StateT Heap (OptionT-over-PMF)`: failure (`SDistr`'s `none`) carries no
final heap. The structural mirror of that stack is

* `spPostShape = .arg Heap (.except PUnit .pure)`

so assertions are `Heap → ULift Prop` and postconditions carry a *heap-free*
failure barrel `PUnit → ULift Prop`. The alternative shape
`.except PUnit (.arg Heap .pure)` would give the failure barrel a `Heap`
argument that the semantics cannot supply (there is no heap at failure), and
`wp_bind` fails for it; with the heap-free barrel both `WPMonad` laws hold
on the nose.

`⇓ r => ...` (total correctness: the program must not fail) and
`⇓? r => ...` (partial correctness: nothing asserted on failure) both make
sense for this shape; `⇓?`-triples coincide with the unary `pHoare`
judgment, and `⇓`-triples additionally assert `SPComp.NoFail`.

## Main definitions

* `SPComp.wpProp` — support-level weakest precondition as a plain predicate
* `SPComp.wpSupport`, `SPComp.instWP`, `SPComp.instWPMonad` — the `Std.Do`
  instances at shape `spPostShape`
* adequacy: `wpProp_iff_forall_support`, `triple_mayThrow_iff`,
  `triple_noThrow_iff`, `pHoare_iff_triple`, `triple_noThrow_true_iff_noFail`,
  `isPure_wpProp_iff`
* `@[spec]` lemmas for `SPComp.get`/`set`/`sample`/`fail` so `mvcgen`
  walks `SPComp` do-blocks

Reached via the `CatCrypt.Tactics` umbrella through `Tactics/VC.lean`
(`ssprove_nofail` / `ssprove_phoare` lower goals into this bridge).
-/

namespace CatCrypt.Core.SPComp

open CatCrypt.Prob Std.Do
open scoped ENNReal

universe u

variable {α β : Type}

/-! ## SDistr support lemmas for bind

Support and failure mass of `SDistr.bind`, in the `≠ 0` form used by the
support-level WP. -/

theorem _root_.CatCrypt.Prob.SDistr.bind_apply_some_ne_zero_iff {α β : Type u}
    (d : SDistr α) (f : α → SDistr β) (b : β) :
    (d.bind f) (some b) ≠ 0 ↔ ∃ a, d (some a) ≠ 0 ∧ (f a) (some b) ≠ 0 := by
  unfold SDistr.bind
  rw [ne_eq, PMF.bind_apply, ENNReal.tsum_eq_zero]
  push Not
  constructor
  · rintro ⟨oa, hoa⟩
    cases oa with
    | none => simp at hoa
    | some a => exact ⟨a, mul_ne_zero_iff.mp hoa⟩
  · rintro ⟨a, h1, h2⟩
    exact ⟨some a, mul_ne_zero h1 h2⟩

theorem _root_.CatCrypt.Prob.SDistr.bind_apply_none_ne_zero_iff {α β : Type u}
    (d : SDistr α) (f : α → SDistr β) :
    (d.bind f) none ≠ 0 ↔ d none ≠ 0 ∨ ∃ a, d (some a) ≠ 0 ∧ (f a) none ≠ 0 := by
  unfold SDistr.bind
  rw [ne_eq, PMF.bind_apply, ENNReal.tsum_eq_zero]
  push Not
  constructor
  · rintro ⟨oa, hoa⟩
    cases oa with
    | none =>
      left
      simpa using hoa
    | some a => exact Or.inr ⟨a, mul_ne_zero_iff.mp hoa⟩
  · rintro (h | ⟨a, h1, h2⟩)
    · exact ⟨none, by simpa using h⟩
    · exact ⟨some a, mul_ne_zero h1 h2⟩

/-- `(SDistr.pure x) (some y) ≠ 0` iff `x = y` (point-mass support). -/
theorem _root_.CatCrypt.Prob.SDistr.pure_apply_some_ne_zero_iff {α : Type u} (x y : α) :
    (SDistr.pure x) (some y) ≠ 0 ↔ x = y :=
  SDistr.mem_support_pure_iff x y

/-! ## SPComp-level support lemmas -/

/-- Support of a bound computation, in `≠ 0` form. -/
theorem bind_apply_some_ne_zero_iff (c : SPComp α) (f : α → SPComp β)
    (h : Heap) (b : β) (h'' : Heap) :
    ((SPComp.bind c f) h) (some (b, h'')) ≠ 0 ↔
      ∃ a h', (c h) (some (a, h')) ≠ 0 ∧ ((f a) h') (some (b, h'')) ≠ 0 := by
  rw [SPComp.bind_def, SDistr.bind_apply_some_ne_zero_iff]
  constructor
  · rintro ⟨⟨a, h'⟩, h1, h2⟩
    exact ⟨a, h', h1, h2⟩
  · rintro ⟨a, h', h1, h2⟩
    exact ⟨(a, h'), h1, h2⟩

/-- Failure mass of a bound computation, in `≠ 0` form. -/
theorem bind_apply_none_ne_zero_iff (c : SPComp α) (f : α → SPComp β) (h : Heap) :
    ((SPComp.bind c f) h) none ≠ 0 ↔
      (c h) none ≠ 0 ∨ ∃ a h', (c h) (some (a, h')) ≠ 0 ∧ ((f a) h') none ≠ 0 := by
  rw [SPComp.bind_def, SDistr.bind_apply_none_ne_zero_iff]
  constructor
  · rintro (hn | ⟨⟨a, h'⟩, h1, h2⟩)
    · exact Or.inl hn
    · exact Or.inr ⟨a, h', h1, h2⟩
  · rintro (hn | ⟨a, h', h1, h2⟩)
    · exact Or.inl hn
    · exact Or.inr ⟨(a, h'), h1, h2⟩

/-! ## The support-level weakest precondition -/

/-- Support-level (almost-sure) weakest precondition for `SPComp`: from
initial heap `h`, every outcome `(a, h')` in the support of `c h` satisfies
`post a h'`. Says nothing about the failure mass — see the failure barrel of
`wpSupport` for that. -/
def wpProp {α : Type*} (c : SPComp α) (post : α → Heap → Prop) : Heap → Prop :=
  fun h => ∀ a h', (c h) (some (a, h')) ≠ 0 → post a h'

/-- Adequacy: `wpProp` is the ∀-over-support statement. -/
theorem wpProp_iff_forall_support {α : Type*} (c : SPComp α)
    (post : α → Heap → Prop) (h : Heap) :
    wpProp c post h ↔ ∀ p ∈ (c h).support, post p.1 p.2 := by
  constructor
  · rintro hw ⟨a, h'⟩ hp
    exact hw a h' hp
  · intro hw a h' hp
    exact hw (a, h') hp

/-- The `Std.Do` post shape for `SPComp`: one state layer (`Heap`) over one
heap-free failure layer (`PUnit`, the subprobability defect of `SDistr`). -/
abbrev spPostShape : PostShape := .arg Heap (.except PUnit .pure)

/-- The support-level predicate transformer of an `SPComp` computation:
success barrel = `wpProp`, failure barrel = guard on nonzero failure mass. -/
protected def wpSupport (c : SPComp α) : PredTrans spPostShape α where
  trans Q h :=
    ⟨wpProp c (fun a h' => (Q.1 a h').down) h ∧ ((c h) none ≠ 0 → (Q.2.1 ⟨⟩).down)⟩
  conjunctiveRaw := by
    intro Q₁ Q₂ h
    simp only [SPred.bientails_nil, SPred.and_cons, SPred.and_nil, wpProp]
    constructor
    · rintro ⟨hs, hf⟩
      exact ⟨⟨fun a h' hp => (hs a h' hp).1, fun hn => (hf hn).1⟩,
             ⟨fun a h' hp => (hs a h' hp).2, fun hn => (hf hn).2⟩⟩
    · rintro ⟨⟨hs₁, hf₁⟩, ⟨hs₂, hf₂⟩⟩
      exact ⟨fun a h' hp => ⟨hs₁ a h' hp, hs₂ a h' hp⟩, fun hn => ⟨hf₁ hn, hf₂ hn⟩⟩

instance instWP : WP SPComp spPostShape where
  wp c := SPComp.wpSupport c

theorem wp_eq (c : SPComp α) : wp (m := SPComp) c = SPComp.wpSupport c := rfl

/-- Unfolding lemma for the support-level WP. Deliberately *not* `@[simp]`:
`mvcgen` must keep `wp⟦·⟧` opaque and walk via `@[spec]` lemmas. -/
theorem wpSupport_apply_down (c : SPComp α) (Q : PostCond α spPostShape) (h : Heap) :
    ((SPComp.wpSupport c).apply Q h).down ↔
      (∀ a h', (c h) (some (a, h')) ≠ 0 → (Q.1 a h').down) ∧
        ((c h) none ≠ 0 → (Q.2.1 ⟨⟩).down) :=
  Iff.rfl

instance instWPMonad : WPMonad SPComp spPostShape where
  toLawfulMonad := inferInstance
  toWP := instWP
  wp_pure a := by
    ext Q h
    simp only [wp_eq, wpSupport_apply_down, PredTrans.apply_Pure_pure,
      monad_pure_eq, SPComp.pure_def, SDistr.pure_apply_none,
      SDistr.pure_apply_some_ne_zero_iff]
    constructor
    · rintro ⟨hs, -⟩
      exact hs a h rfl
    · intro hQ
      refine ⟨fun b h' hb => ?_, fun hn => absurd rfl hn⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hb
      exact hQ
  wp_bind x f := by
    ext Q h
    simp only [wp_eq, PredTrans.apply_Bind_bind, wpSupport_apply_down,
      monad_bind_eq, bind_apply_some_ne_zero_iff, bind_apply_none_ne_zero_iff]
    constructor
    · rintro ⟨hs, hf⟩
      exact ⟨fun a h' ha =>
        ⟨fun b h'' hb => hs b h'' ⟨a, h', ha, hb⟩,
         fun hn => hf (Or.inr ⟨a, h', ha, hn⟩)⟩,
        fun hn => hf (Or.inl hn)⟩
    · rintro ⟨hs, hf⟩
      refine ⟨fun b h'' hb => ?_, fun hn => ?_⟩
      · obtain ⟨a, h', ha, hb'⟩ := hb
        exact (hs a h' ha).1 b h'' hb'
      · rcases hn with hn | ⟨a, h', ha, hn⟩
        · exact hf hn
        · exact (hs a h' ha).2 hn

/-! ## Adequacy: triples vs `wpProp`, `pHoare`, `NoFail`, `IsPure` -/

/-- A `Triple` from pointwise success/failure obligations. -/
theorem triple_of_forall (c : SPComp α) (P : Assertion spPostShape)
    (Q : PostCond α spPostShape)
    (hsucc : ∀ h, (P h).down → ∀ a h', (c h) (some (a, h')) ≠ 0 → (Q.1 a h').down)
    (hfail : ∀ h, (P h).down → (c h) none ≠ 0 → (Q.2.1 ⟨⟩).down) :
    Triple c P Q := by
  intro h hP
  exact ⟨fun a h' hp => hsucc h hP a h' hp, hfail h hP⟩

/-- Adequacy for partial correctness (`⇓?`): a `mayThrow` triple is exactly
the universally-quantified `wpProp` statement. Nothing is asserted about the
failure mass. -/
theorem triple_mayThrow_iff (c : SPComp α) (P : Heap → Prop)
    (post : α → Heap → Prop) :
    Triple c (fun h => ⌜P h⌝) (PostCond.mayThrow fun a h => ⌜post a h⌝) ↔
      ∀ h, P h → wpProp c post h := by
  constructor
  · intro ht h hP a h' hp
    exact (ht h hP).1 a h' hp
  · intro hw h hP
    exact ⟨fun a h' hp => hw h hP a h' hp, fun _ => trivial⟩

/-- Adequacy for total correctness (`⇓`): a `noThrow` triple is `wpProp`
plus zero failure mass from every `P`-heap. -/
theorem triple_noThrow_iff (c : SPComp α) (P : Heap → Prop)
    (post : α → Heap → Prop) :
    Triple c (fun h => ⌜P h⌝) (PostCond.noThrow fun a h => ⌜post a h⌝) ↔
      ∀ h, P h → wpProp c post h ∧ (c h) none = 0 := by
  constructor
  · intro ht h hP
    refine ⟨fun a h' hp => (ht h hP).1 a h' hp, ?_⟩
    by_contra hn
    exact (ht h hP).2 hn
  · intro hw h hP
    exact ⟨fun a h' hp => (hw h hP).1 a h' hp, fun hn => absurd (hw h hP).2 hn⟩

/-- The unary pHL judgment (`CatCrypt.Unary.pHoare`) is exactly the
partial-correctness (`⇓?`) `Std.Do` triple. -/
theorem pHoare_iff_triple (P : Unary.UPre) (c : SPComp α) (Q : Unary.UPost α) :
    Unary.pHoare P c Q ↔
      Triple c (fun h => ⌜P h⌝) (PostCond.mayThrow fun a h => ⌜Q a h⌝) :=
  (triple_mayThrow_iff c P Q).symm

/-- `SPComp.NoFail` is the trivial total-correctness triple: the failure
barrel `⌜False⌝` of `noThrow` forces zero failure mass. -/
theorem triple_noThrow_true_iff_noFail (c : SPComp α) :
    Triple c (fun _ => ⌜True⌝) (PostCond.noThrow fun _ _ => ⌜True⌝) ↔
      CatCrypt.Crypto.SPComp.NoFail c := by
  rw [triple_noThrow_iff]
  constructor
  · intro hw h
    exact (hw h trivial).2
  · intro hnf h _
    exact ⟨fun _ _ _ => trivial, hnf h⟩

/-- For an `IsPure` computation with witness distribution `d`, the
support-level WP is the ∀-over-`d.support` statement at the *unchanged*
heap. -/
theorem isPure_wpProp_iff {c : SPComp α} {d : SDistr α}
    (hd : ∀ h, c h = d.bind fun a => SDistr.pure (a, h))
    (post : α → Heap → Prop) (h : Heap) :
    wpProp c post h ↔ ∀ a, d (some a) ≠ 0 → post a h := by
  constructor
  · intro hw a ha
    refine hw a h ?_
    rw [hd h, SDistr.bind_apply_some_ne_zero_iff]
    exact ⟨a, ha, (SDistr.pure_apply_some_ne_zero_iff _ _).mpr rfl⟩
  · intro hp a h' hsupp
    rw [hd h, SDistr.bind_apply_some_ne_zero_iff] at hsupp
    obtain ⟨a₀, ha₀, hp'⟩ := hsupp
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ (SDistr.pure_apply_some_ne_zero_iff _ _).mp hp'
    exact hp a₀ ha₀

/-! ## `@[spec]` lemmas for the SPComp primitives

These let `mvcgen` walk `SPComp` do-blocks: the generic `Std.Do.Spec.bind` /
`Spec.pure` handle the monadic skeleton (via `instWPMonad`), and these
lemmas handle the leaves. -/

namespace Spec

/-- Spec for `SPComp.get`: returns the heap's value at `l`, heap unchanged,
never fails. -/
@[spec]
theorem get (l : Location) {Q : PostCond l.ty spPostShape} :
    Triple (SPComp.get l) (fun h => Q.1 (h.get l) h) Q := by
  apply triple_of_forall
  · intro h hP a h' hs
    obtain ⟨rfl, rfl⟩ :=
      Prod.mk.injEq .. ▸ (SDistr.pure_apply_some_ne_zero_iff _ _).mp hs
    exact hP
  · intro h _ hn
    exact absurd (SDistr.pure_apply_none _) hn

/-- Spec for `SPComp.set`: writes `v` at `l`, returns `()`, never fails. -/
@[spec]
theorem set (l : Location) (v : l.ty) {Q : PostCond Unit spPostShape} :
    Triple (SPComp.set l v) (fun h => Q.1 () (h.set l v)) Q := by
  apply triple_of_forall
  · intro h hP a h' hs
    obtain ⟨rfl, rfl⟩ :=
      Prod.mk.injEq .. ▸ (SDistr.pure_apply_some_ne_zero_iff _ _).mp hs
    exact hP
  · intro h _ hn
    exact absurd (SDistr.pure_apply_none _) hn

/-- Spec for `SPComp.sample`: the result can be any element of `A`
(uniform has full support), heap unchanged, never fails. -/
@[spec]
theorem sample (A : Type) [Fintype A] [Nonempty A] {Q : PostCond A spPostShape} :
    Triple (SPComp.sample A) (fun h => SPred.forall fun a => Q.1 a h) Q := by
  apply triple_of_forall
  · intro h hP a h' hs
    rcases (SDistr.bind_apply_some_ne_zero_iff _ _ _).mp hs with ⟨a₀, _, hp⟩
    obtain ⟨rfl, rfl⟩ :=
      Prod.mk.injEq .. ▸ (SDistr.pure_apply_some_ne_zero_iff _ _).mp hp
    exact hP a₀
  · intro h _ hn
    rcases (SDistr.bind_apply_none_ne_zero_iff _ _).mp hn with hu | ⟨a, _, hp⟩
    · exact absurd SDistr.uniform_apply_none hu
    · exact absurd (SDistr.pure_apply_none _) hp

/-- Spec for `SPComp.fail`: empty support, always fails — the precondition
is the failure barrel. -/
@[spec]
theorem fail {α : Type} {Q : PostCond α spPostShape} :
    Triple (SPComp.fail : SPComp α) (fun _ => Q.2.1 ⟨⟩) Q := by
  apply triple_of_forall
  · intro h _ a h' hs
    exact absurd (SDistr.fail_apply_some _) hs
  · intro h hP _
    exact hP

/-- Spec for the prefix form `SPComp.pure` (the generic `Std.Do.Spec.pure`
covers `Pure.pure`; this covers explicit `SPComp.pure` leaves). -/
@[spec]
theorem purePrim {α : Type} (a : α) {Q : PostCond α spPostShape} :
    Triple (SPComp.pure a) (Q.1 a) Q := by
  apply triple_of_forall
  · intro h hP b h' hs
    obtain ⟨rfl, rfl⟩ :=
      Prod.mk.injEq .. ▸ (SDistr.pure_apply_some_ne_zero_iff _ _).mp hs
    exact hP
  · intro h _ hn
    exact absurd (SDistr.pure_apply_none _) hn

end Spec

end CatCrypt.Core.SPComp

/-! ## Examples: mvcgen-closed functional-correctness triples -/

namespace CatCrypt.Core.StdDoBridgeExamples

open CatCrypt.Core CatCrypt.Prob Std.Do

/-- Demo location storing a `Bool`. -/
abbrev bLoc : Location := ⟨0, Bool⟩

/-- Write-then-read returns the written value (total correctness: the
program provably does not fail). -/
example (l : Location) (v : l.ty) :
    ⦃⌜True⌝⦄ (do SPComp.set l v; SPComp.get l) ⦃⇓ r => fun _ => ⌜r = v⌝⦄ := by
  mvcgen
  simp [Heap.get_set_same]

/-- Sampling then post-processing: a tautological function of the sample is
almost-surely `true`. -/
example :
    ⦃⌜True⌝⦄ (do let b ← SPComp.sample Bool; pure (b || !b))
    ⦃⇓ r => fun _ => ⌜r = true⌝⦄ := by
  mvcgen
  simp [SPComp.wp_eq, SPComp.wpSupport_apply_down, SPComp.pure_def,
    SDistr.pure_apply_none]

/-- Sample, store, read back: the read value almost-surely equals the
sampled one. -/
example :
    ⦃⌜True⌝⦄
      (do let b ← SPComp.sample Bool
          SPComp.set bLoc b
          let r ← SPComp.get bLoc
          pure (r == b))
    ⦃⇓ r => fun _ => ⌜r = true⌝⦄ := by
  mvcgen
  simp [SPComp.wp_eq, SPComp.wpSupport_apply_down, SPComp.bind_apply_some_ne_zero_iff,
    SPComp.bind_apply_none_ne_zero_iff, SPComp.pure_def, SPComp.get_def, SPComp.set_def,
    SDistr.pure_apply_none, Heap.get_set_same]

end CatCrypt.Core.StdDoBridgeExamples
