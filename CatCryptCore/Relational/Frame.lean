/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Relational.Judgment
import CatCryptCore.Prob.Coupling

/-!
# Location-Based Frame Rule

This file provides a location-based frame rule for pRHL, the CatCrypt analogue
of separation logic's frame rule and Bluebell's `P * Q` (separating conjunction
= independence). The key idea: assertions on disjoint heap regions plus
computations with bounded footprints enable compositional reasoning.

## Main definitions

* `DependsOn P L` — assertion P only examines locations in L
* `PreservesOutside c L` — computation c only modifies locations in L
* `r_frame_local` — the frame rule: disjoint footprints preserve the frame
* `r_frame_of_preservesNothing` — any frame survives computations that write nothing
* `r_frame_agreeOff` — `agreeOff L` survives computations that write only inside `L`

## Design notes

`RPre = Heap → Heap → Prop` is deterministic (no probabilistic separation needed).
The right analogue of Bluebell's probabilistic separation is *location-based
separation*: assertions on disjoint heap regions + computations with bounded
footprints.

## The three frame rules

The three rules cover three shapes of frame footprint, and none of them is an
instance of another.

* `r_frame_local` frames an assertion with a **finite** footprint `L_f`
  (`DependsOn Frame L_f`) across computations writing only inside a `L_c`
  disjoint from it.
* `r_frame_of_preservesNothing` frames an **arbitrary** assertion, at the price
  of asking both computations to write nothing at all.
* `r_frame_agreeOff` frames the specific assertion `agreeOff L`, whose footprint
  is **co-finite**, across computations writing only inside `L`. `DependsOn
  (agreeOff L) L_f` fails for every finite `L_f`, so `r_frame_local` does not
  reach it; the computations write, so `r_frame_of_preservesNothing` does not
  either.

At `L = ∅` the last two rules meet without either containing the other:
`agreeOff ∅` is whole-heap equality (`agreeOff_empty_iff`), one assertion, while
`r_frame_of_preservesNothing` at the same footprint frames every assertion.

## References

* Bluebell (POPL 2025) — `P * Q` separating conjunction for independence
* O'Hearn, Reynolds, Yang — Separation logic
-/

namespace CatCrypt.Relational

open CatCrypt.Core CatCrypt.Prob

variable {α β : Type}

/-! ## Assertion locality -/

/-- `DependsOn P L` means P only examines locations in L: heap pairs
    agreeing on L cannot be distinguished by P. -/
def DependsOn (P : RPre) (L : LocSet) : Prop :=
  ∀ h₁ h₁' h₂ h₂',
    Heap.agreeOn h₁ h₁' L → Heap.agreeOn h₂ h₂' L →
    P h₁ h₂ → P h₁' h₂'

/-! ### DependsOn instances -/

theorem dependsOn_truePre : DependsOn truePre ∅ := by
  intro _ _ _ _ _ _
  exact id

theorem dependsOn_leftHas (l : Location) (v : l.ty) :
    DependsOn (leftHas l v) {l.id} := by
  intro h₁ h₁' h₂ _ hagree _ hleft
  simp only [leftHas] at hleft ⊢
  unfold Heap.agreeOn at hagree
  have := hagree l.id (Finset.mem_singleton.mpr rfl)
  -- hleft : h₁.get l = v, need h₁'.get l = v
  -- hagree gives h₁.data.lookup l.id = h₁'.data.lookup l.id
  unfold Heap.get at hleft ⊢
  rw [← this]; exact hleft

theorem dependsOn_rightHas (l : Location) (v : l.ty) :
    DependsOn (rightHas l v) {l.id} := by
  intro h₁ _ h₂ h₂' _ hagree hright
  simp only [rightHas] at hright ⊢
  unfold Heap.agreeOn at hagree
  have := hagree l.id (Finset.mem_singleton.mpr rfl)
  unfold Heap.get at hright ⊢
  rw [← this]; exact hright

theorem dependsOn_andPre {P Q : RPre} {L₁ L₂ : LocSet}
    (hP : DependsOn P L₁) (hQ : DependsOn Q L₂) :
    DependsOn (P ⋀ Q) (L₁ ∪ L₂) := by
  intro h₁ h₁' h₂ h₂' hagree₁ hagree₂ ⟨hp, hq⟩
  constructor
  · exact hP h₁ h₁' h₂ h₂'
      (fun id hid => hagree₁ id (Finset.mem_union_left L₂ hid))
      (fun id hid => hagree₂ id (Finset.mem_union_left L₂ hid))
      hp
  · exact hQ h₁ h₁' h₂ h₂'
      (fun id hid => hagree₁ id (Finset.mem_union_right L₁ hid))
      (fun id hid => hagree₂ id (Finset.mem_union_right L₁ hid))
      hq

theorem dependsOn_mono {P : RPre} {L L' : LocSet}
    (h : DependsOn P L) (hsub : L ⊆ L') : DependsOn P L' := by
  intro h₁ h₁' h₂ h₂' hagree₁ hagree₂ hp
  exact h h₁ h₁' h₂ h₂'
    (fun id hid => hagree₁ id (hsub hid))
    (fun id hid => hagree₂ id (hsub hid))
    hp

/-! ## Computation footprint -/

/-- `PreservesOutside c L` means c does not modify locations outside L:
    for every output in c's support, non-L locations are unchanged. -/
def PreservesOutside (c : SPComp α) (L : LocSet) : Prop :=
  ∀ h a h', (c h) (some (a, h')) ≠ 0 →
    ∀ id, id ∉ L → h'.data.lookup id = h.data.lookup id

/-! ### PreservesOutside instances -/

theorem preservesOutside_pure (a : α) : PreservesOutside (SPComp.pure a) ∅ := by
  intro h a' h' hne id _
  simp only [SPComp.pure, SDistr.pure, PMF.pure_apply] at hne
  by_cases heq : some (a', h') = some (a, h)
  · simp only [Option.some.injEq, Prod.mk.injEq] at heq; rw [heq.2]
  · exact absurd (if_neg heq) hne

theorem preservesOutside_sample (α : Type) [Fintype α] [Nonempty α] :
    PreservesOutside (SPComp.sample α) ∅ := by
  intro h a h' hne id _
  -- SPComp.sample α h = (SDistr.uniform α).bind (fun a => SDistr.pure (a, h))
  simp only [SPComp.sample, SDistr.bind, PMF.bind_apply] at hne
  -- The distribution only produces (a, h) for the original heap h
  by_contra hdiff
  apply hne
  rw [ENNReal.tsum_eq_zero]
  intro oa
  cases oa with
  | none => simp [SDistr.fail, PMF.pure_apply]
  | some x =>
    simp only [SDistr.pure, PMF.pure_apply]
    by_cases heq : some (a, h') = some (x, h)
    · simp only [Option.some.injEq, Prod.mk.injEq] at heq
      -- heq.2 : h' = h, contradicts hdiff
      exact absurd (heq.2 ▸ rfl) hdiff
    · simp only [heq, ↓reduceIte, mul_zero]

theorem preservesOutside_get (l : Location) : PreservesOutside (SPComp.get l) ∅ := by
  intro h a h' hne id _
  simp only [SPComp.get_def, SDistr.pure, PMF.pure_apply] at hne
  by_cases heq : some (a, h') = some (h.get l, h)
  · simp only [Option.some.injEq, Prod.mk.injEq] at heq; rw [heq.2]
  · exact absurd (if_neg heq) hne

theorem preservesOutside_set (l : Location) (v : l.ty) :
    PreservesOutside (SPComp.set l v) {l.id} := by
  intro h a h' hne id hnotin
  simp only [SPComp.set_def, SDistr.pure, PMF.pure_apply] at hne
  by_cases heq : some (a, h') = some ((), h.set l v)
  · simp only [Option.some.injEq, Prod.mk.injEq] at heq
    rw [heq.2]
    have hne_id : id ≠ l.id := fun h => hnotin (Finset.mem_singleton.mpr h)
    exact Finmap.lookup_insert_of_ne _ hne_id
  · exfalso; exact hne (if_neg heq)

theorem preservesOutside_bind {c : SPComp α} {f : α → SPComp β}
    {L₁ L₂ : LocSet}
    (hc : PreservesOutside c L₁)
    (hf : ∀ a, PreservesOutside (f a) L₂) :
    PreservesOutside (c >>= f) (L₁ ∪ L₂) := by
  intro h b h' hne id hnotin
  have hnotin₁ : id ∉ L₁ := fun hmem => hnotin (Finset.mem_union_left L₂ hmem)
  have hnotin₂ : id ∉ L₂ := fun hmem => hnotin (Finset.mem_union_right L₁ hmem)
  -- c >>= f at h produces (b, h') with nonzero prob
  -- This means ∃ a h'', c h produces (a, h'') and f a h'' produces (b, h')
  -- both with nonzero prob
  simp only [SPComp.monad_bind_eq, SPComp.bind_def, SDistr.bind, PMF.bind_apply] at hne
  -- hne : ∑' oa, c h oa * (match oa ...) (some (b, h')) ≠ 0
  -- So some term in the sum is nonzero
  by_contra hdiff
  apply hne
  rw [ENNReal.tsum_eq_zero]
  intro oa
  cases oa with
  | none => simp [SDistr.fail, PMF.pure_apply]
  | some p =>
    obtain ⟨a, h''⟩ := p
    by_cases hc_prob : c h (some (a, h'')) = 0
    · simp [hc_prob]
    · -- c h produces (a, h'') with nonzero prob
      -- So h''.data.lookup id = h.data.lookup id (from hc)
      have hc_agree := hc h a h'' hc_prob id hnotin₁
      -- If f a h'' produces (b, h') with nonzero prob,
      -- then h'.data.lookup id = h''.data.lookup id (from hf)
      by_cases hf_prob : (f a h'') (some (b, h')) = 0
      · simp [hf_prob, mul_zero]
      · -- h'.data.lookup id = h''.data.lookup id = h.data.lookup id
        have hf_agree := hf a h'' b h' hf_prob id hnotin₂
        -- But h'.data.lookup id ≠ h.data.lookup id by hdiff
        exact absurd (hf_agree.trans hc_agree) hdiff

/-! ## The frame rule -/

/-- Location-based frame rule: if computations only modify locations in `L_c`,
    and the frame assertion only depends on locations in `L_f`, and these
    sets are disjoint, then the frame is preserved.

    This is the CatCrypt analogue of separation logic's frame rule. -/
theorem r_frame_local {Φ Frame : RPre} {Ψ : RPost α β}
    {c₁ : SPComp α} {c₂ : SPComp β}
    {L_c L_f : LocSet}
    (hLocal₁ : PreservesOutside c₁ L_c)
    (hLocal₂ : PreservesOutside c₂ L_c)
    (hFrame : DependsOn Frame L_f)
    (hDisjoint : Disjoint L_c L_f)
    (hInner : rHoare Φ c₁ c₂ Ψ) :
    rHoare (Φ ⋀ Frame) c₁ c₂
      (fun a h₁ b h₂ => Ψ a h₁ b h₂ ∧ Frame h₁ h₂) := by
  intro h₁ h₂ ⟨hΦ, hFr⟩
  -- Get the coupling from the inner judgment
  obtain ⟨coupling, hsat⟩ := hInner h₁ h₂ hΦ
  -- Use the same coupling, but strengthen the relation
  use coupling
  intro ⟨a, h₁'⟩ ⟨b, h₂'⟩ hjoint
  -- hjoint : coupling.joint (some ((a, h₁'), (b, h₂'))) ≠ 0
  -- From satisfies: Ψ a h₁' b h₂'
  have hΨ := hsat ⟨a, h₁'⟩ ⟨b, h₂'⟩ hjoint
  constructor
  · exact hΨ
  · -- Need: Frame h₁' h₂'
    -- Strategy: show h₁' agrees with h₁ on L_f, and h₂' agrees with h₂ on L_f
    -- From the coupling support, extract that c₁ h₁ and c₂ h₂ have nonzero prob
    have hleft := coupling.in_left_support hjoint
    have hright := coupling.in_right_support hjoint
    -- hleft : (c₁ h₁) (some (a, h₁')) ≠ 0
    -- hright : (c₂ h₂) (some (b, h₂')) ≠ 0
    -- From PreservesOutside: non-L_c locations unchanged
    have hagree₁ : ∀ id, id ∉ L_c → h₁'.data.lookup id = h₁.data.lookup id :=
      hLocal₁ h₁ a h₁' hleft
    have hagree₂ : ∀ id, id ∉ L_c → h₂'.data.lookup id = h₂.data.lookup id :=
      hLocal₂ h₂ b h₂' hright
    -- From Disjoint: L_f ⊆ L_cᶜ
    have hsub : ∀ id, id ∈ L_f → id ∉ L_c := by
      intro id hid hid'
      exact Finset.disjoint_right.mp hDisjoint hid hid'
    -- So h₁' agrees with h₁ on L_f, and h₂' agrees with h₂ on L_f
    have h₁_agree : Heap.agreeOn h₁ h₁' L_f := by
      intro id hid
      exact (hagree₁ id (hsub id hid)).symm
    have h₂_agree : Heap.agreeOn h₂ h₂' L_f := by
      intro id hid
      exact (hagree₂ id (hsub id hid)).symm
    -- Apply DependsOn to transfer Frame
    exact hFrame h₁ h₁' h₂ h₂' h₁_agree h₂_agree hFr

/-- A computation that modifies nothing leaves its heap alone. -/
theorem heap_eq_of_preservesOutside_empty {c : SPComp α} (h : PreservesOutside c ∅)
    {h₀ : Heap} {a : α} {h' : Heap} (hsupp : (c h₀) (some (a, h')) ≠ 0) :
    h' = h₀ :=
  Heap.ext_lookup fun id => h h₀ a h' hsupp id (Finset.notMem_empty id)

/-- Frame rule for computations that modify no location: the precondition
carries through to the postcondition, whatever it is.

`r_frame_local` asks the frame to depend on a `LocSet`, which is a `Finset`, so
it cannot frame an assertion with no finite footprint — `eqPre`, whole-heap
equality, is one such. Nothing is needed of the assertion here, because the two
computations leave their heaps as they found them, so the assertion holds of the
final pair exactly when it held of the initial pair. -/
theorem r_frame_of_preservesNothing {Φ : RPre} {Ψ : RPost α β}
    {c₁ : SPComp α} {c₂ : SPComp β}
    (hc₁ : PreservesOutside c₁ ∅) (hc₂ : PreservesOutside c₂ ∅)
    (hInner : rHoare truePre c₁ c₂ Ψ) :
    rHoare Φ c₁ c₂ (fun a h₁ b h₂ => Ψ a h₁ b h₂ ∧ Φ h₁ h₂) := by
  intro h₁ h₂ hΦ
  obtain ⟨coupling, hsat⟩ := hInner h₁ h₂ trivial
  refine ⟨coupling, ?_⟩
  intro ⟨a, h₁'⟩ ⟨b, h₂'⟩ hjoint
  refine ⟨hsat ⟨a, h₁'⟩ ⟨b, h₂'⟩ hjoint, ?_⟩
  have e₁ : h₁' = h₁ :=
    heap_eq_of_preservesOutside_empty hc₁ (coupling.in_left_support hjoint)
  have e₂ : h₂' = h₂ :=
    heap_eq_of_preservesOutside_empty hc₂ (coupling.in_right_support hjoint)
  exact e₁ ▸ e₂ ▸ hΦ

/-- Frame rule for agreement outside a write-set: if both computations write only
inside `L` and the two initial heaps agree outside `L`, the two final heaps agree
outside `L`.

The frame `agreeOff L` constrains every location outside a finite set, so it has
no finite footprint and `DependsOn (agreeOff L) L_f` fails for every `L_f`; the
computations write inside `L`, so `r_frame_of_preservesNothing` does not apply.
What replaces the disjointness hypothesis is that the frame's footprint is the
complement of the write-set: each side's final heap agrees with its own initial
heap outside `L`, and the initial heaps agree with each other there. -/
theorem r_frame_agreeOff {Φ : RPre} {Ψ : RPost α β}
    {c₁ : SPComp α} {c₂ : SPComp β} {L : LocSet}
    (hc₁ : PreservesOutside c₁ L) (hc₂ : PreservesOutside c₂ L)
    (hInner : rHoare Φ c₁ c₂ Ψ) :
    rHoare (Φ ⋀ agreeOff L) c₁ c₂
      (fun a h₁ b h₂ => Ψ a h₁ b h₂ ∧ agreeOff L h₁ h₂) := by
  intro h₁ h₂ ⟨hΦ, hoff⟩
  obtain ⟨coupling, hsat⟩ := hInner h₁ h₂ hΦ
  refine ⟨coupling, ?_⟩
  intro ⟨a, h₁'⟩ ⟨b, h₂'⟩ hjoint
  refine ⟨hsat ⟨a, h₁'⟩ ⟨b, h₂'⟩ hjoint, ?_⟩
  intro id hid
  have e₁ := hc₁ h₁ a h₁' (coupling.in_left_support hjoint) id hid
  have e₂ := hc₂ h₂ b h₂' (coupling.in_right_support hjoint) id hid
  exact e₁.trans ((hoff id hid).trans e₂.symm)

end CatCrypt.Relational
