/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Relational.Judgment
import CatCryptCore.Prob.Coupling

/-!
# Relational Separating Conjunction

A separating conjunction on relational assertions `RPre = Heap → Heap → Prop`, and
the frame rule it supports.

## Main definitions

* `HeapDisj`, `heapUnion` (`⊎`), `HeapSplit` — the partial commutative monoid of heaps
* `sepPre` (`∗`) — separating conjunction of relational preconditions
* `sepPost` (`∗ᵖ`) — separating conjunction of a relational postcondition with a frame
* `emp` — the assertion holding only of the pair of empty heaps
* `Frameable c D` — the separation-logic locality of `c` on heaps satisfying `D`
* `r_frame_sep` — the frame rule
* `not_frameable_get` — reading is not local at a heap that does not own the location

## Design

`sepPre P Q` splits **both** heaps of the pair, and splits them **independently**:
`(P ∗ Q) h₁ h₂` asserts that `h₁ = a₁ ⊎ b₁` and `h₂ = a₂ ⊎ b₂` for some splits with
`P a₁ a₂` and `Q b₁ b₂`. The two splits are unrelated to each other; in particular the
domains `a₁` and `a₂` need not coincide.

The alternative — a lockstep split, additionally demanding `a₁.data.keys = a₂.data.keys`
— is a strictly stronger assertion. As a precondition that is harmless, but the frame
rule needs the same connective in the postcondition, where the extra conjunct becomes an
obligation: the two runs must end with equal domains on the non-frame part. `rHoare`
couples the two runs through a relation on `(value, heap)` pairs and delivers exactly
that relation, so a lockstep postcondition would have to be established from `Ψ`, which
in general does not mention domains. Independent splits keep the frame rule free of that
obligation, and the frame parts `b₁`, `b₂` are still related by the frame assertion, so
no information about the frame is lost.

## The locality side condition

`rHoare` is a *global* triple: it quantifies over whole heaps, and `SPComp` has no fault
state, so a computation cannot be prevented from reading or writing outside a region by
typing alone. The frame rule therefore cannot be side-condition-free; the side condition
is `Frameable c D`, the semantic locality of separation logic:

* `Frameable.frame` — running `c` on `h ⊎ hf` is running it on `h` and re-attaching `hf`;
* `Frameable.confined` — `c` allocates no location outside the domain it was given.

Both are relative to a domain predicate `D`, because `SPComp.get l` and `SPComp.set l v`
are local only on heaps that already contain `l` — that hypothesis is exactly what the
points-to assertion `l ↦ _` supplies in a small-footprint semantics. The frame rule
requires `D` to follow from the precondition.

Unlike `DependsOn`, `Frameable` constrains the *computation*, not the assertion, so the
frame assertion is arbitrary: `eqPre` and `agreeOff`, which have no finite footprint and
so are outside the reach of `r_frame_local`, are framable here.

## Relation to the location-based frame rules of `CatCryptCore.Relational.Frame`

`r_frame_sep` does not subsume `r_frame_local`, `r_frame_of_preservesNothing` or
`r_frame_agreeOff`, and none of them subsumes it. Two independent obstructions separate
`∗` from the location-based family.

**The hypothesis on the computations.** All three location-based rules ask only for
`PreservesOutside`, a condition on *writes*. `Frameable` is a condition on writes and on
*reads*: the frame property fails as soon as a computation can observe a location outside
the heap it was given. `not_frameable_get` is the witness — `SPComp.get l` satisfies
`PreservesOutside (SPComp.get l) ∅`, the strongest hypothesis any of the three rules can
demand, and is not `Frameable (SPComp.get l) (fun _ => True)`. So the three rules apply to
computations for which `r_frame_sep` has no side condition to offer, at any choice of
frame assertion.

**The reading of the assertions.** `(P ∗ R) h₁ h₂` says `P` and `R` hold of *parts* of
`h₁` and `h₂`; `(P ⋀ R) h₁ h₂` says both hold of the wholes. Neither implies the other,
and a whole-heap precondition determines no split, so a location-based conclusion cannot
be re-derived by instantiating `∗` even where `Frameable` does hold.

In the other direction, `r_frame_set_sync_eqPre` frames whole-heap equality of the
untouched region across computations that write. `r_frame_local` cannot state that frame
(no finite footprint), `r_frame_of_preservesNothing` forbids the writes, and
`r_frame_agreeOff` frames only `agreeOff L`, not an arbitrary assertion on the untouched
region. `agreeOff_of_sepPost_eqPre` is the one-way reading of a `∗ᵖ` conclusion back as a
whole-heap `agreeOff` assertion.

The four rules therefore cover four points:

* `r_frame_local` — finite-footprint frame, writes confined away from it, reads free.
* `r_frame_of_preservesNothing` — arbitrary frame, no writes, reads free.
* `r_frame_agreeOff` — co-finite frame of the fixed shape `agreeOff L`, writes inside
  `L`, reads free.
* `r_frame_sep` — arbitrary frame, writes free, reads confined to the owned region.

## References

* Bluebell (POPL 2025) — `P * Q` separating conjunction for independence
* O'Hearn, Reynolds, Yang — Separation logic; locality = safety monotonicity + the frame
  property
-/

namespace CatCrypt.Relational

open CatCrypt.Core CatCrypt.Prob

variable {α β γ : Type*}

/-! ## Heap splitting -/

/-- Two heaps have no location in common. -/
def HeapDisj (h₁ h₂ : Heap) : Prop := Finmap.Disjoint h₁.data h₂.data

/-- Union of two heaps. Left-biased on the overlap, so it is the disjoint union
exactly when the arguments are `HeapDisj`. -/
def heapUnion (h₁ h₂ : Heap) : Heap := ⟨h₁.data ∪ h₂.data⟩

@[inherit_doc] scoped infixl:65 " ⊎ " => heapUnion

/-- `HeapSplit h h₁ h₂` : `h` is the disjoint union of `h₁` and `h₂`. -/
def HeapSplit (h h₁ h₂ : Heap) : Prop := HeapDisj h₁ h₂ ∧ h = h₁ ⊎ h₂

/-! ### Algebra of disjointness and union -/

theorem heapUnion_data (h₁ h₂ : Heap) : (h₁ ⊎ h₂).data = h₁.data ∪ h₂.data := rfl

theorem HeapDisj.symm {h₁ h₂ : Heap} (h : HeapDisj h₁ h₂) : HeapDisj h₂ h₁ :=
  Finmap.Disjoint.symm _ _ h

theorem heapDisj_empty_left (h : Heap) : HeapDisj Heap.empty h :=
  Finmap.disjoint_empty _

theorem heapDisj_empty_right (h : Heap) : HeapDisj h Heap.empty :=
  (heapDisj_empty_left h).symm

theorem heapDisj_union_left {h₁ h₂ h₃ : Heap} :
    HeapDisj (h₁ ⊎ h₂) h₃ ↔ HeapDisj h₁ h₃ ∧ HeapDisj h₂ h₃ :=
  Finmap.disjoint_union_left _ _ _

theorem heapDisj_union_right {h₁ h₂ h₃ : Heap} :
    HeapDisj h₁ (h₂ ⊎ h₃) ↔ HeapDisj h₁ h₂ ∧ HeapDisj h₁ h₃ :=
  Finmap.disjoint_union_right _ _ _

@[simp] theorem heapUnion_empty (h : Heap) : h ⊎ Heap.empty = h :=
  Heap.ext (by simp only [heapUnion_data, Heap.empty, Finmap.union_empty])

@[simp] theorem empty_heapUnion (h : Heap) : Heap.empty ⊎ h = h :=
  Heap.ext (by simp only [heapUnion_data, Heap.empty, Finmap.empty_union])

theorem heapUnion_assoc (h₁ h₂ h₃ : Heap) : (h₁ ⊎ h₂) ⊎ h₃ = h₁ ⊎ (h₂ ⊎ h₃) :=
  Heap.ext (by simp only [heapUnion_data, Finmap.union_assoc])

theorem heapUnion_comm {h₁ h₂ : Heap} (h : HeapDisj h₁ h₂) : h₁ ⊎ h₂ = h₂ ⊎ h₁ :=
  Heap.ext (Finmap.union_comm_of_disjoint h)

theorem lookup_heapUnion_left {h₁ h₂ : Heap} {id : Nat} (h : id ∈ h₁.data) :
    (h₁ ⊎ h₂).data.lookup id = h₁.data.lookup id :=
  Finmap.lookup_union_left h

theorem lookup_heapUnion_right {h₁ h₂ : Heap} {id : Nat} (h : id ∉ h₁.data) :
    (h₁ ⊎ h₂).data.lookup id = h₂.data.lookup id :=
  Finmap.lookup_union_right h

/-- The domain of a union is the union of the domains. -/
theorem mem_heapUnion {h₁ h₂ : Heap} {id : Nat} :
    id ∈ (h₁ ⊎ h₂).data ↔ id ∈ h₁.data ∨ id ∈ h₂.data :=
  Finmap.mem_union

/-! ### Algebra of splits -/

theorem HeapSplit.disj {h h₁ h₂ : Heap} (s : HeapSplit h h₁ h₂) : HeapDisj h₁ h₂ := s.1

theorem HeapSplit.eq {h h₁ h₂ : Heap} (s : HeapSplit h h₁ h₂) : h = h₁ ⊎ h₂ := s.2

/-- Splitting is symmetric. -/
theorem HeapSplit.comm {h h₁ h₂ : Heap} (s : HeapSplit h h₁ h₂) : HeapSplit h h₂ h₁ :=
  ⟨s.1.symm, s.2.trans (heapUnion_comm s.1)⟩

/-- The empty heap is a unit for splitting. -/
theorem HeapSplit.empty_right (h : Heap) : HeapSplit h h Heap.empty :=
  ⟨heapDisj_empty_right h, (heapUnion_empty h).symm⟩

theorem HeapSplit.empty_left (h : Heap) : HeapSplit h Heap.empty h :=
  (HeapSplit.empty_right h).comm

/-- A split whose right part splits again regroups to the left. -/
theorem HeapSplit.assocL {h h₁ h₂ h₃ k : Heap}
    (s : HeapSplit h h₁ k) (t : HeapSplit k h₂ h₃) :
    HeapSplit h (h₁ ⊎ h₂) h₃ ∧ HeapSplit (h₁ ⊎ h₂) h₁ h₂ := by
  obtain ⟨hd, he⟩ := s
  obtain ⟨td, te⟩ := t
  subst te
  have h12 : HeapDisj h₁ h₂ := (heapDisj_union_right.mp hd).1
  have h13 : HeapDisj h₁ h₃ := (heapDisj_union_right.mp hd).2
  refine ⟨⟨heapDisj_union_left.mpr ⟨h13, td⟩, ?_⟩, ⟨h12, rfl⟩⟩
  rw [heapUnion_assoc]
  exact he

/-- A split whose left part splits again regroups to the right. -/
theorem HeapSplit.assocR {h h₁ h₂ h₃ k : Heap}
    (s : HeapSplit h k h₃) (t : HeapSplit k h₁ h₂) :
    HeapSplit h h₁ (h₂ ⊎ h₃) ∧ HeapSplit (h₂ ⊎ h₃) h₂ h₃ := by
  obtain ⟨hd, he⟩ := s
  obtain ⟨td, te⟩ := t
  subst te
  have h13 : HeapDisj h₁ h₃ := (heapDisj_union_left.mp hd).1
  have h23 : HeapDisj h₂ h₃ := (heapDisj_union_left.mp hd).2
  refine ⟨⟨heapDisj_union_right.mpr ⟨td, h13⟩, ?_⟩, ⟨h23, rfl⟩⟩
  rw [← heapUnion_assoc]
  exact he

/-! ## Separating conjunction -/

/-- Separating conjunction of relational preconditions: each of the two heaps splits,
and `P` relates the two left parts while `Q` relates the two right parts. The splits
on the two sides are independent. -/
def sepPre (P Q : RPre) : RPre := fun h₁ h₂ =>
  ∃ a₁ b₁ a₂ b₂, HeapSplit h₁ a₁ b₁ ∧ HeapSplit h₂ a₂ b₂ ∧ P a₁ a₂ ∧ Q b₁ b₂

@[inherit_doc] scoped infixl:64 " ∗ " => sepPre

/-- Separating conjunction of a relational postcondition with a frame assertion:
the postcondition constrains the parts the computations ran on, the frame the parts
they did not. -/
def sepPost (Ψ : RPost α β) (R : RPre) : RPost α β := fun a h₁ b h₂ =>
  ∃ a₁ b₁ a₂ b₂, HeapSplit h₁ a₁ b₁ ∧ HeapSplit h₂ a₂ b₂ ∧ Ψ a a₁ b a₂ ∧ R b₁ b₂

@[inherit_doc] scoped infixl:64 " ∗ᵖ " => sepPost

/-- The assertion of the pair of empty heaps: the unit of `∗`. -/
def emp : RPre := fun h₁ h₂ => h₁ = Heap.empty ∧ h₂ = Heap.empty

/-! ### Algebra of `∗` -/

/-- Introduction rule for `∗`: exhibit the two splits. -/
theorem sepPre_of_split {P Q : RPre} {h₁ h₂ a₁ b₁ a₂ b₂ : Heap}
    (s₁ : HeapSplit h₁ a₁ b₁) (s₂ : HeapSplit h₂ a₂ b₂)
    (hP : P a₁ a₂) (hQ : Q b₁ b₂) : (P ∗ Q) h₁ h₂ :=
  ⟨a₁, b₁, a₂, b₂, s₁, s₂, hP, hQ⟩

theorem sepPre_comm (P Q : RPre) (h₁ h₂ : Heap) : (P ∗ Q) h₁ h₂ ↔ (Q ∗ P) h₁ h₂ := by
  constructor <;>
  · rintro ⟨a₁, b₁, a₂, b₂, s₁, s₂, hP, hQ⟩
    exact ⟨b₁, a₁, b₂, a₂, s₁.comm, s₂.comm, hQ, hP⟩

theorem sepPre_assoc (P Q S : RPre) (h₁ h₂ : Heap) :
    ((P ∗ Q) ∗ S) h₁ h₂ ↔ (P ∗ (Q ∗ S)) h₁ h₂ := by
  constructor
  · rintro ⟨c₁, s₁, c₂, s₂, t₁, t₂, ⟨a₁, b₁, a₂, b₂, u₁, u₂, hP, hQ⟩, hS⟩
    obtain ⟨v₁, w₁⟩ := HeapSplit.assocR t₁ u₁
    obtain ⟨v₂, w₂⟩ := HeapSplit.assocR t₂ u₂
    exact ⟨a₁, b₁ ⊎ s₁, a₂, b₂ ⊎ s₂, v₁, v₂, hP, b₁, s₁, b₂, s₂, w₁, w₂, hQ, hS⟩
  · rintro ⟨a₁, k₁, a₂, k₂, t₁, t₂, hP, b₁, s₁, b₂, s₂, u₁, u₂, hQ, hS⟩
    obtain ⟨v₁, w₁⟩ := HeapSplit.assocL t₁ u₁
    obtain ⟨v₂, w₂⟩ := HeapSplit.assocL t₂ u₂
    exact ⟨a₁ ⊎ b₁, s₁, a₂ ⊎ b₂, s₂, v₁, v₂, ⟨a₁, b₁, a₂, b₂, w₁, w₂, hP, hQ⟩, hS⟩

theorem sepPre_mono {P P' Q Q' : RPre}
    (hP : ∀ k₁ k₂, P k₁ k₂ → P' k₁ k₂) (hQ : ∀ k₁ k₂, Q k₁ k₂ → Q' k₁ k₂)
    {h₁ h₂ : Heap} (h : (P ∗ Q) h₁ h₂) : (P' ∗ Q') h₁ h₂ := by
  obtain ⟨a₁, b₁, a₂, b₂, s₁, s₂, hp, hq⟩ := h
  exact ⟨a₁, b₁, a₂, b₂, s₁, s₂, hP a₁ a₂ hp, hQ b₁ b₂ hq⟩

theorem sepPre_emp (P : RPre) (h₁ h₂ : Heap) : (P ∗ emp) h₁ h₂ ↔ P h₁ h₂ := by
  constructor
  · rintro ⟨a₁, b₁, a₂, b₂, ⟨_, e₁⟩, ⟨_, e₂⟩, hP, hb₁, hb₂⟩
    subst hb₁; subst hb₂
    rw [heapUnion_empty] at e₁ e₂
    exact e₁ ▸ e₂ ▸ hP
  · intro hP
    exact ⟨h₁, Heap.empty, h₂, Heap.empty, HeapSplit.empty_right h₁,
      HeapSplit.empty_right h₂, hP, rfl, rfl⟩

theorem emp_sepPre (P : RPre) (h₁ h₂ : Heap) : (emp ∗ P) h₁ h₂ ↔ P h₁ h₂ :=
  (sepPre_comm emp P h₁ h₂).trans (sepPre_emp P h₁ h₂)

theorem sepPost_mono {Ψ Ψ' : RPost α β} {R R' : RPre}
    (hΨ : ∀ a k₁ b k₂, Ψ a k₁ b k₂ → Ψ' a k₁ b k₂)
    (hR : ∀ k₁ k₂, R k₁ k₂ → R' k₁ k₂)
    {a : α} {b : β} {h₁ h₂ : Heap} (h : (Ψ ∗ᵖ R) a h₁ b h₂) : (Ψ' ∗ᵖ R') a h₁ b h₂ := by
  obtain ⟨a₁, b₁, a₂, b₂, s₁, s₂, hp, hq⟩ := h
  exact ⟨a₁, b₁, a₂, b₂, s₁, s₂, hΨ a a₁ b a₂ hp, hR b₁ b₂ hq⟩

/-! ## Locality of computations -/

/-- Separation-logic locality of `c`, relative to the heaps satisfying `D`.

`frame` is the frame property: extending the heap by a disjoint `hf` extends every
outcome by the same `hf`, with the same probabilities. `confined` says `c` allocates
no location it was not given, which is what keeps the extension disjoint. -/
structure Frameable (c : SPComp α) (D : Heap → Prop) : Prop where
  /-- Running on an extended heap is running on the small heap and re-attaching. -/
  frame : ∀ h hf, D h → HeapDisj h hf →
    c (h ⊎ hf) = (c h).bind fun p => SDistr.pure (p.1, p.2 ⊎ hf)
  /-- Outcomes stay inside the domain of the initial heap. -/
  confined : ∀ h a h', D h → (c h) (some (a, h')) ≠ 0 → ∀ id, id ∈ h'.data → id ∈ h.data

/-- Confinement turns disjointness of the initial heap from a frame into disjointness
of every outcome from that frame. -/
theorem Frameable.disj_of_support {c : SPComp α} {D : Heap → Prop} (hc : Frameable c D)
    {h hf h' : Heap} {a : α} (hD : D h) (hdisj : HeapDisj h hf)
    (hsupp : (c h) (some (a, h')) ≠ 0) : HeapDisj h' hf :=
  fun id hid => hdisj id (hc.confined h a h' hD hsupp id hid)

/-! ### Support extraction -/

/-- A nonzero outcome of a bind comes from a nonzero outcome of each stage. -/
theorem exists_of_bind_ne_zero {d : SDistr γ} {g : γ → SDistr β} {x : β}
    (hne : (d.bind g) (some x) ≠ 0) : ∃ y, d (some y) ≠ 0 ∧ (g y) (some x) ≠ 0 := by
  by_contra hcon
  apply hne
  simp only [SDistr.bind, PMF.bind_apply]
  rw [ENNReal.tsum_eq_zero]
  intro oy
  cases oy with
  | none => simp only [SDistr.fail_apply_some, mul_zero]
  | some y =>
    by_cases hd : d (some y) = 0
    · simp only [hd, zero_mul]
    · by_cases hg : (g y) (some x) = 0
      · simp only [hg, mul_zero]
      · exact absurd ⟨y, hd, hg⟩ hcon

/-- A heap-independent computation leaves the heap alone on its support. -/
theorem heap_eq_of_liftSDistr_support {d : SDistr γ} {h h' : Heap} {a : γ}
    (hne : (d.bind fun x => SDistr.pure (x, h)) (some (a, h')) ≠ 0) : h' = h := by
  obtain ⟨y, _, hy⟩ := exists_of_bind_ne_zero hne
  have heq : (y, h) = (a, h') := (SDistr.mem_support_pure_iff (y, h) (a, h')).mp hy
  exact (congrArg Prod.snd heq).symm

/-! ### Frameable instances -/

/-- Every heap-independent computation is local, with no constraint on the heap. -/
theorem frameable_of_isPure {c : SPComp α} (hc : SPComp.IsPure c) :
    Frameable c (fun _ => True) := by
  obtain ⟨d, hd⟩ := hc
  constructor
  · intro h hf _ _
    rw [hd (h ⊎ hf), hd h, SDistr.bind_assoc]
    exact congrArg d.bind (funext fun x => by rw [SDistr.pure_bind])
  · intro h a h' _ hsupp id hid
    rw [hd h] at hsupp
    exact heap_eq_of_liftSDistr_support hsupp ▸ hid

theorem frameable_pure (a : α) : Frameable (SPComp.pure a) (fun _ => True) :=
  frameable_of_isPure (SPComp.pure_isPure a)

theorem frameable_sample (α : Type) [Fintype α] [Nonempty α] :
    Frameable (SPComp.sample α) (fun _ => True) :=
  frameable_of_isPure (SPComp.sample_isPure α)

theorem frameable_fail : Frameable (SPComp.fail : SPComp α) (fun _ => True) :=
  frameable_of_isPure SPComp.fail_isPure

/-- The heaps that own location `l`: the domain predicate of `get l` and `set l v`. -/
def Owns (l : Location) : Heap → Prop := fun h => l.id ∈ h.data

/-- Reading a location is local on the heaps that own it. Ownership is needed: on a
heap without `l` the read would see the frame's value instead of `default`. -/
theorem frameable_get (l : Location) : Frameable (SPComp.get l) (Owns l) := by
  constructor
  · intro h hf hD _
    have hlook : (h ⊎ hf).data.lookup l.id = h.data.lookup l.id := lookup_heapUnion_left hD
    have : (h ⊎ hf).get l = h.get l := by simp only [Heap.get, hlook]
    rw [SPComp.get_def, SPComp.get_def, this, SDistr.pure_bind]
  · intro h a h' _ hsupp id hid
    rw [SPComp.get_def] at hsupp
    have heq : (h.get l, h) = (a, h') := (SDistr.mem_support_pure_iff _ _).mp hsupp
    have hh' : h' = h := (congrArg Prod.snd heq).symm
    exact hh' ▸ hid

/-- Reading a location is not local at an arbitrary heap. `SPComp.get l` writes nothing,
so `PreservesOutside (SPComp.get l) ∅` holds, yet the frame property fails on a heap that
does not own `l` together with a frame that does: the read sees the frame's value. The
witness needs a location type with a non-default element. -/
theorem not_frameable_get (l : Location) (v : l.ty) (hv : v ≠ default) :
    ¬ Frameable (SPComp.get l) (fun _ => True) := by
  intro hc
  set hf : Heap := ⟨Finmap.singleton l.id (Heap.encode v)⟩ with hhf
  have hfr := hc.frame Heap.empty hf trivial (heapDisj_empty_left hf)
  simp only [SPComp.get_def, SDistr.pure_bind, empty_heapUnion] at hfr
  have hget : hf.get l = v := by
    simp only [hhf, Heap.get, Finmap.lookup_singleton_eq, Heap.decode_encode]
  have hdef : (Heap.empty : Heap).get l = default := Heap.get_empty l
  rw [hget, hdef] at hfr
  have hmem : (v, hf) ∈ (SDistr.pure ((default : l.ty), hf)).support := by
    rw [← hfr]; exact (SDistr.mem_support_pure_iff _ _).mpr rfl
  exact hv (congrArg Prod.fst ((SDistr.mem_support_pure_iff _ _).mp hmem)).symm

/-- Writing a location is local on the heaps that own it. Ownership is needed for
confinement: writing to an unowned location allocates it, and could collide with the
frame. -/
theorem frameable_set (l : Location) (v : l.ty) : Frameable (SPComp.set l v) (Owns l) := by
  constructor
  · intro h hf _ _
    rw [SPComp.set_def, SPComp.set_def, SDistr.pure_bind]
    congr 1
    exact congrArg _ (Heap.ext (Finmap.insert_union))
  · intro h a h' hD hsupp id hid
    rw [SPComp.set_def] at hsupp
    have : ((), h.set l v) = (a, h') := (SDistr.mem_support_pure_iff _ _).mp hsupp
    have hh' : h' = h.set l v := (congrArg Prod.snd this).symm
    rw [hh'] at hid
    rcases Finmap.mem_insert.mp hid with hid' | hid'
    · exact hid' ▸ hD
    · exact hid'

/-- Locality composes through bind, provided the first stage lands in the domain
predicate of the second. -/
theorem Frameable.bind {c : SPComp α} {f : α → SPComp β} {D D' : Heap → Prop}
    (hc : Frameable c D) (hf : ∀ a, Frameable (f a) D')
    (hstep : ∀ h a h', D h → (c h) (some (a, h')) ≠ 0 → D' h') :
    Frameable (SPComp.bind c f) D := by
  constructor
  · intro h hframe hD hdisj
    show (c (h ⊎ hframe)).bind _ = ((c h).bind _).bind _
    rw [hc.frame h hframe hD hdisj, SDistr.bind_assoc, SDistr.bind_assoc]
    refine SDistr.bind_congr_support fun p hp => ?_
    rw [SDistr.pure_bind]
    exact (hf p.1).frame p.2 hframe (hstep h p.1 p.2 hD hp)
      (hc.disj_of_support hD hdisj hp)
  · intro h a h' hD hsupp id hid
    obtain ⟨q, hq, hq'⟩ := exists_of_bind_ne_zero hsupp
    exact hc.confined h q.1 q.2 hD hq id
      ((hf q.1).confined q.2 a h' (hstep h q.1 q.2 hD hq) hq' id hid)

/-! ## The frame rule -/

/-- The frame rule for the relational separating conjunction.

The frame assertion `R` is arbitrary — no footprint condition. What is required is
that the two computations are local (`Frameable`) on the heaps their precondition
describes, which is the semantic content of separation logic's "the triple only talks
about the heap it owns". -/
theorem r_frame_sep {Φ : RPre} {Ψ : RPost α β} {R : RPre}
    {c₁ : SPComp α} {c₂ : SPComp β} {D₁ D₂ : Heap → Prop}
    (hL₁ : Frameable c₁ D₁) (hL₂ : Frameable c₂ D₂)
    (hD₁ : ∀ k₁ k₂, Φ k₁ k₂ → D₁ k₁) (hD₂ : ∀ k₁ k₂, Φ k₁ k₂ → D₂ k₂)
    (hInner : rHoare Φ c₁ c₂ Ψ) :
    rHoare (Φ ∗ R) c₁ c₂ (Ψ ∗ᵖ R) := by
  rintro h₁ h₂ ⟨a₁, b₁, a₂, b₂, ⟨hd₁, he₁⟩, ⟨hd₂, he₂⟩, hΦ, hR⟩
  subst he₁; subst he₂
  have hown₁ : D₁ a₁ := hD₁ a₁ a₂ hΦ
  have hown₂ : D₂ a₂ := hD₂ a₁ a₂ hΦ
  obtain ⟨κ, hκ⟩ := hInner a₁ a₂ hΦ
  -- Strengthen the inner lifting with the disjointness that confinement supplies.
  have hstr : liftR
      (fun (p : α × Heap) (q : β × Heap) =>
        Ψ p.1 p.2 q.1 q.2 ∧ HeapDisj p.2 b₁ ∧ HeapDisj q.2 b₂)
      (c₁ a₁) (c₂ a₂) := by
    refine ⟨κ, fun p q hj => ⟨hκ p q hj, ?_, ?_⟩⟩
    · exact hL₁.disj_of_support hown₁ hd₁ (κ.in_left_support hj)
    · exact hL₂.disj_of_support hown₂ hd₂ (κ.in_right_support hj)
  rw [hL₁.frame a₁ b₁ hown₁ hd₁, hL₂.frame a₂ b₂ hown₂ hd₂]
  refine liftR_bind hstr fun p q hpq => liftR_pure ?_
  exact ⟨p.2, b₁, q.2, b₂, ⟨hpq.2.1, rfl⟩, ⟨hpq.2.2, rfl⟩, hpq.1, hR⟩

/-! ## Framing assertions with no finite footprint -/

/-- Whole-heap equality is framable. `r_frame_local` cannot frame it: `DependsOn`
requires a `LocSet`, which is finite, and `eqPre` constrains every location. -/
theorem r_frame_sep_eqPre {Φ : RPre} {Ψ : RPost α β}
    {c₁ : SPComp α} {c₂ : SPComp β} {D₁ D₂ : Heap → Prop}
    (hL₁ : Frameable c₁ D₁) (hL₂ : Frameable c₂ D₂)
    (hD₁ : ∀ k₁ k₂, Φ k₁ k₂ → D₁ k₁) (hD₂ : ∀ k₁ k₂, Φ k₁ k₂ → D₂ k₂)
    (hInner : rHoare Φ c₁ c₂ Ψ) :
    rHoare (Φ ∗ eqPre) c₁ c₂ (Ψ ∗ᵖ eqPre) :=
  r_frame_sep hL₁ hL₂ hD₁ hD₂ hInner

/-- Agreement outside a finite set is framable. Its footprint is co-finite, so it too
is out of reach of `r_frame_local`. -/
theorem r_frame_sep_agreeOff {Φ : RPre} {Ψ : RPost α β} {L : LocSet}
    {c₁ : SPComp α} {c₂ : SPComp β} {D₁ D₂ : Heap → Prop}
    (hL₁ : Frameable c₁ D₁) (hL₂ : Frameable c₂ D₂)
    (hD₁ : ∀ k₁ k₂, Φ k₁ k₂ → D₁ k₁) (hD₂ : ∀ k₁ k₂, Φ k₁ k₂ → D₂ k₂)
    (hInner : rHoare Φ c₁ c₂ Ψ) :
    rHoare (Φ ∗ agreeOff L) c₁ c₂ (Ψ ∗ᵖ agreeOff L) :=
  r_frame_sep hL₁ hL₂ hD₁ hD₂ hInner

/-! ### A worked instance -/

/-- Writing the same value to the same owned location on both sides keeps the two heaps
equal. The precondition carries the ownership of `l` that `frameable_set` needs. -/
theorem rHoare_set_sync_owned (l : Location) (v : l.ty) :
    rHoare (fun h₁ h₂ => h₁ = h₂ ∧ Owns l h₁) (SPComp.set l v) (SPComp.set l v)
      (fun _ h₁ _ h₂ => h₁ = h₂) := by
  rintro h₁ h₂ ⟨rfl, _⟩
  rw [SPComp.set_def]
  exact liftR_pure rfl

/-- The synchronised write, framed by an arbitrary assertion on the rest of the heap. -/
theorem r_frame_set_sync (l : Location) (v : l.ty) (R : RPre) :
    rHoare ((fun h₁ h₂ => h₁ = h₂ ∧ Owns l h₁) ∗ R) (SPComp.set l v) (SPComp.set l v)
      ((fun _ h₁ _ h₂ => h₁ = h₂) ∗ᵖ R) :=
  r_frame_sep (frameable_set l v) (frameable_set l v)
    (fun _ _ h => h.2) (fun _ _ h => h.1 ▸ h.2) (rHoare_set_sync_owned l v)

/-- The synchronised write framed by whole-heap equality of the untouched region: the
frame assertion here has no finite footprint, so `r_frame_local` does not apply to it. -/
theorem r_frame_set_sync_eqPre (l : Location) (v : l.ty) :
    rHoare ((fun h₁ h₂ => h₁ = h₂ ∧ Owns l h₁) ∗ eqPre) (SPComp.set l v) (SPComp.set l v)
      ((fun _ h₁ _ h₂ => h₁ = h₂) ∗ᵖ eqPre) :=
  r_frame_set_sync l v eqPre

/-- Framing whole-heap equality yields agreement outside the region the computations
ran on: the untouched parts are literally the same heap, so the final heaps can differ
only inside the two owned domains, which are finite. -/
theorem agreeOff_of_sepPost_eqPre {Ψ : RPost α β} {a : α} {b : β} {h₁ h₂ : Heap}
    (h : (Ψ ∗ᵖ eqPre) a h₁ b h₂) : ∃ L : LocSet, agreeOff L h₁ h₂ := by
  obtain ⟨a₁, b₁, a₂, b₂, ⟨_, e₁⟩, ⟨_, e₂⟩, _, hfr⟩ := h
  refine ⟨a₁.data.keys ∪ a₂.data.keys, fun id hid => ?_⟩
  have hn₁ : id ∉ a₁.data := fun hm =>
    hid (Finset.mem_union_left _ (Finmap.mem_keys.mpr hm))
  have hn₂ : id ∉ a₂.data := fun hm =>
    hid (Finset.mem_union_right _ (Finmap.mem_keys.mpr hm))
  rw [e₁, e₂, lookup_heapUnion_right hn₁, lookup_heapUnion_right hn₂, hfr]

end CatCrypt.Relational
