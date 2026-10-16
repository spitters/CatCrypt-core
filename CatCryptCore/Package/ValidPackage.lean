/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Package.RawPackage
public import CatCryptCore.Package.Locations
public import CatCryptCore.Prob.Support

/-!
# Valid Packages

This file defines valid packages - raw packages with proofs that they correctly
implement their interface and only access declared locations.

## Main definitions

* `ValidCode` - A computation whose heap accesses are at locations in L
* `ValidPackage` - A package that correctly implements interface E using imports from I
* `fseparate` - Two packages have disjoint locations

## References

* [Larsen and Schürmann, *Nominal State-Separating Proofs*](https://eprint.iacr.org/2025/598)
-/

@[expose] public section

namespace CatCrypt.Package

open CatCrypt.Core
open CatCrypt.Prob

/-- Specification of location access in code.
    A full implementation would track this syntactically;
    this uses a semantic characterization. -/
structure LocAccess where
  /-- Locations that may be read -/
  reads : Locations
  /-- Locations that may be written -/
  writes : Locations

/-- Code validity: the code accesses the heap only at locations in `L`.

    `frame`: overwriting a location `l ∉ L` with any value `v` before running the
    code has the same effect as overwriting `l` with `v` in every final heap.
    Hence neither the return value nor any final heap value at another location
    depends on the value at `l`; in particular the code cannot copy the value at a
    location outside `L` into a location inside `L`.

    `writes_in_L`: every final heap in the support has the initial value at each
    location `l ∉ L`.

    An `SPComp` is a function on heaps and has no syntax, so both conditions are
    stated on the semantics. A `SPComp` has no imported calls, so the predicate has
    no import interface. -/
class ValidCode (L : Locations) (α : Type*) (c : SPComp α) : Prop where
  /-- Running the code commutes with overwriting a location outside `L` -/
  frame : ∀ l v h, l ∉ L →
    c (Heap.set h l v) = (c h).bind (fun p => SDistr.pure (p.1, Heap.set p.2 l v))
  /-- The code leaves every location outside `L` unchanged -/
  writes_in_L : ∀ l h, l ∉ L → ∀ p, (c h) (some p) ≠ 0 → p.2.get l = h.get l

namespace ValidCode

variable {L : Locations}

/-- The return-value distribution does not depend on locations outside `L`. -/
theorem reads_in_L {α : Type*} {c : SPComp α} (hc : ValidCode L α c) (l : Location) (v : l.ty)
    (h : Heap) (hl : l ∉ L) :
    (c h).bind (fun (a, _) => SDistr.pure a) =
    (c (Heap.set h l v)).bind (fun (a, _) => SDistr.pure a) := by
  rw [hc.frame l v h hl, SDistr.bind_assoc]
  simp only [SDistr.pure_bind]

instance pure {α : Type*} (a : α) : ValidCode L α (SPComp.pure a) where
  frame l v h _ := by simp only [SPComp.pure, SDistr.pure_bind]
  writes_in_L l h _ p hp := by
    have := (SDistr.mem_support_pure_iff (a, h) p).1 hp
    rw [← this]

instance fail {α : Type*} : ValidCode L α SPComp.fail where
  frame l v h _ := by simp only [SPComp.fail, SDistr.bind_fail]
  writes_in_L l h _ p hp := absurd (SDistr.fail_apply_some p) hp

instance sample (α : Type) [Fintype α] [Nonempty α] : ValidCode L α (SPComp.sample α) where
  frame l v h _ := by
    simp only [SPComp.sample, SDistr.bind_assoc, SDistr.pure_bind]
  writes_in_L l h _ p hp := by
    obtain ⟨a, _, hpa⟩ := SDistr.bind_support_witness hp
    have := (SDistr.mem_support_pure_iff (a, h) p).1 hpa
    rw [← this]

theorem get (l₀ : Location) (h₀ : l₀ ∈ L) : ValidCode L l₀.ty (SPComp.get l₀) where
  frame l v h hl := by
    have hne : l.id ≠ l₀.id := fun e => hl (by rw [Locations.mem_iff, e]; exact h₀)
    simp only [SPComp.get, SDistr.pure_bind, Heap.get_set_other _ _ _ _ hne]
  writes_in_L l h _ p hp := by
    have := (SDistr.mem_support_pure_iff (h.get l₀, h) p).1 hp
    rw [← this]

theorem set (l₀ : Location) (w : l₀.ty) (h₀ : l₀ ∈ L) : ValidCode L Unit (SPComp.set l₀ w) where
  frame l v h hl := by
    have hne : l.id ≠ l₀.id := fun e => hl (by rw [Locations.mem_iff, e]; exact h₀)
    simp only [SPComp.set, SDistr.pure_bind, Heap.set_set_comm _ _ _ _ _ hne]
  writes_in_L l h hl p hp := by
    have hne : l₀.id ≠ l.id := fun e => hl (by rw [Locations.mem_iff, ← e]; exact h₀)
    have := (SDistr.mem_support_pure_iff ((), h.set l₀ w) p).1 hp
    rw [← this, Heap.get_set_other _ _ _ _ hne]

instance bind {α β : Type*} (c : SPComp α) (f : α → SPComp β) [hc : ValidCode L α c]
    [hf : ∀ a, ValidCode L β (f a)] : ValidCode L β (SPComp.bind c f) where
  frame l v h hl := by
    simp only [SPComp.bind, hc.frame l v h hl, SDistr.bind_assoc, SDistr.pure_bind]
    congr 1
    funext p
    exact (hf p.1).frame l v p.2 hl
  writes_in_L l h hl p hp := by
    obtain ⟨q, hq, hpq⟩ := SDistr.bind_support_witness hp
    rw [(hf q.1).writes_in_L l q.2 hl p hpq, hc.writes_in_L l h hl q hq]

end ValidCode

/-- A valid package correctly implements an export interface using an import interface.
    - L: the locations the package may access
    - I: the interface the package may import
    - E: the interface the package exports -/
structure ValidPackage (L : Locations) (I E : Interface) (P : RawPackage) : Prop where
  /-- The package implements all operations in E -/
  exports_complete : ∀ id S T, E.has id S T → P.has id S T
  /-- The package only implements operations in E -/
  exports_only : ∀ id S T, P.has id S T → E.has id S T
  /-- All implementations are valid code -/
  valid_impl : ∀ e ∈ P.entries, ∀ x : e.fun_.src,
                 ValidCode L e.fun_.tgt (e.fun_.impl x)

/-- Two packages have separate (disjoint) locations -/
def fseparate (L₁ L₂ : Locations) : Prop :=
  Locations.Separate L₁ L₂

namespace ValidPackage

/-- Valid code for a smaller location set is valid for a larger one.
    This is mathematically sound: if code only accesses L₁, and L₁ ⊆ L₂,
    then the code trivially satisfies validity for L₂. -/
theorem validCode_weaken {L₁ L₂ : Locations} {α : Type*} {c : SPComp α}
    (hL : L₁ ⊆ L₂)
    (hv : ValidCode L₁ α c) :
    ValidCode L₂ α c where
  frame := fun l v h hl =>
    -- If l ∉ L₂ and L₁ ⊆ L₂, then l ∉ L₁
    have hl₁ : l ∉ L₁ := fun h => hl (hL h)
    hv.frame l v h hl₁
  writes_in_L := fun l h hl =>
    have hl₁ : l ∉ L₁ := fun h => hl (hL h)
    hv.writes_in_L l h hl₁

/-- Empty package is valid for empty interface -/
theorem empty_valid (I : Interface) : ValidPackage ∅ I ∅ (∅ : RawPackage) where
  exports_complete := fun id S T h => (Interface.empty_not_has id S T h).elim
  exports_only := fun id S T h => (RawPackage.empty_not_has id S T h).elim
  valid_impl := fun e h => (Finset.notMem_empty _ h).elim

/-- Parallel composition of valid packages -/
theorem par_valid {L₁ L₂ : Locations} {I₁ I₂ E₁ E₂ : Interface}
    {P₁ P₂ : RawPackage}
    (h₁ : ValidPackage L₁ I₁ E₁ P₁) (h₂ : ValidPackage L₂ I₂ E₂ P₂)
    (hL : Locations.Separate L₁ L₂)
    (hI : Interface.Disjoint I₁ I₂)
    (hP : RawPackage.Disjoint P₁ P₂)
    (hE : Interface.Disjoint E₁ E₂) :
    ValidPackage (Locations.union L₁ L₂ hL) (Interface.union I₁ I₂ hI)
                 (Interface.union E₁ E₂ hE) (RawPackage.par P₁ P₂ hP) := by
  constructor
  · intro id S T hE'
    simp only [Interface.union, Interface.has, Finset.mem_union] at hE'
    obtain ⟨e, he, hid, hsig⟩ := hE'
    cases he with
    | inl he₁ =>
      obtain ⟨pe, hpe, hpid, hpS, hpT⟩ := h₁.exports_complete id S T ⟨e, he₁, hid, hsig⟩
      simp only [RawPackage.par, RawPackage.has, Finset.mem_union] at *
      exact ⟨pe, Or.inl hpe, hpid, hpS, hpT⟩
    | inr he₂ =>
      obtain ⟨pe, hpe, hpid, hpS, hpT⟩ := h₂.exports_complete id S T ⟨e, he₂, hid, hsig⟩
      simp only [RawPackage.par, RawPackage.has, Finset.mem_union] at *
      exact ⟨pe, Or.inr hpe, hpid, hpS, hpT⟩
  · intro id S T hP'
    simp only [RawPackage.par, RawPackage.has, Finset.mem_union] at hP'
    obtain ⟨pe, hpe, hpid, hpS, hpT⟩ := hP'
    cases hpe with
    | inl hpe₁ => exact Interface.union_has_left hE id S T (h₁.exports_only id S T ⟨pe, hpe₁, hpid, hpS, hpT⟩)
    | inr hpe₂ => exact Interface.union_has_right hE id S T (h₂.exports_only id S T ⟨pe, hpe₂, hpid, hpS, hpT⟩)
  · -- valid_impl
    intro e he x
    simp only [RawPackage.par, Finset.mem_union] at he
    cases he with
    | inl he₁ => exact validCode_weaken (fun id hid => by
        rw [Locations.union_ids]; exact Finset.mem_union_left _ hid) (h₁.valid_impl e he₁ x)
    | inr he₂ => exact validCode_weaken (fun id hid => by
        rw [Locations.union_ids]; exact Finset.mem_union_right _ hid) (h₂.valid_impl e he₂ x)

/-- Location tracking: get the locations from a ValidPackage -/
def locs (L : Locations) (_I _E : Interface) (_P : RawPackage)
    (_ : ValidPackage L _I _E _P) : Locations := L

end ValidPackage

/-- The game import interface (empty for basic games) -/
def Game_import : Interface := Interface.empty

/-- The adversary export interface (empty for basic adversaries) -/
def A_export : Interface := Interface.empty

end CatCrypt.Package
