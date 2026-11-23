/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Bridges.IrisBridge.HeapAlgebra

/-!
# Embedding heap predicates into iris-lean's Classical BI

The full-ownership embedding `⌈P⌉` of a heap predicate
`P : Heap → Prop` holds at exactly the iris states that are images of heaps
satisfying `P`. It is a homomorphism for separating conjunction
(`embed_hSep`): disjoint Finmap splitting of heaps corresponds exactly
to disjoint splitting of iris states.

A typed points-to `ℓ ↦ₜ v` is also defined directly on iris states (the
state owns `ℓ.id` with the `Fintype` encoding of `v`). Its notation `↦ₜ` is
scoped; `Iris.Instances.Classical.Notation`, which declares a global `↦`
term syntax, is not imported.

## Encoding

Heaps store `Fintype`-encoded values (`Heap.encode : α → Nat`),
so iris states own *encodings*, not typed values. `ℓ ↦ₜ v` asserts ownership
of `ℓ.id` at the encoding of `v : ℓ.ty`; reading back through `Heap.get`
decodes it (`Heap.decode_encode`). Two locations of different types can
carry equal encodings — points-to is type-directed through `Location.ty`,
matching `Heap.get`'s decode-or-default semantics.
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.IrisBridge

open CatCrypt.Core
open Iris.Instances.Data
open HeapAlgebra

/-! ## The full-ownership embedding -/

/-- Full-ownership embedding of a CatCrypt heap predicate: `⌈P⌉` holds at
exactly the heap images of `P`-heaps. -/
def embed (P : Heap → Prop) : HProp :=
  fun σ => ∃ h : Heap, P h ∧ σ = h.toIState

@[inherit_doc] scoped notation "⌈" P "⌉" => embed P

theorem embed_intro {P : Heap → Prop} {h : Heap} (hP : P h) :
    (⌈P⌉) h.toIState :=
  ⟨h, hP, rfl⟩

theorem embed_mono {P Q : Heap → Prop} (h : ∀ h', P h' → Q h') :
    (⌈P⌉ : HProp) ⊢ ⌈Q⌉ := by
  rintro σ ⟨h', hP, rfl⟩
  exact ⟨h', h h' hP, rfl⟩

/-- The embedding is a homomorphism for separating conjunction: CatCrypt's
disjoint-Finmap `⋆` maps exactly to iris's disjoint-state `∗`. -/
theorem embed_hSep (P Q : Heap → Prop) :
    (⌈P ⋆ Q⌉ : HProp) ⊣⊢ ⌈P⌉ ∗ ⌈Q⌉ := by
  constructor
  · rintro σ ⟨h, ⟨h₁, h₂, hd, rfl, hP, hQ⟩, rfl⟩
    exact ⟨h₁.toIState, h₂.toIState, (toIState_union hd).symm ▸ rfl,
      toIState_disjoint_iff.mpr hd, embed_intro hP, embed_intro hQ⟩
  · rintro σ ⟨σ₁, σ₂, hσ, hd, ⟨h₁, hP, rfl⟩, ⟨h₂, hQ, rfl⟩⟩
    have hdisj : h₁.disj h₂ := toIState_disjoint_iff.mp hd
    refine ⟨h₁.union h₂, hSep_intro hdisj hP hQ, ?_⟩
    rw [hσ, toIState_union hdisj]

/-! ## Typed points-to on iris states -/

/-- Typed points-to: the iris state owns location `ℓ.id` carrying the
encoding of `v : ℓ.ty`. Junk-tolerant (the state may own more); `∗` supplies
disjointness where it matters. -/
def ptsTo (ℓ : Location) (v : ℓ.ty) : HProp :=
  fun σ => σ ℓ.id = .result (Heap.encode v)

@[inherit_doc] scoped notation:50 ℓ:51 " ↦ₜ " v:51 => ptsTo ℓ v

/-- Ownership of `ℓ.id` at some (typed) value. The `set` rule requires it. -/
def ptsToAny (ℓ : Location) : HProp :=
  fun σ => ∃ v : ℓ.ty, σ ℓ.id = .result (Heap.encode v)

theorem ptsTo_ptsToAny (ℓ : Location) (v : ℓ.ty) :
    (ℓ ↦ₜ v : HProp) ⊢ ptsToAny ℓ :=
  fun _ hσ => ⟨v, hσ⟩

/-- A heap image satisfies `ℓ ↦ₜ v` iff the heap stores `v`'s encoding
at `ℓ.id`. -/
theorem ptsTo_toIState_iff {ℓ : Location} {v : ℓ.ty} {h : Heap} :
    (ℓ ↦ₜ v : HProp) h.toIState ↔ h.data.lookup ℓ.id = some (Heap.encode v) :=
  toIState_result_iff

/-- Reading through `Heap.get` at an owned location returns the value:
the encoding decodes back via `Heap.decode_encode`. -/
theorem ptsTo_get {ℓ : Location} {v : ℓ.ty} {h : Heap}
    (hp : (ℓ ↦ₜ v : HProp) h.toIState) : h.get ℓ = v := by
  unfold Heap.get
  rw [ptsTo_toIState_iff.mp hp]
  exact Heap.decode_encode v

end CatCrypt.Crypto.IrisBridge
