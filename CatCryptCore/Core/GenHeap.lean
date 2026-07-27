/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Core.Code
import CatCryptCore.Relational.Frame

/-!
# Countable-Typed Heap Locations

`CatCrypt.Core.Location` requires `Fintype ty`, so a heap cell can only hold a value
of a finite type. `GLocation` requires only `Countable ty` and `Inhabited ty`, which
admits cells holding `Nat`, `List α`, association lists, and other unbounded values.

Both flavours read and write the *same* carrier, `CatCrypt.Core.Heap` — a partial
finite map from location ids to natural numbers. Only the value codec differs:
`Heap.get`/`Heap.set` code through `Fintype.equivFin`, while `Heap.gget`/`Heap.gset`
code through `gencode`, a chosen injection `ty ↪ Nat`. Since `gencode` uses
`Fintype.equivFin` whenever the value type happens to be finite, the two codecs
agree on finite types, and `gget`/`gset` restrict to `get`/`set` along
`GLocation.ofLocation` (`gget_ofLocation`, `gset_ofLocation`).

`SPComp α` is `Heap → SDistr (α × Heap)`, so it needs no adjustment: `rHoare`,
`DependsOn` and `PreservesOutside` apply directly to computations built from
`SPComp.gget`/`SPComp.gset`. This file supplies the footprint lemmas for those
operations.

## Main definitions

* `gencode`, `gdecode` — codec for a countable inhabited type
* `GLocation` — heap location with a countable value type
* `Heap.gget`, `Heap.gset` — heap access at a `GLocation`
* `SPComp.gget`, `SPComp.gset` — the corresponding stateful operations
* `CatCrypt.Relational.gLeftHas`, `gRightHas` — one-sided pRHL assertions
-/

open scoped Classical

namespace CatCrypt.Core

/-! ## Codec for a countable type -/

/-- Injection of a countable type into `Nat`. On a finite type it is
`Fintype.equivFin` followed by `Fin.val`; otherwise it is a chosen injection. -/
noncomputable def gencode (α : Type) [Countable α] : α → Nat :=
  if h : Nonempty (Fintype α) then (fun a => (@Fintype.equivFin α h.some a).val)
  else (Countable.exists_injective_nat α).choose

theorem gencode_injective (α : Type) [Countable α] : Function.Injective (gencode α) := by
  rw [gencode]
  split
  · next h => exact fun _ _ hab => (@Fintype.equivFin α h.some).injective (Fin.val_injective hab)
  · exact (Countable.exists_injective_nat α).choose_spec

/-- On a finite type, `gencode` is `Heap.encode`. -/
theorem gencode_eq_encode {α : Type} [inst : Fintype α] :
    gencode α = Heap.encode (α := α) := by
  have hne : Nonempty (Fintype α) := ⟨inst⟩
  rw [gencode, dif_pos hne, Subsingleton.elim hne.some inst]
  rfl

/-- Partial inverse of `gencode`, returning `default` off its image. -/
noncomputable def gdecode (α : Type) [Countable α] [Inhabited α] (n : Nat) : α :=
  if h : ∃ a : α, gencode α a = n then h.choose else default

theorem gdecode_gencode {α : Type} [Countable α] [Inhabited α] (a : α) :
    gdecode α (gencode α a) = a := by
  rw [gdecode, dif_pos (⟨a, rfl⟩ : ∃ b : α, gencode α b = gencode α a)]
  exact gencode_injective α (Exists.choose_spec (⟨a, rfl⟩ : ∃ b : α, gencode α b = gencode α a))

/-- On a finite type, `gdecode` is `Heap.decode`. -/
theorem gdecode_eq_decode {α : Type} [Fintype α] [Inhabited α] :
    gdecode α = Heap.decode α := by
  funext n
  have hval : ∀ a : α, gencode α a = (Fintype.equivFin α a).val := fun a => by
    rw [gencode_eq_encode, Heap.encode]
  by_cases hlt : n < Fintype.card α
  · have hmem : ∃ a : α, gencode α a = n :=
      ⟨(Fintype.equivFin α).symm ⟨n, hlt⟩, by rw [hval, Equiv.apply_symm_apply]⟩
    rw [gdecode, dif_pos hmem, Heap.decode, dif_pos hlt]
    exact gencode_injective α (by rw [hmem.choose_spec, hval, Equiv.apply_symm_apply])
  · have hmem : ¬ ∃ a : α, gencode α a = n :=
      fun ⟨a, ha⟩ => hlt (ha ▸ hval a ▸ (Fintype.equivFin α a).isLt)
    rw [gdecode, dif_neg hmem, Heap.decode, dif_neg hlt]

/-! ## Locations with a countable value type -/

/-- Heap location whose value type is countable and inhabited. The value type is
fixed at `Type` (universe 0), matching `Location`. -/
structure GLocation where
  /-- Location identifier. -/
  id : Nat
  /-- Type of the value stored at this location. -/
  ty : Type
  [countable : Countable ty]
  [inhabited : Inhabited ty]

attribute [instance] GLocation.countable GLocation.inhabited

namespace GLocation

noncomputable instance : DecidableEq GLocation := Classical.decEq GLocation

/-- A `Location` is a `GLocation`: a finite type is countable. -/
def ofLocation (l : Location) : GLocation := { id := l.id, ty := l.ty }

@[simp] theorem ofLocation_id (l : Location) : (ofLocation l).id = l.id := rfl

@[simp] theorem ofLocation_ty (l : Location) : (ofLocation l).ty = l.ty := rfl

end GLocation

/-! ## Heap access at a `GLocation` -/

namespace Heap

/-- Read a countable-typed location. Returns `default` if never written. -/
noncomputable def gget (h : Heap) (l : GLocation) : l.ty :=
  match h.data.lookup l.id with
  | some n => gdecode l.ty n
  | none => default

/-- Write a countable-typed location. -/
noncomputable def gset (h : Heap) (l : GLocation) (v : l.ty) : Heap :=
  ⟨h.data.insert l.id (gencode l.ty v)⟩

@[simp]
theorem gget_gset_same (h : Heap) (l : GLocation) (v : l.ty) :
    (h.gset l v).gget l = v := by
  simp only [gget, gset, Finmap.lookup_insert, gdecode_gencode]

@[simp]
theorem gget_gset_other (h : Heap) (l l' : GLocation) (v : l.ty) (hne : l.id ≠ l'.id) :
    (h.gset l v).gget l' = h.gget l' := by
  simp [gget, gset, hne.symm]

@[simp]
theorem gset_gset_same (h : Heap) (l : GLocation) (v₁ v₂ : l.ty) :
    (h.gset l v₁).gset l v₂ = h.gset l v₂ := by
  simp only [gset, Finmap.insert_insert]

theorem gset_gset_comm (h : Heap) (l₁ l₂ : GLocation) (v₁ : l₁.ty) (v₂ : l₂.ty)
    (hne : l₁.id ≠ l₂.id) :
    (h.gset l₁ v₁).gset l₂ v₂ = (h.gset l₂ v₂).gset l₁ v₁ :=
  ext (Finmap.insert_insert_of_ne _ hne)

@[simp]
theorem gget_empty (l : GLocation) : empty.gget l = default := by
  simp only [gget, empty, Finmap.lookup_empty]

@[simp]
theorem gset_lookup_same (h : Heap) (l : GLocation) (v : l.ty) :
    (h.gset l v).data.lookup l.id = some (gencode l.ty v) :=
  Finmap.lookup_insert _

theorem gset_lookup_of_ne (h : Heap) (l : GLocation) (v : l.ty) {i : Nat} (hne : i ≠ l.id) :
    (h.gset l v).data.lookup i = h.data.lookup i :=
  Finmap.lookup_insert_of_ne _ hne

/-- Two heaps agreeing on a location's id agree on its contents. -/
theorem gget_congr_of_agreeOn {h₁ h₂ : Heap} {locs : LocSet} (hag : agreeOn h₁ h₂ locs)
    {l : GLocation} (hmem : l.id ∈ locs) : h₁.gget l = h₂.gget l := by
  simp only [gget, hag l.id hmem]

/-! ### Compatibility of the two flavours

The countable codec extends the finite one, so a `Location` read or written through
the generalized interface behaves exactly as it does through `Heap.get`/`Heap.set`. -/

@[simp]
theorem gget_ofLocation (h : Heap) (l : Location) :
    h.gget (GLocation.ofLocation l) = h.get l := by
  simp only [gget, get, GLocation.ofLocation_id, GLocation.ofLocation_ty, gdecode_eq_decode]
  rfl

@[simp]
theorem gset_ofLocation (h : Heap) (l : Location) (v : l.ty) :
    h.gset (GLocation.ofLocation l) v = h.set l v := by
  simp only [gset, set, GLocation.ofLocation_id, GLocation.ofLocation_ty, gencode_eq_encode]

/-- A finite-typed write does not disturb a countable-typed read at a different id. -/
theorem gget_set_other (h : Heap) (l : Location) (l' : GLocation) (v : l.ty)
    (hne : l.id ≠ l'.id) : (h.set l v).gget l' = h.gget l' := by
  simp [gget, set, hne.symm]

/-- A countable-typed write does not disturb a finite-typed read at a different id. -/
theorem get_gset_other (h : Heap) (l : GLocation) (l' : Location) (v : l.ty)
    (hne : l.id ≠ l'.id) : (h.gset l v).get l' = h.get l' := by
  simp [get, gset, hne.symm]

end Heap

/-! ## Stateful operations -/

namespace SPComp

/-- Read a countable-typed location. -/
noncomputable def gget (l : GLocation) : SPComp l.ty :=
  fun h => CatCrypt.Prob.SDistr.pure (h.gget l, h)

/-- Write a countable-typed location. -/
noncomputable def gset (l : GLocation) (v : l.ty) : SPComp Unit :=
  fun h => CatCrypt.Prob.SDistr.pure ((), h.gset l v)

theorem gget_def (l : GLocation) (h : Heap) :
    (gget l) h = CatCrypt.Prob.SDistr.pure (h.gget l, h) := rfl

theorem gset_def (l : GLocation) (v : l.ty) (h : Heap) :
    (gset l v) h = CatCrypt.Prob.SDistr.pure ((), h.gset l v) := rfl

/-- The generalized operations restrict to the finite-typed ones. -/
theorem gget_ofLocation (l : Location) :
    gget (GLocation.ofLocation l) = get l := by
  funext h; simp only [gget, get, Heap.gget_ofLocation]; rfl

theorem gset_ofLocation (l : Location) (v : l.ty) :
    gset (GLocation.ofLocation l) v = set l v := by
  funext h; simp only [gset, set, Heap.gset_ofLocation]

end SPComp

end CatCrypt.Core

/-! ## Framing -/

namespace CatCrypt.Relational

open CatCrypt.Core CatCrypt.Prob

/-- The left heap stores `v` at a countable-typed location. -/
def gLeftHas (l : GLocation) (v : l.ty) : RPre := fun h₁ _ => h₁.gget l = v

/-- The right heap stores `v` at a countable-typed location. -/
def gRightHas (l : GLocation) (v : l.ty) : RPre := fun _ h₂ => h₂.gget l = v

theorem dependsOn_gLeftHas (l : GLocation) (v : l.ty) :
    DependsOn (gLeftHas l v) {l.id} :=
  fun _ _ _ _ hagree _ hleft =>
    (Heap.gget_congr_of_agreeOn hagree (Finset.mem_singleton.mpr rfl)).symm.trans hleft

theorem dependsOn_gRightHas (l : GLocation) (v : l.ty) :
    DependsOn (gRightHas l v) {l.id} :=
  fun _ _ _ _ _ hagree hright =>
    (Heap.gget_congr_of_agreeOn hagree (Finset.mem_singleton.mpr rfl)).symm.trans hright

theorem preservesOutside_gget (l : GLocation) : PreservesOutside (SPComp.gget l) ∅ := by
  intro h a h' hne id _
  simp only [SPComp.gget_def, SDistr.pure, PMF.pure_apply, ne_eq, ite_eq_right_iff,
    Classical.not_imp, Option.some.injEq, Prod.mk.injEq] at hne
  rw [hne.1.2]

theorem preservesOutside_gset (l : GLocation) (v : l.ty) :
    PreservesOutside (SPComp.gset l v) {l.id} := by
  intro h a h' hne id hnotin
  simp only [SPComp.gset_def, SDistr.pure, PMF.pure_apply, ne_eq, ite_eq_right_iff,
    Classical.not_imp, Option.some.injEq, Prod.mk.injEq] at hne
  rw [hne.1.2]
  exact Heap.gset_lookup_of_ne _ _ _ fun hid => hnotin (Finset.mem_singleton.mpr hid)

end CatCrypt.Relational

/-! ## Non-vacuity

`Nat` is a legal `GLocation` value type and is not a legal `Location` value type. -/

namespace CatCrypt.Core

/-- An unbounded counter cell. -/
@[reducible] def natCounter (id : Nat) : GLocation := { id := id, ty := Nat }

/-- `Nat` carries no `Fintype` instance, so `natCounter`'s value type is outside
the range of `Location`. -/
theorem nat_no_fintype : ¬ Nonempty (Fintype Nat) := fun ⟨_⟩ => not_finite Nat

/-- Incrementing a counter held in the heap. -/
noncomputable def incr (id : Nat) : SPComp Nat :=
  SPComp.bind (SPComp.gget (natCounter id)) fun n =>
    SPComp.bind (SPComp.gset (natCounter id) (n + 1)) fun _ =>
      SPComp.pure (n + 1)

/-- `incr` run twice from the empty heap yields `2` and stores `2`. -/
theorem incr_twice_empty (id : Nat) :
    SPComp.bind (incr id) (fun _ => incr id) Heap.empty =
      CatCrypt.Prob.SDistr.pure (2, Heap.empty.gset (natCounter id) 2) := by
  simp [incr, SPComp.bind, SPComp.gget, SPComp.gset, SPComp.pure,
    CatCrypt.Prob.SDistr.pure_bind]

end CatCrypt.Core
