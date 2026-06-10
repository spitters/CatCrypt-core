/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Nominal.Fresh

/-!
# Support Utilities for Nominal Sets

This file provides additional utilities and notations for working with support
in nominal sets. It builds on top of the core definitions in `Nominal.lean`
and `Fresh.lean`.

## Main definitions

* `supp` - Convenient alias for `NomSet.supp`
* Notation `a # x` for freshness (using `Fresh` from Fresh.lean)

## References

* [Pitts, *Nominal Sets*], Chapter 2
* SSProve `theories/Crypt/nominal/Nominal.v`
-/

namespace CatCrypt.Nominal

/-! ## Support utilities -/

/-- Get the support of a value in a nominal set (convenient alias for NomSet.supp) -/
noncomputable abbrev supp {α : Type*} [NomSet α] (x : α) : Finset Atom :=
  NomSet.supp x

/-! ## Notation -/

/-- Notation for freshness: `a # x` means atom `a` is fresh for `x` -/
scoped notation:50 a " # " x => Fresh a x

/-! ## Additional lemmas -/

/-- Disjointness is symmetric -/
theorem Disj.symm {α β : Type*} [NomSet α] [NomSet β] {x : α} {y : β}
    (h : Disj x y) : Disj y x := by
  simp only [Disj, disjoint_comm] at h ⊢
  exact h

/-- Fresh atom generation for a single element -/
noncomputable def freshForOne {α : Type*} [NomSet α] (x : α) : Atom :=
  Atom.fresh (NomSet.supp x)

theorem freshForOne_fresh {α : Type*} [NomSet α] (x : α) : Fresh (freshForOne x) x := by
  simp only [freshForOne, Fresh]
  exact Atom.fresh_not_mem (NomSet.supp x)

end CatCrypt.Nominal
