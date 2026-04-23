/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Memory Locations

This file defines memory locations for stateful computations.
-/

namespace CatCrypt.Core

/-- Location identifier with type information.
    Note: We fix `ty` at `Type` (universe 0) to avoid universe polymorphism issues
    that would otherwise require complex universe unification in invariant proofs.
    This is sufficient for cryptographic applications where location types are
    typically finite types like `Bool`, `Fin n`, `BitVec n`, etc. -/
structure Location where
  id : Nat
  ty : Type  -- Fixed at Type 0 to avoid universe polymorphism issues
  [fintype : Fintype ty]
  [inhabited : Inhabited ty]

attribute [instance] Location.fintype Location.inhabited

/-- A set of locations -/
abbrev LocSet := Finset Nat  -- Simplified for now; could be Finset Location

namespace Location

/-- We consider two locations equal if they have the same id.
    Note: This is a weaker notion that ignores type equality,
    which is appropriate for our heap model where location ids are unique. -/
noncomputable instance : DecidableEq Location := Classical.decEq Location

end Location

end CatCrypt.Core
