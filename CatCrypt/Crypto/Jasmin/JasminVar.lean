/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.JasminTypes
import CatCrypt.Core.Location
import Mathlib.Data.Nat.Pairing

/-!
# Jasmin Variable/Memory Model

This file defines the mapping from Jasmin variables to CatCrypt heap locations,
following the Rocq `jasmin_translate.v`.

## Scope Management

The Rocq version uses binary positives (`BinNums.positive`) for scope identifiers
(`p_id`) with a prefix ordering. We use `Nat` for simplicity since the key property
is injectivity of the variable-to-location mapping.

## Memory Model

Memory is represented as a single location holding a `JArray memSize` value.
Loads and stores go through this location.
-/

namespace CatCrypt.Crypto.Jasmin

open CatCrypt.Core

/-! ## Scope Identifiers -/

/-- Scope identifier for variable namespacing. -/
abbrev ScopeId := Nat

/-- Generate two fresh child scope ids from a parent scope. -/
def freshId (sid : ScopeId) : ScopeId × ScopeId :=
  (sid * 2 + 1, sid * 2 + 2)

theorem freshId_fst_ne_snd (sid : ScopeId) :
    (freshId sid).1 ≠ (freshId sid).2 := by
  simp [freshId]

/-! ## Variable Encoding -/

/-- Encode a character list as a natural number using Cantor pairing.
    The `+1` shifts non-empty lists above the base case to ensure the
    empty list `[]` has a unique encoding. -/
def encodeChars : List Char → Nat
  | []       => 0
  | c :: cs  => Nat.pair c.toNat (encodeChars cs) + 1

/-- Encode a variable name as a natural number via Cantor-paired char codes.
    Provably injective (see `encodeVarName_injective`). -/
def encodeVarName (name : String) : Nat :=
  encodeChars name.toList

/-- Encode a Jasmin type as a natural number.

    Uses parity to distinguish `sarr` from `sword`: arrays get even codes
    `2 * (2 + n)` and words get odd codes `2 * ws.bits + 1`.  This makes the
    `sword` / `sarr` disjointness lemma `wordLoc_id_ne_towerLoc_id` work
    unconditionally for any `TowerType` byteSize (Phase D/E/I/K extensions
    introduce arbitrary-byteSize tower types like `TFpGen` / `TBytes`).
    `sbool` and `sint` retain their constants 0 and 1. -/
def encodeSType : SType → Nat
  | .sbool    => 0
  | .sint     => 1
  | .sarr n   => 2 * (2 + n)
  | .sword ws => 2 * ws.bits + 1

/-- Map a Jasmin variable to an CatCrypt location id within a given scope.
    Uses Cantor pairing for injectivity: distinct (sid, type, name) triples map
    to distinct ids. -/
def varLocId (sid : ScopeId) (v : Var) : Nat :=
  Nat.pair (Nat.pair sid (encodeSType v.vtype)) (encodeVarName v.vname)

/-- `encodeChars` is injective. -/
theorem encodeChars_injective : Function.Injective encodeChars := by
  intro l1 l2 heq
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons c cs => simp [encodeChars] at heq
  | cons c1 cs1 ih =>
    cases l2 with
    | nil => simp [encodeChars] at heq
    | cons c2 cs2 =>
      simp only [encodeChars, Nat.add_right_cancel_iff] at heq
      obtain ⟨hc, hrest⟩ := Nat.pair_eq_pair.mp heq
      have hc' : c1.val = c2.val := UInt32.toNat_inj.mp hc
      have : c1 = c2 := Char.ext hc'
      subst this
      rw [ih hrest]

/-- `encodeVarName` is injective: distinct strings map to distinct naturals. -/
theorem encodeVarName_injective : Function.Injective encodeVarName := by
  intro s1 s2 heq
  exact String.toList_injective (encodeChars_injective heq)

/-! ## Location Construction -/

/-- Translate a Jasmin variable to an CatCrypt `Location`. -/
noncomputable def translateVar (sid : ScopeId) (v : Var) : Location :=
  match v.vtype with
  | .sbool =>
    { id := varLocId sid v, ty := Bool }
  | .sint =>
    { id := varLocId sid v, ty := BitVec 64,
      fintype := CatCrypt.Crypto.instFintypeBitVec 64 }
  | .sarr n =>
    { id := varLocId sid v, ty := JArray n,
      fintype := JArray.instFintypeJArray n }
  | .sword ws =>
    { id := varLocId sid v, ty := BitVec ws.bits,
      fintype := CatCrypt.Crypto.instFintypeBitVec ws.bits }

/-- Translate a `VarI` to a location. -/
noncomputable def translateVarI (sid : ScopeId) (vi : VarI) : Location :=
  translateVar sid vi.var

/-! ## Memory Location -/

/-- Size of the memory model (number of addressable bytes). -/
def memSize : Nat := 4096

/-- The global memory location (id 0). -/
noncomputable def memLoc : Location :=
  { id := 0, ty := JArray memSize,
    fintype := JArray.instFintypeJArray memSize }

/-! ## Location Sets -/

/-- Collect all location ids used by a list of variables in a scope. -/
def varLocs (sid : ScopeId) (vars : List Var) : List Nat :=
  vars.map (varLocId sid ·)

/-- Location ids used by a function declaration. -/
def funLocs (sid : ScopeId) (fd : FunDecl) : List Nat :=
  let paramLocs := fd.params.map (fun p => varLocId sid p.var.var)
  let resultLocs := fd.results.map (fun vi => varLocId sid vi.var)
  paramLocs ++ resultLocs

end CatCrypt.Crypto.Jasmin
