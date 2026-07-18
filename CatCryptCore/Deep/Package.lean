/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Deep.RawCode

/-!
# Deep Embedding Packages

This file defines packages for the deep embedding of CatCrypt computations.

## Main definitions

* `DeepInterface` - Specifies operation signatures (id, domain, codomain)
* `ValidCode` - Code that only uses declared locations
* `DeepPackage` - A package with location support and interface specifications
* `DeepPackage.link` - Sequential composition of packages
* `DeepPackage.par` - Parallel composition of packages
* `DeepPackage.sep` - Separation predicate (disjoint locations)

## Nominal Structure

Packages support nominal operations for automatic state separation:
* `NomPackage.atoms` - Get the atoms used by a package
* `NomPackage.atomSep` - Separation based on disjoint atoms
* `NomPackage.sep_of_atomSep` - Atom separation implies location separation

## Overview

In the deep embedding, packages represent cryptographic protocol implementations
with explicit state management. Each package:

1. Has a finite set of locations (memory cells) it uses
2. Imports operations from other packages
3. Exports operations it implements
4. Contains code implementations for exported operations

Separation reasoning can be based on either:
- Location id disjointness (DeepPackage.sep)
- Atom disjointness (NomPackage.atomSep) for nominal reasoning

## References

* [Larsen and Schürmann, *Nominal State-Separating Proofs*](https://eprint.iacr.org/2025/598)
* SSProve Rocq: `theories/Crypt/nominal/Nominal.v`, `free_code.v`
-/

namespace CatCrypt.Deep

open CatCrypt.Core
open CatCrypt.Nominal

/-! ## Interfaces -/

universe u

/-- An interface specifies the signature of operations.
    Each operation has an id (for identification), a domain type, and a codomain type.
    All types are at the same universe `u`, matching `RawCode.oracleCall`.

    Example: A PRF interface might have:
    - Operation 0: Unit → BitVec 128  (key generation)
    - Operation 1: BitVec 128 → BitVec 128  (evaluation) -/
structure DeepInterface where
  /-- The operations in this interface.
      Each entry is (operation_id, domain_type, codomain_type). -/
  ops : List (ℕ × Type u × Type u)

namespace DeepInterface

/-- The empty interface with no operations -/
def empty : DeepInterface.{u} := ⟨[]⟩

instance : EmptyCollection DeepInterface.{u} := ⟨empty⟩

instance : Inhabited DeepInterface.{u} := ⟨empty⟩

/-- Check if an operation is in the interface -/
def contains (i : DeepInterface.{u}) (op_id : ℕ) (dom codom : Type u) : Prop :=
  (op_id, dom, codom) ∈ i.ops

/-- Two interfaces are equal if they have the same operations -/
theorem ext {i₁ i₂ : DeepInterface.{u}} (h : i₁.ops = i₂.ops) : i₁ = i₂ := by
  cases i₁; cases i₂; simp only [mk.injEq]; exact h

end DeepInterface

/-! ## Valid Code (Inductive Definition)

Following Rocq SSProve, we define validity inductively. This approach:
1. Avoids the problem of computing continuation locations for bind
2. Makes HEq proofs trivial via proof irrelevance
3. Matches the Rocq implementation exactly -/

/-- Valid code uses only locations from a declared set.

    Defined inductively following Rocq SSProve's `valid_code`.
    Each constructor checks that location accesses are within the declared set `L`.
    Note: We use LocSet (= Finset Nat) for location id sets. -/
inductive ValidCode (L : LocSet) : (α : Type u) → RawCode α → Prop where
  | ret : ∀ {α : Type u} (x : α), ValidCode L α (RawCode.ret x)
  | bind : ∀ {α β : Type u} (c : RawCode α) (k : α → RawCode β),
      ValidCode L α c → (∀ a, ValidCode L β (k a)) → ValidCode L β (RawCode.bind c k)
  | sample : ∀ (T : Type u) [Fintype T] [Nonempty T], ValidCode L T (@RawCode.sample T _ _)
  | get : ∀ (ℓ : Core.Location), ℓ.id ∈ L → ValidCode L (ULift.{u} ℓ.ty) (RawCode.get ℓ)
  | put : ∀ (ℓ : Core.Location) (v : ℓ.ty), ℓ.id ∈ L → ValidCode L (ULift.{u} Unit) (RawCode.put ℓ v)
  | fail : ∀ {α : Type u}, ValidCode L α (@RawCode.fail α)
  | oracleCall : ∀ (op : ℕ) (dom codom : Type u) (x : dom),
      ValidCode L codom (RawCode.oracleCall op dom codom x)
  | embed : ∀ {α : Type u} (c : Core.SPComp α), ValidCode L α (RawCode.embed c)

/-- Monotonicity: if code is valid for L and L ⊆ L', then code is valid for L'. -/
theorem ValidCode.mono {L L' : LocSet} (h_sub : L ⊆ L')
    {α : Type u} {c : RawCode α} (hv : ValidCode L α c) :
    ValidCode L' α c := by
  induction hv with
  | ret x => exact ValidCode.ret x
  | bind c k _ _ ih_c ih_k =>
    exact ValidCode.bind c k ih_c ih_k
  | sample T => exact ValidCode.sample T
  | get ℓ hℓ => exact ValidCode.get ℓ (h_sub hℓ)
  | put ℓ v hℓ => exact ValidCode.put ℓ v (h_sub hℓ)
  | fail => exact ValidCode.fail
  | oracleCall op dom codom x => exact ValidCode.oracleCall op dom codom x
  | embed c => exact ValidCode.embed c

/-- A valid code bundle: code together with its validity proof.
    This is the structure used in packages. -/
structure ValidCodeBundle (L : LocSet) (α : Type*) where
  code : RawCode α
  valid : ValidCode L α code

/-! ## Type Class for Automatic Validity Proofs

The `IsValid` type class provides automatic synthesis of ValidCode proofs.
This hybrid approach gives the best of both worlds:
- RawCode remains a simple free monad without validity constraints
- ValidCode proofs are synthesized automatically via type class inference
- Manual proofs are still possible when needed
-/

/-- Type class for synthesizing ValidCode proofs automatically. -/
class IsValid (L : LocSet) {α : Type u} (c : RawCode α) : Prop where
  proof : ValidCode L α c

/-- `ret x` is always valid. -/
instance IsValid.ret {L : LocSet} {α : Type u} (x : α) :
    IsValid L (RawCode.ret x) where
  proof := ValidCode.ret x

/-- `bind c k` is valid if `c` is valid and `k a` is valid for all `a`. -/
instance IsValid.bind {L : LocSet} {α β : Type u}
    (c : RawCode α) (k : α → RawCode β)
    [hc : IsValid L c] [hk : ∀ a, IsValid L (k a)] :
    IsValid L (RawCode.bind c k) where
  proof := ValidCode.bind c k hc.proof (fun a => (hk a).proof)

/-- `sample T` is always valid. -/
instance IsValid.sample {L : LocSet} (T : Type u) [Fintype T] [Nonempty T] :
    IsValid L (@RawCode.sample T _ _) where
  proof := ValidCode.sample T

/-- `get ℓ` is valid if `ℓ.id ∈ L`.
    Uses `Fact (ℓ.id ∈ L)` to allow instance synthesis when membership is decidable. -/
instance IsValid.get {L : LocSet} (ℓ : Core.Location) [h : Fact (ℓ.id ∈ L)] :
    IsValid L (RawCode.get ℓ) where
  proof := ValidCode.get ℓ h.out

/-- `put ℓ v` is valid if `ℓ.id ∈ L`.
    Uses `Fact (ℓ.id ∈ L)` to allow instance synthesis when membership is decidable. -/
instance IsValid.put {L : LocSet} (ℓ : Core.Location) (v : ℓ.ty) [h : Fact (ℓ.id ∈ L)] :
    IsValid L (RawCode.put ℓ v) where
  proof := ValidCode.put ℓ v h.out

/-- `fail` is always valid. -/
instance IsValid.fail {L : LocSet} {α : Type u} :
    IsValid L (@RawCode.fail α) where
  proof := ValidCode.fail

/-- `oracleCall` is always valid (no location access). -/
instance IsValid.oracleCall {L : LocSet} (op : ℕ) (dom codom : Type u) (x : dom) :
    IsValid L (RawCode.oracleCall op dom codom x) where
  proof := ValidCode.oracleCall op dom codom x

/-- `embed c` is always valid: an embedded shallow computation reads no declared
    location syntactically, so it is valid for every location set. This is the
    missing companion to the other `IsValid` instances and is what lets a reified
    opaque/abstract subterm carry an automatic validity proof. -/
instance IsValid.embed {L : LocSet} {α : Type u} (c : Core.SPComp α) :
    IsValid L (RawCode.embed c) where
  proof := ValidCode.embed c

/-- Convert an IsValid instance to a ValidCode proof. -/
theorem IsValid.toValidCode {L : LocSet} {α : Type u} (c : RawCode α)
    [h : IsValid L c] : ValidCode L α c := h.proof

/-- Create a ValidCodeBundle automatically using type class synthesis. -/
def ValidCodeBundle.auto {L : LocSet} {α : Type u} (c : RawCode α)
    [h : IsValid L c] : ValidCodeBundle L α where
  code := c
  valid := h.proof

namespace ValidCodeBundle

variable {L : LocSet} {α β : Type*}

/-- Monotonicity: if code bundle is valid for L, we can extend to any superset L'. -/
def mono {L' : LocSet} (h_sub : L ⊆ L') (vc : ValidCodeBundle L α) :
    ValidCodeBundle L' α where
  code := vc.code
  valid := ValidCode.mono h_sub vc.valid

/-- Two ValidCodeBundles with the same location set and code are equal (proof irrelevance). -/
theorem eq_of_code_eq {L : LocSet} {α : Type*}
    (vc₁ vc₂ : ValidCodeBundle L α) (h : vc₁.code = vc₂.code) : vc₁ = vc₂ := by
  cases vc₁; cases vc₂
  simp only [mk.injEq]
  exact h

end ValidCodeBundle

/-! ## Oracle Substitution Validity

When we substitute oracle calls with valid code, the result is valid. -/

/-- Substituting oracle calls with valid code preserves validity.

    If `c` is valid for locations `L₁` and every oracle call's replacement
    is valid for locations `L₂`, then `c.substOracle env` is valid for `L₁ ∪ L₂`.

    This is needed for `DeepPackage.link`: p₁'s code is valid for p₁.locs,
    and p₂'s implementations are valid for p₂.locs, so the linked code
    is valid for `p₁.locs ∪ p₂.locs`. -/
theorem substOracle_valid {L₁ L₂ : LocSet} {α : Type u} {c : RawCode α}
    (env : ∀ (op : ℕ) (dom codom : Type u), dom → RawCode codom)
    (hv : ValidCode L₁ α c)
    (henv : ∀ (op : ℕ) (dom codom : Type u) (x : dom),
      ValidCode (L₁ ∪ L₂) codom (env op dom codom x)) :
    ValidCode (L₁ ∪ L₂) α (c.substOracle env) := by
  induction hv with
  | ret x => exact ValidCode.ret x
  | bind c k _ _ ih_c ih_k =>
    exact ValidCode.bind _ _ ih_c ih_k
  | sample T => exact ValidCode.sample T
  | get ℓ hℓ => exact ValidCode.get ℓ (Finset.mem_union_left _ hℓ)
  | put ℓ v hℓ => exact ValidCode.put ℓ v (Finset.mem_union_left _ hℓ)
  | fail => exact ValidCode.fail
  | oracleCall op dom codom x => exact henv op dom codom x
  | embed c => exact ValidCode.embed c

/-! ## Deep Packages -/

/-- A package bundles code implementations with interface specifications.

    A package consists of:
    - A finite set of location ids (state) it uses
    - An import interface (operations it calls)
    - An export interface (operations it implements)
    - Code implementations for each exported operation

    The key invariant is that implementations only use declared locations,
    enabling modular composition and separation reasoning. -/
structure DeepPackage where
  /-- The finite set of location ids used by this package -/
  locs : LocSet
  /-- Operations this package imports (calls from other packages) -/
  imports : DeepInterface
  /-- Operations this package exports (implements) -/
  exports : DeepInterface
  /-- Implementation of exported operations.
      For each operation in the export interface, we provide code (bundled with validity proof)
      that maps domain values to a computation producing codomain values.
      All types are at universe `u`, matching `RawCode.oracleCall` and `substOracle`. -/
  impl : ∀ (op : ℕ) (dom codom : Type u),
    (op, dom, codom) ∈ exports.ops → dom → ValidCodeBundle locs codom

namespace DeepPackage

/-! ## Basic operations -/

/-- Empty package with no locations, no imports, no exports -/
def empty : DeepPackage where
  locs := ∅
  imports := ∅
  exports := ∅
  impl := fun _ _ _ h _ => nomatch h

instance : EmptyCollection DeepPackage := ⟨empty⟩

instance : Inhabited DeepPackage := ⟨empty⟩

/-! ## Separation -/

/-- Two packages are separated if their location ids are disjoint.

    This is the key property for modular reasoning: separated packages
    cannot interfere with each other's state. -/
def sep (p₁ p₂ : DeepPackage) : Prop :=
  Disjoint p₁.locs p₂.locs

theorem sep_comm (p₁ p₂ : DeepPackage) : sep p₁ p₂ ↔ sep p₂ p₁ := by
  simp only [sep, disjoint_comm]

theorem sep_empty_left (p : DeepPackage) : sep empty p := by
  simp only [sep, empty, Finset.disjoint_empty_left]

theorem sep_empty_right (p : DeepPackage) : sep p empty := by
  simp only [sep, empty, Finset.disjoint_empty_right]

/-! ## Package Composition -/

/-- Sequential composition (linking) of packages.

    `link p₁ p₂` connects p₂'s exported operations to p₁'s imports.
    The resulting package:
    - Uses locations from both packages
    - Imports p₂'s imports (operations not provided by p₂)
    - Exports p₁'s exports
    - Implementations from p₁, with oracle calls resolved via `substOracle`

    Oracle calls in p₁'s code are resolved as follows:
    - If the called operation is in p₂'s exports, the call is replaced
      with p₂'s implementation (extended to the union of locations)
    - If not, the oracle call is left as-is (evaluates to failure
      or is resolved by further linking) -/
noncomputable def link (p₁ p₂ : DeepPackage.{u}) : DeepPackage.{u} where
  locs := p₁.locs ∪ p₂.locs
  imports := p₂.imports
  exports := p₁.exports
  impl := fun op dom codom h_exp x =>
    let vc := p₁.impl op dom codom h_exp x
    -- Build oracle environment from p₂'s exports
    -- Use Classical.dec since Type u doesn't have DecidableEq
    let env : ∀ (op' : ℕ) (dom' codom' : Type u), dom' → RawCode codom' :=
      fun op' dom' codom' x' =>
        have := Classical.dec ((op', dom', codom') ∈ p₂.exports.ops)
        if h : (op', dom', codom') ∈ p₂.exports.ops
        then (p₂.impl op' dom' codom' h x').code
        else .fail
    ⟨vc.code.substOracle env,
     substOracle_valid env vc.valid (fun op' dom' codom' x' => by
       simp only [env]
       have := Classical.dec ((op', dom', codom') ∈ p₂.exports.ops)
       split
       · next h => exact (p₂.impl op' dom' codom' h x').valid.mono Finset.subset_union_right
       · exact ValidCode.fail)⟩

/-- Link a specific operation's code with an oracle environment.

    Given code `c` at universe `u` and an oracle environment `env` that
    provides implementations for oracle calls, this produces linked code
    where oracle calls are substituted with implementations.

    This is a lower-level building block than `link`. Use it when you need
    custom oracle environments rather than linking two packages. -/
noncomputable def linkCode {L₁ L₂ : LocSet} {α : Type u}
    (vc : ValidCodeBundle L₁ α)
    (env : ∀ (op : ℕ) (dom codom : Type u), dom → RawCode codom)
    (henv : ∀ (op : ℕ) (dom codom : Type u) (x : dom),
      ValidCode (L₁ ∪ L₂) codom (env op dom codom x)) :
    ValidCodeBundle (L₁ ∪ L₂) α :=
  ⟨vc.code.substOracle env,
   substOracle_valid env vc.valid henv⟩

/-- Parallel composition of packages with disjoint locations.

    `par p₁ p₂ sep_proof` combines two packages that don't share state.
    The resulting package:
    - Uses locations from both packages (guaranteed disjoint)
    - Imports operations from both packages
    - Exports operations from both packages
    - Implementations from both packages (extended to the larger location set)

    The separation proof ensures no interference between packages. -/
noncomputable def par (p₁ p₂ : DeepPackage) (_h_sep : sep p₁ p₂) : DeepPackage where
  locs := p₁.locs ∪ p₂.locs
  imports := ⟨p₁.imports.ops ++ p₂.imports.ops⟩  -- Union of imports
  exports := ⟨p₁.exports.ops ++ p₂.exports.ops⟩  -- Union of exports
  impl := fun op dom codom h_exp x =>
    -- The operation is in either p₁.exports or p₂.exports
    -- Use dite (term-mode) for clean definitional unfolding
    have := Classical.dec ((op, dom, codom) ∈ p₁.exports.ops)
    if h₁ : (op, dom, codom) ∈ p₁.exports.ops then
      -- Use p₁'s implementation, extended to larger location set
      (p₁.impl op dom codom h₁ x).mono Finset.subset_union_left
    else
      -- Must be in p₂.exports
      have h₂ : (op, dom, codom) ∈ p₂.exports.ops :=
        (List.mem_append.mp h_exp).resolve_left h₁
      (p₂.impl op dom codom h₂ x).mono Finset.subset_union_right

/-! ## Par Implementation Characterization -/

/-- When the operation is in p₁'s exports, par dispatches to p₁'s implementation.
    The code is the same (mono only affects the validity proof, not the code). -/
theorem par_impl_code_eq_left (p₁ p₂ : DeepPackage.{u}) (h_sep : sep p₁ p₂)
    (op : ℕ) (dom codom : Type u)
    (h₁ : (op, dom, codom) ∈ p₁.exports.ops)
    (h_par : (op, dom, codom) ∈ (par p₁ p₂ h_sep).exports.ops)
    (x : dom) :
    ((par p₁ p₂ h_sep).impl op dom codom h_par x).code =
    (p₁.impl op dom codom h₁ x).code := by
  simp only [par, dif_pos h₁, ValidCodeBundle.mono]

/-- When the operation is NOT in p₁'s exports, par dispatches to p₂'s implementation. -/
theorem par_impl_code_eq_right (p₁ p₂ : DeepPackage.{u}) (h_sep : sep p₁ p₂)
    (op : ℕ) (dom codom : Type u)
    (h₁ : (op, dom, codom) ∉ p₁.exports.ops)
    (h₂ : (op, dom, codom) ∈ p₂.exports.ops)
    (h_par : (op, dom, codom) ∈ (par p₁ p₂ h_sep).exports.ops)
    (x : dom) :
    ((par p₁ p₂ h_sep).impl op dom codom h_par x).code =
    (p₂.impl op dom codom h₂ x).code := by
  simp only [par, dif_neg h₁, ValidCodeBundle.mono]

/-! ## Properties -/

/-- Separation is preserved by parallel composition -/
theorem par_sep_left (p₁ p₂ p₃ : DeepPackage)
    (h₁₂ : sep p₁ p₂) (h₁₃ : sep p₁ p₃) (h₂₃ : sep p₂ p₃) :
    sep p₁ (par p₂ p₃ h₂₃) := by
  simp only [sep, par]
  exact Finset.disjoint_union_right.mpr ⟨h₁₂, h₁₃⟩

/-- Separation is preserved by parallel composition (right) -/
theorem par_sep_right (p₁ p₂ p₃ : DeepPackage)
    (h₁₂ : sep p₁ p₂) (h₁₃ : sep p₁ p₃) (h₂₃ : sep p₂ p₃) :
    sep (par p₁ p₂ h₁₂) p₃ := by
  simp only [sep, par]
  exact Finset.disjoint_union_left.mpr ⟨h₁₃, h₂₃⟩

/-- Parallel composition is commutative up to reordering -/
theorem par_comm (p₁ p₂ : DeepPackage) (h₁₂ : sep p₁ p₂) (h₂₁ : sep p₂ p₁) :
    (par p₁ p₂ h₁₂).locs = (par p₂ p₁ h₂₁).locs := by
  simp only [par, Finset.union_comm]

/-! ## Identity Package

The identity (passthrough) package for an interface. It forwards all operations
from its exports to its imports by making oracle calls. This is the unit of
linking: `link p (id p.imports) = p` and `link (id p.exports) p = p`
(up to evaluation equivalence). -/

/-- The identity package for an interface: forwards every operation to the oracle.

    For each operation in the interface, the implementation is simply an oracle call,
    i.e., it passes the request through unchanged. This package has no locations
    (no state of its own).

    This is the monoidal unit for `link`:
    - `link p (id p.imports)` is evaluation-equivalent to `p`
    - `link (id p.exports) p` is evaluation-equivalent to `p` -/
noncomputable def id (iface : DeepInterface) : DeepPackage where
  locs := ∅
  imports := iface
  exports := iface
  impl := fun op dom codom h_exp x =>
    ⟨RawCode.oracleCall op dom codom x, ValidCode.oracleCall op dom codom x⟩

/-! ## Linking Properties -/

/-- The oracle environment built by `link` from a package `p₂`.

    This extracts the oracle substitution function from `link`'s definition
    for use in compositional reasoning. For each operation:
    - If `(op, dom, codom) ∈ p₂.exports.ops`, use p₂'s implementation
    - Otherwise, return `fail` -/
noncomputable def linkEnv (p₂ : DeepPackage.{u}) :
    ∀ (op : ℕ) (dom codom : Type u), dom → RawCode codom :=
  fun op dom codom x =>
    have := Classical.dec ((op, dom, codom) ∈ p₂.exports.ops)
    if h : (op, dom, codom) ∈ p₂.exports.ops
    then (p₂.impl op dom codom h x).code
    else .fail

/-- Linking with the identity package on the right preserves the code
    of each exported operation (up to oracle calls becoming identity).

    Specifically, for any operation in `p.exports`, the linked code
    `(link p (id p.imports)).impl op dom codom h x` has the same
    `substOracle` structure: oracle calls not in `p.imports` become `fail`,
    oracle calls in `p.imports` remain as oracle calls.

    At the evaluation level, this means `link p (id p.imports)` behaves
    the same as `p` (since unlinked oracle calls evaluate to `fail` anyway). -/
theorem link_id_right_code (p : DeepPackage.{u})
    (op : ℕ) (dom codom : Type u) (h : (op, dom, codom) ∈ p.exports.ops) (x : dom) :
    ((link p (id p.imports)).impl op dom codom h x).code =
    (p.impl op dom codom h x).code.substOracle (linkEnv (id p.imports)) := by
  -- This is definitionally true from how link and linkEnv are defined
  rfl

-- Double linking can be expressed as single linking with a composed oracle environment.
--
-- `link (link p₁ p₂) p₃` substitutes p₃'s oracle env into the already-substituted
-- code `p₁.code.substOracle(p₂.env)`. By `substOracle_comp`, this equals
-- `p₁.code.substOracle(fun op ... => (p₂.env op ...).substOracle(p₃.env))`.
--
-- Similarly, `link p₁ (link p₂ p₃)` substitutes the composed env from `link p₂ p₃`
-- into p₁'s code.
--
-- These two composed environments are NOT definitionally equal because:
-- - Left-associated: oracle calls in p₂'s code that aren't in p₃ become `fail`
-- - Right-associated: p₁ first resolves oracles via `link p₂ p₃`, which resolves
--   p₂'s oracles via p₃
--
-- However, they agree on evaluation because `fail.substOracle env = fail` and
-- `fail.eval = SPComp.fail` in both cases.

-- NOTE: Definitional equality `link (link p₁ p₂) p₃ = link p₁ (link p₂ p₃)` does NOT hold
-- because the oracle environments differ structurally (one uses nested substOracle,
-- the other uses a single dite lookup into a linked package).
-- The equality DOES hold at the evaluation level, which is what matters for advantage.

end DeepPackage

/-! ## Nominal Packages

`NomPackage` wraps `DeepPackage` with a location registry, enabling
atom-based separation reasoning.
-/

/-- Nominal package: DeepPackage with an associated location registry.
    This enables nominal reasoning (atom-based separation)
    while maintaining compatibility with evaluation.

    The key invariant `locs_eq` ensures that the location set is exactly
    the image of atoms under the registry mapping. This enables proving
    that atom separation implies location separation. -/
structure NomPackage where
  /-- The underlying DeepPackage -/
  pkg : DeepPackage
  /-- The registry mapping atoms to Core.Location ids -/
  registry : LocRegistry := LocRegistry.default
  /-- The atoms used by this package -/
  usedAtoms : Finset Atom := ∅
  /-- Invariant: locs is exactly the image of atoms under atomToId -/
  locs_eq : pkg.locs = usedAtoms.image registry.atomToId := by rfl

namespace NomPackage

/-- Get the location ids used by the package -/
def locs (p : NomPackage) : LocSet := p.pkg.locs

/-- Get the atoms used by the package -/
def atoms (p : NomPackage) : Finset Atom := p.usedAtoms

/-- Empty nominal package -/
def empty : NomPackage where
  pkg := DeepPackage.empty

instance : EmptyCollection NomPackage := ⟨empty⟩

instance : Inhabited NomPackage := ⟨empty⟩

/-- Two packages are atom-separated if their atoms are disjoint.
    This is the key property for nominal modular reasoning. -/
def atomSep (p₁ p₂ : NomPackage) : Prop :=
  Disjoint p₁.atoms p₂.atoms

theorem atomSep_comm (p₁ p₂ : NomPackage) : atomSep p₁ p₂ ↔ atomSep p₂ p₁ := by
  simp only [atomSep, disjoint_comm]

theorem atomSep_empty_left (p : NomPackage) : atomSep empty p := by
  simp only [atomSep, empty, atoms, Finset.disjoint_empty_left]

theorem atomSep_empty_right (p : NomPackage) : atomSep p empty := by
  simp only [atomSep, empty, atoms, Finset.disjoint_empty_right]

/-- If packages are atom-separated with the same registry, they are location-separated.
    This follows from the locs_eq invariant and injectivity of the registry. -/
theorem sep_of_atomSep (p₁ p₂ : NomPackage)
    (h : atomSep p₁ p₂)
    (hreg : p₁.registry = p₂.registry) :
    DeepPackage.sep p₁.pkg p₂.pkg := by
  simp only [DeepPackage.sep]
  -- Use the locs_eq invariant to rewrite locs as images of atoms
  rw [p₁.locs_eq, p₂.locs_eq, hreg]
  -- Now we need to show: Disjoint (atoms₁.image f) (atoms₂.image f) where f is injective
  -- and Disjoint atoms₁ atoms₂
  rw [Finset.disjoint_image p₂.registry.injective]
  exact h

/-- Parallel composition of nominal packages.
    Requires atom separation and the same registry. -/
noncomputable def par (p₁ p₂ : NomPackage) (h : atomSep p₁ p₂)
    (hreg : p₁.registry = p₂.registry) : NomPackage where
  pkg := DeepPackage.par p₁.pkg p₂.pkg (sep_of_atomSep p₁ p₂ h hreg)
  registry := p₁.registry
  usedAtoms := p₁.atoms ∪ p₂.atoms
  locs_eq := by
    simp only [DeepPackage.par, atoms]
    rw [p₁.locs_eq, p₂.locs_eq, hreg, Finset.image_union]

/-- Sequential composition (linking) of nominal packages.
    `link p₁ p₂` connects p₂'s exports to p₁'s imports.
    The resulting package uses atoms from both packages. -/
noncomputable def link (p₁ p₂ : NomPackage)
    (hreg : p₁.registry = p₂.registry := by rfl) : NomPackage where
  pkg := DeepPackage.link p₁.pkg p₂.pkg
  registry := p₁.registry
  usedAtoms := p₁.atoms ∪ p₂.atoms
  locs_eq := by
    simp only [DeepPackage.link, atoms]
    rw [p₁.locs_eq, p₂.locs_eq, hreg, Finset.image_union]

end NomPackage

/-! ## Documentation

This implementation provides the core package structure for the deep embedding.
Key completed features:

1. **DeepInterface**: Operation signatures with (id, domain, codomain)
2. **ValidCode**: Code restricted to declared locations
3. **DeepPackage**: Packages with location sets and interface specifications
4. **Composition**: `link` (sequential) and `par` (parallel) operations
5. **Separation**: The `sep` predicate for disjoint location reasoning

## Nominal Extension

The `NomPackage` type adds nominal structure:
- `NomPackage.atoms` - Atoms used by the package
- `NomPackage.atomSep` - Atom-based separation
- `NomPackage.sep_of_atomSep` - Atom separation implies location separation
-/

end CatCrypt.Deep
