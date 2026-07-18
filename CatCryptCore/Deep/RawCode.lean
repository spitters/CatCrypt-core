/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Core.Location
import CatCryptCore.Core.Code
import CatCryptCore.Deep.Location
import CatCryptCore.Tactics.LeOfSum
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic

/-!
# Raw Code: Free Monad for Computations

This file defines the deep embedding of CatCrypt computations as a free monad.

## Main definitions

* `RawCode` - The free monad representing computation syntax trees
* `RawCode.ret` - Pure return
* `RawCode.bind` - Monadic bind (sequencing)
* `RawCode.sample` - Sample from a uniform distribution
* `RawCode.get` - Read from a location
* `RawCode.put` - Write to a location
* `RawCode.fail` - Failure/exception

## Location model

## Nominal Structure

Location validity is tracked by the `ValidCode` inductive predicate
(see `Package.lean`), not by a syntactic `locs` function on `RawCode`.

## Implementation notes

This is a *free* monad, meaning it represents computation syntax trees
without any semantic interpretation. The monad instance allows using
do-notation for building computations, but the monad laws are not
necessarily satisfied at the syntactic level (they hold after quotienting
by observational equivalence).

We use `Core.Location` directly to enable axiom-free interpretation to
the shallow embedding (`SPComp`). This unifies the heap model between
the deep and shallow embeddings.

## References

* SSProve `theories/Crypt/rhl_semantics/free_prot/free_code.v`
* [Larsen and Schürmann, *Nominal State-Separating Proofs*](https://eprint.iacr.org/2025/598)
-/

namespace CatCrypt.Deep

open CatCrypt.Core
open CatCrypt.Nominal

universe u

/-- Raw code: syntax tree for probabilistic stateful computations.

    This is a free monad representing:
    - Pure computations (ret)
    - Sequencing (bind)
    - Probabilistic choice (sample)
    - State access (get/put)
    - Failure (fail)

    The type parameter α is the return type of the computation.

    Note: We use `Core.Location` directly to enable axiom-free interpretation
    to the shallow embedding. Location types are at Type 0 (universe level 0),
    so get returns `ULift.{u} ℓ.ty` to lift to universe u. -/
inductive RawCode : Type u → Type (u+1) where
  | ret {α : Type u} (a : α) : RawCode α
  | bind {α β : Type u} (c : RawCode α) (k : α → RawCode β) : RawCode β
  | sample (T : Type u) [Fintype T] [Nonempty T] : RawCode T
  | get (ℓ : CatCrypt.Core.Location) : RawCode (ULift.{u} ℓ.ty)
  | put (ℓ : CatCrypt.Core.Location) (v : ℓ.ty) : RawCode (ULift.{u} Unit)
  | fail {α : Type u} : RawCode α
  | oracleCall (op : ℕ) (dom : Type u) (codom : Type u) (x : dom) : RawCode codom
  /-- Embed an arbitrary `SPComp` value as opaque code.
      Used to express completeness: any heap-manipulating probabilistic
      computation has a corresponding `RawCode` representation whose
      `eval` is the original `SPComp`. -/
  | embed {α : Type u} (c : CatCrypt.Core.SPComp α) : RawCode α

namespace RawCode

/-- Pure return: lift a value into a computation -/
@[match_pattern]
def pure {α : Type u} (a : α) : RawCode α := ret a

/-- Monadic bind: sequence two computations -/
@[match_pattern]
def seq {α β : Type u} (c : RawCode α) (k : α → RawCode β) : RawCode β := bind c k

/-- Monad instance for RawCode.

    Note: This instance is not lawful at the syntactic level!
    The monad laws hold only after quotienting by observational equivalence.
    This instance is provided to enable do-notation. -/
instance : Monad RawCode where
  pure := @pure
  bind := @bind
  map f c := bind c (fun a => ret (f a))

/-- Applicative functor instance (derived from Monad) -/
instance : Applicative RawCode where
  pure := @pure
  seq f c := bind f fun g => bind (c ()) fun a => ret (g a)

/-- Structural induction principle for RawCode.

    This provides a convenient way to prove properties by structural induction,
    handling all constructors of the free monad. -/
def inductionOn {α : Type u} {motive : ∀ {α : Type u}, RawCode α → Prop}
    (c : RawCode α)
    (ret : ∀ {α : Type u} (a : α), motive (RawCode.ret a))
    (bind : ∀ {α β : Type u} (c : RawCode α) (k : α → RawCode β),
      motive c → (∀ a, motive (k a)) → motive (RawCode.bind c k))
    (sample : ∀ (T : Type u) [Fintype T] [Nonempty T], motive (@RawCode.sample T _ _))
    (get : ∀ (ℓ : CatCrypt.Core.Location), motive (RawCode.get ℓ))
    (put : ∀ (ℓ : CatCrypt.Core.Location) (v : ℓ.ty), motive (RawCode.put ℓ v))
    (fail : ∀ {α : Type u}, motive (@RawCode.fail α))
    (oracleCall : ∀ (op : ℕ) (dom codom : Type u) (x : dom),
      motive (RawCode.oracleCall op dom codom x))
    (embed : ∀ {α : Type u} (c : CatCrypt.Core.SPComp α), motive (RawCode.embed c)) :
    motive c := by
  induction c with
  | ret a => exact ret a
  | bind c k ih_c ih_k => exact bind c k ih_c ih_k
  | sample T => exact sample T
  | get ℓ => exact get ℓ
  | put ℓ v => exact put ℓ v
  | fail => exact fail
  | oracleCall op dom codom x => exact oracleCall op dom codom x
  | embed c => exact embed c

/-- Helper: sample from a non-empty fintype (with explicit instance arguments) -/
def sampleFrom (T : Type u) [Fintype T] [Nonempty T] : RawCode T :=
  sample T

/-- Helper: failing computation -/
@[inline]
def failure {α : Type u} : RawCode α := fail

/-- Example: get and increment a natural number location -/
example (ℓ : CatCrypt.Core.Location) (h : ℓ.ty = Nat) : RawCode Nat := do
  let n ← get ℓ
  -- Cast from ℓ.ty to Nat using the hypothesis, unwrap from ULift
  pure (h ▸ n.down + 1)

/-- Example: sampling and storing -/
example (ℓ : CatCrypt.Core.Location) (_h : ℓ.ty = Bool) : RawCode Bool := do
  let b ← sample Bool
  pure b

/-! ## Oracle Call Substitution

`substOracle` replaces oracle calls in code with concrete implementations.
This is the key operation for package linking: after constructing code with
`oracleCall` placeholders, linking substitutes the linked package's
implementations. -/

/-- Substitute all oracle calls in code with concrete implementations.

    Given an environment `env` that maps operation identifiers and types
    to RawCode implementations, this function recursively replaces every
    `oracleCall op dom codom x` with `env op dom codom x`.

    This is the core of `DeepPackage.link`: the linked package's
    implementations become the oracle environment. -/
def substOracle {α : Type u} (c : RawCode α)
    (env : ∀ (op : ℕ) (dom codom : Type u), dom → RawCode codom) : RawCode α :=
  match c with
  | .ret a => .ret a
  | .bind c k => .bind (substOracle c env) fun a => substOracle (k a) env
  | @RawCode.sample T fi ne => @RawCode.sample T fi ne
  | .get ℓ => .get ℓ
  | .put ℓ v => .put ℓ v
  | .fail => .fail
  | .oracleCall op dom codom x => env op dom codom x
  | .embed c => .embed c

/-- Substituting with the identity oracle environment (oracleCall) is a no-op.

    `substOracle c (fun op dom codom x => .oracleCall op dom codom x) = c`

    This is proved by structural induction on the code tree. -/
@[grind =] theorem substOracle_id {α : Type u} (c : RawCode α) :
    c.substOracle (fun op dom codom x => .oracleCall op dom codom x) = c := by
  induction c with
  | ret a => rfl
  | bind c k ih_c ih_k =>
    simp only [substOracle, ih_c]; congr_funext
  | sample T => rfl
  | get ℓ => rfl
  | put ℓ v => rfl
  | fail => rfl
  | oracleCall op dom codom x => rfl
  | embed c => rfl

/-- Double substitution can be composed into a single substitution.

    `(c.substOracle env₁).substOracle env₂ = c.substOracle (fun op dom codom x => (env₁ op dom codom x).substOracle env₂)`

    This is the key lemma for proving associativity of `DeepPackage.link`. -/
theorem substOracle_comp {α : Type u} (c : RawCode α)
    (env₁ : ∀ (op : ℕ) (dom codom : Type u), dom → RawCode codom)
    (env₂ : ∀ (op : ℕ) (dom codom : Type u), dom → RawCode codom) :
    (c.substOracle env₁).substOracle env₂ =
    c.substOracle (fun op dom codom x => (env₁ op dom codom x).substOracle env₂) := by
  induction c with
  | ret a => rfl
  | bind c k ih_c ih_k =>
    simp only [substOracle, ih_c]; congr_funext
  | sample T => rfl
  | get ℓ => rfl
  | put ℓ v => rfl
  | fail => rfl
  | oracleCall op dom codom x => rfl
  | embed c => rfl

/-- Substituting into `fail` gives `fail`. -/
@[simp]
theorem substOracle_fail {α : Type u}
    (env : ∀ (op : ℕ) (dom codom : Type u), dom → RawCode codom) :
    (@RawCode.fail α).substOracle env = .fail := rfl

/-- Substituting into `ret` gives `ret`. -/
@[simp]
theorem substOracle_ret {α : Type u} (a : α)
    (env : ∀ (op : ℕ) (dom codom : Type u), dom → RawCode codom) :
    (RawCode.ret a).substOracle env = .ret a := rfl

/-- A predicate asserting that a `RawCode` tree contains no `oracleCall` nodes.

    Code satisfying `NoOracleCall` is self-contained: it does not depend on
    any oracle environment. This is a key property for reduction packages,
    where non-delegated operations are handled by code that never calls imports.

    All code produced by `G_core_package_construction` satisfies this predicate,
    since it has `imports := ∅`. -/
inductive NoOracleCall : {α : Type u} → RawCode α → Prop where
  | ret {α : Type u} (a : α) : NoOracleCall (.ret a)
  | bind {α β : Type u} {c : RawCode β} {k : β → RawCode α}
      (hc : NoOracleCall c) (hk : ∀ b, NoOracleCall (k b)) : NoOracleCall (.bind c k)
  | sample {T : Type u} [Fintype T] [Nonempty T] : NoOracleCall (.sample T)
  | get (ℓ : CatCrypt.Core.Location) : NoOracleCall (.get ℓ)
  | put (ℓ : CatCrypt.Core.Location) (v : ℓ.ty) : NoOracleCall (.put ℓ v)
  | fail {α : Type u} : NoOracleCall (@RawCode.fail α)
  | embed {α : Type u} (c : CatCrypt.Core.SPComp α) : NoOracleCall (.embed c)

/-- `substOracle` is a no-op on code without oracle calls.

    This is the foundational lemma for reduction package proofs:
    when the reduction delegates an operation to `G_core`'s impl (which
    has no oracle calls), the linking substitution doesn't change the code. -/
theorem substOracle_eq_self {α : Type u} {c : RawCode α}
    (h : NoOracleCall c) (env : ∀ (op : ℕ) (dom codom : Type u), dom → RawCode codom) :
    c.substOracle env = c := by
  induction h with
  | ret _ => rfl
  | bind _ _ ih_c ih_k =>
    simp only [substOracle, ih_c]; congr_funext
  | sample => rfl
  | get _ => rfl
  | put _ _ => rfl
  | fail => rfl
  | embed _ => rfl

end RawCode

/-! ## Location Registry

A location registry maps atoms to Core.Locations. This enables nominal
reasoning about code while maintaining compatibility with the evaluation
that uses Core.Location (with nat ids).

The registry ensures:
1. Each atom maps to a unique Core.Location id
2. The mapping is consistent (same atom always gives same id)
3. Types are preserved
-/

/-- A location registry maps atoms to Core.Location ids.
    This bridges the nominal (atom-based) and evaluation (nat-based) models. -/
structure LocRegistry where
  /-- Map from atom to Core.Location id -/
  atomToId : Atom → Nat
  /-- The mapping is injective: different atoms map to different ids -/
  injective : Function.Injective atomToId

namespace LocRegistry

/-- Default registry: atoms map directly to their underlying nat value -/
def default : LocRegistry where
  atomToId := Atom.val
  injective := fun _ _ h => Atom.ext h

instance : Inhabited LocRegistry := ⟨default⟩

/-- Two atoms with different values map to different ids -/
theorem atomToId_ne (reg : LocRegistry) (a₁ a₂ : Atom) (h : a₁ ≠ a₂) :
    reg.atomToId a₁ ≠ reg.atomToId a₂ := fun heq => h (reg.injective heq)

end LocRegistry

end CatCrypt.Deep
