/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Deep.RawCode
import CatCrypt.Core.Code
import CatCrypt.Prob.SDistr
import CatCrypt.Relational.Judgment
import CatCrypt.Package.RawPackage

/-!
# Interpretation from Deep to Shallow Embedding

This file defines the interpretation of the deep embedding (RawCode) into
the shallow embedding (SPComp). This bridges structural reasoning in the
deep embedding with probabilistic reasoning in the shallow embedding.

## Main definitions

* `RawCode.eval` - Interpret RawCode into SPComp
* `DeepRHoare` - Relational Hoare logic for deep embedding

## Theorems

* `eval_ret` - Evaluation respects pure
* `eval_bind` - Evaluation respects bind
* `eval_get` - Evaluation of get uses SPComp.get directly
* `eval_put` - Evaluation of put uses SPComp.set directly
* `eval_rHoare` - Deep relational judgments imply shallow ones

## Design rationale

The interpretation serves multiple purposes:

1. **Semantic interpretation**: Give meaning to deep code via the shallow embedding
2. **Soundness**: Show that structural transformations preserve semantics
3. **Completeness**: Any shallow computation can be represented deeply
4. **Bridging**: Connect structural proofs (deep) with distribution proofs (shallow)

## Unified Heap Model

Both the deep embedding (RawCode) and shallow embedding (SPComp) now use
the same heap model (Core.Heap) and location type (Core.Location). This
eliminates the need for any heap translation axioms.

The key insight is that RawCode.get and RawCode.put use Core.Location directly,
so evaluation is a simple mapping:
- `RawCode.get ℓ` evaluates to `SPComp.get ℓ` (with ULift for universe handling)
- `RawCode.put ℓ v` evaluates to `SPComp.set ℓ v` (returning ULift Unit)

## References

* CatCrypt: theories/Crypt/rhl_semantics/free_prot/free_prot_semantics.v
* [Benton et al., *Nominal CatCrypt*](https://eprint.iacr.org/2025/598)
-/

namespace CatCrypt.Deep

open CatCrypt.Core
open CatCrypt.Prob
open CatCrypt.Relational
open CatCrypt.Package

universe u v w

variable {α β γ : Type*}

/-! ## Evaluation: Deep to Shallow

The main interpretation function that gives semantics to deep code.
Since RawCode now uses Core.Location directly, no heap translation is needed.
-/

/-- Interpret a RawCode computation into the shallow SPComp monad.

    This is the semantic interpretation that gives meaning to deep code.
    Each constructor of RawCode is mapped to the corresponding SPComp operation.

    The interpretation is noncomputable because:
    1. Sample uses uniform distribution (noncomputable)
    2. Heap operations use classical choice for encoding/decoding

    Key insight: Since RawCode uses Core.Location directly, get and put
    operations map directly to SPComp.get and SPComp.set with no translation needed.
-/
noncomputable def RawCode.eval : {α : Type*} → RawCode α → SPComp α
  | _, .ret x => SPComp.pure x
  | _, .bind c f => c.eval.bind fun x => (f x).eval
  | _, @RawCode.sample T _ _ => @SPComp.sample T _ _
  | _, .get ℓ => SPComp.bind (SPComp.get ℓ) fun v => SPComp.pure ⟨v⟩
  | _, .put ℓ v => SPComp.bind (SPComp.set ℓ v) fun _ => SPComp.pure ⟨()⟩
  | _, .fail => SPComp.fail
  | _, .oracleCall _ _ _ _ => SPComp.fail

/-! ## Evaluation properties

These theorems show that evaluation preserves the monad structure and
basic operations.
-/

/-- Evaluation respects pure/return

    This is definitionally true from the definition of eval.
-/
@[simp]
theorem eval_ret {α : Type u} (x : α) : (RawCode.ret x).eval = SPComp.pure x := rfl

/-- Evaluation distributes over bind.

    This is a key property: evaluation is a monad morphism.
    Definitionally true from the definition of eval.
-/
@[simp]
theorem eval_bind {α β : Type u} (c : RawCode α) (f : α → RawCode β) :
    (RawCode.bind c f).eval = c.eval.bind (fun x => (f x).eval) := rfl

/-- Evaluation of sample gives uniform distribution

    Definitionally true from the definition of eval.
-/
@[simp]
theorem eval_sample {T : Type u} [Fintype T] [Nonempty T] :
    (@RawCode.sample T _ _).eval = @SPComp.sample T _ _ := rfl

/-- Evaluation of fail gives SPComp.fail

    Definitionally true from the definition of eval.
-/
@[simp]
theorem eval_fail {α : Type u} : (@RawCode.fail α).eval = SPComp.fail := rfl

/-- Evaluation of oracle call gives SPComp.fail (unlinked oracle)

    Oracle calls that haven't been substituted (via `substOracle` / `link`)
    evaluate to failure. After linking, oracle calls are replaced with
    concrete implementations and this case never arises.
-/
@[simp]
theorem eval_oracleCall {op : ℕ} {dom codom : Type u} {x : dom} :
    (RawCode.oracleCall op dom codom x).eval = SPComp.fail := rfl

/-- Evaluation of get reads from the heap and lifts to ULift.

    This is definitionally true from the definition of eval.
-/
@[simp]
theorem eval_get (ℓ : CatCrypt.Core.Location) :
    (RawCode.get ℓ).eval = SPComp.bind (SPComp.get ℓ) fun v => SPComp.pure ⟨v⟩ := rfl

/-- Evaluation of put writes to the heap and returns ULift Unit.

    This is definitionally true from the definition of eval.
-/
@[simp]
theorem eval_put (ℓ : CatCrypt.Core.Location) (v : ℓ.ty) :
    (RawCode.put ℓ v).eval = SPComp.bind (SPComp.set ℓ v) fun _ => SPComp.pure ⟨()⟩ := rfl

/-! ## Evaluation with Oracle Handler

`evalWith` generalizes `eval` by taking an oracle handler instead of
mapping all oracle calls to failure. This is the key definition for
stating that `substOracle` commutes with `eval`.
-/

/-- Interpret RawCode into SPComp, using a custom oracle handler.

    Like `eval`, but instead of mapping `oracleCall` to `SPComp.fail`,
    it calls the provided `oracle` function. This allows us to state
    the semantic correctness of `substOracle`:

      (code.substOracle env).eval = code.evalWith (fun op dom codom x => (env op dom codom x).eval)

    When `oracle` maps everything to `SPComp.fail`, this reduces to `eval`. -/
noncomputable def RawCode.evalWith
    (oracle : ∀ (op : ℕ) (dom codom : Type u), dom → SPComp codom) :
    {α : Type u} → RawCode α → SPComp α
  | _, .ret x => SPComp.pure x
  | _, .bind c f => (c.evalWith oracle).bind fun x => (f x).evalWith oracle
  | _, @RawCode.sample T _ _ => @SPComp.sample T _ _
  | _, .get ℓ => SPComp.bind (SPComp.get ℓ) fun v => SPComp.pure ⟨v⟩
  | _, .put ℓ v => SPComp.bind (SPComp.set ℓ v) fun _ => SPComp.pure ⟨()⟩
  | _, .fail => SPComp.fail
  | _, .oracleCall op dom codom x => oracle op dom codom x

/-- `evalWith` with the fail oracle is just `eval`. -/
@[simp]
theorem RawCode.evalWith_fail :
    ∀ {α : Type u} (c : RawCode α),
    c.evalWith (fun _ _ _ _ => SPComp.fail) = c.eval := by
  intro α c
  induction c with
  | ret _ => rfl
  | bind c f ih_c ih_f =>
    simp only [evalWith, eval, ih_c]; congr_funext
  | sample T => rfl
  | get ℓ => rfl
  | put ℓ v => rfl
  | fail => rfl
  | oracleCall _ _ _ _ => rfl

/-- `evalWith` on code without oracle calls equals `eval`, regardless of oracle handler.

    This is the semantic version of `substOracle_eq_self`: if the code never
    invokes any oracle, the oracle handler is irrelevant. -/
theorem RawCode.evalWith_eq_eval_no_oracle {α : Type u} {c : RawCode α}
    (h : RawCode.NoOracleCall c)
    (oracle : ∀ (op : ℕ) (dom codom : Type u), dom → SPComp codom) :
    c.evalWith oracle = c.eval := by
  induction h with
  | ret _ => rfl
  | bind _ _ ih_c ih_k =>
    simp only [evalWith, eval, ih_c]; congr_funext
  | sample => rfl
  | get _ => rfl
  | put _ _ => rfl
  | fail => rfl

/-! ### Correctness of substOracle

The central theorem: substituting oracle calls and then evaluating is the same
as evaluating with the oracle handler that evaluates the substituted code.
This is proved by structural induction on `RawCode`.
-/

/-- **Correctness of substOracle**: Evaluating code after oracle substitution
    is the same as evaluating the original code with an oracle handler that
    evaluates the substituted implementations.

    This is the key semantic theorem for package linking. It says that
    `substOracle` (a syntactic operation on the free monad) commutes with
    `eval` (the semantic interpretation):

    ```
    substOracle env ; eval  =  evalWith (eval ∘ env)
    ```

    The proof is by structural induction on `RawCode`. Each case is
    straightforward:
    - `ret`, `sample`, `get`, `put`, `fail`: `substOracle` preserves these,
      so both sides agree definitionally.
    - `bind c k`: by induction, the substitution distributes through bind.
    - `oracleCall op dom codom x`: `substOracle` replaces this with
      `env op dom codom x`, and `evalWith` applies the oracle handler,
      giving `(env op dom codom x).eval` on both sides. -/
theorem eval_substOracle {α : Type u} (c : RawCode α)
    (env : ∀ (op : ℕ) (dom codom : Type u), dom → RawCode codom) :
    (c.substOracle env).eval = c.evalWith (fun op dom codom x => (env op dom codom x).eval) := by
  induction c with
  | ret _ => rfl
  | bind c k ih_c ih_k =>
    simp only [RawCode.substOracle, RawCode.eval, RawCode.evalWith, ih_c]; congr_funext
  | sample T => rfl
  | get ℓ => rfl
  | put ℓ v => rfl
  | fail => rfl
  | oracleCall op dom codom x => rfl

/-! ## evalWith composition

The key theorem for link associativity: composing evalWith through
substOracle produces the same result as a single evalWith with
the composed handler. -/

/-- Composing evalWith through substOracle: evaluating substituted code with
    a handler is the same as evaluating the original code with a composed handler.

    This generalizes `eval_substOracle` by using an arbitrary handler instead of `eval`. -/
theorem evalWith_substOracle {α : Type u} (c : RawCode α)
    (env : ∀ (op : ℕ) (dom codom : Type u), dom → RawCode codom)
    (h : ∀ (op : ℕ) (dom codom : Type u), dom → SPComp codom) :
    (c.substOracle env).evalWith h =
    c.evalWith (fun op dom codom x => (env op dom codom x).evalWith h) := by
  induction c with
  | ret _ => rfl
  | bind c k ih_c ih_k =>
    simp only [RawCode.substOracle, RawCode.evalWith, ih_c]; congr_funext
  | sample T => rfl
  | get ℓ => rfl
  | put ℓ v => rfl
  | fail => rfl
  | oracleCall op dom codom x => rfl

/-- Two evalWith handlers that agree produce the same SPComp.

    This is useful for showing that two different oracle environments
    produce the same evaluation when they agree on all oracle calls. -/
theorem evalWith_congr {α : Type u} (c : RawCode α)
    (h₁ h₂ : ∀ (op : ℕ) (dom codom : Type u), dom → SPComp codom)
    (heq : ∀ op dom codom x, h₁ op dom codom x = h₂ op dom codom x) :
    c.evalWith h₁ = c.evalWith h₂ := by
  induction c with
  | ret _ => rfl
  | bind c k ih_c ih_k =>
    simp only [RawCode.evalWith, ih_c]; congr_funext
  | sample T => rfl
  | get ℓ => rfl
  | put ℓ v => rfl
  | fail => rfl
  | oracleCall op dom codom x => exact heq op dom codom x

/-- `substOracle` commutes with type casts (`▸`).

    When `h : α = β` and `c : RawCode β`, substituting oracles in the
    cast code `h ▸ c : RawCode α` is the same as casting the substituted code.
    Proof: `subst h` makes the cast trivial. -/
theorem RawCode.substOracle_cast {α β : Type u} (h : α = β) (c : RawCode β)
    (env : ∀ (op : ℕ) (dom codom : Type u), dom → RawCode codom) :
    (h ▸ c).substOracle env = h ▸ (c.substOracle env) := by subst h; rfl

/-- `eval` commutes with type casts.

    Evaluating cast code is the same as casting the evaluated result.
    Proof: `subst h` makes the cast trivial. -/
theorem RawCode.eval_cast {α β : Type u} (h : α = β) (c : RawCode β) :
    (h ▸ c : RawCode α).eval = h ▸ (c.eval : SPComp β) := by subst h; rfl

/-- `evalWith` commutes with type casts.

    Like `eval_cast` but for `evalWith` with a custom oracle handler.
    Proof: `subst h` makes the cast trivial. -/
theorem RawCode.evalWith_cast {α β : Type u} (h : α = β) (c : RawCode β)
    (oracle : ∀ (op : ℕ) (dom codom : Type u), dom → SPComp codom) :
    (h ▸ c : RawCode α).evalWith oracle = h ▸ (c.evalWith oracle : SPComp β) := by subst h; rfl

/-- `evalWith` for fail is just `SPComp.fail`. -/
@[simp]
theorem evalWith_fail_code {α : Type u}
    (h : ∀ (op : ℕ) (dom codom : Type u), dom → SPComp codom) :
    (@RawCode.fail α).evalWith h = SPComp.fail := rfl

/-! ## Relational Hoare logic for deep embedding

We define a relational Hoare logic for the deep embedding using the
shallow embedding's rHoare. Since both use Core.Heap, no translation is needed.
-/

/-- Relational precondition (on Core.Heap) -/
abbrev RPre := Heap → Heap → Prop

/-- Relational postcondition -/
abbrev RPost (α β : Type*) := α → Heap → β → Heap → Prop

/-- Relational Hoare logic for deep embedding.

    `DeepRHoare pre c₁ c₂ post` means:
    For all heap pairs (h₁, h₂) satisfying pre,
    after evaluating c₁ and c₂, the results satisfy post.

    This is defined semantically using the shallow embedding:
    we evaluate the deep code to shallow code and use the existing rHoare.
    Since both embeddings use Core.Heap, no heap translation is needed.
-/
noncomputable def DeepRHoare (pre : RPre) (c₁ c₂ : RawCode α) (post : RPost α α) : Prop :=
  rHoare pre c₁.eval c₂.eval post

/-- Deep relational judgments are exactly shallow relational judgments on evaluated code.

    This is the key soundness theorem: proving something in the deep embedding's
    rHoare is equivalent to proving it in the shallow embedding (after evaluation).

    The proof is immediate since DeepRHoare is defined in terms of rHoare.
-/
theorem eval_rHoare (c₁ c₂ : RawCode α)
    (pre : RPre) (post : RPost α α) :
    DeepRHoare pre c₁ c₂ post ↔ rHoare pre c₁.eval c₂.eval post := by
  rfl

/-! ## Package evaluation

Interpret deep packages to shallow packages.

NOTE: The new Package.lean uses a different structure with interfaces and ValidCode.
For now, we provide a simplified evaluation that focuses on the core concepts.
A full evaluation would need to handle interface matching and code validity.
-/

/-! ## Examples and Properties

The evaluation equations are now proved as theorems using `rfl`, since
the definition of `eval` directly matches these equalities:

- `(RawCode.ret x).eval = SPComp.pure x`
- `(RawCode.fail).eval = SPComp.fail`
- `(c.bind f).eval = c.eval.bind (fun x => (f x).eval)`
- `(@RawCode.sample T _ _).eval = @SPComp.sample T _ _`
- `(RawCode.get ℓ).eval = SPComp.bind (SPComp.get ℓ) fun v => SPComp.pure ⟨v⟩`
- `(RawCode.put ℓ v).eval = SPComp.bind (SPComp.set ℓ v) fun _ => SPComp.pure ⟨()⟩`

These are all marked with `@[simp]` for automatic simplification.
-/

example : (RawCode.ret 42).eval = SPComp.pure 42 := rfl

example : (@RawCode.fail Nat).eval = SPComp.fail := rfl

example (c : RawCode Nat) (f : Nat → RawCode Bool) :
    (c.bind f).eval = c.eval.bind (fun n => (f n).eval) := rfl

/-! ## Design Notes

### Unified Heap Model

The key insight that eliminates all heap translation axioms is using
Core.Location and Core.Heap directly in the deep embedding:

**Before (with axioms):**
- Deep: `CatCrypt.Deep.Location` (atom name + type)
- Deep: `DeepHeap` (heterogeneous, `∀ ℓ, Option ℓ.ty`)
- Shallow: `CatCrypt.Core.Location` (nat id + type)
- Shallow: `Heap` (homogeneous, `Nat → Nat` with encoding)
- Required 8 axioms for translation between the two heap models

**After (axiom-free):**
- Both: `CatCrypt.Core.Location` (nat id + type)
- Both: `Core.Heap` (homogeneous, `Nat → Nat` with encoding)
- Direct evaluation: `RawCode.get ℓ` → `SPComp.get ℓ`
- No translation axioms needed!

### Universe Handling

Since `Core.Location.ty : Type` (universe 0) but `RawCode : Type u → Type (u+1)`,
we use `ULift` to bridge the universes:
- `RawCode.get ℓ : RawCode (ULift.{u} ℓ.ty)`
- `RawCode.put ℓ v : RawCode (ULift.{u} Unit)`

The evaluation wraps values in `ULift.up` and unwraps with `.down` as needed.

### What Was Removed

The following axioms are no longer needed and have been deleted:
1. `atomToId` - Atom to Nat mapping
2. `deepLocToShallow` - Deep Location to Core Location
3. `deepToHeap_data` / `deepToHeap` - DeepHeap to Heap conversion
4. `heapToDeep_data` / `heapToDeep` - Heap to DeepHeap conversion
5. `heap_roundtrip_get` - Round-trip property for get
6. `heap_set_commute` - Commutativity of set across conversion
7. `eval_get_impl` - Axiom for get evaluation
8. `eval_put_impl` - Axiom for put evaluation
9. `DeepRHoare_syntactic` - Placeholder for syntactic judgment
10. `DeepRHoare_sound` - Placeholder for soundness proof
-/

end CatCrypt.Deep
