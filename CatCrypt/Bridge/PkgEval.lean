/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Category.PkgFam
import CatCrypt.Deep.Eval
import CatCrypt.Crypto.NomAdvantage

/-!
# Evaluation Bridge: DeepPackage → PkgImpl

This file bridges `DeepPackage` (syntactic, oracle-based) to `PkgImpl` (semantic,
SPComp morphisms in Fam(KlSPComp)) via the existing `RawCode.eval` infrastructure.

## Key insight

`DeepPackage.link` performs syntactic oracle substitution (replacing `oracleCall`
nodes with implementations from another package), while `PkgImpl` composition
uses Kleisli bind. The theorem `eval_substOracle` connects these:

    (code.substOracle env).eval = code.evalWith (eval ∘ env)

## Main definitions

* `oracleHandler` — semantic oracle handler from a package's exports
* `evalImpl` — evaluate a closed DeepPackage to a PkgImpl
* `evalImplWith` — evaluate with a custom oracle handler

## Main theorems

* `evalImpl_link` — linking corresponds to evalWith with oracleHandler
* `evalImpl_par_eval_left/right` — parallel composition dispatches correctly
* `runPkg_eq_eval` — connects runPkg to the eval bridge
-/

namespace CatCrypt.Bridge

open CatCrypt.Core CatCrypt.Deep CatCrypt.Category CatCrypt.Crypto

/-! ## Oracle Handler -/

/-- Semantic oracle handler from a package's exports.
    For each operation `(op, dom, codom)`:
    - If exported, evaluate the implementation via `RawCode.eval`
    - Otherwise, return `SPComp.fail` -/
noncomputable def oracleHandler (p : DeepPackage) :
    ∀ (op : ℕ) (dom codom : Type), dom → SPComp codom :=
  fun op dom codom x =>
    have := Classical.dec ((op, dom, codom) ∈ p.exports.ops)
    if h : (op, dom, codom) ∈ p.exports.ops
    then (p.impl op dom codom h x).code.eval
    else SPComp.fail

/-- The oracle handler equals evaluating the linkEnv at every operation. -/
theorem oracleHandler_eq_linkEnv_eval (p : DeepPackage)
    (op : ℕ) (dom codom : Type) (x : dom) :
    oracleHandler p op dom codom x = (DeepPackage.linkEnv p op dom codom x).eval := by
  simp only [oracleHandler, DeepPackage.linkEnv]
  split
  · rfl
  · rfl

/-! ## Evaluate DeepPackage to PkgImpl -/

/-- Evaluate a closed DeepPackage to a PkgImpl.
    Each exported operation (indexed by `Fin`) is evaluated via `RawCode.eval`.
    Unresolved oracle calls become `SPComp.fail`. -/
noncomputable def evalImpl (p : DeepPackage) :
    PkgImpl (DeepInterface.toPkgInterface p.exports) :=
  PkgImpl.ofImpls _ fun i x =>
    (p.impl (p.exports.ops.get i).1 (p.exports.ops.get i).2.1 (p.exports.ops.get i).2.2
      (List.get_mem p.exports.ops i) x).code.eval

/-- Evaluate a DeepPackage with a custom oracle handler. -/
noncomputable def evalImplWith (p : DeepPackage)
    (oracle : ∀ (op : ℕ) (dom codom : Type), dom → SPComp codom) :
    PkgImpl (DeepInterface.toPkgInterface p.exports) :=
  PkgImpl.ofImpls _ fun i x =>
    (p.impl (p.exports.ops.get i).1 (p.exports.ops.get i).2.1 (p.exports.ops.get i).2.2
      (List.get_mem p.exports.ops i) x).code.evalWith oracle

/-! ## Helper Lemmas -/

/-- The linked package's impl code is the substOracle of the first package's code.
    This is definitionally true from the definitions of `link` and `linkEnv`. -/
theorem link_impl_code (p₁ p₂ : DeepPackage)
    (op : ℕ) (dom codom : Type) (h : (op, dom, codom) ∈ p₁.exports.ops) (x : dom) :
    ((DeepPackage.link p₁ p₂).impl op dom codom h x).code =
    (p₁.impl op dom codom h x).code.substOracle (DeepPackage.linkEnv p₂) := rfl

/-! ## Link Correctness -/

/-- **Link correctness**: evaluating a linked package equals evaluating the first
    package with the second's oracle handler.

    This connects `DeepPackage.link` (syntactic `substOracle`) to semantic
    oracle resolution (`evalWith`). -/
theorem evalImpl_link (p₁ p₂ : DeepPackage) :
    evalImpl (DeepPackage.link p₁ p₂) = evalImplWith p₁ (oracleHandler p₂) := by
  apply FamObj.fam_ext
  · rfl
  · intro i; apply heq_of_eq; funext x
    simp only [evalImpl, evalImplWith, PkgImpl.ofImpls, DeepPackage.link]
    rw [eval_substOracle]
    apply evalWith_congr
    intro op dom codom y
    exact (oracleHandler_eq_linkEnv_eval p₂ op dom codom y).symm

/-! ## Par Correctness -/

/-- Parallel composition dispatches left operations to the left package at eval level. -/
theorem evalImpl_par_eval_left (p₁ p₂ : DeepPackage) (h_sep : DeepPackage.sep p₁ p₂)
    (op : ℕ) (dom codom : Type)
    (h₁ : (op, dom, codom) ∈ p₁.exports.ops)
    (h_par : (op, dom, codom) ∈ (DeepPackage.par p₁ p₂ h_sep).exports.ops)
    (x : dom) :
    ((DeepPackage.par p₁ p₂ h_sep).impl op dom codom h_par x).code.eval =
    (p₁.impl op dom codom h₁ x).code.eval := by
  congr 1
  exact DeepPackage.par_impl_code_eq_left p₁ p₂ h_sep op dom codom h₁ h_par x

/-- Parallel composition dispatches right operations to the right package at eval level. -/
theorem evalImpl_par_eval_right (p₁ p₂ : DeepPackage) (h_sep : DeepPackage.sep p₁ p₂)
    (op : ℕ) (dom codom : Type)
    (h₁ : (op, dom, codom) ∉ p₁.exports.ops)
    (h₂ : (op, dom, codom) ∈ p₂.exports.ops)
    (h_par : (op, dom, codom) ∈ (DeepPackage.par p₁ p₂ h_sep).exports.ops)
    (x : dom) :
    ((DeepPackage.par p₁ p₂ h_sep).impl op dom codom h_par x).code.eval =
    (p₂.impl op dom codom h₂ x).code.eval := by
  congr 1
  exact DeepPackage.par_impl_code_eq_right p₁ p₂ h_sep op dom codom h₁ h₂ h_par x

/-! ## runPkg Connection -/

/-- `runPkg` computes the evaluation of the main `(0, Unit, Bool)` operation. -/
theorem runPkg_eq_eval (p : DeepPackage)
    (h : (0, Unit, Bool) ∈ p.exports.ops) :
    runPkg p = (p.impl 0 Unit Bool h ()).code.eval := by
  simp only [runPkg, h, dite_true]

/-! ## Functoriality: Identity Laws -/

/-- `evalImplWith` with the fail handler equals `evalImpl`.
    Since `evalWith (fun _ _ _ _ => fail) = eval`, this is pointwise true. -/
theorem evalImplWith_fail (p : DeepPackage) :
    evalImplWith p (fun _ _ _ _ => SPComp.fail) = evalImpl p := by
  apply FamObj.fam_ext
  · rfl
  · intro i; apply heq_of_eq; funext x
    simp only [evalImplWith, evalImpl, PkgImpl.ofImpls]
    exact RawCode.evalWith_fail _

/-- The oracle handler of the identity package is always `SPComp.fail`.
    The id package forwards all ops as `oracleCall`, which evaluates to fail. -/
theorem oracleHandler_id (I : DeepInterface)
    (op : ℕ) (dom codom : Type) (x : dom) :
    oracleHandler (DeepPackage.id I) op dom codom x = SPComp.fail := by
  simp only [oracleHandler, DeepPackage.id]
  split
  · simp [RawCode.eval]
  · rfl

/-- **Right identity**: linking with the identity package preserves evalImpl.

    `evalImpl (link p (id p.imports)) = evalImpl p`

    The id package's oracle handler maps everything to fail, which is the
    same behavior as unresolved oracle calls in `eval`. -/
theorem evalImpl_link_id_right (p : DeepPackage) :
    evalImpl (DeepPackage.link p (DeepPackage.id p.imports)) = evalImpl p := by
  rw [evalImpl_link]
  -- evalImplWith p (oracleHandler (id p.imports)) = evalImpl p
  -- oracleHandler of id is fail, so this reduces to evalImplWith_fail
  have : oracleHandler (DeepPackage.id p.imports) = fun _ _ _ _ => SPComp.fail := by
    funext op dom codom x
    exact oracleHandler_id p.imports op dom codom x
  rw [this]
  exact evalImplWith_fail p

/-- **Left identity**: linking the identity package on the left preserves evalImpl.

    `evalImpl (link (id p.exports) p) = evalImpl p`

    The id package's code is `oracleCall`, which after substOracle with p's
    linkEnv becomes p's implementation (when the operation is exported). -/
theorem evalImpl_link_id_left (p : DeepPackage) :
    evalImpl (DeepPackage.link (DeepPackage.id p.exports) p) = evalImpl p := by
  apply FamObj.fam_ext
  · rfl
  · intro i; apply heq_of_eq; funext x
    simp only [evalImpl, PkgImpl.ofImpls, DeepPackage.link, DeepPackage.id]
    -- Code is (oracleCall op dom codom x).substOracle(linkEnv p)
    -- = linkEnv p op dom codom x (by substOracle on oracleCall)
    simp only [RawCode.substOracle]
    -- The dite resolves positively since the operation IS in p.exports.ops
    simp

/-! ## Functoriality: Associativity -/

/-- **Link associativity** at the evalImpl level.

    `evalImpl (link (link p₁ p₂) p₃) = evalImpl (link p₁ (link p₂ p₃))`

    Syntactically, `link (link p₁ p₂) p₃ ≠ link p₁ (link p₂ p₃)` because
    double substOracle differs from single substOracle with composed env.
    But semantically (after `eval`), both agree because:
    - Left: `(code.substOracle(env₂).substOracle(env₃)).eval`
    - Right: `code.substOracle(env_{link p₂ p₃}).eval`
    - Both equal `code.evalWith(handler)` for the same handler.

    This generalizes `runPkg_link_assoc` from the main operation to all operations. -/
theorem evalImpl_link_assoc (p₁ p₂ p₃ : DeepPackage) :
    evalImpl (DeepPackage.link (DeepPackage.link p₁ p₂) p₃) =
    evalImpl (DeepPackage.link p₁ (DeepPackage.link p₂ p₃)) := by
  apply FamObj.fam_ext
  · rfl
  · intro i; apply heq_of_eq; funext x
    simp only [evalImpl, PkgImpl.ofImpls, DeepPackage.link]
    -- LHS: ((code.substOracle env₂).substOracle env₃).eval
    -- RHS: (code.substOracle env_{link p₂ p₃}).eval
    -- Step 1: Rewrite LHS via substOracle_comp
    conv_lhs => simp only [RawCode.substOracle_comp]
    -- Step 2: Convert both sides to evalWith form
    rw [eval_substOracle, eval_substOracle]
    -- Step 3: Show handlers agree
    apply evalWith_congr
    intro op dom codom y
    -- LHS handler: (linkEnv p₂ op dom codom y).substOracle(linkEnv p₃) |>.eval
    -- RHS handler: linkEnv (link p₂ p₃) op dom codom y |>.eval
    -- Case split on whether op is in p₂.exports
    have := Classical.dec ((op, dom, codom) ∈ p₂.exports.ops)
    by_cases h₂ : (op, dom, codom) ∈ p₂.exports.ops
    · -- In p₂.exports: both give (p₂.impl.code.substOracle(linkEnv p₃)).eval
      simp [h₂]
    · -- Not in p₂.exports: both give fail.eval = SPComp.fail
      simp [h₂]

/-! ## Typed Semantic Packages

A `SemPkg` is a semantic package at the SPComp level. It maps oracle handlers
to oracle handlers: given implementations for import operations, it produces
implementations for export operations.

`SemPkg` forms a proper category (with function composition as linking),
and `evalImpl` factors through it cleanly, avoiding the need for quotienting
`DeepPackage` by eval-equivalence.
-/

/-- Untyped oracle handler: provides SPComp implementations for any operation
    identified by `(op : ℕ, dom : Type, codom : Type)`. -/
abbrev Handler := ∀ (op : ℕ) (dom codom : Type), dom → SPComp codom

/-- The trivial handler that maps all operations to failure. -/
noncomputable def Handler.fail : Handler := fun _ _ _ _ => SPComp.fail

/-- A semantic typed package: a function from import oracle handlers to export
    oracle handlers. The interface parameters `I_imp` and `I_exp` track which
    operations are imported and exported.

    This forms a category with function composition as linking:
    - Identity: the handler that passes operations through unchanged
    - Composition: `(g.comp f).resolve oracle = g.resolve (f.resolve oracle)` -/
structure SemPkg (I_imp I_exp : DeepInterface) where
  /-- Given an oracle handler (resolving imports), produce an oracle handler
      (providing exports). -/
  resolve : Handler → Handler

@[ext]
theorem SemPkg.ext {I_imp I_exp : DeepInterface}
    {s₁ s₂ : SemPkg I_imp I_exp} (h : s₁.resolve = s₂.resolve) :
    s₁ = s₂ := by
  cases s₁; cases s₂; congr

namespace SemPkg

variable {I_imp I_exp I_mid I₁ I₂ I₃ : DeepInterface}

/-- Identity semantic package: passes the handler through unchanged. -/
noncomputable def id (I : DeepInterface) : SemPkg I I where
  resolve := _root_.id

/-- Composition of semantic packages: resolve imports of `g` through `f`. -/
noncomputable def comp (g : SemPkg I_mid I_exp) (f : SemPkg I_imp I_mid) :
    SemPkg I_imp I_exp where
  resolve oracle := g.resolve (f.resolve oracle)

@[simp] theorem id_resolve (I : DeepInterface) (h : Handler) :
    (SemPkg.id I).resolve h = h := rfl

@[simp] theorem comp_resolve (g : SemPkg I_mid I_exp) (f : SemPkg I_imp I_mid)
    (h : Handler) :
    (g.comp f).resolve h = g.resolve (f.resolve h) := rfl

/-- Composition is associative. -/
theorem comp_assoc (h : SemPkg I₃ I_exp) (g : SemPkg I₂ I₃) (f : SemPkg I₁ I₂) :
    h.comp (g.comp f) = (h.comp g).comp f := rfl

/-- Left identity for composition. -/
theorem id_comp (f : SemPkg I_imp I_exp) :
    (SemPkg.id I_exp).comp f = f := rfl

/-- Right identity for composition. -/
theorem comp_id (f : SemPkg I_imp I_exp) :
    f.comp (SemPkg.id I_imp) = f := rfl

end SemPkg

/-! ## DeepPackage → SemPkg -/

/-- Convert a DeepPackage to a semantic package.
    For each operation in the exports, evaluates the implementation
    with the given oracle handler. Non-exported operations return fail. -/
noncomputable def toSemPkg (p : DeepPackage) :
    SemPkg p.imports p.exports where
  resolve oracle op dom codom x :=
    have := Classical.dec ((op, dom, codom) ∈ p.exports.ops)
    if h : (op, dom, codom) ∈ p.exports.ops
    then (p.impl op dom codom h x).code.evalWith oracle
    else SPComp.fail

/-- `toSemPkg` with the fail handler gives the same as `oracleHandler`.
    Both evaluate the code, but `oracleHandler` uses `eval` (= `evalWith fail`). -/
theorem toSemPkg_fail (p : DeepPackage) :
    (toSemPkg p).resolve Handler.fail = oracleHandler p := by
  funext op dom codom x
  simp only [toSemPkg, oracleHandler]
  split
  · exact RawCode.evalWith_fail _
  · rfl

/-- **`toSemPkg` preserves linking** (pointwise): evaluating a linked package
    is the same as composing the semantic handlers.

    For any oracle handler `oracle` and operation `(op, dom, codom)`:
    `toSemPkg(link p₁ p₂).resolve oracle = toSemPkg(p₁).resolve(toSemPkg(p₂).resolve oracle)`

    This is the fundamental functoriality theorem. It follows from
    `evalWith_substOracle`: oracle substitution composes with evalWith. -/
theorem toSemPkg_link (p₁ p₂ : DeepPackage)
    (oracle : Handler) (op : ℕ) (dom codom : Type) (x : dom) :
    (toSemPkg (DeepPackage.link p₁ p₂)).resolve oracle op dom codom x =
    (toSemPkg p₁).resolve ((toSemPkg p₂).resolve oracle) op dom codom x := by
  simp only [toSemPkg, DeepPackage.link]
  split
  · next h =>
    rw [evalWith_substOracle]
    apply evalWith_congr
    intro op' dom' codom' y
    split <;> rfl
  · rfl

/-- `toSemPkg` preserves identity for exported operations.

    For operations in `I.ops`, `toSemPkg (id I)` acts as the identity handler.
    (For operations NOT in `I.ops`, `toSemPkg (id I)` returns fail, since
    `DeepPackage.id I` only forwards operations declared in `I`.) -/
theorem toSemPkg_id_mem (I : DeepInterface)
    (oracle : Handler) (op : ℕ) (dom codom : Type) (x : dom)
    (h : (op, dom, codom) ∈ I.ops) :
    (toSemPkg (DeepPackage.id I)).resolve oracle op dom codom x =
    oracle op dom codom x := by
  simp only [toSemPkg, DeepPackage.id, h, dite_true, RawCode.evalWith]

/-! ## Category Instance for DeepInterface

`SemPkg` satisfies the axioms of a Mathlib `Category` on `DeepInterface` objects:
- `Hom I J := SemPkg I J` (semantic packages as morphisms)
- Composition is diagrammatic: `f ≫ g = g.comp f` (apply f first, then g)
- Identity and associativity follow from `SemPkg.id_comp`, `SemPkg.comp_id`, `SemPkg.comp_assoc`

This gives access to `≫` notation, `Category.assoc`, and categorical tactics. -/

open CategoryTheory in
noncomputable instance : Category DeepInterface where
  Hom I J := SemPkg I J
  id I := SemPkg.id I
  comp f g := g.comp f
  id_comp f := SemPkg.comp_id f
  comp_id f := SemPkg.id_comp f
  assoc f g h := SemPkg.comp_assoc h g f

end CatCrypt.Bridge
