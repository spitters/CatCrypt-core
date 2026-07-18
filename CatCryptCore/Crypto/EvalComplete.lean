/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Deep.Eval
import CatCryptCore.Deep.Package

/-!
# Eval Completeness: Embedding `SPComp` into `RawCode`

The `embed` constructor of `RawCode` embeds an arbitrary `SPComp α` computation
into `RawCode α`, making `eval : RawCode α → SPComp α` surjective. This file
packages that constructor as `RawCode.ofSPComp` together with the equations
witnessing that the deep embedding (syntactic free monad) can represent any
computation expressible in the shallow embedding (semantic domain).

## Main results

* `RawCode.ofSPComp` — embeds any `SPComp α` into `RawCode α`
* `RawCode.ofSPComp_eval` — `eval ∘ ofSPComp = id` (right inverse of eval)
* `RawCode.substOracle_ofSPComp` — `ofSPComp` code is invariant under oracle substitution
* `ValidCode.ofSPComp` — `ofSPComp` code is valid for any location set
* `RawCode.ofSPComp_evalWith` — `evalWith` on `ofSPComp` ignores the handler
* `ValidCodeBundle.ofSPComp` — the bundled valid-code witness

**Rewinding warning**: because `embed` can represent *any* `SPComp` — including
state-resetting operations like `heapReset` (which discards the current heap and
replaces it with a saved snapshot) — it enables rewinding adversaries. This is
what makes the `nomPkg_absorb` construction go through, but it is **unsound in
quantum UC** due to no-cloning. For quantum-safe results, use the `IsPure + NoFail`
path (`sdist_of_deepNomAdvantage`), which does not depend on these definitions.
-/

namespace CatCrypt.Deep

open CatCrypt.Core CatCrypt.Prob

/-! ## Embedding `SPComp` into `RawCode` -/

/-- Embed an arbitrary `SPComp` into `RawCode`.
    This is the right inverse of `eval : RawCode α → SPComp α`. -/
@[match_pattern]
def RawCode.ofSPComp {α : Type} (c : SPComp α) : RawCode α := RawCode.embed c

/-- `ofSPComp` is a right inverse of `eval`.
    Evaluating the embedded code recovers the original computation. -/
@[simp]
theorem RawCode.ofSPComp_eval {α : Type} (c : SPComp α) :
    (RawCode.ofSPComp c).eval = c := rfl

/-- `ofSPComp` produces code that is invariant under oracle substitution.
    Since the embedded code represents a closed computation (no external
    oracle dependencies), substituting oracles has no effect. -/
@[simp]
theorem RawCode.substOracle_ofSPComp {α : Type} (c : SPComp α)
    (env : ∀ (op : ℕ) (dom codom : Type), dom → RawCode codom) :
    (RawCode.ofSPComp c).substOracle env = RawCode.ofSPComp c := rfl

/-- `ofSPComp` code is valid for any location set.
    Since the embedded code's heap access pattern is opaque, the
    `ValidCode.embed` constructor declares it valid for any location set. -/
theorem ValidCode.ofSPComp {α : Type} (c : SPComp α) (L : LocSet) :
    ValidCode L α (RawCode.ofSPComp c) :=
  ValidCode.embed c

/-! ## Derived Results -/

/-- `evalWith` on `ofSPComp` ignores the oracle handler.
    Since `ofSPComp` has no oracle calls, the handler is irrelevant. -/
theorem RawCode.ofSPComp_evalWith {α : Type} (c : SPComp α)
    (handler : ∀ (op : ℕ) (dom codom : Type), dom → SPComp codom) :
    (RawCode.ofSPComp c).evalWith handler = c := by
  -- Construct env such that (env · · · ·).eval = handler
  let env : ∀ (op : ℕ) (dom codom : Type), dom → RawCode codom :=
    fun op dom codom x => RawCode.ofSPComp (handler op dom codom x)
  -- Use eval_substOracle: (c.substOracle env).eval = c.evalWith env.eval
  have h1 := eval_substOracle (RawCode.ofSPComp c) env
  -- By substOracle_ofSPComp: LHS simplifies to (ofSPComp c).eval
  rw [substOracle_ofSPComp] at h1
  -- By ofSPComp_eval: (ofSPComp c).eval = c
  rw [ofSPComp_eval] at h1
  -- h1 : c = (ofSPComp c).evalWith (fun op dom codom x => (env op dom codom x).eval)
  -- Simplify env.eval = handler
  have h2 : (fun op dom codom x => (env op dom codom x).eval) = handler := by
    funext op dom codom x; exact ofSPComp_eval _
  rw [h2] at h1
  exact h1.symm

/-- `ValidCodeBundle` from `ofSPComp`, for constructing `DeepPackage` implementations. -/
noncomputable def ValidCodeBundle.ofSPComp {α : Type} (c : SPComp α) (L : LocSet) :
    ValidCodeBundle L α :=
  ⟨RawCode.ofSPComp c, CatCrypt.Deep.ValidCode.ofSPComp c L⟩

end CatCrypt.Deep
