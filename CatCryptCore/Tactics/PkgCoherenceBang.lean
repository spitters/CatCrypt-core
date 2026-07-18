/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Tactics.PkgCoherence
import CatCryptCore.Tactics.SPNormalize
import CatCryptCore.Deep.Reflect
import CatCryptCore.Deep.Eval
import CatCryptCore.Deep.MonadNormalize

/-!
# Enhanced Package Coherence (`pkg_coherence!`)

Extends `pkg_coherence` with a leaf-level closer that reaches into the
deep embedding.

* **`sp_normalize_deep`** — extends the minimal `sp_normalize` (defined
  in `Tactics/SPNormalize.lean`) with `RawCode.eval` unfolding, so leaf
  goals over reified programs reduce to pure `SPComp` chains.

* **`pkg_coherence!`** — the composite: try `pkg_coherence`; if structural
  leaves survive, finish them with `sp_normalize_deep`.

## Where reflection helps

`pkg_coherence` by itself closes SMC structural coherence (associators,
unitors, braiding, `pair`/`fst`/`snd` laws) because the SMC on `PkgInterface`
is built on `Sum`-indexed families and every structural morphism reduces to
`Sum` case-analysis + `rfl`.  It does **not** close leaf obligations whose
`SPComp` bodies are related by non-definitional rewrites — typical symptoms
are `evalWith`-parameterized handlers, reified programs obtained via
`rawCode%`, or hand-written compositions involving `RawCode.substOracle`.
`pkg_coherence!` covers those by turning the leaf into a simp goal over the
deep-embedding evaluation semantics.
-/

set_option autoImplicit false

namespace CatCrypt.Tactics

open CatCrypt.Core CatCrypt.Deep

/-! ## Leaf-normalizer (deep variant) -/

/-- `sp_normalize` extended with `RawCode.eval` unfolding.  Use when a
    leaf SPComp goal involves a reified `(rawCode% …).eval` on either
    side, or more generally any `RawCode.eval` application over the six
    core constructors. -/
macro "sp_normalize_deep" : tactic =>
  `(tactic| (
    simp only [
      -- SPComp monad laws
      CatCrypt.Core.SPComp.pure_bind, CatCrypt.Core.SPComp.bind_pure,
      CatCrypt.Core.SPComp.bind_assoc, CatCrypt.Core.SPComp.fail_bind,
      -- RawCode evaluation (so goals over reified programs reduce to SPComp)
      CatCrypt.Deep.eval_ret, CatCrypt.Deep.eval_sample, CatCrypt.Deep.eval_fail,
      CatCrypt.Deep.eval_get, CatCrypt.Deep.eval_put,
      -- Monad-class redirection on SPComp
      CatCrypt.Core.SPComp.monad_bind_eq, CatCrypt.Core.SPComp.monad_pure_eq]
    <;> try rfl))

/-! ## Composite tactic -/

/-- Extended package-coherence tactic.

    Strategy:
    1. Try `rfl` (for trivially equal terms).
    2. Try `pkg_coherence` (SMC-structural equality via `funext` +
       `sum_cases` + handler simp + `rfl`).
    3. Fall back to `funext` + `sum_cases`, then close each leaf with the
       reflective `mon_coherence` (the ring/`monoidal`-coherence analog for
       the Kleisli bind — normal-form + one soundness lemma, `MonadNormalize`),
       and only if that misses, the `sp_normalize_deep` simp. `mon_coherence`
       discharges the non-definitional bind assoc/unit on concrete reified
       spines by `rfl` on normal forms, replacing the step-by-step simp. -/
macro "pkg_coherence!" : tactic =>
  `(tactic| (
    first
    | rfl
    | pkg_coherence
    | (funext _
       sum_cases
       all_goals (first | rfl | mon_coherence | sp_normalize_deep))
    | (funext _ _
       sum_cases
       all_goals (first | rfl | mon_coherence | sp_normalize_deep))))

end CatCrypt.Tactics

/-! ## Test suite -/

section PkgCoherenceBangTests

open CatCrypt.Core CatCrypt.Deep

-- Pure monad laws on SPComp (minimal sp_normalize from Tactics/SPNormalize).

example {α : Type} (a : α) :
    SPComp.bind (SPComp.pure a) SPComp.pure = (SPComp.pure a : SPComp α) := by
  sp_normalize

example {α β : Type} (a : α) (f : α → SPComp β) :
    SPComp.bind (SPComp.pure a) f = f a := by
  sp_normalize

-- RawCode round-trip: the deep variant handles `(rawCode% prog).eval`.

example {α : Type} (a : α) :
    (rawCode% (SPComp.pure a : SPComp α)).eval = SPComp.pure a := by
  sp_normalize_deep

-- pkg_coherence! subsumes pkg_coherence on the earlier examples.

open CatCrypt.Category CategoryTheory

variable {I J : PkgInterface}

example (f : I ⟶ J) (h : TypedHandler I) :
    (𝟙 I ≫ f) h = f h := by pkg_coherence!

example (h : TypedHandler (I.tensor J)) :
    TypedHandler.pair h.fst h.snd = h := by pkg_coherence!

end PkgCoherenceBangTests
