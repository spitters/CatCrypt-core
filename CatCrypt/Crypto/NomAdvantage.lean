/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Advantage
import CatCrypt.Deep.Package
import CatCrypt.Deep.Eval

/-!
# Nominal Advantage

This file defines advantage for nominal packages via the deep embedding.

`DeepNomAdvantage` uses `DeepPackage.link` for actual oracle substitution
via `RawCode.substOracle`, enabling adversary-game composition.

## Main definitions

* `runPkg` - Evaluate a `DeepPackage`'s main export `(0, Unit, Bool)`
* `DeepNomAdvantage` - Distinguishing probability with adversary composition
* `NomPkgSecure` - Adversary-dependent game-based security

## References

* [Benton et al., *Nominal SSProve*](https://eprint.iacr.org/2025/598)
-/

namespace CatCrypt.Crypto

open CatCrypt.Core CatCrypt.Prob
open scoped ENNReal

/-! ## Running deep packages -/

/-- Run a deep package by evaluating its "main" exported operation.

    Convention: the main entry point is export operation `(0, Unit, Bool)`.
    This mirrors the cryptographic game convention where the adversary's
    main procedure takes no input and returns a boolean guess.

    If the package exports `(0, Unit, Bool)`, we evaluate the corresponding
    `RawCode Bool` via `RawCode.eval` to get an `SPComp Bool`.
    Otherwise, the package has no main entry point and we return `pure true`.

    In the adversary-composition model:
    - The adversary `A` exports `(0, Unit, Bool)` (its `main` procedure)
    - The adversary imports operations from the game `G`
    - `DeepPackage.link A.pkg G.pkg` resolves A's oracle calls via G's exports
    - `runPkg` evaluates the linked adversary's main procedure -/
noncomputable def runPkg (p : CatCrypt.Deep.DeepPackage) : SPComp Bool :=
  have := Classical.dec ((0, Unit, Bool) ∈ p.exports.ops)
  if h : (0, Unit, Bool) ∈ p.exports.ops then
    let vc := p.impl 0 Unit Bool h ()
    vc.code.eval
  else
    SPComp.pure true

/-- Run a deep nominal package by delegating to `runPkg` on the underlying
    `DeepPackage`. The nominal structure (registry, atoms) is used only for
    separation reasoning, not for evaluation. -/
noncomputable def runDeep (p : CatCrypt.Deep.NomPackage) : SPComp Bool :=
  runPkg p.pkg

/-- Advantage on deep nominal packages with adversary composition.

    `DeepNomAdvantage G G' A` measures how well adversary `A` can distinguish
    game `G` from game `G'`:

    `DeepNomAdvantage G G' A = |Pr[eval(A ∥ G) => 1] - Pr[eval(A ∥ G') => 1]|`

    The adversary `A` is linked with each game via `DeepPackage.link`:
    - `A.pkg` exports the main procedure `(0, Unit, Bool)`
    - `A.pkg` imports operations that `G.pkg` / `G'.pkg` export
    - Linking resolves A's oracle calls with G's (resp. G's) implementations
    - `runPkg` evaluates the linked package's main procedure

    The atom separation between A and G/G' is an implicit precondition for
    meaningful security statements. -/
noncomputable def DeepNomAdvantage
    (G G' A : CatCrypt.Deep.NomPackage) : ℝ≥0∞ :=
  Advantage (runPkg (CatCrypt.Deep.DeepPackage.link A.pkg G.pkg))
            (runPkg (CatCrypt.Deep.DeepPackage.link A.pkg G'.pkg))

/-- Triangle inequality for deep nominal advantage. -/
theorem DeepNomAdvantage_triangle
    (G₁ G₂ G₃ A : CatCrypt.Deep.NomPackage) :
    DeepNomAdvantage G₁ G₃ A ≤
      DeepNomAdvantage G₁ G₂ A + DeepNomAdvantage G₂ G₃ A := by
  simp only [DeepNomAdvantage]
  exact advantage_triangle _ _ _

/-- Self-advantage is zero for deep nominal packages. -/
theorem DeepNomAdvantage_self (G A : CatCrypt.Deep.NomPackage) :
    DeepNomAdvantage G G A = 0 := by
  simp only [DeepNomAdvantage]
  exact Advantage_self _

/-- Deep nominal advantage is symmetric. -/
theorem DeepNomAdvantage_comm (G G' A : CatCrypt.Deep.NomPackage) :
    DeepNomAdvantage G G' A = DeepNomAdvantage G' G A := by
  simp only [DeepNomAdvantage, Advantage]
  rw [max_comm]

/-- **Advantage equality under runPkg equivalence.**

    If two game pairs produce the same `SPComp Bool` when linked with adversary A,
    then they have the same advantage. This is the key lemma for code equivalence
    proofs: show that `runPkg (link A G₀)` = `runPkg (link A G₀')` (and similarly
    for G₁/G₁'), then conclude the advantages are equal.

    Typical use: after showing that G₀ and G₀' have the same oracle implementations
    via `runPkg_link_congr`, apply this lemma to rewrite the advantage. -/
theorem DeepNomAdvantage_runPkg_eq
    (G₀ G₁ G₀' G₁' A : CatCrypt.Deep.NomPackage)
    (h₀ : runPkg (CatCrypt.Deep.DeepPackage.link A.pkg G₀.pkg) =
           runPkg (CatCrypt.Deep.DeepPackage.link A.pkg G₀'.pkg))
    (h₁ : runPkg (CatCrypt.Deep.DeepPackage.link A.pkg G₁.pkg) =
           runPkg (CatCrypt.Deep.DeepPackage.link A.pkg G₁'.pkg)) :
    DeepNomAdvantage G₀ G₁ A = DeepNomAdvantage G₀' G₁' A := by
  simp only [DeepNomAdvantage]
  rw [h₀, h₁]

/-- **Advantage equality when games are NomPackage-equal.**

    A corollary of `DeepNomAdvantage_runPkg_eq` for the common case where
    the games are literally equal as `NomPackage` values. -/
theorem DeepNomAdvantage_congr
    (G₀ G₁ G₀' G₁' A : CatCrypt.Deep.NomPackage)
    (h₀ : G₀ = G₀') (h₁ : G₁ = G₁') :
    DeepNomAdvantage G₀ G₁ A = DeepNomAdvantage G₀' G₁' A := by
  subst h₀; subst h₁; rfl

/-! ## Linking Correctness

The foundational theorem connecting `DeepPackage.link` with `RawCode.eval`:
running a linked package is the same as running the first package's main
procedure with oracle calls resolved through the second package.
-/

open CatCrypt.Deep in
/-- **Correctness of package linking with respect to evaluation.**

    Running a linked package `runPkg (link p₁ p₂)` is equivalent to
    evaluating p₁'s main procedure `(0, Unit, Bool)` with an oracle handler
    that resolves oracle calls through p₂:

    - If `(op, dom, codom)` is in p₂'s exports, the oracle call is replaced
      by evaluating p₂'s implementation.
    - Otherwise, the oracle call evaluates to `SPComp.fail`.

    This theorem is the semantic justification for `DeepNomAdvantage`:
    it shows that `DeepPackage.link` (a syntactic operation on the free monad)
    correctly implements oracle resolution at the semantic level (`SPComp`).

    **Proof**: Unfolds `runPkg` and `DeepPackage.link`, then applies
    `eval_substOracle` which proves the commutativity of `substOracle`
    with `eval` by structural induction on `RawCode`. -/
theorem runPkg_link (p₁ p₂ : CatCrypt.Deep.DeepPackage) :
    runPkg (CatCrypt.Deep.DeepPackage.link p₁ p₂) =
    (have := Classical.dec ((0, Unit, Bool) ∈ p₁.exports.ops)
     if h : (0, Unit, Bool) ∈ p₁.exports.ops then
      let vc := p₁.impl 0 Unit Bool h ()
      let env : ∀ (op' : ℕ) (dom' codom' : Type), dom' → CatCrypt.Deep.RawCode codom' :=
        fun op' dom' codom' x' =>
          have := Classical.dec ((op', dom', codom') ∈ p₂.exports.ops)
          if h₂ : (op', dom', codom') ∈ p₂.exports.ops
          then (p₂.impl op' dom' codom' h₂ x').code
          else .fail
      vc.code.evalWith (fun op dom codom x => (env op dom codom x).eval)
    else
      SPComp.pure true) := by
  simp only [runPkg, CatCrypt.Deep.DeepPackage.link]
  split
  · next h =>
    exact CatCrypt.Deep.eval_substOracle _ _
  · next h =>
    rfl

/-- **Corollary**: If two games have the same oracle implementations for all
    operations that the adversary calls, then the linked packages produce
    the same computation.

    This is the key lemma for proving `DeepNomAdvantage G G' A = 0`
    when G and G' agree on the operations that A imports. -/
theorem runPkg_link_congr (A G G' : CatCrypt.Deep.DeepPackage)
    (h_exp : ∀ (op : ℕ) (dom codom : Type) (h₁ : (op, dom, codom) ∈ G.exports.ops)
               (h₂ : (op, dom, codom) ∈ G'.exports.ops) (x : dom),
      (G.impl op dom codom h₁ x).code.eval = (G'.impl op dom codom h₂ x).code.eval)
    (h_ops : G.exports.ops = G'.exports.ops) :
    runPkg (CatCrypt.Deep.DeepPackage.link A G) =
    runPkg (CatCrypt.Deep.DeepPackage.link A G') := by
  simp only [runPkg_link]
  split
  · next h =>
    -- Apply evalWith_congr: it suffices to show the oracle handlers agree
    apply CatCrypt.Deep.evalWith_congr
    intro op dom codom x
    -- Both dite conditions use h_ops-related membership
    have h_mem_iff : (op, dom, codom) ∈ G.exports.ops ↔
                     (op, dom, codom) ∈ G'.exports.ops := by rw [h_ops]
    -- Case split on whether the operation is in G's exports
    have := Classical.dec ((op, dom, codom) ∈ G.exports.ops)
    by_cases hm : (op, dom, codom) ∈ G.exports.ops
    · -- Operation is exported by both G and G'
      have hm' : (op, dom, codom) ∈ G'.exports.ops := h_mem_iff.mp hm
      simp [hm, hm']
      exact h_exp op dom codom hm hm' x
    · -- Operation is not exported by either
      have hm' : (op, dom, codom) ∉ G'.exports.ops := fun h => hm (h_mem_iff.mpr h)
      simp [hm, hm']
  · rfl

/-! ## Link Associativity

Definitional equality `link (link p₁ p₂) p₃ = link p₁ (link p₂ p₃)` does NOT
hold because the oracle substitution environments have different structure.
However, both sides produce the same `SPComp Bool` when evaluated via `runPkg`.

The key insight: in both formulations, oracle calls in p₁ are resolved as follows:
- If the operation is in p₂'s exports: use p₂'s implementation, with p₂'s own
  oracle calls resolved through p₃
- If the operation is NOT in p₂'s exports: evaluate to `fail`
  (Left: `fail.substOracle env₃ = fail`; Right: `link p₂ p₃` only exports
  `p₂.exports`, so the lookup fails)

Therefore the two sides agree semantically.
-/

open CatCrypt.Deep in
/-- **Link associativity at the evaluation level.**

    `runPkg (link (link p₁ p₂) p₃) = runPkg (link p₁ (link p₂ p₃))`

    This is the correct formulation of link associativity. We cannot prove
    `link (link p₁ p₂) p₃ = link p₁ (link p₂ p₃)` as a definitional equality
    on `DeepPackage` because the oracle substitution environments differ structurally.
    But at the semantic level (after evaluation to SPComp via `runPkg`), they agree.

    The proof uses:
    - `eval_substOracle`: substOracle commutes with eval
    - `evalWith_substOracle`: composed evalWith decomposes
    - `substOracle_comp`: double substitution equals composed substitution

    This theorem is critical for the reduction lemma `DeepNomAdvantage_link`. -/
theorem runPkg_link_assoc (p₁ p₂ p₃ : CatCrypt.Deep.DeepPackage) :
    runPkg (CatCrypt.Deep.DeepPackage.link (CatCrypt.Deep.DeepPackage.link p₁ p₂) p₃) =
    runPkg (CatCrypt.Deep.DeepPackage.link p₁ (CatCrypt.Deep.DeepPackage.link p₂ p₃)) := by
  simp only [runPkg, CatCrypt.Deep.DeepPackage.link]
  -- Both sides check if (0, Unit, Bool) ∈ p₁.exports.ops
  -- (since link preserves the first package's exports)
  split
  · next h =>
    -- Main export exists; show the evaluated code agrees
    -- Left side: ((p₁.code.substOracle env₂).substOracle env₃).eval
    -- Right side: (p₁.code.substOracle env_{link p₂ p₃}).eval

    -- Step 1: Rewrite left side: double substOracle → single substOracle (via comp)
    conv_lhs =>
      simp only [CatCrypt.Deep.RawCode.substOracle_comp]

    -- Step 2: Both sides are now p₁.code.substOracle(env).eval
    -- Convert both to evalWith form
    rw [CatCrypt.Deep.eval_substOracle, CatCrypt.Deep.eval_substOracle]

    -- Step 3: Show the two oracle handlers agree for all oracle calls
    apply CatCrypt.Deep.evalWith_congr
    intro op dom codom x

    -- handler_left: (env₂ op dom codom x).substOracle env₃ |>.eval
    -- handler_right: env_{link p₂ p₃} op dom codom x |>.eval
    -- env₂: if (op,dom,codom) ∈ p₂.exports → p₂.impl.code, else fail
    -- env_{link p₂ p₃}: if (op,dom,codom) ∈ p₂.exports → (p₂.impl.code).substOracle(env₃), else fail
    -- After substOracle(env₃) on env₂:
    --   In p₂: (p₂.impl.code).substOracle(env₃).eval ✓
    --   Not in p₂: fail.substOracle(env₃).eval = fail.eval ✓

    have := Classical.dec ((op, dom, codom) ∈ p₂.exports.ops)
    by_cases h₂ : (op, dom, codom) ∈ p₂.exports.ops
    · -- Operation in p₂'s exports: both sides give (p₂.impl.code).substOracle(env₃).eval
      simp [h₂]
    · -- Operation NOT in p₂'s exports: both give fail.eval = SPComp.fail
      simp [h₂]
  · next h =>
    -- No main export: both return pure true
    rfl

/-! ## Advantage Link (Reduction Lemma)

The key theorem for security reductions: composing a reduction R with both
games is equivalent to having R as part of the adversary.

  DeepNomAdvantage G₀ G₁ ⟨link A R⟩ = DeepNomAdvantage ⟨link R G₀⟩ ⟨link R G₁⟩ A

This follows from link associativity:
  link (link A R) G = link A (link R G)
So:
  runPkg (link (link A R) G₀) = runPkg (link A (link R G₀))
  runPkg (link (link A R) G₁) = runPkg (link A (link R G₁))
-/

/-- **Advantage link (reduction lemma) using NomPackage.link.**

    Composing a reduction wrapper `R` with both games is equivalent to
    having `R` as part of the adversary:

    `DeepNomAdvantage G₀ G₁ (link A R) = DeepNomAdvantage (link R G₀) (link R G₁) A`

    This follows directly from `runPkg_link_assoc`:
    - `link (link A.pkg R.pkg) G₀.pkg` evaluates the same as `link A.pkg (link R.pkg G₀.pkg)`
    - `link (link A.pkg R.pkg) G₁.pkg` evaluates the same as `link A.pkg (link R.pkg G₁.pkg)`

    This theorem is critical for modular security proofs: it allows us to
    "absorb" a reduction wrapper R into the adversary A, which is the standard
    technique for composing security games in hybrid arguments.

    Requires compatible registries (all packages use the same registry). -/
theorem DeepNomAdvantage_link (G₀ G₁ A R : CatCrypt.Deep.NomPackage)
    (hregAR : A.registry = R.registry)
    (hregRG₀ : R.registry = G₀.registry)
    (hregRG₁ : R.registry = G₁.registry) :
    DeepNomAdvantage G₀ G₁ (CatCrypt.Deep.NomPackage.link A R hregAR) =
    DeepNomAdvantage (CatCrypt.Deep.NomPackage.link R G₀ hregRG₀)
                     (CatCrypt.Deep.NomPackage.link R G₁ hregRG₁) A := by
  simp only [DeepNomAdvantage, CatCrypt.Deep.NomPackage.link]
  congr 1
  · exact runPkg_link_assoc A.pkg R.pkg G₀.pkg
  · exact runPkg_link_assoc A.pkg R.pkg G₁.pkg

/-! ## ID Package Properties -/

open CatCrypt.Deep in
/-- Linking with the identity package on the right preserves evaluation.

    `runPkg (link p (id p.imports))` = `runPkg p`

    This holds because:
    - `id` forwards all oracle calls, so `oracleCall` -> `oracleCall`
    - For p's code, after substOracle with id's env, oracle calls that
      are in p.imports remain as oracle calls (id forwards them)
    - Oracle calls not in p.imports become fail (same as unlinked evaluation)
    - In both cases, `eval` maps unresolved oracle calls to `SPComp.fail`

    So the link with `id` is semantically a no-op. -/
theorem runPkg_link_id_right (p : CatCrypt.Deep.DeepPackage) :
    runPkg (CatCrypt.Deep.DeepPackage.link p (CatCrypt.Deep.DeepPackage.id p.imports)) =
    runPkg p := by
  simp only [runPkg, CatCrypt.Deep.DeepPackage.link, CatCrypt.Deep.DeepPackage.id]
  split
  · next h =>
    -- Main export exists; show linked code evaluates same as original
    -- After substOracle with id's env:
    --   oracleCall op dom codom x -> if (op,dom,codom) in p.imports.ops
    --                                then oracleCall op dom codom x
    --                                else fail
    -- Under eval, both oracleCall and fail map to SPComp.fail
    -- So the result is the same
    rw [CatCrypt.Deep.eval_substOracle]
    -- Now: code.evalWith (handler) = code.eval
    -- Rewrite code.eval as code.evalWith (fun _ _ _ _ => SPComp.fail)
    rw [← CatCrypt.Deep.RawCode.evalWith_fail]
    apply CatCrypt.Deep.evalWith_congr
    intro op dom codom x
    have := Classical.dec ((op, dom, codom) ∈ p.imports.ops)
    split
    · -- In imports: id forwards as oracleCall, which evaluates to fail
      simp [CatCrypt.Deep.RawCode.eval]
    · -- Not in imports: fail, which evaluates to fail
      simp [CatCrypt.Deep.RawCode.eval]
  · next h =>
    -- No main export: both pure true
    rfl

open CatCrypt.Deep in
/-- Linking with the identity package on the left preserves evaluation,
    provided the main entry point `(0, Unit, Bool)` is in p's exports.

    `runPkg (link (id p.exports) p)` = `runPkg p`

    This holds because `id p.exports`'s implementation is just `oracleCall`,
    which after linking with p gets substituted with p's actual implementation. -/
theorem runPkg_link_id_left (p : CatCrypt.Deep.DeepPackage)
    (h_main : (0, Unit, Bool) ∈ p.exports.ops) :
    runPkg (CatCrypt.Deep.DeepPackage.link (CatCrypt.Deep.DeepPackage.id p.exports) p) =
    runPkg p := by
  simp only [runPkg, CatCrypt.Deep.DeepPackage.link, CatCrypt.Deep.DeepPackage.id]
  -- (0, Unit, Bool) is in (id p.exports).exports = p.exports
  simp only [h_main, dite_true]
  -- id's implementation for (0, Unit, Bool) is oracleCall 0 Unit Bool ()
  -- After substOracle with p's env:
  --   oracleCall 0 Unit Bool () -> if (0, Unit, Bool) in p.exports then p.impl.code else fail
  simp only [RawCode.substOracle, h_main, dite_true]

/-! ## Interchange Law

The fundamental interchange law for packages:

  `link (par p₁ p₂) (par p₃ p₄) ≈ par (link p₁ p₃) (link p₂ p₄)`

at the evaluation level (`runPkg` equality).

This requires an interface matching condition: the oracle environment from
`par p₃ p₄` must agree with `p₃`'s environment for operations that `p₁` calls
(and symmetrically with `p₄` for operations that `p₂` calls).

In a fully typed setting (where package types encode `P : package M E`),
this condition holds by construction: `p₁` only calls operations in `M`,
which are exactly `p₃`'s exports.
-/

open CatCrypt.Deep in
/-- **Interchange law for package composition.**

    At the evaluation level:

    `runPkg (link (par p₁ p₂ h₁₂) (par p₃ p₄ h₃₄))`
    `= runPkg (par (link p₁ p₃) (link p₂ p₄) h_link)`

    The interface matching condition `h_env` requires that the oracle
    environment from `par p₃ p₄` agrees with `p₃`'s environment at the
    eval level. This is automatically satisfied when:
    - p₃ and p₄ have disjoint export operation ids, AND
    - p₁ only makes oracle calls to operations in p₃.exports

    The proof reduces both sides to `evalWith` form on the same code,
    then uses `evalWith_congr` with the environment agreement hypothesis. -/
theorem runPkg_interchange (p₁ p₂ p₃ p₄ : CatCrypt.Deep.DeepPackage)
    (h₁₂ : CatCrypt.Deep.DeepPackage.sep p₁ p₂)
    (h₃₄ : CatCrypt.Deep.DeepPackage.sep p₃ p₄)
    (h_link_sep : CatCrypt.Deep.DeepPackage.sep
      (CatCrypt.Deep.DeepPackage.link p₁ p₃)
      (CatCrypt.Deep.DeepPackage.link p₂ p₄))
    -- Main entry dispatch: (0, Unit, Bool) is exported by p₁
    (h_main : (0, Unit, Bool) ∈ p₁.exports.ops)
    -- Interface matching: oracle environments agree at eval level
    (h_env : ∀ op dom codom x,
      (CatCrypt.Deep.DeepPackage.linkEnv
        (CatCrypt.Deep.DeepPackage.par p₃ p₄ h₃₄) op dom codom x).eval =
      (CatCrypt.Deep.DeepPackage.linkEnv p₃ op dom codom x).eval) :
    runPkg (CatCrypt.Deep.DeepPackage.link
      (CatCrypt.Deep.DeepPackage.par p₁ p₂ h₁₂)
      (CatCrypt.Deep.DeepPackage.par p₃ p₄ h₃₄)) =
    runPkg (CatCrypt.Deep.DeepPackage.par
      (CatCrypt.Deep.DeepPackage.link p₁ p₃)
      (CatCrypt.Deep.DeepPackage.link p₂ p₄) h_link_sep) := by
  -- Step 1: Unfold runPkg and link on both sides
  simp only [runPkg, CatCrypt.Deep.DeepPackage.link, CatCrypt.Deep.DeepPackage.par]
  -- Step 2: Both sides check (0, Unit, Bool) membership in p₁.exports.ops ++ p₂.exports.ops
  -- Since h_main says it's in p₁.exports.ops, it's in the appended list
  have h_app : (0, Unit, Bool) ∈ p₁.exports.ops ++ p₂.exports.ops :=
    List.mem_append_left _ h_main
  simp only [h_app, dite_true]
  -- Step 3: The par dispatch on the left gives p₁'s implementation
  -- (since (0,Unit,Bool) ∈ p₁.exports.ops)
  simp only [dif_pos h_main, ValidCodeBundle.mono]
  -- Step 4: Convert both sides to evalWith form via eval_substOracle
  rw [CatCrypt.Deep.eval_substOracle, CatCrypt.Deep.eval_substOracle]
  -- Step 5: Apply evalWith_congr — the handlers must agree pointwise
  apply CatCrypt.Deep.evalWith_congr
  exact h_env

/-! ## Advantage under Parallel Composition

The interchange law enables reasoning about advantage under parallel composition:
the common component C can be absorbed into the adversary.

TODO: State and prove `DeepNomAdvantage_par` once NomPackage-level par/link
are available with proper interface matching.
-/

/-! ## NomPkgSecure: Game-Based UC for Deep Packages

`NomPkgSecure G G' ε` says that for all adversaries A, the advantage of
distinguishing G from G' (via deep linking) is bounded by `ε A`.

This is the analogue of `GameUCEmulates` (UC.lean) for the deep package model
where adversaries are `NomPackage` rather than oracle-to-SPComp functions.

The bound is **adversary-dependent**: `ε : NomPackage → ℝ≥0∞`. This is essential
for concrete security (time/query complexity bounds). For composition, the
adversary-dependent bounds add pointwise.

### Relationship to other security notions

| Notion | Adversary | Composable | Axioms |
|--------|-----------|------------|--------|
| `NomPkgSecure` | NomPkg | via triangle | 0 |
| `GameUCEmulates` | OracleIf → SPComp Bool | via triangle | 0 |
| sdist ≤ ε | (absorbed) | full PPL | 0 |
| `UCEmulates` | (∀A ∃S) | full UC | 0 |

For TLS games (which use heap state), `NomPkgSecure` is the strongest notion
achievable without proving IsPure for linked packages.
-/

/-- Adversary-dependent game-based security for NomPkg games.

    `NomPkgSecure G G' ε` states that for all adversaries `A : NomPackage`,
    the advantage of distinguishing G from G' is bounded by `ε A`.

    This captures the standard cryptographic game-based security notion where
    the bound depends on the adversary's complexity (time, oracle queries). -/
def NomPkgSecure (G G' : CatCrypt.Deep.NomPackage)
    (ε : CatCrypt.Deep.NomPackage → ℝ≥0∞) : Prop :=
  ∀ (A : CatCrypt.Deep.NomPackage), DeepNomAdvantage G G' A ≤ ε A

/-- Reflexivity: any game is trivially secure against itself. -/
theorem NomPkgSecure_refl (G : CatCrypt.Deep.NomPackage) :
    NomPkgSecure G G (fun _ => 0) :=
  fun A => le_of_eq (DeepNomAdvantage_self G A)

/-- Symmetry: swapping real and ideal preserves the bound. -/
theorem NomPkgSecure_sym {G G' : CatCrypt.Deep.NomPackage}
    {ε : CatCrypt.Deep.NomPackage → ℝ≥0∞}
    (h : NomPkgSecure G G' ε) :
    NomPkgSecure G' G ε :=
  fun A => (DeepNomAdvantage_comm G G' A) ▸ (h A)

/-- Transitivity: composition via triangle inequality.
    The adversary-dependent bounds add pointwise. -/
theorem NomPkgSecure_trans {G₁ G₂ G₃ : CatCrypt.Deep.NomPackage}
    {ε₁ ε₂ : CatCrypt.Deep.NomPackage → ℝ≥0∞}
    (h₁ : NomPkgSecure G₁ G₂ ε₁)
    (h₂ : NomPkgSecure G₂ G₃ ε₂) :
    NomPkgSecure G₁ G₃ (fun A => ε₁ A + ε₂ A) :=
  fun A => le_trans (DeepNomAdvantage_triangle G₁ G₂ G₃ A) (add_le_add (h₁ A) (h₂ A))

/-- Monotonicity: weakening the bound. -/
theorem NomPkgSecure_mono {G G' : CatCrypt.Deep.NomPackage}
    {ε₁ ε₂ : CatCrypt.Deep.NomPackage → ℝ≥0∞}
    (h : NomPkgSecure G G' ε₁)
    (hle : ∀ A, ε₁ A ≤ ε₂ A) :
    NomPkgSecure G G' ε₂ :=
  fun A => le_trans (h A) (hle A)

/-- Uniform bound version: when the bound doesn't depend on the adversary. -/
theorem NomPkgSecure_uniform {G G' : CatCrypt.Deep.NomPackage}
    {ε : CatCrypt.Deep.NomPackage → ℝ≥0∞} {ε_u : ℝ≥0∞}
    (h : NomPkgSecure G G' ε)
    (hle : ∀ A, ε A ≤ ε_u) :
    NomPkgSecure G G' (fun _ => ε_u) :=
  NomPkgSecure_mono h hle

end CatCrypt.Crypto
