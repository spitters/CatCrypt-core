/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Deep.Eval
import CatCryptCore.Deep.Package
import CatCryptCore.Deep.Bridge
import CatCryptCore.Crypto.Advantage

/-!
# Package Behavioral Equivalence

This file defines behavioral equivalence for deep packages and proves that
package linking preserves it.

## Main definitions

* `DeepPackage.BehavEquiv` - Two packages are behaviorally equivalent if they
  have the same exports and produce the same `SPComp` for every exported
  operation under every oracle handler.

## Main results

* `link_evalOp_eq` - Linking correctness: evaluating a linked operation equals
  evaluating the original code with oracles resolved via `evalWith`.
* `BehavEquiv.link_congr_right` - If `p₂ ≡ p₃`, then `p₁.link p₂ ≡ p₁.link p₃`.
* `BehavEquiv.advantage_link_congr` - If `p₂ ≡ p₃`, the advantage of distinguishing
  `p₁.link p₂` from `p₁.link p₃` is zero.

## Design

Behavioral equivalence is defined semantically using `evalWith`, which
interprets `RawCode` into `SPComp` given an oracle handler. Two packages are
equivalent when, for every shared exported operation, evaluating their
implementations with *any* oracle handler yields the same `SPComp` computation.

This is stronger than just comparing `eval` (which maps unresolved oracles to
`fail`), because it captures how the packages behave when composed with
arbitrary environments.

## References

* [Larsen and Schürmann, *Nominal State-Separating Proofs*](https://eprint.iacr.org/2025/598)
-/

namespace CatCrypt.Deep

open CatCrypt.Core
open CatCrypt.Prob
open CatCrypt.Relational
open CatCrypt.Crypto

universe u

/-! ## Behavioral Equivalence -/

/-- Two deep packages are behaviorally equivalent if:
    1. They have the same export interface.
    2. For every exported operation and every oracle handler, their
       implementations produce the same `SPComp` computation.

    This captures semantic equivalence: the packages are interchangeable
    in any context (linking environment). Using `evalWith` rather than
    `eval` ensures we account for how the code behaves when oracle calls
    are resolved by an arbitrary environment. -/
structure DeepPackage.BehavEquiv (p₁ p₂ : DeepPackage.{u}) : Prop where
  /-- The packages export the same operations -/
  exports_eq : p₁.exports = p₂.exports
  /-- For every exported operation and oracle handler, the evaluations agree -/
  impl_eq : ∀ (op : ℕ) (dom codom : Type u)
    (h₁ : (op, dom, codom) ∈ p₁.exports.ops)
    (h₂ : (op, dom, codom) ∈ p₂.exports.ops)
    (x : dom)
    (oracle : ∀ (_ : ℕ) (dom' codom' : Type u), dom' → SPComp codom'),
    (p₁.impl op dom codom h₁ x).code.evalWith oracle =
    (p₂.impl op dom codom h₂ x).code.evalWith oracle

namespace DeepPackage.BehavEquiv

variable {p₁ p₂ p₃ : DeepPackage.{u}}

/-- Behavioral equivalence is reflexive. -/
theorem refl (p : DeepPackage.{u}) : BehavEquiv p p :=
  ⟨rfl, fun _ _ _ h₁ h₂ _ _ => by congr 1⟩

/-- Behavioral equivalence is symmetric. -/
theorem symm (h : BehavEquiv p₁ p₂) : BehavEquiv p₂ p₁ :=
  ⟨h.exports_eq.symm, fun op dom codom h₂ h₁ x oracle =>
    (h.impl_eq op dom codom h₁ h₂ x oracle).symm⟩

/-- Behavioral equivalence is transitive. -/
theorem trans (h₁₂ : BehavEquiv p₁ p₂) (h₂₃ : BehavEquiv p₂ p₃) : BehavEquiv p₁ p₃ :=
  ⟨h₁₂.exports_eq.trans h₂₃.exports_eq,
   fun op dom codom h₁ h₃ x oracle => by
    have h₂ : (op, dom, codom) ∈ p₂.exports.ops :=
      h₁₂.exports_eq ▸ h₁
    exact (h₁₂.impl_eq op dom codom h₁ h₂ x oracle).trans
      (h₂₃.impl_eq op dom codom h₂ h₃ x oracle)⟩

end DeepPackage.BehavEquiv

/-! ## Linking Correctness -/

/-- **Linking correctness**: Evaluating a linked operation is the same as
    evaluating the original code with an oracle handler that dispatches to
    the linked package's implementations.

    Concretely, for an operation `(op, dom, codom)` exported by `p₁`:
    ```
    ((p₁.link p₂).impl op dom codom h x).code.eval
      = (p₁.impl op dom codom h x).code.evalWith (fun op' dom' codom' x' =>
          linkEnv p₂ op' dom' codom' x' |>.eval)
    ```

    This follows directly from `eval_substOracle`. -/
theorem DeepPackage.link_evalOp_eq (p₁ p₂ : DeepPackage.{u})
    (op : ℕ) (dom codom : Type u) (h : (op, dom, codom) ∈ p₁.exports.ops) (x : dom) :
    ((p₁.link p₂).impl op dom codom h x).code.eval =
    (p₁.impl op dom codom h x).code.evalWith
      (fun op' dom' codom' x' => (linkEnv p₂ op' dom' codom' x').eval) := by
  simp only [DeepPackage.link]
  exact eval_substOracle _ _

/-- Generalized linking correctness with an arbitrary outer oracle handler.

    Evaluating a linked operation with handler `oracle` equals evaluating the
    original code with a composed handler: oracle calls first go through `p₂`'s
    link environment (via `substOracle`), then the result is evaluated with
    `oracle`.

    This follows from `evalWith_substOracle`. -/
theorem DeepPackage.link_evalWith_eq (p₁ p₂ : DeepPackage.{u})
    (op : ℕ) (dom codom : Type u) (h : (op, dom, codom) ∈ p₁.exports.ops) (x : dom)
    (oracle : ∀ (_ : ℕ) (dom' codom' : Type u), dom' → SPComp codom') :
    ((p₁.link p₂).impl op dom codom h x).code.evalWith oracle =
    (p₁.impl op dom codom h x).code.evalWith
      (fun op' dom' codom' x' => (linkEnv p₂ op' dom' codom' x').evalWith oracle) := by
  simp only [DeepPackage.link]
  exact evalWith_substOracle _ _ _

/-! ## Linking Preserves Behavioral Equivalence -/

/-- **Right congruence for linking**: If `p₂` and `p₃` are behaviorally
    equivalent, then `p₁.link p₂` is behaviorally equivalent to `p₁.link p₃`.

    The proof unfolds `link` on both sides, applies `evalWith_substOracle` to
    reduce to evaluating `p₁`'s code with composed handlers, then shows the
    handlers agree because `p₂` and `p₃` agree (by behavioral equivalence). -/
theorem DeepPackage.BehavEquiv.link_congr_right
    (p₁ : DeepPackage.{u}) {p₂ p₃ : DeepPackage.{u}}
    (h : BehavEquiv p₂ p₃) : BehavEquiv (p₁.link p₂) (p₁.link p₃) := by
  constructor
  · -- exports are the same: both are p₁.exports
    simp only [DeepPackage.link]
  · intro op dom codom h₁₂ h₁₃ x oracle
    -- Unfold link and use evalWith_substOracle
    rw [DeepPackage.link_evalWith_eq, DeepPackage.link_evalWith_eq]
    -- Now show the composed handlers agree
    apply evalWith_congr
    intro op' dom' codom' x'
    -- Need: (linkEnv p₂ ...).evalWith oracle = (linkEnv p₃ ...).evalWith oracle
    simp only [DeepPackage.linkEnv]
    -- Both sides do dite on membership in exports.ops
    -- Since p₂.exports = p₃.exports, the dite conditions agree
    have hexports : p₂.exports.ops = p₃.exports.ops := by
      rw [h.exports_eq]
    -- Split on whether the operation is in p₂'s exports
    have := Classical.dec ((op', dom', codom') ∈ p₂.exports.ops)
    by_cases hmem : (op', dom', codom') ∈ p₂.exports.ops
    · -- Operation is in both exports
      have hmem₃ : (op', dom', codom') ∈ p₃.exports.ops := hexports ▸ hmem
      simp only [dif_pos hmem, dif_pos hmem₃]
      exact h.impl_eq op' dom' codom' hmem hmem₃ x' oracle
    · -- Operation is in neither exports
      have hmem₃ : (op', dom', codom') ∉ p₃.exports.ops := by
        rwa [← hexports]
      simp only [dif_neg hmem, dif_neg hmem₃]

/-- **Left congruence for linking**: If `p₁` and `p₂` are behaviorally
    equivalent and have the same imports, then `p₁.link q` is behaviorally
    equivalent to `p₂.link q`.

    The proof uses `evalWith_congr` in the other direction: now the outer
    code differs (p₁ vs p₂) but the oracle environment is the same (q). -/
theorem DeepPackage.BehavEquiv.link_congr_left
    {p₁ p₂ : DeepPackage.{u}} (q : DeepPackage.{u})
    (h : BehavEquiv p₁ p₂) : BehavEquiv (p₁.link q) (p₂.link q) := by
  constructor
  · -- exports: p₁.exports = p₂.exports (from behavioral equiv)
    simp only [DeepPackage.link, h.exports_eq]
  · intro op dom codom h_l h_r x oracle
    -- Rewrite both sides using link_evalWith_eq
    rw [DeepPackage.link_evalWith_eq, DeepPackage.link_evalWith_eq]
    -- The oracle environments are the same (both use linkEnv q)
    -- The code differs: p₁.impl vs p₂.impl
    -- But h.impl_eq tells us they agree on evalWith for any handler
    have h₁ : (op, dom, codom) ∈ p₁.exports.ops := by
      simp only [DeepPackage.link] at h_l; exact h_l
    have h₂ : (op, dom, codom) ∈ p₂.exports.ops := by
      simp only [DeepPackage.link] at h_r; exact h_r
    exact h.impl_eq op dom codom h₁ h₂ x _

/-! ## Advantage from Behavioral Equivalence -/

/-- If two packages are behaviorally equivalent, evaluating any exported
    operation (with `eval`, i.e., unresolved oracles become `fail`) gives
    the same `SPComp`. -/
theorem DeepPackage.BehavEquiv.evalOp_eq
    {p₁ p₂ : DeepPackage.{u}}
    (h : BehavEquiv p₁ p₂)
    (op : ℕ) (dom codom : Type u)
    (h₁ : (op, dom, codom) ∈ p₁.exports.ops)
    (h₂ : (op, dom, codom) ∈ p₂.exports.ops)
    (x : dom) :
    p₁.evalOp op dom codom h₁ x = p₂.evalOp op dom codom h₂ x := by
  simp only [DeepPackage.evalOp]
  -- eval = evalWith fail_handler, and we can use impl_eq
  rw [← RawCode.evalWith_fail (p₁.impl op dom codom h₁ x).code,
      ← RawCode.evalWith_fail (p₂.impl op dom codom h₂ x).code]
  exact h.impl_eq op dom codom h₁ h₂ x _

/-- **Zero advantage from behavioral equivalence of linked packages.**

    If `p₂ ≡ p₃`, then for any distinguisher package `p₁` and any
    adversary `A`, the advantage of distinguishing `p₁.link p₂` from
    `p₁.link p₃` is zero (for any exported operation used as the game).

    Specialized to universe 0 because `AdvantageA` requires `{α : Type}`.

    This follows from:
    1. `link_congr_right` gives `p₁.link p₂ ≡ p₁.link p₃`
    2. Behavioral equivalence implies `evalOp` equality
    3. Equal `SPComp`s have zero advantage -/
theorem DeepPackage.BehavEquiv.advantage_link_congr
    (p₁ : DeepPackage.{0}) {p₂ p₃ : DeepPackage.{0}}
    (h : BehavEquiv p₂ p₃)
    (op : ℕ) (dom codom : Type)
    (h₁₂ : (op, dom, codom) ∈ (p₁.link p₂).exports.ops)
    (h₁₃ : (op, dom, codom) ∈ (p₁.link p₃).exports.ops)
    (x : dom) :
    ∀ A, AdvantageA
      ((p₁.link p₂).evalOp op dom codom h₁₂ x)
      ((p₁.link p₃).evalOp op dom codom h₁₃ x) A = 0 := by
  intro A
  have hequiv := h.link_congr_right p₁
  have hevalOp := hequiv.evalOp_eq op dom codom h₁₂ h₁₃ x
  rw [hevalOp]
  simp only [AdvantageA, Advantage, tsub_self, max_self]

/-! ## Useful Derived Lemmas -/

/-- Linking with behaviorally equivalent packages gives the same `evalOp`.

    This is a convenience wrapper combining `link_congr_right` and `evalOp_eq`. -/
theorem DeepPackage.link_evalOp_congr_right
    (p₁ : DeepPackage.{u}) {p₂ p₃ : DeepPackage.{u}}
    (h : BehavEquiv p₂ p₃)
    (op : ℕ) (dom codom : Type u)
    (h₁₂ : (op, dom, codom) ∈ (p₁.link p₂).exports.ops)
    (h₁₃ : (op, dom, codom) ∈ (p₁.link p₃).exports.ops)
    (x : dom) :
    (p₁.link p₂).evalOp op dom codom h₁₂ x =
    (p₁.link p₃).evalOp op dom codom h₁₃ x :=
  (h.link_congr_right p₁).evalOp_eq op dom codom h₁₂ h₁₃ x

/-- `rHoare` from behavioral equivalence: equivalent packages satisfy
    relational Hoare logic with `eqPre`/`eqPost`. -/
theorem DeepPackage.BehavEquiv.rHoare_evalOp
    {p₁ p₂ : DeepPackage.{u}}
    (h : BehavEquiv p₁ p₂)
    (op : ℕ) (dom codom : Type u)
    (h₁ : (op, dom, codom) ∈ p₁.exports.ops)
    (h₂ : (op, dom, codom) ∈ p₂.exports.ops)
    (x : dom) :
    rHoare eqPre (p₁.evalOp op dom codom h₁ x)
                 (p₂.evalOp op dom codom h₂ x) eqPost := by
  rw [h.evalOp_eq op dom codom h₁ h₂ x]
  exact rHoare_refl _

end CatCrypt.Deep
