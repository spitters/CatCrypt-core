/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoDispatchExt
public meta import CatCryptCore.Tactics.AutoDispatchExt

/-!
# Tests for the `catcrypt_auto` arms of `AutoDispatchExt`

One example per arm of `CatCryptCore.Tactics.AutoDispatchExt`, a coupling goal on
which every arm fails, a hybrid advantage goal closed by the hop chain arm of
`AutoDispatch` after the arms of this module fail, the error naming both shapes,
a goal of no shape of that module (handled by `AutoDispatch`), and the suggestion
of `catcrypt_auto?`.
-/

set_option autoImplicit false

open CatCrypt CatCrypt.Core CatCrypt.Relational CatCrypt.Crypto CatCrypt.XDijkstra
  CatCrypt.Prob
open scoped ENNReal

namespace CatCrypt.Tactics.AutoDispatchExtTest

/-! ## Coupling -/

/-- An `n`-round coupled loop whose per-round coupling is a hypothesis (the shape
of `XCombinedAutomation.loop_coupling_via_relmvcgen_bang_hook`). -/
example {W : Type} {R : W → W → Prop} {k₁ k₂ : W → SDistr W}
    {ε : ℝ≥0∞} (rk₀ : W) (n : ℕ) (hR₀ : R rk₀ rk₀)
    (hstep : ∀ a b, R a b → XRelTripleQ0 (T := SDistr) ε R (k₁ a) (k₂ b)) :
    XRelTripleQ0 (T := SDistr) (0 + n • ε) R
      (relForN k₁ (SDistr.pure rk₀) n) (relForN k₂ (SDistr.pure rk₀) n) := by
  catcrypt_auto

/-- A three-hop straight-line coupling whose hops are hypotheses (the shape of
`XCombinedAutomation.relDemo3_via_relmvcgen_bang_hook`). -/
example {T : Type → Type} [RelQ0 T] {α₀ β₀ α₁ β₁ α₂ β₂ : Type} {ε₁ ε₂ ε₃ : ℝ≥0∞}
    {R₀ : α₀ → β₀ → Prop} {R₁ : α₁ → β₁ → Prop} {R₂ : α₂ → β₂ → Prop}
    {m₁ : T α₀} {m₂ : T β₀} {k₁ : α₀ → T α₁} {k₂ : β₀ → T β₁}
    {l₁ : α₁ → T α₂} {l₂ : β₁ → T β₂}
    (h₁ : RelSpecTriple ε₁ R₀ m₁ m₂)
    (h₂ : ∀ a b, R₀ a b → RelSpecTriple ε₂ R₁ (k₁ a) (k₂ b))
    (h₃ : ∀ a b, R₁ a b → RelSpecTriple ε₃ R₂ (l₁ a) (l₂ b)) :
    RelSpecTriple ((ε₁ + ε₂) + ε₃) R₂
      (RelQ0.bind' (RelQ0.bind' m₁ k₁) l₁) (RelQ0.bind' (RelQ0.bind' m₂ k₂) l₂) := by
  catcrypt_auto

/-- Without the per-round hypothesis every arm fails. -/
example {W : Type} {R : W → W → Prop} {_k₁ _k₂ : W → SDistr W}
    {_ε : ℝ≥0∞} (rk₀ : W) (_n : ℕ) (_hR₀ : R rk₀ rk₀) : True := by
  fail_if_success
    have _ : XRelTripleQ0 (T := SDistr) (0 + _n • _ε) R
      (relForN _k₁ (SDistr.pure rk₀) _n) (relForN _k₂ (SDistr.pure rk₀) _n) := by
      catcrypt_auto
  trivial

/-! ## Hybrid advantage -/

/-- A uniform `q`-hop hybrid with the per-hop bound as hypothesis (`advmvcgen!?`). -/
example {α : Type} (G : ℕ → SPComp α) (A : α → SPComp Bool) (q : ℕ) (ε : ℝ≥0∞)
    (hstep : ∀ i, i < q → AdvantageA (G i) (G (i + 1)) A ≤ ε) :
    AdvantageA (G 0) (G q) A ≤ q * ε := by
  catcrypt_auto

/-- A `q`-hop hybrid with per-hop bounds `ε i` (`advmvcgen_dep` arm). -/
example {α : Type} (G : ℕ → SPComp α) (A : α → SPComp Bool) (q : ℕ) (ε : ℕ → ℝ≥0∞)
    (hstep : ∀ i, i < q → AdvantageA (G i) (G (i + 1)) A ≤ ε i) :
    AdvantageA (G 0) (G q) A ≤ ∑ i ∈ Finset.range q, ε i := by
  catcrypt_auto

/-- The three-hop chain of Examples/PRF.lean:187 (`cascade_prf_bound`), with the
birthday term abstracted to `b`: the arms of this module fail and the hop chain
arm of `AutoDispatch` closes the goal. -/
example {α : Type} (G : ℕ → SPComp α) (A : α → SPComp Bool) (ε_prf b : ℝ≥0∞)
    (h01 : AdvantageA (G 0) (G 1) A ≤ ε_prf) (h12 : AdvantageA (G 1) (G 2) A ≤ b)
    (h23 : AdvantageA (G 2) (G 3) A ≤ ε_prf) :
    AdvantageA (G 0) (G 3) A ≤ 2 * ε_prf + b := by
  catcrypt_auto?

-- Without hop hypotheses every arm fails. When the elaborator of this module
-- fails, Lean runs the elaborator of `AutoDispatch` next, and its error, which
-- names the shape and the failed arms of `AutoDispatch`, is the one reported.
/--
error: catcrypt_auto: goal shape advantage/sdist inequality; every arm failed
-/
#guard_msgs (substring := true) in
example {α : Type} (G₀ G₁ : SPComp α) (A : α → SPComp Bool) (ε : ℝ≥0∞) :
    AdvantageA G₀ G₁ A ≤ ε := by
  catcrypt_auto

/-! ## Zero advantage -/

/-- Identical games have zero advantage against every adversary (`prob_to_rHoare`). -/
example (G : SPComp Bool) : ∀ A, AdvantageA G G A = 0 := by
  catcrypt_auto

/-- The same for a fixed adversary (second arm). -/
example (G : SPComp Bool) (A : Bool → SPComp Bool) : AdvantageA G G A = 0 := by
  catcrypt_auto

/-! ## Extended triple -/

/-- A unary `SDistr` triple of `pure` (the shape of `XSDistrSoundness.demo_sdistr_pure`). -/
example : XTriple (m := SDistr) (ps := .pure) (Ω := Prop)
    True (SDistr.pure (3 : Nat)) (fun x => x = 3, PUnit.unit) := by
  catcrypt_auto

/-! ## Other goals -/

/-- A goal of no shape of `AutoDispatchExt` is handled by `AutoDispatch`. -/
example (n : ℕ) (h : n = 3) : n + 1 = 4 := by
  catcrypt_auto

/-- `catcrypt_auto?` suggests the closing arm. -/
example {α : Type} (G : ℕ → SPComp α) (A : α → SPComp Bool) (q : ℕ) (ε : ℝ≥0∞)
    (hstep : ∀ i, i < q → AdvantageA (G i) (G (i + 1)) A ≤ ε) :
    AdvantageA (G 0) (G q) A ≤ q * ε := by
  catcrypt_auto?

end CatCrypt.Tactics.AutoDispatchExtTest
