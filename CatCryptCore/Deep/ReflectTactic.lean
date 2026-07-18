/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Deep.ReflectUCHelpers

set_option autoImplicit false

/-!
# End-to-end reflective SSP tactic: shallow games → package / UC security

`Deep/ReflectUCHelpers.lean` supplies the perfect-security *stack combinators*
(`nomPkgSecure_ofOracle`, `uc_ofOracle`, `deepNomAdvantage_ofOracle_zero`,
`sdist_ofOracle_zero`) that consume two **reflected** oracle bodies
`impl₀ impl₁ : dom → RawCode codom`, their `IsValid` instances, and the single
body-`.eval` equality `h : ∀ x, (impl₀ x).eval = (impl₁ x).eval`. Each example
(`OneTimePad`, `Commitment`, `SecretSharing`, …) still has to hand-write a
~40-line "Reflection into the Package / UC Stack" section: reflect the two game
bodies with `rawCode%`, register `IsValid`, prove the `.eval` equality, build the
`ofOracle` package pair, and thread the four package theorems.

This file collapses that section into **one term-level invocation** per goal.
Given the two *shallow* `SPComp` game families and the single shallow coupling
`h : ∀ x, g₀ x = g₁ x`, the macros

* `reflect_ofOracle_nompkg_secure op g₀ g₁ h : NomPkgSecure … (fun _ => 0)`
* `reflect_ofOracle_uc op g₀ g₁ h : UCEmulates 0 …`

reflect each family as `fun x => rawCode% (gᵢ x)`, let instance resolution
discharge the `IsValid` obligations, turn the shallow `h` into the reflected
`.eval` equality (`(rawCode% (gᵢ x)).eval` is the shallow `gᵢ x`, so `simp
[RawCode.eval]` + `h x` closes it), and apply the matching stack combinator.

## Design

Both are **term-level macros** (not tactic macros): the combinators are already
ordinary lemmas taking the reflected data explicitly, so the only metaprogramming
needed is (a) the `rawCode%` reflection under a binder and (b) plumbing the
shallow coupling into the reflected obligation — both purely syntactic. A term
macro keeps the call a single expression that elaborates directly against the
goal's `op`/`dom`/`codom`, with instance resolution supplying `IsValid`.

The `.eval`-equality obligation is discharged by a small cascade: for
constructor-only bodies (no `get`/`set`) the round-trip `(rawCode% e).eval = e`
holds definitionally, so `exact h x` closes it directly; otherwise
`simp [RawCode.eval]` normalizes the round-trip before `exact h x`.
-/

namespace CatCrypt.Deep

open CatCrypt.Core CatCrypt.Crypto

/-- Discharge the reflected body-`.eval` equality from a shallow coupling `h`.
    `(rawCode% (gᵢ x)).eval` round-trips to the shallow `gᵢ x`, so after reducing
    the round-trip the goal is `g₀ x = g₁ x`, closed by `h x`. -/
macro "reflect_eval_congr " h:term:max : tactic =>
  `(tactic| (intro x
             first
               | exact $h x
               | (simp only [RawCode.eval]; exact $h x)
               | (simp [RawCode.eval]; exact $h x)))

/-- **Package-level perfect security from shallow games in one invocation.**
    `reflect_ofOracle_nompkg_secure op g₀ g₁ h` reflects the shallow `SPComp`
    game families `g₀ g₁ : dom → SPComp codom`, exports each as the oracle
    `(op, dom, codom)`, and closes `NomPkgSecure … (fun _ => 0)` from the single
    shallow coupling `h : ∀ x, g₀ x = g₁ x`. Collapses the `ofOracle`-package
    plumbing of a hand-written reflection section. -/
macro "reflect_ofOracle_nompkg_secure " op:term:max g0:term:max g1:term:max h:term:max : term =>
  `(nomPkgSecure_ofOracle (op := $op)
      (fun x => rawCode% ($g0 x))
      (fun x => rawCode% ($g1 x))
      (by reflect_eval_congr $h))

/-- **Perfect UC emulation from shallow games in one invocation.**
    `reflect_ofOracle_uc op g₀ g₁ h` reflects the shallow `SPComp` game families,
    exports each as the oracle `(op, dom, codom)`, and closes `UCEmulates 0 …`
    over the trivial-leak interface from the single shallow coupling
    `h : ∀ x, g₀ x = g₁ x`. Collapses the reflection-to-UC section to one line. -/
macro "reflect_ofOracle_uc " op:term:max g0:term:max g1:term:max h:term:max : term =>
  `(uc_ofOracle (op := $op)
      (fun x => rawCode% ($g0 x))
      (fun x => rawCode% ($g1 x))
      (by reflect_eval_congr $h))

end CatCrypt.Deep
