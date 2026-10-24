/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Relational.Judgment
public import CatCryptCore.Tactics.AutoBase

/-!
# Tests for `catcrypt_auto` over the Lean-only dispatcher

The module imports `CatCryptCore.Relational.Judgment` (which imports
`CatCryptCore.Core.Code`) and the dispatcher `CatCryptCore.Tactics.AutoBase`, whose import
closure is printed below: `Init`, `Std`, `Lean` and four modules of this directory. An
`IsPure` side condition closes by the `solve_by_elim` arm over the combinators of
`Core.Code`, after the `>>=` normalisation; a relational judgment closes with the
premises of this module, by a theorem stated before it.
-/

namespace CatCrypt.Tactics.AutoBaseTest

open CatCrypt.Core CatCrypt.Relational

/--
info: import closure of CatCryptCore.Tactics.AutoBase: roots [CatCryptCore,
 Init,
 Lean,
 Std]; modules outside Init, Std and Lean: [CatCryptCore.Tactics.AutoBase,
 CatCryptCore.Tactics.AutoDispatchCore,
 CatCryptCore.Tactics.AutoHopRegistry,
 CatCryptCore.Tactics.AutoPremises]
-/
#guard_msgs in
#import_closure_roots CatCryptCore.Tactics.AutoBase

-- A `do` block of a sample and a `pure` is pure: the `CatCryptRel` arm, whose rules
-- `Core.Code` registers, after the `>>=` normalisation.
/--
info: Try this:
  [apply] (simp only [CatCrypt.Core.SPComp.monad_bind_eq];
    aesop  (rule_sets := [CatCryptRel])  (config := { terminal := true }))
-/
#guard_msgs in
example : SPComp.IsPure (do let a ← SPComp.sample Bool; pure (!a) : SPComp Bool) := by
  catcrypt_auto?

/-- The consequence rule in the postcondition, stated in this module. -/
theorem testRel_weaken {α β : Type} {Φ : RPre} {Ψ Ψ' : RPost α β} {c₁ : SPComp α}
    {c₂ : SPComp β} (h : rHoare Φ c₁ c₂ Ψ)
    (hΨ : ∀ a₁ h₁ a₂ h₂, Ψ a₁ h₁ a₂ h₂ → Ψ' a₁ h₁ a₂ h₂) : rHoare Φ c₁ c₂ Ψ' :=
  rHoare_mono_post h hΨ

-- A relational judgment with no arm of its shape at this level closes with the
-- premises of this module: `testRel_weaken`.
/--
info: Try this:
  [apply] solve_by_elim [testRel_weaken]
-/
#guard_msgs in
example {α β : Type} {Φ : RPre} {Ψ Ψ' : RPost α β} {c₁ : SPComp α} {c₂ : SPComp β}
    (h : rHoare Φ c₁ c₂ Ψ) (hΨ : ∀ a₁ h₁ a₂ h₂, Ψ a₁ h₁ a₂ h₂ → Ψ' a₁ h₁ a₂ h₂) :
    rHoare Φ c₁ c₂ Ψ' := by
  catcrypt_auto?

end CatCrypt.Tactics.AutoBaseTest
