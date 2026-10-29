/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoBase
public meta import CatCryptCore.Tactics.AutoDispatchCore

/-!
# Tests of the premise forms of `catcrypt_auto`

Goals over recursive fixtures, each closed by `premise_forms_test`, which runs
`AutoDispatch.PremiseForms.closeWith` on the premises of the premise stage of
`catcrypt_auto` (`AutoDispatch.stagePremises`: the theorems of this module and the fields
of local hypotheses), one goal per form:

| Goal | Closing form |
|---|---|
| an equation under a product | `rw [rf_eq]` |
| an equation under a binder | `simp only [bf_eq]` |
| a lemma with a hypothesis argument | `apply hp_of_hq <;> assumption` |
| explicit arguments determined by unification | `exact up_add _ _` |
| an inequality inside a sum | `catcrypt_grind [d1_le_d2 S A]` |
| two inequalities chained | `catcrypt_grind [e2_le_e3 n, e1_le_e2 n]` |
| an equation field of a hypothesis | `rw [h.fix]` |

Two goals are closed by `catcrypt_auto` through its premise stage.
-/

set_option autoImplicit false

namespace CatCrypt.Tactics.AutoPremiseFormsTest

/-- `premise_forms_test` closes the main goal by the premise forms of `catcrypt_auto`
applied to the premises of its premise stage. -/
syntax (name := premiseFormsTest) "premise_forms_test" : tactic

open Lean Elab Tactic in
/-- The elaborator of `premise_forms_test`. -/
@[tactic premiseFormsTest] public meta def evalPremiseFormsTest : Tactic := fun _ => do
  discard (AutoDispatch.PremiseForms.closeWith (← AutoDispatch.stagePremises))

/-- A fixture function: `rf n = 2 * n`, by recursion. -/
def rf : Nat → Nat
  | 0 => 0
  | n + 1 => rf n + 2

/-- A fixture function. -/
def rg (n : Nat) : Nat := 2 * n

theorem rf_eq (n : Nat) : rf n = rg n := by
  induction n <;> grind [rf, rg]

example (n : Nat) : rf (n + 2) * 3 = rg (n + 2) * 3 := by
  premise_forms_test

/-- A fixture function: `bf n = 3 * n + 1`, by recursion. -/
def bf : Nat → Nat
  | 0 => 1
  | n + 1 => bf n + 3

/-- A fixture function. -/
def bg (n : Nat) : Nat := 3 * n + 1

theorem bf_eq (n : Nat) : bf n = bg n := by
  induction n <;> grind [bf, bg]

example : (fun x => bf x + 1) = (fun x => bg x + 1) := by
  premise_forms_test

/-- A fixture predicate. -/
def HQ (a : Nat) : Prop := rf a = 0

/-- A fixture predicate. -/
def HP (a : Nat) : Prop := rg a = 0

theorem hp_of_hq (a : Nat) (h : HQ a) : HP a := by
  unfold HQ at h; unfold HP; rw [← rf_eq]; exact h

example (a : Nat) (hq : HQ a) : HP a := by
  premise_forms_test

/-- A fixture relation. -/
def UP (x y : Nat) : Prop := y ≤ x

theorem up_add (a b : Nat) : UP (a + b) b := by
  unfold UP; omega

example : UP (2 + 3) 3 := by
  premise_forms_test

/-- A fixture function. -/
def d1 (S : Nat → Nat) (A : Nat) : Nat := S A

/-- A fixture function. -/
def d2 (S : Nat → Nat) (A : Nat) : Nat := S A + rf A

theorem d1_le_d2 (S : Nat → Nat) (A : Nat) : d1 S A ≤ d2 S A := by
  unfold d1 d2; omega

example (S : Nat → Nat) (A x : Nat) : d1 S A + x ≤ d2 S A + x + 1 := by
  premise_forms_test

/-- A fixture function. -/
def e1 (n : Nat) : Nat := rf n

/-- A fixture function. -/
def e2 (n : Nat) : Nat := 2 * n

/-- A fixture function. -/
def e3 (n : Nat) : Nat := 3 * n

theorem e1_le_e2 (n : Nat) : e1 n ≤ e2 n := by
  unfold e1 e2; rw [rf_eq, rg]; exact Nat.le_refl _

theorem e2_le_e3 (n : Nat) : e2 n ≤ e3 n := by
  unfold e2 e3; omega

example (n : Nat) : e1 n ≤ e3 n + 1 := by
  premise_forms_test

/-- A fixture function: the identity, by recursion. -/
def hf : Nat → Nat
  | 0 => 0
  | n + 1 => hf n + 1

/-- A fixture structure with an equation field. -/
structure HasFix (c : Nat) : Prop where
  fix : hf c = c

example (c : Nat) (h : HasFix c) : hf c + hf c = 2 * c := by
  premise_forms_test

example (n : Nat) : rf (n + 5) + 7 ≤ rg (n + 5) + 8 := by
  catcrypt_auto

example (n : Nat) : e1 (n + 1) ≤ e3 (n + 1) + 2 := by
  catcrypt_auto

end CatCrypt.Tactics.AutoPremiseFormsTest
