/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoPremises
public meta import CatCryptCore.Tactics.AutoPremises

/-!
# Tests for `catcrypt_premises?`

Abstract fixtures for the four sources of `CatCryptCore.Tactics.AutoPremises`:
theorems of this module stated before the goal (and not those stated after it), fields of
a hypothesis of structure type, hypotheses with instantiated quantifiers (and the exclusion
of a hardness-shaped hypothesis over an adversary binder), and definitions at the head of
the goal and of its sides. The ranking and the bound on the number of candidates are
shown on the same fixtures.
-/

set_option autoImplicit false

namespace CatCrypt.Tactics.AutoPremisesTest

/-- A fixture function. -/
def f (n : Nat) : Nat := n

/-- A fixture function above `f`. -/
def g (n : Nat) : Nat := n + 1

/-- A fixture function unrelated to `f` and `g`. -/
def k (n : Nat) : Nat := n

/-- A fixture bound, a definition at the head of a goal. -/
def Bound (n : Nat) : Prop := f n ≤ g n

/-- A fixture distance, a definition at the head of a side of a goal. -/
def dist (a b : Nat) : Nat := a + b

/-- A fixture adversary type. -/
structure Adversary where
  run : Nat → Nat

/-- A fixture advantage. -/
def adv (A : Adversary) : Nat := A.run 0

/-- A fixture structure of hop facts. -/
structure HopFacts : Prop where
  hybrid_bound : ∀ n, f n ≤ g n
  tail : k 0 = 0

/-- The hop lemma the file-local source finds. -/
theorem hop_fg (n : Nat) : f n ≤ g n := Nat.le_succ n

/-- A lemma about `k`, ranked below `hop_fg` on goals about `f` and `g`. -/
theorem k_id (n : Nat) : k n = n := rfl

/-- A lemma with the goal's head and one of its functions, ranked between the two. -/
theorem f_le_self (n : Nat) : f n ≤ n := Nat.le_refl n

-- Source 1 and the ranking: `hop_fg` (common head, Jaccard 4/5) before `f_le_self` (common
-- head, 3/5) before `k_id` (no common head, 1/7); the theorems generated for `Adversary`
-- and `HopFacts` and `after_goal` (stated after this example) are absent.
/--
info: premises:
1.80 fileDecl hop_fg
1.60 fileDecl f_le_self
1.00 unfold f
1.00 unfold g
0.14 fileDecl k_id
-/
#guard_msgs in
example : f 3 ≤ g 3 := by
  catcrypt_premises?
  exact hop_fg 3

-- Source 2: the fields `hybrid_bound` and `tail` of `h_bot`, and the components of the
-- conjunction `h`; `h.right` has the goal's constants and ranks first.
/--
info: premises:
2.00 hypField h.right
1.80 hypField h_bot.hybrid_bound ?n
1.80 fileDecl hop_fg
1.60 fileDecl f_le_self
1.00 unfold f
1.00 unfold g
0.63 hyp h
0.29 hypField h_bot.tail
0.29 hypField h.left
0.14 fileDecl k_id
-/
#guard_msgs in
set_option linter.unusedVariables false in
example (h_bot : HopFacts) (h : k 1 = 1 ∧ f 1 ≤ g 1) : f 2 ≤ g 2 := by
  catcrypt_premises?
  exact h_bot.hybrid_bound 2

-- Source 3: `hn` with its quantifier instantiated and the reduction `hR`; the
-- hardness-shaped `hA` (an adversary binder and a bound free of the adversary) is absent.
-- At equal score `hn ?n` ranks before `hop_fg`.
/--
info: premises:
2.00 hyp hR
1.40 fileDecl f_le_self
1.33 hyp hn ?n
1.33 fileDecl hop_fg
1.00 unfold adv
1.00 unfold k
0.40 fileDecl k_id
-/
#guard_msgs in
set_option linter.unusedVariables false in
example (hn : ∀ n : Nat, f n ≤ g n) (hA : ∀ A : Adversary, adv A ≤ 1)
    (hR : ∀ A : Adversary, adv A ≤ k (adv A)) (A₀ : Adversary) : adv A₀ ≤ k (adv A₀) := by
  catcrypt_premises?
  exact hR A₀

-- Source 4: `Bound` at the head of the goal, score 2.
/--
info: premises:
2.00 unfold Bound
0.20 fileDecl f_le_self
0.20 fileDecl k_id
0.17 fileDecl hop_fg
-/
#guard_msgs in
example : Bound 4 := by
  catcrypt_premises?
  exact hop_fg 4

-- Source 4: `dist` at the head of a side of the goal, score 1; the search stops at `dist`
-- and does not report `f`.
/--
info: premises:
1.60 fileDecl f_le_self
1.50 fileDecl hop_fg
1.00 unfold dist
0.14 fileDecl k_id
-/
#guard_msgs in
example : dist (f 1) 2 ≤ 5 := by
  catcrypt_premises?
  decide

-- The option `catcrypt_premises.max` cuts the list.
/--
info: premises:
1.80 fileDecl hop_fg
1.60 fileDecl f_le_self
-/
#guard_msgs in
example : f 3 ≤ g 3 := by
  set_option catcrypt_premises.max 2 in
  catcrypt_premises?
  exact hop_fg 3

/-- A theorem stated after the goals above, absent from their candidates. -/
theorem after_goal (n : Nat) : f n ≤ g n := hop_fg n

end CatCrypt.Tactics.AutoPremisesTest
