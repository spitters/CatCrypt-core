/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Lean
import CatCrypt.Relational.Rules
import CatCrypt.Relational.Reorder
import CatCrypt.Tactics.Basic
import CatCrypt.Tactics.Sync
import CatCrypt.Tactics.WP
import CatCrypt.Tactics.Call
import CatCrypt.Tactics.RSpec
import CatCrypt.Prob.XorBij

/-!
# Automated Bisimulation Tactic

This file provides tactics for automatic bisimulation proofs in pRHL,
analogous to EasyCrypt's `sim` tactic.

## Main tactics

* `ssprove_sim` - automatically prove equivalence by structural matching
* `ssprove_sim_bij f` - sim with explicit bijection for sampling steps
* `ssprove_sim_step` - one step of sim (match heads, apply rule)

## What EasyCrypt does

EasyCrypt's `sim` automatically proves pRHL equivalences by structurally
matching both programs and maintaining a conjunction of equalities.
It works backwards, applying coupling rules for each matching operation pair:

| Both sides have | Rule applied |
|-----------------|-------------|
| `sample T` | diagonal coupling |
| `get l` | synchronized get |
| `set l v` | synchronized set |
| `pure v` | same return |
| `sample` + bijection | bijection coupling |
| `bind c k` | decompose + recurse |

## How it maps to CatCrypt

We compose existing tactics in the same structural matching order:
1. Normalize both sides (code_simpl)
2. Try to match heads and apply appropriate relational rule
3. Recurse on continuations
4. Close remaining goals with automation

## References

* EasyCrypt: `sim` tactic
* CatCrypt/Rocq: `r_reflexivity_alt` procedure
-/

namespace CatCrypt.Relational

open CatCrypt.Core CatCrypt.Prob

variable {α β γ : Type}

/-! ## Additional Rules for Sim

These rules complement the existing sync rules for use in bisimulation.
-/

/-- Synchronized get on two possibly different locations, with the precondition
implying both heap equality and location agreement.

This rule is used by sim when both sides do `get l` for the same `l` and
the precondition implies the heaps agree on `l`.
-/
theorem rHoare_get_sync_eq {l : Location} :
    rHoare eqPre (SPComp.get l) (SPComp.get l) eqPost := by
  intro h₁ h₂ heq
  subst heq
  simp only [SPComp.get_def]
  exact liftR_pure ⟨rfl, rfl⟩

/-- Synchronized set on the same location with the same value,
preserving heap equality. -/
theorem rHoare_set_sync_eq {l : Location} {v : l.ty} :
    rHoare eqPre (SPComp.set l v) (SPComp.set l v)
      (fun _ h₁ _ h₂ => eqPre h₁ h₂) := by
  intro h₁ h₂ heq
  subst heq
  simp only [SPComp.set_def]
  exact liftR_pure rfl

/-- Sampling the same type preserves heap equality and gives equal values. -/
theorem rHoare_sample_same_eq (α : Type) [Fintype α] [Nonempty α] :
    rHoare eqPre (SPComp.sample α) (SPComp.sample α) eqPost := by
  apply rHoare_conseq (fun _ _ h => h) _ (rHoare_sample_same α)
  intro a₁ h₁ a₂ h₂ ⟨hh, hv⟩
  exact ⟨hv, hh⟩

/-- Return same value with heap equality. -/
theorem rHoare_ret_same_eq {a : α} :
    rHoare eqPre (pure a : SPComp α) (pure a : SPComp α) eqPost :=
  rHoare_ret (fun _ _ h => ⟨rfl, h⟩)

/-- Bind with eqPost intermediate and eqPost final gives eqPost. -/
theorem rHoare_bind_eq {c₁ c₂ : SPComp α} {f₁ f₂ : α → SPComp β}
    (hc : rHoare eqPre c₁ c₂ eqPost)
    (hf : ∀ a, rHoare eqPre (f₁ a) (f₂ a) eqPost) :
    rHoare eqPre (c₁.bind f₁) (c₂.bind f₂) eqPost := by
  apply rHoare_bind hc
  intro a b h₁ h₂ hpost
  obtain ⟨hab, hheq⟩ := hpost
  subst hab; subst hheq
  exact hf a h₁ h₁ rfl

end CatCrypt.Relational

namespace CatCrypt.Tactics

open Lean Elab Tactic Meta
open CatCrypt.Relational CatCrypt.Core

/-! ## Register core rules with @[rspec] -/

-- Return and reflexivity
attribute [rspec] rHoare_ret_same rHoare_refl

-- Sampling rules
attribute [rspec] rHoare_sample_same

-- Synchronized get/set
attribute [rspec] rHoare_get_sync rHoare_set_sync

-- One-sided get/put
attribute [rspec] rHoare_get_l rHoare_get_r rHoare_put_l rHoare_put_r

-- Conditionals
attribute [rspec] rHoare_ite rHoare_if

/-! ## RSpec Lookup Tactic -/

/-- `ssprove_rspec` queries the `@[rspec]` discrimination tree for a lemma
matching the current goal and applies it. -/
elab "ssprove_rspec" : tactic => do
  let goal ← Tactic.getMainGoal
  let goalTy ← goal.getType >>= instantiateMVars
  let lems ← rspecLookup goalTy
  for lem in lems do
    try
      let gs ← goal.apply (← mkConstWithFreshMVarLevels lem)
      -- Introduce binders created by the applied lemma
      for g in gs do
        try
          let (_, g') ← g.intro1
          Tactic.replaceMainGoal [g']
        catch _ => pure ()
      return
    catch _ => pure ()
  throwError "ssprove_rspec: no matching rspec lemma found"

/-! ## Reorder Tactic -/

/-- `ssprove_reorder` tries to commute mismatched head operations to align
    both sides of a pRHL judgment. It applies reorder rules from
    `CatCrypt.Relational.Reorder` as a fallback when heads don't match.

    Tries (in order):
    1. `rHoare_sample_comm` — both sides sample but in opposite type order
    2. `rHoare_reorder_pure_l` — commute IsPure past anything on LHS
    3. `rHoare_reorder_pure_r` — same for RHS
    4. `rHoare_sample_past_get_l` — commute sample past get on LHS
    5. `rHoare_sample_past_set_l` — commute sample past set on LHS -/
macro "ssprove_reorder" : tactic => `(tactic| (
  first
  -- Opposite-order sampling
  | (apply rHoare_sample_comm; intro _ _)
  -- Pure commutativity (needs IsPure proof)
  | (apply rHoare_reorder_pure_l <;> [exact SPComp.sample_isPure _; skip])
  | (apply rHoare_reorder_pure_l <;> [exact SPComp.pure_isPure _; skip])
  | (apply rHoare_reorder_pure_r <;> [exact SPComp.sample_isPure _; skip])
  | (apply rHoare_reorder_pure_r <;> [exact SPComp.pure_isPure _; skip])
  -- Sample past get/set
  | apply rHoare_sample_past_get_l
  | apply rHoare_sample_past_set_l
))

/-! ## Sim Tactics -/

/-- `ssprove_sim_step` matches the head operation on both sides
and applies the appropriate relational rule.

It tries (in order):
1. Same return value → `rHoare_ret_same`
2. Same sample → `rHoare_sample_same`
3. Synchronized get → `rHoare_get_sync`
4. Synchronized set → `rHoare_set_sync`
5. Bind decomposition → `rHoare_bind`

After applying a rule, it introduces continuation variables if needed.
-/
macro "ssprove_sim_step" : tactic => `(tactic| (
  first
  -- Reflexivity shortcuts (identical code)
  | apply rHoare_refl
  | apply rHoare_ret_same_eq
  | apply rHoare_ret_same
  -- Sampling rules
  | apply rHoare_sample_same_eq
  | apply rHoare_sample_same
  -- Get rules
  | apply rHoare_get_sync_eq
  | (apply rHoare_get_sync <;> [intro h₁ h₂ _; rfl])
  | (apply rHoare_get_sync <;> [intro h₁ h₂ heq; rw [heq]])
  -- Set rules
  | apply rHoare_set_sync_eq
  | (apply rHoare_set_sync <;> [intro h₁ h₂ _; assumption])
  | (apply rHoare_set_sync <;> [intro h₁ h₂ heq; rw [heq]])
  -- Combined coupling steps (sample >>= k with same distribution)
  | (apply rHoare_same_step; intro _)
  -- Bind decomposition (with eqPost intermediate or general)
  | (apply rHoare_bind_eq <;> [skip; intro _])
  | (apply rHoare_bind <;> [skip; intro _ _])
  -- WP to absorb tail
  | ssprove_wp_step
  -- RSpec lookup: query @[rspec] discrimination tree
  | ssprove_rspec
  -- Reorder: commute mismatched heads
  | ssprove_reorder
  | fail "ssprove_sim_step: no matching heads"
))

/-- `ssprove_sim` automatically proves pRHL equivalences by
structurally matching both programs.

The tactic:
1. Normalizes both sides (code_simpl)
2. Repeatedly matches heads and applies coupling rules
3. Tries to close remaining goals with automation

This handles most cases where both programs have the same structure
and perform the same operations in the same order.

Example:
```
-- Identical programs
theorem sim_ident : rHoare eqPre
    (do let k ← SPComp.sample Bool; SPComp.pure k)
    (do let k ← SPComp.sample Bool; SPComp.pure k)
    eqPost := by
  ssprove_sim

-- Same structure with rfl-closable side conditions
theorem sim_sample_get : rHoare eqPre
    (do let x ← SPComp.sample Bool; let v ← SPComp.get l; SPComp.pure (x, v))
    (do let x ← SPComp.sample Bool; let v ← SPComp.get l; SPComp.pure (x, v))
    eqPost := by
  ssprove_sim
```
-/
macro "ssprove_sim" : tactic => `(tactic| (
  try ssprove_code_simpl
  repeat ssprove_sim_step
  -- Try to close remaining goals
  all_goals (first
    | rfl
    | assumption
    | (constructor <;> [rfl; rfl])
    | (intro _ _ _ _ h; exact h)
    | (intro _ _ _ _ ⟨h, _⟩; exact h)
    | (intro _ _ _ _ ⟨_, h⟩; exact h)
    | simp_all
    | grind
    | skip)
))

/-- `ssprove_sim_bij f` applies sim with an explicit bijection for
the first sampling step.

Use this when the two programs sample from the same type but relate
the samples through a bijection `f`.

Example:
```
-- Programs related by negation bijection
theorem sim_bij : rHoare eqPre
    (SPComp.sample Bool)
    (SPComp.sample Bool)
    (fun a h₁ b h₂ => eqPre h₁ h₂ ∧ notBij a = b) := by
  ssprove_sim_bij notBij
```
-/
macro "ssprove_sim_bij" f:term : tactic => `(tactic| (
  try ssprove_code_simpl
  first
  | (ssprove_sync_bij $f)
  | (ssprove_bind
     · ssprove_sync_bij $f
     · intro _ _; ssprove_sim)
  all_goals (first | rfl | assumption | simp_all | skip)
))

/-- `ssprove_sim_eq` proves equivalence under eqPre/eqPost.

Specialized version of sim that maintains heap equality throughout.
More aggressive at closing goals since it knows the invariant.
-/
macro "ssprove_sim_eq" : tactic => `(tactic| (
  try ssprove_code_simpl
  first
  | apply rHoare_refl
  | (repeat (first
      | apply rHoare_bind_eq <;> [skip; intro _]
      | apply rHoare_sample_same_eq
      | apply rHoare_get_sync_eq
      | apply rHoare_set_sync_eq
      | apply rHoare_ret_same_eq
      | apply rHoare_refl)
     all_goals (first | rfl | assumption | simp_all | skip))
))

/-- `ssprove_sim_auto` extends `ssprove_sim` with automatic postcondition inference.

When both sides sample from the same distribution but apply different
pure functions, it automatically closes the proof by:
1. Using `ssprove_sim_step` rules (including `rHoare_same_step`)
2. Applying `rHoare_ret` to reduce return goals to value equations
3. Trying `simp_all`/`grind` to close the value equations

This automates the most common manual postcondition pattern:
sample same distribution, apply different functions, prove results equal.

Example:
```
-- Both sides sample a Bool, but apply different functions.
-- ssprove_sim_auto closes this automatically.
theorem example : rHoare eqPre
    (do let k ← SPComp.sample Bool; SPComp.pure (k && true))
    (do let k ← SPComp.sample Bool; SPComp.pure k)
    eqPost := by
  ssprove_sim_auto
```
-/
macro "ssprove_sim_auto" : tactic => `(tactic| (
  -- NOTE: We intentionally do NOT call ssprove_code_simpl here.
  -- It applies SPComp.bind_pure which can asymmetrically simplify
  -- `(sample T).bind pure` → `sample T` on one side while leaving
  -- `(sample T).bind (fun k => pure (f k))` unchanged on the other,
  -- breaking rHoare_same_step which needs bind on both sides.
  repeat (first
    -- All standard sim rules (reflexivity, sample, get, set, same_step, bind, wp)
    | ssprove_sim_step
    -- Return with possibly different values: close postcondition via automation
    | (apply rHoare_ret; intro _ _ _; first | simp_all [eqPost, eqPre] | grind))
  -- Try to close remaining goals
  all_goals (first
    | rfl
    | assumption
    | (constructor <;> [rfl; rfl])
    | (intro _ _ _ _ h; exact h)
    | (intro _ _ _ _ ⟨h, _⟩; exact h)
    | (intro _ _ _ _ ⟨_, h⟩; exact h)
    | simp_all [eqPost, eqPre]
    | grind
    | skip)
))

/-- `ssprove_try_bij f` applies a bijection coupling step with bijection `f`.

This is a convenience wrapper around `rHoare_bij_step` that also
introduces the sampled value.

Example:
```
-- Couple via XOR bijection
ssprove_try_bij (boolXorBij m)
-- Goal becomes: ∀ k, rHoare Φ (k₁ k) (k₂ (xor k m)) Ψ
```
-/
macro "ssprove_try_bij" f:term : tactic => `(tactic| (
  first
  | (apply rHoare_bij_step $f; intro _)
  | (apply rHoare_bij_step_bare_r $f; intro _)
  | (apply rHoare_bij_step_bare_l $f; intro _)
))

end CatCrypt.Tactics
