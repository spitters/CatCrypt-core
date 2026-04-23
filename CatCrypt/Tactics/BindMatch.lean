/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Core.Code

/-!
# Bind-Match Normalization and Swap Tactics

Do-notation like `let (a, b) ← c; rest a b` desugars to
`SPComp.bind c (fun __discr => match __discr with | (a, b) => rest a b)`.

This match prefix blocks `SPComp.isPure_bind_comm`, which expects the
`bind c₁ (fun a => bind c₂ (fun b => k a b))` form without intervening
matches.

This file provides:

* `SPComp.bind_pair_match` — simp lemma replacing a pair-match inside a
  bind with explicit `.1` / `.2` projections.
* `@[ssprove_bind_norm]` simp attribute collecting the normalization.
* `ssprove_bind_comm_ispure` — tactic that normalizes pair/triple matches
  in both sides of the goal, then applies `isPure_bind_comm` to commute
  the first two `IsPure` binds.

With these tools, game-equality proofs that need to commute independent
`IsPure` samplings across `do`-notation match expressions become a single
tactic call.
-/

namespace CatCrypt.Core.SPComp

open CatCrypt.Core

variable {α β γ δ : Type*}

/-! ## Match-to-projection normalization -/

/-- Pair-match under a `SPComp.bind` reduces to `.1`/`.2` projections.

    This converts do-notation tuple destructuring back into the pattern
    that `isPure_bind_comm` expects. Definitionally true by match-eta. -/
@[simp]
theorem bind_pair_match (c : SPComp (α × β)) (k : α → β → SPComp γ) :
    (c.bind (fun p => match p with | (a, b) => k a b)) =
    c.bind (fun p => k p.1 p.2) := by
  congr

/-- Triple-match normalization. -/
@[simp]
theorem bind_triple_match (c : SPComp (α × β × γ)) (k : α → β → γ → SPComp δ) :
    (c.bind (fun p => match p with | (a, b, d) => k a b d)) =
    c.bind (fun p => k p.1 p.2.1 p.2.2) := by
  congr

/-- Nested pair-match with inner pair. -/
@[simp]
theorem bind_pair_pair_match (c : SPComp ((α × β) × γ))
    (k : α → β → γ → SPComp δ) :
    (c.bind (fun p => match p with | ((a, b), d) => k a b d)) =
    c.bind (fun p => k p.1.1 p.1.2 p.2) := by
  congr

/-! ## Tactic: commute two independent IsPure binds through matches -/

/-- `ssprove_bind_comm_ispure c₁ c₂ hc₁ hc₂` commutes two `IsPure`
computations `c₁`, `c₂` past any intervening do-notation pair-matches.

Equivalent to: normalize pair/triple matches via `simp` on
`bind_pair_match` / `bind_triple_match`, then `rw [isPure_bind_comm c₁ c₂ _ hc₁ hc₂]`.

Typical usage:
```
theorem game_reorder (P : Params) :
    realGame P = idealReduction P := by
  unfold realGame idealReduction
  ssprove_bind_comm_ispure P.keygen P.keygen P.keygen_isPure P.keygen_isPure
```
-/
syntax (name := ssproveBindCommIsPure) "ssprove_bind_comm_ispure" term:max term:max term:max term:max : tactic

macro_rules
  | `(tactic| ssprove_bind_comm_ispure $c₁ $c₂ $hc₁ $hc₂) =>
    `(tactic| (
        simp only [bind_pair_match, bind_triple_match, bind_pair_pair_match]
        rw [SPComp.isPure_bind_comm $c₁ $c₂ _ $hc₁ $hc₂]))

/-- Shorter alias when both IsPure facts are accessible by the same name
(e.g. `P.dh.keygen_isPure`). -/
syntax (name := ssproveBindCommSelf) "ssprove_bind_comm_self" term:max term:max : tactic

macro_rules
  | `(tactic| ssprove_bind_comm_self $c $hc) =>
    `(tactic| ssprove_bind_comm_ispure $c $c $hc $hc)

/-! ## Tactic: deep bind-comm on LHS via conv navigation

`ssprove_swap_binds_deep c₁ c₂ hc₁ hc₂` performs a `rw [isPure_bind_comm]`
even when the target pattern is nested below outer bind lambdas. It
navigates *only* the LHS (via `conv_lhs`), so divergence between LHS and
RHS outer structure is not an issue.

At each step, the tactic:
1. Tries the rewrite at the current conv focus.
2. On failure, drills into the continuation of the outermost `bind` by
   navigating `arg 2` (the function arg of `SPComp.bind`) then `ext` to
   enter the lambda body.
3. Recurses on the new focus.

Because conv modifies only LHS (or only RHS, etc.), the sibling side is
untouched. This makes the tactic safe to use even when LHS and RHS have
fundamentally different outer structures. -/

/-- `ssprove_swap_binds_deep c₁ c₂ hc₁ hc₂` — apply bind-comm swap at any
depth within the LHS, up to 5 levels deep. The tactic enumerates depths
0–5, drilling through the bind chain via `arg 2; ext _` at each step,
until the rewrite succeeds. All drilling happens inside a single
`conv_lhs` block so focus is preserved. -/
macro "ssprove_swap_binds_deep"
    c₁:term:max c₂:term:max hc₁:term:max hc₂:term:max : tactic =>
  `(tactic|
    conv_lhs =>
      first
      | rw [SPComp.isPure_bind_comm $c₁ $c₂ _ $hc₁ $hc₂]
      | (arg 2; ext _
         rw [SPComp.isPure_bind_comm $c₁ $c₂ _ $hc₁ $hc₂])
      | (arg 2; ext _; arg 2; ext _
         rw [SPComp.isPure_bind_comm $c₁ $c₂ _ $hc₁ $hc₂])
      | (arg 2; ext _; arg 2; ext _; arg 2; ext _
         rw [SPComp.isPure_bind_comm $c₁ $c₂ _ $hc₁ $hc₂])
      | (arg 2; ext _; arg 2; ext _; arg 2; ext _; arg 2; ext _
         rw [SPComp.isPure_bind_comm $c₁ $c₂ _ $hc₁ $hc₂])
      | (arg 2; ext _; arg 2; ext _; arg 2; ext _; arg 2; ext _; arg 2; ext _
         rw [SPComp.isPure_bind_comm $c₁ $c₂ _ $hc₁ $hc₂]))

/-- `ssprove_swap_at n c₁ c₂ hc₁ hc₂` — apply bind-comm swap at exactly
depth `n` within the LHS. Unlike `ssprove_swap_binds_deep` which finds the
first match, this variant forces the swap at the specified depth. -/
macro "ssprove_swap_at_0"
    c₁:term:max c₂:term:max hc₁:term:max hc₂:term:max : tactic =>
  `(tactic|
    conv_lhs => rw [SPComp.isPure_bind_comm $c₁ $c₂ _ $hc₁ $hc₂])

macro "ssprove_swap_at_1"
    c₁:term:max c₂:term:max hc₁:term:max hc₂:term:max : tactic =>
  `(tactic|
    conv_lhs => (arg 2; ext _
                 rw [SPComp.isPure_bind_comm $c₁ $c₂ _ $hc₁ $hc₂]))

macro "ssprove_swap_at_2"
    c₁:term:max c₂:term:max hc₁:term:max hc₂:term:max : tactic =>
  `(tactic|
    conv_lhs => (arg 2; ext _; arg 2; ext _
                 rw [SPComp.isPure_bind_comm $c₁ $c₂ _ $hc₁ $hc₂]))

macro "ssprove_swap_at_3"
    c₁:term:max c₂:term:max hc₁:term:max hc₂:term:max : tactic =>
  `(tactic|
    conv_lhs => (arg 2; ext _; arg 2; ext _; arg 2; ext _
                 rw [SPComp.isPure_bind_comm $c₁ $c₂ _ $hc₁ $hc₂]))

macro "ssprove_swap_at_4"
    c₁:term:max c₂:term:max hc₁:term:max hc₂:term:max : tactic =>
  `(tactic|
    conv_lhs => (arg 2; ext _; arg 2; ext _; arg 2; ext _; arg 2; ext _
                 rw [SPComp.isPure_bind_comm $c₁ $c₂ _ $hc₁ $hc₂]))

macro "ssprove_swap_at_5"
    c₁:term:max c₂:term:max hc₁:term:max hc₂:term:max : tactic =>
  `(tactic|
    conv_lhs =>
      (arg 2; ext _; arg 2; ext _; arg 2; ext _; arg 2; ext _; arg 2; ext _
       rw [SPComp.isPure_bind_comm $c₁ $c₂ _ $hc₁ $hc₂]))

macro "ssprove_swap_at_6"
    c₁:term:max c₂:term:max hc₁:term:max hc₂:term:max : tactic =>
  `(tactic|
    conv_lhs =>
      (arg 2; ext _; arg 2; ext _; arg 2; ext _; arg 2; ext _; arg 2; ext _; arg 2; ext _
       rw [SPComp.isPure_bind_comm $c₁ $c₂ _ $hc₁ $hc₂]))

macro "ssprove_swap_at_7"
    c₁:term:max c₂:term:max hc₁:term:max hc₂:term:max : tactic =>
  `(tactic|
    conv_lhs =>
      (arg 2; ext _; arg 2; ext _; arg 2; ext _; arg 2; ext _; arg 2; ext _; arg 2; ext _
       arg 2; ext _
       rw [SPComp.isPure_bind_comm $c₁ $c₂ _ $hc₁ $hc₂]))

end CatCrypt.Core.SPComp
