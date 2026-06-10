/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Lean
import CatCrypt.Crypto.Advantage

/-!
# Triangle Inequality Tactic

This file provides the `ssprove_triangle` tactic for game-hopping proofs.

## Main definitions

* `advantage_sum` - Recursive sum of pairwise advantages for a chain of games
* `Advantage_triangle_chain` - Triangle inequality for chains of games
* `ssprove_triangle` - Tactic to introduce a triangle inequality bound

## Usage

The tactic `ssprove_triangle G₀ [G₁, G₂, G₃] G₄` produces:
```
ineq : Advantage G₀ G₄ ≤
       Advantage G₀ G₁ + Advantage G₁ G₂ +
       Advantage G₂ G₃ + Advantage G₃ G₄
```

This is essential for game-hopping proofs where we transition through
a sequence of hybrid games.

## References

* CatCrypt: theories/Crypt/package/pkg_advantage.v
* [Benton et al., *Nominal CatCrypt*](https://eprint.iacr.org/2025/598)
-/

namespace CatCrypt.Crypto

open CatCrypt.Core CatCrypt.Prob
open scoped ENNReal

/-! ## Advantage Sum -/

/-- Recursive sum of pairwise advantages for a chain of games.

    `advantage_sum G₀ [G₁, G₂] G₃` = `Advantage G₀ G₁ + Advantage G₁ G₂ + Advantage G₂ G₃`

    The base case `advantage_sum G₀ [] G₁` = `Advantage G₀ G₁`. -/
noncomputable def advantage_sum (G₀ : SPComp Bool) (gs : List (SPComp Bool))
    (Gn : SPComp Bool) : ℝ≥0∞ :=
  match gs with
  | [] => Advantage G₀ Gn
  | G₁ :: rest => Advantage G₀ G₁ + advantage_sum G₁ rest Gn

/-- Triangle inequality for chains of games.

    For any sequence of games G₀, G₁, ..., Gₙ:
    `Advantage G₀ Gₙ ≤ Advantage G₀ G₁ + Advantage G₁ G₂ + ... + Advantage Gₙ₋₁ Gₙ` -/
theorem Advantage_triangle_chain (G₀ : SPComp Bool) (gs : List (SPComp Bool))
    (Gn : SPComp Bool) :
    Advantage G₀ Gn ≤ advantage_sum G₀ gs Gn := by
  induction gs generalizing G₀ Gn with
  | nil => simp only [advantage_sum, le_refl]
  | cons G₁ rest ih =>
    simp only [advantage_sum]
    calc Advantage G₀ Gn
      _ ≤ Advantage G₀ G₁ + Advantage G₁ Gn := advantage_triangle G₀ G₁ Gn
      _ ≤ Advantage G₀ G₁ + advantage_sum G₁ rest Gn :=
          add_le_add le_rfl (ih G₁ Gn)

/-! ## AdvantageA Sum -/

/-- Recursive sum of pairwise advantages with explicit adversary. -/
noncomputable def advantageA_sum {α : Type} (G₀ : SPComp α) (gs : List (SPComp α))
    (Gn : SPComp α) (A : α → SPComp Bool) : ℝ≥0∞ :=
  match gs with
  | [] => AdvantageA G₀ Gn A
  | G₁ :: rest => AdvantageA G₀ G₁ A + advantageA_sum G₁ rest Gn A

/-- Triangle inequality for AdvantageA. -/
theorem advantageA_triangle {α : Type} (G₀ G₁ G₂ : SPComp α) (A : α → SPComp Bool) :
    AdvantageA G₀ G₂ A ≤ AdvantageA G₀ G₁ A + AdvantageA G₁ G₂ A := by
  simp only [AdvantageA]
  exact advantage_triangle (G₀.bind A) (G₁.bind A) (G₂.bind A)

/-- Triangle inequality for chains with explicit adversary. -/
theorem AdvantageA_triangle_chain {α : Type} (G₀ : SPComp α) (gs : List (SPComp α))
    (Gn : SPComp α) (A : α → SPComp Bool) :
    AdvantageA G₀ Gn A ≤ advantageA_sum G₀ gs Gn A := by
  induction gs generalizing G₀ Gn with
  | nil => rfl
  | cons G₁ rest ih =>
    simp only [advantageA_sum]
    calc AdvantageA G₀ Gn A
      _ ≤ AdvantageA G₀ G₁ A + AdvantageA G₁ Gn A := advantageA_triangle G₀ G₁ Gn A
      _ ≤ AdvantageA G₀ G₁ A + advantageA_sum G₁ rest Gn A :=
          add_le_add le_rfl (ih G₁ Gn)

/-! ## Convenience Lemmas for Simplification -/

/-- Simplification lemma: expand advantage_sum for the empty list case -/
@[simp]
theorem advantage_sum_nil (G₀ Gn : SPComp Bool) :
    advantage_sum G₀ [] Gn = Advantage G₀ Gn := rfl

/-- Simplification lemma: expand advantage_sum for the cons case -/
@[simp]
theorem advantage_sum_cons (G₀ G₁ : SPComp Bool) (rest : List (SPComp Bool)) (Gn : SPComp Bool) :
    advantage_sum G₀ (G₁ :: rest) Gn = Advantage G₀ G₁ + advantage_sum G₁ rest Gn := rfl

/-- Simplification lemma: expand advantageA_sum for the empty list case -/
@[simp]
theorem advantageA_sum_nil {α : Type} (G₀ Gn : SPComp α) (A : α → SPComp Bool) :
    advantageA_sum G₀ [] Gn A = AdvantageA G₀ Gn A := rfl

/-- Simplification lemma: expand advantageA_sum for the cons case -/
@[simp]
theorem advantageA_sum_cons {α : Type} (G₀ G₁ : SPComp α) (rest : List (SPComp α))
    (Gn : SPComp α) (A : α → SPComp Bool) :
    advantageA_sum G₀ (G₁ :: rest) Gn A =
    AdvantageA G₀ G₁ A + advantageA_sum G₁ rest Gn A := rfl

end CatCrypt.Crypto

namespace CatCrypt.Tactics

open Lean Elab Tactic Meta Term
open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto

/-! ## Triangle Tactic Implementation

The `ssprove_triangle` tactic automates the application of triangle inequality
for game-hopping proofs.

### Syntax

```lean
ssprove_triangle G₀ [G₁, G₂, G₃] G₄
```

This introduces a hypothesis `ineq` with type:
```lean
Advantage G₀ G₄ ≤ Advantage G₀ G₁ + Advantage G₁ G₂ + Advantage G₂ G₃ + Advantage G₃ G₄
```

After introduction, use `simp only [advantage_sum_nil, advantage_sum_cons] at ineq`
to expand the sum into individual advantage terms.

### Variants

- `ssprove_triangle_A` - For games with explicit adversary `AdvantageA`
-/

/-- `ssprove_triangle G₀ gs Gₙ` introduces a hypothesis
    `ineq : Advantage G₀ Gₙ ≤ advantage_sum G₀ gs Gₙ`

    Where `gs` is a list of intermediate games.

    After introducing the hypothesis, use:
    `simp only [advantage_sum_nil, advantage_sum_cons] at ineq`
    to expand the sum into individual pairwise advantages.

    This is the main tactic for game-hopping proofs where we need to bound
    the advantage through a sequence of hybrid games. -/
macro "ssprove_triangle" G₀:term gs:term Gn:term : tactic =>
  `(tactic| have ineq := Advantage_triangle_chain $G₀ $gs $Gn)

/-- `ssprove_triangle_A G₀ gs Gₙ A` for AdvantageA.

    Produces: `ineq : AdvantageA G₀ Gₙ A ≤ advantageA_sum G₀ gs Gₙ A` -/
macro "ssprove_triangle_A" G₀:term gs:term Gn:term A:term : tactic =>
  `(tactic| have ineq := AdvantageA_triangle_chain $G₀ $gs $Gn $A)

/-- `ssprove_triangle_simpl` simplifies advantage_sum expressions.

    After `ssprove_triangle`, the bound is in terms of `advantage_sum`.
    This tactic expands it into explicit pairwise advantages.

    Usage: `ssprove_triangle_simpl` or `ssprove_triangle_simpl at h` -/
macro "ssprove_triangle_simpl" : tactic =>
  `(tactic| simp only [advantage_sum_nil, advantage_sum_cons,
                       advantageA_sum_nil, advantageA_sum_cons])

/-- `ssprove_triangle_simpl at h` simplifies advantage_sum in hypothesis h. -/
macro "ssprove_triangle_simpl" "at" h:ident : tactic =>
  `(tactic| simp only [advantage_sum_nil, advantage_sum_cons,
                       advantageA_sum_nil, advantageA_sum_cons] at $h:ident)

end CatCrypt.Tactics
