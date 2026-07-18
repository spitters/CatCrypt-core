/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# `field_clear` tactic

Extends `field_simp` for proofs where the goal denominators are
ring-equivalent to provided hypotheses but not syntactically identical
(e.g. after `(n/D)²` expansion or commutative reordering).

## Pattern

`field_simp` does syntactic matching: a hypothesis `h : a ≠ 0` only
clears `a⁻¹` from the goal if `a` appears literally as written. After
intermediate `ring_nf` or expansion, the goal denominator may be in a
ring-equivalent but syntactically different form (e.g. `1 + 2D + D²`
vs `(1+D)²`, or `Y*X` vs `X*Y`), so the match fails.

## Strategy

Given hypotheses `hA : a ≠ 0`, `hB : b ≠ 0`, ..., `field_clear`
auto-derives common variants:
- `pow_ne_zero 2 hA : a² ≠ 0` and `pow_ne_zero 3 hA : a³ ≠ 0`
- `mul_ne_zero (two_ne_zero) hA : 2 * a ≠ 0`
- `mul_ne_zero hA hB : a * b ≠ 0` (pairwise products)

then calls `field_simp` with the augmented set. Designed for use after
the SymPy-witness + `set` atoms approach (see
`~/.claude/skills/rocq-to-lean-porting/field_fsatz_porting.md`).

## Caveats

This is a heuristic — it doesn't solve the general problem of
ring-equivalent matching. It auto-derives specific variants that arise
in `Field.fsatz`-style algebraic-curve proofs. If a denominator in the
goal is in some other ring-equivalent form (e.g. `1 + 2*D*X*Y` vs
`1 + 2*Y*X*D`), the user must either reformulate the hypothesis to
match, or extend this tactic.
-/

namespace CatCrypt.Tactic.FieldClear

open Lean Elab Tactic Meta

/-- `field_clear [h₁, h₂, ...]` augments `field_simp`'s hypothesis
    list with squared and pairwise-product variants of the supplied
    nonzero hypotheses, then invokes `field_simp` plus `ring_nf` for
    cleanup.

    Usage:
    ```
    have hA : a ≠ 0 := …
    have hB : b ≠ 0 := …
    field_clear [hA, hB]
    -- behaves like:
    --   have hA_sq : a^2 ≠ 0 := pow_ne_zero 2 hA
    --   have hB_sq : b^2 ≠ 0 := pow_ne_zero 2 hB
    --   have hAB   : a * b ≠ 0 := mul_ne_zero hA hB
    --   field_simp [hA, hB, hA_sq, hB_sq, hAB]
    --   ring_nf
    ```

    For specific ring-equivalent forms not caught by this default
    augmentation, the user can provide them explicitly in the
    hypothesis list. -/
syntax (name := fieldClear) "field_clear" "[" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| field_clear [$hs:term,*]) => do
    let hsArr := hs.getElems
    let mut allHs : Array (TSyntax `term) := hsArr
    -- Generate squared forms
    for (h, i) in hsArr.zip (Array.range hsArr.size) do
      let id := Lean.mkIdent (Name.mkSimple s!"_field_clear_sq_{i}")
      Lean.Elab.Tactic.evalTactic (← `(tactic| have $id:ident := pow_ne_zero 2 $h))
      allHs := allHs.push (← `($id:ident))
    -- (Doubled forms `2 * x ≠ 0` skipped: requires `NeZero 2` instance which
    -- isn't available for arbitrary `Field F`. Users in characteristic-≠2
    -- contexts should provide doubled hypotheses explicitly.)
    -- Generate pairwise products
    for i in [:hsArr.size] do
      for j in [(i+1):hsArr.size] do
        let id := Lean.mkIdent (Name.mkSimple s!"_field_clear_prod_{i}_{j}")
        Lean.Elab.Tactic.evalTactic
          (← `(tactic| have $id:ident := mul_ne_zero $(hsArr[i]!) $(hsArr[j]!)))
        allHs := allHs.push (← `($id:ident))
    -- Now invoke field_simp with the full augmented hypothesis set,
    -- followed by `ring_nf` (and a final `ring`) to close polynomial
    -- residues. Use `ring_nf` first because it can close goals where
    -- `ring` fails (non-canonical form, residual `(...)⁻¹`, etc.).
    let hList ← allHs.mapM fun h =>
      `(Lean.Parser.Tactic.simpLemma| $h:term)
    Lean.Elab.Tactic.evalTactic
      (← `(tactic| (field_simp [$[$hList],*]; try ring_nf; try ring)))

end CatCrypt.Tactic.FieldClear
