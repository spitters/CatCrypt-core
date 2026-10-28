/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean.Elab.Command
public meta import Lean.Elab.Command

/-!
# Literal characteristic instances for `grind`

The ring solver of `grind` reduces coefficients modulo the characteristic `p` of a ring `α`
when it finds an instance `Lean.Grind.IsCharP α p` whose index `p` its evaluator `evalNat?`
reads as a numeral. That evaluator handles literals and arithmetic on literals and does not
unfold constants. For a field `ZMod q` with a named modulus `q` (a `def`, an `abbrev` or an
`irreducible_def`), the instance found has index `q`, and `grind` works over the integers.

* `isCharP_ofEq` transports an instance `Lean.Grind.IsCharP α n` along an equation
  `n = m`.
* `grind_char_numeral α` finds the instance `Lean.Grind.IsCharP α n`, reduces `n` to a
  numeral `p` (whnf with all transparency), and declares the instance
  `Lean.Grind.IsCharP α p` at high priority, proved by `isCharP_ofEq` and
  `decide +kernel`.
  `grind_char_numeral α using h` takes an equation `h : n = e` whose right side reduces to
  a numeral, for a modulus that does not unfold (an `irreducible_def`, with `h` its
  `_def` equation).
-/

public section

universe u

namespace CatCrypt.Tactic.GrindChar

/-- An instance `Lean.Grind.IsCharP α n` gives `Lean.Grind.IsCharP α m` when `n = m`. -/
theorem isCharP_ofEq {α : Type u} [Lean.Grind.Semiring α] {n m : Nat}
    [inst : Lean.Grind.IsCharP α n] (h : n = m) : Lean.Grind.IsCharP α m :=
  h ▸ inst

end CatCrypt.Tactic.GrindChar

meta section

open Lean Elab Command Meta

namespace CatCrypt.Tactic.GrindChar

/-- The numeral that `e` reduces to under whnf with all transparency, if any. -/
def numeralOf? (e : Expr) : MetaM (Option Nat) := do
  let e ← withTransparency .all <| whnf (← instantiateMVars e)
  match e with
  | .lit (.natVal v) => return some v
  | _ => return e.nat?

/-- `grind_char_numeral α` declares `Lean.Grind.IsCharP α p` for the numeral `p` that the
index of the instance `Lean.Grind.IsCharP α n` in scope reduces to.
`grind_char_numeral α using h` reads `p` from the right side of `h : n = e`. -/
syntax (name := grindCharNumeral) "grind_char_numeral " term (" using " term)? : command

/-- Elaborator of `grind_char_numeral`. -/
@[command_elab grindCharNumeral]
def elabGrindCharNumeral : CommandElab := fun stx => do
  match stx with
  | `(grind_char_numeral $ty $[using $h?]?) =>
    let (nStx, lit) ← liftTermElabM do
      let inst ← Term.elabTerm (← `((inferInstance : Lean.Grind.IsCharP $ty _))) none
      Term.synthesizeSyntheticMVarsNoPostponing
      let n := (← instantiateMVars (← inferType inst)).appArg!
      let nStx ← withOptions (·.setBool `pp.fullNames true) <| PrettyPrinter.delab n
      let v ← match h? with
      | none =>
        let some v ← numeralOf? n
          | throwErrorAt ty
              m!"grind_char_numeral: the characteristic {n} is not a numeral; add `using` h"
        pure v
      | some h =>
        let pf ← Term.elabTerm h none
        Term.synthesizeSyntheticMVarsNoPostponing
        let some (_, _, rhs) := (← instantiateMVars (← inferType pf)).eq?
          | throwErrorAt h m!"grind_char_numeral: `using` expects an equation `{n} = e`"
        let some v ← numeralOf? rhs
          | throwErrorAt h m!"grind_char_numeral: {rhs} does not reduce to a numeral"
        pure v
      return (nStx, v)
    let litStx := Syntax.mkNumLit (toString lit)
    let pf ← match h? with
      | some h => `(Eq.trans $h (by decide +kernel))
      | none => `((by decide +kernel))
    elabCommand (← `(instance (priority := high) : Lean.Grind.IsCharP $ty $litStx :=
        CatCrypt.Tactic.GrindChar.isCharP_ofEq (n := $nStx) $pf))
  | _ => throwUnsupportedSyntax

end CatCrypt.Tactic.GrindChar
