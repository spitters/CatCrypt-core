/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean

/-!
# `#decl_fingerprint` — a hash of a declaration's statement

`#decl_fingerprint n₁ n₂ …` logs one information message per named constant:

```
decl_fingerprint <full name> kind=<kind> stmt=<16 hex> pp=<16 hex> value=<16 hex or ->
```

* `kind` is the constructor of the `ConstantInfo`: `theorem`, `def`, `axiom`, `opaque`,
  `inductive`, `ctor`, `recursor` or `quot`. An instance is a `def`.
* `stmt` hashes the structure of the type (`Expr.hash`), the binder infos of its leading
  `∀`-telescope and its universe parameter names. `Expr.hash` ignores binder names and binder
  infos, so renaming a bound variable leaves `stmt` unchanged while turning an implicit
  argument of the statement into an explicit one changes it. The hash is computed from names,
  levels and literals only, so it is the same in every elaboration of the same statement.
* `pp` hashes the universe parameter names and the pretty-printed type under
  `pp.fullNames` and `pp.universes`. It depends on the notations in scope where the command
  runs, so it is comparable only between runs of the command from the same imports.
* `value` hashes the body of a `def` (`-` for every other kind), so a changed definition body
  is visible although its type is unchanged.

An unknown name is reported as an error at its position.

Usage, in a file importing the modules that declare the constants:

```
import CatCryptCore.Tactics.DeclFingerprint

#decl_fingerprint Nat.add_comm List.length
```

## Main definitions

* `#decl_fingerprint`: the command.
* `statementHash`, `ppHash`: the two hashes of a constant's type.
-/

public section

meta section

open Lean Elab Command Meta

namespace CatCrypt.Tactic.DeclFingerprint

/-- Mix the binder infos of the leading `∀`-telescope of `e` into `h`. -/
def spineBinderHash : Expr → UInt64 → UInt64
  | .forallE _ _ b bi, h => spineBinderHash b (mixHash h (hash bi))
  | _, h => h

/-- A `UInt64` as sixteen lower-case hexadecimal digits. -/
def hex16 (h : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 h.toNat)
  "".pushn '0' (16 - s.length) ++ s

/-- The name of the `ConstantInfo` constructor of `ci`. -/
def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quot"

/-- The structural hash of the statement of `ci`: `Expr.hash` of its type, the binder infos
of the type's leading `∀`-telescope and the universe parameter names. -/
def statementHash (ci : ConstantInfo) : UInt64 :=
  mixHash (hash ci.levelParams) (spineBinderHash ci.type ci.type.hash)

/-- The hash of the universe parameter names and the type of `ci` pretty-printed with
`pp.fullNames` and `pp.universes`. -/
def ppHash (ci : ConstantInfo) : MetaM UInt64 := do
  let fmt ← withOptions (fun o => (o.setBool `pp.fullNames true).setBool `pp.universes true) <|
    ppExpr ci.type
  return hash s!"{ci.levelParams} {fmt.pretty 1000000}"

/-- The fingerprint line of `ci`. -/
def fingerprintLine (ci : ConstantInfo) : MetaM String := do
  let value := match ci with
    | .defnInfo v => hex16 v.value.hash
    | _ => "-"
  return s!"decl_fingerprint {ci.name} kind={kindOf ci} stmt={hex16 (statementHash ci)} \
    pp={hex16 (← ppHash ci)} value={value}"

/-- `#decl_fingerprint n₁ n₂ …` logs, for each named constant, its full name, its kind, the
hashes `stmt` and `pp` of its statement and the hash `value` of a definition's body. -/
syntax (name := declFingerprint) "#decl_fingerprint" (ppSpace ident)+ : command

@[command_elab declFingerprint]
def elabDeclFingerprint : CommandElab := fun stx => do
  match stx with
  | `(#decl_fingerprint $ids*) =>
    for id in ids do
      try
        let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
        let ci ← getConstInfo n
        let line ← liftTermElabM <| fingerprintLine ci
        logInfoAt id line
      catch e =>
        logErrorAt id m!"decl_fingerprint {id.getId} missing: {e.toMessageData}"
  | _ => throwUnsupportedSyntax

end CatCrypt.Tactic.DeclFingerprint
