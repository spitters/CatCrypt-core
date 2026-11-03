/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean

/-!
# Classical decisions and choice in costed forms

A time certificate charges the steps of an algorithm. A decision `if c then … else …` whose
`Decidable c` instance is classical, and a data term computed by `Classical.choice`, have no
algorithm, so a cost assigned to them is not a running time. This module detects both.

* `classicalIn? e` — a subterm of `e` in a data position (not a closed proof or type) that is
  `Classical.choice` or a constant marked `noncomputable`. A `Decidable` instance with such a
  subterm is classical. Constants are not unfolded: the compiler refuses a computable
  definition that mentions a noncomputable constant in a data position.
* `choiceConstants` — the constants that compute data by choice.
* `classicalHits e` — the decisions (`ite`, `dite`, `Decidable.decide`) of `e` by a classical
  instance, the other occurrences of a classical `Decidable` instance, and the applications of
  a choice constant.
* `#classical_cost_audit` — reports the hits in the value of every constant of the
  environment whose name ends in `timed` or `timedCost`; `#classical_cost_audit N` restricts
  the scan to the constants under the prefix `N`.

`Classical.arbitrary` is not a choice constant here: `derive_timed` prices a default value as
free.
-/

public section

meta section

namespace CatCrypt.Tactics.ClassicalCostAudit

open Lean Elab Meta Command

/-- The constants that compute data by the axiom of choice: a term headed by one of them has
no running time. -/
def choiceConstants : Array Name :=
  #[``Classical.choice, ``Classical.choose, ``Exists.choose, ``Classical.epsilon,
    ``Classical.indefiniteDescription, ``Classical.strongIndefiniteDescription]

/-- Whether the constant `c` has no algorithm: `Classical.choice`, or marked `noncomputable`. -/
def isClassicalConst (env : Environment) (c : Name) : Bool :=
  c == ``Classical.choice || isNoncomputable env c

/-- Whether the argument `a` is in a data position: an open term, or a closed term that is
neither a proof nor a type. -/
def isDataArg (a : Expr) : MetaM Bool := do
  if a.hasLooseBVars then return true
  try return !(← isProof a) && !(← isType a) catch _ => return true

/-- A subterm of `e` in a data position that is `Classical.choice` or an application of a
constant marked `noncomputable`; `none` when there is none. A `Decidable` instance `e` with
such a subterm is classical. -/
partial def classicalIn? (e : Expr) : MetaM (Option Expr) := do
  let e := e.consumeMData
  match e with
  | .const c _ => return if isClassicalConst (← getEnv) c then some e else none
  | .app .. =>
    let f := e.getAppFn
    if let .const c _ := f then
      if isClassicalConst (← getEnv) c then return some e
    else if let some h ← classicalIn? f then return some h
    for a in e.getAppArgs do
      if ← isDataArg a then
        if let some h ← classicalIn? a then return some h
    return none
  | .lam _ _ b _ => classicalIn? b
  | .letE _ _ v b _ =>
    if let some h ← classicalIn? v then return some h
    classicalIn? b
  | .proj _ _ s => classicalIn? s
  | _ => return none

/-- A finding of `classicalHits`. -/
inductive Hit where
  /-- A decision of the condition `cond` by the classical instance `inst`. -/
  | decision (cond inst : Expr)
  /-- A classical `Decidable` instance outside the instance position of a decision. -/
  | inst (inst : Expr)
  /-- A data term computed by a choice constant. -/
  | choice (term : Expr)

/-- The message of a hit. -/
def Hit.msg : Hit → MessageData
  | .decision c i => m!"decides `{c}` by a classical instance (`{i}`)"
  | .inst i => m!"uses the classical instance `{i}`"
  | .choice t => m!"computes `{t}` by Classical.choice"

/-- Whether the constant `c` is a `Decidable` instance: its type ends in `Decidable _`, after
unfolding reducible definitions (`DecidableEq`, `DecidablePred`). -/
def isDecidableConst (c : Name) : MetaM Bool := do
  let some info := (← getEnv).find? c | return false
  forallTelescopeReducing info.type fun _ b => return (← whnfR b).isAppOf ``Decidable

/-- The condition and the instance of a decision `ite`, `dite` or `Decidable.decide` with the
arguments `args`. -/
def decisionArgs? (c : Name) (args : Array Expr) : Option (Expr × Expr) :=
  if (c == ``ite || c == ``dite) && args.size ≥ 3 then some (args[1]!, args[2]!)
  else if c == ``Decidable.decide && args.size ≥ 2 then some (args[0]!, args[1]!)
  else none

/-- The walk of `classicalHits`, recording into `r` and skipping the terms in `seen`. -/
partial def hitsGo (r : IO.Ref (Array Hit)) (seen : IO.Ref (Std.HashSet Expr)) (e : Expr) :
    MetaM Unit := do
  if (← seen.get).contains e then return
  seen.modify (·.insert e)
  match e with
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    if let .const c _ := f then
      if choiceConstants.contains c then
        r.modify (·.push (.choice e))
        return
      if isNoncomputable (← getEnv) c && (← isDecidableConst c) then
        r.modify (·.push (.inst e))
        return
      if let some (cond, inst) := decisionArgs? c args then
        if (← classicalIn? inst).isSome then
          r.modify (·.push (.decision cond inst))
          for a in args, i in [0:args.size] do
            unless i == (if c == ``Decidable.decide then 1 else 2) do hitsGo r seen a
          return
    else hitsGo r seen f
    for a in args do hitsGo r seen a
  | .const c _ =>
    if choiceConstants.contains c then r.modify (·.push (.choice e))
    else if isNoncomputable (← getEnv) c && (← isDecidableConst c) then
      r.modify (·.push (.inst e))
  | .lam _ t b _ | .forallE _ t b _ => hitsGo r seen t; hitsGo r seen b
  | .letE _ t v b _ => hitsGo r seen t; hitsGo r seen v; hitsGo r seen b
  | .mdata _ b | .proj _ _ b => hitsGo r seen b
  | _ => pure ()

/-- The decisions by a classical instance, the other classical `Decidable` instances and the
choices in data of the term `e`. -/
def classicalHits (e : Expr) : MetaM (Array Hit) := do
  let r ← IO.mkRef #[]
  let seen ← IO.mkRef {}
  hitsGo r seen e
  r.get

/-- Whether the name `n` is that of a costed form or a cost: its last component is `timed` or
`timedCost`. -/
def isCostedName (n : Name) : Bool :=
  match n with
  | .str _ s => s == "timed" || s == "timedCost"
  | _ => false

/-- The hits of every costed form and cost of the environment under the prefix `pre`
(`Name.anonymous` for all), one line per constant with a hit, with the number of constants
scanned. The binders of a value are named locals, so that the hits print with their names. -/
def auditEnv (pre : Name) : MetaM (Nat × Array MessageData) := do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun acc n info =>
    if isCostedName n && pre.isPrefixOf n && info matches .defnInfo _ then acc.push n else acc
  let names := names.qsort fun a b => a.toString < b.toString
  let mut out := #[]
  for n in names do
    let some (.defnInfo dv) := env.find? n | continue
    let line? ← lambdaTelescope dv.value fun _ b => do
      let hs ← classicalHits b
      if hs.isEmpty then return none
      some <$> addMessageContext
        (m!"{n}: " ++ MessageData.joinSep (hs.toList.map Hit.msg) "; ")
    if let some l := line? then out := out.push l
  return (names.size, out)

/-- `#classical_cost_audit` reports the classical decisions and the choices in data of the
costed forms and costs of the environment; `#classical_cost_audit N` those under `N`. -/
syntax (name := classicalCostAuditCmd) "#classical_cost_audit" (ppSpace ident)? : command

/-- The elaborator of `#classical_cost_audit`. -/
@[command_elab classicalCostAuditCmd]
def elabClassicalCostAudit : CommandElab := fun stx => do
  let pre := match stx[1].getOptional? with
    | some i => i.getId
    | none => Name.anonymous
  let (n, lines) ← liftTermElabM <| auditEnv pre
  logInfo <| m!"classical_cost_audit: {lines.size} of {n} costed forms and costs" ++
    MessageData.joinSep (lines.toList.map (m!"\n" ++ ·)) ""

end CatCrypt.Tactics.ClassicalCostAudit

end

end
