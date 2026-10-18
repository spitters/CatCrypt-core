/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean
public import CatCryptCore.Tactics.AutoHopRegistry
public meta import CatCryptCore.Tactics.AutoHopRegistry
public import CatCryptCore.Tactics.AutoPremises
public meta import CatCryptCore.Tactics.AutoPremises

/-!
# The goal-shape dispatcher `catcrypt_auto` and its registry

`catcrypt_auto` closes the main goal by reading its shape and running, in order, the
arms registered for that shape. The module imports only `Lean` and the two Lean-only
modules `CatCryptCore.Tactics.AutoHopRegistry` and `CatCryptCore.Tactics.AutoPremises`:
shapes match head constants by `Name`, arms are tactic texts parsed at the call site, and
neither needs the module that declares the constants or tactics it names. A module
imports this one to register shapes and arms for the theory it imports.

## Registry

* `catcrypt_auto_shape "name" [direct] priority p := m` registers a shape: a matcher `m`
  on the goal type (see `Matcher`), read in the stage `direct` (the goal as stated) or,
  by default, in the normalised stage.
* `catcrypt_auto_arm "shape" order k [le_only] [skip_forall_ineq] [budget_div n]
  [needs [c₁, …]] := "tactic"` registers an arm of the shape `shape`. Arms of a shape run
  in increasing `order`. The shape `"*"` holds the arms run once for each term argument
  (`%TERM`), before the arms of the shape of the normalised stage; the shape `"premises"`
  holds the arms of the premise stage; the shape `"other"` is the shape of a goal of the
  normalised stage that no registered shape matches.
* `catcrypt_auto_norm [needs [c₁, …]] when m := "tactic"` registers a normalisation step,
  run before the shape of the normalised stage is read on a goal that `m` matches; the
  step is kept when it changes the goal.

Registrations from imported modules are merged. An arm whose `needs` constant is not in
the environment, or whose text does not parse there, is skipped, and the error names it
with the reason. An arm text contains these placeholders, replaced by the arguments of
`catcrypt_auto [t₁, …]` sorted by `classifyArgs`: `%GRIND` (` [g₁, …]` or nothing),
`%GRIND_TAIL` (`, g₁, …` or nothing), `%AESOP_ADD` (` (add unsafe a₁, …)` or nothing),
`%HOP` and `%DEFS` (` [x₁, …]` or nothing), `%SIMP_ALL` (the `simp_all` arm, after `clear`
of the `set` equations), `%TERM` (the term of a `"*"` arm) and `%PREMISES` (` [p₁, …]`,
the premises of the premise stage; an arm with it is left out when there are none).

## Procedure

1. Direct stage: the shape of highest priority among the `direct` shapes that match the
   instantiated goal runs its arms.
2. Normalisation: the registered normalisation steps that change the goal, then, while
   the goal has shape `other` and its head is a definition that `isUnfoldable` accepts,
   the unfolding of that definition (at most four times), each followed by the
   normalisation steps.
3. The shape of the normalised stage is read from the goal with its `set`/`let` variables
   replaced by their values and, failing a match, from its `whnfR`; the `"*"` arms of
   each non-proof term argument run, then the arms of the shape.
4. Unfolding pass: when every arm fails, the definitions that `unfoldHeads` finds in the
   goal and the definition arguments that occur in it are unfolded, the normalisation
   steps are applied, and the arms of the new shape run.
5. Premise stage: the goal of step 3 is restored and the arms of `"premises"` run with
   the premises that `AutoPremises.premises` ranks for it from the theorems of the current
   file and the fields of local hypotheses.

Each arm runs under its own heartbeat budget, counted from its start:
`catcrypt_auto.maxHeartbeats` heartbeats (default 20000, in the unit of `maxHeartbeats`),
divided by the arm's `budget_div`, with error recovery off. Each arm also runs under a
wall-clock budget of `catcrypt_auto.maxMillis` milliseconds (default 5000), cut to the
time left of the total budget `catcrypt_auto.totalMillis` (default 30000) of the whole
dispatch. An arm that fails, leaves a goal open, logs an error, assigns the goal a term
containing `sorry`, or exceeds either budget (a runtime exception or an interrupt,
caught) is undone with its messages, and the next arm runs. The steps between arms (the
shape matchers, the normalisation and unfolding steps, the premise ranking) run under
the heartbeat budget of one arm and the time left of the total budget; a step that
exceeds them is undone and treated as having found nothing. Once the total budget is
spent no further arm runs. When every arm fails, the error names the shape and each arm
with the first line of its error, formatted without the goals and traces that the arm's
error carries (`elideMessage`).

The wall-clock budgets use the cancellation token of `Core.Context`: a watcher task sets
a token of the dispatcher at the deadline or when the enclosing token is set, and
`Core.checkInterrupted` (called by `checkSystem`, `whnf`, `isDefEq`, `inferType` and the
kernel) stops the computation. An interrupt from the enclosing token is passed on.

`catcrypt_auto?` behaves as `catcrypt_auto` and adds a "Try this" suggestion with the
closing arm and its arguments, preceded by the normalisation and `unfold` steps that
changed the goal.

`#import_closure_roots M` prints the root packages of the transitive imports of the
module `M` and the imported modules outside `Init`, `Std` and `Lean`.
-/

public section

namespace CatCrypt.Tactics.AutoDispatch

open Lean Elab Tactic Meta

meta section

register_option catcrypt_auto.maxHeartbeats : Nat := {
  defValue := 20000
  descr := "heartbeat budget of each arm of `catcrypt_auto`, in the unit of `maxHeartbeats`"
}

register_option catcrypt_auto.maxMillis : Nat := {
  defValue := 5000
  descr := "wall-clock budget of each arm of `catcrypt_auto`, in milliseconds (0: none)"
}

register_option catcrypt_auto.totalMillis : Nat := {
  defValue := 30000
  descr := "wall-clock budget of a whole run of `catcrypt_auto`, in milliseconds (0: none)"
}

/-! ## Wall-clock budgets -/

/-- `x`, with every exception of `x`, including an interrupt, passed to `h`. -/
def catchAllCore {α : Type} (x : CoreM α) (h : Exception → CoreM α) : CoreM α :=
  fun ctx s => (x ctx s).tryCatch (fun e => h e ctx s)

/-- `catchAllCore` lifted to `TacticM`. -/
def catchAll {α : Type} (x : TacticM α) (h : Exception → TacticM α) : TacticM α :=
  controlAt CoreM fun run => catchAllCore (run x) (fun e => run (h e))

/-- The tag of the error of `withMillis` at the deadline. -/
def timeoutTag : Name := `catcrypt_auto.timeout

/-- `ex` is the error of `withMillis` at the deadline. -/
def isTimeout (ex : Exception) : Bool :=
  match ex with
  | .error _ (.tagged n _) => n == timeoutTag
  | _ => false

/-- The watcher of `withMillis`: sets `tk` at the time `deadline` (of `IO.monoMsNow`) or
when `outer?` is set, polling every 5 ms, and returns without setting it once `stop` is
set. -/
partial def watchDeadline (tk stop : IO.CancelToken) (outer? : Option IO.CancelToken)
    (deadline : Nat) : IO Unit := do
  if ← stop.isSet then return
  let outerSet ← match outer? with
    | some o => o.isSet
    | none => pure false
  if outerSet || (← IO.monoMsNow) ≥ deadline then
    tk.set
    return
  IO.sleep 5
  watchDeadline tk stop outer? deadline

/-- Run `x` under a wall-clock budget of `ms` milliseconds, or without one when `ms` is
`0`: `x` runs with a fresh cancellation token that `watchDeadline` sets after `ms`
milliseconds or when the enclosing token is set. An interrupt of `x` by the deadline
becomes the error "exceeded the time budget of `ms` ms" (tagged `timeoutTag`); an
interrupt by the enclosing token is rethrown. -/
def withMillis {α : Type} (ms : Nat) (x : TacticM α) : TacticM α := do
  if ms == 0 then return ← x
  let outer? := (← readThe Core.Context).cancelTk?
  let tk ← IO.CancelToken.new
  let stop ← IO.CancelToken.new
  let deadline := (← IO.monoMsNow) + ms
  let _ ← IO.asTask (prio := .dedicated) (watchDeadline tk stop outer? deadline)
  catchAll
    (do
      let a ← withTheReader Core.Context (fun c => { c with cancelTk? := some tk }) x
      stop.set
      pure a)
    fun ex => do
      stop.set
      if ex.isInterrupt then
        if let some o := outer? then
          if ← o.isSet then throw ex
        throw <| .error (← getRef) <| .tagged timeoutTag m!"exceeded the time budget of {ms} ms"
      throw ex

/-- The budgets of a run of `catcrypt_auto`. A budget of `0` milliseconds is no
wall-clock budget. -/
structure Budget where
  /-- Heartbeats of each arm, in the unit of `maxHeartbeats`. -/
  hb : Nat
  /-- Milliseconds of each arm. -/
  ms : Nat
  /-- Milliseconds of the whole run. -/
  totalMs : Nat
  /-- The end of the run, in the time of `IO.monoMsNow`. -/
  deadline : Nat

/-- The total budget of `b` is spent. -/
def Budget.spent (b : Budget) : IO Bool := do
  return b.totalMs != 0 && (← IO.monoMsNow) ≥ b.deadline

/-- The wall-clock budget of a step: the milliseconds left of the total budget, cut to
the budget of an arm when `arm` is set; `0` when neither budget is set. -/
def Budget.slice (b : Budget) (arm : Bool) : IO Nat := do
  let now ← IO.monoMsNow
  let left := if b.totalMs == 0 then 0 else max 1 (b.deadline - now)
  let own := if arm then b.ms else 0
  return if own == 0 then left else if left == 0 then own else min own left

/-- The budgets of the options `catcrypt_auto.maxMillis` and `catcrypt_auto.totalMillis`
with `hb` heartbeats per arm, the total budget starting now. -/
def Budget.ofOptions (hb : Nat) : CoreM Budget := do
  let opts ← getOptions
  let totalMs := catcrypt_auto.totalMillis.get opts
  return { hb, ms := catcrypt_auto.maxMillis.get opts, totalMs,
           deadline := (← IO.monoMsNow) + totalMs }

/-! ## The registry -/

/-- A predicate on a goal type, built from head constants given by `Name`. -/
inductive Matcher where
  /-- The term is an application of the constant. -/
  | app (n : Name)
  /-- The term is an application of the constant to exactly `k` arguments. -/
  | appArity (n : Name) (k : Nat)
  /-- The term is an application of `n` to `k` arguments whose argument `i` (after
  `whnfR` when `whnf` is set) satisfies `m`. -/
  | arg (n : Name) (k i : Nat) (whnf : Bool) (m : Matcher)
  /-- The term mentions one of the constants. -/
  | mentions (ns : List Name)
  /-- The term is a `∀` whose body satisfies `m`. -/
  | underForall (m : Matcher)
  /-- One of the matchers holds. -/
  | any (ms : List Matcher)
  /-- All of the matchers hold. -/
  | all (ms : List Matcher)
  /-- The term is `rel _ _ a b` with `a` and `b` applications of the same function to the
  same number of arguments. -/
  | sameHeadSides (rel : Name)
  /-- The term is `a ≤ b` over a type whose `whnfR` is one of `types`, where `a` is a
  distance registered with `@[hop_metric]` (read directly or after `whnfR`) or a sum with
  one as summand, or `a` or `b` mentions one of `consts` or a `@[hop_metric]` head. -/
  | distance (types consts : List Name)
  deriving Inhabited

/-- The stage in which a shape is read. -/
inductive Stage where
  /-- The goal as stated. -/
  | direct
  /-- The goal after the normalisation steps and head unfolding. -/
  | normalised
  deriving Inhabited, BEq

/-- A registered shape. -/
structure ShapeSpec where
  /-- The name, as printed in errors and referred to by arms. -/
  name : String
  /-- The stage. -/
  stage : Stage
  /-- Among matching shapes of a stage, the one of highest priority is chosen. -/
  priority : Nat
  /-- The matcher. -/
  matcher : Matcher
  deriving Inhabited

/-- A registered arm. -/
structure ArmSpec where
  /-- The shape the arm belongs to. -/
  shape : String
  /-- Arms of a shape run in increasing order. -/
  order : Nat
  /-- The tactic text with placeholders. -/
  text : String
  /-- Constants that must be in the environment; otherwise the arm is skipped. -/
  needs : List Name := []
  /-- The arm runs only on goals whose `whnfR` is `_ ≤ _`. -/
  leOnly : Bool := false
  /-- The arm is skipped when a local hypothesis is a `∀`-quantified inequality. -/
  skipForallIneq : Bool := false
  /-- The arm's budget is the budget of `catcrypt_auto` divided by this number. -/
  budgetDiv : Nat := 1
  deriving Inhabited

/-- A registered normalisation step. -/
structure NormSpec where
  /-- The goals the step applies to. -/
  trigger : Matcher
  /-- The tactic text. -/
  text : String
  /-- Constants that must be in the environment; otherwise the step is skipped. -/
  needs : List Name := []
  deriving Inhabited

/-- An entry of the registry. -/
inductive Entry where
  | shape (s : ShapeSpec)
  | arm (a : ArmSpec)
  | norm (n : NormSpec)
  deriving Inhabited

/-- The registry: shapes, arms and normalisation steps, in registration order. -/
structure Registry where
  shapes : Array ShapeSpec := #[]
  arms : Array ArmSpec := #[]
  norms : Array NormSpec := #[]
  deriving Inhabited

/-- Add an entry to the registry. -/
def Registry.add (r : Registry) : Entry → Registry
  | .shape s => { r with shapes := r.shapes.push s }
  | .arm a => { r with arms := r.arms.push a }
  | .norm n => { r with norms := r.norms.push n }

/-- The registry of `catcrypt_auto`. -/
initialize autoRegistryExt : SimpleScopedEnvExtension Entry Registry ←
  registerSimpleScopedEnvExtension { addEntry := Registry.add, initial := {} }

/-- The registry in the current environment. -/
def registry : CoreM Registry :=
  return autoRegistryExt.getState (← getEnv)

/-! ## Matchers -/

/-- `e` mentions one of the constants `cs`. -/
def mentionsConst (cs : List Name) (e : Expr) : Bool :=
  (e.find? fun s => match s.constName? with
    | some n => cs.contains n
    | none => false).isSome

/-- The head constants of the `@[hop_metric]` registrations. -/
def registeredHeads : MetaM (List Name) := do
  return (← AutoArms.hopEntries).toList.map (·.head)

/-- `e` is a registered distance, read directly or after `whnfR`. -/
def isDistance (e : Expr) : MetaM Bool := do
  if (← AutoArms.distView? e).isSome then return true
  return (← AutoArms.distView? (← whnfR e)).isSome

/-- `e` is a registered distance or a sum with a registered distance as a summand. -/
partial def hasDistanceSummand (e : Expr) : MetaM Bool := do
  let e := e.cleanupAnnotations
  if let some (a, b) := AutoArms.addSides? e then
    return (← hasDistanceSummand a) || (← hasDistanceSummand b)
  isDistance e

/-- `a` and `b` are applications of the same function to the same number of
arguments. -/
def sameHead (a b : Expr) : Bool :=
  a.getAppNumArgs > 0 && a.getAppNumArgs == b.getAppNumArgs && a.getAppFn == b.getAppFn

/-- Evaluate a matcher on `t`. -/
partial def Matcher.eval : Matcher → Expr → MetaM Bool
  | .app n, t => pure (t.isAppOf n)
  | .appArity n k, t => pure (t.isAppOfArity n k)
  | .arg n k i w m, t => do
    unless t.isAppOfArity n k do return false
    let a := t.getArg! i
    let a ← if w then whnfR a else pure a
    m.eval a
  | .mentions ns, t => pure (mentionsConst ns t)
  | .underForall m, t => if t.isForall then m.eval t.bindingBody! else pure false
  | .any ms, t => ms.anyM (·.eval t)
  | .all ms, t => ms.allM (·.eval t)
  | .sameHeadSides rel, t =>
    pure (t.isAppOfArity rel 4 && sameHead (t.getArg! 2) (t.getArg! 3))
  | .distance tys cs, t => do
    unless t.isAppOfArity ``LE.le 4 do return false
    let α ← whnfR (t.getArg! 0)
    unless tys.any α.isConstOf do return false
    let a := t.getArg! 2
    let b := t.getArg! 3
    let cs := cs ++ (← registeredHeads)
    if mentionsConst cs a || mentionsConst cs b then return true
    hasDistanceSummand a

/-- The head constants of `.app` and `.appArity` matchers, through `any` and `all`. -/
partial def Matcher.heads : Matcher → List Name
  | .app n | .appArity n _ => [n]
  | .any ms | .all ms => ms.flatMap Matcher.heads
  | _ => []

/-- The constants of `.distance` matchers, through `any` and `all`. -/
partial def Matcher.distanceConsts : Matcher → List Name
  | .distance _ cs => cs
  | .any ms | .all ms => ms.flatMap Matcher.distanceConsts
  | _ => []

/-- The shapes of a stage, by decreasing priority, registration order among equals. -/
def shapesOf (st : Stage) : MetaM (Array ShapeSpec) := do
  let ss := (← registry).shapes.filter (·.stage == st)
  return ss.insertionSort fun a b => a.priority > b.priority

/-- The first shape of the stage `st` whose matcher holds on `t`. -/
def firstShape (st : Stage) (t : Expr) : MetaM (Option ShapeSpec) := do
  for s in ← shapesOf st do
    if ← s.matcher.eval t then return some s
  return none

/-- The name of the shape of the goal type `t` in the normalised stage: the first
matching shape of `t` with its `let` variables replaced by their values, else of its
`whnfR`, else `"other"`. -/
def shape (t : Expr) : MetaM String := do
  let t ← zetaReduce (← instantiateMVars t)
  if let some s ← firstShape .normalised t.cleanupAnnotations then return s.name
  if let some s ← firstShape .normalised (← whnfR t).cleanupAnnotations then return s.name
  return "other"

/-- The constants of the matchers of the normalised stage that stay folded: the heads
of `.app` matchers and the constants of `.distance` matchers. -/
def shapeConsts : MetaM (List Name × List Name) := do
  let ss ← shapesOf .normalised
  return (ss.toList.flatMap (·.matcher.heads), ss.toList.flatMap (·.matcher.distanceConsts))

/-! ## Arguments -/

/-- The terms of the optional argument list `[t₁, …, tₙ]` at position `1` of
the syntax of `catcrypt_auto` or `catcrypt_auto?`. -/
def argsOf (stx : Syntax) : Array Term :=
  if stx[1].getNumArgs == 3 then stx[1][1].getSepArgs.map (⟨·⟩) else #[]

/-- The source text of the term `t`, pretty-printed. -/
def termText (t : Term) : TacticM String := do
  return (← PrettyPrinter.ppTerm t).pretty

/-- Parse `s` as a tactic. -/
def parseTactic (s : String) : TacticM (TSyntax `tactic) := do
  match Parser.runParserCategory (← getEnv) `tactic s with
  | .ok stx => return ⟨stx⟩
  | .error e => throwError "catcrypt_auto: cannot parse the arm `{s}`: {e}"

/-- The arguments of `catcrypt_auto [t₁, …, tₙ]`, as source texts, sorted by the
arms that receive them. -/
structure ArgClasses where
  /-- The lemma arguments of `grind` and `catcrypt_grind`. -/
  grind : Array String := #[]
  /-- The lemma arguments of `simp_all`. -/
  simp : Array String := #[]
  /-- The rules added to `aesop` as `(add unsafe ·)`. -/
  aesop : Array String := #[]
  /-- The hop facts of `hop_chain`. -/
  hop : Array String := #[]
  /-- The definitions, unfolded by `gcongr_unfold` and by the unfolding pass. -/
  defs : Array Name := #[]
  /-- The source texts of `defs`. -/
  defTexts : Array String := #[]
  /-- The terms elaborated against the goal by the `"*"` arms. -/
  terms : Array String := #[]
  /-- The premises of the premise stage. -/
  premises : Array String := #[]

/-- `stx` contains a hole `_` or a synthetic hole `?x`. -/
partial def hasHole (stx : Syntax) : Bool :=
  stx.isOfKind ``Lean.Parser.Term.hole || stx.isOfKind ``Lean.Parser.Term.syntheticHole ||
    stx.getArgs.any hasHole

/-- The global definition named by the identifier `t`, if `t` is one and the
definition is not a proof. -/
def defOfIdent? (t : Term) : TacticM (Option Name) := do
  unless t.raw.isIdent do return none
  let some n ← (try some <$> realizeGlobalConstNoOverload t.raw catch _ => pure none)
    | return none
  let some (.defnInfo d) := (← getEnv).find? n | return none
  if ← isProp d.type then return none
  return some n

/-- Sort the arguments `ts` by the arms that receive them, in the context of the
goal `g`. Each argument is elaborated as one term (an application `h a` is one
argument).

* A local hypothesis goes to `simp_all` and `aesop`, and not to `grind` or
  `catcrypt_grind`: `grind` uses the local context and rejects a local hypothesis
  as a redundant parameter.
* A definition goes to `grind`, `catcrypt_grind` and `simp_all`, which unfold it,
  to `gcongr_unfold`, and to the unfolding pass; it is not an `aesop` rule.
* A term with a hole `_` or `?x`, a term whose type is not a proposition, and a
  term that does not elaborate without an expected type go to the `"*"` arms only,
  which elaborate them against the goal. Instance problems that stay stuck without
  an expected type (the type class arguments of a lemma such as `ucCdist_self`) do
  not make the elaboration fail.
* Any other term is a proof: it goes to `grind`, `catcrypt_grind`, `simp_all`, to
  `aesop` (in parentheses unless it is an identifier), and to `hop_chain` when its
  type is not `∀`-quantified. -/
def classifyArgs (g : MVarId) (ts : Array Term) : TacticM ArgClasses :=
  g.withContext do
    let mut c : ArgClasses := {}
    for t in ts do
      let txt ← termText t
      if t.raw.isIdent && ((← getLCtx).findFromUserName? t.raw.getId).isSome then
        c := { c with simp := c.simp.push txt, aesop := c.aesop.push txt }
        continue
      if let some n ← defOfIdent? t then
        c := { c with grind := c.grind.push txt, simp := c.simp.push txt,
                      defs := c.defs.push n, defTexts := c.defTexts.push txt }
        continue
      if hasHole t.raw then
        c := { c with terms := c.terms.push txt }
        continue
      -- `0`: a term for the `"*"` arms; `1`: an unquantified proof; `2`: a quantified one
      let kind ← withoutModifyingState do
        try
          let e ← Term.withoutErrToSorry <|
            Term.withSynthesize (postpone := .partial) <| Term.elabTerm t none
          let ty ← instantiateMVars (← inferType e)
          if !(← isProp ty) then pure 0
          else if (← whnfR ty).isForall then pure 2 else pure 1
        catch _ => pure 0
      if kind == 0 then
        c := { c with terms := c.terms.push txt }
      else
        let a := if t.raw.isIdent then txt else s!"({txt})"
        c := { c with grind := c.grind.push txt, simp := c.simp.push txt,
                      aesop := c.aesop.push a,
                      hop := if kind == 1 then c.hop.push txt else c.hop }
    return c

/-- ` [x₁, …, xₙ]`, or the empty string when `xs` is empty. -/
def listText (xs : Array String) : String :=
  if xs.isEmpty then "" else s!" [{", ".intercalate xs.toList}]"

/-! ## `set` equations -/

/-- The names of the local hypotheses `h : x = e` or `h : e = x` of the goal `g`
where `x` is a local definition with value `e`: the equations that
`set x := e with h` introduces. Hypotheses with inaccessible names are left out. -/
def setEqHyps (g : MVarId) : MetaM (Array Name) := g.withContext do
  let isSetEq (x v : Expr) : MetaM Bool := do
    let .fvar fv := x | return false
    let some val ← fv.getValue? | return false
    withReducible (isDefEq val v)
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail || d.userName.hasMacroScopes then continue
    let some (_, a, b) := (← instantiateMVars d.type).eq? | continue
    if (← isSetEq a b) || (← isSetEq b a) then out := out.push d.userName
  return out

/-- The `simp_all` arm with the lemma arguments `xs`, run after `clear` of the
`set` equations `hs`. Rule: `simp_all` runs without the equations of `set`. Such an
equation `x = e` rewrites the local definition `x` back into `e`; beside a
hypothesis that states a subterm of `e` in terms of `x` the two rewrite into each
other until the maximum recursion depth. The local definition `x` keeps its value
after the `clear`. -/
def simpAllText (hs : Array Name) (xs : Array String) : String :=
  let xs := xs.filter fun x => !hs.any (·.toString == x)
  let tac := s!"simp_all{listText xs}"
  if hs.isEmpty then tac
  else s!"(clear {" ".intercalate (hs.toList.map (·.toString))}; {tac})"

/-! ## Unfolding -/

/-- The roots of the modules whose definitions the unfolding pass leaves folded:
the Lean core and its libraries, Mathlib, Batteries, Aesop and Qq. Their
definitions are reasoned about through their own lemmas. -/
def foreignRoots : List Name :=
  [`Init, `Std, `Lean, `Lake, `Mathlib, `Batteries, `Aesop, `Qq]

/-- `e` with its first `k` leading `fun` binders removed. -/
def stripLams : Nat → Expr → Expr
  | k + 1, .lam _ _ b _ => stripLams k b
  | _, e => e

/-- `n` is a constant the unfolding traversal does not descend through: a constant
of a `.distance` matcher or a `@[hop_metric]` head. -/
def isStopConst (n : Name) : MetaM Bool := do
  let (_, dists) ← shapeConsts
  return dists.contains n || (← registeredHeads).contains n

/-- `n` is a definition the unfolding pass unfolds: a definition with a value,
of regular reducibility, not recursive, not an instance, a projection or a
matcher, not from a module of `foreignRoots`, not a head of a shape of the
normalised stage, a `@[hop_metric]` head or a constant of a `.distance` matcher, and
defined in terms of other operations of its result type: its value, after the
binders of its declared type, is not a `fun`. A definition whose value is a `fun`
beyond its declared binders, such as `SPComp.bind c f := fun h => …`, is an
operation on the representation of its type and stays folded. -/
def isUnfoldable (n : Name) : MetaM Bool := do
  let env ← getEnv
  let some (.defnInfo d) := env.find? n | return false
  if isInstanceCore env n || env.isProjectionFn n || isMatcherCore env n then return false
  if ← isRecursiveDefinition n then return false
  match ← getReducibilityStatus n with
  | .semireducible => pure ()
  | _ => return false
  if let some idx := env.getModuleIdxFor? n then
    if foreignRoots.contains (env.header.moduleNames[idx.toNat]!).getRoot then return false
  let (heads, _) ← shapeConsts
  if heads.contains n || (← isStopConst n) then return false
  let k ← forallTelescope d.type fun xs _ => pure xs.size
  return !(stripLams k d.value).isLambda

/-- The head constant of the goal `t`, read with its `let` variables replaced by
their values and, failing that, after `whnfR`, when `t` has shape `other` and
the head is a definition that `isUnfoldable` accepts. -/
def headToUnfold? (t : Expr) : MetaM (Option Name) := do
  unless (← shape t) == "other" do return none
  let t ← zetaReduce (← instantiateMVars t)
  for e in [t, ← whnfR t] do
    if let some n := e.cleanupAnnotations.getAppFn.constName? then
      if ← isUnfoldable n then return some n
  return none

/-- The definitions of the unfolding pass in `t`: the traversal
`AutoPremises.unfoldHeadsWith` from the root to depth 3 with `isUnfoldable` as the
accepted heads and `isStopConst` as the constants not descended through. -/
def unfoldHeads (t : Expr) : MetaM (Array Name) := do
  let hs ← AutoPremises.unfoldHeadsWith isUnfoldable isStopConst t 0 #[]
  return hs.map (·.1)

/-! ## Arms -/

/-- An arm: the tactic (absent when the text does not parse), its source text, its
heartbeat budget, and the reason it is skipped. -/
structure Arm where
  tac : Option (TSyntax `tactic)
  txt : String
  budget : Nat
  skip : Option String := none

/-- The name of a local hypothesis of the goal `g` that is a `∀`-quantified
inequality, if any. -/
def forallIneqHyp? (g : MVarId) : MetaM (Option Name) := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isForall then
      let concl ← forallTelescopeReducing ty fun _ b => pure b
      if concl.isAppOfArity ``LE.le 4 || concl.isAppOfArity ``LT.lt 4 then
        return some d.userName
  return none

/-- The registered arms of the shape `sh`, by increasing order, registration order
among equals. -/
def armSpecs (sh : String) : CoreM (Array ArmSpec) := do
  let as := (← registry).arms.filter (·.shape == sh)
  return as.insertionSort fun a b => a.order < b.order

/-- The text of the arm `a` with the placeholders replaced. -/
def expand (c : ArgClasses) (simpAll : String) (term : String) (s : String) : String :=
  let more := if c.grind.isEmpty then "" else s!", {", ".intercalate c.grind.toList}"
  let aesopAdd := if c.aesop.isEmpty then ""
    else s!" (add {", ".intercalate (c.aesop.toList.map (s!"unsafe {·}"))})"
  ((((((((s.replace "%GRIND_TAIL" more).replace "%GRIND" (listText c.grind)).replace
    "%AESOP_ADD" aesopAdd).replace "%HOP" (listText c.hop)).replace "%DEFS"
    (listText c.defTexts)).replace "%SIMP_ALL" simpAll).replace "%TERM" term).replace
    "%PREMISES" (listText c.premises))

/-- The arm of the specification `a` on the goal `g`, or `none` when it is left out
(`le_only` on a goal that is not `_ ≤ _`, `%PREMISES` without premises). -/
def mkArm (a : ArmSpec) (g : MVarId) (c : ArgClasses) (hb : Nat) (simpAll : String)
    (term : String := "") : TacticM (Option Arm) := do
  if a.leOnly then
    let isLe ← g.withContext do
      return (← whnfR (← instantiateMVars (← g.getType))).isAppOfArity ``LE.le 4
    unless isLe do return none
  if c.premises.isEmpty && (a.text.splitOn "%PREMISES").length > 1 then return none
  let txt := expand c simpAll term a.text
  let budget := max 1 (hb / max 1 a.budgetDiv)
  let env ← getEnv
  if let some n := a.needs.find? (!env.contains ·) then
    return some { tac := none, txt, budget, skip := some s!"skipped: `{n}` is not in the environment" }
  let tac? ← try some <$> parseTactic txt catch _ => pure none
  let some tac := tac?
    | return some { tac := none, txt, budget, skip := some "skipped: the tactic does not parse here" }
  let mut skip := none
  if a.skipForallIneq then
    if let some n ← forallIneqHyp? g then
      skip := some s!"skipped: the ∀-quantified inequality {n} is in context, \
        and unifying its conclusion with the goal unfolds the game definitions"
  return some { tac := some tac, txt, budget, skip }

/-- The arms of the shape `sh` on the goal `g`, in the order they are tried. When
`withTerms` is set, each term of `c.terms` contributes the arms of `"*"` first. -/
def arms (sh : String) (g : MVarId) (c : ArgClasses) (hb : Nat) (withTerms : Bool) :
    TacticM (Array Arm) := do
  let simpAll := simpAllText (← setEqHyps g) c.simp
  let mut out : Array Arm := #[]
  if withTerms then
    let stars ← armSpecs "*"
    for t in c.terms do
      for a in stars do
        if let some arm ← mkArm a g c hb simpAll t then out := out.push arm
  for a in ← armSpecs sh do
    if let some arm ← mkArm a g c hb simpAll then out := out.push arm
  return out

/-- `m` with each goal replaced by `⋯`, the children of each trace node dropped, each
widget replaced by its text, and the text and expression leaves after the first `n`
replaced by `⋯`. -/
partial def elideMessageAux : MessageData → StateM Nat MessageData
  | .ofGoal _ => return .ofFormat "⋯"
  | .trace d msg _ => return .trace d (← elideMessageAux msg) #[]
  | m@(.ofFormatWithInfos _) | m@(.ofLazy ..) => do
    let k ← get
    if k == 0 then return .ofFormat "⋯"
    set (k - 1)
    return m
  | .ofWidget _ alt => elideMessageAux alt
  | .withContext c d => return .withContext c (← elideMessageAux d)
  | .withNamingContext c d => return .withNamingContext c (← elideMessageAux d)
  | .nest n d => return .nest n (← elideMessageAux d)
  | .group d => return .group (← elideMessageAux d)
  | .compose a b => return .compose (← elideMessageAux a) (← elideMessageAux b)
  | .tagged n d => return .tagged n (← elideMessageAux d)
  | .ofOriginatingSyntax s d => return .ofOriginatingSyntax s (← elideMessageAux d)

/-- The error `m` of an arm as `elideMessageAux` leaves it with 40 leaves: the part that
the one-line report of the arm shows, without formatting the goals and traces that a
failing tactic attaches to its error. -/
def elideMessage (m : MessageData) : MessageData :=
  (elideMessageAux m).run' 40

/-- Run `x` under a budget of `hb` heartbeats (in the unit of `maxHeartbeats`)
counted from its start and of `ms` milliseconds (none when `ms` is `0`), with error
recovery off. The run is accepted only when `x` logs no error (a nested `by` block
reports its unsolved goals by logging an error and admitting them) and the goals it
starts on are assigned terms without `sorry`. A rejected run, a failure, an exceeded
budget or another runtime exception restores the state, including the message log,
and returns the error (by `elideMessage`) on one line, cut at 160 characters. -/
def budgeted (hb ms : Nat) (x : TacticM Unit) : TacticM (Except String Unit) := do
  let saved ← Tactic.saveState
  let goals ← getGoals
  let log ← Core.getMessageLog
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxHeartbeats := hb * 1000 }) do
      modifyThe Core.State fun s => { s with messages := {} }
      withCurrHeartbeats (withMillis ms (Term.withoutErrToSorry (withoutRecover x)))
      let new ← Core.getMessageLog
      if let some m := new.toList.find? (·.severity == .error) then
        throwError m!"logged the error: {m.data}"
      for g in goals do
        if (← instantiateMVars (mkMVar g)).hasSorry then
          throwError "the proof term contains sorry"
      modifyThe Core.State fun s => { s with messages := log ++ new }
      return .ok ())
    fun ex => do
      saved.restore
      let msg ← (elideMessage ex.toMessageData).toString
      let line := " ".intercalate ((msg.splitOn "\n").map (·.trimAscii.toString))
      return .error (line.take 160).toString

/-- Run `x`, a step between arms, under the heartbeat budget of one arm of `b` and the
time left of its total budget; return `dflt` with the state restored when the total
budget is spent, or when `x` exceeds a budget or throws another runtime exception. The
heartbeats of `x` are counted from its start, so the heartbeats of earlier arms do not
count against it. -/
def bounded {α : Type} (b : Budget) (dflt : α) (x : TacticM α) : TacticM α := do
  if ← b.spent then return dflt
  let ms ← b.slice false
  let saved ← Tactic.saveState
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxHeartbeats := b.hb * 1000 }) do
      withCurrHeartbeats (withMillis ms x))
    fun ex => do
      unless ex.isRuntime || isTimeout ex do throw ex
      saved.restore
      return dflt

/-- Run the tactic text `s` on the main goal under the budgets `b`; keep the
result and return `true` when it leaves exactly one goal of a different type,
restore the state and return `false` otherwise. -/
def stepChanges (s : String) (b : Budget) : TacticM Bool := do
  if ← b.spent then return false
  let before ← instantiateMVars (← (← getMainGoal).getType)
  let saved ← Tactic.saveState
  let some stx ← (try some <$> parseTactic s catch _ => pure none) | return false
  let .ok () ← budgeted b.hb (← b.slice true) (evalTactic stx) | return false
  match ← getGoals with
  | [g] =>
    if (← instantiateMVars (← g.getType)) == before then
      saved.restore
      return false
    return true
  | _ =>
    saved.restore
    return false

/-- Apply the registered normalisation steps whose trigger matches the main goal and
whose constants are in the environment, in registration order, keeping those that
change the goal; returns their texts. -/
def normalise (b : Budget) : TacticM (Array String) := do
  let mut done := #[]
  for n in (← registry).norms do
    let env ← getEnv
    unless n.needs.all env.contains do continue
    let t ← instantiateMVars (← (← getMainGoal).getType)
    unless ← bounded b false (n.trigger.eval t) do continue
    if ← stepChanges n.text b then done := done.push n.text
  return done

/-- Unfold the definitions `ds` in the main goal, one `unfold` step each, keeping
the steps that change the goal; returns their texts joined by `; `, or `none`
when no step changes the goal. -/
def unfoldStep (ds : Array Name) (b : Budget) : TacticM (Option String) := do
  let mut done : Array String := #[]
  for d in ds do
    if d.hasMacroScopes then continue
    let s := s!"unfold {privateToUserName d}"
    if ← stepChanges s b then done := done.push s
  if done.isEmpty then return none
  return some ("; ".intercalate done.toList)

/-- Run the arms of the shape `sh` on the main goal under the budgets `b`. Returns the
closing arm, or the failure (or reason for skipping) of each arm. Once the total budget
is spent the remaining arms are not run, and one line says so. -/
def runArms (sh : String) (c : ArgClasses) (b : Budget) (withTerms : Bool) :
    TacticM (Except (Array MessageData) Arm) := do
  let g ← getMainGoal
  let mut tried : Array MessageData := #[]
  for arm in ← bounded b #[] (arms sh g c b.hb withTerms) do
    let label : MessageData := match arm.tac with
      | some t => m!"{t}"
      | none => m!"{arm.txt}"
    if let some why := arm.skip then
      tried := tried.push m!"\n  {label}: {why}"
      continue
    let some tac := arm.tac | continue
    if ← b.spent then
      tried := tried.push m!"\n  {label} and the arms after it: not run, the total time \
        budget of {b.totalMs} ms is spent"
      break
    let s ← Tactic.saveState
    let r ← budgeted arm.budget (← b.slice true) do
      evalTactic tac
      unless (← getGoals).isEmpty do throwError "goals remain open"
    match r with
    | .ok () => return .ok arm
    | .error e =>
      s.restore
      tried := tried.push m!"\n  {label}: {e}"
  return .error tried

/-- One pass of the normalised stage on the main goal: read its shape and run the
`"*"` arms and the arms of that shape. Returns the closing arm, or the shape with the
failure of each arm. -/
def pass (c : ArgClasses) (b : Budget) : TacticM (Except (String × Array MessageData) Arm) := do
  let g ← getMainGoal
  let sh ← bounded b "other" (g.withContext do shape (← g.getType))
  match ← runArms sh c b true with
  | .ok arm => return .ok arm
  | .error tried => return .error (sh, tried)

/-- Step 2 of `runWith` on the main goal: the normalisation steps, then the unfolding
of a head definition of a goal of shape `other`, at most four times, each followed by
the normalisation steps. Returns the texts of the steps that changed the goal. -/
def prepare (b : Budget) : TacticM (Array String) := do
  let mut steps : Array String := ← normalise b
  for _ in [0:4] do
    let g ← getMainGoal
    let t ← g.getType
    let n? ← bounded b none (g.withContext (headToUnfold? t))
    let some n := n? | break
    let s? ← unfoldStep #[n] b
    let some s := s? | break
    steps := steps.push s
    steps := steps ++ (← normalise b)
  return steps

/-- Set the goals to `rest` and return the closing arm, preceded by the steps
`steps` when there are any. -/
def finishWith (rest : List MVarId) (steps : Array String) (arm : Arm) :
    TacticM (TSyntax `tactic) := do
  setGoals rest
  let some tac := arm.tac | throwError "catcrypt_auto: internal error"
  if steps.isEmpty then return tac
  parseTactic s!"({"; ".intercalate (steps.push arm.txt).toList})"

/-- The premises of the premise stage for the main goal: the candidates of
`AutoPremises.premises` from the theorems of the current file and the fields of local
hypotheses, at most `catcrypt_premises.max` of them. -/
def stagePremises : TacticM (Array String) := do
  let g ← getMainGoal
  let opts ← getOptions
  let self? ← Term.getDeclName?
  let ps ← withoutModifyingState <| AutoPremises.premises g self?
    (AutoPremises.catcrypt_premises.max.get opts)
    (AutoPremises.catcrypt_premises.fieldDepth.get opts)
  return (ps.filter fun p => p.source == .fileDecl || p.source == .hypField).map (·.display)

/-- Close the main goal by the procedure of the module docstring, with the arguments
`ts`, each step and arm under the budgets `b`. Returns the closing arm, preceded by the
normalisation and unfolding steps that changed the goal. -/
def runWith (b : Budget) (ts : Array Term) : TacticM (TSyntax `tactic) := do
  let goal ← getMainGoal
  let rest := (← getGoals).drop 1
  let start ← Tactic.saveState
  setGoals [goal]
  let c ← bounded b {} (classifyArgs goal ts)
  -- 1. the direct stage
  let mut pre : MessageData := m!""
  let t0 := (← instantiateMVars (← goal.getType)).cleanupAnnotations
  if let some s ← bounded b none (goal.withContext (firstShape .direct t0)) then
    match ← runArms s.name c b false with
    | .ok arm => return ← finishWith rest #[] arm
    | .error tried =>
      pre := m!"\non the goal as stated: goal shape {s.name}; every arm failed:\
        {MessageData.joinSep tried.toList ""}"
  -- 2. and 3. normalisation and the shape's arms
  let steps ← prepare b
  let prepared ← Tactic.saveState
  match ← pass c b with
  | .ok arm => finishWith rest steps arm
  | .error (sh, tried) =>
    -- 4. the unfolding pass
    let g ← getMainGoal
    let ds ← bounded b #[] <| g.withContext do
      let t ← instantiateMVars (← g.getType)
      let heads ← unfoldHeads t
      pure (heads ++ c.defs.filter fun d => mentionsConst [d] t && !heads.contains d)
    let mut second : MessageData := m!""
    if let some u ← unfoldStep ds b then
      let steps2 := (steps.push u) ++ (← normalise b)
      match ← pass c b with
      | .ok arm => return ← finishWith rest steps2 arm
      | .error (sh2, tried2) =>
        second := m!"\nafter `{u}`: goal shape {sh2}; every arm failed:\
          {MessageData.joinSep tried2.toList ""}"
    -- 5. the premise stage
    prepared.restore
    let ps ← bounded b #[] stagePremises
    let mut third : MessageData := m!""
    unless ps.isEmpty do
      match ← runArms "premises" { premises := ps } b false with
      | .ok arm => return ← finishWith rest steps arm
      | .error tried3 =>
        unless tried3.isEmpty do
          third := m!"\nwith the premises of the current file and the local hypotheses:\
            {MessageData.joinSep tried3.toList ""}"
    start.restore
    let spent : MessageData :=
      if ← b.spent then m!"\nthe total time budget of {b.totalMs} ms is spent" else m!""
    throwError m!"catcrypt_auto: goal shape {sh}; every arm failed \
      (budget {b.hb} heartbeats and {b.ms} ms each):\
      {MessageData.joinSep tried.toList ""}{second}{third}{pre}{spent}"

/-- `runWith` under the budgets of the options `catcrypt_auto.maxHeartbeats`,
`catcrypt_auto.maxMillis` and `catcrypt_auto.totalMillis`. -/
def run (ts : Array Term) : TacticM (TSyntax `tactic) := do
  runWith (← Budget.ofOptions (catcrypt_auto.maxHeartbeats.get (← getOptions))) ts

/-- `catcrypt_auto` closes the main goal by the arms registered for its shape (see
the module docstring), each under the heartbeat budget `catcrypt_auto.maxHeartbeats`
(in the unit of `maxHeartbeats`). `catcrypt_auto [t₁, …, tₙ]` passes the terms to the
arms by their kind (`classifyArgs`). -/
syntax (name := catcryptAuto) "catcrypt_auto" (" [" term,* "]")? : tactic

/-- `catcrypt_auto?` behaves as `catcrypt_auto` and suggests the closing arm. -/
syntax (name := catcryptAutoTrace) "catcrypt_auto?" (" [" term,* "]")? : tactic

@[tactic catcryptAuto] def evalCatcryptAuto : Tactic := fun stx => do
  discard (run (argsOf stx))

@[tactic catcryptAutoTrace] def evalCatcryptAutoTrace : Tactic := fun stx => do
  let arm ← run (argsOf stx)
  Lean.Meta.Tactic.TryThis.addSuggestion stx arm

/-! ## Registration commands -/

/-- The matchers of `catcrypt_auto_shape` and `catcrypt_auto_norm`. -/
declare_syntax_cat catcrypt_auto_matcher (behavior := both)

/-- `app c`: an application of the constant `c`. -/
syntax (name := mApp) &"app" ident : catcrypt_auto_matcher
/-- `app c/k`: an application of `c` to exactly `k` arguments. -/
syntax (name := mAppArity) &"app" ident "/" num : catcrypt_auto_matcher
/-- `arg c/k at i [whnf] (m)`: argument `i` of an application of `c` to `k` arguments
satisfies `m`, after `whnfR` when `whnf` is given. -/
syntax (name := mArg) &"arg" ident "/" num " at " num (&"whnf")? " (" catcrypt_auto_matcher ")" :
  catcrypt_auto_matcher
/-- `mentions [c₁, …]`: the goal mentions one of the constants. -/
syntax (name := mMentions) &"mentions" "[" ident,* "]" : catcrypt_auto_matcher
/-- `under_forall (m)`: a `∀` whose body satisfies `m`. -/
syntax (name := mUnderForall) &"under_forall" "(" catcrypt_auto_matcher ")" :
  catcrypt_auto_matcher
/-- `any [m₁, …]`: one of the matchers holds. -/
syntax (name := mAny) &"any" "[" catcrypt_auto_matcher,* "]" : catcrypt_auto_matcher
/-- `all [m₁, …]`: all of the matchers hold. -/
syntax (name := mAll) &"all" "[" catcrypt_auto_matcher,* "]" : catcrypt_auto_matcher
/-- `same_head_sides r`: `r _ _ a b` with `a` and `b` of the same head. -/
syntax (name := mSameHead) &"same_head_sides" ident : catcrypt_auto_matcher
/-- `distance [T₁, …] mentioning [c₁, …]`: see `Matcher.distance`. -/
syntax (name := mDistance) &"distance" "[" ident,* "]" &"mentioning" "[" ident,* "]" :
  catcrypt_auto_matcher

/-- The names of a separated list of identifiers. -/
def idsOf (stx : Syntax) : List Name :=
  (stx.getSepArgs.map (·.getId)).toList

/-- The natural number of a numeral. -/
def natOf (stx : Syntax) : Nat :=
  stx.isNatLit?.getD 0

/-- Elaborate a matcher. -/
partial def elabMatcher (stx : Syntax) : Command.CommandElabM Matcher := do
  let k := stx.getKind
  if k == ``mApp then return .app stx[1].getId
  if k == ``mAppArity then return .appArity stx[1].getId (natOf stx[3])
  if k == ``mArg then
    return .arg stx[1].getId (natOf stx[3]) (natOf stx[5]) (!stx[6].isNone)
      (← elabMatcher stx[8])
  if k == ``mMentions then return .mentions (idsOf stx[2])
  if k == ``mUnderForall then return .underForall (← elabMatcher stx[2])
  if k == ``mAny then return .any (← stx[2].getSepArgs.toList.mapM elabMatcher)
  if k == ``mAll then return .all (← stx[2].getSepArgs.toList.mapM elabMatcher)
  if k == ``mSameHead then return .sameHeadSides stx[1].getId
  if k == ``mDistance then return .distance (idsOf stx[2]) (idsOf stx[6])
  throwErrorAt stx "catcrypt_auto: unknown matcher"

/-- `catcrypt_auto_shape "name" [direct] priority p := m` registers a shape of
`catcrypt_auto`: the goals that the matcher `m` accepts, read in the direct stage when
`direct` is given and in the normalised stage otherwise. -/
syntax (name := shapeCmd) "catcrypt_auto_shape " str (&"direct")? &"priority" num
  " := " catcrypt_auto_matcher : command

/-- `catcrypt_auto_arm "shape" order k [le_only] [skip_forall_ineq] [budget_div n]
[needs [c₁, …]] := "tactic"` registers an arm of `catcrypt_auto` for the shape `shape`
(see the module docstring for the placeholders of the tactic text). -/
syntax (name := armCmd) "catcrypt_auto_arm " str &"order" num (&"le_only")?
  (&"skip_forall_ineq")? (&"budget_div" num)? (&"needs" "[" ident,* "]")? " := " str :
  command

/-- `catcrypt_auto_norm [needs [c₁, …]] when m := "tactic"` registers a normalisation
step of `catcrypt_auto`, run on goals that `m` accepts and kept when it changes the goal. -/
syntax (name := normCmd) "catcrypt_auto_norm " (&"needs" "[" ident,* "]")? &"when"
  catcrypt_auto_matcher " := " str : command

@[command_elab shapeCmd] def elabShapeCmd : Command.CommandElab := fun stx => do
  let name := stx[1].isStrLit?.getD ""
  let stage : Stage := if stx[2].isNone then .normalised else .direct
  let m ← elabMatcher stx[6]
  autoRegistryExt.add (.shape { name, stage, priority := natOf stx[4], matcher := m })

@[command_elab armCmd] def elabArmCmd : Command.CommandElab := fun stx => do
  let shape := stx[1].isStrLit?.getD ""
  let budgetDiv := if stx[6].isNone then 1 else natOf stx[6][1]
  let needs := if stx[7].isNone then [] else idsOf stx[7][2]
  let text := stx[9].isStrLit?.getD ""
  let leOnly := !stx[4].isNone
  let skipForallIneq := !stx[5].isNone
  let spec : ArmSpec :=
    { shape, order := natOf stx[3], text, needs, leOnly, skipForallIneq, budgetDiv }
  autoRegistryExt.add (.arm spec)

@[command_elab normCmd] def elabNormCmd : Command.CommandElab := fun stx => do
  let needs := if stx[1].isNone then [] else idsOf stx[1][2]
  let m ← elabMatcher stx[3]
  autoRegistryExt.add (.norm { trigger := m, text := stx[5].isStrLit?.getD "", needs })

/-! ## Import closure -/

/-- `#import_closure_roots M` prints the root packages of the transitive imports of the
imported module `M` (including `M`) and the modules among them outside `Init`, `Std` and
`Lean`. -/
syntax (name := importClosureCmd) "#import_closure_roots " ident : command

@[command_elab importClosureCmd] def elabImportClosure : Command.CommandElab := fun stx => do
  let m := stx[1].getId
  let env ← getEnv
  let names := env.header.moduleNames
  let some i0 := names.idxOf? m | throwErrorAt stx[1] "module {m} is not imported"
  let mut seen : Std.HashSet Name := {}
  let mut todo : Array Name := #[names[i0]!]
  while h : todo.size > 0 do
    let n := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some i := names.idxOf? n | continue
    for imp in env.header.moduleData[i]!.imports do
      unless seen.contains imp.module do todo := todo.push imp.module
  let all := seen.toArray.qsort (·.toString < ·.toString)
  let roots := (all.map (·.getRoot)).toList.eraseDups
  let own := all.filter fun n => ![`Init, `Std, `Lean].contains n.getRoot
  logInfo m!"import closure of {m}: roots {roots}; \
    modules outside Init, Std and Lean: {own.toList}"

end

end CatCrypt.Tactics.AutoDispatch
