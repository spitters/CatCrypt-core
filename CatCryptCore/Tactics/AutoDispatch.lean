/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.Ring
public import CatCryptCore.Tactics.AutoSets
public import CatCryptCore.Tactics.BindVcgen
public import CatCryptCore.Tactics.Triangle
public import CatCryptCore.Tactics.AutoMetrics
public meta import CatCryptCore.Tactics.AutoArms

/-!
# Goal-shape dispatch over the automation sets

`catcrypt_auto` closes the main goal by reading its shape and running, in order,
the closers that apply to that shape. When the goal contains `>>=` it is first
rewritten by `simp only [SPComp.monad_bind_eq]`, so that `do` goals show their
head; the rewrite is kept only when it changes the goal. The shape is read from
the instantiated goal with its `set`/`let` variables replaced by their values
(`zetaReduce`) and, failing a match, from its `whnfR`.

| Shape | Detected head | Arms, in order |
|---|---|---|
| side condition | `SPComp.IsPure _`, `SPComp.NoFail _` | `aesop` over `CatCryptRel` |
| relational | `rHoare _ _ _ _` | `aesop` over `CatCryptRel`; `ssprove_crypto`; `ssprove_crypto_grind` |
| distance inequality | `_ ≤ _` over `ℝ≥0∞` or `ℝ` whose left side is a registered distance or a sum with one as summand, or that mentions a registered head, `prTrue` or `prEvent` | `hop_chain`; `sum_atoms_le`; `gcongr <;> catcrypt_grind`; `catcrypt_grind`; `bound` |
| monotonicity | `f a₁ … aₙ ≤ f b₁ … bₙ` or `<`, the same head on both sides; `Monotone f`, `Antitone f`, `StrictMono f`, `StrictAnti f` | `gcongr_unfold`; `gcongr`; `gcongr <;> catcrypt_grind`; `sum_atoms_le` (on `≤`); `simp_all`; `grind` |
| heap read | `Heap.get (Heap.set _ _ _) _ = _` (either side), or `=`, `≠`, `¬ _ = _` mentioning `Heap.set` | `grind [Heap.get_set_same, Heap.get_set_other]` |
| game equality | `_ = _` over `SPComp _` | `catcrypt_grind`; `bind_vcgen` |
| other | anything else | `sum_atoms_le` (on `≤`); `simp_all`; `grind` |

Each term argument that is not a proof (see below) adds the arms `exact t` and
`apply t`, tried before the arms of the table. Every `simp_all` arm runs after
`clear` of the equations `h : x = e` that `set x := e with h` introduces: such an
equation rewrites `x` back into `e`, and beside a hypothesis that states a
subterm of `e` in terms of `x` the two rewrite into each other until the maximum
recursion depth.

Unfolding. Before the shape is read, a goal of shape `other` whose head is a
definition is unfolded, at most four times. When every arm fails, the unfolding
pass unfolds, on each branch of the goal's explicit arguments down to depth 3,
the first head that is a definition, together with the definition arguments
that occur in the goal, and runs the arms of the new shape. The definitions
unfolded are those of `isUnfoldable`: non-recursive, of regular reducibility,
not an instance, projection or matcher, not from the Lean core, Mathlib,
Batteries, Aesop or Qq, not a shape head, registered head or probability
constant, and not an operation on the representation of its type (a value that
is a `fun` beyond the binders of its declared type, as `SPComp.bind`). The
suggestion records each `unfold` step.

A registered distance is a term that `distView?` of `CatCryptCore.Tactics.AutoArms`
reads as an application of a distance whose triangle lemma carries `@[hop_metric]`,
after unfolding the definitions and equations registered with `@[hop_metric]`; a
term that is not one is read again after `whnfR`. A registered head is the head
constant of a `@[hop_metric]` registration. The registrations of `sdist`,
`Advantage` and `AdvantageA` are in `CatCryptCore.Tactics.AutoMetrics`, which this
module imports; a definition of an advantage or a probability becomes a registered
distance by `@[hop_metric]` on it or on its defining equation.

The `hop_chain` arm receives the arguments that elaborate to a proof of an
unquantified proposition; the `sum_atoms_le` arm closes a sum of atoms against a
sum of atoms with the inequalities of the local context; the `gcongr_unfold` arm
receives the arguments that are identifiers as the definitions to unfold.

`bound` runs under a quarter of the arm budget, and not at all when a local
hypothesis is a `∀`-quantified inequality: `bound` then tries to unify that
hypothesis's conclusion with the goal, which unfolds the game definitions.

`catcrypt_auto [t₁, …, tₙ]` passes each term `tᵢ`, elaborated as one term, to
the arms by its kind (`classifyArgs`): a local hypothesis to `simp_all` and
`aesop` (not to `grind`, which uses the local context and rejects it as a
redundant parameter); a definition to `grind`, `catcrypt_grind`, `simp_all`,
`gcongr_unfold` and the unfolding pass (not to `aesop`); a term with a hole, a
term whose type is not a proposition, or a term that does not elaborate without
an expected type to the `exact` and `apply` arms only; any other proof to
`grind`, `catcrypt_grind` and `simp_all` as a lemma argument, to `aesop` as
`(add unsafe (tᵢ))`, and to `hop_chain` as a hop fact when it is not
`∀`-quantified.

Each arm runs under a heartbeat budget of its own, counted from the arm's start:
`catcrypt_auto.maxHeartbeats` heartbeats (default 20000, in the unit of
`maxHeartbeats`), with error recovery off, so that a combinator such as `<;>`
reports the first error of a branch. An arm that fails, leaves a goal open, logs
an error, assigns the goal a term containing `sorry`, or exceeds its budget (a
runtime exception, caught) is undone with its messages, and the next arm runs.
When every arm fails, the error names the shape and each arm with the first line
of its error.

`catcrypt_auto?` behaves as `catcrypt_auto` and adds a "Try this" suggestion with
the closing arm and its arguments, preceded by the `simp only` normalisation and
the `unfold` steps that changed the goal.
-/

public section

namespace CatCrypt.Tactics.AutoDispatch

open Lean Elab Tactic Meta

meta section

register_option catcrypt_auto.maxHeartbeats : Nat := {
  defValue := 20000
  descr := "heartbeat budget of each arm of `catcrypt_auto`, in the unit of `maxHeartbeats`"
}

/-- The goal shapes `catcrypt_auto` distinguishes. -/
inductive Shape where
  | sideCondition
  | relational
  | distanceBound
  | monotone
  | heapRead
  | gameEquality
  | other
  deriving Inhabited, BEq

/-- The name of a shape, as printed in the error and trace messages. -/
def Shape.name : Shape → String
  | .sideCondition => "IsPure/NoFail side condition"
  | .relational => "relational rHoare judgment"
  | .distanceBound => "distance inequality"
  | .monotone => "monotonicity inequality"
  | .heapRead => "heap read after write"
  | .gameEquality => "SPComp equality"
  | .other => "other"

/-- `e` mentions one of the constants `cs`. -/
def mentionsConst (cs : List Name) (e : Expr) : Bool :=
  (e.find? fun s => match s.constName? with
    | some n => cs.contains n
    | none => false).isSome

/-- The probability constants whose occurrence marks an inequality as a distance
inequality. -/
def probabilityConsts : List Name :=
  [`CatCrypt.Crypto.prTrue, `CatCrypt.Unary.prEvent]

/-- The head constants of the `@[hop_metric]` registrations. -/
def registeredHeads : MetaM (List Name) := do
  return (← AutoArms.hopEntries).toList.map (·.head)

/-- `e` is a registered distance, read directly or after `whnfR`. -/
def isDistance (e : Expr) : MetaM Bool := do
  if (← AutoArms.distView? e).isSome then return true
  return (← AutoArms.distView? (← whnfR e)).isSome

/-- `e` is a registered distance or a sum with a registered distance as a
summand. -/
partial def hasDistanceSummand (e : Expr) : MetaM Bool := do
  let e := e.cleanupAnnotations
  if let some (a, b) := AutoArms.addSides? e then
    return (← hasDistanceSummand a) || (← hasDistanceSummand b)
  isDistance e

/-- `a ≤ b` is a distance inequality: `a` is a registered distance or a sum with
one as summand, or `a` or `b` mentions a registered head or a probability
constant. -/
def isDistanceIneq (a b : Expr) : MetaM Bool := do
  let cs := probabilityConsts ++ (← registeredHeads)
  if mentionsConst cs a || mentionsConst cs b then return true
  hasDistanceSummand a

/-- The monotonicity predicates read as the monotonicity shape. -/
def monotonePreds : List Name :=
  [``Monotone, ``Antitone, ``StrictMono, ``StrictAnti]

/-- `e` is `Heap.get (Heap.set _ _ _) _`. -/
def isGetOfSet (e : Expr) : Bool :=
  e.isAppOfArity ``CatCrypt.Core.Heap.get 2 &&
    (e.getArg! 0).isAppOfArity ``CatCrypt.Core.Heap.set 3

/-- `a` and `b` are applications of the same function to the same number of
arguments. -/
def sameHead (a b : Expr) : Bool :=
  a.getAppNumArgs > 0 && a.getAppNumArgs == b.getAppNumArgs && a.getAppFn == b.getAppFn

/-- The shape of `t`, read from its head; `none` when no shape other than
`other` matches. -/
def shapeOf? (t : Expr) : MetaM (Option Shape) := do
  let t := t.cleanupAnnotations
  match_expr t with
  | CatCrypt.Core.SPComp.IsPure _ _ => return some .sideCondition
  | CatCrypt.Crypto.SPComp.NoFail _ _ => return some .sideCondition
  | CatCrypt.Relational.rHoare _ _ _ _ _ _ => return some .relational
  | LE.le α _ a b =>
    let α ← whnfR α
    if (α.isConstOf ``ENNReal || α.isConstOf ``Real) && (← isDistanceIneq a b) then
      return some .distanceBound
    if sameHead a b then return some .monotone
    return none
  | LT.lt _ _ a b =>
    if sameHead a b then return some .monotone
    return none
  | Eq α a b =>
    if isGetOfSet a || isGetOfSet b then return some .heapRead
    let α ← whnfR α
    if α.isAppOf ``CatCrypt.Core.SPComp then return some .gameEquality
    if mentionsConst [``CatCrypt.Core.Heap.set] t then return some .heapRead
    return none
  | Ne _ _ _ =>
    if mentionsConst [``CatCrypt.Core.Heap.set] t then return some .heapRead
    return none
  | Not p =>
    if p.isAppOfArity ``Eq 3 && mentionsConst [``CatCrypt.Core.Heap.set] p then
      return some .heapRead
    return none
  | _ =>
    if monotonePreds.any t.isAppOf then return some .monotone
    return none

/-- The shape of `t`: the head of `t` with its `let` variables replaced by their
values, else the head of its `whnfR`. -/
def shape (t : Expr) : MetaM Shape := do
  let t ← zetaReduce (← instantiateMVars t)
  if let some s ← shapeOf? t then return s
  if let some s ← shapeOf? (← whnfR t) then return s
  return .other

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

/-! ## Arguments -/

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
  /-- The terms elaborated against the goal by the `exact` and `apply` arms. -/
  terms : Array String := #[]

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
  term that does not elaborate without an expected type go to the `exact` and
  `apply` arms only, which elaborate them against the goal. Instance problems
  that stay stuck without an expected type (the type class arguments of a lemma
  such as `ucCdist_self`) do not make the elaboration fail.
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
      -- `0`: a term for `exact`/`apply`; `1`: an unquantified proof; `2`: a quantified one
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

/-- `tac` followed by the list `[t₁, …, tₙ]` of `xs`, or `tac` alone when `xs` is
empty. -/
def withList (tac : String) (xs : Array String) : String :=
  if xs.isEmpty then tac else s!"{tac} [{", ".intercalate xs.toList}]"

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
  let tac := withList "simp_all" xs
  if hs.isEmpty then tac
  else s!"(clear {" ".intercalate (hs.toList.map (·.toString))}; {tac})"

/-! ## Unfolding -/

/-- The roots of the modules whose definitions the unfolding pass leaves folded:
the Lean core and its libraries, Mathlib, Batteries, Aesop and Qq. Their
definitions are reasoned about through their own lemmas. -/
def foreignRoots : List Name :=
  [`Init, `Std, `Lean, `Lake, `Mathlib, `Batteries, `Aesop, `Qq]

/-- The heads that `shapeOf?` reads as a shape and that are definitions. -/
def shapeHeads : List Name :=
  [``CatCrypt.Core.SPComp.IsPure, ``CatCrypt.Crypto.SPComp.NoFail,
    ``CatCrypt.Relational.rHoare] ++ monotonePreds

/-- `e` with its first `k` leading `fun` binders removed. -/
def stripLams : Nat → Expr → Expr
  | k + 1, .lam _ _ b _ => stripLams k b
  | _, e => e

/-- `n` is a definition the unfolding pass unfolds: a definition with a value,
of regular reducibility, not recursive, not an instance, a projection or a
matcher, not from a module of `foreignRoots`, not a shape head, a registered
head or a probability constant, and defined in terms of other operations of its
result type: its value, after the binders of its declared type, is not a `fun`.
A definition whose value is a `fun` beyond its declared binders, such as
`SPComp.bind c f := fun h => …`, is an operation on the representation of its
type and stays folded. -/
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
  if shapeHeads.contains n || probabilityConsts.contains n || (← registeredHeads).contains n then
    return false
  let k ← forallTelescope d.type fun xs _ => pure xs.size
  return !(stripLams k d.value).isLambda

/-- The head constant of the goal `t`, read with its `let` variables replaced by
their values and, failing that, after `whnfR`, when `t` has shape `other` and
the head is a definition that `isUnfoldable` accepts. -/
def headToUnfold? (t : Expr) : MetaM (Option Name) := do
  unless (← shape t) == .other do return none
  let t ← zetaReduce (← instantiateMVars t)
  for e in [t, ← whnfR t] do
    if let some n := e.cleanupAnnotations.getAppFn.constName? then
      if ← isUnfoldable n then return some n
  return none

/-- The definitions of the unfolding pass in `t`: on each branch through the
explicit arguments, read from the root to depth 3, the first head constant that
`isUnfoldable` accepts. A branch stops at a registered head or a probability
constant. -/
partial def unfoldHeads (t : Expr) (d : Nat) (acc : Array Name) : MetaM (Array Name) := do
  if d > 3 then return acc
  let t := (← instantiateMVars t).cleanupAnnotations
  let some c := t.getAppFn.constName? | return acc
  if ← isUnfoldable c then
    return if acc.contains c then acc else acc.push c
  if probabilityConsts.contains c || (← registeredHeads).contains c then return acc
  let args := t.getAppArgs
  let fi ← getFunInfoNArgs t.getAppFn args.size
  let mut acc := acc
  for h : i in [:args.size] do
    let explicit := match fi.paramInfo[i]? with
      | some pi => pi.binderInfo.isExplicit
      | none => true
    if explicit then acc ← unfoldHeads args[i] (d + 1) acc
  return acc

/-! ## Arms -/

/-- An arm: the tactic, its source text, its heartbeat budget, and the reason it
is skipped. -/
structure Arm where
  tac : TSyntax `tactic
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

/-- The arms for a shape on the goal `g`, in the order they are tried, with the
arguments sorted by `classifyArgs` inserted. Each term of `c.terms` contributes
the arms `exact t` and `apply t` (with `assumption` or `catcrypt_grind` on the
premises), tried first. On a goal `_ ≤ _` the monotonicity and `other` shapes
include `sum_atoms_le`. Arms are built as text and parsed, so the suggested text
names the rule set and lemmas as written. -/
def arms (sh : Shape) (g : MVarId) (c : ArgClasses) (hb : Nat) : TacticM (Array Arm) := do
  let lst := if c.grind.isEmpty then "" else s!" [{", ".intercalate c.grind.toList}]"
  let more := if c.grind.isEmpty then "" else s!", {", ".intercalate c.grind.toList}"
  let aesopAdd := if c.aesop.isEmpty then ""
    else s!" (add {", ".intercalate (c.aesop.toList.map (s!"unsafe {·}"))})"
  let aesopTxt := s!"aesop (rule_sets := [CatCryptRel]) \
    (config := \{ terminal := true }){aesopAdd}"
  let simpAll := simpAllText (← setEqHyps g) c.simp
  let mk (s : String) : TacticM Arm := do
    return { tac := ← parseTactic s, txt := s, budget := hb }
  let isLe ← g.withContext do
    return (← whnfR (← instantiateMVars (← g.getType))).isAppOfArity ``LE.le 4
  let sumArm : Array Arm ← if isLe then pure #[← mk "sum_atoms_le"] else pure #[]
  let mut termArms : Array Arm := #[]
  for t in c.terms do
    termArms := termArms.push (← mk s!"exact {t}")
    termArms := termArms.push (← mk s!"(apply {t} <;> (first | assumption | catcrypt_grind))")
  let shaped ← match sh with
    | .sideCondition => pure #[← mk aesopTxt]
    | .relational => pure #[← mk aesopTxt, ← mk "ssprove_crypto", ← mk "ssprove_crypto_grind"]
    | .distanceBound => do
      let skip ← match ← forallIneqHyp? g with
        | some n => pure (some s!"skipped: the ∀-quantified inequality {n} is in context, \
            and unifying its conclusion with the goal unfolds the game definitions")
        | none => pure none
      pure #[← mk (withList "hop_chain" c.hop), ← mk "sum_atoms_le",
        ← mk s!"(gcongr <;> catcrypt_grind{lst})", ← mk s!"catcrypt_grind{lst}",
        { tac := ← parseTactic "bound", txt := "bound", budget := max 1 (hb / 4), skip }]
    | .monotone => pure (#[← mk (withList "gcongr_unfold" c.defTexts), ← mk "gcongr",
        ← mk s!"(gcongr <;> catcrypt_grind{lst})"] ++ sumArm ++
        #[← mk simpAll, ← mk s!"grind{lst}"])
    | .heapRead => pure #[← mk s!"grind [CatCrypt.Core.Heap.get_set_same, \
        CatCrypt.Core.Heap.get_set_other{more}]"]
    | .gameEquality => pure #[← mk s!"catcrypt_grind{lst}", ← mk "bind_vcgen"]
    | .other => pure (sumArm ++ #[← mk simpAll, ← mk s!"grind{lst}"])
  return termArms ++ shaped

/-- Run `x` under a budget of `hb` heartbeats (in the unit of `maxHeartbeats`)
counted from its start, with error recovery off. The run is accepted only when
`x` logs no error (a nested `by` block reports its unsolved goals by logging an
error and admitting them) and the goals it starts on are assigned terms without
`sorry`. A rejected run, a failure, an exceeded heartbeat budget or another
runtime exception restores the state, including the message log, and returns the
error on one line, cut at 160 characters. -/
def budgeted (hb : Nat) (x : TacticM Unit) : TacticM (Except String Unit) := do
  let saved ← Tactic.saveState
  let goals ← getGoals
  let log ← Core.getMessageLog
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxHeartbeats := hb * 1000 }) do
      modifyThe Core.State fun s => { s with messages := {} }
      withCurrHeartbeats (Term.withoutErrToSorry (withoutRecover x))
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
      let msg ← ex.toMessageData.toString
      let line := " ".intercalate ((msg.splitOn "\n").map (·.trimAscii.toString))
      return .error (line.take 160).toString

/-- `e` mentions `Bind.bind`. -/
def mentionsBind (e : Expr) : Bool := mentionsConst [``Bind.bind] e

/-- Run the tactic text `s` on the main goal under the budget `hb`; keep the
result and return `true` when it leaves exactly one goal of a different type,
restore the state and return `false` otherwise. -/
def stepChanges (s : String) (hb : Nat) : TacticM Bool := do
  let before ← instantiateMVars (← (← getMainGoal).getType)
  let saved ← Tactic.saveState
  let some stx ← (try some <$> parseTactic s catch _ => pure none) | return false
  let .ok () ← budgeted hb (evalTactic stx) | return false
  match ← getGoals with
  | [g] =>
    if (← instantiateMVars (← g.getType)) == before then
      saved.restore
      return false
    return true
  | _ =>
    saved.restore
    return false

/-- The normalisation of goals containing `>>=`. -/
def normText : String := "simp only [CatCrypt.Core.SPComp.monad_bind_eq]"

/-- Apply `normText` to the main goal when it mentions `>>=` and the rewrite
changes it; returns the step's text when applied. -/
def normalise (hb : Nat) : TacticM (Option String) := do
  unless mentionsBind (← instantiateMVars (← (← getMainGoal).getType)) do return none
  if ← stepChanges normText hb then return some normText
  return none

/-- Unfold the definitions `ds` in the main goal, one `unfold` step each, keeping
the steps that change the goal; returns their texts joined by `; `, or `none`
when no step changes the goal. -/
def unfoldStep (ds : Array Name) (hb : Nat) : TacticM (Option String) := do
  let mut done : Array String := #[]
  for d in ds do
    if d.hasMacroScopes then continue
    let s := s!"unfold {privateToUserName d}"
    if ← stepChanges s hb then done := done.push s
  if done.isEmpty then return none
  return some ("; ".intercalate done.toList)

/-- One pass of the dispatcher on the main goal: read its shape and run the arms
of that shape. Returns the closing arm, or the shape with the failure of each
arm. -/
def pass (c : ArgClasses) (hb : Nat) : TacticM (Except (Shape × Array MessageData) Arm) := do
  let g ← getMainGoal
  let sh ← g.withContext do shape (← g.getType)
  let mut tried : Array MessageData := #[]
  for arm in ← arms sh g c hb do
    if let some why := arm.skip then
      tried := tried.push m!"\n  {arm.tac}: {why}"
      continue
    let s ← Tactic.saveState
    let r ← budgeted arm.budget do
      evalTactic arm.tac
      unless (← getGoals).isEmpty do throwError "goals remain open"
    match r with
    | .ok () => return .ok arm
    | .error e =>
      s.restore
      tried := tried.push m!"\n  {arm.tac}: {e}"
  return .error (sh, tried)

/-- Steps 1 and 2 of `run` on the main goal: the `>>=` normalisation, then the
unfolding of a head definition of a goal of shape `other`, at most four times,
each followed by the normalisation. Returns the texts of the steps that changed
the goal. -/
def prepare (hb : Nat) : TacticM (Array String) := do
  let mut steps : Array String := #[]
  if let some s ← normalise hb then steps := steps.push s
  for _ in [0:4] do
    let g ← getMainGoal
    let t ← g.getType
    let n? ← g.withContext (headToUnfold? t)
    let some n := n? | break
    let s? ← unfoldStep #[n] hb
    let some s := s? | break
    steps := steps.push s
    if let some s ← normalise hb then steps := steps.push s
  return steps

/-- Set the goals to `rest` and return the closing arm, preceded by the steps
`steps` when there are any. -/
def finishWith (rest : List MVarId) (steps : Array String) (arm : Arm) :
    TacticM (TSyntax `tactic) := do
  setGoals rest
  if steps.isEmpty then return arm.tac
  parseTactic s!"({"; ".intercalate (steps.push arm.txt).toList})"

/-- Close the main goal by the arms of its shape, with the arguments `ts`, each
step and arm under a budget of `hb` heartbeats.

1. A goal containing `>>=` is rewritten by `normText` when that changes it.
2. Head unfolding: while the goal has shape `other` and its head is a definition
   that `isUnfoldable` accepts, that definition is unfolded (at most four times),
   followed by step 1.
3. The arms of the shape run (`pass`).
4. When every arm fails, the unfolding pass unfolds the definitions that
   `unfoldHeads` finds in the goal and the definitions among the arguments that
   occur in it, applies step 1, and runs the arms of the new shape.

Returns the closing arm, preceded by the normalisation and unfolding steps that
changed the goal. `pre` lists the arms already tried by `AutoDispatchExt` on the
shape `preShape`; the error reports them. -/
def runWith (hb : Nat) (ts : Array Term) (pre : Array MessageData := #[])
    (preShape : String := "") : TacticM (TSyntax `tactic) := do
  let goal ← getMainGoal
  let rest := (← getGoals).drop 1
  let start ← Tactic.saveState
  setGoals [goal]
  let c ← classifyArgs goal ts
  let steps ← prepare hb
  match ← pass c hb with
  | .ok arm => finishWith rest steps arm
  | .error (sh, tried) =>
    let g ← getMainGoal
    let ds ← g.withContext do
      let t ← instantiateMVars (← g.getType)
      let heads ← unfoldHeads t 0 #[]
      pure (heads ++ c.defs.filter fun d => mentionsConst [d] t && !heads.contains d)
    let mut second : MessageData := m!""
    if let some u ← unfoldStep ds hb then
      let mut steps2 := steps.push u
      if let some s ← normalise hb then steps2 := steps2.push s
      match ← pass c hb with
      | .ok arm => return ← finishWith rest steps2 arm
      | .error (sh2, tried2) =>
        second := m!"\nafter `{u}`: goal shape {sh2.name}; every arm failed:\
          {MessageData.joinSep tried2.toList ""}"
    start.restore
    let shapes := if pre.isEmpty then m!"goal shape {sh.name}"
      else m!"goal shape {preShape} (arms of AutoDispatchExt), then {sh.name}"
    throwError m!"catcrypt_auto: {shapes}; every arm failed \
      (budget {hb} heartbeats each):{MessageData.joinSep (pre ++ tried).toList ""}{second}"

/-- `runWith` under the budget `catcrypt_auto.maxHeartbeats`. -/
def run (ts : Array Term) (pre : Array MessageData := #[]) (preShape : String := "") :
    TacticM (TSyntax `tactic) := do
  runWith (catcrypt_auto.maxHeartbeats.get (← getOptions)) ts pre preShape

/-- `catcrypt_auto` closes the main goal by the closers registered for its
shape (see the module docstring), each under the heartbeat budget
`catcrypt_auto.maxHeartbeats` (in the unit of `maxHeartbeats`).
`catcrypt_auto [t₁, …, tₙ]` passes the terms to the `grind`, `simp_all`,
`catcrypt_grind` and `aesop` arms, to `hop_chain` and to `gcongr_unfold`. -/
syntax (name := catcryptAuto) "catcrypt_auto" (" [" term,* "]")? : tactic

/-- `catcrypt_auto?` behaves as `catcrypt_auto` and suggests the closing arm. -/
syntax (name := catcryptAutoTrace) "catcrypt_auto?" (" [" term,* "]")? : tactic

@[tactic catcryptAuto] def evalCatcryptAuto : Tactic := fun stx => do
  discard (run (argsOf stx))

@[tactic catcryptAutoTrace] def evalCatcryptAutoTrace : Tactic := fun stx => do
  let arm ← run (argsOf stx)
  Lean.Meta.Tactic.TryThis.addSuggestion stx arm

end

end CatCrypt.Tactics.AutoDispatch
