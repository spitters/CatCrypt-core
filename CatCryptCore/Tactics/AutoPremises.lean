/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean

/-!
# Premise retrieval from the current file and the local context

`premises g` returns a ranked list of candidate premises for the goal `g`, drawn from four
sources:

1. `fileDecl`: the theorems of the current module elaborated before the declaration that
   contains `g` (the constants of the staged environment map, filtered by
   `Lean.LibrarySuggestions.isDeniedPremise`, as in the core selector
   `Lean.LibrarySuggestions.currentFile`);
2. `hypField`: the `Prop`-valued fields of local hypotheses whose type is a structure,
   as projections (`h.hybrid_bound`, `h.1`), through nested structure fields up to depth
   `catcrypt_premises.fieldDepth`;
3. `hyp`: the `Prop`-valued local hypotheses, with their leading universal quantifiers
   instantiated by metavariables up to the first adversary binder;
4. `unfold`: the definitions at the head of the goal and of its sides, as unfolding
   candidates.

## Adversary binders

A binder is an adversary binder when its type mentions a constant whose last name
component contains one of `Adversary`, `Distinguisher`, `Forger`, `Attacker`, `Adv`,
`Prover`, `Oracle` or `SPComp`.
Instantiation stops at the first adversary binder. A candidate of sources 1 to 3 whose
statement, under an adversary binder `A`, concludes `x ≤ ε` or `x < ε` with `A` not
occurring in `ε` has the shape of an unbounded hardness assumption and is dropped.

## Score

Let `C(e)` be the constants of `e` other than instances, outside instance arguments and
proofs (`Lean.Expr.relevantConstantsAsSet`), and `hd(e)` the head constant of `e`.
For a candidate of sources 1 to 3 with conclusion `c` (the statement after all leading
universal quantifiers) and goal `t`,

  `score = [hd c = hd t] + |C c ∩ C t| / |C c ∪ C t|`,

the indicator of a common head plus the Jaccard overlap of the constant sets; it lies in
`[0, 2]`. An unfolding candidate found at depth `d` (`d = 0` for the head of the goal,
`d = 1` for the head of a side, and so on) has score `2 / (1 + d)`.

The sides of a term are its explicit arguments. The search for unfolding candidates
descends through the explicit arguments of heads that are not candidates (projection
functions such as `LE.le` and `HAdd.hAdd`, inductive types such as `Eq` and `And`, and
definitions of the modules `Init`, `Std`, `Lean`, `Lake`), up to depth 3. A candidate is a
definition that is no instance and no projection function, from any other module.

Candidates of score 0 are dropped. The others are ordered by score, ties by source in the
order `hypField`, `hyp`, `fileDecl`, `unfold`, then by order of retrieval; duplicates (by
printed term) are removed and the list is cut at `catcrypt_premises.max` entries
(default 16). Candidates are only
type-inferred, never elaborated.

`fileSelector` is source 1 as a `Lean.LibrarySuggestions.Selector`, to be combined with the
core selectors by `Lean.LibrarySuggestions.Selector.combine`.

## Tactic

`catcrypt_premises?` prints the list for the main goal, one line per candidate with its
score, source and term, and leaves the goal unchanged.

## Use by `catcrypt_auto`

The premise stage of `catcrypt_auto` (`CatCryptCore.Tactics.AutoDispatchCore`) passes the
candidates of sources 1 and 2 to its `premises` arms, and its unfolding pass is the
traversal `unfoldHeadsWith` of source 4 with the dispatcher's predicates.
-/

public section

namespace CatCrypt.Tactics.AutoPremises

open Lean Elab Tactic Meta

meta section

register_option catcrypt_premises.max : Nat := {
  defValue := 16
  descr := "the number of candidates `catcrypt_premises?` returns"
}

register_option catcrypt_premises.fieldDepth : Nat := {
  defValue := 2
  descr := "the depth of nested structure fields `catcrypt_premises?` reads from a hypothesis"
}

/-- The source of a candidate premise. -/
inductive Source where
  | hypField
  | hyp
  | fileDecl
  | unfold
  deriving Inhabited, BEq, Repr

/-- The rank of a source among candidates of equal score (smaller first). -/
def Source.rank : Source → Nat
  | .hypField => 0
  | .hyp => 1
  | .fileDecl => 2
  | .unfold => 3

/-- The name of a source, as printed by `catcrypt_premises?`. -/
def Source.name : Source → String
  | .hypField => "hypField"
  | .hyp => "hyp"
  | .fileDecl => "fileDecl"
  | .unfold => "unfold"

/-- A candidate premise: its source, the term (a constant, a projection of a hypothesis, or
a hypothesis applied to metavariables), the printed term and the score. -/
structure Premise where
  source : Source
  term : Expr
  display : String
  score : Float
  deriving Inhabited

/-- The name fragments marking a binder type as an adversary type. -/
def adversaryFragments : List String :=
  ["Adversary", "Distinguisher", "Forger", "Attacker", "Adv", "Prover", "Oracle", "SPComp"]

/-- `ty` mentions a constant whose last name component contains an adversary fragment. -/
def isAdversaryType (ty : Expr) : Bool :=
  (ty.find? fun s => match s.constName? with
    | some (.str _ last) => adversaryFragments.any fun frag => (last.splitOn frag).length > 1
    | _ => false).isSome

/-- The head constant of `e`. -/
def headConst? (e : Expr) : Option Name :=
  e.cleanupAnnotations.getAppFn.constName?

/-- `ty`, read under the adversary binder `x`, concludes `a ≤ ε` or `a < ε` with `x` not
in `ε`. -/
def isHardnessShape (x : Expr) (ty : Expr) : MetaM Bool :=
  forallTelescopeReducing ty fun _ concl => do
    let concl ← instantiateMVars concl
    match concl.cleanupAnnotations.getAppFnArgs with
    | (``LE.le, #[_, _, _, rhs]) | (``LT.lt, #[_, _, _, rhs]) =>
      return !rhs.containsFVar x.fvarId!
    | _ => return false

/-- Instantiates the leading universal quantifiers of `term : ty` by metavariables up to the
first adversary binder. Returns the instantiated term and the conclusion of the full
statement, or `none` when the statement has the hardness shape under an adversary
binder. -/
partial def instantiateNonAdversary (term ty : Expr) : MetaM (Option (Expr × Expr)) := do
  let ty ← whnfR (← instantiateMVars ty)
  match ty with
  | .forallE n d b _ =>
    if isAdversaryType d then
      let hard ← withLocalDeclD n d fun x => isHardnessShape x (b.instantiate1 x)
      if hard then return none
      let (_, _, concl) ← forallMetaTelescope ty
      return some (term, concl)
    let m ← mkFreshExprMVar d (userName := n)
    instantiateNonAdversary (mkApp term m) (b.instantiate1 m)
  | _ => return some (term, ty)

/-- The score of a conclusion against the goal: the head indicator plus the Jaccard overlap
of the constant sets. -/
def scoreAgainst (goalHead : Option Name) (goalConsts : NameSet) (concl : Expr) :
    MetaM Float := do
  let concl ← instantiateMVars concl
  let cs ← concl.relevantConstantsAsSet
  let inter := cs.foldl (fun k n => if goalConsts.contains n then k + 1 else k) 0
  let union := cs.size + goalConsts.size - inter
  let jac : Float := if union == 0 then 0 else inter.toFloat / union.toFloat
  let head : Float := if (headConst? concl).isSome && headConst? concl == goalHead then 1 else 0
  return head + jac

/-- The candidate for `term : ty` from `source`, or `none` when the statement is not a
proposition or has the hardness shape. -/
def candidate (source : Source) (goalHead : Option Name) (goalConsts : NameSet)
    (term ty : Expr) (display? : Option String := none) : MetaM (Option Premise) := do
  unless ← isProp ty do return none
  let some (inst, concl) ← instantiateNonAdversary term ty | return none
  let score ← scoreAgainst goalHead goalConsts concl
  let display ← match display? with
    | some d => pure d
    | none => do pure (toString (← ppExpr (← instantiateMVars inst)))
  return some { source, term := inst, display, score }

/-- The name `n` as written in the source: without the private prefix and relative to the
current namespace. -/
def displayName (n : Name) : MetaM String := do
  let n := privateToUserName n
  let ns ← getCurrNamespace
  let n := if ns != .anonymous && ns.isPrefixOf n && ns != n then n.replacePrefix ns .anonymous
    else n
  return n.toString

/-- Source 1: the theorems of the current module elaborated before the current
declaration `self?`, written in the source (with a declaration range) and not projection
functions; the auxiliary declarations of `self?` are skipped. -/
def fileDecls (self? : Option Name) (goalHead : Option Name) (goalConsts : NameSet) :
    MetaM (Array Premise) := do
  let env ← getEnv
  let mut out := #[]
  for (name, ci) in env.constants.map₂ do
    if LibrarySuggestions.isDeniedPremise env name (allowPrivate := true) then continue
    unless wasOriginallyTheorem env name do continue
    if env.isProjectionFn name then continue
    if let some self := self? then
      if self.isPrefixOf name then continue
    if (← findDeclarationRanges? name).isNone then continue
    let c ← mkConstWithFreshMVarLevels name
    let d ← displayName name
    if let some p ← candidate .fileDecl goalHead goalConsts c ci.type (some d) then
      out := out.push p
  return out

/-- Source 2: the `Prop`-valued fields of `term : ty` when `ty` is a structure, through nested
structure fields up to `depth`. -/
partial def structFields (goalHead : Option Name) (goalConsts : NameSet) (depth : Nat)
    (term ty : Expr) : MetaM (Array Premise) := do
  if depth == 0 then return #[]
  let ty ← whnfR (← instantiateMVars ty)
  let some sName := ty.getAppFn.constName? | return #[]
  let env ← getEnv
  unless isStructure env sName do return #[]
  let mut out := #[]
  for f in getStructureFieldsFlattened env sName (includeSubobjectFields := false) do
    let some proj ← observing? (mkProjection term f) | continue
    let some fty ← observing? (inferType proj) | continue
    if let some p ← candidate .hypField goalHead goalConsts proj fty then
      out := out.push p
    out := out ++ (← structFields goalHead goalConsts (depth - 1) proj fty)
  return out

/-- Sources 2 and 3: the local hypotheses other than instance arguments. -/
def hypotheses (goalHead : Option Name) (goalConsts : NameSet) (fieldDepth : Nat) :
    MetaM (Array Premise) := do
  let mut out := #[]
  for h in ← getLocalHyps do
    let decl ← h.fvarId!.getDecl
    if decl.binderInfo.isInstImplicit then continue
    let ty ← instantiateMVars decl.type
    if let some p ← candidate .hyp goalHead goalConsts h ty then
      out := out.push p
    out := out ++ (← structFields goalHead goalConsts fieldDepth h ty)
  return out

/-- The definition `c` is an unfolding candidate: no instance, no projection function, and
not from the modules `Init`, `Std`, `Lean`, `Lake`. -/
def isUnfoldCandidate (c : Name) : MetaM Bool := do
  let env ← getEnv
  let some (.defnInfo _) := env.find? c | return false
  if isInstanceCore env c then return false
  if env.isProjectionFn c then return false
  match env.getModuleIdxFor? c with
  | none => return true
  | some idx =>
    let root := (env.header.moduleNames[idx.toNat]!).getRoot
    return !([`Init, `Std, `Lean, `Lake].contains root)

/-- The unfolding traversal: on each branch of `e` through the explicit arguments, read
from depth `d` down to depth 3, the first head constant that `accept` accepts, with the
depth at which it occurs. A branch whose head is not accepted and satisfies `stop` is not
descended. Source 4 is this traversal with `isUnfoldCandidate`; the unfolding pass of
`catcrypt_auto` (`CatCryptCore.Tactics.AutoDispatchCore`) uses it with its own
predicates. -/
partial def unfoldHeadsWith (accept stop : Name → MetaM Bool) (e : Expr) (d : Nat)
    (acc : Array (Name × Nat)) : MetaM (Array (Name × Nat)) := do
  if d > 3 then return acc
  let e ← instantiateMVars e
  let e := e.cleanupAnnotations
  let some c := e.getAppFn.constName? | return acc
  if ← accept c then
    if acc.any (·.1 == c) then return acc
    return acc.push (c, d)
  if ← stop c then return acc
  let args := e.getAppArgs
  let fi ← getFunInfoNArgs e.getAppFn args.size
  let mut acc := acc
  for h : i in [:args.size] do
    let explicit := match fi.paramInfo[i]? with
      | some pi => pi.binderInfo.isExplicit
      | none => true
    if explicit then
      acc ← unfoldHeadsWith accept stop args[i] (d + 1) acc
  return acc

/-- Source 4: the unfolding candidates of `e` at depth `d` and below, up to depth 3. -/
def unfoldHeads (e : Expr) (d : Nat) (acc : Array (Name × Nat)) :
    MetaM (Array (Name × Nat)) :=
  unfoldHeadsWith isUnfoldCandidate (fun _ => pure false) e d acc

/-- Formats a score with two decimals. -/
def fmtScore (s : Float) : String :=
  let k := (s * 100).round.toUInt64.toNat
  let frac := k % 100
  s!"{k / 100}.{if frac < 10 then "0" else ""}{frac}"

/-- The ranked candidate premises for the goal `g` of the declaration `self?`, at most `max`
of them (see the module docstring for the sources and the score). -/
def premises (g : MVarId) (self? : Option Name := none) (max : Nat := 16)
    (fieldDepth : Nat := 2) : MetaM (Array Premise) := g.withContext do
  let target ← instantiateMVars (← g.getType)
  let goalHead := headConst? target
  let goalConsts ← target.relevantConstantsAsSet
  let hyps ← hypotheses goalHead goalConsts fieldDepth
  let decls ← fileDecls self? goalHead goalConsts
  let heads ← unfoldHeads target 0 #[]
  let unfolds ← heads.mapM fun (c, d) => do
    let display ← displayName c
    let score := 2.0 / (1 + d).toFloat
    return ({ source := .unfold, term := mkConst c, display, score } : Premise)
  let all := (hyps ++ decls ++ unfolds).filter (·.score > 0)
  let indexed := (List.range all.size).toArray.zip all
  let sorted := indexed.qsort fun (i, a) (j, b) =>
    a.score > b.score ||
      (a.score == b.score &&
        (a.source.rank < b.source.rank || (a.source.rank == b.source.rank && i < j)))
  let mut seen : Std.HashSet String := {}
  let mut out := #[]
  for (_, p) in sorted do
    if out.size ≥ max then break
    if seen.contains p.display then continue
    seen := seen.insert p.display
    out := out.push p
  return out

/-- Source 1 as a core premise selector: the theorems of the current module elaborated before
the current declaration, scored as in the module docstring, at most
`config.maxSuggestions` of them, filtered by `config.filter`. -/
def fileSelector : LibrarySuggestions.Selector := fun g config => g.withContext do
  let target ← instantiateMVars (← g.getType)
  let decls ← fileDecls none (headConst? target) (← target.relevantConstantsAsSet)
  let sorted := decls.qsort fun a b => a.score > b.score
  let mut out := #[]
  for p in sorted do
    if out.size ≥ config.maxSuggestions then break
    let some n := p.term.getAppFn.constName? | continue
    if ← config.filter n then
      out := out.push { name := n, score := p.score }
  return out

/-- `catcrypt_premises?` prints the ranked candidate premises for the main goal (see the
module docstring), at most `catcrypt_premises.max` of them, and leaves the goal
unchanged. -/
syntax (name := catcryptPremises) "catcrypt_premises?" : tactic

@[tactic catcryptPremises] def evalCatcryptPremises : Tactic := fun _ => do
  let g ← getMainGoal
  let opts ← getOptions
  let max := catcrypt_premises.max.get opts
  let depth := catcrypt_premises.fieldDepth.get opts
  let self? ← Term.getDeclName?
  let ps ← withoutModifyingState (premises g self? max depth)
  let lines := ps.toList.map fun p => m!"\n{fmtScore p.score} {p.source.name} {p.display}"
  logInfo (MessageData.joinSep (m!"premises:" :: lines) "")

end

end CatCrypt.Tactics.AutoPremises
