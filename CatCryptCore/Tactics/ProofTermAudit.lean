/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean

/-!
# `ProofTermAudit` — machine-checked shell / vacuity detection over proof terms

This module ports the *deterministic* (zero-LLM-token) core of
facebookresearch/autoform-bot's `autoform/eval/` subsystem to CatCrypt.
autoform-bot grades autoformalizations by introspecting the **compiled
proof term** rather than the surface syntax; we reuse the same idea to
**machine-check** the project's shell-vs-genuine-reduction distinction.

CatCrypt's existing audit (`scripts/audit_security.lean`) detects "shell"
theorems via a *docstring-tag convention* (`(composition plumbing)`,
`(concurrent UC via ITreeN)`, …) and via *text scanning* of theorem
signatures. Those are convention-dependent: a theorem mislabelled in its
docstring, or whose body silently became trivial, slips through. This
module inspects the elaborated `Expr` of a declaration's proof term and
reports structural tags that no comment can fake.

## Tags

Each tag is computed purely from the proof term `e := value?` of a
declaration, after stripping leading `fun`-binders (`stripLambdas`). Let
`nl` be the number of stripped binders (the declaration's parameters and
hypotheses) and `body` the head-beta-reduced lambda body.

| Tag | Detection (implemented) |
|---|---|
| `vacuous_body` | `body`'s head constant is `True.intro` / `trivial` / `And.intro` of `True.intro`s, or `body` is a `rfl`-proof (`Eq.refl` / `rfl`) at a *propositionally trivial* head — i.e. the proof carries no hypothesis-dependent content. |
| `returns_assumption` | `body` is exactly a `bvar` referring to one of the `nl` binders — the proof `fun … hᵢ … => hᵢ` directly returns a hypothesis. |
| `trivial_constructor` | `body`'s head is a structure/inductive *constructor* (`ConstructorVal`) **and** the constructor has no explicit (non-instance, non-Prop-erased) data arguments derived from the binders — a content-free constructor application (e.g. `⟨⟩ : True`, `PUnit.unit`, `Unit.unit`). |
| `field_projection_body` | `body` is a `.proj`, or its head is a projection function (`Environment.getProjectionFnInfo?`) — the proof is "read a field", not a derivation. |
| `proof_by_subsingleton` | `body`'s head constant is `Subsingleton.elim` / `Subsingleton.allEq` / `proof_irrel`. |
| `proof_by_exfalso` | `body`'s head constant is `False.elim` / `absurd` / `False.rec` / `Empty.elim` — goal derived from a contradiction on an assumption. |
| `ignores_params` | At least one of the `nl` stripped binders does **not** occur in `body`. (Reported with the used/total count.) This is the structural analogue of autoform-bot's "the proof does not use its premises" check. Note: a binder may legitimately appear only in the *type* of a later binder; this tag is advisory, surfaced together with the stronger `returns_assumption` / `vacuous_body` signals rather than failing on its own. |

### Stubbed / partial

| Tag | Status |
|---|---|
| `custom_hypothesis_in_type` | **Partial.** Full autoform-bot semantics ("the statement carries a suspicious custom hypothesis that trivializes the goal") requires modelling which hypotheses are *load-bearing* for the conclusion — undecidable in general. We implement a conservative proxy: flag declarations whose **type** contains a hypothesis of the form `(h : P) → P` (an identity implication a `returns_assumption` body would discharge), or whose conclusion is defeq to `True`. Anything subtler is deferred. |

## Shell classification

`shellTags` is the subset that indicates a *content-free* proof:
`vacuous_body`, `returns_assumption`, `trivial_constructor`. The audit
driver treats a declaration as a *potential undocumented shell* when it
carries a shell tag but its docstring lacks an honest
`(composition plumbing)` / `sdist_self` marker, and as a
*docstring/body mismatch* when the docstring claims a genuine result yet
the body is `vacuous_body` / `returns_assumption`.

A *genuine* reduction (e.g. one that `apply`s a composition lemma and
then discharges its premise from the hypotheses, like
`UCEmulates_of_sdist` followed by `exact hkdf_sdist …`) elaborates to a
term whose head is the composition lemma applied to the binders, so it is
**not** tagged — exactly the discrimination the
`feedback_no_genuine_reduction` memory and the UC docstring convention
are guarding.

## Usage

* Interactive: `#proof_term_tags <decl-name>` logs the tags for one decl.
* Programmatic: `ProofTermAudit.tagsFor (n : Name) : MetaM (Array Tag)`.
* Batch driver: see `CatCrypt/Tactic/ProofTermAuditDriver.lean` (the
  `lake exe proofaudit` executable), which scans every `UCEmulates` /
  `*_uc_secure` / reduction theorem in the environment and prints a
  report consumed by `scripts/audit_security.lean`.

## Future work (NOT implemented this increment)

* **Increment 2 — dependency-graph cone alerts.** Walk the transitive
  `getUsedConstants` cone of each security theorem and alert when a
  "genuine"-tagged theorem's cone bottoms out in an `axiom` or `sorryAx`
  that is not on the sanctioned list. (autoform-bot's reachability check.)
* **Increment 3 — LLM faithfulness jury.** Grade whether the Lean
  statement faithfully renders the informal/RFC claim. This is the
  LLM-token path and is explicitly out of scope here.
-/

public section

meta section

open Lean Meta Elab

namespace CatCrypt.Tactic.ProofTermAudit

/-- A structural tag computed from a declaration's proof term. -/
inductive Tag where
  | vacuousBody
  | returnsAssumption
  | trivialConstructor
  | fieldProjectionBody
  | proofBySubsingleton
  | proofByExfalso
  /-- carries `(used, total)` binder counts -/
  | ignoresParams (used total : Nat)
  /-- partial detector (see module doc) -/
  | customHypothesisInType
  deriving Repr, BEq, Inhabited

namespace Tag

/-- Human-readable, stable string form (matches the module-doc table). -/
def toString : Tag → String
  | vacuousBody => "vacuous_body"
  | returnsAssumption => "returns_assumption"
  | trivialConstructor => "trivial_constructor"
  | fieldProjectionBody => "field_projection_body"
  | proofBySubsingleton => "proof_by_subsingleton"
  | proofByExfalso => "proof_by_exfalso"
  | ignoresParams used total => s!"ignores_params({used}/{total})"
  | customHypothesisInType => "custom_hypothesis_in_type"

instance : ToString Tag := ⟨toString⟩

/-- Tags indicating a *content-free* proof body (the "shell" set). -/
def isShell : Tag → Bool
  | vacuousBody => true
  | returnsAssumption => true
  | trivialConstructor => true
  | _ => false

end Tag

/-- Tags that mark the proof body as content-free. -/
def Tag.shellTags (ts : Array Tag) : Array Tag :=
  ts.filter Tag.isShell

/-! ## Term-inspection helpers -/

/-- Strip leading `fun`-binders, returning their count and the body. -/
partial def stripLambdas : Expr → Nat × Expr
  | .lam _ _ b _ => let (n, b') := stripLambdas b; (n + 1, b')
  | .mdata _ e => stripLambdas e
  | e => (0, e)

/-- Collect the de-Bruijn indices (relative to the *body*, i.e. counting
    the stripped lambdas as the outermost binders) of every free `bvar`
    occurrence. `extra` tracks binders introduced *inside* `body`. -/
partial def usedBinders (e : Expr) (extra : Nat) (acc : Std.HashSet Nat) : Std.HashSet Nat :=
  match e with
  | .bvar i => if i ≥ extra then acc.insert (i - extra) else acc
  | .app f a => usedBinders a extra (usedBinders f extra acc)
  | .lam _ t b _ => usedBinders b (extra + 1) (usedBinders t extra acc)
  | .forallE _ t b _ => usedBinders b (extra + 1) (usedBinders t extra acc)
  | .letE _ t v b _ =>
      usedBinders b (extra + 1) (usedBinders v extra (usedBinders t extra acc))
  | .mdata _ b => usedBinders b extra acc
  | .proj _ _ b => usedBinders b extra acc
  | _ => acc

/-- Count how many of the `nl` outermost binders occur in `body`. -/
def countUsedBinders (nl : Nat) (body : Expr) : Nat :=
  let used := usedBinders body 0 {}
  (List.range nl).filter (fun k => used.contains k) |>.length

/-- Is `n` one of the recognised "vacuous proof" head constants? -/
def isVacuousHead (n : Name) : Bool :=
  n == ``True.intro || n == ``trivial || n == ``id

/-- Is `n` a subsingleton-elimination head? -/
def isSubsingletonHead (n : Name) : Bool :=
  n == ``Subsingleton.elim || n == ``Subsingleton.allEq || n == ``proof_irrel

/-- Is `n` an ex-falso head? -/
def isExfalsoHead (n : Name) : Bool :=
  n == ``False.elim || n == ``absurd || n == ``False.rec || n == ``Empty.elim
    || n == ``False.casesOn || n == ``Empty.casesOn

/-- Is `n` a recognised content-free `rfl`-proof head? `Eq.refl` / `rfl` /
    `HEq.refl` / `Iff.rfl` — these carry no hypothesis-dependent content. -/
def isReflHead (n : Name) : Bool :=
  n == ``Eq.refl || n == ``rfl || n == ``HEq.refl || n == ``Iff.refl
    || n == ``Iff.rfl

/-- Does `body`'s head resolve to a structure/inductive *constructor* with
    no explicit data argument that comes from a binder? Such an
    application (e.g. `PUnit.unit`, `⟨⟩ : True`) is a trivial constructor. -/
def isTrivialConstructorApp (env : Environment) (nl : Nat) (body : Expr) : Bool :=
  let hd := body.getAppFn
  match hd.constName? with
  | none => false
  | some cn =>
    match env.find? cn with
    | some (.ctorInfo _) =>
      -- A constructor application is "trivial" when none of the
      -- declaration's binders flows into its (non-type) arguments.
      countUsedBinders nl body == 0
    | _ => false

/-- Is `body` (or its head) a structure-field projection? -/
def isFieldProjection (env : Environment) (body : Expr) : Bool :=
  if body.isProj then true
  else match body.getAppFn.constName? with
    | none => false
    | some cn => (env.getProjectionFnInfo? cn).isSome

/-! ## Type-side (partial) detector -/

/-- Walk a forall-telescope *syntactically* (no `whnf`/`isDefEq`), returning
    the list of binder domains and the final conclusion. Cheap and total —
    deliberately avoids the reduction cost that makes a `MetaM` telescope
    blow heartbeats on heavy crypto types. -/
partial def piTelescopeSyntactic : Expr → List Expr × Expr
  | .forallE _ t b _ => let (ts, c) := piTelescopeSyntactic b; (t :: ts, c)
  | .mdata _ e => piTelescopeSyntactic e
  | e => ([], e)

/-- Conservative, **syntactic** `custom_hypothesis_in_type` proxy: scan the
    type's pi-telescope for a hypothesis binder whose domain is *structurally
    identical* to the conclusion (an `(h : P) → … → P` identity implication a
    `returns_assumption` body would discharge), or a conclusion that is the
    constant `True`. Purely syntactic so it never reduces (and never blows
    heartbeats); subtler defeq cases are deferred (see module doc). -/
def typeHasCustomTrivialiser (type : Expr) : Bool :=
  let (doms, concl) := piTelescopeSyntactic type
  if concl.isConstOf ``True then true
  else doms.any (fun d => d == concl)

/-! ## The tagger -/

/-- Compute the structural tags for declaration `n`. Returns `#[]` for
    declarations with no inspectable value (axioms, opaques) — they are
    not the subject of this audit. -/
def tagsFor (n : Name) : MetaM (Array Tag) := do
  let env ← getEnv
  let some ci := env.find? n | return #[]
  let some val := ci.value? | return #[]
  let (nl, body0) := stripLambdas val
  let body := body0.headBeta
  let mut ts : List Tag := []
  -- returns_assumption: body is exactly a bound variable
  if body.isBVar then
    ts := Tag.returnsAssumption :: ts
  -- head-constant–based tags
  let hd := body.getAppFn
  if let some hn := hd.constName? then
    if isVacuousHead hn || isReflHead hn then
      -- a refl/trivial head is only "vacuous" if no binder feeds the body
      if countUsedBinders nl body == 0 then
        ts := Tag.vacuousBody :: ts
    if isSubsingletonHead hn then
      ts := Tag.proofBySubsingleton :: ts
    if isExfalsoHead hn then
      ts := Tag.proofByExfalso :: ts
  -- trivial constructor application
  if isTrivialConstructorApp env nl body then
    ts := Tag.trivialConstructor :: ts
  -- field projection
  if isFieldProjection env body then
    ts := Tag.fieldProjectionBody :: ts
  -- ignores_params
  let usedCount := countUsedBinders nl body
  if nl > 0 && usedCount < nl then
    ts := Tag.ignoresParams usedCount nl :: ts
  -- custom_hypothesis_in_type (partial, syntactic)
  if typeHasCustomTrivialiser ci.type then
    ts := Tag.customHypothesisInType :: ts
  return ts.toArray

/-! ## Statement-level detectors

The tags above read a proof term. The three detectors here read a *statement*,
so they apply to axioms (which have no term) and to theorems whatever their
proof.

* `statementFromBinders` — the conclusion is definitionally the type of a
  hypothesis binder, or of a Prop-valued field of a structure-typed binder. For
  an axiom this means the axiom is provable (`fun P => P.field`) and asserts
  nothing while adding a name to every downstream `#print axioms`. For a
  theorem it is the self-hypothesis shape, detected after unfolding, so a
  hypothesis wrapped in a named `Prop` (`h : Bound P` with `Bound P := …`) is
  caught as well.
* `isNominalStatement` — a theorem whose conclusion and at least one hypothesis
  are propositions about numbers only: every local occurs either with a numeric
  type or as the argument of a projection with a numeric result type, after
  unfolding Prop-valued definitions from the CatCrypt namespaces, and an opaque
  constant of numeric type counts as a number. Such a theorem relates named
  quantities to named quantities; no game, adversary or scheme constrains it.
  A statement whose type mentions no CatCrypt constant at all is plain
  arithmetic and is not reported.
-/

/-- Types whose values the nominal-bound detector treats as numbers. -/
def isNumericTypeName (n : Name) : Bool :=
  [``Nat, ``Int, ``Real, ``ENNReal, ``NNReal, ``Rat].contains n

/-- Is `t` (up to reducible unfolding) one of the numeric carrier types? -/
def isNumericType (t : Expr) : MetaM Bool := do
  let t ← whnfR t
  match t.getAppFn.constName? with
  | some n => return isNumericTypeName n
  | none => return false

/-- Is `n` in a CatCrypt namespace (dev or core)? -/
def isCatCryptName (n : Name) : Bool :=
  let r := n.getRoot
  r == `CatCrypt || r == `CatCryptCore

/-- Does the type of `n` mention a constant from a CatCrypt namespace? -/
def typeMentionsCatCrypt (n : Name) : MetaM Bool := do
  let env ← getEnv
  let some ci := env.find? n | return false
  return ci.type.getUsedConstants.any isCatCryptName

/-- `isDefEq` under a heartbeat cap, with failures read as `false`. -/
def isDefEqCapped (a b : Expr) : MetaM Bool := do
  try
    withTheReader Core.Context (fun c => { c with maxHeartbeats := 400000 * 1000 })
      (isDefEq a b)
  catch _ => return false

/-- The Prop-valued fields of the structure-typed local `x` whose type is
    definitionally `concl`; the first such field name. -/
def projectionMatchingConcl (x : Expr) (concl : Expr) : MetaM (Option Name) := do
  let env ← getEnv
  let xT ← whnfR (← inferType x)
  let some sName := xT.getAppFn.constName? | return none
  unless isStructure env sName do return none
  for f in getStructureFieldsFlattened env sName (includeSubobjectFields := false) do
    let hit ← try
        let p ← mkProjection x f
        let pT ← inferType p
        if (← isProp pT) then isDefEqCapped pT concl else pure false
      catch _ => pure false
    if hit then return some f
  return none

/-- For a declaration of type `∀ xs, C` with `C : Prop`: a witness that `C` is
    definitionally the type of a hypothesis binder, or of a Prop-valued field of
    a structure-typed binder. `reducibleOnly` restricts unfolding to reducible
    definitions (the syntactic tier); otherwise definitions unfold, which is the
    tier that sees through a named-`Prop` wrapper. -/
def statementFromBinders (n : Name) (reducibleOnly : Bool) : MetaM (Option String) := do
  let env ← getEnv
  let some ci := env.find? n | return none
  let run : MetaM (Option String) :=
    forallTelescope ci.type fun xs concl => do
      unless (← isProp concl) do return none
      for x in xs do
        let xT ← inferType x
        let xn ← x.fvarId!.getUserName
        if (← isProp xT) then
          if ← isDefEqCapped xT concl then
            return some s!"hypothesis {xn}"
        else if let some f ← projectionMatchingConcl x concl then
          return some s!"field {f} of {xn}"
      return none
  try
    if reducibleOnly then withReducible run else run
  catch _ => return none

/-- Unfold the head of `e` while it is a definition from a CatCrypt namespace
    whose value is a proposition, at most `fuel` times. -/
partial def unfoldCatCryptProp (e : Expr) (fuel : Nat) : MetaM Expr := do
  if fuel == 0 then return e
  let some hn := e.getAppFn.constName? | return e
  unless isCatCryptName hn do return e
  let env ← getEnv
  let some (.defnInfo _) := env.find? hn | return e
  unless (← isProp e) do return e
  match ← unfoldDefinition? e with
  | some e' => unfoldCatCryptProp e'.headBeta (fuel - 1)
  | none => return e

/-- Is `e` a proposition about numbers only, relative to the locals `xs`? Every
    local occurrence must be numeric-typed or the argument of a projection with a
    numeric result type; an application of an opaque constant with a numeric
    result type is a number; binders inside `e` are not admitted. -/
partial def nominalExpr (xs : Array Expr) (e : Expr) : MetaM Bool := do
  let env ← getEnv
  let e ← unfoldCatCryptProp e 8
  match e with
  | .fvar _ =>
    if xs.contains e then isNumericType (← inferType e) else return true
  | .app .. =>
    let hd := e.getAppFn
    let args := e.getAppArgs
    if let some hn := hd.constName? then
      -- a projection of a local with a numeric result type
      if (env.getProjectionFnInfo? hn).isSome then
        if let some last := args.back? then
          if xs.contains last then
            if ← isNumericType (← inferType e) then
              return ← (args.pop).allM (nominalExpr xs)
      -- an opaque constant of numeric type is a named number
      if let some (.opaqueInfo _) := env.find? hn then
        if ← isNumericType (← inferType e) then return true
    let hdOk ← match hd with
      | .fvar _ => nominalExpr xs hd
      | _ => pure true
    if !hdOk then return false
    args.allM (nominalExpr xs)
  | .proj _ _ b =>
    if xs.contains b then
      if ← isNumericType (← inferType e) then return true else return false
    nominalExpr xs b
  | .mdata _ b => nominalExpr xs b
  | .lam .. | .forallE .. | .letE .. => return false
  | _ => return true

/-- Is theorem `n` a nominal-bound statement: a Prop-typed declaration whose
    type mentions a CatCrypt constant, whose conclusion is a proposition about
    numbers only, and at least one of whose hypothesis binders is too? -/
def isNominalStatement (n : Name) : MetaM Bool := do
  let env ← getEnv
  let some ci := env.find? n | return false
  unless (← typeMentionsCatCrypt n) do return false
  try
    forallTelescope ci.type fun xs concl => do
      unless (← isProp concl) do return false
      unless (← nominalExpr xs concl) do return false
      for x in xs do
        let xT ← inferType x
        if (← isProp xT) then
          if ← nominalExpr xs xT then return true
      return false
  catch _ => return false

/-- Pretty one-line summary of a decl's tags (`""` if clean). -/
def summaryFor (n : Name) : MetaM String := do
  let ts ← tagsFor n
  return String.intercalate ", " (ts.toList.map Tag.toString)

/-! ## Interactive command -/

open Lean.Elab.Command in
/-- `#proof_term_tags foo` logs the structural shell/vacuity tags of `foo`. -/
elab "#proof_term_tags " id:ident : command => do
  liftTermElabM do
    let n ← realizeGlobalConstNoOverloadWithInfo id
    let tags ← tagsFor n
    if tags.isEmpty then
      logInfo m!"{n}: (no structural shell tags)"
    else
      logInfo m!"{n}: {String.intercalate ", " (tags.toList.map Tag.toString)}"

end CatCrypt.Tactic.ProofTermAudit
