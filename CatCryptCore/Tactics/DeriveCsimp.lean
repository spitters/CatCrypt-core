/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.NatFindBounded
public import CatCryptCore.Tactics.DeriveCost
public import CatCryptCore.Tactics.ClassicalCostAudit
public meta import Lean.Compiler.CSimpAttr
public meta import Lean.Util.CollectAxioms

/-!
# `derive_csimp f via S`: proof-carrying runtime implementations

A `@[csimp]` theorem `@f = @g` makes the code generator compile every later occurrence of the
constant `f` as `g`. `derive_csimp f via S₁, …, Sₙ` builds `g` from source theorems `Sᵢ` and
proves the replacement:

* `f.csimpImpl`, with the type of `f`, including its implicit and instance arguments;
* `f.csimpImpl_eq : ∀ xs, f.csimpImpl xs = f xs`;
* `@[csimp] f_csimp : @f = @f.csimpImpl`.

The command works inside the binders `xs` of `f` on a target term, `f xs` at the start. Each
stage replaces the target `t` by a term `b` and proves `b = t`; the body of `f.csimpImpl` is the
last target. The stages:

* `eq S` — `S : ∀ ys, g ys = h ys` (either orientation), whose side matching the target is
  unified with it; the other side is the new target. `S` may have no hypothesis.
* `guard S fallback R` — `S : ∀ ys, D ys → g ys = h ys` with one hypothesis, `R` an `eq`
  source for the target; the new target is `if D then g else r`, with `D` decided by the
  instance found for `Decidable D`.
* `wrap S using he, hd` — `S : ∀ us, dom u₁ → … → φ (src us) = op (φ u₁) …`, a homomorphism
  on a domain, `hd : ∀ a, φ (e a) = a`, `he : ∀ a, dom (e a)`. Each argument `x` of `f` of the
  type decoded by `hd` is replaced by `φ (e x)`, `S` is matched against the result and its
  hypotheses are discharged by `he`; the new target is `φ (src (e x₁) …)`.
* `wrapR S using hd` — `S : ∀ ys, enc (op ys) = bop (enc y₁) …`, `hd : ∀ a, d (enc a) = a`;
  the new target is `d (bop (enc x₁) …)`.
* `transfer [r₁, ←r₂, …]` — unfolds `f` once if the target is `f xs`, then rewrites with the
  rules in order; this moves a definition through an equivalence (`e.symm (op (e x) (e y))`
  becomes the operation on the other side by the homomorphism lemma of `e` reversed and
  `e.symm_apply_apply`).
* `bounded hb` — the target unfolds to `if h : ∃ k, P k then Nat.find h else 0`, and
  `hb : ∀ k, P k → ∃ j, j ≤ b ∧ P j` (after its leading arguments); the new target is
  `boundedLeast P b`, a search over `List.range (b + 1)`.
* `unique hL` — the target unfolds to `if h : ∃! a, p a then some h.exists.choose else none`,
  and `hL : ∀ a, p a → a ∈ L`; the new target is `uniqueWitness p L`, the sole element of the
  deduplicated filter of `L`, which needs `DecidableEq` on the witness type.

## Checks and refusals

The command refuses, with a message naming `f` and the source, a conditional equation without
an encoding or a guard, a decoder missing in `wrapR`, an instance the implementation needs and
`f` does not take (a csimp replacement keeps the type of `f`), an implementation that uses a
constant without an algorithm (`ClassicalCostAudit.isClassicalConst`; types, type formers and
proofs are erased by the code generator and not inspected), a definition by a choice whose
witness is not unique, `bounded` without a bound, and an axiom outside `propext`,
`Classical.choice` and `Quot.sound` in the generated proof, in a source term or in the
definition of `f`. Lean does not check the axioms of a csimp theorem, and the axioms of a
compiled caller of `f` do not include them, so `sorryAx` or another axiom is refused here. The
statement `@f = @f.csimpImpl` mentions
`f`, so the axioms of the csimp theorem include those of `f` even when the generated proof
reaches `f` only by unfolding: a specification whose instance carries a `native_decide` proof is
refused at this point. The check is the one `#csimp_audit` (`CatCryptCore.Tactics.CsimpAudit`)
runs over an environment.

Callers of `f` compiled before the csimp theorem keep the code of `f`. The command warns, naming
the computable definitions of the current module that call `f`, and warns when `f` is defined in
another module.

## Cost

After the replacement the command runs `derive_cost f.csimpImpl` and, when it succeeds, defines
`f.timedCost := f.csimpImpl.timedCost`, so that `derive_timed` prices a call of `f` by the code
that runs. The justification of this cost is `f_csimp`. When the derivation is refused, the
command reports the refusal as information and registers no cost.

## Main definitions

* `boundedLeast`, `boundedLeast_eq` — the bounded least-witness search and its equation
* `uniqueWitness`, `uniqueWitness_eq` — the unique-witness search and its equation
* `ite_eq_of_imp` — the equation of a guarded implementation
* `derive_csimp f via S₁, …, Sₙ` — the command
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveCsimp

universe u v

/-- The least `k ≤ b` with `P k`, or `0`: the first hit of `find?` on `List.range (b + 1)`. -/
def boundedLeast (P : ℕ → Prop) [DecidablePred P] (b : ℕ) : ℕ :=
  ((List.range (b + 1)).find? (fun k => decide (P k))).getD 0

/-- The bounded search equals the classical least witness of `P` (or `0`), at any decision
procedures `D` of `∃ k, P k` and `J` of `P`, when every witness is dominated by one at most
`b`. -/
theorem boundedLeast_eq (P : ℕ → Prop) (I : DecidablePred P) (b : ℕ)
    (hb : ∀ k, P k → ∃ j, j ≤ b ∧ P j) (D : Decidable (∃ k, P k)) (J : DecidablePred P) :
    @boundedLeast P I b = @dite ℕ (∃ k, P k) D (fun h => @Nat.find P J h) (fun _ => 0) := by
  rw [boundedLeast, @CatCryptCore.ForMathlib.leastOr0_eq P I b hb]
  obtain rfl : I = J := Subsingleton.elim _ _
  congr

/-- The sole element of the deduplicated filter of `L` by `p`, or `none`. -/
def uniqueWitness {α : Type u} [DecidableEq α] (p : α → Prop) [DecidablePred p] (L : List α) :
    Option α :=
  match (L.filter (fun a => decide (p a))).dedup with
  | [a] => some a
  | _ => none

/-- The unique-witness search equals the choice of the unique witness of `p` (or `none`), at
any decision procedure `D` of `∃! a, p a`, when the witnesses of `p` lie in `L`. -/
theorem uniqueWitness_eq {α : Type u} [DecidableEq α] (p : α → Prop) [DecidablePred p]
    (L : List α) (hL : ∀ a, p a → a ∈ L) (D : Decidable (∃! a, p a)) :
    uniqueWitness p L =
      @dite (Option α) (∃! a, p a) D (fun h => some h.exists.choose) (fun _ => none) := by
  have h := CatCryptCore.ForMathlib.chooseOpt_eq_filter_dedup p L hL
  unfold uniqueWitness
  grind

/-- A guarded implementation `if c then a else b` equals `t` when `a = t` under `c` and
`b = t`. -/
theorem ite_eq_of_imp {α : Sort v} {c : Prop} [Decidable c] {a b t : α} (ha : c → a = t)
    (hb : b = t) : (if c then a else b) = t := by
  split
  · grind
  · grind

end CatCrypt.Tactics.DeriveCsimp

namespace CatCrypt.Tactics.DeriveCsimp

open Lean Elab Meta Term Command
open CatCrypt.Tactics.ClassicalCostAudit

/-- The axioms a generated csimp theorem may depend on. -/
meta def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- The stages of `derive_csimp`. -/
declare_syntax_cat csimpStage (behavior := symbol)

/-- `eq S`: an unconditional equation `S`, one side of which matches the target. -/
syntax (name := stageEq) &"eq " term:max : csimpStage
/-- `guard S fallback R`: an equation `S` under one decidable hypothesis, with the `eq` source
`R` for the other case. -/
syntax (name := stageGuard) &"guard " term:max (&" fallback " term:max)? : csimpStage
/-- `wrap S using he, hd`: a homomorphism `S` on a domain, with an encoding into the domain
(`he`) and its decoding (`hd`). -/
syntax (name := stageWrap) &"wrap " term:max (&" using " term:max ", " term:max)? : csimpStage
/-- `wrapR S using hd`: a commuting square `S` of an encoding, with its decoder `hd`. -/
syntax (name := stageWrapR) &"wrapR " term:max (&" using " term:max)? : csimpStage
/-- `transfer [r₁, ←r₂, …]`: unfold the specification once and rewrite. -/
syntax (name := stageTransfer) &"transfer " Lean.Parser.Tactic.rwRuleSeq : csimpStage
/-- `bounded hb`: the bounded least witness, with the witness bound `hb`. -/
syntax (name := stageBounded) &"bounded" (term:max)? : csimpStage
/-- `unique hL`: the unique witness, with the witnesses in the list of `hL`. -/
syntax (name := stageUnique) &"unique " term:max : csimpStage

/-- `derive_csimp f via S₁, …, Sₙ` defines `f.csimpImpl` from the stages `Sᵢ`, proves
`f.csimpImpl_eq` and registers `@[csimp] f_csimp : @f = @f.csimpImpl`. -/
syntax (name := deriveCsimpCmd) "derive_csimp " ident &" via " csimpStage,+ : command

/-- A parsed stage: its kind, its elaborated sources, the orientation flags of `transfer` and
the source syntax. -/
abbrev StageData := Name × Array AbstractMVarsResult × Array Bool × Array Syntax

/-- Elaborates a source term at the command level, with its remaining metavariables (and the
universe levels of a constant) abstracted, to be opened inside the binders of `f`. -/
meta def elabSource (stx : Syntax) : TermElabM AbstractMVarsResult := do
  let e ← withoutErrToSorry do
    if stx.isIdent then
      try
        let c ← realizeGlobalConstNoOverloadWithInfo stx
        mkConstWithFreshMVarLevels c
      catch _ => elabTerm stx none
    else elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing
  abstractMVars (← instantiateMVars e)

/-- The message of an implementation instance that `f` does not take. -/
meta def instanceMsg (f : Name) (ty : Expr) : MessageData :=
  m!"derive_csimp {f}: `{f}.csimpImpl` needs the instance `[{ty}]` that `{f}` does not take; \
    a csimp replacement keeps the type of `{f}` including its instance arguments. Install it at \
    a monomorphic constant, or add the binder to `{f}`."

/-- The message of a conditional equation without an encoding or a guard. -/
meta def conditionalMsg (f : Name) (src : Syntax) (D : MessageData) : MessageData :=
  m!"derive_csimp {f}: `{src}` is conditional on `{D}` and no total encoding into it was \
    found; supply `wrap {src} using he, hd` with `he : ∀ a, D (e a)` and \
    `hd : ∀ a, φ (e a) = a`, or `guard {src} fallback R` with a decision procedure for the \
    condition and a computable fallback `R : ∀ x, r x = {f} x`."

/-- Assigns the metavariables `ms` left unassigned that are instances, by synthesis, and returns
those that are propositions (the hypotheses). Any other unassigned metavariable is an error. -/
meta def finishMVars (f : Name) (src : Syntax) (ms : Array Expr) : MetaM (Array MVarId) := do
  let mut hyps := #[]
  for m in ms do
    let m := m.mvarId!
    if ← m.isAssigned then continue
    let ty ← instantiateMVars (← m.getType)
    if (← isClass? ty).isSome then
      match ← trySynthInstance ty with
      | .some val =>
        unless ← isDefEq (.mvar m) val do throwError instanceMsg f ty
      | _ => throwError instanceMsg f ty
    else if ← isProp ty then
      hyps := hyps.push m
    else
      throwError "derive_csimp {f}: the argument `{Expr.mvar m}` : `{ty}` of `{src}` is not \
        determined by the target"
  return hyps

/-- The source `r` opened in the current context and applied to fresh metavariables for its
binders: the instance, all its metavariables and its conclusion. -/
meta def openSource (r : AbstractMVarsResult) : MetaM (Expr × Array Expr × Expr) := do
  let (ms₀, _, pf) ← openAbstractMVarsResult r
  let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType pf)
  return (mkAppN pf ms, ms₀ ++ ms, ← instantiateMVars concl)

/-- Matches a side of the equation `concl` with `t`: the other side and whether the proof must
be reversed to state `other = t`. The side whose head is that of `t` is tried first; a side
headed by a metavariable is not tried. -/
meta def matchEq (concl t : Expr) : MetaM (Option (Expr × Bool)) := do
  let some (_, l, r) := concl.eq? | return none
  let tHead := t.getAppFn.constName?
  let lFirst := tHead.isSome && l.getAppFn.constName? == tHead
  let cands := if lFirst then #[(l, r, true), (r, l, false)] else #[(r, l, false), (l, r, true)]
  for (side, other, symm) in cands do
    if side.getAppFn.isMVar then continue
    if ← isDefEq side t then return some (other, symm)
  return none

/-- The proof `pf : l = r` oriented as `other = t` by `matchEq`. -/
meta def orient (pf : Expr) (symm : Bool) : MetaM Expr := do
  let pf ← instantiateMVars pf
  if symm then mkEqSymm pf else pure pf

/-- Instantiates the leading binders of the source `r` until its type is `expected`. -/
meta def instantiatePrefix (f : Name) (src : Syntax) (r : AbstractMVarsResult) (expected : Expr) :
    MetaM Expr := do
  let (ms₀, _, pf) ← openAbstractMVarsResult r
  let ty ← inferType pf
  let n ← forallTelescopeReducing ty fun xs _ => pure xs.size
  for k in [0:n + 1] do
    let saved ← saveState
    let (ms, _, rest) ← forallMetaBoundedTelescope ty k
    if ← isDefEq rest expected then
      let hyps ← finishMVars f src (ms₀ ++ ms)
      unless hyps.isEmpty do
        throwError "derive_csimp {f}: `{src}` leaves the hypothesis \
          `{← instantiateMVars (← hyps[0]!.getType)}`"
      return ← instantiateMVars (mkAppN pf ms)
    saved.restore
  throwError "derive_csimp {f}: `{src}` does not state `{← instantiateMVars expected}` after its \
    leading arguments"

/-- Stage `eq`: `(body, body = t)`. -/
meta def stageEqRun (f : Name) (src : Syntax) (r : AbstractMVarsResult) (t : Expr) :
    MetaM (Expr × Expr) := do
  let (pf, ms, concl) ← openSource r
  let some (body, symm) ← matchEq concl t
    | throwError "derive_csimp {f}: no side of the conclusion `{concl}` of `{src}` matches \
        `{t}`"
  let hyps ← finishMVars f src ms
  if let some h := hyps[0]? then
    throwError conditionalMsg f src m!"{← instantiateMVars (← h.getType)}"
  return (← instantiateMVars body, ← orient pf symm)

/-- Stage `guard`: `(if D then g else r, proof)`. -/
meta def stageGuardRun (f : Name) (src fbStx : Syntax) (r fb : AbstractMVarsResult) (t : Expr) :
    MetaM (Expr × Expr) := do
  let (pf, ms, concl) ← openSource r
  let some (gbody, symm) ← matchEq concl t
    | throwError "derive_csimp {f}: no side of the conclusion `{concl}` of `{src}` matches \
        `{t}`"
  let hyps ← finishMVars f src ms
  let some h := hyps[0]?
    | throwError "derive_csimp {f}: guard: `{src}` has no hypothesis; use `eq {src}`"
  unless hyps.size == 1 do
    throwError "derive_csimp {f}: guard: `{src}` has {hyps.size} hypotheses; state them as one \
      conjunction"
  let D ← instantiateMVars (← h.getType)
  if D.hasMVar then
    throwError "derive_csimp {f}: guard: the condition `{D}` of `{src}` is not determined"
  let (rbody, rpf) ← stageEqRun f fbStx fb t
  let pImp ← mkLambdaFVars #[.mvar h] (← orient pf symm)
  let gbody ← instantiateMVars gbody
  let decTy := mkApp (mkConst ``Decidable) D
  let some decInst ← (do match ← trySynthInstance decTy with
      | .some i => pure (some i)
      | _ => pure none) | throwError instanceMsg f decTy
  let α ← inferType t
  let lvl ← getLevel α
  let body := mkApp5 (mkConst ``ite [lvl]) α D decInst gbody rbody
  let proof := mkAppN (mkConst ``ite_eq_of_imp [lvl]) #[α, D, decInst, gbody, rbody, t, pImp, rpf]
  return (body, proof)

/-- Stage `wrap`: `(φ (src (e x₁) …), proof)`. -/
meta def stageWrapRun (f : Name) (xs : Array Expr) (stxs : Array Syntax)
    (src he hd : AbstractMVarsResult) (t : Expr) : MetaM (Expr × Expr) := do
  -- The arguments of `f` decoded by `hd`, with `φ (e x)` and `φ (e x) = x`.
  let mut subs : Array (Expr × Expr × Expr) := #[]
  for x in xs do
    let saved ← saveState
    let (hpf, hms, hc) ← openSource hd
    let some (_, hl, hr) := hc.eq?
      | throwError "derive_csimp {f}: wrap: `{stxs[2]!}` is not an equation `φ (e a) = a`"
    if hr.isMVar && (← isDefEq (← inferType hr) (← inferType x)) && (← isDefEq hr x) then
      let hyps ← finishMVars f stxs[2]! hms
      unless hyps.isEmpty do
        throwError "derive_csimp {f}: wrap: `{stxs[2]!}` has a hypothesis"
      subs := subs.push (x, ← instantiateMVars hl, ← instantiateMVars hpf)
    else saved.restore
  if subs.isEmpty then
    throwError "derive_csimp {f}: wrap: no argument of `{f}` has the type decoded by \
      `{stxs[2]!}`"
  let tStar := t.replaceFVars (subs.map (·.1)) (subs.map (·.2.1))
  let (pf, ms, concl) ← openSource src
  let some (body, symm) ← matchEq concl tStar
    | throwError "derive_csimp {f}: wrap: no side of the conclusion `{concl}` of `{stxs[0]!}` \
        matches `{tStar}`"
  let hyps ← finishMVars f stxs[0]! ms
  for h in hyps do
    if ← h.isAssigned then continue
    let D ← instantiateMVars (← h.getType)
    let (hepf, hems, hec) ← openSource he
    unless ← isDefEq hec D do
      throwError "derive_csimp {f}: wrap: `{stxs[1]!}` does not discharge `{D}`"
    let rest ← finishMVars f stxs[1]! hems
    unless rest.isEmpty do
      throwError "derive_csimp {f}: wrap: `{stxs[1]!}` has a hypothesis"
    h.assign (← instantiateMVars hepf)
  let mut proof ← orient pf symm
  -- `T k`: `t` with the substitutions from `k` on; `T 0 = tStar`, `T n = t`.
  let n := subs.size
  for k in [0:n] do
    let later := subs.extract (k + 1) n
    let tNext := t.replaceFVars (later.map (·.1)) (later.map (·.2.1))
    let (x, _, px) := subs[k]!
    let motive ← mkLambdaFVars #[x] tNext
    proof ← mkEqTrans proof (← mkCongrArg motive px)
  return (← instantiateMVars body, proof)

/-- Stage `wrapR`: `(d (bop (enc x₁) …), proof)`. -/
meta def stageWrapRRun (f : Name) (stxs : Array Syntax) (src hd : AbstractMVarsResult)
    (t : Expr) : MetaM (Expr × Expr) := do
  let (hpf, hms, hc) ← openSource hd
  let some (_, hl, hr) := hc.eq?
    | throwError "derive_csimp {f}: wrapR: `{stxs[1]!}` is not an equation `d (enc a) = a`"
  unless hr.isMVar && (← isDefEq hr t) do
    throwError "derive_csimp {f}: wrapR: `{stxs[1]!}` does not decode values of the type of \
      `{t}`"
  let hyps ← finishMVars f stxs[1]! hms
  unless hyps.isEmpty do
    throwError "derive_csimp {f}: wrapR: `{stxs[1]!}` has a hypothesis"
  let hl ← instantiateMVars hl
  unless hl.isApp do
    throwError "derive_csimp {f}: wrapR: `{stxs[1]!}` is not of the form `d (enc a) = a`"
  let dfn := hl.appFn!
  let X := hl.appArg!
  let (pf, ms, concl) ← openSource src
  let some (body₀, symm) ← matchEq concl X
    | throwError "derive_csimp {f}: wrapR: no side of the conclusion `{concl}` of `{stxs[0]!}` \
        matches `{X}`"
  let hyps ← finishMVars f stxs[0]! ms
  if let some h := hyps[0]? then
    throwError conditionalMsg f stxs[0]! m!"{← instantiateMVars (← h.getType)}"
  let pf ← orient pf symm
  let body₀ ← instantiateMVars body₀
  let proof ← mkEqTrans (← mkCongrArg dfn pf) (← instantiateMVars hpf)
  return (mkApp dfn body₀, proof)

/-- Stage `transfer`: unfold `f` once and rewrite with the rules in order. -/
meta def stageTransferRun (f : Name) (stxs : Array Syntax) (rules : Array AbstractMVarsResult)
    (symms : Array Bool) (t : Expr) : MetaM (Expr × Expr) := do
  let t₁ ← if t.getAppFn.isConstOf f then
      pure ((← unfoldDefinition? t).getD t).headBeta
    else pure t
  let mut cur := t₁
  let mut proof ← mkEqRefl t₁
  for i in [0:rules.size] do
    let (_, _, pf) ← openAbstractMVarsResult rules[i]!
    let g ← mkFreshExprMVar (← mkEq cur cur)
    let res ← try g.mvarId!.rewrite cur pf symms[i]!
      catch e => throwError "derive_csimp {f}: transfer: the rule `{stxs[i]!}` does not \
        rewrite `{cur}`: {e.toMessageData}"
    for m in res.mvarIds do
      unless ← m.isAssigned do
        throwError conditionalMsg f stxs[i]! m!"{← instantiateMVars (← m.getType)}"
    proof ← mkEqTrans (← mkEqSymm res.eqProof) proof
    cur ← instantiateMVars res.eNew
  return (cur, proof)

/-- Stage `bounded`: `(boundedLeast P b, proof)`. -/
meta def stageBoundedRun (f : Name) (stx : Syntax) (hb : AbstractMVarsResult) (t : Expr) :
    MetaM (Expr × Expr) := do
  let v := ((← unfoldDefinition? t).getD t).headBeta
  let fail {β : Type} : MetaM β := throwError "derive_csimp {f}: bounded: `{t}` does not unfold \
    to `if h : ∃ k, P k then Nat.find h else 0`; it unfolds to `{v}`"
  unless v.isAppOfArity ``dite 5 do fail
  let args := v.getAppArgs
  let c := args[1]!
  unless c.isAppOfArity ``Exists 2 && (← isDefEq args[0]! (mkConst ``Nat)) do fail
  let P := c.appArg!
  let D := args[2]!
  let J ← match args[3]! with
    | .lam _ _ b _ =>
      if b.isAppOfArity ``Nat.find 3 && !(b.getArg! 1).hasLooseBVars then pure (b.getArg! 1)
      else fail
    | _ => fail
  let predTy ← mkAppM ``DecidablePred #[P]
  let I ← match ← trySynthInstance predTy with
    | .some i => pure i
    | _ => throwError instanceMsg f predTy
  let b ← mkFreshExprMVar (mkConst ``Nat)
  let nat := Lean.mkConst ``Nat
  let expected ← withLocalDeclD `k nat fun k => do
    withLocalDeclD `hk (mkApp P k).headBeta fun hk => do
      let ex ← withLocalDeclD `j nat fun j => do
        mkLambdaFVars #[j] (← mkAppM ``And #[← mkAppM ``LE.le #[j, b], (mkApp P j).headBeta])
      mkForallFVars #[k, hk] (← mkAppM ``Exists #[ex])
  let hbPf ← instantiatePrefix f stx hb expected
  let b ← instantiateMVars b
  if b.hasMVar then
    throwError "derive_csimp {f}: bounded: the bound of `{stx}` is not determined"
  let body ← mkAppOptM ``boundedLeast #[P, I, b]
  let proof ← mkAppOptM ``boundedLeast_eq #[P, I, b, hbPf, D, J]
  return (body, proof)

/-- Stage `unique`: `(uniqueWitness p L, proof)`. -/
meta def stageUniqueRun (f : Name) (stx : Syntax) (hL : AbstractMVarsResult) (t : Expr) :
    MetaM (Expr × Expr) := do
  let v := ((← unfoldDefinition? t).getD t).headBeta
  let args := v.getAppArgs
  unless v.isAppOfArity ``dite 5 && args[1]!.isAppOfArity ``ExistsUnique 2 do
    if (v.find? fun e => e.isConst && choiceConstants.contains e.constName!).isSome then
      throwError "derive_csimp {f}: `{f}` is defined by a choice whose witness is not \
        determined (`Classical.choose` of a non-unique existential): no computable function \
        provably equals it."
    throwError "derive_csimp {f}: unique: `{t}` does not unfold to \
      `if h : ∃! a, p a then some h.exists.choose else none`; it unfolds to `{v}`"
  let c := args[1]!
  let α := c.getArg! 0
  let p := c.appArg!
  let D := args[2]!
  let eqTy ← mkAppM ``DecidableEq #[α]
  let decEq ← match ← trySynthInstance eqTy with
    | .some i => pure i
    | _ => throwError instanceMsg f eqTy
  let predTy ← mkAppM ``DecidablePred #[p]
  let decP ← match ← trySynthInstance predTy with
    | .some i => pure i
    | _ => throwError instanceMsg f predTy
  let L ← mkFreshExprMVar (← mkAppM ``List #[α])
  let expected ← withLocalDeclD `a α fun a => do
    withLocalDeclD `h (mkApp p a).headBeta fun h => do
      mkForallFVars #[a, h] (← mkAppM ``Membership.mem #[L, a])
  let hLPf ← instantiatePrefix f stx hL expected
  let L ← instantiateMVars L
  let body ← mkAppOptM ``uniqueWitness #[α, decEq, p, decP, L]
  let proof ← mkAppOptM ``uniqueWitness_eq #[α, decEq, p, decP, L, hLPf, D]
  return (body, proof)

/-- Runs one stage on the target `t`: the new target and its equation with `t`. -/
meta def runStage (f : Name) (xs : Array Expr) (st : StageData) (t : Expr) :
    MetaM (Expr × Expr) := do
  let (k, rs, flags, stxs) := st
  if k == ``stageEq then stageEqRun f stxs[0]! rs[0]! t
  else if k == ``stageGuard then stageGuardRun f stxs[0]! stxs[1]! rs[0]! rs[1]! t
  else if k == ``stageWrap then stageWrapRun f xs stxs rs[0]! rs[1]! rs[2]! t
  else if k == ``stageWrapR then stageWrapRRun f stxs rs[0]! rs[1]! t
  else if k == ``stageTransfer then stageTransferRun f stxs rs flags t
  else if k == ``stageBounded then stageBoundedRun f stxs[0]! rs[0]! t
  else if k == ``stageUnique then stageUniqueRun f stxs[0]! rs[0]! t
  else throwError "derive_csimp {f}: unknown stage {k}"

/-- Elaborates the sources of a stage. -/
meta def parseStage (f : Name) (stx : Syntax) : TermElabM StageData := do
  let k := stx.getKind
  if k == ``stageEq || k == ``stageUnique then
    return (k, #[← elabSource stx[1]], #[], #[stx[1]])
  else if k == ``stageGuard then
    if stx[2].getNumArgs == 0 then
      throwErrorAt stx "derive_csimp {f}: guard: no fallback given; supply \
        `guard {stx[1]} fallback R` with a computable `r` and `R : ∀ x, r x = {f} x`."
    return (k, #[← elabSource stx[1], ← elabSource stx[2][1]], #[], #[stx[1], stx[2][1]])
  else if k == ``stageWrap then
    if stx[2].getNumArgs == 0 then
      throwErrorAt stx "derive_csimp {f}: `{stx[1]}` is conditional and no total encoding into \
        its domain was given; supply `wrap {stx[1]} using he, hd` with `he : ∀ a, dom (e a)` \
        and `hd : ∀ a, φ (e a) = a`."
    return (k, #[← elabSource stx[1], ← elabSource stx[2][1], ← elabSource stx[2][3]], #[],
      #[stx[1], stx[2][1], stx[2][3]])
  else if k == ``stageWrapR then
    if stx[2].getNumArgs == 0 then
      throwErrorAt stx "derive_csimp {f}: `{stx[1]}` gives an injective encoding but no \
        decoder; supply `wrapR {stx[1]} using hd` with a computable `d` and \
        `hd : ∀ a, d (enc a) = a`."
    return (k, #[← elabSource stx[1], ← elabSource stx[2][1]], #[], #[stx[1], stx[2][1]])
  else if k == ``stageTransfer then
    let rules := stx[1][1].getSepArgs
    let rs ← rules.mapM fun r => elabSource r[1]
    return (k, rs, rules.map fun r => !r[0].isNone, rules.map (·[1]))
  else if k == ``stageBounded then
    if stx[1].getNumArgs == 0 then
      throwErrorAt stx "derive_csimp {f}: bounded: no bound given; prove \
        `∀ x k, P x k → ∃ j ≤ b x, P x j` for a computable `b`."
    return (k, #[← elabSource stx[1][0]], #[], #[stx[1][0]])
  else throwErrorAt stx "derive_csimp {f}: unknown stage"

/-- The constants without an algorithm (`isClassicalConst`) in the computationally relevant part
of `e`: types, type formers and proofs are skipped, since the code generator erases them. -/
meta partial def classicalUses (e : Expr) : MetaM (Array Name) := do
  let r ← IO.mkRef (#[] : Array Name)
  let env ← getEnv
  let rec go (e : Expr) : MetaM Unit := do
    if e.isSort then return
    if (← isProof e) || (← isType e) || (← isTypeFormer e) then return
    match e with
    | .lam .. => lambdaTelescope e fun _ b => go b
    | .letE .. => lambdaLetTelescope e fun _ b => go b
    | .mdata _ b => go b
    | .proj _ _ b => go b
    | .const c _ =>
      if isClassicalConst env c then r.modify fun a => if a.contains c then a else a.push c
    | .app .. => e.withApp fun fn args => do
      go fn
      for a in args do go a
    | _ => pure ()
  go e
  r.get

/-- The axioms of the constants used by `e`. -/
meta def axiomsOf (e : Expr) : CoreM (Array Name) := do
  let mut acc := #[]
  for c in e.getUsedConstants do
    for a in ← collectAxioms c do
      unless acc.contains a do acc := acc.push a
  return acc

/-- The computable definitions of the current module, other than those under `f`, whose value
mentions `f`; their code was compiled before the replacement. -/
meta def earlierCallers (env : Environment) (f : Name) : Array Name :=
  let found := env.constants.map₂.foldl (init := #[]) fun acc n ci =>
    match ci with
    | .defnInfo d =>
      if !f.isPrefixOf n && !isNoncomputable env n && (d.value.find? (·.isConstOf f)).isSome
      then acc.push n else acc
    | _ => acc
  found.qsort Name.lt

/-- The core of `derive_csimp`: defines `f.csimpImpl`, proves `f.csimpImpl_eq` and registers
`f_csimp`. -/
meta def deriveCsimpCore (f : Name) (stages : Array StageData) : TermElabM Unit := do
  let env ← getEnv
  let info ← getConstInfo f
  unless info.isDefinition do
    throwError "derive_csimp {f}: `{f}` is not a definition"
  if (Compiler.CSimp.ext.getState env).map.contains f then
    throwError "derive_csimp {f}: `{f}` already has a csimp replacement"
  let implName := f ++ `csimpImpl
  let eqName := f ++ `csimpImpl_eq
  let thmName := f.appendAfter "_csimp"
  for n in [implName, eqName, thmName] do
    if env.contains n then throwError "derive_csimp {f}: `{n}` is already declared"
  let us := info.levelParams.map mkLevelParam
  let fC := Lean.mkConst f us
  let (implVal, eqPf) ← forallTelescope (α := Expr × Expr) info.type fun xs _ => do
    let t := mkAppN fC xs
    let mut cur := t
    let mut proof ← mkEqRefl t
    for st in stages do
      let (b, p) ← runStage f xs st cur
      proof ← mkEqTrans p proof
      cur := b
    let body ← instantiateMVars cur
    let pf ← instantiateMVars proof
    if body.hasMVar || pf.hasMVar then
      throwError "derive_csimp {f}: the implementation `{body}` is not determined"
    if (body.find? (·.isConstOf f)).isSome then
      throwError "derive_csimp {f}: the implementation `{body}` calls `{f}`"
    let bad ← classicalUses body
    if let some c := bad[0]? then
      throwError "derive_csimp {f}: `{f}.csimpImpl` is not computable: `{body}` uses `{c}` \
        (noncomputable, no csimp, implemented_by or extern)."
    return (← mkLambdaFVars xs body, ← mkLambdaFVars xs pf)
  Meta.check eqPf
  let bad := (← axiomsOf eqPf).filter (!standardAxioms.contains ·)
  if bad.contains ``sorryAx then
    throwError "derive_csimp {f}: the proof of `{thmName}` depends on `sorryAx`; a csimp \
      theorem is not recorded in the axioms of its callers, so it must be fully proved."
  if let some a := bad[0]? then
    throwError "derive_csimp {f}: the proof of `{thmName}` depends on the axiom `{a}`; a csimp \
      theorem is not recorded in the axioms of its callers, so it may use only `propext`, \
      `Classical.choice` and `Quot.sound`."
  for (_, rs, _, stxs) in stages do
    for i in [0:rs.size] do
      if let some a := (← axiomsOf rs[i]!.expr).find? (!standardAxioms.contains ·) then
        throwError "derive_csimp {f}: the source `{stxs[i]!}` depends on the axiom `{a}`; a csimp \
          theorem may use only `propext`, `Classical.choice` and `Quot.sound`."
  if let some a := (← collectAxioms f).find? (!standardAxioms.contains ·) then
    throwError "derive_csimp {f}: the definition of `{f}` depends on the axiom `{a}`, and so \
      does the statement `@{f} = @{implName}` of `{thmName}`; a csimp theorem may use only \
      `propext`, `Classical.choice` and `Quot.sound`."
  let implDecl := Declaration.defnDecl {
    name := implName, levelParams := info.levelParams, type := info.type, value := implVal,
    hints := .regular (getMaxHeight (← getEnv) implVal + 1), safety := .safe,
    all := [implName] }
  addDecl implDecl (forceExpose := true)
  compileDecl implDecl
  addDocStringCore implName s!"The runtime implementation of `{f}` derived by `derive_csimp`."
  let implC := Lean.mkConst implName us
  let eqStmt ← forallTelescope info.type fun xs _ => do
    mkForallFVars xs (← mkEq (mkAppN implC xs) (mkAppN fC xs))
  unless ← isDefEq (← inferType eqPf) eqStmt do
    throwError "derive_csimp {f}: the derived equation `{← inferType eqPf}` is not `{eqStmt}`"
  let eqVal : TheoremVal :=
    { name := eqName, levelParams := info.levelParams, type := eqStmt, value := eqPf }
  addDecl (.thmDecl eqVal)
  addDocStringCore eqName s!"`{implName}` computes `{f}`."
  let eqC := Lean.mkConst eqName us
  let csimpPf ← forallTelescope info.type fun xs _ => do
    let mut pf ← mkEqSymm (mkAppN eqC xs)
    for i in (List.range xs.size).reverse do
      pf ← mkFunExt (← mkLambdaFVars #[xs[i]!] pf)
    return pf
  let csimpTy ← mkEq fC implC
  let csimpVal : TheoremVal :=
    { name := thmName, levelParams := info.levelParams, type := csimpTy, value := csimpPf }
  addDecl (.thmDecl csimpVal)
  addDocStringCore thmName s!"`{f}` is compiled as `{implName}`."
  Compiler.CSimp.add thmName .global
  let callers := earlierCallers (← getEnv) f
  unless callers.isEmpty do
    logWarning m!"derive_csimp {f}: `{f}` has compiled callers earlier in this module \
      ({callers.toList}); they keep the code of `{f}`."
  if let some idx := (← getEnv).getModuleIdxFor? f then
    let mod := (← getEnv).header.moduleNames[idx.toNat]!
    logWarning m!"derive_csimp {f}: `{f}` is defined in the module `{mod}`; code compiled there \
      and in the modules imported here keeps the code of `{f}`."

/-- Derives the cost of `f.csimpImpl` and registers it as the cost `f.timedCost` of `f`; a
refused derivation is reported as information and leaves the environment unchanged. -/
meta def registerCost (f : Name) : CommandElabM Unit := do
  let costName := f ++ `timedCost
  let implName := f ++ `csimpImpl
  let thmName := f.appendAfter "_csimp"
  if (← getEnv).contains costName then
    logInfo m!"derive_csimp {f}: `{costName}` is already registered; it is kept."
    return
  let s₁ ← get
  try
    liftTermElabM (CatCrypt.Tactics.DeriveTimed.deriveCostCore #[] implName)
    let lhs := mkIdent (`_root_ ++ costName)
    let rhs := mkCIdent (implName ++ `timedCost)
    elabCommand (← `(@[expose] noncomputable def $lhs := @$rhs))
    let doc := s!"The cost of `{f}`: the derived cost of `{implName}`, which `{f}` is \
      compiled as by `{thmName}`."
    liftCoreM <| addDocStringCore costName doc
  catch e =>
    set s₁
    logInfo m!"derive_csimp {f}: no cost registered; `derive_cost {implName}` was refused: \
      {e.toMessageData}"

@[command_elab deriveCsimpCmd, inherit_doc deriveCsimpCmd]
meta def elabDeriveCsimp : CommandElab := fun stx => do
  let s₀ ← get
  let f ← try
      liftTermElabM do
        let f ← realizeGlobalConstNoOverloadWithInfo stx[1]
        let stages ← stx[3].getSepArgs.mapM (parseStage f)
        deriveCsimpCore f stages
        return f
    catch e =>
      set s₀
      throw e
  registerCost f

end CatCrypt.Tactics.DeriveCsimp

end
