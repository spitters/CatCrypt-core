/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Party.Derived
public import CatCryptCore.Crypto.Party.Timed
public import CatCryptCore.Crypto.Party.Call
public meta import CatCryptCore.Crypto.Party.Call

/-!
# `party_derive`: the derivation tactic of the party language

`party_derive` proves the side conditions of a concrete party program by structural descent
over the program term: the sampling structure `Prog.Samples p c` used by `Prog.loopMulti_stepEq`,
the port typing `ProgE.Ports Pe Po p` (in particular the absence of receives and sends), the
reflexivity `ProgE.ViewRel V Eq p p` of a program that neither receives nor sends, and the time
bound `ProgE.Bound w p t P` at a bound `t` given in the statement, or, for a goal
`∃ t, ProgE.Bound w p t P`, at a bound it computes from the program.

At each goal the tactic introduces binders, tries the terms it is given, applies the
constructor rule of the head of the program (`Samples.ret/.map/.sample_map/.bind/.sample/.ite`,
`Ports.ret/.fail/.bind/.opN/.send/.recv`, the rules `bound_*` of this file), splits a `match`
or an `if` at the head of the program with `split`, and otherwise unfolds the head constant of
the program (for `Samples`, also the head constant of the sampled computation). The remaining
goals (the predicate of a time bound at a return, a budget inequality, a port predicate) are
closed by `rfl`, `True.intro`, `omega`, or `simp` and `simp_all` with the given terms.

The rule at a goal is chosen by the head constant of its program, read syntactically, so that no
failing rule makes the unifier unfold the program. At a time bound, a subprogram with head
constant `c` (other than the head of the goal's program) is bounded by a hypothesis about it or
by the theorem `c_bound` (`bind_of_bound`, `ProgE.Bound.mono`) when the rest of the descent
succeeds with that bound, and is unfolded otherwise; `party_derive!` always unfolds.

The tests are in `CatCryptCore.Tactics.PartyDeriveTest`.

Search words: party language, derivation tactic, port typing, time bound, sampling structure,
information flow, side conditions of programs.

## Main definitions

* `CatCrypt.Tactics.PartyDerive.partyDerive`, `partyDeriveBang`: the tactics
  `party_derive [t₁, …]` and `party_derive! [t₁, …]`.
* `CatCrypt.Tactics.PartyDerive.estimateBound`: the time bound of a program read off its term.

## Main results

* `CatCrypt.Crypto.Party.PartyDerive.bound_ret`, `bound_send`, `bound_recv`, `bound_opN`,
  `bound_fail`, `bound_sample`: the introduction rules of `ProgE.Bound`.
* `CatCrypt.Crypto.Party.PartyDerive.bind_of_bound`: a time bound of `p.bind f` from one of `p`.
* `CatCrypt.Crypto.Party.PartyDerive.ports_sample`, `sample_bind`: port typing of a sample and
  `bind` after a sample.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Party.PartyDerive

open CatCrypt.Core

variable {Op E O α β γ : Type}

/-- A return meets a time bound when its value satisfies the predicate. -/
theorem bound_ret {w : Op → ℕ} {a : α} {t : ℕ} {P : α → Prop} (h : P a) :
    ProgE.Bound w (.ret a : ProgE Op E O α) t P := h

/-- A send costs one unit. -/
theorem bound_send {w : Op → ℕ} {o : O} {p : ProgE Op E O α} {t : ℕ} {P : α → Prop}
    (ht : 1 ≤ t) (h : ProgE.Bound w p (t - 1) P) : ProgE.Bound w (.send o p) t P := ⟨ht, h⟩

/-- A receive costs one unit. -/
theorem bound_recv {w : Op → ℕ} {k : E → ProgE Op E O α} {t : ℕ} {P : α → Prop}
    (ht : 1 ≤ t) (h : ∀ e, ProgE.Bound w (k e) (t - 1) P) : ProgE.Bound w (.recv k) t P :=
  ⟨ht, h⟩

/-- An operation `q` costs `w q`. -/
theorem bound_opN {w : Op → ℕ} {q : Op} {k : ℕ → ProgE Op E O α} {t : ℕ} {P : α → Prop}
    (ht : w q ≤ t) (h : ∀ n, ProgE.Bound w (k n) (t - w q) P) :
    ProgE.Bound w (.opN q k) t P := ⟨ht, h⟩

/-- Failure meets every time bound. -/
theorem bound_fail {w : Op → ℕ} {t : ℕ} {P : α → Prop} :
    ProgE.Bound w (.fail : ProgE Op E O α) t P := trivial

/-- A sample from a countable type costs the weight of its operation. -/
theorem bound_sample [Countable β] {w : SPComp ℕ → ℕ} {μ : SPComp β} {k : β → Prog E O α}
    {t : ℕ} {P : α → Prop} (h : ∀ q, w q ≤ t ∧ ∀ b, ProgE.Bound w (k b) (t - w q) P) :
    ProgE.Bound w (Prog.sample μ k) t P := by
  unfold Prog.sample
  refine ⟨(h _).1, fun n => ?_⟩
  dsimp only
  split
  · exact (h _).2 _
  · trivial

/-- A time bound of `p` with the predicate `Q` and time bounds of the continuations at the returns
satisfying `Q` give a time bound of `p.bind f`. -/
theorem bind_of_bound {w : Op → ℕ} {p : ProgE Op E O α} {f : α → ProgE Op E O β} {t T : ℕ}
    {Q : α → Prop} {P : β → Prop} (hp : ProgE.Bound w p t Q)
    (hf : ∀ a, Q a → ProgE.Bound w (f a) (T - t) P) (ht : t ≤ T) :
    ProgE.Bound w (p.bind f) T P :=
  (ProgE.Bound.bind (hp.mono le_rfl hf)).mono (by omega) fun _ => id

/-- Port typing of a sample from a countable type. -/
theorem ports_sample [Countable β] {Pe : E → Prop} {Po : O → Prop} {μ : SPComp β}
    {k : β → Prog E O α} (hk : ∀ b, ProgE.Ports Pe Po (k b)) :
    ProgE.Ports Pe Po (Prog.sample μ k) := by
  unfold Prog.sample
  refine ProgE.Ports.opN _ _ fun n => ?_
  split
  · exact hk _
  · exact ProgE.Ports.fail

/-- `bind` after a sample binds in each continuation of the sample. -/
theorem sample_bind [Countable β] (μ : SPComp β) (k : β → Prog E O α) (f : α → Prog E O γ) :
    ProgE.bind (Prog.sample μ k) f = Prog.sample μ fun b => ProgE.bind (k b) f := by
  unfold Prog.sample
  simp only [ProgE.bind]
  congr 1
  funext n
  split <;> rfl

end CatCrypt.Crypto.Party.PartyDerive

end

public meta section

namespace CatCrypt.Tactics.PartyDerive

open Lean Meta Elab Tactic

/-- The kinds of goals `party_derive` descends on. -/
inductive Mode where
  /-- `Prog.Samples p c`. -/
  | samples
  /-- `ProgE.Ports Pe Po p`. -/
  | ports
  /-- `ProgE.ViewRel V RA p p'`. -/
  | viewRel
  /-- `ProgE.Bound w p t P`. -/
  | bound
  /-- `∃ t, ProgE.Bound w p t P`. -/
  | boundEx
  /-- Any other goal. -/
  | leaf
  deriving BEq, Inhabited

/-- The mode of a goal and the program it is about (and, for `Samples`, the computation). -/
def classify (tgt : Expr) : MetaM (Mode × Option Expr × Option Expr) := do
  let tgt ← whnfR (← instantiateMVars tgt)
  let tgt := tgt.consumeMData
  let f := tgt.getAppFn
  let args := tgt.getAppArgs
  if f.isConstOf ``CatCrypt.Crypto.Party.Prog.Samples && args.size == 5 then
    return (.samples, some args[3]!, some args[4]!)
  if f.isConstOf ``CatCrypt.Crypto.Party.ProgE.Ports && args.size == 7 then
    return (.ports, some args[6]!, none)
  if f.isConstOf ``CatCrypt.Crypto.Party.ProgE.ViewRel && args.size == 8 then
    return (.viewRel, some args[6]!, none)
  if f.isConstOf ``CatCrypt.Crypto.Party.ProgE.Bound && args.size == 8 then
    return (.bound, some args[5]!, none)
  if f.isConstOf ``Exists && args.size == 2 then
    if let .lam _ _ body _ := args[1]!.consumeMData then
      let b := body.consumeMData
      if b.getAppFn.isConstOf ``CatCrypt.Crypto.Party.ProgE.Bound && b.getAppNumArgs == 8 then
        return (.boundEx, some b.getAppArgs[5]!, none)
  return (.leaf, none, none)

/-- Constants that `party_derive` never unfolds: the constructors and combinators it has rules
for. -/
def stopConsts : List Name :=
  [``CatCrypt.Crypto.Party.ProgE.ret, ``CatCrypt.Crypto.Party.ProgE.recv,
    ``CatCrypt.Crypto.Party.ProgE.send, ``CatCrypt.Crypto.Party.ProgE.opN,
    ``CatCrypt.Crypto.Party.ProgE.fail, ``CatCrypt.Crypto.Party.ProgE.bind,
    ``CatCrypt.Crypto.Party.Prog.sample, ``CatCrypt.Core.SPComp.bind,
    ``CatCrypt.Core.SPComp.pure, ``CatCrypt.Core.SPComp.map, ``CatCrypt.Core.SPComp.sample,
    ``ite, ``dite]

/-- The head of a program term, through the first argument of `ProgE.bind` and of
`SPComp.bind`. -/
partial def headOf (e : Expr) : Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``CatCrypt.Crypto.Party.ProgE.bind 7 then headOf e.getAppArgs[5]!
  else if e.isAppOfArity ``CatCrypt.Core.SPComp.bind 4 then headOf e.getAppArgs[2]!
  else e.getAppFn

/-- The head of a program is a `match` or an `if`. -/
def headSplits (e : Expr) : MetaM Bool := do
  match headOf e with
  | .const c _ => return c == ``ite || c == ``dite || (← isMatcher c)
  | _ => return false

/-- The head constant of a program when `party_derive` unfolds it. -/
def headUnfold? (e : Expr) : MetaM (Option Name) := do
  match headOf e with
  | .const c _ =>
    if stopConsts.contains c || (← isMatcher c) then return none
    let some info := (← getEnv).find? c | return none
    if info.hasValue then return some c else return none
  | _ => return none

/-- Run a tactic on the main goal; on failure restore the state and return `false`. -/
def tryTac (tac : TSyntax `tactic) : TacticM Bool := do
  let s ← saveState
  let msgs ← Core.getMessageLog
  try
    withoutRecover <| Term.withoutErrToSorry <| evalTactic tac
    let errs (l : MessageLog) := (l.toList.filter (·.severity == .error)).length
    if errs (← Core.getMessageLog) != errs msgs then
      throwError "party_derive: the step logged an error"
    return true
  catch _ =>
    s.restore
    Core.setMessageLog msgs
    return false

/-- Run the first tactic of the list that succeeds. -/
def firstTac (tacs : List (TSyntax `tactic)) : TacticM Bool := do
  for t in tacs do
    if ← tryTac t then return true
  return false

/-- The time bound of a program, read off its term: a return or a failure costs `0`, a send or a
receive one unit, an operation its weight, a `bind` the sum of its parts, a `match` or an `if`
the maximum of its branches; a constant with a body is unfolded. The weight must evaluate to a
numeral. -/
partial def estimateBound (w : Expr) (fuel : Nat) (e : Expr) : MetaM Nat := do
  if fuel == 0 then throwError "party_derive: the bound estimate ran out of fuel"
  let e ← instantiateMVars e
  let e := e.headBeta.consumeMData
  let f := e.getAppFn
  let args := e.getAppArgs
  let go := estimateBound w (fuel - 1)
  let under (k : Expr) : MetaM Nat := do
    let k ← whnfR k
    match k with
    | .lam n ty _ _ => withLocalDeclD n ty fun x => go (k.beta #[x])
    | _ => do
      let ty ← inferType k
      match (← whnf ty) with
      | .forallE n d _ _ => withLocalDeclD n d fun x => go (mkApp k x)
      | _ => throwError "party_derive: not a continuation {k}"
  let weight (q : Expr) : MetaM Nat := do
    let v ← whnf (mkApp w q)
    match v.rawNatLit? with
    | some n => return n
    | none =>
      match (← evalNat v) with
      | some n => return n
      | none => throwError "party_derive: the weight {v} is not a numeral"
  match f with
  | .const c _ =>
    if c == ``CatCrypt.Crypto.Party.ProgE.ret || c == ``CatCrypt.Crypto.Party.ProgE.fail then
      return 0
    if c == ``CatCrypt.Crypto.Party.ProgE.send && args.size == 6 then
      return 1 + (← go args[5]!)
    if c == ``CatCrypt.Crypto.Party.ProgE.recv && args.size == 5 then
      return 1 + (← under args[4]!)
    if c == ``CatCrypt.Crypto.Party.ProgE.opN && args.size == 6 then
      return (← weight args[4]!) + (← under args[5]!)
    if c == ``CatCrypt.Crypto.Party.ProgE.bind && args.size == 7 then
      return (← go args[5]!) + (← under args[6]!)
    if c == ``CatCrypt.Crypto.Party.Prog.sample && args.size == 7 then
      let ty ← inferType w
      let .forallE n d _ _ ← whnf ty | throwError "party_derive: weight {w}"
      let wq ← withLocalDeclD n d fun q => weight q
      return wq + (← under args[6]!)
    if c == ``ite && args.size == 5 then
      return max (← go args[3]!) (← go args[4]!)
    if c == ``dite && args.size == 5 then
      return max (← under args[3]!) (← under args[4]!)
    if let some m ← matchMatcherApp? e then
      let mut acc := 0
      for alt in m.alts, n in m.altNumParams do
        let v ← lambdaBoundedTelescope alt n fun _ b => go b
        acc := max acc v
      return acc
    match ← unfoldDefinition? e with
    | some e' => go e'
    | none => throwError "party_derive: no bound for {e}"
  | _ => throwError "party_derive: no bound for {e}"

open CatCrypt.Crypto.Party in
/-- The head constant of a term, or the anonymous name. -/
def headName (e : Expr) : Name :=
  match e.consumeMData.getAppFn.consumeMData with
  | .const c _ => c
  | _ => .anonymous

open CatCrypt.Crypto.Party in
/-- The heads of a first argument of `ProgE.bind` that `party_derive` pushes `bind` into. -/
def bindNormal : List Name :=
  [``ProgE.ret, ``ProgE.recv, ``ProgE.send, ``ProgE.opN, ``ProgE.fail, ``ProgE.bind,
    ``Prog.sample]

open CatCrypt.Crypto.Party in
/-- One step of `party_derive` on the main goal, with the given terms. Returns `false` when no
rule applies. -/
def step (ts : Array Term) : TacticM Bool := do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  if tgt.consumeMData.isForall then
    evalTactic (← `(tactic| intro _))
    return true
  let (mode, prog?, comp?) ← classify tgt
  for t in ts do
    if ← tryTac (← `(tactic| with_reducible exact $t)) then return true
  match mode with
  | .leaf => return false
  | .boundEx =>
    let tgt' ← whnfR tgt
    let .lam _ _ body _ := tgt'.getAppArgs[1]!.consumeMData | return false
    let w := body.getAppArgs[4]!
    if w.hasLooseBVars then return false
    let n ← estimateBound w 10000 prog?.get!
    let lit := Syntax.mkNumLit (toString n)
    evalTactic (← `(tactic| refine ⟨$lit, ?_⟩))
    return true
  | _ => pure ()
  let prog := (← instantiateMVars prog?.get!).consumeMData
  if prog.getAppFn.consumeMData.isLambda then
    if ← tryTac (← `(tactic| dsimp only)) then return true
  let h := headName prog
  if mode == .samples then
    let comp := (← instantiateMVars comp?.get!).consumeMData
    if (← headSplits comp) && (!(← headSplits prog) || (← isMatcher (headName comp))) then
      if ← tryTac (← `(tactic| simp only [*])) then return true
  let rules : List (TSyntax `tactic) ← match mode with
    | .samples =>
      if h == ``ProgE.ret then
        pure [← `(tactic| exact CatCrypt.Crypto.Party.Prog.Samples.ret _)]
      else if h == ``ProgE.bind then
        pure [← `(tactic| apply CatCrypt.Crypto.Party.Prog.Samples.map),
          ← `(tactic| apply CatCrypt.Crypto.Party.Prog.Samples.bind)]
      else if h == ``Prog.sample then
        pure [← `(tactic| apply CatCrypt.Crypto.Party.Prog.Samples.sample_map),
          ← `(tactic| apply CatCrypt.Crypto.Party.Prog.Samples.sample)]
      else if h == ``ite then
        pure [← `(tactic| apply CatCrypt.Crypto.Party.Prog.Samples.ite)]
      else pure []
    | .ports =>
      if h == ``ProgE.ret then pure [← `(tactic| exact CatCrypt.Crypto.Party.ProgE.Ports.ret _)]
      else if h == ``ProgE.fail then
        pure [← `(tactic| exact CatCrypt.Crypto.Party.ProgE.Ports.fail)]
      else if h == ``ProgE.bind then
        pure [← `(tactic| apply CatCrypt.Crypto.Party.ProgE.Ports.bind)]
      else if h == ``Prog.sample then
        pure [← `(tactic| apply CatCrypt.Crypto.Party.PartyDerive.ports_sample)]
      else if h == ``ProgE.opN then
        pure [← `(tactic| apply CatCrypt.Crypto.Party.ProgE.Ports.opN)]
      else if h == ``ProgE.send then
        pure [← `(tactic| apply CatCrypt.Crypto.Party.ProgE.Ports.send)]
      else if h == ``ProgE.recv then
        pure [← `(tactic| apply CatCrypt.Crypto.Party.ProgE.Ports.recv)]
      else pure []
    | .viewRel => pure [← `(tactic|
        refine CatCrypt.Crypto.Party.ProgE.ViewRel.refl_of_ports (fun _ => rfl) ?_)]
    | _ =>
      if h == ``ProgE.fail then
        pure [← `(tactic| exact CatCrypt.Crypto.Party.PartyDerive.bound_fail)]
      else if h == ``ProgE.ret then
        pure [← `(tactic| refine CatCrypt.Crypto.Party.PartyDerive.bound_ret ?_)]
      else if h == ``ProgE.send then
        pure [← `(tactic| refine CatCrypt.Crypto.Party.PartyDerive.bound_send ?_ ?_)]
      else if h == ``ProgE.recv then
        pure [← `(tactic| refine CatCrypt.Crypto.Party.PartyDerive.bound_recv ?_ ?_)]
      else if h == ``ProgE.opN then
        pure [← `(tactic| refine CatCrypt.Crypto.Party.PartyDerive.bound_opN ?_ ?_)]
      else if h == ``Prog.sample then
        pure [← `(tactic|
          refine CatCrypt.Crypto.Party.PartyDerive.bound_sample fun _ => ⟨?_, ?_⟩)]
      else if h == ``ProgE.bind && bindNormal.contains (headName prog.getAppArgs[5]!) then
        pure [← `(tactic| simp only [CatCrypt.Crypto.Party.ProgE.bind,
          CatCrypt.Crypto.Party.ProgE.bind_assoc, CatCrypt.Crypto.Party.PartyDerive.sample_bind])]
      else pure []
  if ← firstTac rules then return true
  if ← headSplits prog then
    if ← tryTac (← `(tactic| split)) then return true
  if let some c ← headUnfold? prog then
    let mut names := #[mkIdent c]
    if mode == .samples then
      if let some d ← headUnfold? comp?.get! then
        if d != c then names := names.push (mkIdent d)
    if ← tryTac (← `(tactic| unfold $names*)) then return true
  return false

/-- The closing tactics at a goal that is not about a program. -/
def closeLeaf (ts : Array Term) : TacticM Bool := do
  let ls : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    ts.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
  firstTac [← `(tactic| with_reducible rfl), ← `(tactic| exact True.intro), ← `(tactic| omega),
    ← `(tactic| (simp [$ls,*]; done)), ← `(tactic| (simp [$ls,*]; omega)),
    ← `(tactic| (simp_all [$ls,*]; done)), ← `(tactic| (simp_all [$ls,*]; omega))]

open CatCrypt.Crypto.Party in
/-- The time bounds of a subprogram with head constant `c`, as terms: the hypotheses about a
program with head `c`, and the theorem `c_bound` when `c` is not `root`. -/
def boundLemmas (root c : Name) : TacticM (Array Term) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty := (← instantiateMVars d.type).consumeMData
    if ty.getAppFn.isConstOf ``ProgE.Bound && ty.getAppNumArgs == 8 &&
        headName ty.getAppArgs[5]! == c then
      out := out.push (← Term.exprToSyntax d.toExpr)
  if c != root then
    if let .str p s := c then
      let n := Name.str p (s ++ "_bound")
      if (← getEnv).contains n then out := out.push (← `($(mkIdent n) ..))
  return out

open CatCrypt.Crypto.Party in
/-- The steps at a time-bound goal that use a time bound of a subprogram (`boundLemmas`): at
`ProgE.bind p f` the rule `bind_of_bound` with a bound of `p`, at any other program `Bound.mono`
with a bound of the program. -/
def lemmaSteps (root : Name) : TacticM (Array (TSyntax `tactic)) := withMainContext do
  let (mode, prog?, _) ← classify (← getMainTarget)
  unless mode == .bound do return #[]
  let prog := (← instantiateMVars prog?.get!).consumeMData
  if prog.isAppOfArity ``ProgE.bind 7 then
    let c := headName prog.getAppArgs[5]!
    if c.isAnonymous || stopConsts.contains c then return #[]
    (← boundLemmas root c).mapM fun l =>
      `(tactic| refine CatCrypt.Crypto.Party.PartyDerive.bind_of_bound $l ?_ ?_)
  else
    let c := headName prog
    if c.isAnonymous || stopConsts.contains c then return #[]
    (← boundLemmas root c).mapM fun l =>
      `(tactic| refine CatCrypt.Crypto.Party.ProgE.Bound.mono $l ?_ ?_)

/-- Descend on every goal: a step with a time bound of a subprogram when one is found
(`useLemmas`) and the rest of the descent succeeds, otherwise a step where a rule applies, and a
closing tactic where none does. -/
partial def descend (ts : Array Term) (useLemmas : Bool) (root : Name) (fuel : Nat) :
    TacticM Unit := do
  if fuel == 0 then throwError "party_derive: out of fuel"
  for g in ← getUnsolvedGoals do
    if ← g.isAssigned then continue
    setGoals [g]
    if useLemmas then
      let mut done := false
      for tac in ← lemmaSteps root do
        let s ← saveState
        try
          withoutRecover <| Term.withoutErrToSorry <| evalTactic tac
          descend ts useLemmas root (fuel - 1)
          done := true
          break
        catch _ =>
          s.restore
          setGoals [g]
      if done then continue
    if ← step ts then
      descend ts useLemmas root (fuel - 1)
    else
      let ok ← closeLeaf ts
      let rest ← getUnsolvedGoals
      if !ok || !rest.isEmpty then
        throwError "party_derive: no rule closes the goal{indentD (MessageData.ofGoal g)}"

/-- `party_derive [t₁, …]` proves `Prog.Samples p c`, `ProgE.Ports Pe Po p`, `ProgE.ViewRel V Eq
p p` for a program `p` that neither receives nor sends, `ProgE.Bound w p t P`, and
`∃ t, ProgE.Bound w p t P` with a bound computed from `p`, by structural descent over the
program term. The terms `tᵢ` close subgoals (lemmas about subprograms) and are passed to
`simp_all` at the remaining goals (definitions to unfold in the predicate of a bound). At a time
bound of `ProgE.bind p f`, or of a program `p`, whose head constant `c` is not the head of the
goal's program, a hypothesis bounding a program with head `c` or the theorem `c_bound` is used
in place of unfolding `c` when the rest of the descent succeeds with it. -/
syntax (name := partyDerive) "party_derive" (" [" term,* "]")? : tactic

/-- `party_derive! [t₁, …]` is `party_derive [t₁, …]` without the time bounds of subprograms:
every subprogram is unfolded. -/
syntax (name := partyDeriveBang) "party_derive!" (" [" term,* "]")? : tactic

/-- Run the descent of `party_derive` on the main goal. -/
def runPartyDerive (stx : Syntax) (useLemmas : Bool) : TacticM Unit := do
  let ts : Array Term :=
    if stx[1].getNumArgs == 3 then stx[1][1].getSepArgs.map (⟨·⟩) else #[]
  let gs ← getGoals
  match gs with
  | [] => throwError "party_derive: no goals"
  | g :: rest =>
    setGoals [g]
    let (_, prog?, _) ← g.withContext do classify (← g.getType)
    let root := match prog? with
      | some p => headName p
      | none => .anonymous
    g.withContext <| descend ts useLemmas root 1000
    setGoals rest

@[tactic partyDerive, inherit_doc partyDerive]
def evalPartyDerive : Tactic := fun stx => runPartyDerive stx true

@[tactic partyDeriveBang, inherit_doc partyDeriveBang]
def evalPartyDeriveBang : Tactic := fun stx => runPartyDerive stx false

end CatCrypt.Tactics.PartyDerive

end
