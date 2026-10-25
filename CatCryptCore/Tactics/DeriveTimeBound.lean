/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoTime

/-!
# The time theorem of a costed computation tree

`derive_time_bound R.tree` states and proves the time theorem `R.tree.timeBound_timed` of the
costed tree `R.tree.timed` that `derive_timed` (or `derive_reduction R`) defined:

* every binder `A : X₁ → … → SPTree.Timed β` (an adversary or a sub-computation in tree
  form) gets a bound `T_A` and the hypothesis `∀ x, (A x).time ≤ T_A`;
* every binder `k : SPTree.Timed β` (a key generation) gets a bound `G_k` and the hypothesis
  `k.time ≤ G_k`;
* every cost companion `fCost : X₁ → … → ℕ` gets its own bound `t_fCost` and the hypothesis
  `∀ x, fCost x ≤ t_fCost`;
* the bound of the theorem is the cost of the tree with every atom replaced by its bound:
  the step costs and node units along the tree, a bind charged with the bound of its first
  tree plus the bound of its continuation, a branch `if` charged with the maximum of its
  branches, normalised to a sum of atoms with natural coefficients.

A bound that mentions a value bound inside the tree (a sampled value, a value read from the
heap, the result of a bind, a matched value) is admitted when the value occurs only inside
registered costs `f.timedCost a` whose closed form does not mention it: each such cost is
replaced by the right side of `f.timedCost_eq` at `a`, or by the bound of `f.timedCost_le` at
`a` (premises closed from the hypotheses of the theorem), whichever exists and is free of the
value (`rewriteCosts`). Since every operation of a bound is monotone, the replaced bound bounds
the original one, and `time_bound` uses the same lemmas at its arithmetic leaves.

A `match` in a step cost whose alternatives have bounds that mention their pattern variables
is bounded by the same `match` on the same discriminants, each alternative replaced by its
bound (`matchBound`). When no bound of an alternative mentions its pattern variables, the
bound of the `match` is the maximum of the bounds of its alternatives. The bound of a match by
cases is monotone in each alternative, and `time_bound` proves it by splitting the arithmetic
leaf on the discriminants of the match.

The theorem is proved by `time_bound`, under its own heartbeat budget (`proofHeartbeats`).
When the bound cannot be computed (a cost that depends on a bound value through a term other
than a companion with such a closed form, a recursive definition) or `time_bound` does not
close the goal, nothing is
declared and the command fails with the reason. The command is written once per reduction,
in place of a hand-stated theorem of the same name.

## Main definitions

* `rewriteCosts` — the registered costs that mention a bound value, replaced by closed forms
* `matchBound` — the bound of a `match` by cases
* `emitTimeBound` — the procedure; it returns the reason when the theorem is not proved
* `derive_time_bound R.tree` — the command
-/

public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimeBound

open Lean Meta Elab Term Command CatCrypt.Core

meta section

/-- The role of a binder of a costed tree in its time theorem. -/
inductive Role where
  /-- A function into costed trees: its time is bounded pointwise. -/
  | tree
  /-- A costed tree: its time is bounded. -/
  | key
  /-- A cost companion: bounded pointwise. -/
  | cost

/-- The role of a binder of type `t`. -/
def roleOf (t : Expr) : MetaM (Option Role) := do
  forallTelescopeReducing t fun ys b => do
    let b ← whnfR b
    if b.isAppOf ``SPTree.Timed then
      return some (if ys.isEmpty then .key else .tree)
    if b.isConstOf ``Nat && !ys.isEmpty then return some .cost
    return none

/-- The bounds: each bounded binder with its bound variable and role. -/
abbrev Bounds := Array (FVarId × Expr × Role)

/-- `ℕ`. -/
def natE : Expr := Lean.mkConst ``Nat

/-- `a + b` over `ℕ`. -/
def mkAddN (a b : Expr) : Expr :=
  mkApp6 (Lean.mkConst ``HAdd.hAdd [0, 0, 0]) natE natE natE
    (mkApp2 (Lean.mkConst ``instHAdd [0]) natE (Lean.mkConst ``instAddNat)) a b

/-- `a * b` over `ℕ`. -/
def mkMulN (a b : Expr) : Expr :=
  mkApp6 (Lean.mkConst ``HMul.hMul [0, 0, 0]) natE natE natE
    (mkApp2 (Lean.mkConst ``instHMul [0]) natE (Lean.mkConst ``instMulNat)) a b

/-- `max a b` over `ℕ`. -/
def mkMaxN (a b : Expr) : MetaM Expr := mkAppM ``Max.max #[a, b]

/-- The closed form of the registered cost `s = f.timedCost a` that does not mention `b`: the
right side of `f.timedCost_eq` at `a`, or the bound of `f.timedCost_le` at `a`, with the
propositional premises closed from the context by `closeByContext`. -/
def costClosedForm? (b : FVarId) (s : Expr) : MetaM (Option Expr) := do
  let some n := s.getAppFn.constName? | return none
  for c in ← CatCrypt.Tactics.AutoTime.costLemmas n do
    let st ← saveState
    let (ms, _, body) ← forallMetaTelescopeReducing (← inferType c)
    let side? := if body.isAppOfArity ``Eq 3 then some (body.getArg! 1, body.getArg! 2)
      else CatCrypt.Tactics.AutoTime.natLe? body
    let some (l, r) := side? | st.restore; continue
    if ← isDefEq l s then
      let ok ← ms.allM fun m => do
        let mid := m.mvarId!
        if ← mid.isAssigned then return true
        unless ← isProp (← mid.getType) do return true
        CatCrypt.Tactics.AutoTime.closeByContext mid
      let r ← instantiateMVars r
      if ok && !r.hasExprMVar && !r.containsFVar b then return some r
    st.restore
  return none

/-- `e` with every registered cost `f.timedCost a` that mentions `b` replaced by its closed
form free of `b` (`costClosedForm?`), where one exists. -/
def rewriteCosts (b : FVarId) (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun s => do
    unless s.containsFVar b do return .done s
    let some n := s.getAppFn.constName? | return .continue
    unless n.lastComponentAsString == "timedCost" do return .continue
    match ← costClosedForm? b s with
    | some r => return .done r
    | none => return .continue)

/-- The fresh variable `b : γ` in `k`, which must not occur in the result after the registered
costs that mention it are replaced by their closed forms (`rewriteCosts`). -/
def withFresh (γ : Expr) (k : Expr → MetaM Expr) : MetaM Expr :=
  withLocalDeclD `b γ fun b => do
    let r ← k b
    let r ← instantiateMVars r
    let r ← if r.containsFVar b.fvarId! then rewriteCosts b.fvarId! r else pure r
    if r.containsFVar b.fvarId! then
      throwError "the bound depends on a bound value{indentExpr r}"
    return r

/-- The head-reduced form of a tree or pair: `whnfR`, then the unfolding of a non-recursive
head definition, at most eight times. -/
def reduceHead (e : Expr) : MetaM Expr := do
  let mut e ← CatCrypt.Tactics.AutoTime.whnfC e
  for _ in [0:8] do
    match ← CatCrypt.Tactics.AutoTime.unfoldTree? e with
    | some e' => e := e'
    | none => break
  return e

/-- The `match` `m` with result type `ℕ` and the alternatives `alts` (each a function of the
pattern variables of its alternative), on the discriminants of `m`. `none` when `m` has
arguments after its alternatives or its motive has no universe parameter. -/
def matchBound (m : MatcherApp) (alts : Array Expr) : MetaM (Option Expr) := do
  unless m.remaining.isEmpty do return none
  let some pos := m.uElimPos? | return none
  let motive ← forallBoundedTelescope (← inferType m.motive) m.discrs.size fun xs _ =>
    mkLambdaFVars xs natE
  let r := { m with matcherLevels := m.matcherLevels.set! pos Level.one, motive, alts }.toExpr
  try
    check r
    return some r
  catch _ => return none

mutual

/-- The bound of a step cost `e : ℕ`. -/
partial def boundCost (bs : Bounds) (e : Expr) : MetaM Expr := do
  let e := e.headBeta
  match e with
  | .letE _ _ v b _ => boundCost bs (b.instantiate1 v)
  | .mdata _ b => boundCost bs b
  | _ =>
  if e.isAppOfArity ``HAdd.hAdd 6 then
    return mkAddN (← boundCost bs (e.getArg! 4)) (← boundCost bs (e.getArg! 5))
  if e.isAppOfArity ``HMul.hMul 6 then
    return mkMulN (← boundCost bs (e.getArg! 4)) (← boundCost bs (e.getArg! 5))
  if e.isAppOfArity ``Max.max 4 then
    return ← mkMaxN (← boundCost bs (e.getArg! 2)) (← boundCost bs (e.getArg! 3))
  if e.isAppOfArity ``ite 5 then
    return ← mkMaxN (← boundCost bs (e.getArg! 3)) (← boundCost bs (e.getArg! 4))
  if let some y := CatCrypt.Tactics.AutoTime.fstOf? e then
    -- the step cost of a pair is at most its time
    return ← boundStep bs y
  if let .fvar f := e.getAppFn then
    if let some (_, v, .cost) := bs.find? (·.1 == f) then return v
  -- a `match` in a cost: the maximum of the bounds of its alternatives, or, when a bound
  -- mentions a pattern variable, the `match` of the bounds of its alternatives
  if let some m ← matchMatcherApp? e then
    let mut acc : Option Expr := none
    let mut lams : Array Expr := #[]
    let mut dep := false
    for alt in m.alts, n in m.altNumParams do
      let (b, lam, d) ← lambdaBoundedTelescope alt n fun ys body => do
        let r ← instantiateMVars (← boundCost bs body)
        let r ← ys.foldlM (init := r) fun r y => rewriteCosts y.fvarId! r
        let d := ys.any fun y => r.containsFVar y.fvarId!
        return (r, ← mkLambdaFVars ys r, d)
      lams := lams.push lam
      dep := dep || d
      unless d do
        acc ← match acc with
          | none => pure (some b)
          | some a => if a == b then pure (some a) else some <$> mkMaxN a b
    if dep then
      match ← matchBound m lams with
      | some r => return r
      | none => throwError "the bound depends on a matched value{indentExpr e}"
    if let some r := acc then return r
  if let some _ := e.nat? then return e
  if e.isRawNatLit then return e
  return e

/-- The bound of `stepTime x` for a pair `x : ℕ × SPTree.Timed α`. -/
partial def boundStep (bs : Bounds) (x : Expr) : MetaM Expr := do
  let x ← reduceHead x
  if x.isAppOfArity ``Prod.mk 4 then
    let e := x.getArg! 2
    let t := x.getArg! 3
    -- `(c + y.1, y.2)`: the pair `y` after `c`
    if let some y := CatCrypt.Tactics.AutoTime.sndOf? t then
      let fsts := (CatCrypt.Tactics.AutoTime.appsOf e #[]).filter fun o =>
        match CatCrypt.Tactics.AutoTime.fstOf? o with
        | some y' => y' == y
        | none => false
      if let some o := fsts[0]? then
        let c := e.replace fun s => if s == o then some (mkNatLit 0) else none
        return mkAddN (← boundCost bs c) (← boundStep bs y)
    return mkAddN (← boundCost bs e) (← boundTree bs t)
  if x.isAppOfArity ``SPTree.Timed.delay 3 then
    return mkAddN (← boundCost bs (x.getArg! 1)) (← boundStep bs (x.getArg! 2))
  if x.isAppOfArity ``SPTree.Timed.map 5 then
    let a := x.getArg! 4
    let fc := x.getArg! 3
    let α := x.getArg! 0
    return mkAddN (← boundTree bs a) (← withFresh α fun v => boundCost bs (fc.beta #[v]))
  if x.isAppOfArity ``SPTree.Timed.bind 4 then
    let a := x.getArg! 2
    let f := x.getArg! 3
    let α := x.getArg! 0
    return mkAddN (← boundTree bs a) (← withFresh α fun v => boundStep bs (f.beta #[v]))
  if x.isAppOfArity ``ite 5 then
    return ← mkMaxN (← boundStep bs (x.getArg! 3)) (← boundStep bs (x.getArg! 4))
  if x.isAppOfArity ``dite 5 then
    let c := x.getArg! 1
    let l ← withFresh c fun h => boundStep bs ((x.getArg! 3).beta #[h])
    let r ← withFresh (mkNot c) fun h => boundStep bs ((x.getArg! 4).beta #[h])
    return ← mkMaxN l r
  throwError "no bound for the pair{indentExpr x}"

/-- The bound of `t.time` for a tree `t : SPTree.Timed α`. -/
partial def boundTree (bs : Bounds) (t : Expr) : MetaM Expr := do
  if let .fvar f := t.getAppFn then
    if let some (_, v, r) := bs.find? (·.1 == f) then
      match r with
      | .tree | .key => return v
      | .cost => pure ()
  let t ← reduceHead t
  if let .fvar f := t.getAppFn then
    if let some (_, v, r) := bs.find? (·.1 == f) then
      match r with
      | .tree | .key => return v
      | .cost => pure ()
  if t.isAppOf ``SPTree.Timed.ret then return mkNatLit 0
  if t.isAppOf ``SPTree.Timed.fail then return mkNatLit 0
  if t.isAppOfArity ``SPTree.Timed.sample 6 then
    let γ := t.getArg! 1
    let c := t.getArg! 4
    let k := t.getArg! 5
    let b ← withFresh γ fun v => do
      return mkAddN (← boundCost bs (c.beta #[v])) (← boundTree bs (k.beta #[v]))
    return mkAddN (mkNatLit 1) b
  if t.isAppOfArity ``SPTree.Timed.get 4 then
    let l := t.getArg! 1
    let c := t.getArg! 2
    let k := t.getArg! 3
    let b ← withFresh (mkApp (Lean.mkConst ``Location.ty) l) fun v => do
      return mkAddN (← boundCost bs (c.beta #[v])) (← boundTree bs (k.beta #[v]))
    return mkAddN (mkNatLit 1) b
  if t.isAppOfArity ``SPTree.Timed.set 5 then
    return mkAddN (mkNatLit 1)
      (mkAddN (← boundCost bs (t.getArg! 3)) (← boundTree bs (t.getArg! 4)))
  if let some y := CatCrypt.Tactics.AutoTime.sndOf? t then
    return ← boundStep bs y
  if t.isAppOfArity ``ite 5 then
    return ← mkMaxN (← boundTree bs (t.getArg! 3)) (← boundTree bs (t.getArg! 4))
  throwError "no bound for the tree{indentExpr t}"

end

/-- The summands of a sum over `ℕ`, a numeral contributing its value. -/
partial def summands (e : Expr) : Array Expr × Nat :=
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let (a, m) := summands (e.getArg! 4)
    let (b, n) := summands (e.getArg! 5)
    (a ++ b, m + n)
  else match e.nat? with
    | some n => (#[], n)
    | none => match e.rawNatLit? with
      | some n => (#[], n)
      | none => (#[e], 0)

/-- The sum `e` normalised: equal summands collected with a coefficient, numerals summed last,
operands of `max` and products normalised. -/
partial def normalizeSum (e : Expr) : MetaM Expr := do
  let (ts, k) := summands e
  let ts ← ts.mapM fun t => do
    if t.isAppOfArity ``Max.max 4 then
      mkMaxN (← normalizeSum (t.getArg! 2)) (← normalizeSum (t.getArg! 3))
    else if t.isAppOfArity ``HMul.hMul 6 then
      return mkMulN (← normalizeSum (t.getArg! 4)) (← normalizeSum (t.getArg! 5))
    else return t
  let groups : Array (Expr × Nat) := ts.foldl (init := #[]) fun acc t =>
    match acc.findIdx? (·.1 == t) with
    | some i => acc.modify i fun (u, n) => (u, n + 1)
    | none => acc.push (t, 1)
  let terms := groups.map fun (t, n) => if n == 1 then t else mkMulN (mkNatLit n) t
  let body := terms.foldl (init := none) fun acc t =>
    match acc with
    | none => some t
    | some s => some (mkAddN s t)
  return match body with
    | none => mkNatLit k
    | some s => if k == 0 then s else mkAddN s (mkNatLit k)

/-- The bound variables and hypotheses of the bounded binders `xs`, in order, passed to `k`
with the bounds. -/
partial def withBounds {γ : Type} (xs : Array Expr) (i : Nat) (bs : Bounds)
    (vars hyps : Array Expr) (k : Bounds → Array Expr → Array Expr → TermElabM γ) :
    TermElabM γ := do
  if h : i < xs.size then
    let x := xs[i]
    let t ← inferType x
    match ← roleOf t with
    | none => withBounds xs (i + 1) bs vars hyps k
    | some r =>
      let n := (← x.fvarId!.getUserName).eraseMacroScopes
      let vName := match r with
        | .tree => Name.mkSimple ("T_" ++ n.toString)
        | .key => Name.mkSimple ("G_" ++ n.toString)
        | .cost => Name.mkSimple ("t_" ++ n.toString)
      withLocalDecl vName .implicit natE fun v => do
        let hTy ← forallTelescopeReducing t fun ys _ => do
          let lhs ← match r with
            | .cost => pure (mkAppN x ys)
            | _ => mkAppM ``SPTree.Timed.time #[mkAppN x ys]
          mkForallFVars ys (← mkAppM ``LE.le #[lhs, v])
        withLocalDeclD (Name.mkSimple ("h_" ++ n.toString)) hTy fun hx =>
          withBounds xs (i + 1) (bs.push (x.fvarId!, v, r)) (vars.push v) (hyps.push hx) k
  else k bs vars hyps

/-- The heartbeat budget, in thousands, of the proof of one time theorem by `time_bound`. -/
def proofHeartbeats : Nat := 400000

/-- State and prove `name`: the time theorem of the costed tree `c` (a definition returning
`ℕ × SPTree.Timed α`). Returns `none` with the reason when the bound is not computed or
`time_bound` does not prove it. -/
def emitTimeBound (c name : Name) : TermElabM (Option MessageData) := do
  let info ← getConstInfo c
  let lvls := info.levelParams.map mkLevelParam
  forallTelescope info.type fun xs body => do
    unless (← whnfR body).isAppOfArity ``Prod 2 do
      return some m!"`{c}` is not a step-prefixed tree"
    withBounds xs 0 #[] #[] #[] fun bs vars hyps => do
      let x := mkAppN (Lean.mkConst c lvls) xs
      let bound ← try
          normalizeSum (← instantiateMVars (← boundStep bs x))
        catch e => return some m!"no bound: {e.toMessageData}"
      let goal ← mkAppM ``LE.le #[← mkAppM ``SPTree.Timed.stepTime #[x], bound]
      let mv ← mkFreshExprSyntheticOpaqueMVar goal
      let s ← saveState
      let tac ← `(tactic| time_bound)
      let cap (c : Core.Context) : Core.Context :=
        { c with maxHeartbeats := proofHeartbeats * 1000 }
      let r ← tryCatchRuntimeEx
        (withCurrHeartbeats <| withTheReader Core.Context cap do
          let gs ← Tactic.run mv.mvarId! (Tactic.evalTactic tac)
          return if gs.isEmpty then none else some m!"`time_bound` left goals")
        fun e => do
          if e.isInterrupt then throw e
          return some m!"`time_bound` failed: {e.toMessageData}"
      if let some why := r then
        s.restore
        return some why
      let pf ← instantiateMVars mv
      if pf.hasSorry || pf.hasExprMVar then return some m!"the proof is incomplete"
      let ty ← mkForallFVars (xs ++ vars ++ hyps) goal
      let val ← mkLambdaFVars (xs ++ vars ++ hyps) pf
      addDecl (Declaration.thmDecl
        { name, levelParams := info.levelParams, type := ty, value := val })
      return none

/-- `derive_time_bound R.tree` states and proves `R.tree.timeBound_timed`, the time theorem of
`R.tree.timed` (see the module docstring), and fails with the reason when it is not proved. -/
syntax (name := deriveTimeBoundCmd) "derive_time_bound " ident : command

@[command_elab deriveTimeBoundCmd]
def elabDeriveTimeBound : CommandElab := fun stx => do
  liftTermElabM do
    let t ← realizeGlobalConstNoOverloadWithInfo stx[1]
    let name := t ++ `timeBound_timed
    if let some why ← emitTimeBound (t ++ `timed) name then
      throwError "`{name}` is not proved: {why}"

end

end CatCrypt.Tactics.DeriveTimeBound
