/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Core.Code
public meta import CatCryptCore.Core.Code

/-!
# Commutation of independent `IsPure` binds in `SPComp` equalities

`bind_swap_nf` proves an equality of two `SPComp` bind chains that are equal up to the
order of independent bindings, where each exchanged pair contains an `IsPure`
computation (a computation that neither reads nor writes the heap, such as a uniform
sample or a key generation), as the `swap` tactic of EasyCrypt does for program
statements: `SPComp.isPure_bind_comm_left` and
`SPComp.isPure_bind_comm_right` state that an `IsPure` computation commutes with any
computation it does not depend on.

## Procedure

1. Normalisation: `simp only [SPComp.monad_bind_eq, SPComp.monad_pure_eq,
   SPComp.bind_assoc, SPComp.pure_bind]` brings both sides to right-nested chains
   `SPComp.bind c₁ (fun x₁ => SPComp.bind c₂ (fun x₂ => … k))`.
2. Pairing hint: the final terms of the two chains are traversed together, and the
   binding of the left chain whose variable occurs where the right final term has the
   variable of a right binding is paired with that binding (`varHint`).
3. Alignment: when the two sides are not equal (definitional equality at reducible and
   instance transparency), the first computation `p` of the left chain is searched in
   the right chain: a binding whose computation is equal to `p` and mentions no variable
   bound before it is moved to the front by exchanges with the bindings before it. Each
   exchange uses `SPComp.isPure_bind_comm_right` when the moved computation is `IsPure`,
   and `SPComp.isPure_bind_comm_left` when the computation it passes is. The binding
   paired by the hint is tried first, then the other occurrences of `p` (those that the
   hint pairs with no other binding first), with backtracking when the alignment under
   the binder fails; when none succeeds, the first computation of the right chain is
   searched in the left chain in the same way. The common first binding is removed by
   `congrArg (SPComp.bind p)` and `funext`, and the alignment continues under the binder.
   The number of alignment steps over all branches is bounded by `maxSteps`.
4. The leaves are closed by definitional equality at reducible and instance transparency.

The `IsPure` side conditions are proved from the combinators of `pure`, `sample`, `fail`
and `SPComp.bind`, from the `IsPure` hypotheses of the local context (possibly
universally quantified), from the `Prop`-valued fields of structure-typed hypotheses up
to depth two (`deps.keygen_isPure` for `deps : Deps`), and from the terms given as
arguments: `bind_swap_nf [h₁, …]`.

Two chains are equal up to such exchanges exactly when they denote the same trace of the
partially commutative word whose letters are the bindings; moving an occurrence of the
left head to the front of the right chain, with backtracking over repeated letters, decides
equality of traces; the step bound makes the procedure fail on goals whose search exceeds
it. The procedure does not reorder two bindings neither of which is `IsPure`, and does not
remove an unused binding.
-/

@[expose] public section

namespace CatCrypt.Core.SPComp

variable {α β γ : Type*}

/-- An `IsPure` computation bound second commutes with any computation bound first that
it does not depend on: `c₁ >>= fun a => c₂ >>= fun b => k a b` equals
`c₂ >>= fun b => c₁ >>= fun a => k a b` when `c₂` is `IsPure`. -/
theorem isPure_bind_comm_right (c₁ : SPComp α) (c₂ : SPComp β)
    (k : α → β → SPComp γ) (hc₂ : IsPure c₂) :
    SPComp.bind c₁ (fun a => SPComp.bind c₂ (fun b => k a b)) =
    SPComp.bind c₂ (fun b => SPComp.bind c₁ (fun a => k a b)) :=
  (isPure_bind_comm_left c₂ c₁ (fun b a => k a b) hc₂).symm

end CatCrypt.Core.SPComp

end

public meta section

namespace CatCrypt.Tactic.BindSwap

open Lean Meta Elab Tactic

/-- The parts `(α, β, c, f)` of `@SPComp.bind α β c f`. -/
def bindApp? (e : Expr) : Option (Expr × Expr × Expr × Expr) :=
  if e.isAppOfArity ``CatCrypt.Core.SPComp.bind 4 then
    let args := e.getAppArgs
    some (args[0]!, args[1]!, args[2]!, args[3]!)
  else none

/-- The term `e` with its head beta-reduced, and, when it is not a bind, reduced by
`whnfCore` if that exposes a bind (a `match` on a pair variable reduces by structure
eta). -/
def chainView (e : Expr) : MetaM Expr := do
  let e := (← instantiateMVars e).headBeta
  if (bindApp? e).isSome then return e
  let e' ← whnfCore e
  return if (bindApp? e').isSome then e' else e

/-- The binder name of a continuation, or `x`. -/
def binderName (k : Expr) : Name :=
  match k with
  | .lam n .. => n
  | _ => `x

/-- The type `ty`, after its universal quantifiers, is an application of `SPComp.IsPure`. -/
def concludesIsPure (ty : Expr) : MetaM Bool :=
  forallTelescopeReducing ty fun _ b => do
    return (← instantiateMVars b).isAppOf ``CatCrypt.Core.SPComp.IsPure

/-- The projections of `term : ty`, for `ty` a structure, whose type concludes with
`SPComp.IsPure`, through nested structure fields up to `depth`. -/
partial def structPureFields (depth : Nat) (term ty : Expr) : MetaM (Array Expr) := do
  if depth == 0 then return #[]
  let ty ← whnfR (← instantiateMVars ty)
  let some sName := ty.getAppFn.constName? | return #[]
  let env ← getEnv
  unless isStructure env sName do return #[]
  let mut out := #[]
  for f in getStructureFieldsFlattened env sName (includeSubobjectFields := false) do
    let some proj ← observing? (mkProjection term f) | continue
    let some fty ← observing? (inferType proj) | continue
    if ← concludesIsPure fty then
      out := out.push proj
    else
      out := out ++ (← structPureFields (depth - 1) proj fty)
  return out

/-- The `IsPure` facts available in the current context: the terms `extra` whose type
concludes with `SPComp.IsPure`, the local hypotheses of such a type, and the fields of
such a type of structure-typed local hypotheses (depth two). -/
def collectFacts (extra : Array Expr) : MetaM (Array Expr) := do
  let mut out := #[]
  for t in extra do
    if ← concludesIsPure (← inferType t) then out := out.push t
  for h in ← getLocalHyps do
    let decl ← h.fvarId!.getDecl
    if decl.isImplementationDetail || decl.binderInfo.isInstImplicit then continue
    let ty ← instantiateMVars decl.type
    if ← concludesIsPure ty then
      out := out.push h
    else if !(← isProp ty) then
      out := out ++ (← structPureFields 2 h ty)
  return out

/-- A proof of `SPComp.IsPure c` from the facts, the combinators of `pure`, `sample`,
`fail` and `SPComp.bind`, or `none`. The recursion through `SPComp.bind` is bounded by
`depth`. -/
partial def provePure (facts : Array Expr) (c : Expr) (depth : Nat) :
    MetaM (Option Expr) := do
  let c ← chainView c
  let goal ← mkAppM ``CatCrypt.Core.SPComp.IsPure #[c]
  for f in facts do
    let r ← withoutModifyingState? do
      let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType f)
      if ← withReducibleAndInstances (isDefEq concl goal) then
        let pf ← instantiateMVars (mkAppN f ms)
        if pf.hasExprMVar then return none
        return some pf
      return none
    if let some pf := r then return some pf
  let fn := c.getAppFn
  let some (cname, lvls) := (match fn with
    | .const n ls => some (n, ls)
    | _ => none) | return none
  let leaf? : Option Name :=
    if cname == ``CatCrypt.Core.SPComp.pure && c.getAppNumArgs == 2 then
      some ``CatCrypt.Core.SPComp.pure_isPure
    else if cname == ``CatCrypt.Core.SPComp.sample && c.getAppNumArgs == 3 then
      some ``CatCrypt.Core.SPComp.sample_isPure
    else if cname == ``CatCrypt.Core.SPComp.fail && c.getAppNumArgs == 1 then
      some ``CatCrypt.Core.SPComp.fail_isPure
    else none
  if let some lem := leaf? then
    let pf := mkAppN (.const lem lvls) c.getAppArgs
    if ← withReducibleAndInstances (isDefEq (← inferType pf) goal) then return some pf
    return none
  if depth == 0 then return none
  let some (α, _, p, k) := bindApp? c | return none
  let some hp ← provePure facts p (depth - 1) | return none
  let hk? ← withLocalDeclD (binderName k) α fun x => do
    let some h ← provePure facts (k.beta #[x]) (depth - 1) | return none
    return some (← mkLambdaFVars #[x] h)
  let some hk := hk? | return none
  observing? (mkAppM ``CatCrypt.Core.SPComp.bind_isPure #[hp, hk])
where
  /-- Run `x` and keep its state changes only when it returns `some`. -/
  withoutModifyingState? {γ : Type} (x : MetaM (Option γ)) : MetaM (Option γ) := do
    let s ← saveState
    try
      let r ← x
      if r.isNone then s.restore
      return r
    catch _ =>
      s.restore
      return none

/-- Maximal depth of a binding moved to the front of a chain. -/
def maxHoistDepth : Nat := 32

/-- For a bind chain `e`, move to the front a binding whose computation is equal to `p`
(reducible and instance transparency) and mentions no variable bound before it in `e`:
the binding at position `pos` when `atPos = some pos`, and otherwise the occurrence of
index `skip` among such bindings. The result is the new chain `e'`, a proof of `e = e'`
and the position of the moved binding; `none` when no such binding exists or an exchange
has no `IsPure` side. `depth` is the position of `e` in the original chain. -/
partial def hoist (facts : Array Expr) (p e : Expr) (depth skip : Nat) (atPos : Option Nat) :
    MetaM (Option (Expr × Expr × Nat)) := do
  let e ← chainView e
  let some (α, β, r, k) := bindApp? e | return none
  let here := match atPos with
    | some q => q == depth
    | none => true
  let found ← if here then withReducibleAndInstances (isDefEq r p) else pure false
  if here && atPos.isSome && !found then return none
  if found && skip == 0 then
    return some (e, ← mkEqRefl e, depth)
  let skip := if found then skip - 1 else skip
  if depth ≥ maxHoistDepth then return none
  withLocalDeclD (binderName k) α fun x => do
    let some (body', pfBody, pos) ← hoist facts p (k.beta #[x]) (depth + 1) skip atPos |
      return none
    let some (_, _, r', k') := bindApp? body' | return none
    if r'.containsFVar x.fvarId! then return none
    -- `e = SPComp.bind r (fun x => body')`
    let bindR ← mkAppOptM ``CatCrypt.Core.SPComp.bind #[α, β, r]
    let pf1 ← mkCongrArg bindR (← mkFunExt (← mkLambdaFVars #[x] pfBody))
    -- exchange `r` and `r'`
    let kk ← mkLambdaFVars #[x] k'
    let swap? ← (do
      if let some hq ← provePure facts r' 8 then
        return some (← mkAppM ``CatCrypt.Core.SPComp.isPure_bind_comm_right #[r, r', kk, hq])
      if let some hr ← provePure facts r 8 then
        return some (← mkAppM ``CatCrypt.Core.SPComp.isPure_bind_comm_left #[r, r', kk, hr])
      return none : MetaM (Option Expr))
    let some pfSwap := swap? | return none
    let some (_, _, e') := (← inferType pfSwap).eq? | return none
    let e' ← Core.betaReduce (← instantiateMVars e')
    let pf ← mkExpectedTypeHint (← mkEqTrans pf1 pfSwap) (← mkEq e e')
    return some (e', pf, pos)

/-- Run `k` on the binder variables and the final term of the bind chain `e`, the binders
instantiated by local variables. -/
partial def withChain {γ : Type} (e : Expr) (acc : Array FVarId)
    (k : Array FVarId → Expr → MetaM γ) : MetaM γ := do
  let e ← chainView e
  match bindApp? e with
  | some (α, _, _, f) =>
    withLocalDeclD (binderName f) α fun x => withChain (f.beta #[x]) (acc.push x.fvarId!) k
  | none => k acc e

/-- The correspondence between the binder variables `lv` of one chain and `rv` of the
other read from a simultaneous traversal of the terms `a` and `b`: where `a` has the
variable `lv[i]` at the position where `b` has `rv[j]`, the entry `i` is `j` (the first
such position counts). -/
partial def matchVars (lv rv : Array FVarId) (a b : Expr) (σ : Array (Option Nat)) :
    Array (Option Nat) :=
  match a, b with
  | .fvar x, .fvar y =>
    match lv.idxOf? x, rv.idxOf? y with
    | some i, some j => if σ[i]!.isNone then σ.set! i (some j) else σ
    | _, _ => σ
  | .app f a', .app g b' => matchVars lv rv a' b' (matchVars lv rv f g σ)
  | .lam _ t₁ b₁ _, .lam _ t₂ b₂ _ => matchVars lv rv b₁ b₂ (matchVars lv rv t₁ t₂ σ)
  | .forallE _ t₁ b₁ _, .forallE _ t₂ b₂ _ => matchVars lv rv b₁ b₂ (matchVars lv rv t₁ t₂ σ)
  | .letE _ t₁ v₁ b₁ _, .letE _ t₂ v₂ b₂ _ =>
    matchVars lv rv b₁ b₂ (matchVars lv rv v₁ v₂ (matchVars lv rv t₁ t₂ σ))
  | .proj _ _ a', .proj _ _ b' => matchVars lv rv a' b' σ
  | .mdata _ a', b => matchVars lv rv a' b σ
  | a, .mdata _ b' => matchVars lv rv a b' σ
  | _, _ => σ

/-- The correspondence hint of the chains `lhs` and `rhs`: entry `i` is the position in
`rhs` of the binding whose variable occurs in the final term of `rhs` where the variable of
binding `i` of `lhs` occurs in the final term of `lhs`. -/
def varHint (lhs rhs : Expr) : MetaM (Array (Option Nat)) :=
  withChain lhs #[] fun lv la => withChain rhs #[] fun rv ra =>
    return matchVars lv rv la ra (Array.replicate lv.size none)

/-- Maximal number of occurrences of a computation tried as the partner of the first
binding of the other side. -/
def maxCandidates : Nat := 4

/-- The pairing of bindings suggested by `varHint`: `σ[i]` is the original position in the
right chain of the partner of binding `i` of the left chain, `rhsOrder` the original
positions of the bindings of the current right chain, and `lhsIdx` the original position
of the current left head. -/
structure Hint where
  /-- Partner of each binding of the left chain. -/
  σ : Array (Option Nat)
  /-- Original positions of the bindings of the current right chain. -/
  rhsOrder : Array Nat
  /-- Original position of the current left head. -/
  lhsIdx : Nat

/-- Close the goal `g : lhs = rhs` by the alignment documented at `bind_swap_nf`. The
partner of the left head in the right chain is first the binding that `hint` pairs with
it, then the occurrences of its computation in order (at most `maxCandidates`), with
backtracking when the alignment under the binder fails; when none succeeds, the head of
the right chain is searched in the left chain. Every call consumes one unit of
`budget`. -/
partial def align (facts : Array Expr) (g : MVarId) (budget : IO.Ref Nat)
    (hint : Option Hint) : MetaM Unit :=
  g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let some (_, lhs, rhs) := ty.eq? |
    throwError "bind_swap_nf: the goal is not an equality:{indentExpr ty}"
  if ← withReducibleAndInstances (isDefEq lhs rhs) then
    g.assign (← mkEqRefl lhs)
    return
  let fuel ← budget.get
  if fuel == 0 then throwError "bind_swap_nf: step limit reached at{indentExpr ty}"
  budget.set (fuel - 1)
  let lhs ← chainView lhs
  let rhs ← chainView rhs
  -- `step α p f k close`: assign `g` from `h : bind p f = bind p k` via `close h`
  let step (α β p f k : Expr) (close : Expr → MetaM Expr) (n : Name) (hint' : Option Hint) :
      MetaM Unit := do
    let mTy ← withLocalDeclD n α fun a => do
      mkForallFVars #[a] (← mkEq (f.beta #[a]) (k.beta #[a]))
    let m ← mkFreshExprSyntheticOpaqueMVar mTy
    let bindP ← mkAppOptM ``CatCrypt.Core.SPComp.bind #[α, β, p]
    let h ← mkCongrArg bindP (← mkFunExt m)
    g.assign (← mkExpectedTypeHint (← close h) ty)
    let (_, g') ← m.mvarId!.intro n
    align facts g' budget hint'
  -- the hint after the left head is paired with the right binding at position `pos`
  let advance (pos : Nat) : Option Hint := hint.map fun h =>
    { h with rhsOrder := h.rhsOrder.eraseIdxIfInBounds pos, lhsIdx := h.lhsIdx + 1 }
  let mut err? : Option Exception := none
  if let some (α, β, p, f) := bindApp? lhs then
    -- the position of the right binding that the hint pairs with the left head
    let hinted : Option Nat := hint.bind fun h =>
      (h.σ[h.lhsIdx]?).join.bind fun j => h.rhsOrder.idxOf? j
    -- a right binding is reserved when the hint pairs it with some left binding
    let reserved (pos : Nat) : Bool := hint.any fun h =>
      match h.rhsOrder[pos]? with
      | some j => h.σ.contains (some j)
      | none => false
    -- the hinted partner, then the unreserved occurrences, then the reserved ones
    let mut tries : Array (Nat × Option Nat × Bool) := #[]
    if let some pos := hinted then tries := tries.push (0, some pos, true)
    for i in [0:maxCandidates] do tries := tries.push (i, none, false)
    for i in [0:maxCandidates] do tries := tries.push (i, none, true)
    for (i, atPos, allowReserved) in tries do
      let some (rhs', pf, pos) ← hoist facts p rhs 0 i atPos | continue
      if atPos.isNone && hinted == some pos then continue
      if atPos.isNone && reserved pos != allowReserved then continue
      let some (_, _, _, k) := bindApp? rhs' | break
      let s ← saveState
      try
        return ← step α β p f k (fun h => do mkEqTrans h (← mkEqSymm pf)) (binderName f)
          (advance pos)
      catch e =>
        s.restore
        err? := some e
  if let some (α, β, q, k) := bindApp? rhs then
    for i in [0:maxCandidates] do
      let some (lhs', pf, _) ← hoist facts q lhs 0 i none | break
      let some (_, _, _, f) := bindApp? lhs' | break
      let s ← saveState
      try
        return ← step α β q f k (fun h => mkEqTrans pf h) (binderName k) none
      catch e =>
        s.restore
        err? := some e
  if let some e := err? then throw e
  throwError "bind_swap_nf: the two sides have no common binding that can be moved to \
    the front:{indentExpr lhs}\n={indentExpr rhs}"

/-- Maximal number of alignment steps of `bind_swap_nf`, counted over all branches of the
backtracking search. -/
def maxSteps : Nat := 256

/-- `bind_swap_nf` proves an equality of two `SPComp` bind chains that are equal up to the
order of independent bindings, each exchange involving an `IsPure` computation. Both sides
are normalised by `simp only [SPComp.monad_bind_eq, SPComp.monad_pure_eq,
SPComp.bind_assoc, SPComp.pure_bind]`; then the first binding of one side is moved to the
front of the other by `SPComp.isPure_bind_comm_left`/`SPComp.isPure_bind_comm_right`
and removed by congruence, until the two sides are definitionally equal at reducible and
instance transparency; the module documentation describes the pairing hint and the
backtracking. The `IsPure` side
conditions are proved from the combinators of `pure`, `sample`, `fail` and
`SPComp.bind`, the `IsPure` hypotheses of the context, the `IsPure` fields of
structure-typed hypotheses, and the terms `hᵢ` of `bind_swap_nf [h₁, …]`. -/
syntax (name := bindSwapNfStx) "bind_swap_nf" (" [" term,* "]")? : tactic

@[tactic bindSwapNfStx] def evalBindSwapNf : Tactic := fun stx => do
  let ts : Array Syntax :=
    if stx[1].isNone then #[] else stx[1][1].getSepArgs
  evalTactic (← `(tactic| try (set_option linter.unusedSimpArgs false in
    simp only [CatCrypt.Core.SPComp.monad_bind_eq, CatCrypt.Core.SPComp.monad_pure_eq,
      CatCrypt.Core.SPComp.bind_assoc, CatCrypt.Core.SPComp.pure_bind])))
  if (← getGoals).isEmpty then return
  let g ← getMainGoal
  g.withContext do
    let extra ← ts.mapM fun t => Tactic.elabTerm t none
    let facts ← collectFacts extra
    let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).eq? |
      throwError "bind_swap_nf: the goal is not an equality"
    let σ ← varHint lhs rhs
    let n ← withChain rhs #[] fun rv _ => return rv.size
    align facts g (← IO.mkRef maxSteps)
      (some { σ, rhsOrder := (List.range n).toArray, lhsIdx := 0 })
  replaceMainGoal []

end CatCrypt.Tactic.BindSwap
