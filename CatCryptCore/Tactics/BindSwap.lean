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
5. Removal of unused bindings, when the alignment fails: a binding whose variable the rest
   of its chain does not mention is removed by a discard fact `SPComp.bind c (fun _ => r) =
   r` or by `SPComp.isPure_bind_discard` (`c` is `IsPure` and of mass one from every heap),
   and the alignment runs again.
6. Chain facts, when this fails: a fact `∀ f, c₁ >>= fun p => c₂ >>= fun q => f p q (t p q)
   = c₁ >>= fun p => c₂ >>= fun q => f p q (t' p q)` (such as the correctness of
   Diffie–Hellman on honest key pairs) rewrites one side, in either direction: a binding
   `p` of `c₁` and a later binding `q` of `c₂` are brought together by `hoist`, the
   occurrences of `t p q` in the rest of the chain are abstracted, and the fact replaces
   them by `t' p q`; the alignment runs on each rewritten goal, with at most
   `maxFactDepth` rewrites on a branch and `maxFactTries` goals in all.
7. Product samples, when this fails: each uniform sample `SPComp.sample (A × B)` is
   replaced by the samples of `A` and `B` followed by the pair (`SPComp.sample_prod_eq`),
   both sides are normalised again and steps 3 to 6 run on the result, so that a sample of
   a product on one side aligns with the samples of the components on the other.

An argument `t` of `bind_swap_nf [t, …]` that is an identifier naming a global definition
is a definition to unfold: it is unfolded by name in the goal before step 1, and none of
its implicit or instance arguments is elaborated (a game `G {W : Type} [Fintype W] …` is
given as `G`, not `G (W := W)`). An identifier naming a global theorem is the constant
with its arguments universally quantified. Another term is elaborated; when it is not a
proof and its head is a definition, that definition is unfolded.

The `IsPure` side conditions are proved from the combinators of `pure`, `sample`, `fail`
and `SPComp.bind`, from the `IsPure` hypotheses of the local context (possibly
universally quantified), from the `Prop`-valued fields of structure-typed hypotheses up
to depth two (`deps.keygen_isPure` for `deps : Deps`), and from the terms given as
arguments: `bind_swap_nf [h₁, …]`. The mass-one, discard and chain facts are collected
from the same sources; mass-one side conditions are also proved by the lemmas of
`CatCryptCore.Unary.Lossless` for `pure`, `sample` and `SPComp.bind` when that module is
in the environment. An argument that is an equation of another form is applied by
`simp only` to two leaves that are not definitionally equal; a permutation equation such
as `dh a b = dh b a` is applied by ordered rewriting, so that both leaves, whose bound
variables are shared, reach the same normal form.

Two chains are equal up to such exchanges exactly when they denote the same trace of the
partially commutative word whose letters are the bindings; moving an occurrence of the
left head to the front of the right chain, with backtracking over repeated letters, decides
equality of traces; the step bound makes the procedure fail on goals whose search exceeds
it. The procedure does not reorder two bindings neither of which is `IsPure`.

`advantage_eq_nf [h₁, …]` proves an equality of two advantages `Advantage X Y =
Advantage X' Y'` (after unfolding the heads of the two sides, such as `AdvantageA` and
`DDH_Advantage`) from the game equalities `X = X'` and `Y = Y'` (or `X = Y'` and
`Y = X'`), each closed by unfolding the game definitions at its heads and the definitions
among the arguments, and `bind_swap_nf [h₁, …]`. It refers to `CatCrypt.Crypto.Advantage`
by name and applies where that definition is in the environment.

`spec_inline [t₁, …]` proves an `SPComp` equality in which an abstract operation `op a`
occurs that a hypothesis specifies as a bind chain:
`h : ∀ xs, P xs → (c₁ >>= fun a => … pure t) = op a`. The goal is normalised by
`simp only` with the monad laws and the arguments that are not specifications, its
conditionals are split by `split_ifs`, and in each branch the specifications are turned
into rewrite rules `op a = chain`: the binders of `h` that are not propositions and occur
in `op a` stay universally quantified, the others are instantiated by local variables of
their type; a premise that mentions a quantified binder stays a premise of the rule, the
others are instantiated by local hypotheses. The rules rewrite the goal by `simp only`
together with the propositional local hypotheses (such as the case hypothesis of the
split, which discharges the premises) and the monad laws; then the definitions of the goal
applied to a constructor (such as a definition by cases applied to `Sum.inr a`) are
unfolded by their equation lemmas, and each branch is closed by `rfl` or by
`bind_swap_nf`. The procedure fails without running any tactic when the goal is not an
`SPComp` equality or no hypothesis or argument has the form of a specification whose
operation occurs in the goal.

`le_of_eq_nf [t₁, …]` proves `a ≤ b` between two advantages by `le_of_eq` and
`advantage_eq_nf [t₁, …]`.

The module registers with `catcrypt_auto` (`CatCryptCore.Tactics.AutoDispatchCore`) these
arms:

| Shape | Arm | Order |
|---|---|---|
| `advantage equality` | `advantage_eq_nf` | 5 |
| `SPComp equality` | `bind_swap_nf`; `spec_inline` | 5; 22 |
| `distance inequality` | `le_of_eq_nf` | 25 |
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

/-- An `IsPure` computation of mass one from every heap, bound to a continuation that does
not use its result, can be dropped: `c >>= fun _ => k` equals `k`. The mass condition is
`CatCrypt.Unary.isLossless c` unfolded. -/
theorem isPure_bind_discard (c : SPComp α) (k : SPComp β) (hc : IsPure c)
    (hl : ∀ h, CatCrypt.Prob.SDistr.mass (c h) = 1) :
    SPComp.bind c (fun _ => k) = k := by
  obtain ⟨d, hd⟩ := hc
  funext h
  have e : SPComp.bind c (fun _ => k) h = (c h).bind (fun _ => k h) := by
    simp only [bind, hd h, CatCrypt.Prob.SDistr.bind_assoc, CatCrypt.Prob.SDistr.pure_bind]
  rw [e]
  exact CatCrypt.Prob.SDistr.bind_const_mass_one (hl h) (k h)

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

/-- The kinds of facts that `bind_swap_nf` uses. -/
inductive FactKind where
  /-- `SPComp.IsPure c`. -/
  | isPure
  /-- `SDistr.mass (c h) = 1` for every heap `h`, possibly stated as
  `CatCrypt.Unary.isLossless c`. -/
  | lossless
  /-- `SPComp.bind c (fun _ => r) = r`. -/
  | discard
  /-- `c₁ >>= fun p => c₂ >>= fun q => f p q t = c₁ >>= fun p => c₂ >>= fun q => f p q t'`
  for a universally quantified `f`. -/
  | chain
  /-- An equation of another form. -/
  | equation
  /-- Any other statement. -/
  | other
  deriving BEq, Inhabited

/-- `e` is the numeral `1`. -/
def isOneLit (e : Expr) : Bool :=
  e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 1).rawNatLit? == some 1

/-- `e` is `g a b t` for the local `g` among `xs`, `a` and `b` the loose bound variables
`1` and `0`, and `t` a term that mentions one of them. -/
def isChainLeaf (xs : Array Expr) (e : Expr) : Option Expr :=
  let args := e.getAppArgs
  if xs.contains e.getAppFn && args.size == 3 && args[0]! == .bvar 1 && args[1]! == .bvar 0
      && args[2]!.hasLooseBVars then
    some e.getAppFn
  else none

/-- The leaf `f p q t` of a two-binding chain `c₁ >>= fun p => c₂ >>= fun q => f p q t`,
with `p` and `q` as the loose bound variables `1` and `0`. -/
def chainLeaf? (e : Expr) : Option Expr := do
  let (_, _, _, k₁) ← bindApp? e
  let .lam _ _ b₁ _ := k₁ | none
  let (_, _, _, k₂) ← bindApp? b₁
  let .lam _ _ b₂ _ := k₂ | none
  some b₂

/-- The kind of a fact of type `ty`, read after its universal quantifiers. -/
def factKind (ty : Expr) : MetaM FactKind :=
  forallTelescopeReducing ty fun xs b => do
    let b ← instantiateMVars b
    if b.isAppOf ``CatCrypt.Core.SPComp.IsPure then return .isPure
    let some (_, l, r) := b.eq? | return .other
    if l.isAppOf ``CatCrypt.Prob.SDistr.mass && isOneLit r then return .lossless
    if let some (_, _, _, .lam _ _ body _) := bindApp? l then
      if !body.hasLooseBVars && body == r then return .discard
    if let (some a, some b) := (chainLeaf? l, chainLeaf? r) then
      if let (some f, some g) := (isChainLeaf xs a, isChainLeaf xs b) then
        if f == g then return .chain
    return .equation

/-- The facts that `bind_swap_nf` uses, by kind. -/
structure Facts where
  /-- Proofs concluding `SPComp.IsPure c`. -/
  isPure : Array Expr := #[]
  /-- Proofs concluding `SDistr.mass (c h) = 1`. -/
  lossless : Array Expr := #[]
  /-- Proofs concluding `SPComp.bind c (fun _ => r) = r`. -/
  discard : Array Expr := #[]
  /-- Proofs of equalities of two-binding chains that differ in the last argument of a
  universally quantified continuation. -/
  chain : Array Expr := #[]
  /-- Equations of other forms given as arguments, applied to the leaves. -/
  equations : Array Expr := #[]

/-- `fs` with the fact `t : ty` added under its kind; an equation of another form is added
only when `explicit`. -/
def Facts.add (fs : Facts) (t ty : Expr) (explicit : Bool := false) : MetaM Facts := do
  return match ← factKind ty with
    | .isPure => { fs with isPure := fs.isPure.push t }
    | .lossless => { fs with lossless := fs.lossless.push t }
    | .discard => { fs with discard := fs.discard.push t }
    | .chain => { fs with chain := fs.chain.push t }
    | .equation => if explicit then { fs with equations := fs.equations.push t } else fs
    | .other => fs

/-- The projections of `term : ty`, for `ty` a structure, whose type is a fact of a kind
used by `bind_swap_nf` (`IsPure`, mass one, discard or two-binding chain), through nested
structure fields up to `depth`. -/
partial def structFactFields (depth : Nat) (term ty : Expr) : MetaM (Array (Expr × Expr)) := do
  if depth == 0 then return #[]
  let ty ← whnfR (← instantiateMVars ty)
  let some sName := ty.getAppFn.constName? | return #[]
  let env ← getEnv
  unless isStructure env sName do return #[]
  let mut out := #[]
  for f in getStructureFieldsFlattened env sName (includeSubobjectFields := false) do
    let some proj ← observing? (mkProjection term f) | continue
    let some fty ← observing? (inferType proj) | continue
    let k ← factKind fty
    if k != .other && k != .equation then
      out := out.push (proj, fty)
    else if !(← isProp fty) then
      out := out ++ (← structFactFields (depth - 1) proj fty)
  return out

/-- The facts available in the current context: the terms `extra`, the local hypotheses,
and the fields of structure-typed local hypotheses (depth two), each of the kind
`IsPure`, mass one, discard or two-binding chain. -/
def collectFacts (extra : Array Expr) : MetaM Facts := do
  let mut fs : Facts := {}
  for t in extra do
    fs ← fs.add t (← inferType t) (explicit := true)
  for h in ← getLocalHyps do
    let decl ← h.fvarId!.getDecl
    if decl.isImplementationDetail || decl.binderInfo.isInstImplicit then continue
    let ty ← instantiateMVars decl.type
    let k ← factKind ty
    if k != .other && k != .equation then
      fs ← fs.add h ty
    else if !(← isProp ty) then
      for (p, pty) in ← structFactFields 2 h ty do
        fs ← fs.add p pty
  return fs

/-- Run `x` and keep its state changes only when it returns `some`. -/
def withoutModifyingState? {γ : Type} (x : MetaM (Option γ)) : MetaM (Option γ) := do
  let s ← saveState
  try
    let r ← x
    if r.isNone then s.restore
    return r
  catch _ =>
    s.restore
    return none

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

/-- The proposition `∀ h, SDistr.mass (c h) = 1`. -/
def losslessType (c : Expr) : MetaM Expr :=
  withLocalDeclD `h (mkConst ``CatCrypt.Core.Heap) fun h => do
    let m ← mkAppM ``CatCrypt.Prob.SDistr.mass #[mkApp c h]
    mkForallFVars #[h] (← mkEq m (← mkNumeral (mkConst ``ENNReal) 1))

/-- A proof of `∀ h, SDistr.mass (c h) = 1` from the mass-one facts, or, when the module
`CatCryptCore.Unary.Lossless` is in the environment, from its lemmas for `pure`, `sample`
and `SPComp.bind`; `none` otherwise. The recursion through `SPComp.bind` is bounded by
`depth`. -/
partial def proveLossless (facts : Array Expr) (c : Expr) (depth : Nat) :
    MetaM (Option Expr) := do
  let c ← chainView c
  let ty ← losslessType c
  for f in facts do
    let r ← withoutModifyingState? do
      forallTelescope ty fun hs gc => do
        let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType f)
        if ← withReducibleAndInstances (isDefEq concl gc) then
          let pf ← instantiateMVars (mkAppN f ms)
          if pf.hasExprMVar then return none
          return some (← mkLambdaFVars hs pf)
        return none
    if let some pf := r then return some pf
  let env ← getEnv
  if c.isAppOfArity ``CatCrypt.Core.SPComp.pure 2 &&
      env.contains `CatCrypt.Unary.lossless_pure then
    return ← observing? (mkAppOptM `CatCrypt.Unary.lossless_pure #[none, some c.appArg!])
  if c.isAppOfArity ``CatCrypt.Core.SPComp.sample 3 &&
      env.contains `CatCrypt.Unary.lossless_sample then
    return ← observing? (mkAppOptM `CatCrypt.Unary.lossless_sample (c.getAppArgs.map some))
  if depth == 0 || !env.contains `CatCrypt.Unary.lossless_bind then return none
  let some (α, _, p, k) := bindApp? c | return none
  let some hp ← proveLossless facts p (depth - 1) | return none
  let hk? ← withLocalDeclD (binderName k) α fun x => do
    let some h ← proveLossless facts (k.beta #[x]) (depth - 1) | return none
    return some (← mkLambdaFVars #[x] h)
  let some hk := hk? | return none
  observing? (mkAppOptM `CatCrypt.Unary.lossless_bind
    #[none, none, some p, some k, some hp, some hk])

/-- A proof of `SPComp.bind r (fun _ => body) = body`, for `r : SPComp α` and
`body : SPComp β`, from a discard fact, or from `SPComp.isPure_bind_discard` with the
`IsPure` and mass-one side conditions; `none` otherwise. -/
def proveDiscard (fs : Facts) (α β r body : Expr) : MetaM (Option Expr) := do
  let lhs := mkApp (← mkAppOptM ``CatCrypt.Core.SPComp.bind #[α, β, r]) (.lam `x α body .default)
  let goal ← mkEq lhs body
  for f in fs.discard do
    let r? ← withoutModifyingState? do
      let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType f)
      if ← withReducibleAndInstances (isDefEq concl goal) then
        let pf ← instantiateMVars (mkAppN f ms)
        if pf.hasExprMVar then return none
        return some pf
      return none
    if let some pf := r? then return some pf
  let some hp ← provePure fs.isPure r 8 | return none
  let some hl ← proveLossless fs.lossless r 8 | return none
  observing? (mkAppM ``CatCrypt.Core.SPComp.isPure_bind_discard #[r, body, hp, hl])

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

/-- Rewrite the target of `g` by `simp only` with the equations `eqs`; the new goal, or
`none` when the goal is closed. -/
def simpOnlyWith (g : MVarId) (eqs : Array Expr) : MetaM (Option MVarId) := g.withContext do
  let mut thms : SimpTheorems := {}
  for e in eqs do
    thms ← thms.add (.other `bind_swap_nf) #[] e
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let (r?, _) ← simpTarget g ctx
  return r?

/-- Close the goal `g : lhs = rhs` by the alignment documented at `bind_swap_nf`. The
partner of the left head in the right chain is first the binding that `hint` pairs with
it, then the occurrences of its computation in order (at most `maxCandidates`), with
backtracking when the alignment under the binder fails; when none succeeds, the head of
the right chain is searched in the left chain. Two leaves (sides that are not binds) that
are not definitionally equal are closed by `simp only` with the equations `eqs`. Every
call consumes one unit of `budget`. -/
partial def align (facts : Array Expr) (g : MVarId) (budget : IO.Ref Nat)
    (hint : Option Hint) (eqs : Array Expr := #[]) : MetaM Unit :=
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
  if !eqs.isEmpty && (bindApp? lhs).isNone && (bindApp? rhs).isNone then
    let s ← saveState
    try
      match ← simpOnlyWith g eqs with
      | none => return
      | some g' =>
        withReducible g'.refl
        return
    catch _ => pure ()
    s.restore
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
    align facts g' budget hint' eqs
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

/-- The bind chain `e` with each binding whose variable the rest of the chain does not
mention removed, when `proveDiscard` proves its removal: `none` when no binding is
removed, else the new chain `e'` and a proof of `e = e'`. -/
partial def dropUnused (fs : Facts) (e : Expr) (depth : Nat) :
    MetaM (Option (Expr × Expr)) := do
  let e ← chainView e
  let some (α, β, r, k) := bindApp? e | return none
  if depth ≥ maxHoistDepth then return none
  let bindR ← mkAppOptM ``CatCrypt.Core.SPComp.bind #[α, β, r]
  -- `(unused, k' or the body, proof of `k = k'` under the binder)`
  let res? ← withLocalDeclD (binderName k) α fun x => do
    let body ← chainView (k.beta #[x])
    let sub ← dropUnused fs body (depth + 1)
    let body' := (sub.map (·.1)).getD body
    let pfLam? ← sub.mapM fun (_, pf) => mkLambdaFVars #[x] pf
    if body'.containsFVar x.fvarId! then
      if pfLam?.isNone then return none
      return some (false, ← mkLambdaFVars #[x] body', pfLam?)
    return some (true, body', pfLam?)
  let some (unused, b, pfLam?) := res? | return none
  let k' := if unused then Expr.lam (binderName k) α b .default else b
  let e₁ := mkApp bindR k'
  let pf₁ ← match pfLam? with
    | some pfLam => do mkExpectedTypeHint (← mkCongrArg bindR (← mkFunExt pfLam)) (← mkEq e e₁)
    | none => do mkExpectedTypeHint (← mkEqRefl e) (← mkEq e e₁)
  if unused then
    if let some pfD ← proveDiscard fs α β r b then
      return some (b, ← mkEqTrans pf₁ pfD)
  if pfLam?.isNone then return none
  return some (e₁, pf₁)

/-- `e` with each `match` on a variable of a structure type reduced by structure eta
(`whnfCore`), so that the components appear as projections. -/
def etaMatches (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    if ← isMatcherApp e then
      let e' ← whnfCore e
      if e' != e then return .visit e'
    return .continue)

/-- Rewrite the bind chain `e` at its binding of position `pos` by the two-binding chain
fact `fact` (from right to left when `rev`): when the binding at `pos` has the first
computation `c₁` of the fact, the occurrence of index `skip` of its second computation `c₂`
after it is moved next to it (`hoist`), the last argument `t p q` of the fact's
continuation is abstracted in the rest of the chain, and the fact replaces it by `t' p q`.
The result is the new chain and a proof of `e = e'`, or `none`. -/
partial def factRewrite (fs : Facts) (fact : Expr) (rev : Bool) (e : Expr) (pos skip : Nat) :
    MetaM (Option (Expr × Expr)) := do
  let e ← chainView e
  let some (α, β, r, k) := bindApp? e | return none
  let bindR ← mkAppOptM ``CatCrypt.Core.SPComp.bind #[α, β, r]
  if pos > 0 then
    let res? ← withLocalDeclD (binderName k) α fun x => do
      let some (b', pf) ← factRewrite fs fact rev (k.beta #[x]) (pos - 1) skip | return none
      return some (← mkLambdaFVars #[x] b', ← mkLambdaFVars #[x] pf)
    let some (k', pfLam) := res? | return none
    let e' := mkApp bindR k'
    let pf ← mkCongrArg bindR (← mkFunExt pfLam)
    return some (e', ← mkExpectedTypeHint pf (← mkEq e e'))
  withoutModifyingState? do
    let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType fact)
    let some (_, l, rr) := concl.eq? | return none
    let L := if rev then rr else l
    let some (_, _, C₁, K₁) := bindApp? L | return none
    unless ← withReducibleAndInstances (isDefEq C₁ r) do return none
    let res? ← withLocalDeclD (binderName k) α fun x₁ => do
      let some (_, _, C₂, K₂) := bindApp? (K₁.beta #[x₁]).headBeta | return none
      let C₂ ← instantiateMVars C₂
      let some (rest', pfH, _) ← hoist fs.isPure C₂ (k.beta #[x₁]) 0 skip none | return none
      let some (α₂, _, _, k₂) := bindApp? rest' | return none
      let ok ← withLocalDeclD (binderName k₂) α₂ fun x₂ => do
        let inner ← instantiateMVars (K₂.beta #[x₂]).headBeta
        let args := inner.getAppArgs
        unless inner.getAppFn.isMVar && args.size == 3 && args[0]! == x₁ && args[1]! == x₂ do
          return false
        let t := args[2]!
        if t.hasExprMVar then return false
        let body ← etaMatches (k₂.beta #[x₂])
        let bodyAbs ← kabstract body t
        unless bodyAbs.hasLooseBVars do return false
        let fLam ← withLocalDeclD `v (← inferType t) fun v =>
          mkLambdaFVars #[x₁, x₂, v] (bodyAbs.instantiate1 v)
        isDefEq inner.getAppFn fLam
      unless ok do return none
      return some (← mkLambdaFVars #[x₁] rest', ← mkLambdaFVars #[x₁] pfH)
    let some (restLam, pfHLam) := res? | return none
    let pfFact ← instantiateMVars (mkAppN fact ms)
    if pfFact.hasExprMVar then return none
    let pfFact ← if rev then mkEqSymm pfFact else pure pfFact
    let some (_, _, rhsF) := (← inferType pfFact).eq? | return none
    let e' ← Core.betaReduce (← instantiateMVars rhsF)
    let mid := mkApp bindR restLam
    let pf₁ ← mkExpectedTypeHint (← mkCongrArg bindR (← mkFunExt pfHLam)) (← mkEq e mid)
    let pf ← mkEqTrans pf₁ (← mkExpectedTypeHint pfFact (← mkEq mid e'))
    return some (e', pf)

/-- From `g : lhs = rhs` and `pf : side = e'` for the left side (`left`) or the right side,
the goal with that side replaced by `e'`; `g` is assigned. -/
def rewriteSide (g : MVarId) (left : Bool) (e' pf : Expr) : MetaM MVarId := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let some (_, lhs, rhs) := ty.eq? | throwError "bind_swap_nf: the goal is not an equality"
  if left then
    let g' ← mkFreshExprSyntheticOpaqueMVar (← mkEq e' rhs)
    g.assign (← mkExpectedTypeHint (← mkEqTrans pf g') ty)
    return g'.mvarId!
  else
    let g' ← mkFreshExprSyntheticOpaqueMVar (← mkEq lhs e')
    g.assign (← mkExpectedTypeHint (← mkEqTrans g' (← mkEqSymm pf)) ty)
    return g'.mvarId!

/-- Close `g : lhs = rhs` by `align` with the budget `maxSteps` and the pairing hint read
from its two sides. -/
def alignGoal (fs : Facts) (g : MVarId) : MetaM Unit := g.withContext do
  let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).eq? |
    throwError "bind_swap_nf: the goal is not an equality"
  let σ ← varHint lhs rhs
  let n ← withChain rhs #[] fun rv _ => return rv.size
  align fs.isPure g (← IO.mkRef maxSteps)
    (some { σ, rhsOrder := (List.range n).toArray, lhsIdx := 0 }) fs.equations

/-- `alignGoal`, with the state restored and `false` returned when it fails. -/
def tryAlign (fs : Facts) (g : MVarId) : MetaM Bool := do
  let s ← saveState
  try
    alignGoal fs g
    return true
  catch _ =>
    s.restore
    return false

/-- The goal `g` with the unused bindings of both sides removed by `dropUnused`, or `none`
when no binding is removed. -/
def dropGoal (fs : Facts) (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  let some (_, lhs, _) := (← instantiateMVars (← g.getType)).eq? | return none
  let mut g' := g
  let mut changed := false
  if let some (l', pf) ← dropUnused fs lhs 0 then
    g' ← rewriteSide g' true l' pf
    changed := true
  let some (_, _, rhs) := (← instantiateMVars (← g'.getType)).eq? | return none
  if let some (r', pf) ← g'.withContext (dropUnused fs rhs 0) then
    g' ← rewriteSide g' false r' pf
    changed := true
  return if changed then some g' else none

/-- Maximal number of rewrites by chain facts on one branch of `factSearch`. -/
def maxFactDepth : Nat := 2

/-- Maximal number of goals tried by `factSearch` after a rewrite by a chain fact. -/
def maxFactTries : Nat := 64

/-- Close `g` by rewriting one side with a chain fact (`factRewrite`, every position,
partner, fact and orientation) and `alignGoal`, up to `depth` rewrites on a branch and
`tries` goals in all. -/
partial def factSearch (fs : Facts) (g : MVarId) (depth : Nat) (tries : IO.Ref Nat) :
    MetaM Bool := g.withContext do
  if depth == 0 then return false
  let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).eq? | return false
  let mut cands : Array (Bool × Expr × Expr) := #[]
  for left in [true, false] do
    let e := if left then lhs else rhs
    let n ← withChain e #[] fun v _ => return v.size
    for fact in fs.chain do
      for rev in [false, true] do
        for pos in [0:n] do
          for skip in [0:maxCandidates] do
            let s ← saveState
            let r? ← factRewrite fs fact rev e pos skip
            match r? with
            | some (e', pf) =>
              let e' ← instantiateMVars e'
              let pf ← instantiateMVars pf
              s.restore
              cands := cands.push (left, e', pf)
            | none => s.restore
  for (left, e', pf) in cands do
    if (← tries.get) == 0 then return false
    tries.modify (· - 1)
    let s ← saveState
    try
      let g' ← rewriteSide g left e' pf
      if ← tryAlign fs g' then return true
      if ← factSearch fs g' (depth - 1) tries then return true
      s.restore
    catch _ =>
      s.restore
  return false

/-- Close `g : lhs = rhs`: by `alignGoal`; failing that, after removing the unused bindings
(`dropGoal`); failing that, by `factSearch` with the chain facts. The error is that of the
first `alignGoal`. -/
def closeGoalCore (fs : Facts) (g : MVarId) : MetaM Unit := do
  let s ← saveState
  let err ← try
      alignGoal fs g
      return
    catch e => pure e
  s.restore
  let g' := (← dropGoal fs g).getD g
  if g' != g then
    if ← tryAlign fs g' then return
  unless fs.chain.isEmpty do
    if ← factSearch fs g' maxFactDepth (← IO.mkRef maxFactTries) then return
  s.restore
  throw err

/-- `e` contains a uniform sample `SPComp.sample (A × B)` of a product type. -/
def hasProdSample (e : Expr) : Bool :=
  (e.find? fun x => x.isAppOfArity ``CatCrypt.Core.SPComp.sample 3 &&
    (x.getArg! 0).isAppOfArity ``Prod 2).isSome

/-- Rewrite the target of `g` by `simp only [SPComp.sample_prod_eq, SPComp.bind_assoc,
SPComp.pure_bind]`: each uniform sample of a product type becomes the two samples of its
components followed by the pair, and the pair is passed to the continuation. The new
goal, or `none` when the goal is closed. -/
def splitProdSamples (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  let mut thms : SimpTheorems := {}
  for n in [``CatCrypt.Core.SPComp.sample_prod_eq, ``CatCrypt.Core.SPComp.bind_assoc,
      ``CatCrypt.Core.SPComp.pure_bind] do
    thms ← thms.addConst n
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let (r?, _) ← simpTarget g ctx
  return r?

/-- Close `g : lhs = rhs` by `closeGoalCore`; failing that, when the goal samples from a
product type, by `closeGoalCore` after each such sample is replaced by the samples of its
components (`splitProdSamples`), so that a product sample on one side aligns with the
samples of the components on the other. The error is that of the first `closeGoalCore`. -/
def closeGoal (fs : Facts) (g : MVarId) : MetaM Unit := do
  let s ← saveState
  let err ← try
      closeGoalCore fs g
      return
    catch e => pure e
  s.restore
  if hasProdSample (← instantiateMVars (← g.getType)) then
    try
      match ← splitProdSamples g with
      | none => return
      | some g' =>
        closeGoalCore fs g'
        return
    catch _ => s.restore
  throw err

/-- `bind_swap_nf` proves an equality of two `SPComp` bind chains that are equal up to the
order of independent bindings, each exchange involving an `IsPure` computation, up to the
removal of unused bindings, and up to rewrites by two-binding chain facts. The arguments
`hᵢ` of `bind_swap_nf [h₁, …]` that are equations of another form are applied by
`simp only [hᵢ, …]` to two leaves that are not definitionally equal (a permutation
equation such as `dh a b = dh b a` by ordered rewriting). Both sides are normalised by
`simp only
[SPComp.monad_bind_eq, SPComp.monad_pure_eq, SPComp.bind_assoc, SPComp.pure_bind]`; then
the first binding of one side is moved to the front of the other by
`SPComp.isPure_bind_comm_left`/`SPComp.isPure_bind_comm_right` and removed by congruence,
until the two sides are definitionally equal at reducible and instance transparency; the
module documentation describes the pairing hint and the backtracking. When this fails,
each binding whose variable is unused is removed by a discard fact
(`SPComp.bind c (fun _ => r) = r`) or by `SPComp.isPure_bind_discard` (`c` is `IsPure`
and of mass one), and the alignment is run again; when this fails, one side is rewritten
by a two-binding chain fact (`∀ f, c₁ >>= fun p => c₂ >>= fun q => f p q (t p q) = c₁ >>=
fun p => c₂ >>= fun q => f p q (t' p q)`, in either direction, at most `maxFactDepth`
rewrites on a branch). The facts are the hypotheses of the context, the fields of
structure-typed hypotheses (depth two) and the terms `hᵢ`; `IsPure` side conditions are
also proved from the combinators of `pure`, `sample`, `fail` and `SPComp.bind`, and
mass-one side conditions from the lemmas of `CatCryptCore.Unary.Lossless` when that
module is imported. When all of this fails, each uniform sample of a product type is
replaced by the samples of its components (`SPComp.sample_prod_eq`) and the procedure runs
again. An argument that names a definition (an identifier, or a term that is not a proof
whose head is a definition) is unfolded in the goal first, with no implicit or instance
argument elaborated. -/
syntax (name := bindSwapNfStx) "bind_swap_nf" (" [" term,* "]")? : tactic

/-- The global constant that the identifier `t` names, when `t` is an identifier whose
first component is not a local hypothesis and which resolves to a definition or a
theorem. -/
def argConst? (t : Syntax) : TacticM (Option Name) := do
  unless t.isIdent do return none
  if ((← getLCtx).findFromUserName? t.getId.getRoot).isSome then return none
  let some n ← (try some <$> realizeGlobalConstNoOverloadWithInfo t catch _ => pure none) |
    return none
  match ← getConstInfo n with
  | .defnInfo _ | .thmInfo _ => return some n
  | _ => return none

/-- The arguments `ts` of `bind_swap_nf [t₁, …]` and `advantage_eq_nf [t₁, …]`, read in
the context of the main goal: the definitions to unfold and the facts. An identifier that
names a global theorem is the constant, with all its arguments universally quantified,
and an identifier that names a global definition is a definition to unfold, so that no
implicit or instance argument of either is elaborated without the goal. Another term is
elaborated; it is a definition to unfold when it is not a proof and its head is a
definition, and a fact otherwise. -/
def elabArgs (ts : Array Syntax) : TacticM (Array Name × Array Expr) := do
  let mut ns : Array Name := #[]
  let mut es : Array Expr := #[]
  for t in ts do
    if let some n ← argConst? t then
      let c ← mkConstWithFreshMVarLevels n
      if ← isProp (← inferType c) then es := es.push c
      else ns := ns.push n
      continue
    let e ← Tactic.elabTerm t none
    if !(← isProp (← inferType e)) then
      if let some n := e.getAppFn.constName? then
        if let .defnInfo _ ← getConstInfo n then
          ns := ns.push n
          continue
    es := es.push e
  return (ns, es)

/-- Unfold each definition of `ns` in the main goal, where it occurs. -/
def unfoldNames (ns : Array Name) : TacticM Unit := do
  for n in ns do
    evalTactic (← `(tactic| try unfold $(mkIdent n):ident))

/-- Close the main goal by `bind_swap_nf` after unfolding the definitions `ns`, with the
facts `es`. -/
def runBindSwapNfWith (ns : Array Name) (es : Array Expr) : TacticM Unit := do
  unfoldNames ns
  evalTactic (← `(tactic| try (set_option linter.unusedSimpArgs false in
    simp only [CatCrypt.Core.SPComp.monad_bind_eq, CatCrypt.Core.SPComp.monad_pure_eq,
      CatCrypt.Core.SPComp.bind_assoc, CatCrypt.Core.SPComp.pure_bind])))
  if (← getGoals).isEmpty then return
  let g ← getMainGoal
  g.withContext do
    closeGoal (← collectFacts es) g
  replaceMainGoal []

/-- Close the main goal by `bind_swap_nf` with the argument terms `ts` (`elabArgs`). -/
def runBindSwapNf (ts : Array Syntax) : TacticM Unit := do
  let (ns, es) ← withMainContext (elabArgs ts)
  runBindSwapNfWith ns es

@[tactic bindSwapNfStx] def evalBindSwapNf : Tactic := fun stx => do
  let ts : Array Syntax :=
    if stx[1].isNone then #[] else stx[1][1].getSepArgs
  runBindSwapNf ts

/-- `e` with its head unfolded (at most `fuel` times) until it is an application
`CatCrypt.Crypto.Advantage X Y`; the pair `(X, Y)`, or `none`. -/
partial def toAdvantage (e : Expr) (fuel : Nat := 4) : MetaM (Option (Expr × Expr)) := do
  let e := (← instantiateMVars e).headBeta
  if e.isAppOfArity `CatCrypt.Crypto.Advantage 2 then return some (e.appFn!.appArg!, e.appArg!)
  if fuel == 0 then return none
  let some e' ← unfoldDefinition? e | return none
  toAdvantage e' (fuel - 1)

/-- The definitions unfolded before `bind_swap_nf` in a game equality: the head constants
of the two sides and of their arguments (two levels), when they are definitions that are
not instances, projections, theorems or operations of `SPComp`. -/
def gameHeads (ty : Expr) : MetaM (Array Name) := do
  let some (_, lhs, rhs) := (← instantiateMVars ty).eq? | return #[]
  let env ← getEnv
  let mut out := #[]
  let mut todo := #[(lhs, 0), (rhs, 0)]
  while !todo.isEmpty do
    let (e, d) := todo.back!
    todo := todo.pop
    if let some n := e.getAppFn.constName? then
      if let some (.defnInfo _) := env.find? n then
        unless out.contains n || n.getPrefix == `CatCrypt.Core.SPComp || isInstanceCore env n
            || (← isProjectionFn n) do
          out := out.push n
    if d < 2 then
      for a in e.getAppArgs do todo := todo.push (a, d + 1)
  return out

/-- Close a game equality `X = X'`: unfold the definitions `gameHeads` names and the
definitions among the argument terms `ts` (`elabArgs`), reduce the projections by
`dsimp only`, and run `bind_swap_nf` with the facts among `ts`. -/
def closeGameEq (g : MVarId) (ts : Array Syntax) : TacticM Unit := do
  setGoals [g]
  let heads ← g.withContext do gameHeads (← g.getType)
  let (ns, es) ← withMainContext (elabArgs ts)
  unfoldNames (ns.foldl (fun acc n => if acc.contains n then acc else acc.push n) heads)
  evalTactic (← `(tactic| try dsimp only))
  if (← getGoals).isEmpty then return
  runBindSwapNfWith #[] es
  unless (← getGoals).isEmpty do throwError "advantage_eq_nf: a game equality remains"

/-- `advantage_eq_nf [h₁, …]` proves an equality `a = b` of advantages, each side an
application of `CatCrypt.Crypto.Advantage` up to the unfolding of its head (`AdvantageA G₀
G₁ A`, `DDH_Advantage D B`, …): with `a = Advantage X Y` and `b = Advantage X' Y'`, it
proves `X = X'` and `Y = Y'`, or `X = Y'` and `Y = X'` with `Advantage_sym`; each game
equality is closed by unfolding the definitions at the heads of its sides and of their
arguments and the definitions named among the arguments `hᵢ` (unfolded by name, with no
implicit or instance argument elaborated), and by `bind_swap_nf` with the other
arguments. -/
syntax (name := advantageEqNfStx) "advantage_eq_nf" (" [" term,* "]")? : tactic

@[tactic advantageEqNfStx] def evalAdvantageEqNf : Tactic := fun stx => do
  let ts : Array Syntax :=
    if stx[1].isNone then #[] else stx[1][1].getSepArgs
  let g ← getMainGoal
  let adv := `CatCrypt.Crypto.Advantage
  unless (← getEnv).contains adv do
    throwError "advantage_eq_nf: `CatCrypt.Crypto.Advantage` is not in the environment"
  let (x, y, x', y') ← g.withContext do
    let some (_, a, b) := (← instantiateMVars (← g.getType)).eq? |
      throwError "advantage_eq_nf: the goal is not an equality"
    let some (x, y) ← toAdvantage a |
      throwError "advantage_eq_nf: the left side is not an advantage:{indentExpr a}"
    let some (x', y') ← toAdvantage b |
      throwError "advantage_eq_nf: the right side is not an advantage:{indentExpr b}"
    return (x, y, x', y')
  let mut err? : Option Exception := none
  for swap in [false, true] do
    let s ← saveState
    try
      let (h₁, h₂) ← g.withContext do
        let (a, b) := if swap then (y', x') else (x', y')
        let h₁ ← mkFreshExprSyntheticOpaqueMVar (← mkEq x a)
        let h₂ ← mkFreshExprSyntheticOpaqueMVar (← mkEq y b)
        let pf ← mkCongr (← mkCongrArg (mkConst adv) h₁) h₂
        let pf ← if swap then
            mkEqTrans pf (← mkAppM `CatCrypt.Crypto.Advantage_sym #[y', x'])
          else pure pf
        g.assign (← mkExpectedTypeHint pf (← g.getType))
        return (h₁.mvarId!, h₂.mvarId!)
      closeGameEq h₁ ts
      closeGameEq h₂ ts
      setGoals []
      return
    catch e =>
      s.restore
      err? := some e
  if let some e := err? then throw e

end CatCrypt.Tactic.BindSwap

namespace CatCrypt.Tactic.SpecInline

open Lean Meta Elab Tactic

/-- `L` is a bind chain: its head is `SPComp.bind` or `Bind.bind`. -/
def isChain (L : Expr) : Bool :=
  L.isAppOf ``CatCrypt.Core.SPComp.bind || L.isAppOf ``Bind.bind

/-- The head of an operation `op a`: a constant, a projection or a local variable, applied,
when `op a` is not a monad combinator or a sample. -/
def opHead? (R : Expr) : Option Expr :=
  let f := R.getAppFn
  if R.isAppOf ``CatCrypt.Core.SPComp.bind || R.isAppOf ``CatCrypt.Core.SPComp.pure ||
      R.isAppOf ``Bind.bind || R.isAppOf ``Pure.pure ||
      R.isAppOf ``CatCrypt.Core.SPComp.sample then none
  else if f.isConst || f.isProj || f.isFVar then some f
  else none

/-- `T` (a hypothesis type) has the form `∀ xs, … → L = R` with `L` a bind chain and `R`
an operation whose head occurs in `goal`. -/
def specForm (goal T : Expr) : MetaM Bool :=
  forallTelescopeReducing T fun _ body => do
    let some (_, L, R) := body.eq? | return false
    unless isChain L do return false
    let some hd := opHead? R | return false
    return (goal.find? (· == hd)).isSome

/-- A local value for the binder type `d`: a local hypothesis when `d` is a proposition,
an instance by synthesis when `inst`, else a local variable of type `d`; none of `avoid`. -/
def localValue (d : Expr) (inst : Bool) (avoid : Array Expr) : MetaM (Option Expr) := do
  if inst then return ← observing? (synthInstance d)
  for decl in (← getLCtx).decls.toArray.reverse do
    let some decl := decl | continue
    if decl.isImplementationDetail || avoid.contains decl.toExpr then continue
    if ← withReducible (isDefEq decl.type d) then return some decl.toExpr
  return none

/-- The rewrite rule `∀ ys, R = L` obtained from `t : ∀ xs, … → L = R`: the binders listed
in `keep` stay universally quantified, the others are instantiated by `localValue`. -/
partial def buildRule (t T : Expr) (keep : Array Bool) (i : Nat) (kept : Array Expr) :
    MetaM (Option Expr) := do
  let T ← whnfR T
  match T with
  | .forallE n d b bi =>
    if keep.getD i false then
      withLocalDecl n bi d fun x =>
        buildRule (mkApp t x) (b.instantiate1 x) keep (i + 1) (kept.push x)
    else
      let some v ← localValue d bi.isInstImplicit kept | return none
      buildRule (mkApp t v) (b.instantiate1 v) keep (i + 1) kept
  | _ =>
    unless T.isEq do return none
    let r ← mkLambdaFVars kept (← mkEqSymm t)
    if (← instantiateMVars r).hasLooseBVars then return none
    return some r

/-- The rewrite rule of a specification `t : ∀ xs, … → L = R` (see `buildRule`): the
binders that occur in `R` and are not propositions stay quantified. -/
def specRule (t : Expr) : MetaM (Option Expr) := do
  let T ← inferType t
  let keep ← forallTelescopeReducing T fun xs body => do
    let some (_, L, R) := body.eq? | return none
    unless isChain L do return none
    let some hd := opHead? R | return none
    if (L.find? (· == hd)).isSome then return none
    let mut keep : Array Bool := #[]
    for x in xs do
      let xty ← inferType x
      if ← isProp xty then
        -- a premise stays a premise of the rule when it mentions a quantified binder
        keep := keep.push ((xs.zip keep).any fun (y, k) => k && (xty.find? (· == y)).isSome)
      else
        keep := keep.push (R.find? (· == x)).isSome
    return some keep
  let some keep := keep | return none
  buildRule t T keep 0 #[]

/-- The specifications available in the current context: the arguments and the local
hypotheses whose type has the form of `specForm` at `goal`. -/
def specSources (goal : Expr) (extra : Array Expr) : MetaM (Array Expr) := do
  let mut out := #[]
  for t in extra do
    if ← specForm goal (← inferType t) then out := out.push t
  for h in ← getLocalHyps do
    let decl ← h.fvarId!.getDecl
    if decl.isImplementationDetail then continue
    if ← specForm goal (← instantiateMVars decl.type) then out := out.push h
  return out

/-- The local hypotheses that discharge the premises of a rule: propositions that are not
equations, implications or universal statements, such as the case hypotheses of a split. -/
def atomHyps : MetaM (Array Expr) := do
  let mut out := #[]
  for h in ← getLocalHyps do
    let decl ← h.fvarId!.getDecl
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    unless ← isProp ty do continue
    if ty.isForall || ty.isEq || ty.isAppOf ``CatCrypt.Core.SPComp.IsPure then continue
    out := out.push h
  return out

/-- The definitions (not theorems, not constructors, not monad combinators) applied in `e`
to an argument that is a constructor application: their equation lemmas reduce such an
application by `simp only` (a definition by pattern matching applied to `Sum.inr a`). -/
def ctorAppliedDefs (e : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  let mut out : Array Name := #[]
  for t in collectApps e #[] do
    let some f := t.getAppFn.constName? | continue
    if out.contains f || f.getPrefix == ``CatCrypt.Core.SPComp then continue
    unless (env.find? f).any (·.isDefinition) do continue
    if ← t.getAppArgs.anyM fun a => return (← isConstructorApp a) then
      out := out.push f
  return out
where
  /-- The applications in `e`. -/
  collectApps (e : Expr) (acc : Array Expr) : Array Expr :=
    match e with
    | .app f a => collectApps a (collectApps f (if acc.contains e then acc else acc.push e))
    | .lam _ d b _ | .forallE _ d b _ => collectApps b (collectApps d acc)
    | .mdata _ b => collectApps b acc
    | _ => acc

/-- `spec_inline [t₁, …]` proves an `SPComp` equality by splitting its conditionals,
inlining the specifications of abstract operations given by hypotheses as bind chains,
and commuting `IsPure` bindings (see the module docstring). -/
syntax (name := specInlineStx) "spec_inline" (" [" term,* "]")? : tactic

/-- The elaborator of `spec_inline`. -/
@[tactic specInlineStx] def evalSpecInline : Tactic := fun stx => do
  let ts : Array Term := if stx[1].isNone then #[] else stx[1][1].getSepArgs.map (⟨·⟩)
  let g ← getMainGoal
  -- the arguments that are not specifications (or do not elaborate alone) are
  -- normalisation lemmas
  let (extra, norm) ← g.withContext do
    let t ← instantiateMVars (← g.getType)
    unless t.eq?.any (fun (ty, _, _) => ty.isAppOf ``CatCrypt.Core.SPComp) do
      throwError "spec_inline: the goal is not an SPComp equality"
    let mut extra : Array Expr := #[]
    let mut norm : Array Term := #[]
    for s in ts do
      let e? ← observing? (Term.withoutErrToSorry (elabTerm s none))
      match e? with
      | some e =>
        if ← specForm t (← inferType e) then extra := extra.push e else norm := norm.push s
      | none => norm := norm.push s
    if (← specSources t extra).isEmpty then
      throwError "spec_inline: no hypothesis specifies an operation of the goal as a chain"
    return (extra, norm)
  let laws : Array Term := #[``CatCrypt.Core.SPComp.monad_bind_eq,
    ``CatCrypt.Core.SPComp.bind_assoc, ``CatCrypt.Core.SPComp.pure_bind].map
    fun n => ⟨(mkIdent n).raw⟩
  let simpWith (xs : Array Term) : TacticM Unit := do
    let lemmas ← xs.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
    evalTactic (← `(tactic| try simp only [$lemmas,*]))
  simpWith (norm ++ laws)
  evalTactic (← `(tactic| try split_ifs))
  for b in ← getGoals do
    setGoals [b]
    let (rules, atoms) ← b.withContext do
      let t ← instantiateMVars (← b.getType)
      let srcs ← specSources t extra
      let rs ← srcs.filterMapM fun s => (specRule s : MetaM _)
      let atoms ← atomHyps
      return (← rs.mapM fun r => Term.exprToSyntax r,
        ← atoms.mapM fun a => Term.exprToSyntax a)
    simpWith (rules ++ atoms ++ norm ++ laws)
    for b' in ← getGoals do
      let defs ← b'.withContext do
        ctorAppliedDefs (← instantiateMVars (← b'.getType))
      unless defs.isEmpty do
        simpWith (defs.map (fun n => (⟨(mkIdent n).raw⟩ : Term)) ++ norm ++ laws)
    evalTactic (← `(tactic| all_goals first | rfl | bind_swap_nf))
  setGoals []

/-- `le_of_eq_nf [t₁, …]` proves `a ≤ b` between two advantages from the equality
`a = b`, proved by `advantage_eq_nf [t₁, …]`. -/
syntax (name := leOfEqNfStx) "le_of_eq_nf" (" [" term,* "]")? : tactic

macro_rules
  | `(tactic| le_of_eq_nf) => `(tactic| (refine le_of_eq ?_; advantage_eq_nf))
  | `(tactic| le_of_eq_nf [$ts,*]) =>
    `(tactic| (refine le_of_eq ?_; advantage_eq_nf [$ts,*]))

end CatCrypt.Tactic.SpecInline

end

/-! ## Arms of `catcrypt_auto` -/

catcrypt_auto_arm "advantage equality" order 5 := "advantage_eq_nf%GRIND"
catcrypt_auto_arm "SPComp equality" order 5 := "bind_swap_nf%GRIND"
catcrypt_auto_arm "SPComp equality" order 22 := "spec_inline%GRIND"
catcrypt_auto_arm "distance inequality" order 25 le_only := "le_of_eq_nf%GRIND"
