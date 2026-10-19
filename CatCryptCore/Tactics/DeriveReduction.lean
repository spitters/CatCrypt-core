/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Core.SPTree
public import CatCryptCore.Tactics.DeriveTimed

/-!
# Computation trees of `SPComp` reductions

`derive_reduction B` takes a reduction `B` whose result is a computation `SPComp α`, written
with `do`-notation or the constructors `SPComp.pure`, `SPComp.bind`, `SPComp.sample`,
`SPComp.get`, `SPComp.set` and `SPComp.fail`, and whose adversaries are binders
`A : X₁ → … → Xₙ → SPComp Y` (`n ≥ 0`). It

1. reflects the body of `B` into the computation tree `B.tree : … → SPTree α`, in which each
   adversary binder `A` is replaced by a binder `A : X₁ → … → Xₙ → SPTree Y` and each call
   `A x₁ … xₙ` by the call of the tree-valued binder;
2. proves `B.compile_tree : (B.tree xs').compile = B xs`, where `xs` is `xs'` with each
   adversary binder `A` replaced by `fun x₁ … xₙ => (A x₁ … xₙ).compile`; the proof is a term
   checked by the kernel;
3. runs `derive_timed B.tree`, which defines the costed form `B.tree.timed` and proves its
   erasure theorem `B.tree.erase_timed`.

`derive_reduction B (adv := A₁ … Aₖ)` takes the adversaries to be the binders named
`A₁ … Aₖ`; without it, every binder whose type ends in `SPComp` is an adversary.

## Unfolding

The body of `B` is the value of its declaration, eta-expanded to all binders of its type.
A subterm of type `SPComp α` is brought to a head by `whnfR` (which also substitutes `let`s);
a monad operation of the `Monad SPComp` instance (`>>=`, `pure`, `<$>`, `*>`, `<*`, `<*>`) is
projected through the instance at `.instances` transparency; any other definition, including
a top-level `def` written in `do`-notation and a sub-reduction called by `B`, is
delta-unfolded and retried. Unfolding stops at the six `SPComp` constructors, at `ite`,
`dite` and matchers, and at a local. The traversal is that of `reifySPComp`
(`CatCryptCore.Deep.Reflect`), with these additional stops so that `if` and `match` stay
syntax.

## Translation

| `SPComp` subterm               | `SPTree` image                                          |
|---|---|
| `SPComp.pure a`                | `SPTree.ret a`                                          |
| `SPComp.fail`                  | `SPTree.fail`                                           |
| `SPComp.sample β`              | `SPTree.sample β _ _ (fun b => .ret b)`                 |
| `SPComp.get l`                 | `SPTree.get l (fun v => .ret v)`                        |
| `SPComp.set l v`               | `SPTree.set l v (.ret ())`                              |
| `SPComp.bind (sample β) k`     | `SPTree.sample β _ _ (fun b => tree (k b))`             |
| `SPComp.bind (get l) k`        | `SPTree.get l (fun v => tree (k v))`                    |
| `SPComp.bind (set l v) k`      | `SPTree.set l v (tree (k ()))`                          |
| `SPComp.bind c k`, other `c`   | `SPTree.bind (tree c) (fun x => tree (k x))`            |
| `if`, `if h :`, `match`        | the same `if` or `match` over the trees of the branches |
| `A x₁ … xₙ`, `A` an adversary  | `A' x₁ … xₙ`                                            |

Each `match` of the tree is the body of an auxiliary definition `B.tree.match_i` over the
locals it mentions, and the tree calls it. `derive_timed` derives the costed form of the
auxiliary definition on demand, where the `match` is at the top and its erasure theorem is
proved by case splitting, and rewrites with that theorem under the binders of the caller.

Any other subterm of type `SPComp α`, after unfolding, is an unpriced computation: an
abstract primitive `f x : SPComp β` or a field of a structure (`D.keygen`), a local function
into `SPComp` that is not an adversary, a recursive definition, an opaque constant. The
command fails on it and names the subterm; it does not reflect it as an opaque leaf.

## Trees and `RawCode`

The reflection targets `SPTree` directly, not `RawCode` followed by a conversion: `SPTree` is
the tree kind of `derive_timed` (`CatCryptCore.Core.SPTreeTimed`) and has `compile`, while
`RawCode` has an opaque `embed` leaf, a `bind` constructor and a `ULift` on `get` and `put`.

## Proof of the compile equation

The equation is proved by a traversal of the tree beside the unfolded body: `SPTree.bind` by
`SPTree.compile_bind_eq`, a `sample`, `get` or `set` node by `SPTree.compile_sample_eq`,
`SPTree.compile_get_eq`, `SPTree.compile_set_eq` (or the forms `…_ret` for a node with no
continuation), `if` by `SPTree.compile_ite_eq` and `SPTree.compile_dite_eq`, a `match` by the
`split` tactic, and a leaf (`ret`, `fail`, an adversary call) by reflexivity.

## Main definitions

* `derive_reduction B`, `derive_reduction B (adv := A₁ … Aₖ)` — define `B.tree`, prove
  `B.compile_tree`, and run `derive_timed B.tree`

## Main results

* `SPTree.compile_bind_eq`, `SPTree.compile_sample_eq`, `SPTree.compile_get_eq`,
  `SPTree.compile_set_eq`, `SPTree.compile_ite_eq`, `SPTree.compile_dite_eq` — congruence of
  `SPTree.compile` with the tree constructors and combinators
* `SPTree.compile_sample_ret`, `SPTree.compile_get_ret`, `SPTree.compile_set_ret` — a node
  with the trivial continuation compiles to the bare operation
-/

public section

set_option autoImplicit false

namespace CatCrypt.Core.SPTree

variable {α β : Type}

theorem compile_bind_eq {s : SPTree α} {f : α → SPTree β} {c : SPComp α} {k : α → SPComp β}
    (hs : s.compile = c) (hf : ∀ a, (f a).compile = k a) :
    (s.bind f).compile = SPComp.bind c k := by
  rw [compile_bind, hs, funext hf]

theorem compile_sample_eq {fi : Fintype β} {ne : Nonempty β} {k : β → SPTree α}
    {k₀ : β → SPComp α} (h : ∀ b, (k b).compile = k₀ b) :
    (SPTree.sample β fi ne k).compile = SPComp.bind (@SPComp.sample β fi ne) k₀ := by
  simp only [compile, funext h]

theorem compile_sample_ret {fi : Fintype β} {ne : Nonempty β} :
    (SPTree.sample β fi ne fun b => .ret b).compile = @SPComp.sample β fi ne := by
  simp only [compile]
  exact SPComp.bind_pure _

theorem compile_get_eq {l : Location} {k : l.ty → SPTree α} {k₀ : l.ty → SPComp α}
    (h : ∀ v, (k v).compile = k₀ v) :
    (SPTree.get l k).compile = SPComp.bind (SPComp.get l) k₀ := by
  simp only [compile, funext h]

theorem compile_get_ret {l : Location} :
    (SPTree.get l fun v => .ret v).compile = SPComp.get l := by
  simp only [compile]
  exact SPComp.bind_pure _

theorem compile_set_eq {l : Location} {v : l.ty} {t : SPTree α} {k₀ : Unit → SPComp α}
    (h : t.compile = k₀ ()) :
    (SPTree.set l v t).compile = SPComp.bind (SPComp.set l v) k₀ := by
  simp only [compile, h]

theorem compile_set_ret {l : Location} {v : l.ty} :
    (SPTree.set l v (.ret ())).compile = SPComp.set l v := by
  simp only [compile]
  exact SPComp.bind_pure _

theorem compile_ite_eq {p : Prop} [Decidable p] {t e : SPTree α} {t₀ e₀ : SPComp α}
    (ht : t.compile = t₀) (he : e.compile = e₀) :
    (if p then t else e).compile = if p then t₀ else e₀ := by
  split <;> assumption

theorem compile_dite_eq {p : Prop} [Decidable p] {t : p → SPTree α} {e : ¬p → SPTree α}
    {t₀ : p → SPComp α} {e₀ : ¬p → SPComp α} (ht : ∀ h, (t h).compile = t₀ h)
    (he : ∀ h, (e h).compile = e₀ h) :
    (if h : p then t h else e h).compile = if h : p then t₀ h else e₀ h := by
  split
  · exact ht _
  · exact he _

end CatCrypt.Core.SPTree

meta section

namespace CatCrypt.Tactics.DeriveReduction

open Lean Elab Meta Term Command

/-- Fail with the reason a derivation does not go through. -/
def fail {γ : Type} (what : MessageData) : MetaM γ :=
  throwError m!"derive_reduction: {what}"

/-- The constructors of `SPComp`, at which unfolding stops. -/
def spCompCtors : Array Name :=
  #[``CatCrypt.Core.SPComp.pure, ``CatCrypt.Core.SPComp.bind, ``CatCrypt.Core.SPComp.sample,
    ``CatCrypt.Core.SPComp.get, ``CatCrypt.Core.SPComp.set, ``CatCrypt.Core.SPComp.fail]

/-- The constants at which `normalize` stops: the constructors of `SPComp`, `ite`, `dite` and
`SPTree.compile`. -/
def normalizeStops : Array Name :=
  spCompCtors ++ #[``ite, ``dite, ``CatCrypt.Core.SPTree.compile]

/-- The monad operations projected through the `Monad SPComp` instance. -/
def monadOps : Array Name :=
  #[``Bind.bind, ``Pure.pure, ``Functor.map, ``SeqRight.seqRight, ``SeqLeft.seqLeft, ``Seq.seq]

/-- The result type `α` of the computation type `SPComp α`. -/
def spCompArg? (t : Expr) : MetaM (Option Expr) := do
  let t ← whnfR (← instantiateMVars t)
  if t.isAppOfArity ``CatCrypt.Core.SPComp 1 then return some t.appArg! else return none

/-- Bring the computation `e` to a head: a constructor of `SPComp`, `ite`, `dite`, a matcher,
`SPTree.compile` or a local, or a stuck term. -/
partial def normalize (e : Expr) : MetaM Expr := do
  let e ← whnfR (← instantiateMVars e)
  match e.getAppFn with
  | .const c _ =>
    if normalizeStops.contains c then return e
    if ← isMatcher c then return e
    if monadOps.contains c then
      let e' ← withTransparency .instances (whnf e)
      if e' == e then return e
      return ← normalize e'
    match ← unfoldDefinition? e with
    | some e' => normalize e'.headBeta
    | none => return e
  | _ => return e

/-- An adversary: the original binder, the tree-valued binder replacing it, and its arity. -/
structure Adv where
  orig : FVarId
  tree : Expr
  arity : Nat
  deriving Inhabited

/-- The context of a reflection: the adversaries, and the name of the tree, under which the
auxiliary definitions of the matches are named. -/
structure RCtx where
  advs : Array Adv
  base : Name

/-- The locals of `e`, closed under the locals of their types, in context order. -/
partial def closedFVars (es : Array Expr) : MetaM (Array Expr) := do
  let mut seen : FVarIdSet := {}
  let mut todo := (es.foldl collectFVars {}).fvarIds.toList
  while true do
    match todo with
    | [] => break
    | x :: rest =>
      todo := rest
      if seen.contains x then continue
      seen := seen.insert x
      let d ← x.getDecl
      todo := todo ++ (collectFVars {} (← instantiateMVars d.type)).fvarIds.toList
      if let some v := d.value? then
        todo := todo ++ (collectFVars {} (← instantiateMVars v)).fvarIds.toList
  let lctx ← getLCtx
  return (lctx.sortFVarsByContextOrder seen.toArray).map mkFVar

/-- Add the auxiliary definition `name := fun xs => e` over the locals `xs` of `e` of type
`SPTree α`, and return its application to `xs`. -/
def hoist (name : Name) (e α : Expr) : TermElabM Expr := do
  let xs ← closedFVars #[e, α]
  let value ← mkLambdaFVars xs e
  let type ← mkForallFVars xs (mkApp (mkConst ``CatCrypt.Core.SPTree) α)
  let lps := (collectLevelParams (collectLevelParams {} value) type).params.toList
  CatCrypt.Tactics.DeriveTimed.addTimedDef name lps type value
  return mkAppN (mkConst name (lps.map mkLevelParam)) xs

/-- The trailing binders `ys` of a function `k` applied to fresh locals named `n`, and the
body `k ys` with the head beta-reduced. -/
def withBody {γ : Type} (k : Expr) (n : Nat) (cont : Array Expr → Expr → TermElabM γ) :
    TermElabM γ := do
  forallBoundedTelescope (← whnfR (← inferType k)) n fun ys _ => do
    unless ys.size == n do fail m!"`{k}` takes fewer than {n} arguments"
    cont ys (mkAppN k ys).headBeta

/-- `SPTree α`. -/
def treeTy (α : Expr) : Expr := mkApp (mkConst ``CatCrypt.Core.SPTree) α

/-- `SPTree.ret a : SPTree α`. -/
def mkRet (α a : Expr) : Expr := mkApp2 (mkConst ``CatCrypt.Core.SPTree.ret) α a

/-- Fail on an unpriced computation `e`, reached as `orig`. -/
def unpriced {γ : Type} (orig e : Expr) : MetaM γ :=
  fail m!"unpriced computation: the subterm{indentExpr orig}\nunfolds to{indentExpr e}\n\
    which is not built from `pure`, `bind`, `sample`, `get`, `set`, `fail`, `if`, `match` or \
    a call of an adversary"

mutual

/-- The computation tree of the computation `e : SPComp α`. -/
partial def reify (ctx : RCtx) (e : Expr) : TermElabM Expr := do
  let orig := e
  let some α ← spCompArg? (← inferType e)
    | fail m!"`{e}` is not a computation `SPComp α`"
  let e ← normalize e
  let args := e.getAppArgs
  match e.getAppFn with
  | .fvar id =>
    match ctx.advs.find? (·.orig == id) with
    | some a =>
      unless args.size == a.arity do
        fail m!"the adversary `{e.getAppFn}` is applied to {args.size} arguments, not {a.arity}"
      return mkAppN a.tree args
    | none => unpriced orig e
  | .const c _ =>
    if c == ``CatCrypt.Core.SPComp.pure && args.size == 2 then
      return mkRet α args[1]!
    if c == ``CatCrypt.Core.SPComp.fail && args.size == 1 then
      return mkApp (mkConst ``CatCrypt.Core.SPTree.fail) α
    if c == ``CatCrypt.Core.SPComp.sample && args.size == 3 then
      let k ← withLocalDeclD `b args[0]! fun b => mkLambdaFVars #[b] (mkRet args[0]! b)
      return mkApp5 (mkConst ``CatCrypt.Core.SPTree.sample) α args[0]! args[1]! args[2]! k
    if c == ``CatCrypt.Core.SPComp.get && args.size == 1 then
      let k ← withLocalDeclD `v α fun v => mkLambdaFVars #[v] (mkRet α v)
      return mkApp3 (mkConst ``CatCrypt.Core.SPTree.get) α args[0]! k
    if c == ``CatCrypt.Core.SPComp.set && args.size == 2 then
      let unit : Expr := mkConst ``Unit
      return mkApp4 (mkConst ``CatCrypt.Core.SPTree.set) unit args[0]! args[1]!
        (mkRet unit (mkConst ``Unit.unit))
    if c == ``CatCrypt.Core.SPComp.bind && args.size == 4 then
      return ← reifyBind ctx args[0]! args[1]! args[2]! args[3]!
    if c == ``ite && args.size == 5 then
      return mkApp5 (mkConst ``ite [Level.one.succ]) (treeTy α) args[1]! args[2]!
        (← reify ctx args[3]!) (← reify ctx args[4]!)
    if c == ``dite && args.size == 5 then
      let t ← withBody args[3]! 1 fun hs b => do mkLambdaFVars hs (← reify ctx b)
      let f ← withBody args[4]! 1 fun hs b => do mkLambdaFVars hs (← reify ctx b)
      return mkApp5 (mkConst ``dite [Level.one.succ]) (treeTy α) args[1]! args[2]! t f
    if ← isMatcher c then
      return ← reifyMatch ctx e α
    unpriced orig e
  | _ => unpriced orig e

/-- The computation tree of `SPComp.bind c k`, with `c : SPComp α` and `k : α → SPComp β`. -/
partial def reifyBind (ctx : RCtx) (α β c k : Expr) : TermElabM Expr := do
  let c' ← normalize c
  let cargs := c'.getAppArgs
  let cont (x : Expr) : TermElabM Expr := reify ctx (mkApp k x).headBeta
  if c'.isAppOfArity ``CatCrypt.Core.SPComp.sample 3 then
    let k' ← withLocalDeclD `b cargs[0]! fun b => do mkLambdaFVars #[b] (← cont b)
    return mkApp5 (mkConst ``CatCrypt.Core.SPTree.sample) β cargs[0]! cargs[1]! cargs[2]! k'
  if c'.isAppOfArity ``CatCrypt.Core.SPComp.get 1 then
    let k' ← withLocalDeclD `v α fun v => do mkLambdaFVars #[v] (← cont v)
    return mkApp3 (mkConst ``CatCrypt.Core.SPTree.get) β cargs[0]! k'
  if c'.isAppOfArity ``CatCrypt.Core.SPComp.set 2 then
    return mkApp4 (mkConst ``CatCrypt.Core.SPTree.set) β cargs[0]! cargs[1]!
      (← cont (mkConst ``Unit.unit))
  let s ← reify ctx c
  let k' ← withLocalDeclD `x α fun x => do mkLambdaFVars #[x] (← cont x)
  return mkApp4 (mkConst ``CatCrypt.Core.SPTree.bind) α β s k'

/-- The computation tree of the matcher application `e : SPComp α`: the same match, with
motive `SPTree α` and the trees of the alternatives. -/
partial def reifyMatch (ctx : RCtx) (e α : Expr) : TermElabM Expr := do
  let some app ← matchMatcherApp? e | fail m!"`{e}` is not a matcher application"
  unless app.remaining.isEmpty do
    fail m!"the match{indentExpr e}\nis applied to further arguments"
  let dependent ← lambdaTelescope app.motive fun xs b => pure (xs.any fun x => b.containsFVar x.fvarId!)
  if dependent then fail m!"the match{indentExpr e}\nhas a motive that depends on its discriminants"
  let resTy := treeTy α
  let motive ← lambdaTelescope app.motive fun xs _ => mkLambdaFVars xs resTy
  let lvl ← getLevel resTy
  let some i := app.uElimPos?
    | fail m!"the match{indentExpr e}\neliminates only into propositions"
  let levels := app.matcherLevels.set! i lvl
  let matcherType ← instantiateForall
    (← inferType (mkConst app.matcherName levels.toList)) (app.params ++ #[motive] ++ app.discrs)
  let mut alts := #[]
  let mut ty := matcherType
  for a in app.alts, n in app.altNumParams do
    let .forallE _ _ body _ ← whnf ty | fail m!"the match{indentExpr e}\nhas an unexpected type"
    let a' ← withBody a n fun fs b => do mkLambdaFVars fs (← reify ctx b)
    alts := alts.push a'
    ty := body.instantiate1 a'
  let m := mkAppN (mkConst app.matcherName levels.toList)
    (app.params ++ #[motive] ++ app.discrs ++ alts)
  let env ← getEnv
  let mut i := 1
  while env.contains (ctx.base ++ Name.mkSimple s!"match_{i}") do i := i + 1
  hoist (ctx.base ++ Name.mkSimple s!"match_{i}") m α

end

/-- The sides of the goal `SPTree.compile t = r`: the tree `t` and the computation `r`. -/
def goalSides (g : MVarId) : MetaM (Expr × Expr × Expr) := do
  let ty ← instantiateMVars (← g.getType)
  let some (_, lhs, rhs) := ty.eq? | fail m!"the goal is not an equation:{indentExpr ty}"
  unless lhs.isAppOfArity ``CatCrypt.Core.SPTree.compile 2 do
    fail m!"the goal is not a compile equation:{indentExpr ty}"
  return (lhs.getArg! 0, lhs.getArg! 1, rhs)

/-- `SPTree.compile t : SPComp α`. -/
def mkCompile (α t : Expr) : Expr := mkApp2 (mkConst ``CatCrypt.Core.SPTree.compile) α t

/-- A goal `∀ ys, SPTree.compile (f ys) = k₀ ys` over the binders of the function `f`. -/
def mkPointwise (f k₀ : Expr) (n : Nat) (α : Expr) : TermElabM Expr :=
  withBody f n fun ys b => do
    mkForallFVars ys (← mkEq (mkCompile α b) (mkAppN k₀ ys).headBeta)

/-- Assign the proof `pf` to the goal `g`, after checking its type. -/
def close (g : MVarId) (pf : Expr) : MetaM Unit := do
  let pt ← inferType pf
  unless ← isDefEq pt (← g.getType) do
    fail m!"internal: the proof of type{indentExpr pt}\ndoes not prove{indentExpr (← g.getType)}"
  g.assign pf

/-- The constants at which `treeHead` stops. -/
def treeStops : Array Name :=
  #[``CatCrypt.Core.SPTree.ret, ``CatCrypt.Core.SPTree.sample, ``CatCrypt.Core.SPTree.get,
    ``CatCrypt.Core.SPTree.set, ``CatCrypt.Core.SPTree.fail, ``CatCrypt.Core.SPTree.bind, ``ite,
    ``dite]

/-- Bring the tree `t` to a head: a constructor of `SPTree`, `SPTree.bind`, `ite`, `dite`, a
matcher or a local; the auxiliary definitions of matches are unfolded. -/
partial def treeHead (t : Expr) : MetaM Expr := do
  let t ← whnfR (← instantiateMVars t)
  match t.getAppFn with
  | .const c _ =>
    if treeStops.contains c then return t
    if ← isMatcher c then return t
    match ← unfoldDefinition? t with
    | some t' => treeHead t'.headBeta
    | none => return t
  | _ => return t

/-- Prove the goal `SPTree.compile t = r`, where `t` is the tree of the computation `r`. -/
partial def prove (g : MVarId) : TermElabM Unit := g.withContext do
  let (α, t, r) ← goalSides g
  let t ← treeHead t
  let r ← normalize r.headBeta
  let g ← g.replaceTargetDefEq (← mkEq (mkCompile α t) r)
  let targs := t.getAppArgs
  let rargs := r.getAppArgs
  let sub (ty : Expr) (n : Nat) : TermElabM Expr := do
    let h ← mkFreshExprSyntheticOpaqueMVar ty
    let (_, g') ← h.mvarId!.introNP n
    prove g'
    return h
  let core (n : Name) : Expr := mkConst (``CatCrypt.Core.SPTree ++ n)
  match t.getAppFn with
  | .const c _ =>
    if c == ``CatCrypt.Core.SPTree.bind && targs.size == 4 then
      unless r.isAppOfArity ``CatCrypt.Core.SPComp.bind 4 do
        fail m!"internal: the tree{indentExpr t}\nis not matched by{indentExpr r}"
      let (a, b, s, f) := (targs[0]!, targs[1]!, targs[2]!, targs[3]!)
      let c₀ ← normalize rargs[2]!
      let k₀ := rargs[3]!
      let h₁ ← sub (← mkEq (mkCompile a s) c₀) 0
      let h₂ ← sub (← mkPointwise f k₀ 1 b) 1
      return ← close g (mkAppN (core `compile_bind_eq) #[a, b, s, f, c₀, k₀, h₁, h₂])
    if c == ``CatCrypt.Core.SPTree.sample && targs.size == 5 then
      let (a, γ, fi, ne, k) := (targs[0]!, targs[1]!, targs[2]!, targs[3]!, targs[4]!)
      if r.isAppOfArity ``CatCrypt.Core.SPComp.bind 4 then
        let k₀ := rargs[3]!
        let h ← sub (← mkPointwise k k₀ 1 a) 1
        return ← close g (mkAppN (core `compile_sample_eq) #[a, γ, fi, ne, k, k₀, h])
      return ← close g (mkAppN (core `compile_sample_ret) #[γ, fi, ne])
    if c == ``CatCrypt.Core.SPTree.get && targs.size == 3 then
      let (a, l, k) := (targs[0]!, targs[1]!, targs[2]!)
      if r.isAppOfArity ``CatCrypt.Core.SPComp.bind 4 then
        let k₀ := rargs[3]!
        let h ← sub (← mkPointwise k k₀ 1 a) 1
        return ← close g (mkAppN (core `compile_get_eq) #[a, l, k, k₀, h])
      return ← close g (mkAppN (core `compile_get_ret) #[l])
    if c == ``CatCrypt.Core.SPTree.set && targs.size == 4 then
      let (a, l, v, s) := (targs[0]!, targs[1]!, targs[2]!, targs[3]!)
      if r.isAppOfArity ``CatCrypt.Core.SPComp.bind 4 then
        let k₀ := rargs[3]!
        let h ← sub (← mkEq (mkCompile a s) (mkApp k₀ (mkConst ``Unit.unit)).headBeta) 0
        return ← close g (mkAppN (core `compile_set_eq) #[a, l, v, s, k₀, h])
      return ← close g (mkAppN (core `compile_set_ret) #[l, v])
    if c == ``ite && targs.size == 5 then
      unless r.isAppOfArity ``ite 5 do
        fail m!"internal: the tree{indentExpr t}\nis not matched by{indentExpr r}"
      let h₁ ← sub (← mkEq (mkCompile α targs[3]!) rargs[3]!) 0
      let h₂ ← sub (← mkEq (mkCompile α targs[4]!) rargs[4]!) 0
      return ← close g (mkAppN (core `compile_ite_eq)
        #[α, targs[1]!, targs[2]!, targs[3]!, targs[4]!, rargs[3]!, rargs[4]!, h₁, h₂])
    if c == ``dite && targs.size == 5 then
      unless r.isAppOfArity ``dite 5 do
        fail m!"internal: the tree{indentExpr t}\nis not matched by{indentExpr r}"
      let h₁ ← sub (← mkPointwise targs[3]! rargs[3]! 1 α) 1
      let h₂ ← sub (← mkPointwise targs[4]! rargs[4]! 1 α) 1
      return ← close g (mkAppN (core `compile_dite_eq)
        #[α, targs[1]!, targs[2]!, targs[3]!, targs[4]!, rargs[3]!, rargs[4]!, h₁, h₂])
    if ← isMatcher c then
      let gs ← Tactic.run g (Tactic.evalTactic (← `(tactic| split)))
      if gs.isEmpty then return
      for g' in gs do prove g'
      return
    g.refl
  | _ => g.refl

/-- Define `c.tree`, prove `c.compile_tree`, and run `derive_timed c.tree`. The adversaries
are the binders named in `advNames`, or every binder whose type ends in `SPComp` when it is
empty. -/
partial def deriveReduction (c : Name) (advNames : Array Name) : TermElabM Unit := do
  let env ← getEnv
  let some info := env.find? c | fail m!"unknown constant `{c}`"
  let .defnInfo d := info | fail m!"`{c}` is not a definition"
  if (Structural.eqnInfoExt.find? env c).isSome then fail m!"`{c}` is recursive"
  if (WF.eqnInfoExt.find? env c).isSome then fail m!"`{c}` is recursive"
  let treeName := c ++ `tree
  let thmName := c ++ `compile_tree
  if env.contains treeName then fail m!"`{treeName}` already exists"
  let levels := info.levelParams.map mkLevelParam
  -- Eta-expand to all binders of the type.
  let value ← lambdaTelescope d.value fun xs b => do
    forallTelescope (← instantiateForall d.type xs) fun ys _ =>
      mkLambdaFVars (xs ++ ys) (mkAppN b ys).headBeta
  let (tType, tValue, eType, eValue) ← lambdaTelescope value fun xs b => do
    let some α ← spCompArg? (← inferType b)
      | fail m!"the result of `{c}` is not a computation `SPComp α`"
    -- The adversary binders.
    let mut isAdv : Array (Option Nat) := #[]
    for x in xs do
      let n := (← x.fvarId!.getUserName).eraseMacroScopes
      let t ← inferType x
      let ar ← forallTelescope (← whnfR t) fun ys body => do
        return if (← spCompArg? body).isSome then some ys.size else none
      let named := if advNames.isEmpty then true else advNames.contains n
      isAdv := isAdv.push (if named then ar else none)
    for n in advNames do
      unless ← xs.anyM (fun x => return (← x.fvarId!.getUserName).eraseMacroScopes == n) do
        fail m!"`{c}` has no binder `{n}`"
    for x in xs, ar in isAdv do
      if advNames.contains (← x.fvarId!.getUserName).eraseMacroScopes && ar.isNone then
        fail m!"the binder `{x}` is not a function into `SPComp`"
    -- Bind the tree-valued binders.
    let rec go (i : Nat) (bs : Array Expr) (advs : Array Adv) (args : Array Expr) :
        TermElabM (Expr × Expr × Expr × Expr) := do
      if h : i < xs.size then
        let x := xs[i]
        match isAdv[i]! with
        | none => go (i + 1) (bs.push x) advs (args.push x)
        | some ar =>
          let t ← inferType x
          let tt ← forallTelescope (← whnfR t) fun ys body => do
            let some β ← spCompArg? body | fail m!"internal: `{t}`"
            mkForallFVars ys (treeTy β)
          let n ← x.fvarId!.getUserName
          let bi ← x.fvarId!.getBinderInfo
          withLocalDecl n bi tt fun a' => do
            let arg ← forallTelescope (← whnfR t) fun ys body => do
              let some β ← spCompArg? body | fail m!"internal: `{t}`"
              mkLambdaFVars ys (mkCompile β (mkAppN a' ys))
            go (i + 1) (bs.push a') (advs.push ⟨x.fvarId!, a', ar⟩) (args.push arg)
      else
        let tree ← reify ⟨advs, treeName⟩ b
        let tree ← instantiateMVars tree
        for a in advs do
          if tree.containsFVar a.orig then
            fail m!"the adversary `{mkFVar a.orig}` occurs outside a call position in{indentExpr tree}"
        for bnd in bs do
          let bt ← inferType bnd
          for a in advs do
            if bt.containsFVar a.orig then
              fail m!"the type of the binder `{bnd}` depends on the adversary `{mkFVar a.orig}`"
        let tType ← mkForallFVars bs (treeTy α)
        let tValue ← mkLambdaFVars bs tree
        let rhs := mkAppN (mkConst c levels) args
        let goalTy ← mkEq (mkCompile α tree) rhs
        let mv ← mkFreshExprSyntheticOpaqueMVar goalTy
        prove mv.mvarId!
        let pf ← instantiateMVars mv
        if pf.hasSorry then fail m!"the compile equation is not proved"
        if pf.hasExprMVar then fail m!"the compile equation is not proved"
        let lhs := mkCompile α (mkAppN (mkConst treeName levels) bs)
        let eType ← mkForallFVars bs (← mkEq lhs rhs)
        let eValue ← mkLambdaFVars bs pf
        return (tType, tValue, eType, eValue)
    go 0 #[] #[] #[]
  CatCrypt.Tactics.DeriveTimed.addTimedDef treeName info.levelParams tType tValue
  addDecl (Declaration.thmDecl
    { name := thmName, levelParams := info.levelParams, type := eType, value := eValue })
  CatCrypt.Tactics.DeriveTimed.deriveTimed {} treeName

/-- `derive_reduction B` defines the computation tree `B.tree` of the reduction `B`, proves
`B.compile_tree`, and runs `derive_timed B.tree`; `derive_reduction B (adv := A₁ … Aₖ)` takes
the adversaries to be the binders `A₁ … Aₖ`. -/
syntax (name := deriveReductionCmd) "derive_reduction " ident
  (" (" &"adv" " := " ident+ ")")? : command

@[command_elab deriveReductionCmd]
def elabDeriveReduction : CommandElab := fun stx => do
  let advs : Array Name :=
    if stx[2].getNumArgs > 3 then stx[2][3].getArgs.map (·.getId) else #[]
  liftTermElabM do
    let c ← realizeGlobalConstNoOverloadWithInfo stx[1]
    deriveReduction c advs

end CatCrypt.Tactics.DeriveReduction

end
