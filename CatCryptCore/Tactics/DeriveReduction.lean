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
   adversary binder `A` replaced by `fun x₁ … xₙ => (A x₁ … xₙ).compile`, and the primitives
   of `B` (see below) are further binders of the tree; the proof is a term checked by the
   kernel;
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
`dite` and matchers, at a local, and at a projection of a local. The traversal is that of `reifySPComp`
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
| `F y₁ … yₙ`, `F` a primitive   | `p y₁ … yₙ`                                             |

Each `match` of the tree is the body of an auxiliary definition `B.tree.match_i` over the
locals it mentions, and the tree calls it. `derive_timed` derives the costed form of the
auxiliary definition on demand, where the `match` is at the top and its erasure theorem is
proved by case splitting, and rewrites with that theorem under the binders of the caller.

## Primitives

A primitive is a field `S.f ps s` of a structure or class `s` built from binders of `B` that
are not adversaries (`D.keygen`, `kit.enc`, `P.dh.keygen`, a method of a local instance), or a
binder of `B` that is not an adversary. A primitive is a computation primitive when it is
called as a computation `F y₁ … yₙ : SPComp β`, and a data function when it has a function
type whose codomain is not a computation, a type, a proposition or a class. Each primitive
becomes a binder of `B.tree`, after the binders of `B`: a data function `F : X → Y` the binder
`f : X → Y`, a computation primitive the binder `p : Y₁ → … → Yₙ → SPTree β`, and the tree has
`f` and `p` in place of `F`. `B.compile_tree` instantiates `f` by `F` and takes `p` with the
hypothesis `h_p : ∀ ys, (p ys).compile = F ys`:

  `B.compile_tree : ∀ xs' ps, (∀ ys, (p ys).compile = F ys) → … →`
  `  (B.tree xs' Fs ps).compile = B xs`.

`derive_timed` then gives each data function its cost companion `fCost : X → ℕ` and each
computation primitive the costed binder `p : Y₁ → … → SPTree.Timed β` with the cost
companion `pCost : Y₁ → … → ℕ` (none for `n = 0`): the costs of the primitives are parameters
of `B.tree.timed`, and a time bound on it is stated under bounds on these parameters.

The primitives are found by a first reflection pass, which records them; the second pass
reflects over their binders. When the derivation fails, the command derives again with the
data definitions applied to a structure binder or a local instance (`kit.expandPair p`, a
helper `f kit x`) unfolded in the tree, so that the fields and methods used in their bodies
become data-function primitives; the error of the first derivation is reported when both fail.

Any other subterm of type `SPComp α`, after unfolding, is an unpriced computation: a field of
a structure bound inside the body, a recursive definition, an opaque constant. The command
fails on it and names the subterm.

## Trees and `RawCode`

The reflection targets `SPTree` directly, not `RawCode` followed by a conversion: `SPTree` is
the tree kind of `derive_timed` (`CatCryptCore.Core.SPTreeTimed`) and has `compile`, while
`RawCode` has an opaque `embed` leaf, a `bind` constructor and a `ULift` on `get` and `put`.

## Proof of the compile equation

The equation is proved by a traversal of the tree beside the unfolded body: `SPTree.bind` by
`SPTree.compile_bind_eq`, a `sample`, `get` or `set` node by `SPTree.compile_sample_eq`,
`SPTree.compile_get_eq`, `SPTree.compile_set_eq` (or the forms `…_ret` for a node with no
continuation), `if` by `SPTree.compile_ite_eq` and `SPTree.compile_dite_eq`, a `match` by the
`split` tactic, a call of a computation primitive by its hypothesis, and a leaf (`ret`,
`fail`, an adversary call) by reflexivity.

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

/-- A primitive of a reduction: the field `key` of a binder (a projection `S.f ps s`, `s` built
from binders, or a binder that is not an adversary), either a data function (`data`) or a
computation `key y₁ … yₙ : SPComp β` with `n = arity`; with the binder `fv` that replaces it in
the tree and, for a computation, the hypothesis `hyp?` stating
`∀ ys, (fv ys).compile = key ys`. -/
structure Prim where
  key : Expr
  arity : Nat
  data : Bool
  fv : Expr := default
  hyp? : Option Expr := none
  deriving Inhabited

/-- The context of a reflection: the adversaries, the name of the tree, under which the
auxiliary definitions of the matches are named, the binders of the reduction that are not
adversaries, either the reference collecting the primitives (`found?`, the first pass) or
the bound primitives (`prims`, the second pass), and whether data definitions applied to a
structure binder are unfolded (`unfold`). -/
structure RCtx where
  advs : Array Adv
  base : Name
  top : Array FVarId := #[]
  found? : Option (IO.Ref (Array Prim)) := none
  prims : Array Prim := #[]
  unfold : Bool := false

/-- The primitive of `ps` with key `F`, arity `arity` and kind `data`. -/
def findPrim? (ps : Array Prim) (F : Expr) (arity : Nat) (data : Bool) :
    MetaM (Option Prim) := do
  for p in ps do
    if p.data == data && p.arity == arity then
      if p.key == F then return some p
      if ← withReducible (isDefEq p.key F) then return some p
  return none

/-- Record the primitive `p` unless it is already recorded. -/
def recordPrim (r : IO.Ref (Array Prim)) (p : Prim) : MetaM Unit := do
  if (← findPrim? (← r.get) p.key p.arity p.data).isNone then r.modify (·.push p)

/-- A field application `e = S.f ps s a₁ … aₙ` (or `s.i a₁ … aₙ`), where the structure `s` is
built from the binders `top` and mentions one: the field `S.f ps s` and the arguments
`a₁ … aₙ`. -/
def fieldKey? (top : Array FVarId) (e : Expr) : MetaM (Option (Expr × Array Expr)) := do
  let env ← getEnv
  let ok (s : Expr) : Bool :=
    !s.hasLooseBVars && s.hasFVar && (collectFVars {} s).fvarIds.all top.contains
  let args := e.getAppArgs
  match e.getAppFn with
  | .proj S i s =>
    unless ok s do return none
    let some fld := (getStructureFields env S)[i]? | return none
    try
      return some (← mkProjection s fld, args)
    catch _ => return none
  | f@(.const c _) =>
    let some info := env.getProjectionFnInfo? c | return none
    let n := info.numParams
    unless n < args.size do return none
    unless ok args[n]! do return none
    unless (args.extract 0 n).all (fun a => !a.hasLooseBVars) do return none
    return some (mkAppN f (args.extract 0 (n + 1)), args.extract (n + 1) args.size)
  | _ => return none

/-- Whether `t` is the type of a data function: a function type whose codomain is not a
computation, a type, a proposition or a class. -/
def isDataFnType (t : Expr) : MetaM Bool := do
  if ← isTypeFormerType t then return false
  forallTelescope (← whnfR t) fun ys b => do
    if ys.isEmpty then return false
    if (← spCompArg? b).isSome then return false
    if ← isProp b then return false
    if (← isClass? b).isSome then return false
    return true

/-- Whether the data term `x = c a₁ … aₙ` is unfolded before its fields are abstracted: `c` is
a non-recursive definition that is not a projection, an instance, a matcher or a reduction with
a costed form or a registered cost, some `aᵢ` is a binder of `top` whose type is a structure
or a class, and `x` is data, not a computation or a tree. -/
def unfoldsData (top : Array FVarId) (x : Expr) : MetaM Bool := do
  let .const c _ := x.getAppFn | return false
  let env ← getEnv
  let some (.defnInfo _) := env.find? c | return false
  if (env.getProjectionFnInfo? c).isSome then return false
  if ← isMatcher c then return false
  if ← isInstance c then return false
  if (Structural.eqnInfoExt.find? env c).isSome then return false
  if (WF.eqnInfoExt.find? env c).isSome then return false
  if env.contains (c ++ `timedCost) then return false
  if env.contains (c ++ `timed) then return false
  let structArg ← x.getAppArgs.anyM fun a => do
    unless a.isFVar && top.contains a.fvarId! do return false
    let .const S _ := (← whnfR (← inferType a)).getAppFn | return false
    return isStructure env S
  unless structArg do return false
  let t ← whnfR (← inferType x)
  if (← spCompArg? t).isSome then return false
  if t.isAppOf ``CatCrypt.Core.SPTree then return false
  if ← isTypeFormerType t then return false
  if ← isProp t then return false
  return true

/-- Replace each data-function field of `e` by its binder (second pass), or record it (first
pass). With `ctx.unfold`, a data definition applied to a structure binder is unfolded first,
so that the fields used in its body are found. -/
def abstractData (ctx : RCtx) (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun x => do
    let some (F, args) ← fieldKey? ctx.top x | do
      if ctx.unfold && (← unfoldsData ctx.top x) then
        if let some x' ← unfoldDefinition? x then return .visit x'.headBeta
      return .continue
    unless ← isDataFnType (← inferType F) do return .continue
    match ctx.found? with
    | some r =>
      recordPrim r { key := F, arity := 0, data := true }
      return .continue
    | none =>
      match ← findPrim? ctx.prims F 0 true with
      | some p => return .continue (mkAppN p.fv args)
      | none => return .continue)

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
`SPTree α`, with its data-function fields abstracted, and return its application to `xs`; in
the first pass, record the fields and return `SPTree.fail`. -/
def hoist (ctx : RCtx) (name : Name) (e α : Expr) : TermElabM Expr := do
  let e ← abstractData ctx e
  if ctx.found?.isSome then return mkApp (mkConst ``CatCrypt.Core.SPTree.fail) α
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
    which is not built from `pure`, `bind`, `sample`, `get`, `set`, `fail`, `if`, `match`, \
    a call of an adversary or a call of a primitive"

/-- The tree of a call `e : SPComp α` of a primitive: a field `F` of a binder or a binder that
is not an adversary, applied to arguments. In the first pass the primitive is recorded and the
tree is `SPTree.fail`; in the second it is the call of the primitive's binder. -/
def primLeaf? (ctx : RCtx) (e α : Expr) : MetaM (Option Expr) := do
  let args := e.getAppArgs
  let key? ← match e.getAppFn with
    | f@(.fvar id) => pure (if ctx.top.contains id then some (f, args) else none)
    | _ => fieldKey? ctx.top e
  let some (F, args) := key? | return none
  let ar := args.size
  let isComp ← forallBoundedTelescope (← inferType F) ar fun ys b => do
    if ys.size != ar then return false
    return (← spCompArg? b).isSome
  unless isComp do return none
  match ctx.found? with
  | some r =>
    recordPrim r { key := F, arity := ar, data := false }
    for a in args do discard <| abstractData ctx a
    return some (mkApp (mkConst ``CatCrypt.Core.SPTree.fail) α)
  | none =>
    let some p ← findPrim? ctx.prims F ar false | return none
    return some (mkAppN p.fv args)

/-- The tree of a call of a primitive, or a failure naming the unpriced computation. -/
def leafOrFail (ctx : RCtx) (orig e α : Expr) : MetaM Expr := do
  match ← primLeaf? ctx e α with
  | some t => return t
  | none => unpriced orig e

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
    | none => leafOrFail ctx orig e α
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
    leafOrFail ctx orig e α
  | _ => leafOrFail ctx orig e α

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
  hoist ctx (ctx.base ++ Name.mkSimple s!"match_{i}") m α

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

/-- Prove the goal `SPTree.compile t = r`, where `t` is the tree of the computation `r`; `hs`
maps the binder of each computation primitive to its hypothesis. -/
partial def prove (hs : Array (Expr × Expr)) (g : MVarId) : TermElabM Unit := g.withContext do
  let (α, t, r) ← goalSides g
  let t ← treeHead t
  let r ← normalize r.headBeta
  let g ← g.replaceTargetDefEq (← mkEq (mkCompile α t) r)
  let targs := t.getAppArgs
  let rargs := r.getAppArgs
  let sub (ty : Expr) (n : Nat) : TermElabM Expr := do
    let h ← mkFreshExprSyntheticOpaqueMVar ty
    let (_, g') ← h.mvarId!.introNP n
    prove hs g'
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
      for g' in gs do prove hs g'
      return
    g.refl
  | f@(.fvar _) =>
    match hs.find? (·.1 == f) with
    | some (_, h) => close g (mkAppN h targs)
    | none => g.refl
  | _ => g.refl

/-- A name for the binder of the primitive `key`: its field name, or the name of the binder
it is, made distinct from `used`. -/
def primName (key : Expr) (used : Array Name) : MetaM Name := do
  let base : Name ← match key.getAppFn with
    | .const c _ => pure (Name.mkSimple c.lastComponentAsString)
    | .fvar id => return (← id.getUserName).eraseMacroScopes
    | _ => pure `prim
  if !used.contains base then return base
  let mut i := 2
  while used.contains (base.appendIndexAfter i) do i := i + 1
  return base.appendIndexAfter i

/-- Bind the binders of the primitives `found` from position `i`: a data function `f` by a
binder of its type, a computation `F : ∀ ys, SPComp β` by a binder `p : ∀ ys, SPTree β` and the
hypothesis `∀ ys, (p ys).compile = F ys`. -/
partial def withPrims {γ : Type} (found : Array Prim) (i : Nat) (used : Array Name)
    (ps : Array Prim) (k : Array Prim → TermElabM γ) : TermElabM γ := do
  if h : i < found.size then
    let p := found[i]
    let n ← primName p.key used
    let used := used.push n
    let ty ← inferType p.key
    if p.data then
      withLocalDeclD n ty fun f => withPrims found (i + 1) used (ps.push { p with fv := f }) k
    else
      let tt ← forallBoundedTelescope ty p.arity fun ys b => do
        let some β ← spCompArg? b | fail m!"internal: `{ty}`"
        mkForallFVars ys (treeTy β)
      withLocalDeclD n tt fun f => do
        let ht ← forallBoundedTelescope ty p.arity fun ys b => do
          let some β ← spCompArg? b | fail m!"internal: `{ty}`"
          mkForallFVars ys (← mkEq (mkCompile β (mkAppN f ys)) (mkAppN p.key ys))
        withLocalDeclD (n.appendBefore "h_") ht fun hp =>
          withPrims found (i + 1) used (ps.push { p with fv := f, hyp? := some hp }) k
  else k ps

/-- Define `c.tree`, prove `c.compile_tree`, and run `derive_timed c.tree`. The adversaries
are the binders named in `advNames`, or every binder whose type ends in `SPComp` when it is
empty; `unfold` is the unfolding of data definitions of `RCtx`. -/
partial def deriveReduction (c : Name) (advNames : Array Name) (unfold : Bool := false) :
    TermElabM Unit := do
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
        let top := (xs.zip isAdv).filterMap fun (x, a) => if a.isNone then some x.fvarId! else none
        -- First pass: collect the primitives.
        let r ← IO.mkRef (#[] : Array Prim)
        let ctx₁ : RCtx := { advs, base := treeName, top, found? := some r, unfold }
        discard <| abstractData ctx₁ (← instantiateMVars (← reify ctx₁ b))
        let found ← r.get
        let used ← xs.mapM fun x => return (← x.fvarId!.getUserName).eraseMacroScopes
        withPrims found 0 used #[] fun ps => do
        -- Second pass: the tree over the binders of the primitives.
        let ctx : RCtx := { advs, base := treeName, top, prims := ps, unfold }
        let tree ← abstractData ctx (← instantiateMVars (← reify ctx b))
        for a in advs do
          if tree.containsFVar a.orig then
            fail m!"the adversary `{mkFVar a.orig}` occurs outside a call position in{indentExpr tree}"
        for bnd in bs do
          let bt ← inferType bnd
          for a in advs do
            if bt.containsFVar a.orig then
              fail m!"the type of the binder `{bnd}` depends on the adversary `{mkFVar a.orig}`"
        let dps := ps.filter (·.data)
        let cps := ps.filter fun p => !p.data
        let dFvs := dps.map (·.fv)
        let dKeys := dps.map (·.key)
        let cFvs := cps.map (·.fv)
        let hyps := cps.filterMap (·.hyp?)
        let tBs := bs ++ dFvs ++ cFvs
        let tType ← mkForallFVars tBs (treeTy α)
        let tValue ← mkLambdaFVars tBs tree
        let rhs := mkAppN (mkConst c levels) args
        let goalTy ← mkEq (mkCompile α (tree.replaceFVars dFvs dKeys)) rhs
        let mv ← mkFreshExprSyntheticOpaqueMVar goalTy
        prove (cFvs.zip hyps) mv.mvarId!
        let pf ← instantiateMVars mv
        if pf.hasSorry then fail m!"the compile equation is not proved"
        if pf.hasExprMVar then fail m!"the compile equation is not proved"
        let lhs := mkCompile α (mkAppN (mkConst treeName levels) (bs ++ dKeys ++ cFvs))
        let eBs := bs ++ cFvs ++ hyps
        let eType ← mkForallFVars eBs (← mkEq lhs rhs)
        let eValue ← mkLambdaFVars eBs pf
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
    let s ← saveState
    try
      deriveReduction c advs
    catch e =>
      -- Second attempt: unfold the data definitions applied to a structure binder.
      s.restore
      try
        deriveReduction c advs (unfold := true)
      catch _ =>
        s.restore
        throw e

end CatCrypt.Tactics.DeriveReduction

end
