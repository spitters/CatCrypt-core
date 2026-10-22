/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Core.SPTree
public import CatCryptCore.Crypto.SDist
public import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Tactics.DeriveTimedStructure

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

The body of `B` is the value of its declaration, eta-expanded to all binders of its type,
which is reduced through type definitions (a reduction of declared type `DDH_Adversary W`
takes the three binders of `W → W → W → SPComp Bool`). A `let` of first-order data stays a
`let` of the tree, so that `derive_timed` prices its value once; any other `let` is
substituted. A subterm of type `SPComp α` is brought to a head by `whnfR` without `zeta`;
a monad operation of the `Monad SPComp` instance (`>>=`, `pure`, `<$>`, `*>`, `<*`, `<*>`) is
projected through the instance at `.instances` transparency; any other definition, including
a top-level `def` written in `do`-notation and a sub-reduction called by `B`, is
delta-unfolded and retried. A non-recursive definition is unfolded with its non-atomic
first-order data arguments bound by `let`s around its body, so that an argument is priced once
however often the body uses it, and a call `b` of which two projections `b.1`, `b.2` occur among
the arguments is bound once by a `let` (`unfoldShared?`). Unfolding stops at the six `SPComp`
constructors, at `ite`,
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
| `SPComp.initHeap h₀`           | `SPTree.load h₀ (.ret ())`                              |
| `SPComp.bind (initHeap h₀) k`  | `SPTree.load h₀ (tree (k ()))`                          |
| `fun _ => c h₀` (`fixHeap`)    | `SPTree.load h₀ (tree c)`                               |
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
are not adversaries (`D.keygen`, `kit.enc`, `P.dh.keygen`, a computation method of a local
instance), or a binder of `B` that is not an adversary; a method of an algebraic operation
class or of `CryptoWord` on a local instance is not a primitive (`derive_timed` prices it at
one unit, as a call of the abstract interface), while a method of another class on a local
instance (a primitive interface of a protocol) is. A primitive is a computation primitive when
it is
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
reflects over their binders. In the second pass, a data definition applied to a structure binder
whose body (through further such definitions) applies a data-function primitive is unfolded, so
that the field has one binder and one cost companion in the costed form. A function binder of
`B` that the tree does not mention is not a binder of `B.tree`. When the derivation fails, the
command derives again with the
data definitions applied to a structure binder or a local instance (`kit.expandPair p`, a
helper `f kit x`) unfolded in the tree, so that the fields and methods used in their bodies
become data-function primitives; the error of the first derivation is reported when both fail.

A `let` whose value is a field path of the binders (`let 𝒮 := pcs.scheme`) is substituted,
so that the fields applied through it are primitives. A match whose motive depends on its
discriminants (`fun n => SPComp (Fin n → X)`) has the motive `fun n => SPTree (Fin n → X)`.

Any other subterm of type `SPComp α`, after unfolding, is an unpriced computation: a field of
a structure bound inside the body, an opaque constant. The command fails on it and names the
subterm. A binder that is a type in a universe other than `Type` is refused: `SPTree` is a
tree over `Type`.

## Recursive computations

A computation `c` defined by structural recursion (over `List`, `ℕ`, or any inductive type
that the equation compiler recurses on), whether `B` itself or a computation that `B` calls,
is reflected by the same recursion: `c.tree` is the reflection of the body of the equations of
`c`, with each recursive call of `c` a call of `c.tree` and the matches kept in place, and
`c.compile_tree` is proved by induction over `c.tree` (`fun_induction`), each case by the
traversal below with the recursive calls closed by the induction hypotheses. The tree of `c`
takes all binders of `c`, followed by its data and computation primitives; a recursive call
passes the primitives unchanged, so it must pass unchanged every binder that a primitive
mentions. An adversary binder of `c` (a function into `SPComp`) is a tree binder of `c.tree`,
and an adversary argument of a recursive call (a continuation that changes with the
recursion) is reflected; a match on an adversary binds it in each alternative. A call
`c args` in `B` is the call of `c.tree` (derived on demand) at the arguments, with the data
primitives of `c` at the arguments and the binders of `B` for its computation primitives,
which must be fields of binders of `B`; its compile equation is `c.compile_tree`, with the
adversary arguments related by the traversal.

## Structure-valued reductions

A reduction `B : … → S qs` whose result is a structure with a costed mirror `S.Timed`
(`derive_timed_structure S`, `CatCryptCore.Tactics.DeriveTimedStructure`) is derived field by
field. Its body is brought to a constructor application of `S` by `whnf`. A field that is a
proposition is dropped; a type or data field is kept with its value. A computation field
`f : Y₁ → … → Yₙ → SPComp β` is reflected as above into the tree `B.f.tree`, with
`B.f.compile_tree : (B.f.tree …).compile = (B …).f ys`; a tree field
`f : Y₁ → … → Yₙ → T` of a kind of `CatCrypt.Tactics.DeriveTimed.treeKinds` is kept as the
tree `B.f.tree`. A field of a binder whose type is a tree or a function into trees
(`A.choose : PK → OracleAdv D R α`) is a tree primitive: a binder of the type of the field.
All fields share one first pass, so the trees `B.f.tree` take the same binders and
primitives. `derive_timed` derives `B.f.tree.timed`, and

* `B.timed : … → S.Timed qs` is the mirror whose field `f` is `fun ys => (B.f.tree.timed … ys).2`
  and whose companion `fCost` is `fun ys => (B.f.tree.timed … ys).1`;
* `B.erase_timed : … → S.Timed.Erases (B.timed …) (B …)` holds under the hypotheses
  `∀ ys, (p ys).erase.compile = F ys` for each costed computation primitive `p` of a field `F`
  and `∀ ys, (p ys).erase = F ys` for each costed tree primitive, with the data primitives at
  their fields and each adversary at the compilation of the erasure of its costed form.

A field `(B …).f` that is projected in a compile equation is reduced by `normalize`, which
reduces a projection of a term that `whnf` brings to a constructor application.

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
  `B.compile_tree`, and run `derive_timed B.tree`; for a structure-valued `B`, define
  `B.f.tree` for each tree and computation field, `B.timed`, and prove `B.erase_timed`

## Main results

* `SPTree.compile_bind_eq`, `SPTree.compile_sample_eq`, `SPTree.compile_get_eq`,
  `SPTree.compile_set_eq`, `SPTree.compile_ite_eq`, `SPTree.compile_dite_eq` — congruence of
  `SPTree.compile` with the tree constructors and combinators
* `SPTree.compile_sample_ret`, `SPTree.compile_get_ret`, `SPTree.compile_set_ret` — a node
  with the trivial continuation compiles to the bare operation
* `SPTree.compile_load_eq`, `SPTree.compile_load_initHeap_eq`,
  `SPTree.compile_load_initHeap_ret` — a heap reset compiles to `fun _ => c h₀` and to
  `SPComp.initHeap h₀` followed by its continuation
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

theorem compile_load_eq {h₀ : Heap} {t : SPTree α} {c : SPComp α} (h : t.compile = c) :
    (SPTree.load h₀ t).compile = fun _ => c h₀ := by
  rw [compile_load, h]

theorem compile_load_initHeap_eq {h₀ : Heap} {t : SPTree α} {k₀ : Unit → SPComp α}
    (h : t.compile = k₀ ()) :
    (SPTree.load h₀ t).compile = SPComp.bind (CatCrypt.Crypto.SPComp.initHeap h₀) k₀ := by
  funext h'
  simp only [compile_load, h, SPComp.bind, CatCrypt.Crypto.SPComp.initHeap,
    CatCrypt.Prob.SDistr.pure_bind]

theorem compile_load_initHeap_ret {h₀ : Heap} :
    (SPTree.load h₀ (.ret ())).compile = CatCrypt.Crypto.SPComp.initHeap h₀ := by
  funext h'
  simp only [compile_load, compile_ret, SPComp.pure, CatCrypt.Crypto.SPComp.initHeap]

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

/-- The constants at which `normalize` stops: the constructors of `SPComp`, the heap reset
`SPComp.initHeap`, `ite`, `dite` and `SPTree.compile`. -/
def normalizeStops : Array Name :=
  spCompCtors ++ #[``CatCrypt.Crypto.SPComp.initHeap, ``ite, ``dite,
    ``CatCrypt.Core.SPTree.compile]

/-- The result type `α` of the unfolded computation type `Heap → SDistr (α × Heap)`, the type
that a heap reset `fun _ => c h₀` (or a `let` around one) is inferred at. -/
def unfoldedSpCompArg? (t : Expr) : MetaM (Option Expr) := do
  let t ← whnfR (← instantiateMVars t)
  let .forallE _ d b _ := t | return none
  if b.hasLooseBVars then return none
  unless ← isDefEq d (mkConst ``CatCrypt.Core.Heap) do return none
  let p? : Option Expr :=
    if b.isAppOfArity ``CatCrypt.Prob.SDistr 1 then some b.appArg!
    else if b.isAppOfArity ``PMF 1 && b.appArg!.isAppOfArity ``Option 1 then
      some b.appArg!.appArg!
    else none
  let some p := p? | return none
  unless p.isAppOfArity ``Prod 2 do return none
  return some (p.getArg! 0)

/-- The heap reset `fun _ => c h₀`: the computation `c` and the heap `h₀`, when `e` is a
lambda whose body applies a term `c` to a heap `h₀`, neither mentioning the bound heap. -/
def heapReset? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let .lam _ _ body _ := e | return none
  unless body.isApp do return none
  let c := body.appFn!
  let h₀ := body.appArg!
  if c.hasLooseBVars || h₀.hasLooseBVars then return none
  unless ← isDefEq (← inferType h₀) (mkConst ``CatCrypt.Core.Heap) do return none
  return some (c, h₀)

/-- The monad operations projected through the `Monad SPComp` instance. -/
def monadOps : Array Name :=
  #[``Bind.bind, ``Pure.pure, ``Functor.map, ``SeqRight.seqRight, ``SeqLeft.seqLeft, ``Seq.seq]

/-- The result type `α` of the computation type `SPComp α`. -/
def spCompArg? (t : Expr) : MetaM (Option Expr) := do
  let t ← whnfR (← instantiateMVars t)
  if t.isAppOfArity ``CatCrypt.Core.SPComp 1 then return some t.appArg! else return none

/-- Whether `c` is defined by structural or well-founded recursion. -/
def isRecursive (env : Environment) (c : Name) : Bool :=
  (Structural.eqnInfoExt.find? env c).isSome || (WF.eqnInfoExt.find? env c).isSome

/-- The definition `c` applied to `args` unfolded with each argument priced once, by
`CatCrypt.Tactics.DeriveTimed.bindArgsShared`: the non-atomic first-order data arguments are
bound by `let`s, and a call `b` whose projections `b.1`, `b.2` occur in two places among the
arguments is bound once. `none` when `c` is not a non-recursive definition. -/
def unfoldShared? (e : Expr) : MetaM (Option Expr) := do
  let .const c lvls := e.getAppFn | return none
  let env ← getEnv
  let some (.defnInfo dv) := env.find? c | return none
  if isRecursive env c then return none
  unless lvls.length == dv.levelParams.length do return none
  unless dv.value.isLambda do return none
  let v := dv.value.instantiateLevelParams dv.levelParams lvls
  some <$> CatCrypt.Tactics.DeriveTimed.bindArgsShared v e.getAppArgs

/-- Bring the computation `e` to a head: a constructor of `SPComp`, `ite`, `dite`, a matcher,
`SPTree.compile`, a call of a recursive definition, a local or a `let`, or a stuck term. A
definition is unfolded by `unfoldShared?`, so that its arguments stay `let`s priced once. -/
partial def normalize (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if let .const c _ := e.getAppFn then
    if isRecursive (← getEnv) c then return e
  let e ← withConfig (fun c => { c with zeta := false }) <| whnfR e
  if e.isLet then return e
  match e.getAppFn with
  | .const c _ =>
    if normalizeStops.contains c then return e
    if ← isMatcher c then return e
    if isRecursive (← getEnv) c then return e
    if monadOps.contains c then
      let e' ← withTransparency .instances (whnf e)
      if e' == e then return e
      return ← normalize e'
    if let some e' ← unfoldShared? e then return ← normalize e'
    match ← unfoldDefinition? e with
    | some e' => normalize e'.headBeta
    | none => return e
  | .proj _ i s =>
    -- A field of a structure that reduces to a constructor application: the field's value.
    let s' ← whnf s
    if let some cv ← isConstructorApp? s' then
      if let some v := s'.getAppArgs[cv.numParams + i]? then
        return ← normalize (mkAppN v e.getAppArgs).headBeta
    return e
  | _ => return e

/-- `normalize`, with each `let` at the head substituted into its body. -/
partial def normalizeZeta (e : Expr) : MetaM Expr := do
  let e ← normalize e
  if let .letE _ _ v b _ := e then normalizeZeta (b.instantiate1 v) else return e

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
`∀ ys, (fv ys).compile = key ys`. A tree primitive (`tree`) is a field of a binder of the type
of a tree of a kind of `CatCrypt.Tactics.DeriveTimed.treeKinds` or of a function into such
trees (`A.choose : PK → OracleAdv D R α`), recorded with arity `0`; its binder has the type of
the field. -/
structure Prim where
  key : Expr
  arity : Nat
  data : Bool
  tree : Bool := false
  fv : Expr := default
  hyp? : Option Expr := none
  deriving Inhabited

/-- The context of a reflection: the adversaries, the name of the tree, under which the
auxiliary definitions of the matches are named, the binders of the reduction that are not
adversaries, either the reference collecting the primitives (`found?`, the first pass) or
the bound primitives (`prims`, the second pass), and whether data definitions applied to a
structure binder are unfolded (`unfold`). In the reflection of a recursive definition `c`,
`self?` holds `c`, the local standing for its tree and the adversary positions of its binders,
and matches stay in the tree (`hoist` false), so that its recursive calls stay in its body;
`visiting` holds the recursive definitions whose trees are being derived. -/
structure RCtx where
  advs : Array Adv
  base : Name
  top : Array FVarId := #[]
  found? : Option (IO.Ref (Array Prim)) := none
  prims : Array Prim := #[]
  unfold : Bool := false
  self? : Option (Name × Expr × Array (Option Nat)) := none
  hoist : Bool := true
  visiting : NameSet := {}
  /-- Derive the tree `c.tree` and `c.compile_tree` of a recursive computation `c`, with the
  definitions being derived. -/
  deriveRec : Name → NameSet → TermElabM Unit := fun _ _ => pure ()

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
computation, a tree of a registered kind, a type, a proposition or a class. -/
def isDataFnType (t : Expr) : MetaM Bool := do
  if ← isTypeFormerType t then return false
  forallTelescope (← whnfR t) fun ys b => do
    if ys.isEmpty then return false
    if (← spCompArg? b).isSome then return false
    if (← CatCrypt.Tactics.DeriveTimed.treeTy? b).isSome then return false
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

/-- The maximal applications of a constant among the subterms of `e`: an application `f a b`
is listed once, without its partial applications `f a`. -/
def constApps (e : Expr) : Array Expr := Id.run do
  let mut acc := #[]
  let mut todo := #[e]
  while h : todo.size > 0 do
    let s := todo.back
    todo := todo.pop
    match s with
    | .app .. =>
      let f := s.getAppFn
      if f.isConst then acc := acc.push s else todo := todo.push f
      todo := todo ++ s.getAppArgs
    | .lam _ t b _ | .forallE _ t b _ => todo := todo.push t |>.push b
    | .letE _ t v b _ => todo := todo.push t |>.push v |>.push b
    | .mdata _ b | .proj _ _ b => todo := todo.push b
    | _ => pure ()
  return acc

/-- Whether the data term `x`, unfolded through data definitions applied to a structure binder
(at most `fuel` deep), applies one of the data-function primitives `keys`. The table `neg`
records, for an application already searched without success, the largest fuel of that
search; an application is not searched again with that fuel or less. -/
partial def mentionsKey (top : Array FVarId) (keys : Array Expr)
    (neg : IO.Ref (Std.HashMap Expr Nat)) (x : Expr) (fuel : Nat) : MetaM Bool := do
  let apps := constApps x
  if apps.any fun s => keys.any fun k => s == k || (s.isApp && s.getAppFn == k.getAppFn &&
      s.getAppNumArgs > k.getAppNumArgs &&
      mkAppN s.getAppFn (s.getAppArgs.extract 0 k.getAppNumArgs) == k) then
    return true
  if fuel == 0 then return false
  for s in apps do
    if let some f := (← neg.get)[s]? then
      if fuel - 1 ≤ f then continue
    if ← unfoldsData top s then
      if let some s' ← unfoldDefinition? s then
        if ← mentionsKey top keys neg s'.headBeta (fuel - 1) then return true
    neg.modify (·.insert s (fuel - 1))
  return false

/-- Replace each data-function field of `e` by its binder (second pass), or record it (first
pass). A data definition applied to a structure binder is unfolded first, by `unfoldShared?`,
when its body applies a data-function primitive found by the first pass (so that the field has
one binder and one cost companion), and with `ctx.unfold` always, so that the fields used in
its body are found. The search `mentionsKey` runs only when there are such primitives. -/
def abstractData (ctx : RCtx) (e : Expr) : MetaM Expr := do
  let keys := (ctx.prims.filter (·.data)).map (·.key)
  let neg ← IO.mkRef ({} : Std.HashMap Expr Nat)
  Meta.transform e (pre := fun x => do
    let some (F, args) ← fieldKey? ctx.top x | do
      if ← unfoldsData ctx.top x then
        let unfold ← if ctx.unfold then pure true
          else if keys.isEmpty then pure false
          else mentionsKey ctx.top keys neg x 8
        if unfold then
          if let some x' ← unfoldShared? x then return .visit x'
          if let some x' ← unfoldDefinition? x then return .visit x'.headBeta
      return .continue
    unless ← isDataFnType (← inferType F) do return .continue
    -- A method of an algebraic operation class (or of `CryptoWord`) is one call of an
    -- abstract interface, priced at one unit by `derive_timed`: not a primitive.
    if let .const fc _ := F.getAppFn then
      if let some finfo := (← getEnv).getProjectionFnInfo? fc then
        if finfo.fromClass && CatCrypt.Tactics.DeriveTimed.isUnitMethod fc then
          return .continue
    match ctx.found? with
    | some r =>
      recordPrim r { key := F, arity := 0, data := true }
      return .continue
    | none =>
      match ← findPrim? ctx.prims F 0 true with
      | some p => return .continue (mkAppN p.fv args)
      | none => return .continue)

/-- Replace each tree-valued field of `e` (a field of a binder whose type is a tree or a
function into trees, `A.choose`) by its binder (second pass), or record it as a tree primitive
(first pass). -/
def abstractTree (ctx : RCtx) (e : Expr) : MetaM Expr := do
  Meta.transform e (pre := fun x => do
    let some (F, args) ← fieldKey? ctx.top x | return .continue
    let isTree ← forallTelescope (← whnfR (← inferType F)) fun _ b => do
      return (← CatCrypt.Tactics.DeriveTimed.treeTy? b).isSome
    unless isTree do return .continue
    match ctx.found? with
    | some r =>
      recordPrim r { key := F, arity := 0, data := false, tree := true }
      return .continue
    | none =>
      match ctx.prims.find? fun p => p.tree && p.key == F with
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

/-- `SPTree.compile t : SPComp α`. -/
def mkCompile (α t : Expr) : Expr := mkApp2 (mkConst ``CatCrypt.Core.SPTree.compile) α t

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

/-- Whether `v` is a field path of the binders `top`: a binder of `top`, or a projection of a
field path. -/
partial def isTopPath (top : Array FVarId) (v : Expr) : Bool :=
  match v.consumeMData with
  | .fvar id => top.contains id
  | .proj _ _ s => isTopPath top s
  | s =>
    match s.getAppFn with
    | .const _ _ => s.getAppNumArgs > 0 && isTopPath top s.appArg! &&
        s.getAppArgs.pop.all (fun a => !a.hasFVar || a.isFVar)
    | _ => false

/-- The adversary positions of the binders `xs` of a computation: the arity of each binder
whose type is a function into `SPComp` (among the binders named `advNames`, or all when it is
empty). -/
def advPositions (xs : Array Expr) (advNames : Array Name) : MetaM (Array (Option Nat)) := do
  xs.mapM fun x => do
    let n := (← x.fvarId!.getUserName).eraseMacroScopes
    let ar ← forallTelescope (← whnfR (← inferType x)) fun ys body => do
      return if (← spCompArg? body).isSome then some ys.size else none
    return if advNames.isEmpty || advNames.contains n then ar else none

/-- The binders of the computation `c`, as `deriveReduction` takes them: the binders of its
value eta-expanded through the type definitions of its type, continued in `k`. -/
def withCompBinders {γ : Type} (c : Name) (lvls : List Level)
    (k : Array Expr → TermElabM γ) : TermElabM γ := do
  let info ← getConstInfo c
  let type := info.type.instantiateLevelParams info.levelParams lvls
  forallTelescope type fun xs b => do
    CatCrypt.Tactics.DeriveTimed.withTypeBinders b fun ys _ => k (xs ++ ys)

mutual

/-- The computation tree of the computation `e : SPComp α`. -/
partial def reify (ctx : RCtx) (e : Expr) : TermElabM Expr := do
  let orig := e
  -- A heap reset `fun _ => c h₀`, or a `let` around one, has the unfolded type
  -- `Heap → SDistr (α × Heap)`.
  let ty ← inferType e
  let some α ← do
      if let some α ← spCompArg? ty then pure (some α) else unfoldedSpCompArg? ty
    | fail m!"`{e}` is not a computation `SPComp α`"
  let e ← normalize e
  if let .letE n t v b _ := e then
    -- A `let` of a field path of the binders (`let 𝒮 := pcs.scheme`) costs nothing to
    -- evaluate and is substituted, so that the fields applied through it are primitives.
    if (← CatCrypt.Tactics.DeriveTimed.keepsLet t v) && !(isTopPath ctx.top v) then
      -- The first pass records the primitives of the value at the `let`, where a substituted
      -- value would have recorded them at its first use.
      if ctx.found?.isSome then discard <| abstractData ctx v
      return ← withLocalDeclD n t fun x => do
        let body ← instantiateMVars (← reify ctx (b.instantiate1 x))
        return .letE n t v (body.abstract #[x]) false
    return ← reify ctx (b.instantiate1 v)
  if let some (c, h₀) ← heapReset? e then
    return mkApp3 (mkConst ``CatCrypt.Core.SPTree.load) α h₀ (← reify ctx c)
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
    if c == ``CatCrypt.Crypto.SPComp.initHeap && args.size == 1 then
      let unit : Expr := mkConst ``Unit
      return mkApp3 (mkConst ``CatCrypt.Core.SPTree.load) unit args[0]!
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
    if isRecursive (← getEnv) c then
      return ← reifyRecCall ctx e c args α
    leafOrFail ctx orig e α
  | _ => leafOrFail ctx orig e α

/-- The tree `fun ys => tree (a ys)` of an adversary argument `a : Y₁ → … → Yₙ → SPComp β`. -/
partial def reifyAdvArg (ctx : RCtx) (a : Expr) (n : Nat) : TermElabM Expr :=
  withBody a n fun ys b => do mkLambdaFVars ys (← reify ctx b)

/-- The tree of a call `c args` of a recursive computation `c`: the call of the local standing
for the tree in the reflection of `c` itself, and otherwise the call of the tree `c.tree`
(derived on demand) at the arguments, with each adversary argument reflected, followed by the
data and computation primitives of `c` at the arguments: a data primitive is passed as its
value (abstracted with the fields of the reduction), a computation primitive as the binder of
the same primitive of the reduction. -/
partial def reifyRecCall (ctx : RCtx) (e : Expr) (c : Name) (args : Array Expr) (α : Expr) :
    TermElabM Expr := do
  if let some (s, recF, advPos) := ctx.self? then
    if s == c then
      unless args.size == advPos.size do
        fail m!"the recursive call{indentExpr e}\nis applied to {args.size} arguments, not \
          {advPos.size}"
      let args' ← (args.zip advPos).mapM fun (a, ar?) => do
        match ar? with
        | some n => reifyAdvArg ctx a n
        | none => pure a
      return mkAppN recF args'
  let lvls := e.getAppFn.constLevels!
  if ctx.visiting.contains c then
    fail m!"`{c}` is reached again while its tree is derived (mutual recursion)"
  unless (← getEnv).contains (c ++ `compile_tree) do
    try ctx.deriveRec c (ctx.visiting.insert c)
    catch ex =>
      throwError m!"derive_reduction: while deriving the tree of the recursive computation \
        `{c}`:\n{ex.toMessageData}"
  let (nx, advPos) ← withCompBinders c lvls fun xs => do
    return (xs.size, ← advPositions xs #[])
  unless args.size == nx do
    fail m!"the recursive computation `{c}` is applied to {args.size} arguments in{indentExpr e}\n\
      and takes {nx}"
  let args' ← (args.zip advPos).mapM fun (a, ar?) => do
    match ar? with
    | some n => reifyAdvArg ctx a n
    | none => pure a
  let thm := Lean.mkConst (c ++ `compile_tree) lvls
  let ct ← instantiateForall (← inferType thm) args'
  -- The data and computation primitives of `c` at the call.
  let (dKeys, cKeys) ← forallTelescope ct fun zs body => do
    let nc := zs.size / 2
    let some (_, lhs, _) := body.eq? | fail m!"internal: `{c ++ `compile_tree}`"
    let targs := lhs.appArg!.getAppArgs
    let dKeys := targs.extract nx (targs.size - nc)
    let cKeys ← (zs.extract nc zs.size).mapM fun h => do
      forallTelescope (← inferType h) fun ys eq => do
        let some (_, _, F) := eq.eq? | fail m!"internal: `{c ++ `compile_tree}`"
        let Fargs := F.getAppArgs
        return (mkAppN F.getAppFn (Fargs.extract 0 (Fargs.size - ys.size)), ys.size)
    for k in dKeys ++ cKeys.map (·.1) do
      if zs.any (k.containsFVar ·.fvarId!) then
        fail m!"internal: a primitive of `{c}` depends on another primitive"
    return (dKeys, cKeys)
  match ctx.found? with
  | some r =>
    for a in args' ++ dKeys do discard <| abstractData ctx a
    for (k, ar) in cKeys do
      let isPrim := match k.getAppFn with
        | .fvar id => ctx.top.contains id
        | _ => true
      unless isPrim && (k.getAppFn.isFVar || (← fieldKey? ctx.top k).isSome) do
        fail m!"the computation `{k}` of the recursive computation `{c}` is not a field of a \
          binder of the reduction"
      recordPrim r { key := k, arity := ar, data := false }
    return mkApp (mkConst ``CatCrypt.Core.SPTree.fail) α
  | none =>
    let cArgs ← cKeys.mapM fun (k, ar) => do
      let some p ← findPrim? ctx.prims k ar false
        | fail m!"internal: the computation `{k}` of `{c}` has no binder"
      return p.fv
    return mkAppN (Lean.mkConst (c ++ `tree) lvls) (args' ++ dKeys ++ cArgs)

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
  if c'.isAppOfArity ``CatCrypt.Crypto.SPComp.initHeap 1 then
    return mkApp3 (mkConst ``CatCrypt.Core.SPTree.load) β cargs[0]! (← cont (mkConst ``Unit.unit))
  let s ← reify ctx c
  let k' ← withLocalDeclD `x α fun x => do mkLambdaFVars #[x] (← cont x)
  return mkApp4 (mkConst ``CatCrypt.Core.SPTree.bind) α β s k'

/-- The computation tree of the matcher application `e : SPComp α`: the same match, with
motive `SPTree α` (`fun xs => SPTree (τ xs)` for a motive `fun xs => SPComp (τ xs)` that
depends on the discriminants) and the trees of the alternatives. -/
partial def reifyMatch (ctx : RCtx) (e α : Expr) : TermElabM Expr := do
  let some app ← matchMatcherApp? e | fail m!"`{e}` is not a matcher application"
  unless app.remaining.isEmpty do
    fail m!"the match{indentExpr e}\nis applied to further arguments"
  let resTy := treeTy α
  let motive ← lambdaTelescope app.motive fun xs b => do
    if xs.any fun x => b.containsFVar x.fvarId! then
      let some τ ← spCompArg? b
        | fail m!"the match{indentExpr e}\nhas a motive that depends on its discriminants"
      mkLambdaFVars xs (treeTy τ)
    else mkLambdaFVars xs resTy
  let lvl ← getLevel resTy
  let some i := app.uElimPos?
    | fail m!"the match{indentExpr e}\neliminates only into propositions"
  let levels := app.matcherLevels.set! i lvl
  -- An adversary as a discriminant (a definition by pattern matching on its adversary
  -- binder): the discriminant is the compilation `fun ys => (A' ys).compile` of its tree, and
  -- the field of an alternative that binds it (the one field of its type) is the adversary.
  let mut discrs := app.discrs
  let mut advDiscrs : Array Adv := #[]
  for d in app.discrs, k in [0:app.discrs.size] do
    let .fvar id := d.consumeMData | continue
    let some a := ctx.advs.find? (·.orig == id) | continue
    let compiled ← forallTelescope (← whnfR (← inferType d)) fun ys body => do
      let some β ← spCompArg? body | fail m!"internal: the adversary `{d}`"
      mkLambdaFVars ys (mkCompile β (mkAppN a.tree ys))
    discrs := discrs.set! k compiled
    advDiscrs := advDiscrs.push a
  let matcherType ← instantiateForall
    (← inferType (mkConst app.matcherName levels.toList)) (app.params ++ #[motive] ++ discrs)
  let mut alts := #[]
  let mut ty := matcherType
  let mut allBound := true
  for a in app.alts, n in app.altNumParams do
    let .forallE _ _ body _ ← whnf ty | fail m!"the match{indentExpr e}\nhas an unexpected type"
    let (a', bound) ← withBody a n fun fs b => do
      let mut b := b
      let mut bound := true
      for adv in advDiscrs do
        let advTy ← inferType (mkFVar adv.orig)
        let cands ← fs.filterM fun f => do isDefEq (← inferType f) advTy
        if h : cands.size = 1 then b := b.replaceFVar cands[0] (mkFVar adv.orig)
        else bound := false
      return (← mkLambdaFVars fs (← reify ctx b), bound)
    allBound := allBound && bound
    alts := alts.push a'
    ty := body.instantiate1 a'
  -- In the reflection of a recursive definition, whose cases the induction unfolds, an
  -- adversary discriminant that every alternative binds to the adversary is not used: it is
  -- `fun ys => SPComp.fail`, which has no cost.
  if allBound && ctx.self?.isSome then
    for d in app.discrs, k in [0:app.discrs.size] do
      let .fvar id := d.consumeMData | continue
      unless ctx.advs.any (·.orig == id) do continue
      let unused ← forallTelescope (← whnfR (← inferType d)) fun ys body => do
        let some β ← spCompArg? body | fail m!"internal: the adversary `{d}`"
        mkLambdaFVars ys (← mkAppOptM ``CatCrypt.Core.SPComp.fail #[some β])
      discrs := discrs.set! k unused
  let m := mkAppN (mkConst app.matcherName levels.toList)
    (app.params ++ #[motive] ++ discrs ++ alts)
  -- In the reflection of a recursive definition the match stays in the tree, with the
  -- recursive calls in its alternatives.
  unless ctx.hoist do return ← abstractData ctx m
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
    ``CatCrypt.Core.SPTree.set, ``CatCrypt.Core.SPTree.fail, ``CatCrypt.Core.SPTree.load,
    ``CatCrypt.Core.SPTree.bind, ``ite, ``dite]

/-- Bring the tree `t` to a head: a constructor of `SPTree`, `SPTree.bind`, `ite`, `dite`, a
matcher or a local; the auxiliary definitions of matches are unfolded. -/
partial def treeHead (t : Expr) : MetaM Expr := do
  let t ← instantiateMVars t
  if let .const c _ := t.getAppFn then
    if isRecursive (← getEnv) c then return t
  let t ← whnfR t
  match t.getAppFn with
  | .const c _ =>
    if treeStops.contains c then return t
    if ← isMatcher c then return t
    if isRecursive (← getEnv) c then return t
    match ← unfoldDefinition? t with
    | some t' => treeHead t'.headBeta
    | none => return t
  | _ => return t

/-- `funext` over the locals `ys`: from `pf : lhs = rhs` under `ys`, a proof of
`(fun ys => lhs) = (fun ys => rhs)`; `pf` itself when `ys` is empty. -/
partial def mkFunExtN (ys : Array Expr) (pf : Expr) : MetaM Expr := do
  if ys.isEmpty then return pf
  let inner ← mkFunExtN (ys.extract 1 ys.size) pf
  mkFunExt (← mkLambdaFVars #[ys[0]!] inner)

mutual

/-- Prove the goal `SPTree.compile t = r`, where `t` is the tree of the computation `r`; `hs`
maps the binder of each computation primitive to its hypothesis. -/
partial def prove (hs : Array (Expr × Expr)) (g : MVarId) : TermElabM Unit := g.withContext do
  let (α, t, r) ← goalSides g
  let t ← treeHead t
  let r ← normalizeZeta r.headBeta
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
    if c == ``CatCrypt.Core.SPTree.load && targs.size == 3 then
      let (a, h₀, s) := (targs[0]!, targs[1]!, targs[2]!)
      if r.isAppOfArity ``CatCrypt.Core.SPComp.bind 4 then
        let k₀ := rargs[3]!
        let h ← sub (← mkEq (mkCompile a s) (mkApp k₀ (mkConst ``Unit.unit)).headBeta) 0
        return ← close g (mkAppN (core `compile_load_initHeap_eq) #[a, h₀, s, k₀, h])
      if r.isAppOfArity ``CatCrypt.Crypto.SPComp.initHeap 1 then
        return ← close g (mkAppN (core `compile_load_initHeap_ret) #[h₀])
      let some (c₀, _) ← heapReset? r
        | fail m!"internal: the tree{indentExpr t}\nis not matched by{indentExpr r}"
      let h ← sub (← mkEq (mkCompile a s) c₀) 0
      return ← close g (mkAppN (core `compile_load_eq) #[a, h₀, s, c₀, h])
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
    if let .str c' "tree" := c then
      if isRecursive (← getEnv) c then
        return ← proveRecLeaf hs g c' α t r
    g.refl
  | f@(.fvar _) =>
    match hs.find? (·.1 == f) with
    | some (_, h) => close g (mkAppN h targs)
    | none =>
      -- The hypothesis of the primitive among the locals (reintroduced by an induction).
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        let pf := mkAppN d.toExpr targs
        let ok ← try
            let ty ← inferType pf
            isDefEq ty (← g.getType)
          catch _ => pure false
        if ok then return ← close g pf
      g.refl
  | _ => g.refl

/-- Close the goal `g : (c.tree targs).compile = r` at a call of the tree of the recursive
computation `c`: by an induction hypothesis among the locals whose tree is `c.tree targs`, or
by `c.compile_tree` with its hypotheses on the primitives found among the locals. The
equation's right side `c rargs'` differs from `r = c rargs` in the adversary arguments, which
are the compilations `fun ys => (T ys).compile` of the trees `T` of the arguments of `r`. -/
partial def proveRecLeaf (hs : Array (Expr × Expr)) (g : MVarId) (c : Name) (α t r : Expr) :
    TermElabM Unit := g.withContext do
  let lhs := mkCompile α t
  -- An induction hypothesis.
  let mut pf? : Option Expr := none
  for d in ← getLCtx do
    if pf?.isSome then break
    if d.isImplementationDetail then continue
    for e in ← CatCrypt.Tactics.DeriveTimed.conjEqns d.toExpr d.type do
      let some (_, l, _) := (← instantiateMVars (← inferType e)).eq? | continue
      if ← isDefEq l lhs then
        pf? := some e
        break
  let pf ← match pf? with
    | some pf => pure pf
    | none =>
      let thm ← mkConstWithFreshMVarLevels (c ++ `compile_tree)
      let (ms, _, body) ← forallMetaTelescope (← inferType thm)
      let some (_, l, _) := body.eq? | fail m!"internal: `{c ++ `compile_tree}`"
      unless ← isDefEq l lhs do
        fail m!"internal: `{c ++ `compile_tree}` does not apply to{indentExpr lhs}"
      for m in ms do
        if (← instantiateMVars m).isMVar then
          let mty ← instantiateMVars (← inferType m)
          let mut found := false
          for d in ← getLCtx do
            if d.isImplementationDetail then continue
            if ← isDefEq d.type mty then
              m.mvarId!.assign d.toExpr
              found := true
              break
          unless found do
            fail m!"the hypothesis{indentExpr mty}\nof `{c ++ `compile_tree}` is not among \
              the hypotheses of the reduction"
      instantiateMVars (mkAppN thm ms)
  -- The right sides agree up to the adversary arguments.
  let some (_, _, r') := (← instantiateMVars (← inferType pf)).eq?
    | fail m!"internal: `{pf}` is not an equation"
  let r ← instantiateMVars r
  if ← isDefEq r' r then return ← close g pf
  let fn := r'.getAppFn
  let a' := r'.getAppArgs
  let a := r.getAppArgs
  unless a'.size == a.size && (← isDefEq fn r.getAppFn) do
    fail m!"internal: the call{indentExpr r'}\ndoes not match{indentExpr r}"
  let mut cur := a'
  let mut proof := pf
  for i in [0:a.size] do
    if ← isDefEq cur[i]! a[i]! then continue
    -- `fun ys => (T ys).compile = a[i]`, pointwise by the reflection proof.
    let e ← lambdaTelescope cur[i]! fun ys b => do
      unless b.isAppOfArity ``CatCrypt.Core.SPTree.compile 2 do
        fail m!"internal: the argument{indentExpr cur[i]!}\nis not a compiled tree"
      let ty ← mkForallFVars ys (← mkEq b (mkAppN a[i]! ys).headBeta)
      let h ← mkFreshExprSyntheticOpaqueMVar ty
      let (_, g') ← h.mvarId!.introNP ys.size
      prove hs g'
      let h ← instantiateMVars h
      -- `(fun ys => (T ys).compile) = fun ys => a[i] ys`, and `a[i]` is its eta-expansion.
      mkFunExtN ys (mkAppN h ys)
    let motive ← withLocalDeclD `z (← inferType a[i]!) fun z => do
      mkLambdaFVars #[z] (mkAppN fn (cur.set! i z))
    proof ← mkEqTrans proof (← mkCongrArg motive e)
    cur := cur.set! i a[i]!
  close g proof

end

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
    if p.data || p.tree then
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

/-- A field of a structure-valued reduction: its name, its kind, its value in the body, the
binders `ys` of a tree or computation field, the field's body at `ys`, and its result type. -/
structure SField where
  name : Name
  kind : CatCrypt.Tactics.DeriveTimedStructure.FieldKind
  value : Expr
  ys : Array Expr := #[]
  body : Expr := default
  deriving Inhabited

/-- The arguments of an equation `rhs` under the existential quantifiers of `e`, continued in
`k` with the locals standing for the quantified variables. -/
partial def withExistsBody {γ : Type} (e : Expr) (k : Array Expr → Expr → TermElabM γ)
    (acc : Array Expr := #[]) : TermElabM γ := do
  if e.isAppOfArity ``Exists 2 then
    match e.appArg! with
    | .lam n t b _ => withLocalDeclD n t fun h => withExistsBody (b.instantiate1 h) k (acc.push h)
    | _ => fail m!"internal: an existential quantifier over a non-lambda"
  else k acc e

/-- Define `c.timed` from the costed forms `c.f.tree.timed` of the fields, and prove
`c.erase_timed`. `xs` are the binders of `c`, `bsOrig` the same with each adversary replaced by
its tree-valued binder, `kept` those the trees take, and `ps` the primitives. -/
partial def assembleStruct (c : Name) (levels : List Level) (levelParams : List Name) (S : Name)
    (lvlsS : List Level) (qs : Array Expr) (mirrorFields : Array Name) (fields : Array SField)
    (xs bsOrig : Array Expr) (advs : Array Adv)
    (kept : Array Expr) (ps : Array Prim) : TermElabM Unit := do
  let env ← getEnv
  let timedS := S ++ `Timed
  let dps := ps.filter (·.data)
  let pps := ps.filter fun p => !p.data
  let cps := pps.filter fun p => !p.tree
  let tBs := kept ++ dps.map (·.fv) ++ pps.map (·.fv)
  CatCrypt.Tactics.DeriveTimed.withBinders {} tBs fun tctx bs _ => do
  let costed (fv : Expr) : TermElabM Expr := do
    let some info := tctx.locals.get? fv.fvarId! | fail m!"internal: `{fv}` has no costed form"
    return info.value
  -- The field paths whose cost companions the costed forms of the fields take
  -- (`c.f.tree.timed.fieldPaths`), one companion binder of `c.timed` per path.
  let mut allPaths : Array Expr := #[]
  let mut fieldPaths : Array (Name × Array Expr) := #[]
  for fd in fields do
    unless fd.kind matches .tree _ | .comp _ do continue
    let fpName := c ++ fd.name ++ `tree ++ `timed ++ `fieldPaths
    unless env.contains fpName do continue
    let some fp ← unfoldDefinition? (mkAppN (Lean.mkConst fpName levels) (tBs ++ fd.ys))
      | fail m!"internal: `{fpName}` does not unfold"
    let mut tup := fp.headBeta
    let mut paths := #[]
    while tup.isAppOfArity ``PProd.mk 4 do
      let p := tup.getArg! 2
      for y in fd.ys do
        if p.containsFVar y.fvarId! then
          fail m!"the costed form of the field `{fd.name}` takes the cost of the field `{p}`, \
            which depends on the arguments of the field"
      paths := paths.push p
      unless allPaths.contains p do allPaths := allPaths.push p
      tup := (tup.getArg! 3).headBeta
    fieldPaths := fieldPaths.push (fd.name, paths)
  let compDecls ← allPaths.mapM fun p => do
    return (← CatCrypt.Tactics.DeriveTimed.fieldCostName p,
      fun _ => do CatCrypt.Tactics.DeriveTimed.companionType (← inferType p))
  withLocalDeclsD compDecls fun comps => do
  let compsOf (n : Name) : Array Expr :=
    match fieldPaths.find? (·.1 == n) with
    | some (_, ps) => ps.filterMap fun p => (allPaths.idxOf? p).map (comps[·]!)
    | none => #[]
  -- The costed form.
  let mut mvals : Array Expr := #[]
  for fd in fields do
    match fd.kind with
    | .prop => pure ()
    | .type | .data =>
      for x in xs do
        if fd.value.containsFVar x.fvarId! && !bs.contains x then
          fail m!"the field `{fd.name}` of the result mentions `{x}`, which the costed form \
            does not take"
      mvals := mvals.push fd.value
    | _ =>
      let tc := Lean.mkConst (c ++ fd.name ++ `tree ++ `timed) levels
      let ar ← forallTelescope (← inferType tc) fun zs _ => pure zs.size
      let fcs := compsOf fd.name
      unless ar == bs.size + fd.ys.size + fcs.size do
        fail m!"the costed form of the field `{fd.name}` takes {ar} arguments, and \
          {bs.size + fd.ys.size + fcs.size} are its binders, those of the field and its field \
          costs"
      let call := mkAppN tc (bs ++ fd.ys ++ fcs)
      mvals := mvals.push (← mkLambdaFVars fd.ys (← mkAppM ``Prod.snd #[call]))
      if mirrorFields.contains (fd.name.appendAfter "Cost") then
        mvals := mvals.push (← mkLambdaFVars fd.ys (← mkAppM ``Prod.fst #[call]))
  let mirrorCtor := (getStructureCtor env timedS).name
  let resT := mkAppN (mkConst timedS lvlsS) qs
  let timedName := c ++ `timed
  CatCrypt.Tactics.DeriveTimed.addTimedDef timedName levelParams
    (← mkForallFVars (bs ++ comps) resT)
    (← mkLambdaFVars (bs ++ comps) (mkAppN (mkConst mirrorCtor lvlsS) (qs ++ mvals)))
  -- The erasure theorem: the data primitives at their fields, the tree and computation
  -- primitives with hypotheses relating their costed binders to their fields.
  let bsInst := bs.map fun b => match dps.find? (·.fv == b) with
    | some p => p.key
    | none => b
  let erase (fv : Expr) (compile : Bool) : TermElabM Expr := do
    let v ← costed fv
    forallTelescope (← whnfR (← inferType fv)) fun ys bt => do
      let some T ← CatCrypt.Tactics.DeriveTimed.treeTy? bt | fail m!"internal: `{fv}`"
      let e := T.eraseE (mkAppN v ys)
      let e ← if compile then mkAppM ``CatCrypt.Core.SPTree.compile #[e] else pure e
      mkLambdaFVars ys e
  let argsC ← xs.mapM fun x => do
    match advs.find? (·.orig == x.fvarId!) with
    | some a => erase a.tree true
    | none => pure x
  let mut hypDecls : Array (Name × (Array Expr → TermElabM Expr)) := #[]
  for p in pps do
    let v ← costed p.fv
    let t ← forallTelescope (← whnfR (← inferType p.fv)) fun ys _ => do
      let some T ← CatCrypt.Tactics.DeriveTimed.treeTy? (← inferType (mkAppN p.fv ys)) |
        fail m!"internal: `{p.fv}`"
      let lhs := T.eraseE (mkAppN v ys)
      let lhs ← if p.tree then pure lhs else mkAppM ``CatCrypt.Core.SPTree.compile #[lhs]
      mkForallFVars ys (← mkEq lhs (mkAppN p.key ys))
    let n := (← p.fv.fvarId!.getUserName).eraseMacroScopes.appendBefore "h_"
    hypDecls := hypDecls.push (n, fun _ => pure t)
  withLocalDeclsD hypDecls fun hs => do
  let lhsA := mkAppN (mkConst timedName levels) (bsInst ++ comps)
  let rhsA := mkAppN (mkConst c levels) argsC
  let goalTy := mkAppN (mkConst (timedS ++ `Erases) lvlsS) (qs ++ #[lhsA, rhsA])
  let mv ← mkFreshExprSyntheticOpaqueMVar goalTy
  let some unfolded ← unfoldDefinition? goalTy | fail m!"internal: `{timedS ++ `Erases}`"
  let mut g ← mv.mvarId!.replaceTargetDefEq unfolded.headBeta
  -- The erased fields of the costed form, as the equation of the erasure relation states them.
  let mkArgs ← withExistsBody (← g.getType) fun dummies e => do
    let some (_, _, r) := e.eq? | fail m!"internal: the erasure relation is not an equation"
    let as := r.getAppArgs.extract qs.size r.getAppNumArgs
    return as.map fun a => if dummies.any (a.containsFVar ·.fvarId!) then none else some a
  for fd in fields do
    unless fd.kind matches .tree _ | .comp _ do continue
    let some j := fields.findIdx? (·.name == fd.name) | fail m!"internal: `{fd.name}`"
    let some (some W) := mkArgs[j]? | fail m!"internal: the erased field `{fd.name}`"
    let treeName := c ++ fd.name ++ `tree
    let rhsY := mkAppN (← mkProjection rhsA fd.name) fd.ys
    let h1 := mkAppN (mkConst (treeName ++ `erase_timed) levels)
      (bsInst ++ fd.ys ++ compsOf fd.name)
    let pf ← match fd.kind with
      | .comp _ =>
        let some α ← spCompArg? (← inferType fd.body) | fail m!"internal: `{fd.name}`"
        let h1c ← mkCongrArg (mkApp (mkConst ``CatCrypt.Core.SPTree.compile) α) h1
        let compArgs ← bsOrig.mapM fun b => do
          match advs.find? (·.tree == b) with
          | some _ => erase b false
          | none => pure b
        let cArgs ← cps.mapM fun p => erase p.fv false
        let cHyps := (pps.zip hs).filterMap fun (p, h) => if p.tree then none else some h
        let h2 := mkAppN (mkConst (c ++ fd.name ++ `compile_tree) levels)
          (compArgs ++ cArgs ++ cHyps ++ fd.ys)
        mkEqTrans h1c h2
      | _ =>
        -- The erased tree primitives are replaced by their fields, one after the other.
        let mut erArgs ← tBs.mapM fun b => do
          if let some p := dps.find? (·.fv == b) then return p.key
          if (advs.find? (·.tree == b)).isSome || (pps.find? (·.fv == b)).isSome then
            return ← erase b false
          return b
        let mut E := h1
        for p in pps, h in hs do
          unless p.tree do continue
          let some k := tBs.idxOf? p.fv | fail m!"internal: `{p.fv}`"
          let fe ← forallTelescope (← inferType h) fun zs _ => mkFunExtN zs (mkAppN h zs)
          let motive ← withLocalDeclD `z (← inferType p.fv) fun z => do
            mkLambdaFVars #[z] (mkAppN (mkConst treeName levels) (erArgs.set! k z ++ fd.ys))
          E ← mkEqTrans E (← mkCongrArg motive fe)
          let some (_, _, r) := (← inferType fe).eq? | fail m!"internal: `{p.fv}`"
          erArgs := erArgs.set! k r
        pure E
    let e ← mkExpectedTypeHint (← mkFunExtN fd.ys pf) (← mkEq W (← mkLambdaFVars fd.ys rhsY))
    let r ← g.rewrite (← g.getType) e
    unless r.mvarIds.isEmpty do fail m!"internal: rewriting the field `{fd.name}`"
    g ← g.replaceTargetEq r.eNew r.eqProof
  for fd in fields do
    if fd.kind matches .prop then
      g ← g.existsIntro (← mkProjection rhsA fd.name)
  g.refl
  let pf ← instantiateMVars mv
  if pf.hasSorry || pf.hasExprMVar then fail m!"the erasure theorem `{c ++ `erase_timed}` is not proved"
  let newBs := bs.filter fun b => !tBs.contains b
  let eBs := xs.filter (fun x => (advs.find? (·.orig == x.fvarId!)).isNone) ++ newBs ++ comps ++
    hs
  addDecl (Declaration.thmDecl
    { name := c ++ `erase_timed, levelParams,
      type := ← mkForallFVars eBs goalTy, value := ← mkLambdaFVars eBs pf })

/-- Derive the costed form of the reduction `c` with the value `value`, whose result is a
structure `S qs` with a costed mirror `S.Timed`: for each computation field `f` the tree
`c.f.tree` and `c.f.compile_tree`, for each tree field `f` the tree `c.f.tree`, the costed forms
`c.f.tree.timed` (by `derive_timed`), the costed form `c.timed : … → S.Timed qs`, and
`c.erase_timed : … → S.Timed.Erases (c.timed …) (c …)`. -/
partial def deriveStructReduction (c : Name) (advNames : Array Name) (unfold : Bool)
    (value : Expr) (levelParams : List Name)
    (deriveRec : Name → NameSet → TermElabM Unit := fun _ _ => pure ()) :
    TermElabM Unit := do
  let levels := levelParams.map mkLevelParam
  lambdaTelescope value fun xs b => do
    let env ← getEnv
    let rt ← whnf (← inferType b)
    let .const S lvlsS := rt.getAppFn
      | fail m!"the result of `{c}` is neither a computation `SPComp α` nor a structure"
    let some sinfo := getStructureInfo? env S
      | fail m!"the result of `{c}` is neither a computation `SPComp α` nor a structure"
    let qs := rt.getAppArgs
    let timedS := S ++ `Timed
    let some mirrorInfo := getStructureInfo? env timedS
      | fail m!"the result of `{c}` is the structure `{S}`, which has no costed mirror; \
          `derive_timed_structure {S}` defines it"
    let mirrorFields := mirrorInfo.fieldNames
    let bv ← whnf b
    let some cv ← isConstructorApp? bv
      | fail m!"the body of `{c}` does not reduce to a constructor application of `{S}`"
    let vals := bv.getAppArgs.extract cv.numParams bv.getAppNumArgs
    unless vals.size == sinfo.fieldNames.size do
      fail m!"the body of `{c}` is a partial constructor application of `{S}`"
    -- The fields with their kinds.
    let mut ty ← instantiateForall (← inferType (mkConst cv.name lvlsS)) qs
    let mut fields : Array SField := #[]
    for f in sinfo.fieldNames, v in vals do
      let .forallE _ d body _ ← whnf ty | fail m!"internal: the constructor of `{S}`"
      fields := fields.push
        { name := f, kind := ← CatCrypt.Tactics.DeriveTimedStructure.fieldKind d, value := v }
      ty := body.instantiate1 v
    -- The binders of each tree and computation field, and its body.
    let rec withFieldBodies (i : Nat) (acc : Array SField) (k : Array SField → TermElabM Unit) :
        TermElabM Unit := do
      if h : i < fields.size then
        let fd := fields[i]
        match fd.kind with
        | .tree n | .comp n =>
          forallBoundedTelescope (← whnfR (← inferType fd.value)) n fun ys _ => do
            unless ys.size == n do fail m!"internal: the field `{fd.name}`"
            withFieldBodies (i + 1) (acc.push { fd with ys, body := (mkAppN fd.value ys).headBeta })
              k
        | _ => withFieldBodies (i + 1) (acc.push fd) k
      else k acc
    withFieldBodies 0 #[] fun fields => do
    -- The adversary binders.
    let mut isAdv : Array (Option Nat) := #[]
    for x in xs do
      let n := (← x.fvarId!.getUserName).eraseMacroScopes
      let t ← inferType x
      let ar ← forallTelescope (← whnfR t) fun ys body => do
        return if (← spCompArg? body).isSome then some ys.size else none
      let named := if advNames.isEmpty then true else advNames.contains n
      isAdv := isAdv.push (if named then ar else none)
    let rec go (i : Nat) (bs : Array Expr) (advs : Array Adv) (args : Array Expr) :
        TermElabM Unit := do
      if h : i < xs.size then
        let x := xs[i]
        match isAdv[i]! with
        | none => go (i + 1) (bs.push x) advs (args.push x)
        | some ar =>
          let t ← inferType x
          let tt ← forallTelescope (← whnfR t) fun ys body => do
            let some β ← spCompArg? body | fail m!"internal: `{t}`"
            mkForallFVars ys (treeTy β)
          withLocalDecl (← x.fvarId!.getUserName) (← x.fvarId!.getBinderInfo) tt fun a' => do
            let arg ← forallTelescope (← whnfR t) fun ys body => do
              let some β ← spCompArg? body | fail m!"internal: `{t}`"
              mkLambdaFVars ys (mkCompile β (mkAppN a' ys))
            go (i + 1) (bs.push a') (advs.push ⟨x.fvarId!, a', ar⟩) (args.push arg)
      else
        let top := (xs.zip isAdv).filterMap fun (x, a) => if a.isNone then some x.fvarId! else none
        -- First pass over all fields: collect the primitives.
        let r ← IO.mkRef (#[] : Array Prim)
        for fd in fields do
          let ctx₁ : RCtx :=
            { advs, base := c ++ fd.name ++ `tree, top, found? := some r, unfold, deriveRec }
          match fd.kind with
          | .comp _ => discard <| abstractData ctx₁ (← instantiateMVars (← reify ctx₁ fd.body))
          | .tree _ => discard <| abstractData ctx₁ (← abstractTree ctx₁ fd.body)
          | _ => pure ()
        let found ← r.get
        let used ← xs.mapM fun x => return (← x.fvarId!.getUserName).eraseMacroScopes
        withPrims found 0 used #[] fun ps => do
        -- Second pass: the tree of each field over the binders of the primitives.
        let mut trees : Array (Option Expr) := #[]
        for fd in fields do
          let ctx : RCtx :=
            { advs, base := c ++ fd.name ++ `tree, top, prims := ps, unfold, deriveRec }
          match fd.kind with
          | .comp _ => trees := trees.push (some (← abstractData ctx
              (← instantiateMVars (← reify ctx fd.body))))
          | .tree _ => trees := trees.push (some (← abstractData ctx (← abstractTree ctx fd.body)))
          | _ => trees := trees.push none
        for t in trees do
          if let some t := t then
            for a in advs do
              if t.containsFVar a.orig then
                fail m!"the adversary `{mkFVar a.orig}` occurs outside a call position in\
                  {indentExpr t}"
        let dps := ps.filter (·.data)
        let tps := ps.filter (·.tree)
        let cps := ps.filter fun p => !p.data && !p.tree
        let dFvs := dps.map (·.fv)
        let tFvs := tps.map (·.fv)
        let cFvs := cps.map (·.fv)
        let pFvs := (ps.filter fun p => !p.data).map (·.fv)
        let hyps := cps.filterMap (·.hyp?)
        -- The kept binders: as for a computation-valued reduction, with the parameters of the
        -- result, the type and data fields and the binders of the fields.
        let mut needed : FVarIdSet := {}
        for bnd in bs do
          let bt ← inferType bnd
          let isFn ← if (← isProp bt) || (← isTypeFormerType bt) || (← isClass? bt).isSome then
              pure false
            else pure (← whnfR bt).isForall
          unless isFn do needed := needed.insert bnd.fvarId!
        let mut roots : Array Expr := qs ++ (← (dFvs ++ pFvs).mapM fun v => inferType v)
        for fd in fields, t in trees do
          if let some t := t then
            roots := roots.push t
            for y in fd.ys do roots := roots.push (← inferType y)
            roots := roots.push (← inferType fd.body)
          else if !(fd.kind matches .prop) then roots := roots.push fd.value
        for x in roots do
          needed := (collectFVars {} (← instantiateMVars x)).fvarIds.foldl (·.insert ·) needed
        for bnd in bs.reverse do
          if needed.contains bnd.fvarId! then
            needed := (collectFVars {} (← instantiateMVars (← inferType bnd))).fvarIds.foldl
              (·.insert ·) needed
        let kept := bs.filter fun bnd => needed.contains bnd.fvarId!
        let tBs := kept ++ dFvs ++ pFvs
        let tKeys := tps.map (·.key)
        let rhsC := mkAppN (mkConst c levels) args
        -- The tree of each field, and the compile equation of each computation field.
        for fd in fields, t in trees do
          let some t := t | continue
          let treeName := c ++ fd.name ++ `tree
          let ft ← inferType t
          CatCrypt.Tactics.DeriveTimed.addTimedDef treeName levelParams
            (← mkForallFVars (tBs ++ fd.ys) ft)
            (← mkLambdaFVars (tBs ++ fd.ys) t)
          if fd.kind matches .comp _ then
            let some α ← spCompArg? (← inferType fd.body) | fail m!"internal: `{fd.name}`"
            let rhs := mkAppN (← mkProjection rhsC fd.name) fd.ys
            let tI := (t.replaceFVars dFvs (dps.map (·.key))).replaceFVars tFvs tKeys
            let goalTy ← mkEq (mkCompile α tI) rhs
            let mv ← mkFreshExprSyntheticOpaqueMVar goalTy
            prove (cFvs.zip hyps) mv.mvarId!
            let pf ← instantiateMVars mv
            if pf.hasSorry || pf.hasExprMVar then
              fail m!"the compile equation of the field `{fd.name}` is not proved"
            let lhs := mkCompile α (mkAppN (mkConst treeName levels)
              (kept ++ dps.map (·.key) ++ (ps.filter fun p => !p.data).map (fun p =>
                if p.tree then p.key else p.fv) ++ fd.ys))
            let eBs := bs ++ cFvs ++ hyps ++ fd.ys
            addDecl (Declaration.thmDecl
              { name := c ++ fd.name ++ `compile_tree, levelParams,
                type := ← mkForallFVars eBs (← mkEq lhs rhs),
                value := ← mkLambdaFVars eBs pf })
        -- The costed forms of the trees.
        for fd in fields, t in trees do
          if t.isSome then
            CatCrypt.Tactics.DeriveTimed.deriveTimed {} (c ++ fd.name ++ `tree)
        assembleStruct c levels levelParams S lvlsS qs mirrorFields fields xs bs advs kept ps
    go 0 #[] #[] #[]

/-- Replace each call `recF as` of the local `recF` in `e` by `t as extra`. -/
partial def replaceRecCalls (recF t : Expr) (extra : Array Expr) (e : Expr) : Expr :=
  e.replace fun s =>
    if s.getAppFn == recF then
      some (mkAppN t (s.getAppArgs.map (replaceRecCalls recF t extra) ++ extra))
    else none

/-- The proof of the case `g : (c.tree targs).compile = c rargs` of the induction over
`c.tree`: both calls unfolded once by their equations `eq_def`, and the bodies related by
`prove`, whose recursive calls are closed by the induction hypotheses. -/
def proveRecCase (c : Name) (g : MVarId) : TermElabM Unit := g.withContext do
  let (α, t, r) ← goalSides g
  let unfoldOnce (f : Name) (e : Expr) : TermElabM (Expr × Expr) := do
    -- A side that the induction has already unfolded stays.
    let .const n lvls := e.getAppFn | return (← mkEqRefl e, e)
    unless n == f do return (← mkEqRefl e, e)
    let some eqd ← getUnfoldEqnFor? n (nonRec := true)
      | fail m!"internal: `{n}` has no unfolding equation"
    let thm := Lean.mkConst eqd lvls
    let k ← forallTelescope (← inferType thm) fun ys _ => pure ys.size
    let args := e.getAppArgs
    unless k ≤ args.size do fail m!"internal: `{e}` is a partial application"
    let mut pf := mkAppN thm (args.extract 0 k)
    for a in args.extract k args.size do
      pf ← mkCongrFun pf a
    let some (_, _, body) := (← inferType pf).eq? | fail m!"internal: `{eqd}`"
    -- The match of the equation on the constructors of the case, reduced (definitionally).
    let mut body := body.headBeta
    repeat
      match ← reduceMatcher? body with
      | ReduceMatcherResult.reduced b => body := b.headBeta
      | _ => break
    return (pf, body)
  -- The induction states each case with the tree unfolded; the computation is unfolded here.
  let (eT, bT) := (← mkEqRefl t, t)
  let (eR, bR) ← unfoldOnce c r
  let g' ← mkFreshExprSyntheticOpaqueMVar (← mkEq (mkCompile α bT) bR)
  let compileFn := mkApp (mkConst ``CatCrypt.Core.SPTree.compile) α
  let pf ← mkEqTrans (← mkCongrArg compileFn eT) (← mkEqTrans g' (← mkEqSymm eR))
  close g pf
  prove #[] g'.mvarId!

/-- The tree, its type and the compile equation of the recursive computation `c`, from the
reflection `tree` of its body over the binders `bs` (each adversary replaced by its tree), in
which the recursive calls are calls of the local `recF`. The tree `c.tree` is added: its
recursive calls pass the primitives unchanged, so a recursive call must pass every binder that
a primitive mentions unchanged. Its compile equation is proved by induction over `c.tree`
(`fun_induction`), with the data primitives as variables equal to their fields. -/
def recursiveTree (c : Name) (levels : List Level) (levelParams : List Name)
    (xs bs args : Array Expr) (advs : Array Adv) (ps : Array Prim) (recF α tree : Expr) :
    TermElabM (Expr × Expr × Expr × Expr) := do
  let treeName := c ++ `tree
  let dps := ps.filter (·.data)
  let cps := ps.filter fun p => !p.data
  let dFvs := dps.map (·.fv)
  let dKeys := dps.map (·.key)
  let cFvs := cps.map (·.fv)
  let hyps := cps.filterMap (·.hyp?)
  for a in advs do
    if tree.containsFVar a.orig then
      fail m!"the adversary `{mkFVar a.orig}` occurs outside a call position in{indentExpr tree}"
  -- The binders mentioned by a primitive stay fixed in the recursive calls.
  let keys := dKeys ++ cps.map (·.key)
  let fixed := (List.range xs.size).filter fun i => keys.any (·.containsFVar xs[i]!.fvarId!)
  if let some s := tree.find? fun s => s.getAppFn == recF && s.getAppNumArgs == bs.size &&
      fixed.any fun i => s.getArg! i != bs[i]! then
    fail m!"the recursive call{indentExpr s}\nchanges a binder whose fields are primitives"
  let tBs := bs ++ dFvs ++ cFvs
  let treeC := Lean.mkConst treeName levels
  let tree' := replaceRecCalls recF treeC (dFvs ++ cFvs) tree
  if tree'.containsFVar recF.fvarId! then fail m!"internal: a recursive call escaped"
  let tType ← mkForallFVars tBs (treeTy α)
  let tValue ← mkLambdaFVars tBs tree'
  CatCrypt.Tactics.DeriveTimed.addTimedDef treeName levelParams tType tValue
  let rhs := mkAppN (Lean.mkConst c levels) args
  -- The compile equation with each data primitive a variable equal to its field.
  let rec withEqs (i : Nat) (acc : Array Expr) (k : Array Expr → TermElabM Expr) :
      TermElabM Expr := do
    if h : i < dFvs.size then
      withLocalDeclD (Name.mkSimple s!"hd{i}") (← mkEq dFvs[i] dKeys[i]!) fun hd =>
        withEqs (i + 1) (acc.push hd) k
    else k acc
  let stmt ← withEqs 0 #[] fun deqs => do
    mkForallFVars (tBs ++ deqs ++ hyps)
      (← mkEq (mkCompile α (mkAppN treeC tBs)) rhs)
  let n ← forallTelescope stmt fun ys _ => pure ys.size
  let ids : Array (TSyntax `ident) := (Array.range n).map fun i => mkIdent (Name.mkSimple s!"x{i}")
  let explicit ← forallTelescope stmt fun ys _ =>
    (ys.extract 0 tBs.size).mapM fun y => return (← y.fvarId!.getBinderInfo).isExplicit
  let argIds := ((ids.extract 0 tBs.size).zip explicit).filterMap fun (i, e) =>
    if e then some i else none
  let mv ← mkFreshExprSyntheticOpaqueMVar stmt
  let gs ← Term.withoutErrToSorry <| Tactic.run mv.mvarId! (Tactic.evalTactic (← `(tactic|
    (intro $ids*; fun_induction $(mkIdent treeName):ident $argIds* <;> (try subst_vars)))))
  for g in gs do
    proveRecCase c g
  let sProof ← instantiateMVars mv
  if sProof.hasSorry || sProof.hasExprMVar then fail m!"the compile equation is not proved"
  let eValue ← mkLambdaFVars (bs ++ cFvs ++ hyps)
    (mkAppN sProof (tBs.map (fun b => (dFvs.idxOf? b).map (dKeys[·]!) |>.getD b) ++
      (← dKeys.mapM fun k => (mkEqRefl k : MetaM Expr)) ++ hyps))
  let eType ← mkForallFVars (bs ++ cFvs ++ hyps)
    (← mkEq (mkCompile α (mkAppN treeC (bs ++ dKeys ++ cFvs))) rhs)
  return (tType, tValue, eType, eValue)

/-- Define `c.tree`, prove `c.compile_tree`, and run `derive_timed c.tree`. The adversaries
are the binders named in `advNames`, or every binder whose type ends in `SPComp` when it is
empty; `unfold` is the unfolding of data definitions of `RCtx`. -/
partial def deriveReduction (c : Name) (advNames : Array Name) (unfold : Bool := false)
    (visiting : NameSet := {}) : TermElabM Unit := do
  let env ← getEnv
  let some info := env.find? c | fail m!"unknown constant `{c}`"
  let .defnInfo d := info | fail m!"`{c}` is not a definition"
  let recursive := isRecursive env c
  let treeName := c ++ `tree
  let thmName := c ++ `compile_tree
  if env.contains treeName then fail m!"`{treeName}` already exists"
  let levels := info.levelParams.map mkLevelParam
  -- The body: the value of the definition, or for a recursive definition the body of its
  -- equations, in which the recursive calls are calls of `c`.
  let body := match Structural.eqnInfoExt.find? env c, WF.eqnInfoExt.find? env c with
    | some i, _ => i.value
    | _, some i => i.value
    | _, _ => d.value
  -- Eta-expand to all binders of the type.
  let value ← lambdaTelescope body fun xs b => do
    CatCrypt.Tactics.DeriveTimed.withTypeBinders (← instantiateForall d.type xs) fun ys _ =>
      mkLambdaFVars (xs ++ ys) (mkAppN b ys).headBeta
  -- A carrier in a universe other than `Type`: `SPTree` is a tree over `Type`.
  lambdaTelescope value fun xs _ => do
    for x in xs do
      if let .sort u ← whnf (← inferType x) then
        unless (← instantiateLevelMVars u).normalize == Level.one do
          fail m!"the carrier `{x}` is in a universe other than `Type`; computation trees \
            `SPTree` are over `Type`: derive the reduction at carriers in `Type`"
  let deriveRec : Name → NameSet → TermElabM Unit := fun g vis =>
    deriveReduction g #[] (visiting := vis)
  -- A structure-valued reduction: field by field.
  if ← lambdaTelescope value fun _ b => do return (← spCompArg? (← inferType b)).isNone then
    if recursive then fail m!"`{c}` is recursive and its result is not a computation"
    if env.contains (c ++ `timed) then fail m!"`{c ++ `timed}` already exists"
    return ← deriveStructReduction c advNames unfold value info.levelParams deriveRec
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
        -- A recursive definition: its recursive calls are calls of the local `recF`, which
        -- stands for its tree over the same primitives.
        withLocalDeclD `rec (← mkForallFVars bs (treeTy α)) fun recF => do
        let selfInfo := if recursive then some (c, recF, isAdv) else none
        let visiting := visiting.insert c
        -- First pass: collect the primitives.
        let r ← IO.mkRef (#[] : Array Prim)
        let ctx₀ : RCtx := { advs, base := treeName, top, unfold, visiting, deriveRec }
        let ctx₀ := { ctx₀ with hoist := !recursive }
        let ctx₀ := { ctx₀ with self? := selfInfo }
        let ctx₁ := { ctx₀ with found? := some r }
        discard <| abstractData ctx₁ (← instantiateMVars (← reify ctx₁ b))
        let found ← r.get
        let used ← xs.mapM fun x => return (← x.fvarId!.getUserName).eraseMacroScopes
        withPrims found 0 used #[] fun ps => do
        -- Second pass: the tree over the binders of the primitives.
        let ctx := { ctx₀ with prims := ps }
        let tree ← abstractData ctx (← instantiateMVars (← reify ctx b))
        if recursive then
          return ← recursiveTree c levels info.levelParams xs bs args advs ps recF α tree
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
        -- The function binders of the reduction that the tree, its type and the types of the
        -- primitive binders do not mention are not binders of the tree, so that the costed form
        -- has no cost companion for them; every other binder is kept.
        let mut needed : FVarIdSet := {}
        for bnd in bs do
          let bt ← inferType bnd
          let isFn ← if (← isProp bt) || (← isTypeFormerType bt) || (← isClass? bt).isSome then
              pure false
            else pure (← whnfR bt).isForall
          unless isFn do needed := needed.insert bnd.fvarId!
        for x in #[tree, α] ++ (← (dFvs ++ cFvs).mapM fun v => inferType v) do
          needed := (collectFVars {} (← instantiateMVars x)).fvarIds.foldl (·.insert ·) needed
        for bnd in bs.reverse do
          if needed.contains bnd.fvarId! then
            needed := (collectFVars {} (← instantiateMVars (← inferType bnd))).fvarIds.foldl
              (·.insert ·) needed
        let kept := bs.filter fun bnd => needed.contains bnd.fvarId!
        let tBs := kept ++ dFvs ++ cFvs
        let tType ← mkForallFVars tBs (treeTy α)
        let tValue ← mkLambdaFVars tBs tree
        let rhs := mkAppN (mkConst c levels) args
        let goalTy ← mkEq (mkCompile α (tree.replaceFVars dFvs dKeys)) rhs
        let mv ← mkFreshExprSyntheticOpaqueMVar goalTy
        prove (cFvs.zip hyps) mv.mvarId!
        let pf ← instantiateMVars mv
        if pf.hasSorry then fail m!"the compile equation is not proved"
        if pf.hasExprMVar then fail m!"the compile equation is not proved"
        let lhs := mkCompile α (mkAppN (mkConst treeName levels) (kept ++ dKeys ++ cFvs))
        let eBs := bs ++ cFvs ++ hyps
        let eType ← mkForallFVars eBs (← mkEq lhs rhs)
        let eValue ← mkLambdaFVars eBs pf
        return (tType, tValue, eType, eValue)
    go 0 #[] #[] #[]
  unless (← getEnv).contains treeName do
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
