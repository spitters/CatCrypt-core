/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleAdversaryTimed
public import CatCryptCore.Core.SPTreeTimedOps
public import Lean

/-!
# Derived step costs of oracle-tree reductions

`derive_timed R` takes a reduction `R` whose result is an oracle tree `OracleAdv D R α` and
defines its costed form `R.timed`, whose result is a step-prefixed tree
`ℕ × OracleAdv.Timed D R α`, together with the erasure theorem `R.erase_timed`:
`(R.timed xs').2.erase = R xs`, where `xs` is obtained from `xs'` by erasing the costed
binders and dropping the cost companions. The theorem is proved by unfolding both sides and
rewriting with the erasure lemmas of `CatCryptCore.Crypto.OracleAdversaryTimed`, by
functional induction on `R.timed` when `R` is recursive, and is checked by the kernel.

## Tree kinds

The translation is driven by a table of tree kinds (`treeKinds`). An entry gives the tree type
and its costed type, their erasure and step prefix, the nodes and combinators with their costed
forms and the role of each argument (`ArgRole`), and the lemmas that prove the erasure theorems.
The table has two entries:

* oracle trees `OracleAdv D R α`, costed by `OracleAdv.Timed D R α`
  (`CatCryptCore.Crypto.OracleAdversaryTimed`);
* syntactic computation trees `SPTree α`, costed by `SPTree.Timed α`
  (`CatCryptCore.Core.SPTreeTimed`, `CatCryptCore.Core.SPTreeTimedOps`): the nodes `ret`,
  `sample`, `get`, `set` and `fail`, and the combinators `SPTree.bind` and `SPTree.map`.

Below, "tree" means a tree of a kind in the table, and the rules for oracle trees apply to
every kind.

## Binders

A binder of `R` is translated by its type:

* a type, a proposition or an instance is kept;
* first-order data is kept;
* an oracle tree `A : OracleAdv D R α` becomes `A : OracleAdv.Timed D R α`, erased by
  `A.erase`;
* a function into oracle trees `k : X → OracleAdv D R α` becomes `k : X → OracleAdv.Timed D R α`
  followed by its cost companion `kCost : X → ℕ`, the cost of computing the tree `k x` from
  `x`; it is erased by `fun x => (k x).erase`;
* any other function `f : X → Y` is kept and followed by its cost companion `fCost : X → ℕ`,
  the cost of evaluating `f x`.

## Cost rules

Costs follow call-by-value evaluation:

* a call of a constant or of a local function costs one plus the callee's cost at its
  arguments plus the costs of its arguments; the callee's cost is its cost companion for a
  local function, its registered cost `f.timedCost` for a registered primitive, the cost of
  its unfolded body for a non-recursive definition, and the step cost of `f.timed` for a
  reduction;
* `if` and `match` cost one, plus the costs of the condition or the discriminants, plus the
  cost of the branch taken;
* constructors, literals, numerals, casts, projections and variables cost nothing beyond
  their arguments, and a closure costs nothing to build;
* a `rand` or `query` node costs its registered unit (`OracleAdv.Timed.TimeBound`); the
  distribution of a `rand` node is priced by the rules above, with the uniform and point
  distributions free, since sampling is included in the node's unit;
* a `sample`, `get` or `set` node of a computation tree costs its registered unit
  (`SPTree.Timed.time`), and the location and the value of a `get` or `set` node are priced by
  the rules above;
* `OracleAdv.bind`, `OracleAdv.simulate` and `OracleAdv.mapQuery` are translated to
  `OracleAdv.Timed.bind`, `OracleAdv.Timed.simulate` and `OracleAdv.Timed.mapQuery`, with the
  cost of the renaming `ren d` of a `mapQuery` charged per query; `SPTree.bind` and
  `SPTree.map` are translated to `SPTree.Timed.bind` and `SPTree.Timed.map`, with the cost of
  the function of a `map` charged per leaf;
* a `let` is substituted into its body, so its value is priced at each use.

A registered primitive `f` has a cost `f.timedCost`, a definition taking the arguments of
`f`, each function-typed argument followed by its cost companion, and returning `ℕ`; the
command `timed_cost f := e` defines it. A registered cost is a trusted statement about the
cost of `f`. A reduction whose costed form is written by hand (a recursion over an oracle
tree, for instance) is registered by defining `R.timed` and `R.erase_timed` in the binder
convention above.

Calls of reductions without a costed form are derived on demand. A derivation fails, with
the reason, on a function stored in data (a local function without a cost companion), a
class method on a local instance without a registered cost, a recursive or opaque data
function without a registered cost, a `match` whose motive depends on its discriminants,
and a recursion over an oracle-tree argument.

## Attribution

The translation rules and the derivation on demand follow the instrumented translation of
the Ironwood project (`Zcash/Meta/Translate.lean`, `Instrument.lean`, `Efficient.lean`),
which is dual-licensed under the MIT and Apache-2.0 licences; the cost rules are those of
Isabelle's `time_fun` command.

## Main definitions

* `derive_timed R`, `derive_timed (suffix := s) R` — define `R.timed` (or `R.s`) and
  `R.erase_timed` (or `R.erase_s`)
* `timed_cost f := e` — register the cost `e` of the primitive `f`
* `treeKinds` — the table of tree kinds
-/

public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OracleAdv.Timed

variable {D R α : Type}

/-- Erasure of a step-prefixed tree commutes with `if`. -/
theorem erase_snd_ite (c : Prop) [Decidable c] (x y : ℕ × Timed D R α) :
    (if c then x else y).2.erase = if c then x.2.erase else y.2.erase := by
  split <;> rfl

/-- Erasure of a step-prefixed tree commutes with a dependent `if`. -/
theorem erase_snd_dite (c : Prop) [Decidable c] (x : c → ℕ × Timed D R α)
    (y : ¬c → ℕ × Timed D R α) :
    (if h : c then x h else y h).2.erase = if h : c then (x h).2.erase else (y h).2.erase := by
  split <;> rfl

end CatCrypt.Crypto.OracleAdv.Timed

meta section

namespace CatCrypt.Tactics.DeriveTimed

open Lean Elab Meta Term Command

/-- How a binder of a reduction is translated. -/
inductive Kind where
  /-- A type, a proposition or an instance: kept. -/
  | static
  /-- First-order data: kept. -/
  | data
  /-- A function that is not into oracle trees: kept, with a cost companion. -/
  | fn
  /-- An oracle tree: replaced by a costed tree. -/
  | tree
  /-- A function into oracle trees: replaced by a function into costed trees, with a cost
  companion. -/
  | treeFn
  deriving Inhabited, BEq, Repr

/-- The translation of a local of the reduction: its kind, its costed value (the costed tree
for `tree` and `treeFn`, the local itself otherwise) and its cost companion. -/
structure LocalInfo where
  kind : Kind
  value : Expr
  companion? : Option Expr := none
  deriving Inhabited

/-- The context of a translation: the translated locals, the reduction being derived with
the local that stands for its costed form, the suffix of costed forms, and the unfolding
depth of data functions. -/
structure Ctx where
  locals : FVarIdMap LocalInfo := {}
  self? : Option (Name × Expr) := none
  suffix : Name := `timed
  depth : Nat := 0
  visiting : NameSet := {}

/-- The maximal nesting of unfolded data definitions. -/
def maxDepth : Nat := 8

/-- Constants that cost nothing beyond their arguments. -/
def freeConstants : Array Name :=
  #[``OfNat.ofNat, ``Nat.cast, ``NatCast.natCast, ``Int.cast, ``IntCast.intCast, ``id,
    ``Eq.rec, ``Eq.ndrec, ``Eq.mp, ``Eq.mpr, ``cast, ``Subtype.val, ``Fin.val,
    ``PMF.uniformOfFintype, ``PMF.pure, ``Classical.arbitrary, ``Inhabited.default]

/-- Operations of unit cost on `ℕ`: a call costs one. -/
def natUnitOps : Array Name :=
  #[``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HMod.hMod, ``Nat.succ, ``Nat.add,
    ``Nat.sub, ``Nat.mul, ``Nat.div, ``Nat.mod, ``Nat.pred, ``Nat.min, ``Nat.max, ``Min.min,
    ``Max.max]

/-- The literal value of a numeral of type `ℕ`. -/
def natVal? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ =>
    if e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 0).isConstOf ``Nat then
      match e.getArg! 1 with
      | .lit (.natVal n) => some n
      | _ => none
    else none

/-- The numeral `n : ℕ`. -/
def natE (n : Nat) : Expr := mkNatLit n

/-- `a + b` on `ℕ`, with zero summands dropped and leading numerals folded. -/
def add (a b : Expr) : Expr :=
  match natVal? a, natVal? b with
  | some 0, _ => b
  | _, some 0 => a
  | some m, some n => natE (m + n)
  | some m, none =>
    if b.isAppOfArity ``HAdd.hAdd 6 then
      match natVal? (b.getArg! 4) with
      | some n => mkNatAdd (natE (m + n)) (b.getArg! 5)
      | none => mkNatAdd a b
    else mkNatAdd a b
  | _, _ => mkNatAdd a b

/-- The sum of the costs `cs`. -/
def sum (cs : Array Expr) : Expr := cs.foldl add (natE 0)

/-- How an argument of a node or a combinator of a tree kind is translated. The roles of a
node or a combinator apply to the trailing arguments of its constant; the leading arguments
are the parameters of the tree type. -/
inductive ArgRole where
  /-- Kept, at no cost. -/
  | keep
  /-- Kept, with its cost charged. -/
  | data
  /-- A continuation with `n` binders: replaced by its step cost and its costed tree, both
  abstracted over the binders. -/
  | cont (n : Nat)
  /-- A tree: replaced by its costed tree, with its step cost charged in front. -/
  | tree
  /-- A function of `n` arguments into trees: replaced by a function into step-prefixed costed
  trees. -/
  | pairFn (n : Nat)
  /-- A data function of `n` arguments: kept and followed by its cost per call, `extra` plus the
  cost of evaluating it. -/
  | perCall (extra n : Nat)
  deriving Inhabited, BEq, Repr

/-- A node of a tree kind: the constructor `src` and the costed constructor `tgt`, which takes
the parameters of the costed tree type and the translated trailing arguments. -/
structure Node where
  src : Name
  tgt : Name
  roles : Array ArgRole
  deriving Inhabited

/-- A combinator of a tree kind: the constant `src` and its costed form `tgt`, which takes the
translated trailing arguments and returns a step-prefixed costed tree when `pair` holds and a
costed tree otherwise. -/
structure Comb where
  src : Name
  tgt : Name
  roles : Array ArgRole
  pair : Bool
  deriving Inhabited

/-- A kind of tree: the tree type `tree` with `nParams` parameters, its costed tree type `timed`
with the same parameters, the erasure `erase` and the step prefix `delay` of the costed type,
its nodes, its combinators, and the lemmas that prove the erasure theorems. -/
structure TreeKind where
  noun : String
  tree : Name
  nParams : Nat
  timed : Name
  erase : Name
  delay : Name
  nodes : Array Node
  combinators : Array Comb
  eraseLemmas : Array Name
  deriving Inhabited

/-- Oracle trees `OracleAdv D R α`: `ret`, `rand` and `query` nodes, and the combinators
`bind`, `simulate` and `mapQuery`. -/
def oracleKind : TreeKind where
  noun := "oracle tree"
  tree := ``CatCrypt.Crypto.OracleAdv
  nParams := 3
  timed := ``CatCrypt.Crypto.OracleAdv.Timed
  erase := ``CatCrypt.Crypto.OracleAdv.Timed.erase
  delay := ``CatCrypt.Crypto.OracleAdv.Timed.delay
  nodes := #[
    ⟨``CatCrypt.Crypto.OracleAdv.ret, ``CatCrypt.Crypto.OracleAdv.Timed.ret, #[.data]⟩,
    ⟨``CatCrypt.Crypto.OracleAdv.rand, ``CatCrypt.Crypto.OracleAdv.Timed.rand,
      #[.data, .cont 1]⟩,
    ⟨``CatCrypt.Crypto.OracleAdv.query, ``CatCrypt.Crypto.OracleAdv.Timed.query,
      #[.data, .cont 1]⟩]
  combinators := #[
    ⟨``CatCrypt.Crypto.OracleAdv.bind, ``CatCrypt.Crypto.OracleAdv.Timed.bind,
      #[.tree, .pairFn 1], true⟩,
    ⟨``CatCrypt.Crypto.OracleAdv.simulate, ``CatCrypt.Crypto.OracleAdv.Timed.simulate,
      #[.pairFn 2, .tree, .data], true⟩,
    ⟨``CatCrypt.Crypto.OracleAdv.mapQuery, ``CatCrypt.Crypto.OracleAdv.Timed.mapQuery,
      #[.perCall 1 1, .tree], false⟩]
  eraseLemmas := #[``CatCrypt.Crypto.OracleAdv.Timed.erase,
    ``CatCrypt.Crypto.OracleAdv.Timed.delay, ``CatCrypt.Crypto.OracleAdv.Timed.erase_bind,
    ``CatCrypt.Crypto.OracleAdv.Timed.erase_simulate,
    ``CatCrypt.Crypto.OracleAdv.Timed.erase_mapQuery,
    ``CatCrypt.Crypto.OracleAdv.Timed.erase_snd_ite,
    ``CatCrypt.Crypto.OracleAdv.Timed.erase_snd_dite]

/-- Syntactic computation trees `SPTree α`: `ret`, `sample`, `get`, `set` and `fail` nodes, and
the combinators `SPTree.bind` and `SPTree.map`. -/
def spTreeKind : TreeKind where
  noun := "computation tree"
  tree := ``CatCrypt.Core.SPTree
  nParams := 1
  timed := ``CatCrypt.Core.SPTree.Timed
  erase := ``CatCrypt.Core.SPTree.Timed.erase
  delay := ``CatCrypt.Core.SPTree.Timed.delay
  nodes := #[
    ⟨``CatCrypt.Core.SPTree.ret, ``CatCrypt.Core.SPTree.Timed.ret, #[.data]⟩,
    ⟨``CatCrypt.Core.SPTree.sample, ``CatCrypt.Core.SPTree.Timed.sample,
      #[.keep, .keep, .keep, .cont 1]⟩,
    ⟨``CatCrypt.Core.SPTree.get, ``CatCrypt.Core.SPTree.Timed.get, #[.data, .cont 1]⟩,
    ⟨``CatCrypt.Core.SPTree.set, ``CatCrypt.Core.SPTree.Timed.set, #[.data, .data, .cont 0]⟩,
    ⟨``CatCrypt.Core.SPTree.fail, ``CatCrypt.Core.SPTree.Timed.fail, #[]⟩]
  combinators := #[
    ⟨``CatCrypt.Core.SPTree.bind, ``CatCrypt.Core.SPTree.Timed.bind, #[.tree, .pairFn 1], true⟩,
    ⟨``CatCrypt.Core.SPTree.map, ``CatCrypt.Core.SPTree.Timed.map, #[.perCall 0 1, .tree],
      true⟩]
  eraseLemmas := #[``CatCrypt.Core.SPTree.Timed.erase_ret,
    ``CatCrypt.Core.SPTree.Timed.erase_sample, ``CatCrypt.Core.SPTree.Timed.erase_get,
    ``CatCrypt.Core.SPTree.Timed.erase_set, ``CatCrypt.Core.SPTree.Timed.erase_fail,
    ``CatCrypt.Core.SPTree.Timed.delay, ``CatCrypt.Core.SPTree.Timed.erase_bind,
    ``CatCrypt.Core.SPTree.Timed.erase_map, ``CatCrypt.Core.SPTree.Timed.erase_snd_ite,
    ``CatCrypt.Core.SPTree.Timed.erase_snd_dite]

/-- The table of tree kinds. -/
def treeKinds : Array TreeKind := #[oracleKind, spTreeKind]

/-- A tree type: its kind and its parameters. -/
structure TreeTy where
  kind : TreeKind
  params : Array Expr
  deriving Inhabited

/-- Whether `t` is the tree type of a kind in the table. -/
def treeTy? (t : Expr) : MetaM (Option TreeTy) := do
  let t ← whnfR (← instantiateMVars t)
  for k in treeKinds do
    if t.isAppOfArity k.tree k.nParams then return some ⟨k, t.getAppArgs⟩
  return none

namespace TreeTy

/-- The costed tree type. -/
def timedType (T : TreeTy) : Expr := mkAppN (mkConst T.kind.timed) T.params

/-- The step-prefixed tree type `ℕ × T.timedType`. -/
def pairType (T : TreeTy) : Expr :=
  mkApp2 (mkConst ``Prod [Level.zero, Level.one]) (mkConst ``Nat) T.timedType

/-- The pair `(c, t)` of a step cost and a costed tree. -/
def mkPair (T : TreeTy) (c t : Expr) : Expr :=
  mkApp4 (mkConst ``Prod.mk [Level.zero, Level.one]) (mkConst ``Nat) T.timedType c t

/-- Whether `p` is an application of the step prefix `delay`. -/
def isDelay (T : TreeTy) (p : Expr) : Bool := p.isAppOfArity T.kind.delay (T.kind.nParams + 2)

/-- The step cost of a step-prefixed tree, reduced on a literal pair and on `delay`. -/
partial def fstOf (T : TreeTy) (p : Expr) : Expr :=
  if p.isAppOfArity ``Prod.mk 4 then p.getArg! 2
  else if T.isDelay p then
    add (p.getArg! T.kind.nParams) (T.fstOf (p.getArg! (T.kind.nParams + 1)))
  else mkApp3 (mkConst ``Prod.fst [Level.zero, Level.one]) (mkConst ``Nat) T.timedType p

/-- The costed tree of a step-prefixed tree, reduced on a literal pair and on `delay`. -/
partial def sndOf (T : TreeTy) (p : Expr) : Expr :=
  if p.isAppOfArity ``Prod.mk 4 then p.getArg! 3
  else if T.isDelay p then T.sndOf (p.getArg! (T.kind.nParams + 1))
  else mkApp3 (mkConst ``Prod.snd [Level.zero, Level.one]) (mkConst ``Nat) T.timedType p

/-- The step cost `c` in front of the step-prefixed tree `p`. -/
def delayE (T : TreeTy) (c p : Expr) : Expr :=
  if natVal? c == some 0 then p
  else if p.isAppOfArity ``Prod.mk 4 then T.mkPair (add c (p.getArg! 2)) (p.getArg! 3)
  else if T.isDelay p then
    mkAppN (mkConst T.kind.delay)
      (T.params ++ #[add c (p.getArg! T.kind.nParams), p.getArg! (T.kind.nParams + 1)])
  else mkAppN (mkConst T.kind.delay) (T.params ++ #[c, p])

/-- The erasure of the costed tree `v`. -/
def eraseE (T : TreeTy) (v : Expr) : Expr := mkAppN (mkConst T.kind.erase) (T.params.push v)

end TreeTy

/-- The kind of a binder of type `t`. -/
def classify (t : Expr) : MetaM Kind := do
  if ← isProp t then return .static
  if ← isTypeFormerType t then return .static
  if (← isClass? t).isSome then return .static
  forallTelescope (← whnfR t) fun ys b => do
    if (← treeTy? b).isSome then
      return if ys.isEmpty then .tree else .treeFn
    if ys.isEmpty then return .data
    return .fn

/-- Whether `e` is data: not a type, a proposition, a proof or an instance. -/
def isDataExpr (e : Expr) : MetaM Bool := do
  let t ← inferType e
  if ← isTypeFormerType t then return false
  if ← isProp t then return false
  if (← isClass? t).isSome then return false
  return true

/-- The cost companion type `X → ℕ` of a function of type `X → Y`. -/
def companionType (t : Expr) : MetaM Expr := do
  forallTelescope (← whnfR t) fun ys _ => mkForallFVars ys (mkConst ``Nat)

/-- The costed type of a binder of type `t` and kind `k`. -/
def costedType (t : Expr) : MetaM Expr := do
  forallTelescope (← whnfR t) fun ys b => do
    let some T ← treeTy? b | throwError "derive_timed: `{b}` is not a tree of a registered kind"
    mkForallFVars ys T.timedType

/-- The erasure of the costed value `v` of a local of type `t` and kind `k`. -/
def erasure (k : Kind) (t v : Expr) : MetaM Expr := do
  match k with
  | .tree =>
    let some T ← treeTy? t | throwError "derive_timed: `{t}` is not a tree of a registered kind"
    return T.eraseE v
  | .treeFn =>
    forallTelescope (← whnfR t) fun ys b => do
      let some T ← treeTy? b
        | throwError "derive_timed: `{b}` is not a tree of a registered kind"
      mkLambdaFVars ys (T.eraseE (mkAppN v ys))
  | _ => return v

/-- Fail with the reason a derivation does not go through. -/
def fail {β : Type} (what : MessageData) : MetaM β :=
  throwError m!"derive_timed: {what}"

/-- Bind the translated binders of the locals `xs` and continue with the context, the
binders of the costed form and the arguments of the original. -/
partial def withBinders {β : Type} (ctx : Ctx) (xs : Array Expr)
    (k : Ctx → Array Expr → Array Expr → TermElabM β) : TermElabM β :=
  go 0 ctx #[] #[]
where
  go (i : Nat) (ctx : Ctx) (bs args : Array Expr) : TermElabM β := do
    if h : i < xs.size then
      let x := xs[i]
      let t ← inferType x
      let n := (← x.fvarId!.getUserName).eraseMacroScopes
      match ← classify t with
      | .static | .data => go (i + 1) ctx (bs.push x) (args.push x)
      | .fn => do
        let ct ← companionType t
        withLocalDeclD (n.appendAfter "Cost") ct fun c =>
          go (i + 1) { ctx with locals := ctx.locals.insert x.fvarId! ⟨.fn, x, some c⟩ }
            (bs.push x |>.push c) (args.push x)
      | .tree => do
        let vt ← costedType t
        withLocalDeclD n vt fun v => do
          go (i + 1) { ctx with locals := ctx.locals.insert x.fvarId! ⟨.tree, v, none⟩ }
            (bs.push v) (args.push (← erasure .tree t v))
      | .treeFn => do
        let vt ← costedType t
        let ct ← companionType t
        withLocalDeclD n vt fun v =>
          withLocalDeclD (n.appendAfter "Cost") ct fun c => do
            go (i + 1) { ctx with locals := ctx.locals.insert x.fvarId! ⟨.treeFn, v, some c⟩ }
              (bs.push v |>.push c) (args.push (← erasure .treeFn t v))
    else k ctx bs args

/-- The leading binders of `f` applied to `n` fresh locals, with its body beta-reduced. -/
def withEta {β : Type} (f : Expr) (n : Nat) (k : Array Expr → Expr → TermElabM β) :
    TermElabM β := do
  forallBoundedTelescope (← whnfR (← inferType f)) n fun ys _ => do
    unless ys.size == n do fail m!"`{f}` takes fewer than {n} arguments"
    k ys (mkAppN f ys).headBeta

/-- The kinds of the binders of the function `f` at the arguments `args`. -/
def argKinds (f : Expr) (args : Array Expr) : MetaM (Array (Kind × Expr)) := do
  let mut ty ← inferType f
  let mut out := #[]
  for a in args do
    let .forallE _ bt body _ ← whnf ty | fail m!"`{f}` is applied to too many arguments"
    out := out.push (← classify bt, bt)
    ty := body.instantiate1 a
  return out

/-- The trailing arguments of `e` to which `roles` apply. -/
def trailing (e : Expr) (args : Array Expr) (roles : Array ArgRole) : MetaM (Array Expr) := do
  unless roles.size ≤ args.size do
    fail m!"`{e}` is applied to fewer arguments than its translation takes"
  return args.extract (args.size - roles.size) args.size

mutual

/-- The cost of evaluating the data term `e`. -/
partial def costOf (ctx : Ctx) (e : Expr) : TermElabM Expr := do
  let e := e.consumeMData.headBeta
  unless ← isDataExpr e do return natE 0
  match e with
  | .fvar _ | .lit _ | .lam .. | .forallE .. | .sort _ => return natE 0
  | .proj _ _ s => costOf ctx s
  | .letE _ _ v b _ => costOf ctx (b.instantiate1 v)
  | .const .. | .app .. => costApp ctx e
  | _ => fail m!"the data term `{e}` is not supported"

/-- The costs of the data arguments among `args`. -/
partial def argsCost (ctx : Ctx) (args : Array Expr) : TermElabM Expr := do
  let mut cs := #[]
  for a in args do
    if ← isDataExpr a then cs := cs.push (← costOf ctx a)
  return sum cs

/-- The cost of a condition: the costs of the data arguments of the proposition. -/
partial def propCost (ctx : Ctx) (p : Expr) : TermElabM Expr := do
  let p := p.consumeMData
  if p.isAppOf ``Not then return ← propCost ctx p.appArg!
  if p.isAppOf ``And || p.isAppOf ``Or then
    return add (← propCost ctx (p.getArg! 0)) (← propCost ctx (p.getArg! 1))
  argsCost ctx p.getAppArgs

/-- The cost companion of the function-valued argument `a`. -/
partial def companionOf (ctx : Ctx) (a : Expr) : TermElabM Expr := do
  if let .fvar id := a.consumeMData then
    if let some { companion? := some c, .. } := ctx.locals.get? id then return c
  let t ← whnfR (← inferType a)
  forallTelescope t fun ys _ => do
    mkLambdaFVars ys (← costOf ctx (mkAppN a ys).headBeta)

/-- The arguments of a registered cost: each function-typed argument followed by its cost
companion. -/
partial def costArgs (ctx : Ctx) (f : Expr) (args : Array Expr) : TermElabM (Array Expr) := do
  let kinds ← argKinds f args
  let mut out := #[]
  for a in args, (k, _) in kinds do
    out := out.push a
    if k == .fn || k == .treeFn then out := out.push (← companionOf ctx a)
  return out

/-- The cost of the application `e` of a constant or a local. -/
partial def costApp (ctx : Ctx) (e : Expr) : TermElabM Expr := do
  let f := e.getAppFn
  let args := e.getAppArgs
  match f with
  | .fvar id =>
    match ctx.locals.get? id with
    | some { kind := .fn, companion? := some c, .. } =>
      let arity ← forallTelescope (← whnfR (← inferType c)) fun ys _ => pure ys.size
      if args.size < arity then argsCost ctx args
      else if args.size == arity then
        return add (natE 1) (add (mkAppN c args) (← argsCost ctx args))
      else fail m!"the local function `{f}` is applied to more arguments than its companion takes"
    | some _ => fail m!"the oracle tree `{f}` occurs in a data position in `{e}`"
    | none =>
      if args.isEmpty then return natE 0
      fail m!"a function bound in data: the local `{f}` in `{e}` has no cost companion"
  | .const c _ => costConst ctx e c args
  | .proj S i s =>
    -- A field of a structure applied: priced as its projection function.
    let some info := getStructureInfo? (← getEnv) S
      | fail m!"the application `{e}` is headed by a projection of a non-structure"
    let some field := info.fieldNames[i]? | fail m!"the projection `{f}` has no field {i}"
    let pf ← mkAppM (S ++ field) #[s]
    costConst ctx (mkAppN pf args) (S ++ field) (pf.getAppArgs ++ args)
  | _ => fail m!"the application `{e}` is not headed by a constant or a local"

/-- The cost of an application of the constant `c`. -/
partial def costConst (ctx : Ctx) (e : Expr) (c : Name) (args : Array Expr) :
    TermElabM Expr := do
  let env ← getEnv
  let f := e.getAppFn
  if freeConstants.contains c || env.isConstructor c then
    return ← argsCost ctx args
  -- A partial application is a closure.
  let arity ← forallTelescope (← inferType f) fun ys _ => pure ys.size
  if args.size < arity then return ← argsCost ctx args
  if isCasesOnRecursor env c then
    return ← costCases ctx e c args
  -- A registered cost.
  let reg := c ++ `timedCost
  if env.contains reg then
    let regArgs ← costArgs ctx f args
    let regE ← mkAppOptM reg (regArgs.map some)
    return add (natE 1) (add regE (← argsCost ctx args))
  if natUnitOps.contains c && args.size > 0 && (args[0]!).isConstOf ``Nat then
    return add (natE 1) (← argsCost ctx args)
  if c == ``Decidable.decide && args.size == 2 then
    return add (natE 1) (← propCost ctx args[0]!)
  if c == ``ite && args.size == 5 then
    return add (natE 1) (add (← propCost ctx args[1]!)
      (mkApp5 (mkConst ``ite [Level.one]) (mkConst ``Nat) args[1]! args[2]!
        (← costOf ctx args[3]!) (← costOf ctx args[4]!)))
  if c == ``dite && args.size == 5 then
    let ct ← withEta args[3]! 1 fun hs b => do mkLambdaFVars hs (← costOf ctx b)
    let ce ← withEta args[4]! 1 fun hs b => do mkLambdaFVars hs (← costOf ctx b)
    return add (natE 1) (add (← propCost ctx args[1]!)
      (mkApp5 (mkConst ``dite [Level.one]) (mkConst ``Nat) args[1]! args[2]! ct ce))
  if ← isMatcher c then
    return ← costMatch ctx e
  -- A structure projection.
  if let some info ← getProjectionFnInfo? c then
    if info.fromClass then
      let inst := args[info.numParams]!
      if inst.consumeMData.isFVar then
        fail m!"needs a registered primitive: the class method `{c}` on the local instance \
          `{inst}` has no registered cost `{reg}`"
      let some e' ← unfoldProjInst? e
        | fail m!"needs a registered primitive: the class method `{c}` does not unfold"
      if ctx.depth ≥ maxDepth then fail m!"needs a registered primitive: `{c}` unfolds too deep"
      return ← costOf { ctx with depth := ctx.depth + 1 } e'
    if args.size > info.numParams + 1 then
      fail m!"a function bound in data: the field `{c}` is applied in `{e}`"
    return ← argsCost ctx args
  -- A definition, unfolded.
  let some info := env.find? c | fail m!"unknown constant `{c}`"
  if Structural.eqnInfoExt.find? env c |>.isSome then
    fail m!"needs a registered primitive: `{c}` is recursive and has no registered cost `{reg}`"
  if WF.eqnInfoExt.find? env c |>.isSome then
    fail m!"needs a registered primitive: `{c}` is recursive and has no registered cost `{reg}`"
  unless info matches .defnInfo _ do
    fail m!"needs a registered primitive: `{c}` has no definition to price and no registered \
      cost `{reg}`"
  if ctx.depth ≥ maxDepth then
    fail m!"needs a registered primitive: `{c}` unfolds deeper than {maxDepth} definitions"
  let some e' ← withTransparency .all (unfoldDefinition? e)
    | fail m!"needs a registered primitive: `{c}` does not unfold"
  let e' := e'.headBeta
  if (e'.find? fun s => s.isConstOf ``WellFounded.fix || s.isAppOf ``Nat.rec
      || s.isAppOf ``List.rec).isSome then
    fail m!"needs a registered primitive: `{c}` unfolds to a recursor"
  -- An abbreviation is notation: unfolded without the cost of a call.
  let callCost := if ← isReducible c then natE 0 else natE 1
  return add callCost (← costOf { ctx with depth := ctx.depth + 1 } e')

/-- The cost of a data-valued `casesOn` of an inductive type without indices: one, the major
premise, and the branch taken. -/
partial def costCases (ctx : Ctx) (e : Expr) (c : Name) (args : Array Expr) :
    TermElabM Expr := do
  let some (.inductInfo iv) := (← getEnv).find? c.getPrefix
    | fail m!"`{c}` is not the case analysis of an inductive type"
  unless iv.numIndices == 0 do fail m!"the case analysis `{e}` is over an indexed family"
  let arity := iv.numParams + 2 + iv.numCtors
  unless args.size == arity do
    fail m!"the case analysis `{e}` has a motive that depends on further arguments"
  let major := args[iv.numParams + 1]!
  let motive ← withLocalDeclD `x (← inferType major) fun x => mkLambdaFVars #[x] (mkConst ``Nat)
  let mut minors := #[]
  for i in [0:iv.numCtors] do
    let ctor ← getConstInfoCtor iv.ctors[i]!
    let minor := args[iv.numParams + 2 + i]!
    minors := minors.push (← withEta minor ctor.numFields fun fs b => do
      mkLambdaFVars fs (← costOf ctx b))
  let levels := match e.getAppFn.constLevels! with
    | _ :: ls => Level.one :: ls
    | [] => []
  let cases := mkAppN (mkConst c levels)
    (args[0:iv.numParams].toArray ++ #[motive, major] ++ minors)
  return add (natE 1) (add (← costOf ctx major) cases)

/-- The matcher application `e` with its discriminants and alternatives prepared for a
translation with result type `resultType`: the translated discriminants replaced by their
erasures, and each alternative translated by `alt` in the context in which its fields stand
for the translated discriminants they bind. Returns the new application and the cost of the
data discriminants. -/
partial def mapMatch (ctx : Ctx) (e resultType : Expr)
    (alt : Ctx → Expr → TermElabM Expr) : TermElabM (Expr × Expr) := do
  let some app ← matchMatcherApp? e | fail m!"`{e}` is not a matcher application"
  unless app.remaining.isEmpty do
    fail m!"the match `{e}` has a motive that depends on its discriminants"
  let mut discrs := #[]
  let mut trDiscrs : Array (Expr × LocalInfo) := #[]
  let mut cost := natE 0
  for d in app.discrs do
    if let some Td ← treeTy? (← inferType d) then
      fail m!"a recursion over an {Td.kind.noun}: a match on the {Td.kind.noun} `{d}`; register \
        a costed form written by hand"
    match d.consumeMData with
    | .fvar id =>
      match ctx.locals.get? id with
      | some info =>
        let dt ← inferType d
        if info.kind == .fn then discrs := discrs.push d
        else discrs := discrs.push (← erasure info.kind dt info.value)
        trDiscrs := trDiscrs.push (dt, info)
      | none => discrs := discrs.push d
    | _ =>
      discrs := discrs.push d
      cost := add cost (← costOf ctx d)
  let motive ← lambdaTelescope app.motive fun xs _ => mkLambdaFVars xs resultType
  let lvl ← getLevel resultType
  let levels := match app.uElimPos? with
    | some i => app.matcherLevels.set! i lvl
    | none => app.matcherLevels
  let matcherType ← instantiateForall
    (← inferType (mkConst app.matcherName levels.toList)) (app.params ++ #[motive] ++ discrs)
  let mut alts := #[]
  let mut ty := matcherType
  for a in app.alts do
    let .forallE _ aty body _ ← whnf ty | fail m!"the match `{e}` has an unexpected type"
    let n ← forallTelescope aty fun ys _ => pure ys.size
    let a' ← lambdaBoundedTelescope a n fun fs b => do
      let mut ctx' := ctx
      for fv in fs do
        let ft ← inferType fv
        let mut found : Option LocalInfo := none
        for (dt, info) in trDiscrs do
          if ← isDefEq ft dt then
            if found.isSome then
              fail m!"the match `{e}` binds two translated discriminants of type `{ft}`"
            found := some info
        if let some info := found then
          ctx' := { ctx' with locals := ctx'.locals.insert fv.fvarId! info }
      mkLambdaFVars fs (← alt ctx' b)
    alts := alts.push a'
    ty := body.instantiate1 a'
  let e' := mkAppN (mkConst app.matcherName levels.toList)
    (app.params ++ #[motive] ++ discrs ++ alts)
  return (e', cost)

/-- The cost of a data-valued match: one, the discriminants, and the branch taken. -/
partial def costMatch (ctx : Ctx) (e : Expr) : TermElabM Expr := do
  let (e', cd) ← mapMatch ctx e (mkConst ``Nat) costOf
  return add (natE 1) (add cd e')

/-- The translation of the oracle tree `e`: a step-prefixed costed tree whose erasure is `e`
with the translated locals erased. -/
partial def tr (ctx : Ctx) (e : Expr) : TermElabM Expr := do
  let e := e.consumeMData.headBeta
  let some T ← treeTy? (← inferType e)
    | fail m!"`{e}` is not a tree of a registered kind"
  match e with
  | .letE _ _ v b _ => tr ctx (b.instantiate1 v)
  | .fvar id =>
    match ctx.locals.get? id with
    | some { kind := .tree, value, .. } => return T.mkPair (natE 0) value
    | _ => fail m!"a function bound in data: the {T.kind.noun} `{e}` has no costed form"
  | .app .. | .const .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .fvar id =>
      match ctx.locals.get? id with
      | some { kind := .treeFn, value, companion? := some c } =>
        return T.mkPair (add (natE 1) (add (mkAppN c args) (← argsCost ctx args)))
          (mkAppN value args)
      | _ => fail m!"a function bound in data: the local `{f}` in `{e}` has no costed form"
    | .const c _ => trConst ctx e c args T
    | _ => fail m!"the {T.kind.noun} `{e}` is not headed by a constant or a local"
  | _ => fail m!"the {T.kind.noun} `{e}` is not supported"

/-- The translation of a continuation `a` with `n` binders: its step cost and its costed tree,
both abstracted over the binders. -/
partial def trCont (ctx : Ctx) (a : Expr) (n : Nat) : TermElabM (Expr × Expr) := do
  if n == 0 then
    let some Ta ← treeTy? (← inferType a) | fail m!"`{a}` is not a tree of a registered kind"
    let p ← tr ctx a
    return (Ta.fstOf p, Ta.sndOf p)
  withEta a n fun ys b => do
    let some Tb ← treeTy? (← inferType b) | fail m!"`{b}` is not a tree of a registered kind"
    let p ← tr ctx b
    return (← mkLambdaFVars ys (Tb.fstOf p), ← mkLambdaFVars ys (Tb.sndOf p))

/-- The translation of a node: the costed constructor applied to the translated arguments, with
the costs of the data arguments as its step cost. The continuations are translated first. -/
partial def trNode (ctx : Ctx) (e : Expr) (nd : Node) (args : Array Expr) (T : TreeTy) :
    TermElabM Expr := do
  let xs ← trailing e args nd.roles
  let mut conts : Array (Option (Expr × Expr)) := Array.replicate xs.size none
  for h : i in [0:xs.size] do
    if let .cont m := nd.roles[i]! then
      conts := conts.set! i (some (← trCont ctx xs[i] m))
  let mut outs := #[]
  let mut cost := natE 0
  for h : i in [0:xs.size] do
    match nd.roles[i]!, conts[i]! with
    | .cont _, some (cs, ks) => outs := outs.push cs |>.push ks
    | .data, _ =>
      outs := outs.push xs[i]
      cost := add cost (← costOf ctx xs[i])
    | _, _ => outs := outs.push xs[i]
  let node ← mkAppM' (mkAppN (mkConst nd.tgt) T.params) outs
  return T.mkPair cost node

/-- The translation of a combinator: its costed form applied to the translated arguments, with
the step costs of the tree arguments and the costs of the data arguments in front. The tree
arguments are translated first. -/
partial def trComb (ctx : Ctx) (e : Expr) (cb : Comb) (args : Array Expr) (T : TreeTy) :
    TermElabM Expr := do
  let xs ← trailing e args cb.roles
  let mut trees : Array Expr := Array.replicate xs.size (natE 0)
  let mut treeCost := natE 0
  for h : i in [0:xs.size] do
    if cb.roles[i]! == .tree then
      let some Ta ← treeTy? (← inferType xs[i]) | fail m!"`{e}` has an unexpected type"
      let p ← tr ctx xs[i]
      trees := trees.set! i (Ta.sndOf p)
      treeCost := add treeCost (Ta.fstOf p)
  let mut outs := #[]
  let mut dataCost := natE 0
  for h : i in [0:xs.size] do
    let a := xs[i]
    match cb.roles[i]! with
    | .tree => outs := outs.push trees[i]!
    | .pairFn m => outs := outs.push (← withEta a m fun ys b => do mkLambdaFVars ys (← tr ctx b))
    | .perCall extra m =>
      let t ← withEta a m fun ys b => do mkLambdaFVars ys (add (natE extra) (← costOf ctx b))
      outs := outs.push a |>.push t
    | .data =>
      outs := outs.push a
      dataCost := add dataCost (← costOf ctx a)
    | .keep | .cont _ => outs := outs.push a
  let r ← mkAppM cb.tgt outs
  let r := if cb.pair then r else T.mkPair (natE 0) r
  return T.delayE (add treeCost dataCost) r

/-- The translation of a tree headed by the constant `c`. -/
partial def trConst (ctx : Ctx) (e : Expr) (c : Name) (args : Array Expr) (T : TreeTy) :
    TermElabM Expr := do
  let n := args.size
  if let some nd := T.kind.nodes.find? (·.src == c) then
    return ← trNode ctx e nd args T
  if let some cb := T.kind.combinators.find? (·.src == c) then
    return ← trComb ctx e cb args T
  if c == ``ite && n == 5 then
    let pt ← tr ctx args[3]!
    let pe ← tr ctx args[4]!
    let i := mkApp5 (mkConst ``ite [Level.succ Level.one]) T.pairType args[1]! args[2]! pt pe
    return T.delayE (add (natE 1) (← propCost ctx args[1]!)) i
  if c == ``dite && n == 5 then
    let pt ← withEta args[3]! 1 fun hs b => do mkLambdaFVars hs (← tr ctx b)
    let pe ← withEta args[4]! 1 fun hs b => do mkLambdaFVars hs (← tr ctx b)
    let i := mkApp5 (mkConst ``dite [Level.succ Level.one]) T.pairType args[1]! args[2]! pt pe
    return T.delayE (add (natE 1) (← propCost ctx args[1]!)) i
  if ← isMatcher c then
    let (e', cd) ← mapMatch ctx e T.pairType tr
    return T.delayE (add (natE 1) cd) e'
  -- A call of a reduction.
  let target ← match ctx.self? with
    | some (self, rec) => if self == c then pure rec else ensureTimed ctx c e.getAppFn
    | none => ensureTimed ctx c e.getAppFn
  callTimed ctx e target args T

/-- The costed form of the reduction `c` at the universe levels of `f`: registered, or
derived now. -/
partial def ensureTimed (ctx : Ctx) (c : Name) (f : Expr) : TermElabM Expr := do
  let name := c ++ ctx.suffix
  unless (← getEnv).contains name do
    if ctx.visiting.contains c then
      fail m!"`{c}` is reached again while its costed form is derived (mutual recursion)"
    try
      deriveTimed { ctx with visiting := ctx.visiting.insert c } c
    catch ex =>
      throwError m!"derive_timed: while deriving the costed form of the callee `{c}`:\n\
        {ex.toMessageData}"
  return mkConst name f.constLevels!

/-- A call of the reduction whose costed form is `target`: one plus the step cost of the
costed call plus the costs of the arguments. -/
partial def callTimed (ctx : Ctx) (e target : Expr) (args : Array Expr) (T : TreeTy) :
    TermElabM Expr := do
  let kinds ← argKinds e.getAppFn args
  let mut out := #[]
  let mut cost := natE 0
  for a in args, (k, _) in kinds do
    match k with
    | .static => out := out.push a
    | .data =>
      out := out.push a
      cost := add cost (← costOf ctx a)
    | .fn =>
      out := out.push a |>.push (← companionOf ctx a)
      cost := add cost (← costOf ctx a)
    | .tree =>
      let some Ta ← treeTy? (← inferType a)
        | fail m!"`{a}` is not a tree of a registered kind"
      let p ← tr ctx a
      out := out.push (Ta.sndOf p)
      cost := add cost (Ta.fstOf p)
    | .treeFn =>
      match a.consumeMData with
      | .fvar id =>
        match ctx.locals.get? id with
        | some { kind := .treeFn, value, companion? := some c } =>
          out := out.push value |>.push c
        | _ => fail m!"a function bound in data: `{a}` has no costed form"
      | _ =>
        let arity ← forallTelescope (← whnfR (← inferType a)) fun ys _ => pure ys.size
        let (v, c) ← withEta a arity fun ys b => do
          let some Tb ← treeTy? (← inferType b)
            | fail m!"`{b}` is not a tree of a registered kind"
          let p ← tr ctx b
          return (← mkLambdaFVars ys (Tb.sndOf p), ← mkLambdaFVars ys (Tb.fstOf p))
        out := out.push v |>.push c
  return T.delayE (add (natE 1) cost) (mkAppN target out)

/-- Derive and add the costed form `c.timed` and the erasure theorem `c.erase_timed` of the
reduction `c`. -/
partial def deriveTimed (ctx : Ctx) (c : Name) : TermElabM Unit := do
  let env ← getEnv
  let some info := env.find? c | fail m!"unknown constant `{c}`"
  let timedName := c ++ ctx.suffix
  let eraseName := c ++ (Name.mkSimple ("erase_" ++ ctx.suffix.toString))
  if env.contains timedName then fail m!"`{timedName}` already exists"
  let levels := info.levelParams.map mkLevelParam
  let recursive := (Structural.eqnInfoExt.find? env c).isSome || (WF.eqnInfoExt.find? env c).isSome
  let body ← match Structural.eqnInfoExt.find? env c, WF.eqnInfoExt.find? env c, info with
    | some i, _, _ => pure i.value
    | _, some i, _ => pure i.value
    | _, _, .defnInfo d => pure d.value
    | _, _, _ => fail m!"`{c}` has no definition to translate; register `{timedName}`"
  let type := info.type
  -- Eta-expand to all binders of the type.
  let value ← lambdaTelescope body fun xs b => do
    forallTelescope (← instantiateForall type xs) fun ys _ =>
      mkLambdaFVars (xs ++ ys) (mkAppN b ys).headBeta
  let (tType, tValue, eType, nBinders) ← lambdaTelescope value fun xs b => do
    let some T ← treeTy? (← inferType b)
      | fail m!"the result of `{c}` is not a tree of a registered kind"
    withBinders ctx xs fun ctx bs args => do
      let tType ← mkForallFVars bs T.pairType
      withLocalDeclD `rec tType fun recF => do
        let ctx := { ctx with self? := some (c, recF) }
        let p ← tr ctx b
        let p := p.replaceFVar recF (mkConst timedName levels)
        let tValue ← mkLambdaFVars bs p
        if tValue.containsFVar recF.fvarId! then fail m!"internal: the recursive call escaped"
        for x in xs do
          if tValue.containsFVar x.fvarId! && !(bs.contains x) then
            fail m!"the binder `{x}` of `{c}` occurs in a type of the costed form"
        let call := mkAppN (mkConst timedName levels) bs
        let lhs := T.eraseE (T.sndOf call)
        let rhs := mkAppN (mkConst c levels) args
        let eType ← mkForallFVars bs (← mkEq lhs rhs)
        let explicit ← bs.mapM fun b => return (← b.fvarId!.getBinderInfo).isExplicit
        return (tType, tValue, eType, explicit)
  addTimedDef timedName info.levelParams tType tValue
  -- The erasure theorem.
  let callees := collectTimed (← getEnv) ctx.suffix tValue timedName
  -- The erasure lemmas of the tree kinds whose costed trees occur in the costed form.
  let used := tType.getUsedConstants ++ tValue.getUsedConstants
  let kindLemmas := (treeKinds.filter fun k => used.contains k.timed).flatMap (·.eraseLemmas)
  let simpLemmas : Array Name := #[timedName, c] ++ kindLemmas ++ callees
  let ids : Array (TSyntax `ident) := (Array.range nBinders.size).map fun i =>
    mkIdent (Name.mkSimple s!"x{i}")
  let explicitIds := (ids.zip nBinders).filterMap fun (i, e) => if e then some i else none
  let lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    simpLemmas.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  let close ← `(tactic| ((try simp only [$lemmas,*, *]) <;> (try (repeat' split)) <;>
      (try simp only [$lemmas,*, *])))
  let tac ← if recursive then
      `(tactic| (intro $ids*; fun_induction $(mkIdent timedName):ident $explicitIds* <;> $close))
    else
      `(tactic| (intro $ids*; $close))
  let proof ← Term.withoutErrToSorry do
    let mv ← mkFreshExprMVar eType
    let rem ← Tactic.run mv.mvarId! (Tactic.evalTactic tac)
    unless rem.isEmpty do
      fail m!"the erasure theorem `{eraseName}` is not closed by unfolding and the erasure \
        lemmas; goals left:{indentD (MessageData.joinSep (rem.map (.ofGoal ·)) "\n")}"
    instantiateMVars mv
  if proof.hasSorry || proof.hasMVar then
    fail m!"the erasure theorem `{eraseName}` is not proved"
  let thm : TheoremVal :=
    { name := eraseName, levelParams := info.levelParams, type := eType, value := proof }
  addDecl (Declaration.thmDecl thm)

/-- The callees of `v` with a costed form `n.suffix` other than `self`, as their erasure
theorems. -/
partial def collectTimed (env : Environment) (suffix : Name) (v : Expr) (self : Name) :
    Array Name :=
  let eraseSuffix := Name.mkSimple ("erase_" ++ suffix.toString)
  v.getUsedConstants.foldl (init := #[]) fun acc n =>
    match n with
    | .str p s =>
      if n != self && s == suffix.toString then
        let thm := p ++ eraseSuffix
        if env.contains thm && !acc.contains thm then acc.push thm else acc
      else acc
    | _ => acc

/-- Add the definition `name`, settling its recursion as a `def`'s. -/
partial def addTimedDef (name : Name) (levelParams : List Name) (type value : Expr) :
    TermElabM Unit := do
  let saved := (← getThe Core.State).messages
  modifyThe Core.State fun s => { s with messages := {} }
  let outcome ← try
      addPreDefinitions ({}, {}) #[{
        ref := .missing, kind := .def, levelParams,
        modifiers := { computeKind := .noncomputable }, declName := name,
        binders := .missing, type, value, termination := .none }]
      pure none
    catch ex => pure (some ex.toMessageData)
  let msgs := (← getThe Core.State).messages
  modifyThe Core.State fun s => { s with messages := saved }
  let failure := match outcome with
    | some m => some m
    | none =>
      if msgs.hasErrors then
        some (MessageData.joinSep (msgs.toList.filterMap fun (m : Message) =>
          if m.severity == MessageSeverity.error then some m.data else none) "\n")
      else none
  if let some why := failure then
    fail m!"`{name}` could not be defined: {why}"

end

/-- `derive_timed R` defines the costed form `R.timed` of the reduction `R` and proves its
erasure theorem `R.erase_timed`; `derive_timed (suffix := s) R` names them `R.s` and
`R.erase_s`. -/
syntax (name := deriveTimedCmd) "derive_timed " ("(" &"suffix" " := " ident ") ")? ident :
  command

@[command_elab deriveTimedCmd]
def elabDeriveTimed : CommandElab := fun stx => do
  let suffix := match stx[1].getOptional? with
    | some s => s[3].getId
    | none => `timed
  let id := stx[2]
  liftTermElabM do
    let c ← realizeGlobalConstNoOverloadWithInfo id
    deriveTimed { suffix } c

/-- `timed_cost f := e` registers `e` as the cost of the primitive `f`: it defines
`f.timedCost := e`, which takes the arguments of `f`, each function-typed argument followed
by its cost companion. A registered cost is a trusted statement about the cost of `f`. -/
syntax (name := timedCostCmd) "timed_cost " ident " := " term : command

@[command_elab timedCostCmd]
def elabTimedCost : CommandElab := fun stx => do
  let c ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let e : TSyntax `term := ⟨stx[3]⟩
  elabCommand (← `(noncomputable def $(mkIdent (`_root_ ++ c ++ `timedCost)) := $e))

end CatCrypt.Tactics.DeriveTimed

end
