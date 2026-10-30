/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound

/-!
# Derived step costs with optional function-holding state and general sampling (draft)

A draft of `derive_timed` and `derive_reduction` (`CatCryptCore.Tactics.DeriveTimed`,
`CatCryptCore.Tactics.DeriveReduction`) in the namespaces `CatCrypt.Tactics.DeriveTimedFn` and
`CatCrypt.Tactics.DeriveReductionFn`, with the commands `derive_timed_fn`,
`derive_reduction_fn` and `derive_erases_hat_fn`, and of `time_bound` and `derive_time_bound`
(`CatCryptCore.Tactics.AutoTime`, `CatCryptCore.Tactics.DeriveTimeBound`) in the namespaces
`CatCrypt.Tactics.AutoTime.Fn` and `CatCrypt.Tactics.DeriveTimeBound.Fn`, with the tactics
`time_bound_fn`, `allret_bound_fn` and the command `derive_time_bound_fn`. The lemmas of the
committed modules are shared; the rules below are added.

## Optional values holding functions

The costed type of `Option t`, where `t` holds functions, is `Option t̂`: it is erased and
lifted by `Option.map`, the constructors `some a` and `none` are translated componentwise, and
the field `a` of a pattern `some a` of a match on a discriminant `o` with a costed value `ô`
reads its costed value as `Option.elim ô (ι a) id`.

## Case analysis of an optional value

A dispatch on an optional value, `Option.elim o y f`, `Option.casesOn o y f` or
`Option.rec y f o`, whose result is a tree or a computation, is the match of `optionDispatch`
on `o` with the alternatives `y` and `f` (`optionDispatch?`): the function `f` is an
alternative of the match and not a discriminant. On a constructor `o` it is the alternative of
that constructor.

## Sampling from a general distribution

`liftSDistr μ` (and `sampleFrom μ` of `CatCryptCore.NonUniform.Sample`) is reflected as the node
`SPTree.sampleDist β μ (fun b => .ret b)`, and `SPComp.bind (liftSDistr μ) k` as
`SPTree.sampleDist β μ (fun b => tree (k b))`. The node costs its unit (`SPTree.Timed.time`,
`SPTree.Timed.TimeBound`); the distribution `μ` is kept and not priced, since sampling is
included in the node's unit. The time of the node is `1 + ⨆ b, c b + time (k b)`; `time_bound_fn`
bounds it by `time_sampleDist` and `st_bind_sampleDist` from a bound for every sample, and
`derive_time_bound_fn` takes as its bound one plus the bound of the continuation at a fresh
sample.

## Main definitions

* `optionDispatch` — the case analysis of an optional value, written as a `match`
* `derive_timed_fn`, `derive_reduction_fn`, `derive_erases_hat_fn` — the commands
-/

public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimedFn

open CatCrypt.Core

/-- The case analysis of `x : Option α` by `n` on `none` and `s` on `some`, written as a
`match`. Its matcher `optionDispatch.match_1` is the form in which a dispatch `Option.elim x n s`,
`Option.casesOn x n s` or `Option.rec n s x` on an optional value that is not a constructor is
kept (`optionDispatch?`). -/
@[expose] def optionDispatch.{u, w} {α : Type u} (motive : Option α → Sort w) (x : Option α)
    (n : motive none) (s : (a : α) → motive (some a)) : motive x :=
  match x with
  | none => n
  | some a => s a

/-- `Option.elim` is the case analysis `optionDispatch` at the constant motive. -/
theorem elim_eq_optionDispatch {α β : Type} (x : Option α) (n : β) (s : α → β) :
    x.elim n s = optionDispatch (fun _ => β) x n s := by
  cases x <;> rfl

/-- The compile equation of a sampling node of a sub-distribution followed by a continuation. -/
theorem compile_sampleDist_eq {α β : Type} {μ : Prob.SDistr β} {k : β → SPTree α}
    {k₀ : β → SPComp α} (h : ∀ b, (k b).compile = k₀ b) :
    (SPTree.sampleDist β μ k).compile = SPComp.bind (liftSDistr μ) k₀ := by
  simp only [SPTree.compile, funext h]

/-- The compile equation of a sampling node of a sub-distribution that returns its sample. -/
theorem compile_sampleDist_ret {β : Type} {μ : Prob.SDistr β} :
    (SPTree.sampleDist β μ fun b => .ret b).compile = liftSDistr μ := by
  simp only [SPTree.compile]
  exact SPComp.bind_pure _

end CatCrypt.Tactics.DeriveTimedFn

meta section

namespace CatCrypt.Tactics.DeriveTimedFn

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
  /-- Data holding functions (a pair with a function component): replaced by its costed
  value, in which each function is a costed closure. -/
  | hat
  deriving Inhabited, BEq, Repr

/-- The translation of a local of the reduction: its kind, its costed value (the costed tree
for `tree` and `treeFn`, the local itself otherwise) and its cost companion. -/
structure LocalInfo where
  kind : Kind
  value : Expr
  companion? : Option Expr := none
  deriving Inhabited

/-- The context of a translation: the translated locals, the reduction being derived with
the local that stands for its costed form, the suffix of costed forms, the unfolding
depth of data functions, the fields of local structures and instances, each applied to its
parameters and its structure, with their cost companions, the binders of the reduction, at
which field paths start, the reference collecting the field paths without a cost companion
(`fieldRec?`, in the first pass), and the data functions whose costs are being derived (the
members of a mutual block), each with the local that stands for its cost (`selfCosts`). -/
structure Ctx where
  locals : FVarIdMap LocalInfo := {}
  self? : Option (Name × Expr) := none
  suffix : Name := `timed
  depth : Nat := 0
  visiting : NameSet := {}
  fields : Array (Expr × Expr) := #[]
  top : Array FVarId := #[]
  fieldRec? : Option (IO.Ref (Array Expr)) := none
  selfCosts : Array (Name × Expr) := #[]
  /-- The binders of kind `hat` with the erasures `ε x̂` of their costed values, substituted
  for them in the costed form. -/
  hatSubst : Array (Expr × Expr) := #[]
  /-- The costed form has the plain interface of the reduction: a binder holding functions
  takes its plain value, whose functions are tables (`ι`), and the result is erased to the
  plain type (`ε`). The tree of a field of a structure-valued reduction has this interface, the
  one its costed mirror takes. -/
  plain : Bool := false
  /-- The data definitions unfolded in the costed value whose body is a match: unfolded by the
  erasure theorem, so that the hypotheses of its case split rewrite their discriminants. -/
  unfolded? : Option (IO.Ref (Array Name)) := none
  /-- The naturality lemmas `c.bind_ret` of the registered callees `c` called at a costed
  instance of the type parameter that is the result type of a tree argument (`callTimed`):
  rewriting lemmas of the erasure theorem. -/
  natural? : Option (IO.Ref (Array Name)) := none
  /-- The recursive data function whose costed value is being derived, with the local that
  stands for its costed value (`deriveHatValue`). -/
  selfHat? : Option (Name × Expr) := none


/-- Whether the constant `n` is a case analysis: a matcher, `ite` or `dite`. A data definition
whose body is headed by one is unfolded by the erasure theorem, so that its cases meet the
cases of the costed value. -/
def isCaseHead (env : Environment) (n : Name) : Bool :=
  isMatcherCore env n || n == ``ite || n == ``dite

/-- The body of the `let` telescope `e`: a definition `let c := v; match c.f with …` is headed by
its match. -/
partial def letBody (e : Expr) : Expr :=
  match e.consumeMData with
  | .letE _ _ _ b _ => letBody b
  | e' => e'

/-- The maximal nesting of unfolded data definitions: the option `derive_timed.maxDepth`, read
by its name, so that a command of this module runs before the option's initializer has (the
tests of the module). -/
def maxDepth : CoreM Nat := return (← getOptions).get `derive_timed.maxDepth (16 : Nat)

/-- Constants that cost nothing beyond their arguments. -/
def freeConstants : Array Name :=
  #[``OfNat.ofNat, ``Nat.cast, ``NatCast.natCast, ``Int.cast, ``IntCast.intCast, ``id,
    ``Eq.rec, ``Eq.ndrec, ``Eq.mp, ``Eq.mpr, ``cast, ``Subtype.val, ``Fin.val,
    ``PMF.uniformFintype, ``PMF.pure, ``Classical.arbitrary, ``Inhabited.default,
    ``Fin.elim0, ``False.elim, ``absurd, ``Empty.elim, ``PEmpty.elim]

/-- The namespaces of the operations on quotient types (`Finset`, `Multiset`, `Quot`,
`Quotient`), which are priced by a registered cost and never unfolded. -/
def quotientLibs : Array Name := #[`Finset, `Multiset, `Quot, `Quotient]

/-- Operations of unit cost on `ℕ`: a call costs one. -/
def natUnitOps : Array Name :=
  #[``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HMod.hMod, ``Nat.succ, ``Nat.add,
    ``Nat.sub, ``Nat.mul, ``Nat.div, ``Nat.mod, ``Nat.pred, ``Nat.min, ``Nat.max, ``Min.min,
    ``Max.max]

/-- Arithmetic operations of unit cost on `ZMod p`, whose elements are words for the fixed
modulus `p`: a call costs one. -/
def zmodUnitOps : Array Name :=
  #[``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``Add.add, ``Sub.sub,
    ``Mul.mul, ``Div.div, ``Neg.neg, ``Inv.inv]

/-- Arithmetic, bitwise and comparison operations of unit cost on fixed-width words
(`BitVec n`, `UInt8`, `UInt16`, `UInt32`, `UInt64`, `Fin n`): a call costs one (word-RAM). -/
def wordUnitOps : Array Name :=
  #[``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HMod.hMod, ``Add.add, ``Sub.sub,
    ``Mul.mul, ``Div.div, ``Mod.mod, ``Neg.neg, ``HAnd.hAnd, ``HOr.hOr, ``HXor.hXor,
    ``HShiftLeft.hShiftLeft, ``HShiftRight.hShiftRight, ``AndOp.and, ``OrOp.or, ``XorOp.xor,
    ``ShiftLeft.shiftLeft, ``ShiftRight.shiftRight, ``Complement.complement, ``BEq.beq,
    ``Max.max, ``Min.min]

/-- Whether the instance `inst` is built from a local instance: it mentions a local whose type
is a class (a section variable or a binder `[AddCommGroup M]`). -/
def builtFromLocalInstance (inst : Expr) : MetaM Bool := do
  let fvs := (collectFVars {} inst).fvarIds
  fvs.anyM fun fv => do
    let some d := (← getLCtx).find? fv | return false
    return (← isClass? d.type).isSome

/-- The methods of the algebraic operation classes: on a local instance (an abstract algebraic
structure) a call costs one unit, as one call of the interface. -/
def algebraicMethods : Array Name :=
  #[``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HMod.hMod, ``HPow.hPow, ``HSMul.hSMul,
    ``HVAdd.hVAdd, ``Add.add, ``Sub.sub, ``Mul.mul, ``Div.div, ``Mod.mod, ``Neg.neg, ``Inv.inv,
    ``Pow.pow, ``SMul.smul, ``VAdd.vadd, ``Zero.zero, ``One.one, ``OfNat.ofNat]

/-- Whether the class method `c` is a unit operation on a local instance: a method of an
algebraic operation class, or a word operation of `CryptoWord`. The methods of other classes
(the primitive interfaces of a protocol, `WireGuardDependencies.aead_enc`) keep their cost
companions. -/
def isUnitMethod (c : Name) : Bool :=
  algebraicMethods.contains c || c.getPrefix == `CatCrypt.Crypto.CryptoWord

/-- Whether `t` is a fixed-width word type: `BitVec n`, `UInt8` to `UInt64` or `Fin n`. -/
def isWordType (t : Expr) : MetaM Bool := do
  let t ← whnfR t
  return t.isAppOfArity ``BitVec 1 || t.isAppOfArity ``Fin 1 || t.isConstOf ``UInt8 ||
    t.isConstOf ``UInt16 || t.isConstOf ``UInt32 || t.isConstOf ``UInt64

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
  /-- The lemmas that push the erasure `ε` of a result holding functions to the leaves. -/
  hatLemmas : Array Name := #[]
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
    ``CatCrypt.Crypto.OracleAdv.Timed.erase_snd_dite,
    ``CatCrypt.Crypto.OracleAdv.Timed.erase_ofAdv]
  hatLemmas := #[``CatCrypt.Crypto.OracleAdv.bind, ``CatCrypt.Crypto.OracleAdv.bind_assoc,
    ``CatCrypt.Crypto.OracleAdv.bind_ret,
    ``CatCrypt.Crypto.OracleAdv.Timed.erase_simulateHat_bind, ``Prod.mk.eta,
    ``Sum.map_inl, ``Sum.map_inr, ``Option.map_some, ``Option.map_none,
    ``CatCrypt.Crypto.OracleAdv.Timed.bind_ret_eq,
    ``CatCrypt.Tactics.DeriveTimed.fst_ite, ``CatCrypt.Tactics.DeriveTimed.snd_ite,
    ``CatCrypt.Tactics.DeriveTimed.ite_prod_mk, ``CatCrypt.Tactics.DeriveTimed.erase_ite_oracle]

/-- Syntactic computation trees `SPTree α`: `ret`, `sample`, `sampleDist` (its distribution kept
and not priced), `get`, `set`, `fail` and `load`
nodes, and the combinators `SPTree.bind` and `SPTree.map`. -/
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
    ⟨``CatCrypt.Core.SPTree.sampleDist, ``CatCrypt.Core.SPTree.Timed.sampleDist,
      #[.keep, .keep, .cont 1]⟩,
    ⟨``CatCrypt.Core.SPTree.get, ``CatCrypt.Core.SPTree.Timed.get, #[.data, .cont 1]⟩,
    ⟨``CatCrypt.Core.SPTree.set, ``CatCrypt.Core.SPTree.Timed.set, #[.data, .data, .cont 0]⟩,
    ⟨``CatCrypt.Core.SPTree.fail, ``CatCrypt.Core.SPTree.Timed.fail, #[]⟩,
    ⟨``CatCrypt.Core.SPTree.load, ``CatCrypt.Core.SPTree.Timed.load, #[.data, .cont 0]⟩]
  combinators := #[
    ⟨``CatCrypt.Core.SPTree.bind, ``CatCrypt.Core.SPTree.Timed.bind, #[.tree, .pairFn 1], true⟩,
    ⟨``CatCrypt.Core.SPTree.map, ``CatCrypt.Core.SPTree.Timed.map, #[.perCall 0 1, .tree],
      true⟩]
  eraseLemmas := #[``CatCrypt.Core.SPTree.Timed.erase_ret,
    ``CatCrypt.Core.SPTree.Timed.erase_sample, ``CatCrypt.Core.SPTree.Timed.erase_sampleDist,
    ``CatCrypt.Core.SPTree.Timed.erase_get,
    ``CatCrypt.Core.SPTree.Timed.erase_set, ``CatCrypt.Core.SPTree.Timed.erase_fail,
    ``CatCrypt.Core.SPTree.Timed.erase_load,
    ``CatCrypt.Core.SPTree.Timed.delay, ``CatCrypt.Core.SPTree.Timed.erase_bind,
    ``CatCrypt.Core.SPTree.Timed.erase_map, ``CatCrypt.Core.SPTree.Timed.erase_snd_ite,
    ``CatCrypt.Core.SPTree.Timed.erase_snd_dite]
  hatLemmas := #[``CatCrypt.Core.SPTree.bind, ``CatCrypt.Core.SPTree.bind_assoc,
    ``CatCrypt.Core.SPTree.bind_ret_val, ``CatCrypt.Core.SPTree.bind_ret, ``Prod.mk.eta,
    ``Sum.map_inl, ``Sum.map_inr, ``Option.map_some, ``Option.map_none,
    ``CatCrypt.Tactics.DeriveTimed.fst_ite,
    ``CatCrypt.Tactics.DeriveTimed.snd_ite, ``CatCrypt.Tactics.DeriveTimed.ite_prod_mk,
    ``CatCrypt.Tactics.DeriveTimed.erase_ite_spTree]

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

/-- The tree type. -/
def type (T : TreeTy) : Expr := mkAppN (mkConst T.kind.tree) T.params

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

/-- The result type of the tree type. -/
def result (T : TreeTy) : Expr := T.params[T.params.size - 1]!

end TreeTy

/-- A structure whose costed value is a mirror: its name, constructor, universe levels and
parameters at a type, the projections and the types of its fields. -/
structure MirrorStruct where
  struct : Name
  ctor : Name
  levels : List Level
  params : Array Expr
  projs : Array Name
  fieldTypes : Array Expr

/-- The structure `S ps` of the type `tw` (in weak head normal form), when its costed value is
a mirror: a structure that is not a class nor `Prod`, with at least one field, whose fields
are data of types that do not depend on the other fields. -/
def mirrorStruct? (tw : Expr) : MetaM (Option MirrorStruct) := do
  let .const S lvls := tw.getAppFn | return none
  if S == ``Prod || S == ``Sum then return none
  let env ← getEnv
  unless isStructure env S do return none
  if isClass env S then return none
  let some (.inductInfo ii) := env.find? S | return none
  unless ii.numIndices == 0 && tw.getAppNumArgs == ii.numParams do return none
  let [ctor] := ii.ctors | return none
  let fields := getStructureFields env S
  if fields.isEmpty then return none
  let some (.ctorInfo ci) := env.find? ctor | return none
  let cty ← instantiateForall (ci.type.instantiateLevelParams ci.levelParams lvls)
    tw.getAppArgs
  forallTelescope cty fun fs _ => do
    unless fs.size == fields.size do return none
    let mut tys := #[]
    for f in fs do
      let ft ← inferType f
      if ft.hasAnyFVar fun x => fs.any (·.fvarId! == x) then return none
      if ← isProp ft then return none
      if ← isTypeFormerType ft then return none
      if (← isClass? ft).isSome then return none
      tys := tys.push ft
    return some { struct := S, ctor, levels := lvls, params := tw.getAppArgs,
                  projs := fields.map (S ++ ·), fieldTypes := tys }

/-- The mirror type `h₀ × (h₁ × … × hₙ₋₁)` of the costed field types `hs` (`h₀` for one
field). -/
def mirrorType (hs : Array Expr) : MetaM Expr := do
  let some last := hs.back? | throwError "derive_timed: internal: a mirror of no field"
  hs.pop.foldrM (fun h acc => mkAppM ``Prod #[h, acc]) last

/-- The mirror tuple of the costed field values `vs`. -/
def mirrorMk (vs : Array Expr) : MetaM Expr := do
  let some last := vs.back? | throwError "derive_timed: internal: a mirror of no field"
  vs.pop.foldrM (fun v acc => mkAppM ``Prod.mk #[v, acc]) last

/-- The component `i` of the mirror tuple `v` of `n` fields, reduced on a literal tuple. -/
def mirrorProj (n i : Nat) (v : Expr) : MetaM Expr := do
  let proj (fst : Bool) (v : Expr) : MetaM Expr := do
    if v.isAppOfArity ``Prod.mk 4 then return v.getArg! (if fst then 2 else 3)
    mkAppM (if fst then ``Prod.fst else ``Prod.snd) #[v]
  let mut cur := v
  for _ in [0:i] do cur ← proj false cur
  if i + 1 < n then proj true cur else return cur

/-- The costed type of a type `t` of data holding functions: a function `X → Y` with a
first-order domain becomes the costed closure `(X → Ŷ) × (X → ℕ)`, a pair the pair of the
costed types of its components; `none` when `t` holds no such function, whose costed type is
`t` itself. With `mirror := false` a structure is not mirrored: the result is `none` for a
type whose functions are all in fields of structures. -/
partial def hatTy? (t : Expr) (seen : List Name := []) (mirror : Bool := true) :
    MetaM (Option Expr) := do
  let t ← instantiateMVars t
  if ← isProp t then return none
  if ← isTypeFormerType t then return none
  if (← isClass? t).isSome then return none
  if (← treeTy? t).isSome then return none
  let tw ← whnfR t
  if tw.isAppOfArity ``Prod 2 then
    let a := tw.getArg! 0
    let b := tw.getArg! 1
    let ha ← hatTy? a seen mirror
    let hb ← hatTy? b seen mirror
    if ha.isNone && hb.isNone then return none
    return some (← mkAppM ``Prod #[ha.getD a, hb.getD b])
  if tw.isAppOfArity ``Sum 2 then
    let a := tw.getArg! 0
    let b := tw.getArg! 1
    let ha ← hatTy? a seen mirror
    let hb ← hatTy? b seen mirror
    if ha.isNone && hb.isNone then return none
    return some (← mkAppM ``Sum #[ha.getD a, hb.getD b])
  if tw.isAppOfArity ``Option 1 then
    let some ha ← hatTy? (tw.getArg! 0) seen mirror | return none
    return some (← mkAppM ``Option #[ha])
  if let some m ← mirrorStruct? tw then
    if seen.contains m.struct || !mirror then return none
    let hs ← m.fieldTypes.mapM (hatTy? · (m.struct :: seen))
    if hs.all (·.isNone) then return none
    return some (← mirrorType ((m.fieldTypes.zip hs).map fun (f, h) => h.getD f))
  unless tw.isForall do return none
  forallTelescope tw fun ys body => do
    if body.hasAnyFVar fun f => ys.any (·.fvarId! == f) then return none
    for y in ys do
      let yt ← inferType y
      if ← isProp yt then return none
      if ← isTypeFormerType yt then return none
      if (← isClass? yt).isSome then return none
      if (← hatTy? yt).isSome then return none
      if (← treeTy? yt).isSome then return none
    if ← isProp body then return none
    if ← isTypeFormerType body then return none
    if (← treeTy? body).isSome then return none
    if ← isProp (← inferType body) then return none
    let hb ← hatTy? body
    let fnT ← mkForallFVars ys (hb.getD body)
    let cT ← mkForallFVars ys (mkConst ``Nat)
    return some (← mkAppM ``Prod #[fnT, cT])

/-- `Sum.map` of `f` at the components of the sum `a ⊕ b` applied to `v`: with `f = epsE` from
the costed sum to `a ⊕ b`, with `f = iotaE` from `a ⊕ b` to the costed sum. -/
def sumMapE (a b v : Expr) (f : Expr → Expr → MetaM Expr) : MetaM Expr := do
  let vt ← whnfR (← inferType v)
  let side (i : Nat) (c : Expr) : MetaM Expr := do
    withLocalDeclD `x (vt.getArg! i) fun x => do mkLambdaFVars #[x] (← f c x)
  mkAppM ``Sum.map #[← side 0 a, ← side 1 b, v]

/-- `Option.map` of `f` at the content `a` of the optional value `v`: with `f = epsE` from the
costed option to `Option a`, with `f = iotaE` from `Option a` to the costed option. -/
def optionMapE (a v : Expr) (f : Expr → Expr → MetaM Expr) : MetaM Expr := do
  let vt ← whnfR (← inferType v)
  let g ← withLocalDeclD `x (vt.getArg! 0) fun x => do mkLambdaFVars #[x] (← f a x)
  mkAppM ``Option.map #[g, v]

/-- The erasure `ε v : t` of the costed value `v` of type `hatTy? t`: the function of each
costed closure. -/
partial def epsE (t v : Expr) : MetaM Expr := do
  let some _ ← hatTy? t | return v
  let tw ← whnfR t
  if tw.isAppOfArity ``Prod 2 then
    let a ← epsE (tw.getArg! 0) (← mkAppM ``Prod.fst #[v])
    let b ← epsE (tw.getArg! 1) (← mkAppM ``Prod.snd #[v])
    return ← mkAppM ``Prod.mk #[a, b]
  if tw.isAppOfArity ``Sum 2 then
    return ← sumMapE (tw.getArg! 0) (tw.getArg! 1) v epsE
  if tw.isAppOfArity ``Option 1 then
    return ← optionMapE (tw.getArg! 0) v epsE
  if let some m ← mirrorStruct? tw then
    let n := m.fieldTypes.size
    let mut fs := #[]
    for i in [0:n] do
      fs := fs.push (← epsE m.fieldTypes[i]! (← mirrorProj n i v))
    return mkAppN (mkConst m.ctor m.levels) (m.params ++ fs)
  let f ← mkAppM ``Prod.fst #[v]
  forallTelescope tw fun ys body => do
    if (← hatTy? body).isNone then return f
    mkLambdaFVars ys (← epsE body (mkAppN f ys))

/-- The lift `ι v : hatTy? t` of the value `v : t`: each function with the cost companion
zero. -/
partial def iotaE (t v : Expr) : MetaM Expr := do
  let some _ ← hatTy? t | return v
  let tw ← whnfR t
  if tw.isAppOfArity ``Prod 2 then
    let a ← iotaE (tw.getArg! 0) (← mkAppM ``Prod.fst #[v])
    let b ← iotaE (tw.getArg! 1) (← mkAppM ``Prod.snd #[v])
    return ← mkAppM ``Prod.mk #[a, b]
  if tw.isAppOfArity ``Sum 2 then
    return ← sumMapE (tw.getArg! 0) (tw.getArg! 1) v iotaE
  if tw.isAppOfArity ``Option 1 then
    return ← optionMapE (tw.getArg! 0) v iotaE
  if let some m ← mirrorStruct? tw then
    let mut fs := #[]
    for i in [0:m.fieldTypes.size] do
      let pf := mkAppN (mkConst m.projs[i]! m.levels) (m.params.push v)
      fs := fs.push (← iotaE m.fieldTypes[i]! pf)
    return ← mirrorMk fs
  forallTelescope tw fun ys body => do
    let f ← mkLambdaFVars ys (← iotaE body (mkAppN v ys).headBeta)
    let c ← mkLambdaFVars ys (mkNatLit 0)
    mkAppM ``Prod.mk #[f, c]

/-- The erasure function `fun y => ε y` of the type `t`. -/
def epsFun (t : Expr) : MetaM Expr := do
  let some ht ← hatTy? t | throwError "derive_timed: internal: `{t}` holds no function"
  withLocalDeclD `y ht fun y => do mkLambdaFVars #[y] (← epsE t y)

/-- The lift function `fun y => ι y` of the type `t`. -/
def iotaFun (t : Expr) : MetaM Expr := do
  withLocalDeclD `y t fun y => do mkLambdaFVars #[y] (← iotaE t y)

/-- The components of the erasure `ε v : t` of the costed value `v` (`epsE`), each with the
component of `x : t` at the same position: the pairs `(vᵢ, xᵢ)` such that `ε v = x` gives
`vᵢ = xᵢ` by projections. A component is a first-order field (`vᵢ` a projection of `v`) or a
function whose results hold no function (`vᵢ` the function of a costed closure); the
components inside a sum or inside the results of a function are left out. -/
partial def epsLeaves (t v x : Expr) : MetaM (Array (Expr × Expr)) := do
  let some _ ← hatTy? t | return #[(v, x)]
  let tw ← whnfR t
  if tw.isAppOfArity ``Prod 2 then
    let a ← epsLeaves (tw.getArg! 0) (← mkAppM ``Prod.fst #[v]) (← mkAppM ``Prod.fst #[x])
    let b ← epsLeaves (tw.getArg! 1) (← mkAppM ``Prod.snd #[v]) (← mkAppM ``Prod.snd #[x])
    return a ++ b
  if tw.isAppOfArity ``Sum 2 || tw.isAppOfArity ``Option 1 then return #[]
  if let some m ← mirrorStruct? tw then
    let n := m.fieldTypes.size
    let mut out := #[]
    for i in [0:n] do
      let xi := mkAppN (mkConst m.projs[i]! m.levels) (m.params.push x)
      out := out ++ (← epsLeaves m.fieldTypes[i]! (← mirrorProj n i v) xi)
    return out
  forallTelescope tw fun _ body => do
    if (← hatTy? body).isSome then return #[]
    return #[(← mkAppM ``Prod.fst #[v], x)]

/-- The costed value of `x : t` with its functions from `x` and their cost companions from the
costed value `c : hatTy? t`; its erasure reduces to `x` by projections. A sum inside `t` is
lifted by `ι`. -/
partial def refillE (t x c : Expr) : MetaM Expr := do
  let some _ ← hatTy? t | return x
  let tw ← whnfR t
  if tw.isAppOfArity ``Prod 2 then
    let a ← refillE (tw.getArg! 0) (← mkAppM ``Prod.fst #[x]) (← mkAppM ``Prod.fst #[c])
    let b ← refillE (tw.getArg! 1) (← mkAppM ``Prod.snd #[x]) (← mkAppM ``Prod.snd #[c])
    return ← mkAppM ``Prod.mk #[a, b]
  if tw.isAppOfArity ``Sum 2 || tw.isAppOfArity ``Option 1 then return ← iotaE t x
  if let some m ← mirrorStruct? tw then
    let n := m.fieldTypes.size
    let mut fs := #[]
    for i in [0:n] do
      let pf := mkAppN (mkConst m.projs[i]! m.levels) (m.params.push x)
      fs := fs.push (← refillE m.fieldTypes[i]! pf (← mirrorProj n i c))
    return ← mirrorMk fs
  let comp ← mkAppM ``Prod.snd #[c]
  let fn ← mkAppM ``Prod.fst #[c]
  let f ← forallTelescope tw fun ys body => do
    if (← hatTy? body).isNone then return x
    mkLambdaFVars ys (← refillE body (mkAppN x ys).headBeta (mkAppN fn ys).headBeta)
  mkAppM ``Prod.mk #[f, comp]

/-- The fields of the pattern `p` of a discriminant with costed value `v`, each with the
costed value of its position in `v`: a field is the whole value, a component of a pair or of
a structure with a mirror is the component, and the component of `Sum.inl`/`Sum.inr` is read
by `Sum.elim`, with `ι` of the pattern in the other case. A field under any other constructor
is not found. -/
partial def patternHats (p v : Expr) : MetaM (Array (Expr × Expr)) := do
  let p := p.consumeMData
  if p.isFVar then return #[(p, v)]
  let args := p.getAppArgs
  let .const c _ := p.getAppFn | return #[]
  if c == ``Prod.mk && args.size == 4 then
    return (← patternHats args[2]! (← mkAppM ``Prod.fst #[v])) ++
      (← patternHats args[3]! (← mkAppM ``Prod.snd #[v]))
  if (c == ``Sum.inl || c == ``Sum.inr) && args.size == 3 then
    let vt ← whnfR (← inferType v)
    unless vt.isAppOfArity ``Sum 2 do return #[]
    let left := c == ``Sum.inl
    let pt := if left then args[0]! else args[1]!
    let dflt ← iotaE pt args[2]!
    let get ← withLocalDeclD `z (vt.getArg! (if left then 0 else 1)) fun z =>
      mkLambdaFVars #[z] z
    let other ← withLocalDeclD `z (vt.getArg! (if left then 1 else 0)) fun z =>
      mkLambdaFVars #[z] dflt
    let comp ← if left then mkAppM ``Sum.elim #[get, other, v]
      else mkAppM ``Sum.elim #[other, get, v]
    return ← patternHats args[2]! comp
  if c == ``Option.some && args.size == 2 then
    -- The content of `some a` is read from the costed option `v`, with `ι a` on `none`.
    let vt ← whnfR (← inferType v)
    unless vt.isAppOfArity ``Option 1 do return #[]
    let dflt ← iotaE args[0]! args[1]!
    let get ← withLocalDeclD `z (vt.getArg! 0) fun z => mkLambdaFVars #[z] z
    return ← patternHats args[1]! (← mkAppM ``Option.elim #[v, dflt, get])
  let some m ← mirrorStruct? (← whnfR (← inferType p)) | return #[]
  unless c == m.ctor && args.size == m.params.size + m.fieldTypes.size do return #[]
  let mut out := #[]
  for i in [0:m.fieldTypes.size] do
    out := out ++ (← patternHats args[m.params.size + i]! (← mirrorProj m.fieldTypes.size i v))
  return out

/-- The patterns of the alternative `i` of the match `app`, one for each discriminant, over the
fields `fs` of the alternative. -/
def altPatterns (app : MatcherApp) (i : Nat) (fs : Array Expr) : MetaM (Option (Array Expr)) := do
  let mty ← instantiateForall
    (← inferType (mkConst app.matcherName app.matcherLevels.toList)) app.params
  forallBoundedTelescope mty (some 1) fun _ rest => do
    let rest ← instantiateForall rest app.discrs
    forallBoundedTelescope rest (some app.alts.size) fun as _ => do
      let some a := as[i]? | return none
      forallBoundedTelescope (← inferType a) (some fs.size) fun gs body => do
        unless gs.size == fs.size do return none
        let pats := body.getAppArgs
        unless pats.size == app.discrs.size do return none
        return some (pats.map (·.replaceFVars gs fs))

/-- The tree type of `t` with its result type replaced by its costed type (`hatTy?`). -/
def treeTyH? (t : Expr) : MetaM (Option TreeTy) := do
  let some T ← treeTy? t | return none
  let some h ← hatTy? T.result | return some T
  return some { T with params := T.params.set! (T.params.size - 1) h }

/-- The kind of a binder of type `t`. -/
def classify (t : Expr) : MetaM Kind := do
  if ← isProp t then return .static
  if ← isTypeFormerType t then return .static
  if (← isClass? t).isSome then return .static
  forallTelescope (← whnfR t) fun ys b => do
    if (← treeTy? b).isSome then
      return if ys.isEmpty then .tree else .treeFn
    -- A structure binder keeps the convention of field paths: its function fields applied
    -- are priced by cost companions after the binders. So does a binder whose functions are
    -- all in fields of structures (a pair `R × W` of two structures).
    if ys.isEmpty && (← mirrorStruct? b).isSome then return .data
    if ys.isEmpty then
      return if (← hatTy? b (mirror := false)).isSome then .hat else .data
    return .fn

/-- Whether `e` is data: not a type, a proposition, a proof or an instance. -/
def isDataExpr (e : Expr) : MetaM Bool := do
  let t ← inferType e
  if ← isTypeFormerType t then return false
  if ← isProp t then return false
  if (← isClass? t).isSome then return false
  return true

/-- The recursor of `Bool` at a constant motive applied to its two minor premises and its
major premise, `Bool.rec f t b`, as the `if` on the major premise `if b = true then t else f`
(`boolRec_eq_ite`); `none` for any other expression. -/
def boolRecIte? (e : Expr) : MetaM (Option Expr) := do
  unless e.isAppOfArity ``Bool.rec 4 do return none
  let args := e.getAppArgs
  let .lam _ _ body _ := args[0]! | return none
  if body.hasLooseBVars then return none
  let some u := e.getAppFn.constLevels!.head? | return none
  let c ← mkEq args[3]! (mkConst ``Bool.true)
  let inst := mkApp2 (mkConst ``instDecidableEqBool) args[3]! (mkConst ``Bool.true)
  return some (mkApp5 (mkConst ``ite [u]) body c inst args[2]! args[1]!)

/-- A dispatch on an optional value, `Option.elim o y f a₁ … aₙ`, `Option.casesOn o y f a₁ … aₙ`
or `Option.rec y f o a₁ … aₙ`, as a match: when `whnf` brings `o` to a constructor, the
alternative of that constructor applied to `a₁ … aₙ`; otherwise, when `n = 0`, the matcher of
`optionDispatch` on `o`, whose only discriminant is `o`. `none` when `e` is not such a dispatch,
and on a scrutinee that is not a constructor when `n > 0`: the match with the arguments passed
into its alternatives equals the dispatch only propositionally. -/
def optionDispatch? (e : Expr) : MetaM (Option Expr) := do
  let args := e.getAppArgs
  let some c := e.getAppFn.constName? | return none
  unless args.size ≥ 5 do return none
  -- the motive, the scrutinee and the alternatives on `none` and on `some`
  let (motive?, x, y, f) ←
    if c == ``Option.elim then pure (none, args[2]!, args[3]!, args[4]!)
    else if c == ``Option.casesOn then pure (some args[1]!, args[2]!, args[3]!, args[4]!)
    else if c == ``Option.rec then pure (some args[1]!, args[4]!, args[2]!, args[3]!)
    else return none
  let rest := args.extract 5 args.size
  let x' ← whnf x
  if x'.isAppOfArity ``Option.none 1 then return some (mkAppN y rest).headBeta
  if x'.isAppOfArity ``Option.some 2 then
    return some (mkAppN (mkApp f x'.appArg!).headBeta rest).headBeta
  unless rest.isEmpty do return none
  let motive ← match motive? with
    | some m => pure m
    | none =>
      let ty ← inferType e
      withLocalDeclD `x (← inferType x) fun z => mkLambdaFVars #[z] ty
  let d ← mkAppM ``optionDispatch #[motive, x, y, f]
  let some d' ← unfoldDefinition? d | return none
  return some d'.headBeta

/-- Whether `t` is a computation type `SPComp α`. -/
def isSPCompType (t : Expr) : MetaM Bool := do
  return (← whnfR t).isAppOfArity `CatCrypt.Core.SPComp 1

/-- Whether `v` is a projection path of a local: a local, or a structure projection of a
projection path (`kit.hkdf`, `Z.input.1`). -/
partial def isLocalProjPath (v : Expr) : MetaM Bool := do
  match v.consumeMData with
  | .fvar _ => return true
  | .proj _ _ s => isLocalProjPath s
  | v' =>
    let .const m _ := v'.getAppFn | return false
    let some info ← getProjectionFnInfo? m | return false
    unless v'.getAppNumArgs == info.numParams + 1 do return false
    isLocalProjPath v'.appArg!

/-- Whether `let x : t := v` is kept as a `let`, so that the cost of `v` is charged once: `v`
is first-order data that is not a variable, a literal, a constant, a closure or a projection
path of a local. Any other `let` is substituted into its body. -/
def keepsLet (t v : Expr) : MetaM Bool := do
  match v.consumeMData with
  | .fvar _ | .lit _ | .const .. | .lam .. | .sort _ | .forallE .. => return false
  | _ => pure ()
  -- A field path of a local (`kit.hkdf`) costs nothing: substituted, so that the fields
  -- applied through it are fields of a field path.
  if ← isLocalProjPath v then return false
  if ← isProp t then return false
  if ← isTypeFormerType t then return false
  if (← isClass? t).isSome then return false
  if ← isSPCompType t then return false
  if (← treeTy? t).isSome then return false
  if (← whnfR t).isForall then return false
  -- A structure value stays a `let`; its costed value is read through the `let` (`tv`).
  if (← mirrorStruct? (← whnfR t)).isSome then return true
  if (← hatTy? t).isSome then return false
  return true

/-- A `let` applied to arguments with the application pushed into its body,
`(let x := v; f) a ⇝ let x := v; f a` (beta-reduced, through nested `let`s), so that the
`let` is priced once by the rule for `let`. Any other term is returned unchanged. -/
partial def pushLetApp (e : Expr) : Expr :=
  let args := e.getAppArgs
  if args.isEmpty then e else
  match e.getAppFn.consumeMData with
  | .letE n t v b nd =>
    let args' := args.map (·.liftLooseBVars 0 1)
    .letE n t v (pushLetApp (mkAppN b args').headBeta) nd
  | _ => e

/-- The binders of the type `t`, which is reduced at default transparency before each binder,
up to a computation type `SPComp α`, a tree type or a type that is not a function type: `k`
receives the binders and the remaining type. A binder introduced by a type definition (an
adversary type `W → W → W → SPComp Bool` under its name) is a binder of the result. -/
partial def withTypeBinders {β : Type} (t : Expr) (k : Array Expr → Expr → TermElabM β) :
    TermElabM β :=
  go t #[]
where
  go (t : Expr) (acc : Array Expr) : TermElabM β := do
    if ← isSPCompType t then return ← k acc t
    if (← treeTy? t).isSome then return ← k acc t
    match ← whnf t with
    | .forallE n d b bi => withLocalDecl n bi d fun x => go (b.instantiate1 x) (acc.push x)
    | _ => k acc t

/-- The body of the definition value `v` applied to `args`: an argument that `keepsLet` keeps
is bound by a `let` around the body, any other argument is substituted. -/
partial def bindArgs (v : Expr) (args : Array Expr) (i : Nat) : MetaM Expr := do
  if h : i < args.size then
    match v with
    | .lam n ty b _ =>
      let a := args[i]
      if ← keepsLet (← inferType a) a then
        return .letE n ty a (← bindArgs b args (i + 1)) false
      bindArgs (b.instantiate1 a) args (i + 1)
    | _ => return mkAppN v (args.extract i args.size)
  else return v

/-- The base `b` of a projection `b.1`, `b.2` of a pair. -/
def pairProjBase? (e : Expr) : Option Expr :=
  match e with
  | .proj ``Prod _ b => some b
  | _ =>
    if e.isAppOfArity ``Prod.fst 3 || e.isAppOfArity ``Prod.snd 3 then some e.appArg!
    else none

/-- The calls `b` of which at least two projections `b.1`, `b.2` occur in `args`: applications
of a constant without loose bound variables whose type is a pair of first-order data. -/
def sharedPairBases (args : Array Expr) : MetaM (Array Expr) := do
  let mut seen : Array Expr := #[]
  let mut shared : Array Expr := #[]
  for a in args do
    let bs : Array Expr := Id.run do
      let mut acc := #[]
      let mut todo := #[a]
      while h : todo.size > 0 do
        let s := todo.back
        todo := todo.pop
        if let some b := pairProjBase? s then acc := acc.push b
        match s with
        | .app f x => todo := todo.push f |>.push x
        | .lam _ t b _ | .forallE _ t b _ => todo := todo.push t |>.push b
        | .letE _ t v b _ => todo := todo.push t |>.push v |>.push b
        | .mdata _ b | .proj _ _ b => todo := todo.push b
        | _ => pure ()
      return acc
    for b in bs do
      unless b.isApp && b.getAppFn.isConst && !b.hasLooseBVars do continue
      if seen.contains b then
        unless shared.contains b do shared := shared.push b
      else seen := seen.push b
  shared.filterM fun b => do
    let t ← whnfR (← inferType b)
    unless t.isAppOfArity ``Prod 2 do return false
    for c in t.getAppArgs do
      if (← whnfR c).isForall then return false
    keepsLet t b

/-- The body of the definition value `v` applied to `args`, as `bindArgs` gives it, with each
call `b` of which two projections `b.1`, `b.2` occur among the arguments bound once by a `let`
around it. -/
def bindArgsShared (v : Expr) (args : Array Expr) : MetaM Expr := do
  let bases ← sharedPairBases args
  let rec go (i : Nat) (args : Array Expr) : MetaM Expr := do
    if h : i < bases.size then
      let b := bases[i]
      withLetDecl (Name.mkSimple s!"shared{i}") (← inferType b) b fun r => do
        let args := args.map fun a => a.replace fun s => if s == b then some r else none
        mkLetFVars #[r] (← go (i + 1) args)
    else
      return (← bindArgs v args 0).headBeta
  go 0 args

/-- The cost companion type `X → ℕ` of a function of type `X → Y`. -/
def companionType (t : Expr) : MetaM Expr := do
  forallTelescope (← whnfR t) fun ys _ => mkForallFVars ys (mkConst ``Nat)

/-- The costed type of a binder of type `t` and kind `k`. -/
def costedType (t : Expr) : MetaM Expr := do
  forallTelescope (← whnfR t) fun ys b => do
    let some T ← treeTy? b | throwError "derive_timed: `{b}` is not a tree of a registered kind"
    mkForallFVars ys T.timedType

/-- The step-prefixed costed tree `p`, whose results have type `src`, with each result `y`
replaced by `f y`, a result of the tree type `T`: `p` followed by `fun y => (0, ret (f y))`,
at no cost. It lifts the results of a tree binder holding functions to costed closures of
companion zero (`ι`), and erases costed results for a callee whose tree binder takes the
plain type (`ε`). -/
def mapResultE (T : TreeTy) (p src : Expr) (f : Expr → MetaM Expr) : MetaM Expr := do
  let some bindC := T.kind.combinators.find? (·.src == T.kind.tree ++ `bind)
    | throwError "derive_timed: internal: the {T.kind.noun} kind has no bind"
  let lam ← withLocalDeclD `y src fun y => do
    let leaf := mkAppN (mkConst T.kind.nodes[0]!.tgt) (T.params.push (← f y))
    mkLambdaFVars #[y] (T.mkPair (natE 0) leaf)
  let p1 ← if p.isAppOfArity ``Prod.mk 4 then pure (p.getArg! 2) else mkAppM ``Prod.fst #[p]
  let p2 ← if p.isAppOfArity ``Prod.mk 4 then pure (p.getArg! 3) else mkAppM ``Prod.snd #[p]
  return T.delayE p1 (← mkAppM bindC.tgt #[p2, lam])

/-- The costed tree `p` of a binder of the plain tree type `raw`, lifted to the tree type `T`
whose results hold costed closures (`ι`); `p` when the two agree. -/
def liftBinderE (T raw : TreeTy) (p : Expr) : MetaM Expr := do
  if (← hatTy? raw.result).isNone then return p
  mapResultE T p raw.result (iotaE raw.result)

/-- The step-prefixed costed tree `p` of tree type `T`, erased to the plain tree type `raw` of
a callee's tree binder (`ε`); `p` when the two agree. -/
def lowerArgE (T raw : TreeTy) (p : Expr) : MetaM Expr := do
  if (← hatTy? raw.result).isNone then return p
  mapResultE raw p T.result (epsE raw.result)

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
  | .hat => epsE t v
  | _ => return v

/-- The erasure lemma of the tree kind `k` for the matcher `M` (`erase_snd_ite` for a
`match`): for every instance of the parameters, discriminants and alternatives,
`(M ps (fun _ => ℕ × k.timed ts) ds alts).2.erase = M ps (fun _ => k.tree ts) ds
  (fun fs => (alts fs).2.erase)`,
proved by case analysis on the discriminants. Its name is `M.erase_snd_<kind>`; it is added
once per matcher and kind. Returns `none` when `M` does not eliminate into an arbitrary
universe or the case analysis does not close the equation. -/
def matchEraseLemma (k : TreeKind) (M : Name) : TermElabM (Option Name) := do
  let name := M ++ Name.mkSimple ("erase_snd_" ++ k.noun.replace " " "_")
  if (← getEnv).contains name then return some name
  let some mi ← getMatcherInfo? M | return none
  let some uPos := mi.uElimPos? | return none
  let cinfo ← getConstInfo M
  let lps := cinfo.levelParams
  let stmt? ← forallTelescope (← inferType (mkConst k.tree)) fun tps _ => do
    let T1 ← mkAppM ``Prod #[mkConst ``Nat, mkAppN (mkConst k.timed) tps]
    let T2 := mkAppN (mkConst k.tree) tps
    let lvls := lps.map mkLevelParam
    let M1 := Lean.mkConst M (lvls.set uPos (← getLevel T1))
    let M2 := Lean.mkConst M (lvls.set uPos (← getLevel T2))
    let ty1 ← inferType M1
    forallBoundedTelescope ty1 mi.numParams fun ps rest => do
      let .forallE _ motTy _ _ := rest | return none
      let mot1 ← forallTelescope motTy fun xs _ => mkLambdaFVars xs T1
      let mot2 ← forallTelescope motTy fun xs _ => mkLambdaFVars xs T2
      let rest1 ← instantiateForall ty1 (ps.push mot1)
      forallBoundedTelescope rest1 mi.numDiscrs fun ds rest2 => do
        forallBoundedTelescope rest2 mi.numAlts fun alts _ => do
          let erase (v : Expr) : MetaM Expr := do
            return mkAppN (mkConst k.erase) (tps.push (← mkAppM ``Prod.snd #[v]))
          let lhs ← erase (mkAppN M1 (ps ++ #[mot1] ++ ds ++ alts))
          let alts2 ← alts.mapM fun a => do
            forallTelescope (← inferType a) fun fs _ => do
              mkLambdaFVars fs (← erase (mkAppN a fs))
          let rhs := mkAppN M2 (ps ++ #[mot2] ++ ds ++ alts2)
          let eq ← mkEq lhs rhs
          return some (← Core.betaReduce (← mkForallFVars (tps ++ ps ++ ds ++ alts) eq))
  let some stmt := stmt? | return none
  let s ← saveState
  try
    let mv ← mkFreshExprMVar stmt
    let gs ← Tactic.run mv.mvarId! (Tactic.evalTactic (← `(tactic|
      (intros; split <;> (try rfl) <;> (split <;> first | rfl | (exfalso; simp_all))))))
    unless gs.isEmpty do
      s.restore
      return none
    let proof ← instantiateMVars mv
    if proof.hasSorry || proof.hasMVar then
      s.restore
      return none
    let thm : TheoremVal :=
      { name := name, levelParams := lps.eraseIdx uPos, type := stmt, value := proof }
    addDecl (Declaration.thmDecl thm)
    return some name
  catch _ =>
    s.restore
    return none

/-- The bind of the tree kind `k`: its combinator named `bind`. -/
def kindBind? (k : TreeKind) : Option Name :=
  (k.combinators.find? fun cb => match cb.src with
    | .str _ "bind" => true
    | _ => false).map (·.src)

/-- The bind lemma `M.bind_<kind>` of the matcher `M` for trees of kind `k`: the bind of a match
whose alternatives are trees is the match of the binds of the alternatives, stated at every
continuation `f`. It is generated and proved by case analysis on its first use, and is `none`
when the matcher has no universe parameter for its motive or the proof fails. -/
def matchBindLemma (k : TreeKind) (M : Name) : TermElabM (Option Name) := do
  let name := M ++ Name.mkSimple ("bind_" ++ k.noun.replace " " "_")
  if (← getEnv).contains name then return some name
  let some bindC := kindBind? k | return none
  let some mi ← getMatcherInfo? M | return none
  let some uPos := mi.uElimPos? | return none
  let cinfo ← getConstInfo M
  let lps := cinfo.levelParams
  let stmt? ← forallTelescope (← inferType (mkConst k.tree)) fun tps _ => do
    let some α := tps.back? | return none
    withLocalDeclD `β (← inferType α) fun β => do
      let T1 := mkAppN (mkConst k.tree) tps
      let T2 := mkAppN (mkConst k.tree) (tps.pop.push β)
      withLocalDeclD `f (← mkArrow α T2) fun f => do
        let lvls := lps.map mkLevelParam
        let M1 := Lean.mkConst M (lvls.set uPos (← getLevel T1))
        let M2 := Lean.mkConst M (lvls.set uPos (← getLevel T2))
        let ty1 ← inferType M1
        forallBoundedTelescope ty1 mi.numParams fun ps rest => do
          let .forallE _ motTy _ _ := rest | return none
          let mot1 ← forallTelescope motTy fun xs _ => mkLambdaFVars xs T1
          let mot2 ← forallTelescope motTy fun xs _ => mkLambdaFVars xs T2
          let rest1 ← instantiateForall ty1 (ps.push mot1)
          forallBoundedTelescope rest1 mi.numDiscrs fun ds rest2 => do
            forallBoundedTelescope rest2 mi.numAlts fun alts _ => do
              let lhs ← mkAppM bindC #[mkAppN M1 (ps ++ #[mot1] ++ ds ++ alts), f]
              let alts2 ← alts.mapM fun a => do
                forallTelescope (← inferType a) fun fs _ => do
                  mkLambdaFVars fs (← mkAppM bindC #[mkAppN a fs, f])
              let rhs := mkAppN M2 (ps ++ #[mot2] ++ ds ++ alts2)
              let eq ← mkEq lhs rhs
              return some (← Core.betaReduce
                (← mkForallFVars (tps ++ #[β, f] ++ ps ++ ds ++ alts) eq))
  let some stmt := stmt? | return none
  let s ← saveState
  try
    let mv ← mkFreshExprMVar stmt
    let gs ← Tactic.run mv.mvarId! (Tactic.evalTactic (← `(tactic|
      (intros; split <;> (try rfl) <;> (split <;> first | rfl | (exfalso; simp_all))))))
    unless gs.isEmpty do
      s.restore
      return none
    let proof ← instantiateMVars mv
    if proof.hasSorry || proof.hasMVar then
      s.restore
      return none
    let thm : TheoremVal :=
      { name := name, levelParams := lps.eraseIdx uPos, type := stmt, value := proof }
    addDecl (Declaration.thmDecl thm)
    return some name
  catch _ =>
    s.restore
    return none

/-- Whether the call `e` of the tree-valued definition `c` is unfolded rather than translated
to a call of a costed form: `c` is a non-recursive definition that is not a matcher, the result
type of the tree at the call holds functions (`hatTy?`), and the result type of the tree in the
declared type of `c` does not (a callee generic in its state type, called at a state holding
functions). -/
def unfoldsGenericCall (c : Name) (e : Expr) : MetaM Bool := do
  let env ← getEnv
  let some (.defnInfo dv) := env.find? c | return false
  if (Structural.eqnInfoExt.find? env c).isSome || (WF.eqnInfoExt.find? env c).isSome then
    return false
  if isMatcherCore env c then return false
  let some Tc ← treeTy? (← inferType e) | return false
  if (← hatTy? Tc.result).isNone then return false
  forallTelescope dv.type fun _ b => do
    let some Tg ← treeTy? b | return false
    return (← hatTy? Tg.result).isNone

/-- The costed tree of the tree binder `e`, when `e` is one. -/
def treeLocal? (ctx : Ctx) (e : Expr) : Option Expr :=
  match e.consumeMData with
  | .fvar id =>
    match ctx.locals.get? id with
    | some { kind := .tree, value, .. } => some value
    | _ => none
  | _ => none

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
      | .hat => do
        if ctx.plain then
          -- The plain interface: the binder keeps its plain value, its functions tables.
          let v ← iotaE t x
          return ← go (i + 1) { ctx with locals := ctx.locals.insert x.fvarId! ⟨.hat, v, none⟩ }
            (bs.push x) (args.push x)
        let some ht ← hatTy? t | fail m!"internal: `{t}` holds no function"
        withLocalDeclD n ht fun v => do
          let e ← epsE t v
          go (i + 1) { ctx with locals := ctx.locals.insert x.fvarId! ⟨.hat, v, none⟩,
                                hatSubst := ctx.hatSubst.push (x, e) }
            (bs.push v) (args.push e)
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

/-- The applied fields in `e` of local structures and instances without a registered cost:
each a projection applied to its parameters and a local, and to further arguments, without
loose bound variables. -/
partial def fieldPrefixes (e : Expr) : MetaM (Array Expr) := do
  let rec go (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
    match e with
    | .app .. =>
      let f := e.getAppFn
      let args := e.getAppArgs
      let mut acc := acc
      if let .const m _ := f then
        if let some info ← getProjectionFnInfo? m then
          if h : info.numParams + 1 < args.size then
            let p := mkAppN f (args.extract 0 (info.numParams + 1))
            if args[info.numParams].consumeMData.isFVar && !p.hasLooseBVars &&
                !(← getEnv).contains (m ++ `timedCost) && !acc.contains p then
              acc := acc.push p
      acc ← go f acc
      for a in args do acc ← go a acc
      return acc
    | .lam _ t b _ | .forallE _ t b _ => go b (← go t acc)
    | .letE _ t v b _ => go b (← go v (← go t acc))
    | .mdata _ b => go b acc
    | .proj _ _ s => go s acc
    | _ => return acc
  go e #[]

/-- The name of the cost companion of the field key `p`: `fCost` for a field `S.f ps s`, and
`g_fCost` for a field of a computed structure `fun xs => S.f ps (g xs)`. -/
def fieldCostName (p : Expr) : MetaM Name := do
  let last (e : Expr) : MetaM (Option String) := do
    match e.getAppFn with
    | .const m _ => return some (m.updatePrefix .anonymous).toString
    | .fvar id => return some (← id.getUserName).eraseMacroScopes.toString
    | _ => return none
  if p.isLambda then
    return ← lambdaTelescope p fun _ b => do
      let some fl ← last b | return `fieldCost
      unless b.isApp do return Name.mkSimple (fl ++ "Cost")
      let some gl ← last b.appArg! | return Name.mkSimple (fl ++ "Cost")
      return Name.mkSimple (gl ++ "_" ++ fl ++ "Cost")
  if let .proj S i _ := p then
    -- A data path: the costed value of the field, `inputHat` for `Z.input`.
    if let some info := getStructureInfo? (← getEnv) S then
      if let some fl := info.fieldNames[i]? then
        return Name.mkSimple (fl.toString ++ "Hat")
    return `fieldHat
  match ← last p with
  | some fl => return Name.mkSimple (fl ++ "Cost")
  | none => return `fieldCost

/-- Whether a value of type `t` is data holding functions that is not itself a function: its
costed value (`hatTy?`) is a tuple that contains costed closures. -/
def holdsFnData (t : Expr) : MetaM Bool := do
  if (← whnfR t).isForall then return false
  return (← hatTy? t).isSome

/-- Whether the field path `p` is a data path: a primitive projection whose type holds
functions and is not a function. -/
def isDataPath (p : Expr) : MetaM Bool := do
  unless p.isProj do return false
  holdsFnData (← inferType p)

/-- The type of the companion of the field path `p`: the costed type `hatTy? t` of a data path
of type `t`, and the cost companion type `X → ℕ` of a function field of type `X → Y`. -/
def pathCompanionType (p : Expr) : MetaM Expr := do
  let t ← inferType p
  if ← isDataPath p then
    let some ht ← hatTy? t | fail m!"internal: `{t}` holds no function"
    return ht
  companionType t

/-- Bind a companion for each field path of `ps` (`pathCompanionType`: a cost companion of an
applied field, the costed value of a data path) and continue with the pairs of the path and
its companion. -/
def withFieldCosts {β : Type} (ps : Array Expr) (k : Array (Expr × Expr) → TermElabM β) :
    TermElabM β :=
  go 0 #[]
where
  go (i : Nat) (acc : Array (Expr × Expr)) : TermElabM β := do
    if h : i < ps.size then
      let p := ps[i]
      let n ← fieldCostName p
      withLocalDeclD n (← pathCompanionType p) fun cc =>
        go (i + 1) (acc.push (p, cc))
    else k acc

/-- The applications `m ps inst` in `e` of a method `m` of `units` to its parameters and a
local instance `inst`, without loose bound variables. -/
partial def unitPrefixes (units : Array Name) (e : Expr) : MetaM (Array Expr) := do
  let rec go (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
    match e with
    | .app .. =>
      let f := e.getAppFn
      let args := e.getAppArgs
      let mut acc := acc
      if let .const m _ := f then
        if units.contains m then
          if let some info ← getProjectionFnInfo? m then
            if h : info.numParams < args.size then
              let p := mkAppN f (args.extract 0 (info.numParams + 1))
              if args[info.numParams].consumeMData.isFVar && !p.hasLooseBVars &&
                  !acc.contains p then
                acc := acc.push p
      acc ← go f acc
      for a in args do acc ← go a acc
      return acc
    | .lam _ t b _ | .forallE _ t b _ => go b (← go t acc)
    | .letE _ t v b _ => go b (← go v (← go t acc))
    | .mdata _ b => go b acc
    | .proj _ _ s => go s acc
    | _ => return acc
  go e #[]

/-- Whether `s` is a field path: a binder of the reduction, or a field of a structure-valued
field path (`kit`, `kit.hkdf`, `P.dh`). -/
partial def isFieldPath (ctx : Ctx) (s : Expr) : MetaM Bool := do
  match s.consumeMData with
  | .fvar id => return ctx.top.contains id
  | .proj _ _ s' => isFieldPath ctx s'
  | s' =>
    let .const m _ := s'.getAppFn | return false
    let some info ← getProjectionFnInfo? m | return false
    unless s'.getAppNumArgs == info.numParams + 1 do return false
    isFieldPath ctx s'.appArg!

/-- The key of a field `S.f ps (g b₁ … bₘ) …` of a computed structure, applied to the arguments
`args` of the projection `f` with `np` parameters: the structure is computed by a field path `g`
of a binder (`kit.aead`) or a local function with a cost companion, applied to data `bᵢ`. The
key is `fun x₁ … xₘ => S.f ps (g x₁ … xₘ)`, returned with `b₁ … bₘ`. -/
def computedFieldKey? (ctx : Ctx) (f : Expr) (np : Nat) (args : Array Expr) :
    MetaM (Option (Expr × Array Expr)) := do
  let some s := args[np]? | return none
  let s := s.consumeMData
  let ps := args.extract 0 np
  if ps.any (·.hasLooseBVars) then return none
  let sargs := s.getAppArgs
  let some (gp, bs) ← (match s.getAppFn with
      | g@(.fvar id) => do
        match ctx.locals.get? id with
        | some { kind := .fn, companion? := some _, .. } => pure (some (g, sargs))
        | _ => pure none
      | g@(.const m _) => do
        let some gi ← getProjectionFnInfo? m | pure none
        if gi.fromClass then pure none
        else if h : gi.numParams + 1 < sargs.size then
          let gp := mkAppN g (sargs.extract 0 (gi.numParams + 1))
          if !gp.hasLooseBVars && (← isFieldPath ctx sargs[gi.numParams]) then
            pure (some (gp, sargs.extract (gi.numParams + 1) sargs.size))
          else pure none
        else pure none
      | _ => pure none : MetaM (Option (Expr × Array Expr))) | return none
  if bs.isEmpty then return none
  forallBoundedTelescope (← whnfR (← inferType gp)) bs.size fun xs _ => do
    unless xs.size == bs.size do return none
    return some (← mkLambdaFVars xs (mkAppN f (ps.push (mkAppN gp xs))), bs)

/-- The equations among the conjuncts of the proof `pf` of `ty`. -/
partial def conjEqns (pf ty : Expr) : MetaM (Array Expr) := do
  -- At default transparency, so that a match of the hypothesis on a constructor reduces.
  let ty ← whnf (← instantiateMVars ty)
  if ty.isAppOfArity ``And 2 then
    return (← conjEqns (mkApp3 (mkConst ``And.left) (ty.getArg! 0) (ty.getArg! 1) pf)
        (ty.getArg! 0)) ++
      (← conjEqns (mkApp3 (mkConst ``And.right) (ty.getArg! 0) (ty.getArg! 1) pf) (ty.getArg! 1))
  if ty.isAppOfArity ``Eq 3 then return #[pf]
  return #[]

/-- Rewrite the goal `g` from right to left with each hypothesis (or conjunct of one) that is
an equation whose right side is a call of `c`: the induction hypotheses of an erasure theorem
`… = c ys`. -/
def rewriteRecHyps (c : Name) (g : MVarId) : MetaM MVarId := g.withContext do
  let mut g := g
  let mut used : Array FVarId := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    for pf in ← conjEqns d.toExpr d.type do
      let some (ty, lhs, rhs) := (← instantiateMVars (← inferType pf)).eq? | continue
      unless rhs.isAppOf c do continue
      let gt ← instantiateMVars (← g.getType)
      unless (gt.find? (· == rhs)).isSome do continue
      -- The occurrences of `rhs` replaced by `lhs`, by congruence with the motive that
      -- abstracts them.
      let motive ← withLocalDeclD `z ty fun z => do
        mkLambdaFVars #[z] (gt.replace fun s => if s == rhs then some z else none)
      unless ← isTypeCorrect motive do continue
      let gNew := (mkApp motive lhs).headBeta
      g ← g.replaceTargetEq gNew (← mkEqSymm (← mkCongrArg motive pf))
      used := used.push d.fvarId
  -- A used hypothesis is cleared, so that a later `simp [*]` does not rewrite back.
  for h in used do g ← g.tryClear h
  return g

/-- The applications of the constant `t` in `e`, outermost first. -/
partial def appsOfConst (t : Name) (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let acc := if e.isAppOf t then acc.push e else acc
  match e with
  | .app f a => appsOfConst t a (appsOfConst t f acc)
  | .lam _ d b _ | .forallE _ d b _ => appsOfConst t b (appsOfConst t d acc)
  | .letE _ ty v b _ => appsOfConst t b (appsOfConst t v (appsOfConst t ty acc))
  | .mdata _ b | .proj _ _ b => appsOfConst t b acc
  | _ => acc

/-- The induction hypotheses of a functional induction on the source `c` of the costed form `t`
are quantified over the cost companions that the induction generalizes:
`∀ cs, (t ys cs).2.erase … = c ys`. Each is instantiated at the companions of a call `t ys cs'`
in the goal `g`, found by unifying its call of `t` with the call in the goal, and added as a
hypothesis, so that `rewriteRecHyps` rewrites the recursive call of `c` with it. -/
def instRecHyps (t : Name) (g : MVarId) : MetaM MVarId := g.withContext do
  let mut g := g
  let mut used : Array FVarId := #[]
  -- The calls without loose bound variables: a call under a binder whose arguments depend on
  -- the bound variable has no instance of the hypothesis to rewrite with.
  let occs := (appsOfConst t (← instantiateMVars (← g.getType))).filter (!·.hasLooseBVars)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isForall do continue
    for occ in occs do
      let s ← saveState
      let (ms, _, body) ← forallMetaTelescopeReducing ty
      let some (_, lhs, _) := body.eq? | s.restore; break
      let some call := (appsOfConst t lhs)[0]? | s.restore; break
      if ← isDefEq call occ then
        let inst ← instantiateMVars (mkAppN d.toExpr ms)
        let instTy ← instantiateMVars body
        if inst.hasExprMVar || instTy.hasExprMVar then
          s.restore
          continue
        let (_, g') ← (← g.assert d.userName instTy inst).intro1P
        g := g'
        used := used.push d.fvarId
      else s.restore
  -- An instantiated hypothesis is cleared, so that a later `simp [*]` does not rewrite the
  -- recursive call back with it.
  for h in used do g ← g.tryClear h
  return g

/-- The step of the projection `e = s.i` of the structure `S`, a primitive projection or a
projection function (not a class method) applied to its parameters and to `s`: `(S, i, s)`. -/
def projStep? (e : Expr) : MetaM (Option (Name × Nat × Expr)) := do
  match e.consumeMData with
  | .proj S i s => return some (S, i, s)
  | e' =>
    let .const m _ := e'.getAppFn | return none
    let some info ← getProjectionFnInfo? m | return none
    if info.fromClass then return none
    unless e'.getAppNumArgs == info.numParams + 1 do return none
    return some (m.getPrefix, info.i, e'.appArg!)

/-- The projection path `e` with each step written as a primitive projection: the key of a
data path in `Ctx.fields`. -/
partial def canonPath (e : Expr) : MetaM Expr := do
  match ← projStep? e with
  | some (S, i, s) => return .proj S i (← canonPath s)
  | none => return e.consumeMData

/-- Whether the field path `p` of a callee's derived cost is a step below a field path of the
binders of the reduction: `p` is a projection (a primitive projection such as `s.1`, or a
projection function applied to its parameters) of a field path, or an application whose last
argument is a field path. -/
def isFieldPathStep (ctx : Ctx) (p : Expr) : MetaM Bool := do
  if let some (_, _, s) ← projStep? p then return ← isFieldPath ctx s
  let p := p.consumeMData
  if p.isApp then return ← isFieldPath ctx p.appArg!
  return false

/-- The start of the projection path `e`: the term whose projections it takes. -/
partial def pathRoot (e : Expr) : MetaM Expr := do
  match ← projStep? e with
  | some (_, _, s) => pathRoot s
  | none => return e.consumeMData

/-- The component `i` of the costed value `v` of a structure `s` of the structure `S`: a
component of a pair, or of the mirror tuple of a structure holding functions. -/
def projHat? (S : Name) (i : Nat) (s v : Expr) : MetaM (Option Expr) := do
  if S == ``Prod then
    if v.isAppOfArity ``Prod.mk 4 then return some (v.getArg! (if i == 0 then 2 else 3))
    return some (← mkAppM (if i == 0 then ``Prod.fst else ``Prod.snd) #[v])
  let some m ← mirrorStruct? (← whnfR (← inferType s)) | return none
  unless m.struct == S do return none
  return some (← mirrorProj m.fieldTypes.size i v)

/-- The costed value of the projection path `e` below a binder of the reduction that has no
costed value of its own (a structure binder with the convention of field paths, such as an
environment `Z`). The shortest prefix `p` of `e` that is data holding functions and not a
function (the data path `Z.input` of `Z : Env (Unit × S) β`) has as costed value
`refillE t p p̂`, whose functions are those of `p` and whose cost companions are read from the
binder `p̂ : hatTy? t` after the binders of the reduction (`Ctx.fields`, keyed by
`canonPath p`); the costed value of `e` is its component. With `record`, in the first pass, a
data path without a binder is recorded (`fieldRec?`), with its functions as tables (`ι`). -/
partial def pathHat? (ctx : Ctx) (e : Expr) (record : Bool) : MetaM (Option Expr) := do
  let some (S, i, s) ← projStep? e | return none
  let s := s.consumeMData
  if !s.isFVar then
    if let some sv ← pathHat? ctx s record then
      return ← projHat? S i s sv
  -- `s` is a path that holds no function in its prefixes: `e` is a data path when `s` starts
  -- at a binder of the reduction without a costed value.
  unless ← isFieldPath ctx s do return none
  if let .fvar id ← pathRoot s then
    if (ctx.locals.get? id).isSome then return none
  let t ← inferType e
  unless ← holdsFnData t do return none
  let key ← canonPath e
  if let some (_, cc) := ctx.fields.find? (·.1 == key) then
    return some (← refillE t key cc)
  if record then
    if let some r := ctx.fieldRec? then
      unless (← r.get).contains key do r.modify (·.push key)
      return some (← iotaE t key)
  return none

/-- The costed value of the field path `v : t` (a binder of the reduction holding functions
without a costed value of its own, such as a handler state, or a field of one): `ι v`, except
that a function field `S.f v` with a cost companion `cc` (`Ctx.fields`) is the costed closure
`(fun ys => v.f ys, cc)`, and a data path with a costed value (`pathHat?`) is that value. With
a reference `fieldRec?` (the first pass), a function field without a companion is recorded, so
that the second pass gives it one. -/
partial def iotaPathE (ctx : Ctx) (t v : Expr) : TermElabM Expr := do
  let some _ ← hatTy? t | return v
  let tw ← whnfR t
  if tw.isForall then
    let found? ← match ctx.fields.find? (·.1 == v) with
      | some (_, cc) => pure (some cc)
      | none => do
        let key ← canonPath v
        pure ((ctx.fields.find? fun (p, _) => p == key).map (·.2))
    let some cc := found?
      | if let some r := ctx.fieldRec? then
          if !v.hasLooseBVars && v.getAppFn.isConst && (← isFieldPath ctx v) then
            unless (← r.get).contains v do r.modify (·.push v)
        return ← iotaE t v
    let f ← forallTelescope tw fun ys body => do
      mkLambdaFVars ys (← iotaE body (mkAppN v ys).headBeta)
    return ← mkAppM ``Prod.mk #[f, cc]
  if let some h ← pathHat? ctx v (record := true) then return h
  if tw.isAppOfArity ``Prod 2 then
    let a ← iotaPathE ctx (tw.getArg! 0) (← mkAppM ``Prod.fst #[v])
    let b ← iotaPathE ctx (tw.getArg! 1) (← mkAppM ``Prod.snd #[v])
    return ← mkAppM ``Prod.mk #[a, b]
  if let some m ← mirrorStruct? tw then
    let mut fs := #[]
    for i in [0:m.fieldTypes.size] do
      let pf := mkAppN (mkConst m.projs[i]! m.levels) (m.params.push v)
      fs := fs.push (← iotaPathE ctx m.fieldTypes[i]! pf)
    return ← mirrorMk fs
  iotaE t v

/-- Whether `p` is a function field `S.f ps s` of a structure value: `s` is not a field path of
the binders of the reduction, and `s`, or the value of the `let` that binds it, is a
constructor application up to reducible unfolding. The cost companion of such a field is the
cost of the field applied, read through the structure's value (`companionOf`). A field of a
structure computed by a definition, `(kit.aead iv).enc`, keeps its own cost companion (the rule
for computed structures), since unfolding the definition would price its whole body. -/
def isValueField (ctx : Ctx) (p : Expr) : MetaM Bool := do
  if p.hasLooseBVars then return false
  unless (← whnfR (← inferType p)).isForall do return false
  let .const m _ := p.getAppFn | return false
  let some info ← getProjectionFnInfo? m | return false
  if info.fromClass then return false
  unless p.getAppNumArgs == info.numParams + 1 do return false
  let s := p.appArg!.consumeMData
  if ← isFieldPath ctx s then return false
  let sv ← match s with
    | .fvar id => do
      match ← id.getValue? with
      | some v => pure v
      | none => pure s
    | _ => pure s
  return (← isConstructorApp? (← whnfR sv)).isSome

/-- The projection path `e` with its step to the structure argument `s` replaced by `s'`. -/
def replaceProjArg (e s' : Expr) : Expr :=
  match e.consumeMData with
  | .proj S j _ => .proj S j s'
  | e' => mkApp e'.appFn! s'

/-- The structure term `s` with every projection of a constructor application reduced, from the
innermost structure argument out: `{ cfg := s.cfg, … }.cfg` is `s.cfg`. -/
partial def reduceStructArg (s : Expr) : MetaM Expr := do
  let some (_, i, s₀) ← projStep? s | return s
  let s₀' ← reduceStructArg s₀
  if let some v ← projectCore? (← whnfR s₀') i then
    return ← reduceStructArg v
  if s₀' == s₀.consumeMData then return s
  return replaceProjArg s s₀'

/-- The field `S.f s` with its structure argument reduced by `reduceStructArg`:
`{ cfg := s.cfg, … }.cfg.env` is `s.cfg.env`. The outermost projection is kept, so that a field
of a constructor application (`Corr.leaks ⟨f, g⟩`) stays a field of a structure value. -/
def reduceFieldArg (e : Expr) : MetaM Expr := do
  if e.hasLooseBVars then return e
  let some (_, _, s) ← projStep? e | return e
  let s' ← reduceStructArg s
  if s' == s.consumeMData then return e
  return replaceProjArg e s'

/-- The key of the field path `p = S.f ps s` of a callee at a structure `s` computed by a
definition: `s`, or the value of the `let` that binds it, is an application `g as bs` of a
definition `g` that is not a projection, whose value is not a constructor application up to
reducible unfolding, where `as` are the leading implicit and instance arguments of `g` and `bs`
the remaining arguments, none empty. The key is `fun xs => S.f ps (g as xs)`, returned with
`bs`; the caller passes the cost companion of the key applied to `bs`, as for a field of a
computed structure (`computedFieldKey?`). -/
def computedPathKey? (ctx : Ctx) (p : Expr) : MetaM (Option (Expr × Array Expr)) := do
  if p.hasLooseBVars || p.isLambda then return none
  let some (_, _, s₀) ← projStep? p | return none
  let mut s := s₀.consumeMData
  if ← isFieldPath ctx s then return none
  -- The value of the `let` that binds the structure, through nested `let`s.
  for _ in [0:8] do
    let .fvar id := s | break
    let some v ← id.getValue? | break
    s := v.consumeMData
  if (← isConstructorApp? (← whnfR s)).isSome then return none
  let .const g lvls := s.getAppFn | return none
  let some (.defnInfo _) := (← getEnv).find? g | return none
  if (← getProjectionFnInfo? g).isSome then return none
  let sargs := s.getAppArgs
  let k ← forallTelescope (← inferType (mkConst g lvls)) fun ys _ => do
    let mut k := 0
    for y in ys do
      if (← y.fvarId!.getBinderInfo).isExplicit then break
      k := k + 1
    return k
  if k ≥ sargs.size then return none
  let gp := mkAppN (mkConst g lvls) (sargs.extract 0 k)
  let bs := sargs.extract k sargs.size
  if gp.hasLooseBVars then return none
  forallBoundedTelescope (← whnfR (← inferType gp)) bs.size fun xs _ => do
    unless xs.size == bs.size do return none
    let key ← mkLambdaFVars xs (replaceProjArg p (mkAppN gp xs))
    unless ← isTypeCorrect key do return none
    return some (key, bs)

/-- The cost `if c then a else b`, which is `a` when the two branch costs are the same term. -/
def iteNatE (c inst a b : Expr) : Expr :=
  if a == b then a else mkApp5 (mkConst ``ite [Level.one]) (mkConst ``Nat) c inst a b

/-- The common cost of the alternatives of the match `e`, when every alternative is a constant
function of its pattern variables and all have the same value. -/
def constAlts? (e : Expr) : MetaM (Option Expr) := do
  let some app ← matchMatcherApp? e | return none
  let mut v? : Option Expr := none
  for alt in app.alts do
    let b? ← lambdaTelescope alt fun xs b => pure <|
      if b.hasAnyFVar (fun f => xs.any (·.fvarId! == f)) then none else some b
    let some b := b? | return none
    match v? with
    | none => v? := some b
    | some v => unless v == b do return none
  return v?

/-- Close the goal `g` by rewriting it from right to left with a case hypothesis `d = C as`
(a constructor application, as `split` introduces) and `rfl`: the structure
`{ cur := k + 1, env := s.cfg.env }` that the hypothesis `s.cfg.cur = k + 1` produced from the
eta expansion of `s.cfg` becomes that eta expansion again, which `rfl` closes. Each case
hypothesis is tried alone; the goal is unchanged when none closes it. -/
def closeByCaseHypsRev (g : MVarId) : MetaM Bool := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some (_, _, rhs) := (← instantiateMVars d.type).eq? | continue
    unless (← isConstructorApp? rhs).isSome do continue
    let s ← saveState
    try
      let r ← g.rewrite (← g.getType) (← mkEqSymm d.toExpr)
      unless r.mvarIds.isEmpty do throwError "side goals"
      let g' ← g.replaceTargetEq r.eNew r.eqProof
      g'.refl
      return true
    catch _ => s.restore
  return false

mutual

/-- The cost of evaluating the data term `e`. -/
partial def costOf (ctx : Ctx) (e : Expr) : TermElabM Expr := do
  let e := pushLetApp e.consumeMData.headBeta
  unless ← isDataExpr e do return natE 0
  match e with
  | .fvar _ | .lit _ | .lam .. | .forallE .. | .sort _ => return natE 0
  | .proj _ _ s => costOf ctx s
  | .letE n t v b _ =>
    unless ← keepsLet t v do return ← costOf ctx (b.instantiate1 v)
    -- The value is priced once; the body with a local of cost zero in its place.
    let cv ← costOf ctx v
    withLetDecl n t v fun x => do
      let cb ← costOf ctx (b.instantiate1 x)
      return add cv (cb.replaceFVar x v)
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

/-- The cost companion of the function-valued argument `a`: the companion of a local function,
the second component of the costed closure that a path into a costed value denotes, and
otherwise the cost of `a` applied. -/
partial def companionOf (ctx : Ctx) (a : Expr) : TermElabM Expr := do
  if let .fvar id := a.consumeMData then
    if let some { companion? := some c, .. } := ctx.locals.get? id then return c
  if let some v ← hatOf? ctx a then
    if (← whnfR (← inferType v)).isAppOfArity ``Prod 2 then return ← projE false v
  let t ← whnfR (← inferType a)
  forallTelescope t fun ys _ => do
    mkLambdaFVars ys (← costOf ctx (mkAppN a ys).headBeta)

/-- The costed value of a path `e` into a costed value: a local of kind `hat` (its costed
value), a local function with a cost companion (the costed closure of the two), a projection
of a path, an application of a costed closure whose result holds functions, or a projection
path of a binder below a data path (`pathHat?`, which records the data path with `record`). -/
partial def hatOf? (ctx : Ctx) (e : Expr) (record : Bool := false) :
    TermElabM (Option Expr) := do
  let e := e.consumeMData
  if let some v ← pathHat? ctx e record then return some v
  match e with
  | .fvar id =>
    match ctx.locals.get? id with
    | some { kind := .hat, value, .. } => return some value
    | some { kind := .fn, value, companion? := some c } =>
      return some (← mkAppM ``Prod.mk #[value, c])
    | _ => return none
  | .proj ``Prod i s =>
    let some v ← hatOf? ctx s | return none
    return some (← projE (i == 0) v)
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    if (f.isConstOf ``Prod.fst || f.isConstOf ``Prod.snd) && args.size == 3 then
      let some v ← hatOf? ctx args[2]! | return none
      return some (← projE (f.isConstOf ``Prod.fst) v)
    let some (c, rest, _) ← closureHead? ctx e | return none
    return some (← closureApp ctx c rest).2
  | _ => return none

/-- The projection `v.1` (or `v.2`) of a pair, reduced on a literal pair. -/
partial def projE (fst : Bool) (v : Expr) : MetaM Expr := do
  if v.isAppOfArity ``Prod.mk 4 then return v.getArg! (if fst then 2 else 3)
  mkAppM (if fst then ``Prod.fst else ``Prod.snd) #[v]

/-- The costed closure at the head of the application `e`, with the arguments applied to it
and the path that computes it: a local of kind `hat` applied, or a projection of a path
applied. -/
partial def closureHead? (ctx : Ctx) (e : Expr) :
    TermElabM (Option (Expr × Array Expr × Expr)) := do
  let f := e.getAppFn.consumeMData
  let args := e.getAppArgs
  if args.isEmpty then return none
  match f with
  | .fvar id =>
    match ctx.locals.get? id with
    | some { kind := .hat, value, .. } => return some (value, args, f)
    | _ => return none
  | .proj ``Prod _ _ =>
    let some c ← hatOf? ctx f | return none
    return some (c, args, f)
  | .const n _ =>
    unless (n == ``Prod.fst || n == ``Prod.snd) && args.size > 3 do return none
    let q := mkAppN f (args.extract 0 3)
    let some c ← hatOf? ctx q | return none
    return some (c, args.extract 3 args.size, q)
  | _ => return none

/-- The application of the costed closure `c` to `args`: its cost, one plus the companion
at the arguments plus the costs of the arguments for each saturated application, and the
costed value of the result. A partial application (fewer arguments than the companion takes)
costs its arguments and is the costed closure of the remaining arguments. -/
partial def closureApp (ctx : Ctx) (c : Expr) (args : Array Expr) :
    TermElabM (Expr × Expr) := do
  let mut cur := c
  let mut rest := args
  let mut cost := natE 0
  while !rest.isEmpty do
    let ct ← whnfR (← inferType cur)
    unless ct.isAppOfArity ``Prod 2 do
      fail m!"the costed closure `{cur}` is applied to more arguments than it takes"
    let k ← forallTelescope (← whnfR (ct.getArg! 1)) fun ys _ => pure ys.size
    if rest.size < k then
      -- A partial application: the costed closure of the remaining arguments, whose function
      -- and companion are those of `cur` at the arguments given, evaluated when it is built.
      let fn ← projE true cur
      let cp ← projE false cur
      let r ← forallBoundedTelescope (← whnfR (← inferType (mkAppN fn rest)))
        (some (k - rest.size)) fun zs _ => do
          let f ← mkLambdaFVars zs (mkAppN (mkAppN fn rest) zs).headBeta
          let c ← mkLambdaFVars zs (mkAppN (mkAppN cp rest) zs).headBeta
          mkAppM ``Prod.mk #[f, c]
      return (add cost (← argsCost ctx rest), r)
    let now := rest.extract 0 k
    let comp := (mkAppN (← projE false cur) now).headBeta
    cost := add cost (add (natE 1) (add comp (← argsCost ctx now)))
    cur := (mkAppN (← projE true cur) now).headBeta
    rest := rest.extract k rest.size
  return (cost, cur)

/-- The cost and the costed value (`hatTy?`) of the data term `e`; for a term whose type
holds no function, its cost and `e`. A closure costs nothing to build and its companion is
the cost of its body; a partial application of a constant evaluates its arguments when it is
built; a pair, an `if` and a call of a definition are translated componentwise, by branch and
by unfolding. -/
partial def tv (ctx : Ctx) (e : Expr) : TermElabM (Expr × Expr) := do
  let e := pushLetApp e.consumeMData.headBeta
  let t ← inferType e
  let some ht ← hatTy? t | return (← costOf ctx e, e)
  if let some v ← hatOf? ctx e (record := true) then return (← costOf ctx e, v)
  let tw ← whnfR t
  match e with
  | .letE n lt v b _ =>
    unless ← keepsLet lt v do return ← tv ctx (b.instantiate1 v)
    let cv ← costOf ctx v
    withLetDecl n lt v fun x => do
      let (cb, vb) ← tv ctx (b.instantiate1 x)
      return (add cv (cb.replaceFVar x v), vb.replaceFVar x v)
  | .lam .. =>
    let n ← forallTelescope tw fun ys _ => pure ys.size
    withEta e n fun ys b => do
      let (cb, vb) ← tv ctx b
      return (natE 0, ← mkAppM ``Prod.mk #[← mkLambdaFVars ys vb, ← mkLambdaFVars ys cb])
  | .fvar id =>
    -- A `let` of a structure: its costed value is that of the value, whose cost the `let`
    -- charged. A binder of the reduction (a structure with the convention of field paths)
    -- keeps the cost companions of its function fields (`iotaPathE`). Any other local holding
    -- functions without a costed value is a table (`ι`).
    if let some v ← id.getValue? then return (natE 0, (← tv ctx v).2)
    if ← isFieldPath ctx e then return (natE 0, ← iotaPathE ctx t e)
    return (natE 0, ← iotaE t e)
  | .proj S i s =>
    -- A component of a pair holding functions: the component of its costed value.
    if S == ``Prod then
      let (cs, vs) ← tv ctx s
      return (cs, ← projE (i == 0) vs)
    let some m ← mirrorStruct? (← whnfR (← inferType s))
      | fail m!"a function bound in data: the projection `{e}` has no costed form"
    unless m.struct == S do fail m!"internal: the projection `{e}`"
    let (cs, vs) ← tv ctx s
    return (cs, ← mirrorProj m.fieldTypes.size i vs)
  | .app .. | .const .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    -- A sum holding functions: the costed value of the component.
    if (f.isConstOf ``Sum.inl || f.isConstOf ``Sum.inr) && args.size == 3 then
      let (ca, va) ← tv ctx args[2]!
      let ha := (← hatTy? args[0]!).getD args[0]!
      let hb := (← hatTy? args[1]!).getD args[1]!
      let .const n lvls := f | fail m!"internal: `{e}`"
      let lvls' ← [ha, hb].mapM fun x => (getDecLevel x : MetaM Level)
      unless lvls.length == 2 do fail m!"internal: `{e}`"
      return (ca, mkAppN (mkConst n lvls') #[ha, hb, va])
    -- An optional value holding functions: the costed value of its content.
    if f.isConstOf ``Option.some && args.size == 2 then
      let (ca, va) ← tv ctx args[1]!
      return (ca, ← mkAppM ``Option.some #[va])
    if f.isConstOf ``Option.none && args.size == 1 then
      let hw ← whnfR ht
      unless hw.isAppOfArity ``Option 1 do fail m!"internal: `{e}`"
      return (natE 0, ← mkAppOptM ``Option.none #[hw.appArg!])
    if let .const fc _ := f then
      if let some m ← mirrorStruct? tw then
        -- A structure holding functions built by its constructor: the mirror tuple of the
        -- costed values of its fields.
        if fc == m.ctor && args.size == m.params.size + m.fieldTypes.size then
          let mut cs := #[]
          let mut vs := #[]
          for a in args.extract m.params.size args.size do
            let (c, v) ← tv ctx a
            cs := cs.push c
            vs := vs.push v
          return (sum cs, ← mirrorMk vs)
      -- A field of a structure holding functions: the component of its costed value.
      if let some info ← getProjectionFnInfo? fc then
        if !info.fromClass && args.size == info.numParams + 1 then
          let s := args[info.numParams]!
          if let some m ← mirrorStruct? (← whnfR (← inferType s)) then
            if let some i := m.projs.idxOf? fc then
              let (cs, vs) ← tv ctx s
              return (cs, ← mirrorProj m.fieldTypes.size i vs)
    -- A call of a local function with a cost companion whose result holds functions: the
    -- functions of the result are tables (`ι`).
    if let .fvar id := f then
      if let some { kind := .fn, companion? := some _, .. } := ctx.locals.get? id then
        unless tw.isForall do return (← costOf ctx e, ← iotaE t e)
    if f.isConstOf ``Prod.mk && args.size == 4 then
      let (ca, va) ← tv ctx args[2]!
      let (cb, vb) ← tv ctx args[3]!
      return (add ca cb, ← mkAppM ``Prod.mk #[va, vb])
    if let some e' ← boolRecIte? e then return ← tv ctx e'
    if f.isConstOf ``ite && args.size == 5 then
      let (ca, va) ← tv ctx args[3]!
      let (cb, vb) ← tv ctx args[4]!
      let lvl ← getLevel ht
      return (add (natE 1) (add (← propCost ctx args[1]!)
          (iteNatE args[1]! args[2]! ca cb)),
        mkApp5 (mkConst ``ite [lvl]) ht args[1]! args[2]! va vb)
    if tw.isForall then
      -- A partial application of a constant or of a local function with a cost companion:
      -- the arguments are evaluated when the closure is built; the companion prices the call
      -- with them as values. A partial application of any other local function is a table,
      -- applied at unit cost.
      -- Functions in the closure's results are tables (`ι`).
      let cargs ← argsCost ctx args
      let val ← forallTelescope tw fun ys body => do
        if (← hatTy? body).isNone then return e
        mkLambdaFVars ys (← iotaE body (mkAppN e ys))
      match f with
      | .const _ _ => pure ()
      | .fvar id =>
        match ctx.locals.get? id with
        | some { kind := .fn, companion? := some _, .. } => pure ()
        | _ =>
          let z ← forallTelescope tw fun ys _ => mkLambdaFVars ys (natE 0)
          return (cargs, ← mkAppM ``Prod.mk #[val, z])
      | _ => fail m!"a function bound in data: the closure `{e}` is not a partial application \
          of a constant or a local function"
      let comp ← partialAppCompanion ctx e tw f args 0 #[] #[]
      return (cargs, ← mkAppM ``Prod.mk #[val, comp])
    let env ← getEnv
    -- A match whose matcher is compiled to a recursor, a `casesOn` or a sparse `casesOn` (a
    -- match with a wildcard arm, whose catch-all alternative is one branch shared by the
    -- constructors it covers; a definition by cases unfolds to its matcher): the match of the
    -- costed values of the branches, priced as a data-valued match. A matcher compiled to `if`s
    -- on decidable equalities is unfolded below.
    if let some app ← matchMatcherApp? e then
      let byRec := match env.find? app.matcherName with
        | some (.defnInfo mi) => (mi.value.find? fun s => match s with
            | .const n _ => isCasesOnLike env n || isRecCore env n
            | _ => false).isSome
        | _ => false
      if byRec then
        let (v, _) ← mapMatch ctx e ht (fun ctx b => return (← tv ctx b).2)
          (some fun _ => pure ht)
        return (← costMatch ctx e, v)
    let .const c lvls := f | fail m!"a function bound in data: the value `{e}` of type `{t}` \
      has no costed form"
    let some (.defnInfo dv) := env.find? c | fail m!"a function bound in data: the value `{e}` \
      of type `{t}` is not a definition to unfold"
    if (Structural.eqnInfoExt.find? env c).isSome || (WF.eqnInfoExt.find? env c).isSome then
      -- A recursive data function whose result holds functions: the call of its costed value
      -- `c.timed`, derived by its recursion (`deriveHatValue`), at the costed values of the
      -- arguments, priced by the cost of `c`. A recursive call in the derivation of `c.timed`
      -- is a call of the local standing for it; its cost is not used.
      let selfCall := ctx.selfHat?.any (·.1 == c)
      let target ← match ctx.selfHat? with
        | some (self, rec) => if self == c then pure rec else ensureHat ctx c f
        | none => ensureHat ctx c f
      let out ← hatArgs ctx f args
      let arity ← forallTelescope (← inferType target) fun ys _ => pure ys.size
      unless out.size == arity do
        fail m!"the recursive `{c}` returns functions and is applied to {args.size} arguments, \
          not to all binders of its costed value"
      let cost ← if selfCall then pure (natE 0) else costOf ctx e
      return (cost, mkAppN target out)
    if ctx.depth ≥ (← maxDepth) then
      fail m!"needs a registered primitive: `{c}` unfolds too deep"
    unless lvls.length == dv.levelParams.length do fail m!"`{c}` does not unfold"
    let e' ← bindArgsShared (dv.value.instantiateLevelParams dv.levelParams lvls) args
    if let some r := ctx.unfolded? then
      unless isMatcherCore env c do
        let headed ← lambdaTelescope dv.value fun _ b =>
          pure (isCaseHead env (letBody b).getAppFn.constName)
        if headed then r.modify fun a => if a.contains c then a else a.push c
    let (cb, vb) ← tv { ctx with depth := ctx.depth + 1 } e'
    let callCost := if ← isReducible c then natE 0 else natE 1
    return (add callCost cb, vb)
  | _ => fail m!"a function bound in data: the value `{e}` of type `{t}` has no costed form"

/-- The companion of the closure `e = f args` of type `tw`: the cost of `f args ys` at fresh
arguments `ys`, with each data argument that is not a variable, a literal or a closure
standing for its value at no cost. -/
partial def partialAppCompanion (ctx : Ctx) (e tw f : Expr) (args : Array Expr) (i : Nat)
    (vals : Array Expr) (zs : Array (Expr × Expr)) : TermElabM Expr := do
  if h : i < args.size then
    let a := args[i]
    if (← isDataExpr a) && (← keepsLet (← inferType a) a) then
      withLocalDeclD `v (← inferType a) fun z =>
        partialAppCompanion ctx e tw f args (i + 1) (vals.push z) (zs.push (z, a))
    else partialAppCompanion ctx e tw f args (i + 1) (vals.push a) zs
  else
    let c ← forallTelescope tw fun ys _ => do
      mkLambdaFVars ys (← costOf ctx (mkAppN (mkAppN f vals) ys))
    return c.replaceFVars (zs.map (·.1)) (zs.map (·.2))

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
  -- An application of a costed closure held in data.
  if let some (c, rest, hd) ← closureHead? ctx e then
    return add (← costOf ctx hd) (← closureApp ctx c rest).1
  match f with
  | .fvar id =>
    match ctx.locals.get? id with
    | some { kind := .fn, companion? := some c, .. } =>
      let arity ← forallTelescope (← whnfR (← inferType c)) fun ys _ => pure ys.size
      if args.size < arity then argsCost ctx args
      else
        let now := args.extract 0 arity
        let call := add (natE 1) (add (mkAppN c now) (← argsCost ctx now))
        if args.size == arity then return call
        -- A result that is a function under a non-reducible name (`SPComp α`, a function of
        -- the heap): the result is a table, and its application to the remaining arguments
        -- costs one plus their costs.
        let rest := args.extract arity args.size
        return add call (add (natE 1) (← argsCost ctx rest))
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
  if let some (.ctorInfo ci) := env.find? c then
    -- The parameters of the inductive type are not arguments of the call.
    return ← argsCost ctx (args.extract ci.numParams args.size)
  if freeConstants.contains c then
    return ← argsCost ctx args
  -- A partial application is a closure.
  let arity ← forallTelescope (← inferType f) fun ys _ => pure ys.size
  if args.size < arity then return ← argsCost ctx args
  if isCasesOnRecursor env c then
    return ← costCases ctx e c args
  -- A registered cost.
  let reg := c ++ `timedCost
  if let some (_, sc) := ctx.selfCosts.find? (·.1 == c) then
    return add (natE 1) (add (mkAppN sc (← costArgs ctx f args)) (← argsCost ctx args))
  if env.contains reg then
    let regArgs ← costArgs ctx f args
    let regE ← mkAppOptM reg (regArgs.map some)
    -- A derived cost that takes the cost companions of field paths of `c`'s binders: the
    -- caller passes its companions for the same paths at the arguments of the call.
    let extra ← forallTelescope (← inferType regE) fun ys _ => pure ys.size
    let mut fieldArgs := #[]
    if extra > 0 then
      -- In the first pass, every path without a companion is recorded before the call is
      -- priced without its field costs.
      let mut missing := false
      for p in ← calleeFieldPaths c f.constLevels! args do
        let p ← reduceFieldArg p
        -- The key of a field of a structure computed by a definition, for a path that is not a
        -- field path of the binders (those keep their own companions).
        let ck? ← if p.isLambda || (← isFieldPathStep ctx p) then pure none
          else computedPathKey? ctx p
        if let some (_, cc) := ctx.fields.find? (·.1 == p) then
          fieldArgs := fieldArgs.push cc
        else if let some (_, cc) := ctx.fields.find? (·.1 == (← canonPath p)) then
          fieldArgs := fieldArgs.push cc
        else if ← isValueField ctx p then
          -- A field of a structure value: priced at the structure's value.
          fieldArgs := fieldArgs.push (← companionOf ctx p)
        else if let some (key, bs) := ck? then
          -- A field of a structure computed by a definition: the companion of the key,
          -- applied to the arguments that compute the structure.
          if let some (_, cc) := ctx.fields.find? (·.1 == key) then
            fieldArgs := fieldArgs.push (mkAppN cc bs)
          else if let some r := ctx.fieldRec? then
            unless (← r.get).contains key do r.modify (·.push key)
            missing := true
          else
            fail m!"the cost `{reg}` takes the cost of the field `{p}`, whose key `{key}` has \
              no cost companion"
        else if let some r := ctx.fieldRec? then
          if !p.hasLooseBVars && (p.isLambda || (← isFieldPathStep ctx p)) then
            unless (← r.get).contains p do r.modify (·.push p)
          missing := true
        else
          fail m!"the cost `{reg}` takes the cost of the field `{p}`, which is not a field of a \
            binder of the reduction"
      if missing then return add (natE 1) (← argsCost ctx args)
      unless fieldArgs.size == extra do
        fail m!"the cost `{reg}` takes {extra} field costs at `{e}`, and {fieldArgs.size} were \
          found"
    return add (natE 1) (add (mkAppN regE fieldArgs) (← argsCost ctx args))
  if natUnitOps.contains c && args.size > 0 && (args[0]!).isConstOf ``Nat then
    return add (natE 1) (← argsCost ctx args)
  -- Arithmetic modulo `p`: one unit, a word operation for the fixed modulus.
  -- The test of the type is nested, so that `args[0]` is read only when it exists (a `←`
  -- inside a condition is run before the condition).
  if zmodUnitOps.contains c then
    if h : 0 < args.size then
      if (← whnfR args[0]).isAppOfArity `ZMod 1 then
        return add (natE 1) (← argsCost ctx args)
  -- Operations on fixed-width words: one unit.
  if wordUnitOps.contains c then
    if h : 0 < args.size then
      if ← isWordType args[0] then
        return add (natE 1) (← argsCost ctx args)
  -- A comparison of words decided at one unit: `decide (a < b)` is priced by the rule for
  -- `Decidable.decide` below.
  if c == ``Decidable.decide && args.size == 2 then
    return add (natE 1) (← propCost ctx args[0]!)
  if let some e' ← boolRecIte? e then return ← costOf ctx e'
  if c == ``ite && args.size == 5 then
    return add (natE 1) (add (← propCost ctx args[1]!)
      (iteNatE args[1]! args[2]! (← costOf ctx args[3]!) (← costOf ctx args[4]!)))
  if c == ``dite && args.size == 5 then
    let ct ← withEta args[3]! 1 fun hs b => do mkLambdaFVars hs (← costOf ctx b)
    let ce ← withEta args[4]! 1 fun hs b => do mkLambdaFVars hs (← costOf ctx b)
    return add (natE 1) (add (← propCost ctx args[1]!)
      (mkApp5 (mkConst ``dite [Level.one]) (mkConst ``Nat) args[1]! args[2]! ct ce))
  if ← isMatcher c then
    return ← costMatch ctx e
  -- A structure projection.
  if let some info ← getProjectionFnInfo? c then
    -- A method of an abstract algebraic structure, an instance built from a local instance:
    -- one call of the interface, one unit.
    if info.fromClass && isUnitMethod c && args.size > info.numParams then
      if ← builtFromLocalInstance args[info.numParams]! then
        return add (natE 1) (← argsCost ctx (args.extract (info.numParams + 1) args.size))
    -- A field of a local structure or instance with a cost companion.
    if args.size > info.numParams + 1 then
      let p := mkAppN f (args.extract 0 (info.numParams + 1))
      let rest := args.extract (info.numParams + 1) args.size
      -- A field below a projection of a constructor application (`{ cfg := s.cfg, … }.cfg.env`):
      -- the structure is priced, and the field is priced at the reduced path (`s.cfg.env`).
      if !info.fromClass then
        let p' ← reduceFieldArg p
        if p' != p then
          return add (← costOf ctx args[info.numParams]!) (← costOf ctx (mkAppN p' rest))
      -- A function field of a structure below a data path with a binder (`Z.input.2.f x`):
      -- the costed closure of the field in the costed value of the data path, applied.
      if !info.fromClass then
        let s := args[info.numParams]!
        if let some sv ← pathHat? ctx s false then
          if let some m ← mirrorStruct? (← whnfR (← inferType s)) then
            if let some i := m.projs.idxOf? c then
              if (← hatTy? m.fieldTypes[i]!).isSome then
                let comp ← mirrorProj m.fieldTypes.size i sv
                return add (← costOf ctx s) (← closureApp ctx comp rest).1
      if let some (_, cc) := ctx.fields.find? (·.1 == p) then
        let arity ← forallTelescope (← whnfR (← inferType cc)) fun ys _ => pure ys.size
        -- A field whose result is a function under a non-reducible name, applied further
        -- (`Z.obs z o h`, the computation `Z.obs z o : SPComp ζ` run on the heap `h`): the
        -- companion prices the call, and the result is a table whose application to the
        -- remaining arguments costs one plus their costs, as for a local with a companion.
        if rest.size > arity then
          let now := rest.extract 0 arity
          let later := rest.extract arity rest.size
          let call := add (natE 1) (add (mkAppN cc now) (← argsCost ctx now))
          return add call (add (natE 1) (← argsCost ctx later))
        unless rest.size == arity do
          fail m!"the field `{c}` is applied to {rest.size} arguments in `{e}`, and its cost \
            companion takes {arity}"
        return add (natE 1) (add (mkAppN cc rest) (← argsCost ctx rest))
      -- The first pass records the field paths that start at a binder of the reduction.
      if let some r := ctx.fieldRec? then
        if !p.hasLooseBVars && (← isFieldPath ctx args[info.numParams]!) then
          unless (← r.get).contains p do r.modify (·.push p)
          return add (natE 1) (← argsCost ctx rest)
      -- A field of a computed structure `g b₁ … bₘ`: the structure is priced by the rules
      -- above, the field by a companion indexed by `b₁ … bₘ` and the arguments of the field.
      if !info.fromClass then
        if let some (key, bs) ← computedFieldKey? ctx f info.numParams args then
          let s := args[info.numParams]!
          if let some (_, cc) := ctx.fields.find? (·.1 == key) then
            return add (natE 1) (add (mkAppN cc (bs ++ rest))
              (add (← costOf ctx s) (← argsCost ctx rest)))
          if let some r := ctx.fieldRec? then
            unless (← r.get).contains key do r.modify (·.push key)
            return add (natE 1) (add (← costOf ctx s) (← argsCost ctx rest))
    if info.fromClass then
      let inst := args[info.numParams]!
      -- A method of an abstract algebraic structure (an instance built from a local
      -- hypothesis) without a cost companion: a call of the abstract interface, at one unit.
      if inst.consumeMData.isFVar then
        return add (natE 1) (← argsCost ctx (args.extract (info.numParams + 1) args.size))
      let some e' ← unfoldProjInst? e
        | if inst.hasFVar then
            return add (natE 1) (← argsCost ctx (args.extract (info.numParams + 1) args.size))
          fail m!"needs a registered primitive: the class method `{c}` does not unfold"
      if ctx.depth ≥ (← maxDepth) then
        fail m!"needs a registered primitive: `{c}` unfolds too deep"
      return ← costOf { ctx with depth := ctx.depth + 1 } e'
    if args.size > info.numParams + 1 then
      -- A field of a structure that reduces to a constructor application (a constant
      -- structure, or a `let` bound to one): the structure is priced, and the field's value
      -- applied to the arguments is priced as unfolded.
      let s := args[info.numParams]!
      let rest := args.extract (info.numParams + 1) args.size
      let sv ← match s.consumeMData with
        | .fvar id => do
          match ← id.getValue? with
          | some v => pure v
          | none => pure s
        | _ => pure s
      let sw ← whnf sv
      if let some cv ← isConstructorApp? sw then
        if let some v := sw.getAppArgs[cv.numParams + info.i]? then
          if ctx.depth ≥ (← maxDepth) then
            fail m!"needs a registered primitive: `{c}` unfolds too deep"
          return add (← costOf ctx s)
            (← costOf { ctx with depth := ctx.depth + 1 } (mkAppN v rest).headBeta)
      -- A function field of a structure holding functions: the costed closure of the field
      -- in the costed value of the structure, applied.
      if let some m ← mirrorStruct? (← whnfR (← inferType s)) then
        if let some i := m.projs.idxOf? c then
          if (← hatTy? m.fieldTypes[i]!).isSome then
            let (cs, vs) ← tv ctx s
            let comp ← mirrorProj m.fieldTypes.size i vs
            return add cs (← closureApp ctx comp rest).1
      fail m!"a function bound in data: the field `{c}` is applied in `{e}`"
    return ← argsCost ctx args
  -- An operation on finite sets or multisets is defined through a quotient, whose internals
  -- have no cost: it is priced by its registered cost (`CatCryptCore.Tactics.StdCosts`).
  if quotientLibs.contains c.getRoot then
    fail m!"needs a registered primitive: `{c}` is an operation on a quotient type (`Finset`, \
      `Multiset`) without a registered cost `{reg}`; the costs of `Finset.sum`, `Finset.prod`, \
      `Finset.univ`, `Finset.range` and `Finset.erase` are registered in \
      `CatCryptCore.Tactics.StdCosts`, which the module must import"
  -- A definition, unfolded.
  let some info := env.find? c | fail m!"unknown constant `{c}`"
  if (Structural.eqnInfoExt.find? env c).isSome || (WF.eqnInfoExt.find? env c).isSome then
    -- A recursive data function: its cost is derived by its recursion, then the call is priced
    -- by it.
    try
      deriveCostCore #[] c
    catch ex =>
      fail m!"needs a registered primitive: `{c}` is recursive and has no registered cost \
        `{reg}`, and `derive_cost {c}` fails:{indentD ex.toMessageData}"
    return ← costConst ctx e c args
  let .defnInfo dv := info
    | fail m!"needs a registered primitive: `{c}` has no definition to price and no registered \
        cost `{reg}`"
  let depthLimit ← maxDepth
  if ctx.depth ≥ depthLimit then
    fail m!"needs a registered primitive: `{c}` unfolds deeper than {depthLimit} definitions \
      (option `derive_timed.maxDepth`)"
  -- The arguments are bound by `let`s around the body, so that each is priced once.
  let lvls := f.constLevels!
  unless lvls.length == dv.levelParams.length do
    fail m!"needs a registered primitive: `{c}` does not unfold"
  let e' ← bindArgsShared (dv.value.instantiateLevelParams dv.levelParams lvls) args
  if (e'.find? fun s => s.isConstOf ``WellFounded.fix || s.isAppOf ``Nat.rec
      || s.isAppOf ``List.rec).isSome then
    fail m!"needs a registered primitive: `{c}` unfolds to a recursor"
  -- An abbreviation is notation: unfolded without the cost of a call.
  let callCost := if ← isReducible c then natE 0 else natE 1
  return add callCost (← costOf { ctx with depth := ctx.depth + 1 } e')

/-- The cost of a data-valued `casesOn` of an inductive type without indices: one, the major
premise, and the branch taken. A case analysis applied to `k` further arguments `a₁ … aₖ`
(the `Bool.casesOn` of a decidable `if`, applied to the proof of reflection and to the
arguments of the function it selects) is priced by the case analysis of the same major premise
with the motive `fun x => (y₁ : A₁ x) → … → (yₖ : Aₖ x) → ℕ`, whose branches are the costs of
the branches at `y₁ … yₖ`, applied to `a₁ … aₖ`, plus the costs of the arguments. -/
partial def costCases (ctx : Ctx) (e : Expr) (c : Name) (args : Array Expr) :
    TermElabM Expr := do
  let some (.inductInfo iv) := (← getEnv).find? c.getPrefix
    | fail m!"`{c}` is not the case analysis of an inductive type"
  unless iv.numIndices == 0 do fail m!"the case analysis `{e}` is over an indexed family"
  let arity := iv.numParams + 2 + iv.numCtors
  unless args.size ≥ arity do
    fail m!"the case analysis `{e}` is applied to fewer arguments than its minor premises"
  let extra := args.extract arity args.size
  let k := extra.size
  let major := args[iv.numParams + 1]!
  -- the motive `fun x => (ys : As x) → ℕ` over the binders of the further arguments
  let (motive, mlvl) ← withLocalDeclD `x (← inferType major) fun x => do
    let body := (mkApp args[iv.numParams]! x).headBeta
    let ty ← forallBoundedTelescope body k fun ys _ => do
      unless ys.size == k do
        fail m!"the motive of the case analysis `{e}` takes fewer than {k} arguments"
      mkForallFVars ys (mkConst ``Nat)
    return (← mkLambdaFVars #[x] ty, ← getLevel ty)
  let mut minors := #[]
  for i in [0:iv.numCtors] do
    let ctor ← getConstInfoCtor iv.ctors[i]!
    let minor := args[iv.numParams + 2 + i]!
    minors := minors.push (← withEta minor (ctor.numFields + k) fun fs b => do
      mkLambdaFVars fs (← costOf ctx b))
  let levels := match e.getAppFn.constLevels! with
    | _ :: ls => mlvl.normalize :: ls
    | [] => []
  let cases := mkAppN (mkConst c levels)
    (args[0:iv.numParams].toArray ++ #[motive, major] ++ minors ++ extra)
  return add (natE 1) (add (← costOf ctx major) (add cases (← argsCost ctx extra)))

/-- The matcher application `e` with its discriminants and alternatives prepared for a
translation with result type `resultType`: the translated discriminants replaced by their
erasures, and each alternative translated by `alt` in the context in which its fields stand
for the translated discriminants they bind. A motive whose body depends on the discriminants
(a result type `SPTree (Fin n → X)` of a match on `n`) is translated by `motiveRes?` at its
body. Returns the new application and the cost of the data discriminants. -/
partial def mapMatch (ctx : Ctx) (e resultType : Expr)
    (alt : Ctx → Expr → TermElabM Expr)
    (motiveRes? : Option (Expr → TermElabM Expr) := none) : TermElabM (Expr × Expr) := do
  let some app ← matchMatcherApp? e | fail m!"`{e}` is not a matcher application"
  unless app.remaining.isEmpty do
    fail m!"the match `{e}` has a motive that depends on its discriminants"
  let mut discrs := #[]
  let mut trDiscrs : Array (Expr × LocalInfo) := #[]
  let mut cost := natE 0
  -- The discriminants that are local, whose types the motive abstracts.
  let discrFVars := (app.discrs.map (·.consumeMData)).filter (·.isFVar)
  let dependsOnDiscr (t : Expr) : Bool :=
    t.hasAnyFVar fun f => discrFVars.any (·.fvarId! == f)
  -- The function discriminants whose companions are carried through the match (the convoy
  -- pattern): those whose type depends on another discriminant, so that the field binding
  -- them has the type of its alternative, at which the companion has no type. Each is the
  -- position of the discriminant with its companion.
  let mut convoy : Array (Nat × Expr) := #[]
  for d in app.discrs, j in [0:app.discrs.size] do
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
        match info.kind, info.companion? with
        | .fn, some c =>
          if dependsOnDiscr dt then convoy := convoy.push (j, c)
          else trDiscrs := trDiscrs.push (dt, info)
        | _, _ => trDiscrs := trDiscrs.push (dt, info)
      | none => discrs := discrs.push d
    | _ =>
      discrs := discrs.push d
      cost := add cost (← costOf ctx d)
      -- A function passed as a discriminant (`Option.bind o f` matches on `f`): the field
      -- that binds it is a local function with the companion of the function.
      let dt ← inferType d
      if (← isDataExpr d) && (← whnfR dt).isForall && (← treeTy? dt).isNone then
        let c ← companionOf ctx d
        if dependsOnDiscr dt then convoy := convoy.push (j, c)
        else trDiscrs := trDiscrs.push (dt, ⟨.fn, d, some c⟩)
  let convoyTypes ← convoy.mapM fun (_, c) => inferType c
  let motive ← lambdaTelescope app.motive fun xs body => do
    let res ← if xs.any (fun x => body.containsFVar x.fvarId!) then
      match motiveRes? with
      | some f => f body
      | none => fail m!"the match `{e}` has a motive that depends on its discriminants"
    else pure resultType
    -- The type of each carried companion, with the discriminants abstracted.
    let xs' := (app.discrs.zip xs).filterMap fun (d, x) =>
      if d.consumeMData.isFVar then some x else none
    let res := convoyTypes.foldr (init := res) fun ct acc =>
      .forallE `cost (ct.replaceFVars discrFVars xs') acc .default
    mkLambdaFVars xs res
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
    -- With carried companions, the alternative takes its fields and then one companion for
    -- each carried discriminant.
    let n ← if convoy.isEmpty then forallTelescope aty fun ys _ => pure ys.size
      else forallTelescopeReducing aty fun ys _ => pure (ys.size - convoy.size)
    let i := alts.size
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
      -- A field of a pattern of a discriminant with a costed value (a block in a sum, a
      -- function field of a state): its costed value keeps the field's functions and reads
      -- their cost companions from the discriminant's costed value.
      if let some pats ← altPatterns app alts.size fs then
        for d in app.discrs, p in pats do
          let .fvar id := d.consumeMData | continue
          let some { kind := .hat, value := v, .. } := ctx.locals.get? id | continue
          for (fv, c) in ← patternHats p v do
            unless fs.contains fv && (ctx'.locals.get? fv.fvarId!).isNone do continue
            let ft ← inferType fv
            if (← hatTy? ft).isNone then continue
            ctx' := { ctx' with
              locals := ctx'.locals.insert fv.fvarId! ⟨.hat, ← refillE ft fv c, none⟩ }
      if convoy.isEmpty then return ← mkLambdaFVars fs (← alt ctx' b)
      -- The carried companions at the types of this alternative: each is the companion of
      -- the field that the alternative's pattern binds to its discriminant.
      let pats? ← altPatterns app i fs
      forallBoundedTelescope (← instantiateForall aty fs) (some convoy.size) fun cs _ => do
        unless cs.size == convoy.size do
          fail m!"internal: the alternative {i} of `{e}` takes fewer carried companions"
        let mut ctx'' := ctx'
        for (j, _) in convoy, cc in cs do
          let some pats := pats? | continue
          let some p := pats[j]? | continue
          let p := p.consumeMData
          if p.isFVar && fs.contains p then
            ctx'' := { ctx'' with locals := ctx''.locals.insert p.fvarId! ⟨.fn, p, some cc⟩ }
        mkLambdaFVars (fs ++ cs) (← alt ctx'' b)
    alts := alts.push a'
    ty := body.instantiate1 a'
  let e' := mkAppN (mkConst app.matcherName levels.toList)
    (app.params ++ #[motive] ++ discrs ++ alts ++ convoy.map (·.2))
  return (e', cost)

/-- The cost of a data-valued match: one, the discriminants, and the branch taken. -/
partial def costMatch (ctx : Ctx) (e : Expr) : TermElabM Expr := do
  let (e', cd) ← mapMatch ctx e (mkConst ``Nat) costOf (some fun _ => pure (mkConst ``Nat))
  return add (natE 1) (add cd ((← constAlts? e').getD e'))

/-- The translation of the oracle tree `e`: a step-prefixed costed tree whose erasure is `e`
with the translated locals erased. -/
partial def tr (ctx : Ctx) (e : Expr) : TermElabM Expr := do
  let e := pushLetApp e.consumeMData.headBeta
  let some T ← treeTyH? (← inferType e)
    | fail m!"`{e}` is not a tree of a registered kind"
  match e with
  | .letE n t v b _ =>
    unless ← keepsLet t v do return ← tr ctx (b.instantiate1 v)
    if let some ht ← hatTy? t then
      -- A `let` of a value holding functions (a state structure): its costed value is bound by
      -- a second `let` and shared by every use, in the step cost and in the costed tree. A
      -- value without a costed form (a field that is a function into an untimed computation)
      -- is priced by the rule below, which prices only the fields the body uses.
      let s ← saveState
      let recs ← ctx.fieldRec?.mapM (·.get)
      let unf ← ctx.unfolded?.mapM (·.get)
      let tvd? ← try some <$> tv ctx v catch _ => do
        s.restore
        if let (some r, some a) := (ctx.fieldRec?, recs) then r.set a
        if let (some r, some a) := (ctx.unfolded?, unf) then r.set a
        pure none
      if let some (cv, vh) := tvd? then
        return ← withLetDecl n t v fun x => withLetDecl (n.appendAfter "Hat") ht vh fun xh => do
          let ctx' := { ctx with locals := ctx.locals.insert x.fvarId! ⟨.hat, xh, none⟩ }
          let p ← tr ctx' (b.instantiate1 x)
          return T.mkPair (add cv (← mkLetFVars #[x, xh] (T.fstOf p)))
            (← mkLetFVars #[x, xh] (T.sndOf p))
    -- The value is priced once, in front; the costed tree keeps the `let`.
    let cv ← costOf ctx v
    withLetDecl n t v fun x => do
      let p ← tr ctx (b.instantiate1 x)
      let body := (T.sndOf p).abstract #[x]
      return T.mkPair (add cv ((T.fstOf p).replaceFVar x v)) (.letE n t v body false)
  | .fvar id =>
    match ctx.locals.get? id with
    | some { kind := .tree, value, .. } =>
      let some raw ← treeTy? (← inferType e) | fail m!"`{e}` is not a tree"
      liftBinderE T raw (raw.mkPair (natE 0) value)
    | _ => fail m!"a function bound in data: the {T.kind.noun} `{e}` has no costed form"
  | .app .. | .const .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .fvar id =>
      match ctx.locals.get? id with
      | some { kind := .treeFn, value, companion? := some c } =>
        let some raw ← treeTy? (← inferType e) | fail m!"`{e}` is not a tree"
        liftBinderE T raw (raw.mkPair (add (natE 1) (add (mkAppN c args) (← argsCost ctx args)))
          (mkAppN value args))
      | _ => fail m!"a function bound in data: the local `{f}` in `{e}` has no costed form"
    | .const c _ => trConst ctx e c args T
    | .proj S i s =>
      -- A field of a structure applied: translated as its projection function.
      let some sinfo := getStructureInfo? (← getEnv) S
        | fail m!"the {T.kind.noun} `{e}` is headed by a projection of a non-structure"
      let some field := sinfo.fieldNames[i]? | fail m!"the projection `{f}` has no field {i}"
      let pf ← mkAppM (S ++ field) #[s]
      tr ctx (mkAppN pf args)
    | _ => fail m!"the {T.kind.noun} `{e}` is not headed by a constant or a local"
  | _ => fail m!"the {T.kind.noun} `{e}` is not supported"

/-- The translation of a continuation `a` with `n` binders: its step cost and its costed tree,
both abstracted over the binders. -/
partial def trCont (ctx : Ctx) (a : Expr) (n : Nat) : TermElabM (Expr × Expr) := do
  if n == 0 then
    let some Ta ← treeTyH? (← inferType a) | fail m!"`{a}` is not a tree of a registered kind"
    let p ← tr ctx a
    return (Ta.fstOf p, Ta.sndOf p)
  withEta a n fun ys b => do
    let some Tb ← treeTyH? (← inferType b) | fail m!"`{b}` is not a tree of a registered kind"
    -- A sampled or received value holding functions: each function is a table, applied at
    -- unit cost (`ι`).
    let mut ctx := ctx
    for y in ys do
      let yt ← inferType y
      if (← hatTy? yt).isSome then
        ctx := { ctx with locals := ctx.locals.insert y.fvarId! ⟨.hat, ← iotaE yt y, none⟩ }
    let p ← tr ctx b
    return (← mkLambdaFVars ys (Tb.fstOf p), ← mkLambdaFVars ys (Tb.sndOf p))

/-- The translation of a function `a` of `m` arguments into trees, whose arguments are results
of costed trees: a binder holding functions stands for its costed value `x̂`, and `ε x̂` for
the binder in the costed tree. -/
partial def trPairFn (ctx : Ctx) (a : Expr) (m : Nat) : TermElabM Expr :=
  withEta a m fun ys b => do
    let rec go (i : Nat) (ctx : Ctx) (bs : Array Expr) (subst : Array (Expr × Expr)) :
        TermElabM Expr := do
      if h : i < ys.size then
        let y := ys[i]
        let yt ← inferType y
        match ← hatTy? yt with
        | some ht =>
          withLocalDeclD (← y.fvarId!.getUserName) ht fun v => do
            go (i + 1) { ctx with locals := ctx.locals.insert y.fvarId! ⟨.hat, v, none⟩ }
              (bs.push v) (subst.push (y, ← epsE yt v))
        | none => go (i + 1) ctx (bs.push y) subst
      else
        let p ← tr ctx b
        mkLambdaFVars bs (p.replaceFVars (subst.map (·.1)) (subst.map (·.2)))
    go 0 ctx #[] #[]

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
      let (c, v) ← tv ctx xs[i]
      outs := outs.push v
      cost := add cost c
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
      let some Ta ← treeTyH? (← inferType xs[i]) | fail m!"`{e}` has an unexpected type"
      let p ← tr ctx xs[i]
      trees := trees.set! i (Ta.sndOf p)
      treeCost := add treeCost (Ta.fstOf p)
  let mut outs := #[]
  let mut dataCost := natE 0
  for h : i in [0:xs.size] do
    let a := xs[i]
    match cb.roles[i]! with
    | .tree => outs := outs.push trees[i]!
    | .pairFn m => outs := outs.push (← trPairFn ctx a m)
    | .perCall extra m =>
      if (← hatTy? (← inferType e)).isSome ||
          (← xs.anyM fun x => do
            match ← treeTy? (← inferType x) with
            | some Tx => return (← hatTy? Tx.result).isSome
            | none => return false) then
        fail m!"a function bound in data: the result of a tree in `{e}` holds functions"
      let t ← withEta a m fun ys b => do mkLambdaFVars ys (add (natE extra) (← costOf ctx b))
      outs := outs.push a |>.push t
    | .data =>
      let (c, v) ← tv ctx a
      outs := outs.push v
      dataCost := add dataCost c
    | .keep | .cont _ => outs := outs.push a
  -- A simulation whose state holds functions: its costed form carries the erasure and the
  -- lift of the state, which state its erasure theorem.
  if cb.src == ``CatCrypt.Crypto.OracleAdv.simulate then
    let st ← inferType xs[xs.size - 1]!
    if (← hatTy? st).isSome then
      let r ← mkAppM ``CatCrypt.Crypto.OracleAdv.Timed.simulateHat
        (#[← epsFun st, ← iotaFun st] ++ outs)
      return T.delayE (add treeCost dataCost) r
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
  if let some e' ← boolRecIte? e then return ← tr ctx e'
  -- A dispatch on an optional value: the match of `optionDispatch`, whose alternative on
  -- `some` is a branch and not a function discriminant.
  if let some e' ← optionDispatch? e then return ← tr ctx e'
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
    -- A match on an oracle-tree binder is translated as its case analysis.
    if let some app ← matchMatcherApp? e then
      if app.discrs.any fun d => (treeLocal? ctx d).isSome then
        let some e' ← delta? e | fail m!"the match `{e}` does not unfold"
        return ← tr ctx (← Core.betaReduce e')
    -- A dependent motive `fun n => SPTree (τ n)`: the costed tree type at each `n`, of the
    -- interface of `T` (costed results or the plain one).
    let hatted := match ← treeTyH? (← inferType e) with
      | some Th => Th.pairType == T.pairType
      | none => false
    let motiveRes (body : Expr) : TermElabM Expr := do
      let some Tb ← (if hatted then treeTyH? body else treeTy? body)
        | fail m!"the match `{e}` has a motive whose body `{body}` is not a tree"
      return Tb.pairType
    let (e', cd) ← mapMatch ctx e T.pairType tr (some motiveRes)
    return T.delayE (add (natE 1) cd) e'
  if c == ``CatCrypt.Crypto.OracleAdv.casesOn then
    return ← trTreeCases ctx e args T
  -- A tree-valued field of a field path (`S.kem.encaps pk`, a program of a scheme structure):
  -- a primitive, whose oracle tree runs at the unit cost of its nodes and whose computation
  -- is priced by its cost companion, indexed by the arguments of the field.
  if let some info ← getProjectionFnInfo? c then
    if !info.fromClass && args.size > info.numParams &&
        T.kind.tree == ``CatCrypt.Crypto.OracleAdv then
      let p := mkAppN e.getAppFn (args.extract 0 (info.numParams + 1))
      let rest := args.extract (info.numParams + 1) args.size
      if !p.hasLooseBVars && (← isFieldPath ctx args[info.numParams]!) then
        let leaf ← mkAppM ``CatCrypt.Crypto.OracleAdv.Timed.ofAdv #[e]
        if let some (_, cc) := ctx.fields.find? (·.1 == p) then
          return T.mkPair (add (natE 1) (add (mkAppN cc rest) (← argsCost ctx rest))) leaf
        if let some r := ctx.fieldRec? then
          unless (← r.get).contains p do r.modify (·.push p)
          return T.mkPair (add (natE 1) (← argsCost ctx rest)) leaf
  -- A non-recursive callee generic in its state type, called at a state holding functions: its
  -- body is translated in the caller's context, where the state has its costed value, and the
  -- erasure theorem unfolds it.
  if ctx.self?.all (·.1 != c) && (← unfoldsGenericCall c e) then
    if ctx.depth ≥ (← maxDepth) then
      fail m!"needs a registered costed form: `{c}` unfolds too deep"
    let some e' ← delta? e | fail m!"the call `{e}` does not unfold"
    if let some r := ctx.unfolded? then
      r.modify fun a => if a.contains c then a else a.push c
    return ← tr { ctx with depth := ctx.depth + 1 } (← Core.betaReduce e')
  -- A call of a reduction.
  let target ← match ctx.self? with
    | some (self, rec) => if self == c then pure rec else ensureTimed ctx c e.getAppFn
    | none => ensureTimed ctx c e.getAppFn
  callTimed ctx e target args T

/-- The case analysis `OracleAdv.casesOn A ret rand query` of an oracle-tree binder `A` with
costed form `A'`, translated as the case analysis `OracleAdv.Timed.casesOn A'` of the costed
tree (a handler of the nodes of `A`, `T.Timed` having the constructors of `T`): the
continuation `k` of a `rand` or `query` node of `A` stands for the continuation `k'` of the
costed node, with the node's step cost `c` as its cost companion. The case analysis costs one.
A recursive call on `k x` is a recursive call on `k' x`, so a reduction defined by structural
recursion on `A` gets a costed form defined by structural recursion on `A'`. -/
partial def trTreeCases (ctx : Ctx) (e : Expr) (args : Array Expr) (T : TreeTy) :
    TermElabM Expr := do
  unless args.size == 8 do
    fail m!"the case analysis `{e}` has a motive that depends on further arguments"
  let major := args[4]!
  let some A' := treeLocal? ctx major
    | fail m!"a case analysis of the oracle tree `{major}`, which is not a binder"
  let some Tm ← treeTy? (← inferType major) | fail m!"`{major}` is not an oracle tree"
  let motive ← withLocalDeclD `x Tm.timedType fun x => mkLambdaFVars #[x] T.pairType
  let cases := mkAppN (mkConst ``CatCrypt.Crypto.OracleAdv.Timed.casesOn [← getLevel T.pairType])
    (Tm.params ++ #[motive, A'])
  let minorTys ← forallBoundedTelescope (← inferType cases) (some 3) fun ms _ =>
    ms.mapM fun m => inferType m
  unless minorTys.size == 3 do fail m!"internal: unexpected type of `{cases}`"
  -- The `ret` alternative.
  let altRet ← withEta args[5]! 1 fun ys b => do
    mkLambdaFVars ys (T.delayE (natE 1) (← tr ctx b))
  -- A node alternative: the target fields end with the step cost `c` and the continuation
  -- `k'`; the source alternative takes the fields before `c` and the continuation `k`.
  let node (minor : Expr) (ty : Expr) : TermElabM Expr :=
    forallTelescope ty fun fs _ => do
      let c := fs[fs.size - 2]!
      let k' := fs[fs.size - 1]!
      let kTy ← forallTelescope (← inferType k') fun ys _ => mkForallFVars ys Tm.type
      withLocalDeclD `k kTy fun k => do
        let srcFields := (fs.extract 0 (fs.size - 2)).push k
        let b ← Core.betaReduce (mkAppN minor srcFields)
        let ctx' := { ctx with locals := ctx.locals.insert k.fvarId! ⟨.treeFn, k', some c⟩ }
        let p ← tr ctx' b
        let p := p.replaceFVar k (← erasure .treeFn kTy k')
        mkLambdaFVars fs (T.delayE (natE 1) p)
  let altRand ← node args[6]! minorTys[1]!
  let altQuery ← node args[7]! minorTys[2]!
  -- The unit of the case analysis is charged in each alternative, so that the case analysis
  -- heads the costed form and Lean derives its equations.
  return mkAppN cases #[altRet, altRand, altQuery]

/-- The costed form of the reduction `c` at the universe levels of `f`: registered, or
derived now. -/
partial def ensureTimed (ctx : Ctx) (c : Name) (f : Expr) : TermElabM Expr := do
  let name := c ++ ctx.suffix
  unless (← getEnv).contains name do
    if ctx.visiting.contains c then
      fail m!"`{c}` is reached again while its costed form is derived (mutual recursion)"
    try
      -- The callee is derived in its own context: the locals, fields, substitutions and the
      -- plain interface of the caller are not the callee's.
      deriveTimed { suffix := ctx.suffix, visiting := ctx.visiting.insert c } c
    catch ex =>
      throwError m!"derive_timed: while deriving the costed form of the callee `{c}`:\n\
        {ex.toMessageData}"
  return mkConst name f.constLevels!

/-- The costed value `c.timed` of the recursive data function `c` whose result holds functions,
at the universe levels of `f`: registered, or derived now (`deriveHatValue`). -/
partial def ensureHat (ctx : Ctx) (c : Name) (f : Expr) : TermElabM Expr := do
  let name := c ++ ctx.suffix
  unless (← getEnv).contains name do
    if ctx.visiting.contains c then
      fail m!"`{c}` is reached again while its costed value is derived (mutual recursion)"
    try
      deriveHatValue { suffix := ctx.suffix, visiting := ctx.visiting.insert c } c
    catch ex =>
      throwError m!"derive_timed: while deriving the costed value of the recursive data \
        function `{c}`:\n{ex.toMessageData}"
  return mkConst name f.constLevels!

/-- The arguments of the costed value of the data function `f` at the arguments `args` of a
call, by the binder kinds of `f` (`withBinders`): data as it is, data holding functions as its
costed value (`tv`), a function followed by the cost companion of its costed closure. -/
partial def hatArgs (ctx : Ctx) (f : Expr) (args : Array Expr) : TermElabM (Array Expr) := do
  let kinds ← argKinds f args
  let mut out := #[]
  for i in [0:args.size] do
    let a := args[i]!
    match kinds[i]!.1 with
    | .static | .data => out := out.push a
    | .hat => out := out.push (← tv ctx a).2
    | .fn =>
      let comp ← if (← hatTy? (← inferType a)).isSome then
          projE false (← tv ctx a).2
        else companionOf ctx a
      out := out.push a |>.push comp
    | .tree | .treeFn => fail m!"the data function `{f}` takes the tree `{a}`"
  return out

/-- Derive and add the costed value `c.timed` of the recursive data function `c` whose result
type `t` holds functions, and its erasure theorem `c.erase_timed : ε (c.timed xs) = c (ε xs)`
with the projection lemmas `c.erase_timed_<i>`, one for each component of the erasure
(`epsLeaves`). The binders are those of a costed form (`withBinders`); the body is the one Lean
keeps for the equation lemmas of `c`, translated by `tv` with a recursive call standing for a
call of `c.timed`, so that `c.timed` is defined by the recursion of `c`. The erasure theorem is
proved by functional induction on `c.timed`. -/
partial def deriveHatValue (ctx : Ctx) (c : Name) : TermElabM Unit := do
  let env ← getEnv
  let some info := env.find? c | fail m!"unknown constant `{c}`"
  let name := c ++ ctx.suffix
  let eraseName := c ++ Name.mkSimple ("erase_" ++ ctx.suffix.toString)
  if env.contains name then fail m!"`{name}` already exists"
  let levels := info.levelParams.map mkLevelParam
  let value ← costValue c info
  let (hType, hValue) ← lambdaTelescope value fun xs b => do
    let rt ← inferType b
    let some hrt ← hatTy? rt | fail m!"internal: the result of `{c}` holds no function"
    for x in xs do
      if (← classify (← inferType x)) matches .tree | .treeFn then
        fail m!"the recursive data function `{c}` takes the tree `{x}`"
    withBinders { ctx with top := xs.map (·.fvarId!) } xs fun ctx bs _ => do
      withLocalDeclD `rec (← mkForallFVars bs hrt) fun recF => do
        let (_, v) ← tv { ctx with selfHat? := some (c, recF) } b
        let v := v.replaceFVars (ctx.hatSubst.map (·.1)) (ctx.hatSubst.map (·.2))
        let self ← mkLambdaFVars bs (mkAppN (mkConst name levels) bs)
        let v ← instantiateMVars (← Core.betaReduce (v.replaceFVar recF self))
        if v.hasMVar then fail m!"the costed value of `{c}` has unassigned metavariables"
        if v.containsFVar recF.fvarId! then fail m!"internal: the recursive call escaped"
        for x in xs do
          if v.containsFVar x.fvarId! && !(bs.contains x) then
            fail m!"the binder `{x}` of `{c}` occurs in the costed value"
        return (← mkForallFVars bs hrt, ← mkLambdaFVars bs v)
  addTimedDef name info.levelParams hType hValue
  -- The statement of the erasure theorem and of its projection lemmas, over the binders of the
  -- costed value bound again.
  let (eType, explicit, leaves) ← lambdaTelescope value fun xs b => do
    let rt ← inferType b
    withBinders { ctx with top := xs.map (·.fvarId!) } xs fun _ bs args => do
      let call := mkAppN (mkConst name levels) bs
      let rhs := mkAppN (mkConst c levels) args
      let eq ← mkEq (← epsE rt call) rhs
      let explicit ← bs.mapM fun b => return (← b.fvarId!.getBinderInfo).isExplicit
      let leaves ← (← epsLeaves rt call rhs).mapM fun (l, r) => do
        withLocalDeclD `z rt fun z => do
          let r' ← kabstract r rhs
          return (← mkForallFVars bs (← mkEq l (r'.instantiate1 rhs)),
            ← mkLambdaFVars bs (← mkLambdaFVars #[z] (r'.instantiate1 z)))
      return (← mkForallFVars bs eq, explicit, leaves)
  -- The erasure theorem, by functional induction on the costed value.
  let envNow ← getEnv
  let wfC := (WF.eqnInfoExt.find? envNow c).isSome
  let callees := collectTimed envNow ctx.suffix hValue name
  let simpLemmas : Array Name := (if wfC then #[] else #[name, c]) ++ callees ++
    (if hValue.getUsedConstants.contains ``ite then
      #[``CatCrypt.Tactics.DeriveTimed.boolRec_eq_ite] else #[])
  let lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    simpLemmas.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  let ids : Array (TSyntax `ident) := (Array.range explicit.size).map fun i =>
    mkIdent (Name.mkSimple s!"x{i}")
  let explicitIds := (ids.zip explicit).filterMap fun (i, e) => if e then some i else none
  let intros ← if ids.isEmpty then `(tactic| skip) else `(tactic| intro $ids*)
  let close ← `(tactic| ((try simp only [$lemmas,*, *]) <;> (try (repeat' split)) <;>
    (try simp only [$lemmas,*, *]) <;> (try rfl)))
  let tac ← if wfC then
      `(tactic| ($intros; fun_induction $(mkIdent name):ident $explicitIds* <;>
        (try unfold $(mkIdent c):ident) <;> (try unfold $(mkIdent name):ident) <;>
        (try simp (disch := assumption) only [$lemmas,*, *]) <;> $close))
    else
      `(tactic| ($intros; fun_induction $(mkIdent name):ident $explicitIds* <;> $close))
  let proof ← Term.withoutErrToSorry do
    let mv ← mkFreshExprMVar eType
    let rem ← Tactic.run mv.mvarId! (Tactic.evalTactic tac)
    unless rem.isEmpty do
      fail m!"the erasure theorem `{eraseName}` is not closed by functional induction and \
        unfolding; goals left:{indentD (MessageData.joinSep (rem.map (.ofGoal ·)) "\n")}"
    instantiateMVars mv
  if proof.hasSorry || proof.hasMVar then
    fail m!"the erasure theorem `{eraseName}` is not proved"
  addDecl (Declaration.thmDecl
    { name := eraseName, levelParams := info.levelParams, type := eType, value := proof })
  -- The projection lemmas: each component of the erasure theorem, by congruence.
  for h : i in [0:leaves.size] do
    let (ty, proj) := leaves[i]
    let pf ← forallTelescope ty fun bs _ => do
      let hb := mkAppN (mkConst eraseName levels) bs
      let p ← mkCongrArg (mkAppN proj bs).headBeta hb
      mkLambdaFVars bs (← mkExpectedTypeHint p (← instantiateForall ty bs))
    addDecl (Declaration.thmDecl
      { name := eraseName.appendAfter s!"_{i}", levelParams := info.levelParams, type := ty,
        value := pf })

/-- The cost companion of the field path `p` of a local holding functions (a simulation state
of kind `hat`, such as the state of a handler under `simulateHat`): the companion of the
costed closure that the costed value of the local holds at the field; `none` when `p` mentions
no such local or its costed value is not a costed closure. -/
partial def hatFieldCompanion? (ctx : Ctx) (p : Expr) : TermElabM (Option Expr) := do
  let isHat (id : FVarId) : Bool := match ctx.locals.get? id with
    | some { kind := .hat, .. } => true
    | _ => false
  unless p.hasAnyFVar isHat do return none
  let (_, v) ← tv ctx p
  unless (← whnfR (← inferType v)).isAppOfArity ``Prod 2 do return none
  return some (← mkAppM ``Prod.snd #[v])

/-- The pairs `(i, j)` of binders of the function `f`, among its first `n`, such that the
binder `i` is a tree whose result type is the binder `j`, a type parameter that is also the
result type of the tree after the `n` binders (a callee generic in the result type of a tree
argument and of its own result). -/
partial def genericTreeArgs (f : Expr) (n : Nat) : MetaM (Array (Nat × Nat)) := do
  forallBoundedTelescope (← inferType f) (some n) fun xs b => do
    let some Tb ← treeTy? b | return #[]
    let mut out := #[]
    for i in [0:xs.size] do
      let some Tx ← treeTy? (← inferType xs[i]!) | continue
      let r := Tx.result
      unless r.isFVar && Tb.result == r do continue
      let some j := xs.findIdx? (· == r) | continue
      out := out.push (i, j)
    return out

/-- A call of the reduction whose costed form is `target`: one plus the step cost of the
costed call plus the costs of the arguments.

A tree argument whose raw result type is a type parameter `α` of a registered callee `c`
(`genericTreeArgs`) and holds functions is passed as the costed tree, with its results costed,
and `α` is instantiated with their costed type: the call's result has the costed type of the
caller's state. The erasure theorem moves the erasure of the results inside `c` by the
naturality lemma `c.bind_ret`, recorded in `ctx.natural?`; a callee without it is refused. -/
partial def callTimed (ctx : Ctx) (e target : Expr) (args : Array Expr) (T : TreeTy) :
    TermElabM Expr := do
  let kinds ← argKinds e.getAppFn args
  let generic ← genericTreeArgs e.getAppFn args.size
  let mut out := #[]
  let mut cost := natE 0
  -- The positions in `out` of the static arguments, and the costed instances of the type
  -- parameters of the generic rule.
  let mut staticPos : Array (Nat × Nat) := #[]
  let mut instAt : Array (Nat × Expr) := #[]
  for i in [0:args.size] do
    let a := args[i]!
    let k := kinds[i]!.1
    match k with
    | .static =>
      staticPos := staticPos.push (i, out.size)
      out := out.push a
    | .data =>
      out := out.push a
      cost := add cost (← costOf ctx a)
    | .hat =>
      let (c, v) ← tv ctx a
      out := out.push v
      cost := add cost c
    | .fn =>
      out := out.push a |>.push (← companionOf ctx a)
      cost := add cost (← costOf ctx a)
    | .tree =>
      let some Ta ← treeTyH? (← inferType a)
        | fail m!"`{a}` is not a tree of a registered kind"
      let some raw ← treeTy? (← inferType a) | fail m!"`{a}` is not a tree"
      let gen? := generic.find? (·.1 == i)
      if let (some (_, j), some _) := (gen?, ← hatTy? raw.result) then
        let .const cn _ := e.getAppFn
          | fail m!"internal: the generic callee `{e.getAppFn}` is not a constant"
        let lem := cn ++ `bind_ret
        unless (← getEnv).contains lem do
          fail m!"the callee `{cn}` is generic in the result type of its tree argument `{a}`, \
            called at a result type holding functions: its costed form takes the costed \
            results, which needs the naturality lemma `{lem}`, \
            `(c X).bind (fun y => .ret (f y)) = c (X.bind fun y => .ret (f y))`"
        if let some r := ctx.natural? then
          r.modify fun ns => if ns.contains lem then ns else ns.push lem
        let p ← tr ctx a
        instAt := instAt.push (j, Ta.result)
        out := out.push (Ta.sndOf p)
        cost := add cost (Ta.fstOf p)
      else
        let p ← lowerArgE Ta raw (← tr ctx a)
        out := out.push (raw.sndOf p)
        cost := add cost (raw.fstOf p)
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
          let some Tb ← treeTyH? (← inferType b)
            | fail m!"`{b}` is not a tree of a registered kind"
          let some raw ← treeTy? (← inferType b) | fail m!"`{b}` is not a tree"
          let p ← lowerArgE Tb raw (← tr ctx b)
          return (← mkLambdaFVars ys (raw.sndOf p), ← mkLambdaFVars ys (raw.fstOf p))
        out := out.push v |>.push c
  for (j, h) in instAt do
    let some (_, pos) := staticPos.find? (·.1 == j)
      | fail m!"internal: the type parameter of the generic callee `{e.getAppFn}` is not static"
    out := out.set! pos h
  let arity ← forallTelescope (← inferType target) fun ys _ => pure ys.size
  -- The costed form of the callee takes the cost companions of field paths of its binders
  -- (`R.timed.fieldPaths`): the caller passes its companions for the same paths at the
  -- arguments of the call.
  if out.size < arity then
    if let .const tname tlvls := target then
      let fpName := tname ++ `fieldPaths
      if (← getEnv).contains fpName then
        let some fp ← unfoldDefinition? (mkAppN (mkConst fpName tlvls) args)
          | fail m!"internal: `{fpName}` does not unfold"
        let mut tup := fp.headBeta
        let mut paths := #[]
        while tup.isAppOfArity ``PProd.mk 4 do
          paths := paths.push (tup.getArg! 2)
          tup := (tup.getArg! 3).headBeta
        for p in paths do
          let p ← reduceFieldArg p
          if let some (_, cc) := ctx.fields.find? (·.1 == p) then
            out := out.push cc
          else if let some (_, cc) := ctx.fields.find? (·.1 == (← canonPath p)) then
            out := out.push cc
          else if let some cc ← hatFieldCompanion? ctx p then
            out := out.push cc
          else if ← isValueField ctx p then
            -- A field of a structure value: priced at the structure's value.
            out := out.push (← companionOf ctx p)
          else if let some r := ctx.fieldRec? then
            unless (← r.get).contains p do r.modify (·.push p)
            out := out.push (← mkFreshExprMVar (← pathCompanionType p))
          else
            fail m!"the costed form of the callee `{e.getAppFn}` takes the cost of the field \
              `{p}`, which is not a field of a binder of the caller"
  unless out.size == arity do
    fail m!"the costed form of the callee `{e.getAppFn}` takes the costs of fields of local \
      structures or instances; register its costed form at the call"
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
  -- Eta-expand to all binders of the type, through type definitions.
  let value ← lambdaTelescope body fun xs b => do
    withTypeBinders (← instantiateForall type xs) fun ys _ =>
      mkLambdaFVars (xs ++ ys) (mkAppN b ys).headBeta
  -- A distribution is not a program: a reduction valued in `PMF` has no cost structure.
  let resultPMF ← lambdaTelescope value fun _ b => do
    return (← whnfR (← inferType b)).isAppOf ``PMF
  if resultPMF then
    fail m!"no cost structure: `{c}` is valued in `PMF`, a distribution without a program; \
      write it as an oracle tree or a computation tree (`SPComp`) to derive its time"
  -- A tree binder whose results hold functions: its results are lifted to costed closures.
  let binderHat ← lambdaTelescope value fun xs _ => xs.anyM fun x => do
    forallTelescope (← whnfR (← inferType x)) fun _ b => do
      match ← treeTy? b with
      | some T => return (← hatTy? T.result).isSome
      | none => return false
  -- The tree of a field `f` of a structure-valued reduction `R` (named `R.f.tree`) has the
  -- plain interface that the costed mirror of the structure takes.
  let fieldTree : TermElabM Bool :=
    match c with
    | .str (.str P f) "tree" =>
      match env.find? P with
      | some pinfo => forallTelescope pinfo.type fun _ r => do
          match (← whnfR r).getAppFn with
          | .const S _ =>
            pure (isStructure env S && (getStructureFields env S).contains (Name.mkSimple f))
          | _ => pure false
      | none => pure false
    | _ => pure false
  let plain ← if ctx.plain then pure true else fieldTree
  let unfoldedRef ← IO.mkRef (#[] : Array Name)
  let naturalRef ← IO.mkRef (#[] : Array Name)
  let ctx := { ctx with plain, unfolded? := some unfoldedRef, natural? := some naturalRef }
  -- A plain interface around data holding functions: the erasure lemmas of costed closures.
  let plainHat ← if !plain then pure false else lambdaTelescope value fun xs b => do
    if ← xs.anyM fun x => do return (← hatTy? (← inferType x)).isSome then return true
    let some rawT ← treeTy? (← inferType b) | return false
    return (← hatTy? rawT.result).isSome
  let (tType, tValue, eType, nBinders, hatted, dataHat, fp?) ←
      lambdaTelescope value fun xs b => do
    let some T ← treeTyH? (← inferType b)
      | fail m!"the result of `{c}` is not a tree of a registered kind"
    let some rawT ← treeTy? (← inferType b) | fail m!"internal: the result of `{c}`"
    -- The tree type of the costed form: the plain one for the plain interface.
    let To := if plain then rawT else T
    let ctx := { ctx with top := xs.map (·.fvarId!) }
    -- The field paths applied in the body, and those reached through unfolded definitions,
    -- recorded by a first pass.
    let direct ← fieldPrefixes b
    let reached ← withBinders ctx xs fun ctx bs _ => do
      let r ← IO.mkRef (#[] : Array Expr)
      withLocalDeclD `rec (← mkForallFVars bs T.pairType) fun recF => do
        -- A failed first pass leaves no declarations behind: a callee whose costed form was
        -- added before its erasure theorem failed is derived again, and fails, in the second.
        let s ← saveState
        try discard <| tr { ctx with self? := some (c, recF), fieldRec? := some r } b
        catch _ => s.restore
      r.get
    let cands := reached.foldl (fun acc p => if acc.contains p then acc else acc.push p) direct
    -- Methods of an abstract structure (a local instance) cost one unit: no companion.
    let cands ← cands.filterM fun p => do
      let .const pc _ := p.getAppFn | return true
      let some pinfo ← getProjectionFnInfo? pc | return true
      unless pinfo.fromClass && isUnitMethod pc do return true
      let some inst := p.getAppArgs[pinfo.numParams]? | return true
      return !(← builtFromLocalInstance inst)
    withBinders ctx xs fun ctx bs args => do
      withFieldCosts cands fun fcs => do
        -- The costed form with the cost companions of the fields `fs` after the binders `bs`;
        -- a recursive call passes the same companions.
        let build (fs : Array (Expr × Expr)) : TermElabM (Expr × Expr × Expr) := do
          let recType ← mkForallFVars bs To.pairType
          withLocalDeclD `rec recType fun recF => do
            let ctx := { ctx with self? := some (c, recF), fields := fs }
            let p ← tr ctx b
            let p := p.replaceFVars (ctx.hatSubst.map (·.1)) (ctx.hatSubst.map (·.2))
            let p ← if plain then lowerArgE T rawT p else pure p
            let cs := fs.map (·.2)
            let p ← if cs.isEmpty then pure (p.replaceFVar recF (mkConst timedName levels))
              else
                let self ← mkLambdaFVars bs (mkAppN (mkConst timedName levels) (bs ++ cs))
                Core.betaReduce (p.replaceFVar recF self)
            if p.containsFVar recF.fvarId! then fail m!"internal: the recursive call escaped"
            return (← mkForallFVars (bs ++ cs) To.pairType, ← mkLambdaFVars (bs ++ cs) p, p)
        -- Only the fields priced by the translation receive a cost companion.
        let used ← if fcs.isEmpty then pure #[] else do
          let (_, _, v) ← build fcs
          pure (fcs.filter fun (_, cc) => v.containsFVar cc.fvarId!)
        if recursive && !used.isEmpty then
          let fixed := (List.range xs.size).filter fun i =>
            used.any fun (p, _) => p.containsFVar xs[i]!.fvarId!
          let need := fixed.foldl (fun m i => max m (i + 1)) 0
          let bad := b.find? fun s => s.isAppOf c && s.getAppNumArgs ≥ need &&
            fixed.any fun i => s.getArg! i != xs[i]!
          if let some s := bad then
            fail m!"the recursive call `{s}` changes a structure or instance whose applied \
              fields are priced by cost companions"
        let (tType, tValue, _) ← build used
        let bs := bs ++ used.map (·.2)
        for x in xs do
          if tValue.containsFVar x.fvarId! && !(bs.contains x) then
            fail m!"the binder `{x}` of `{c}` occurs in a type of the costed form"
        let call := mkAppN (mkConst timedName levels) bs
        let lhs := To.eraseE (To.sndOf call)
        -- A result holding functions: the erased costed tree followed by `ε`.
        let hatted := !plain && (← hatTy? rawT.result).isSome
        let lhs ← if !hatted then pure lhs else do
          let lam ← withLocalDeclD `y T.result fun y => do
            let r := mkAppN (mkConst T.kind.nodes[0]!.src) (rawT.params.push
              (← epsE rawT.result y))
            mkLambdaFVars #[y] r
          mkAppM (T.kind.tree ++ `bind) #[lhs, lam]
        let rhs := mkAppN (mkConst c levels) args
        let eType ← mkForallFVars bs (← mkEq lhs rhs)
        let explicit ← bs.mapM fun b => return (← b.fvarId!.getBinderInfo).isExplicit
        -- The positions among the binders of the costed form of the explicit binders of `c`,
        -- when each is kept as it is: the targets of a functional induction on `c`.
        let mut srcPos : Option (Array Nat) := some #[]
        for x in xs, a in args do
          if (← x.fvarId!.getBinderInfo).isExplicit then
            srcPos := match srcPos, bs.idxOf? a with
              | some ps, some i => some (ps.push i)
              | _, _ => none
        let explicit := (explicit, srcPos)
        -- The field paths whose cost companions the costed form takes, as a function of the
        -- binders of `c`: a caller passes its companions for them (`callTimed`).
        let fp? ← if used.isEmpty then pure none else do
          let mut tup : Expr := mkConst ``PUnit.unit [Level.one]
          for (p, _) in used.reverse do
            tup ← mkAppM ``PProd.mk #[p, tup]
          pure (some (← mkLambdaFVars xs tup))
        -- A data path with a costed value: its costed closures flow through the trees.
        let dataHat ← used.anyM fun (p, _) => isDataPath p
        return (tType, tValue, eType, explicit, hatted, dataHat, fp?)
  addTimedDef timedName info.levelParams tType tValue
  if let some fp := fp? then
    addTimedDef (timedName ++ `fieldPaths) info.levelParams (← inferType fp) fp
  -- The erasure theorem.
  let callees := collectTimed (← getEnv) ctx.suffix tValue timedName
  -- The erasure lemmas of the tree kinds whose costed trees occur in the costed form.
  let used := tType.getUsedConstants ++ tValue.getUsedConstants
  let kindLemmas := (treeKinds.filter fun k => used.contains k.timed).flatMap (·.eraseLemmas)
  -- The naturality lemmas `c.bind_ret` of registered callees called at a costed instance of
  -- their type parameter (`callTimed`), oriented left to right: the erasure of the results
  -- moves inside the callee, onto the erasure theorem of its tree argument.
  let naturalLemmas ← naturalRef.get
  -- A costed form by recursion over an oracle tree has a case analysis as its only equation,
  -- which `fun_induction` unfolds; as a simp lemma it would loop.
  let treeRec := tValue.getUsedConstants.contains ``CatCrypt.Crypto.OracleAdv.Timed.casesOn
  -- Costed closures in a result or in a simulation state: the lemmas that push `ε` to the
  -- leaves and the erasure of a simulation with a costed state.
  let hatLemmas : Array Name :=
    if hatted || binderHat || plainHat || dataHat ||
        used.contains ``CatCrypt.Crypto.OracleAdv.Timed.simulateHat ||
        callees.any (fun n => n.toString.endsWith "_bind") || !naturalLemmas.isEmpty then
      (treeKinds.filter fun k => used.contains k.timed).flatMap (·.hatLemmas)
    else #[]
  -- A definition by well-founded recursion has an unconditional equation, which loops as a
  -- simp lemma: it is unfolded once by `unfold`, and `fun_induction` unfolds its costed form.
  let envNow ← getEnv
  let wf (n : Name) : Bool := (WF.eqnInfoExt.find? envNow n).isSome
  let wfC := wf c
  -- A `match` in a tree position under a binder (a continuation `fun o => match o with …`),
  -- where `split` does not reach: the erasure lemma of its matcher.
  let mut matchLemmas : Array Name := #[]
  for m in tValue.getUsedConstants.filter (isMatcherCore envNow ·) do
    for k in treeKinds.filter fun k => used.contains k.timed do
      if let some n ← matchEraseLemma k m then matchLemmas := matchLemmas.push n
  let unfoldedDefs := (← unfoldedRef.get).filter (fun n => n != c)
  let simpLemmas : Array Name :=
    ((if treeRec then #[c] else #[timedName, c]).filter (!wf ·)) ++ kindLemmas ++ hatLemmas ++
      matchLemmas ++ callees ++ naturalLemmas ++ unfoldedDefs ++
      (if used.contains ``ite then #[``CatCrypt.Tactics.DeriveTimed.boolRec_eq_ite] else #[]) ++
      -- A dispatch on an optional value (`optionDispatch?`): the source keeps `Option.elim`,
      -- which the case split of the costed match reduces at a constructor.
      (if used.any (·.getPrefix == ``optionDispatch) then
        #[``Option.elim_none, ``Option.elim_some, ``Option.map_none, ``Option.map_some]
      else #[])
  let (nBinders, srcPos) := nBinders
  let ids : Array (TSyntax `ident) := (Array.range nBinders.size).map fun i =>
    mkIdent (Name.mkSimple s!"x{i}")
  let explicitIds := (ids.zip nBinders).filterMap fun (i, e) => if e then some i else none
  let srcIds? : Option (Array (TSyntax `ident)) := srcPos.map (·.filterMap (ids[·]?))
  -- The functional induction on the source `c`: at the binders of the costed form that are
  -- binders of `c`, or, when an argument of `c` is the erasure of a costed binder (a tree or a
  -- function into trees, `fun x => (k x).erase`), at the application of `c` in the goal, the
  -- right side `c (ε xs)` of the erasure theorem.
  let srcInd : TSyntax `tactic ← match srcIds? with
    | some srcIds => `(tactic| fun_induction $(mkIdent c):ident $srcIds*)
    | none => `(tactic| fun_induction $(mkIdent c):ident)
  let lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    simpLemmas.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  -- The side conditions of `erase_simulateHat_bind` are equations under binders, discharged
  -- by the same lemmas. `simp` with a discharger traverses a shared costed value once per
  -- occurrence, so a non-recursive costed form is closed first without the discharger (then by
  -- the `if` closer below), and with it only when goals remain.
  let mkClose (lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) (disch : Bool) :
      TermElabM (TSyntax `tactic) :=
    if hatLemmas.isEmpty || !disch then
      `(tactic| ((try simp only [$lemmas,*, *]) <;> (try (repeat' split)) <;>
        (try simp only [$lemmas,*, *]) <;> (try rfl)))
    else
      `(tactic| ((try simp (disch := (intros; simp only [$lemmas,*])) only [$lemmas,*, *]) <;>
        (try (repeat' split)) <;>
        (try simp (disch := (intros; simp only [$lemmas,*])) only [$lemmas,*, *]) <;>
        (try rfl)))
  let close ← mkClose lemmas recursive
  let closeDisch ← mkClose lemmas true
  -- A callee whose body is a match (an auxiliary definition `B.tree.match_i` of
  -- `derive_reduction`) called at a discriminant built from a constructor, where its erasure
  -- theorem does not close the goal: the callee and its costed form are unfolded, the
  -- discriminants are reduced by the lemmas of `Sum.map` and `Sum.elim` at a constructor, and
  -- `simp` reduces both matches at the constructor. In a `module` file `rfl` does not unfold the
  -- matcher of an imported definition, so that the two matches are not reduced by `rfl` alone.
  let mut matchDefs : Array Name := #[]
  for n in tValue.getUsedConstants do
    let .str p s := n | continue
    unless n != timedName && s == ctx.suffix.toString && !matchDefs.contains p do continue
    let some (.defnInfo dv) := envNow.find? p | continue
    let headed ← lambdaTelescope dv.value fun _ b =>
      pure (isMatcherCore envNow b.getAppFn.constName)
    if headed then matchDefs := matchDefs ++ #[p, n]
  let closeMatch? ← if matchDefs.isEmpty then pure none else do
    let extra := matchDefs ++ #[``Sum.map_inl, ``Sum.map_inr, ``Sum.elim_inl, ``Sum.elim_inr,
      ``Option.map_some, ``Option.map_none, ``Option.elim_some, ``Option.elim_none]
    let more : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
      extra.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
    pure (some (← mkClose (lemmas ++ more) true))
  -- `intro` without names introduces one binder: a reduction without binders introduces none.
  let intros ← if ids.isEmpty then `(tactic| skip) else `(tactic| intro $ids*)
  let tac ← if recursive && wfC then
      -- The induction hypotheses of a recursion through `if` are conditional on the case's
      -- hypothesis, discharged by `assumption`.
      `(tactic| ($intros; fun_induction $(mkIdent timedName):ident $explicitIds* <;>
        (try unfold $(mkIdent c):ident) <;>
        (try simp (disch := assumption) only [$lemmas,*, *]) <;> $close))
    else if recursive then
      -- A costed form that carries companions through a dependent match has no functional
      -- induction theorem of its own (Lean's `FunInd` does not reduce the recursor applied
      -- to the carried companions); it has the recursion of `c`, whose functional induction
      -- generalizes the companions in the induction hypotheses.
      `(tactic| ($intros; first
        | (fun_induction $(mkIdent timedName):ident $explicitIds* <;> $close)
        | ($srcInd <;> $close)))
    else if treeRec then
      `(tactic| ($intros; $close))
    else
      -- A costed form whose body is a match on a binder has its equations split by case:
      -- `unfold` rewrites it at a variable.
      `(tactic| ($intros; (try unfold $(mkIdent timedName):ident); $close))
  -- An `if` in a continuation between costed values whose erasure the other side reads through
  -- functions applied to the `if` (`(if a then s.corrupt u else s).isCorrupted u`): the
  -- projections are pushed through the `if` (`fst_ite`, `snd_ite`) before any
  -- case split, both sides are decomposed by congruence under the binders of the continuations
  -- (`congr!`), and the `if`s, now on variables, are split by their conditions.
  let iteNames := #[``CatCrypt.Tactics.DeriveTimed.fst_ite,
    ``CatCrypt.Tactics.DeriveTimed.snd_ite].filter (!hatLemmas.contains ·)
  let iteLemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    iteNames.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  let allIte := lemmas ++ iteLemmas
  let closeIte ← `(tactic| ((try simp only [$allIte,*, *]) <;> (try congr!) <;>
    (try split_ifs) <;> (try rfl)))
  let tacIte? : Option (TSyntax `tactic) ← if recursive || treeRec then pure none else
    some <$> `(tactic| ($intros; (try unfold $(mkIdent timedName):ident); $closeIte))
  -- The closer with the discharger, for a non-recursive costed form left open by the others.
  let tacDisch? : Option (TSyntax `tactic) ← if recursive || hatLemmas.isEmpty then pure none
    else if treeRec then some <$> `(tactic| ($intros; $closeDisch))
    else some <$> `(tactic| ($intros; (try unfold $(mkIdent timedName):ident); $closeDisch))
  -- A bind of an `if` or a match under a binder (an `if` under the binder of a `query` node
  -- whose branches rebuild a state holding functions, followed by the erasure `ε` of the
  -- result): the bind lemmas of `if`, dependent `if` and the matchers of both sides push the
  -- bind into the branches. The stage runs without the discharger, then with it.
  let usedKinds := treeKinds.filter fun k => used.contains k.timed
  let mut bindNames : Array Name := #[]
  for k in usedKinds do
    if k.tree == ``CatCrypt.Crypto.OracleAdv then
      bindNames := bindNames ++ #[``CatCrypt.Crypto.OracleAdv.ite_bind,
        ``CatCrypt.Crypto.OracleAdv.dite_bind]
    if k.tree == ``CatCrypt.Core.SPTree then
      bindNames := bindNames ++ #[``CatCrypt.Core.SPTree.ite_bind,
        ``CatCrypt.Core.SPTree.dite_bind]
  let bodyConsts := match info with
    | .defnInfo dv => dv.value.getUsedConstants
    | _ => #[]
  for m in (tValue.getUsedConstants ++ bodyConsts).filter (isMatcherCore envNow ·) do
    for k in usedKinds do
      if let some n ← matchBindLemma k m then
        unless bindNames.contains n do bindNames := bindNames.push n
  let bindLemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    bindNames.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  let allBind := allIte ++ bindLemmas
  let closeBind ← `(tactic| ((try simp only [$allBind,*, *]) <;> (try (repeat' split)) <;>
    (try split_ifs) <;> (try simp only [$allBind,*, *]) <;> (try rfl)))
  -- With the discharger, the erasure theorems `R.erase_timed_bind` of callees are left out when
  -- `R.erase_timed` is present: in a side condition of `erase_simulateHat_bind` the handler's
  -- result is followed by `ε`, which `R.erase_timed` matches, while `R.erase_timed_bind` leaves
  -- the round trip `ι ∘ ε` of the state, a structure eta-expanded field by field.
  let plainNames := simpLemmas.filter fun n =>
    !(callees.contains n && n.toString.endsWith "_bind" &&
      callees.any (·.toString ++ "_bind" == n.toString))
  let plainLemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    plainNames.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  let allPlain := plainLemmas ++ iteLemmas ++ bindLemmas
  let closeBindDisch ← `(tactic|
    ((try simp (disch := (intros; simp only [$allPlain,*])) only [$allPlain,*, *]) <;>
      (try (repeat' split)) <;> (try split_ifs) <;>
      (try simp (disch := (intros; simp only [$allPlain,*])) only [$allPlain,*, *]) <;>
      (try rfl)))
  let tacBind? : Option (TSyntax `tactic) ← if recursive || bindNames.isEmpty then pure none
    else if treeRec then some <$> `(tactic| ($intros; $closeBind))
    else some <$> `(tactic| ($intros; (try unfold $(mkIdent timedName):ident); $closeBind))
  let tacBindDisch? : Option (TSyntax `tactic) ←
    if recursive || bindNames.isEmpty || hatLemmas.isEmpty then pure none
    else if treeRec then some <$> `(tactic| ($intros; $closeBindDisch))
    else some <$> `(tactic| ($intros; (try unfold $(mkIdent timedName):ident); $closeBindDisch))
  let proof ← Term.withoutErrToSorry do
    let mv ← mkFreshExprMVar eType
    let rem ← if recursive && hatted then do
        -- A recursion whose result holds functions: the induction hypothesis
        -- `(R.timed ys).2.erase.bind (fun y => ret (ε y)) = R ys` is used from right to left,
        -- so that the recursive call of `R` becomes the erased costed call followed by `ε`,
        -- which the continuation's lemmas (`bind_assoc`, `bind_ret`) absorb.
        let s ← saveState
        let byTimed ← try
            some <$> Tactic.run mv.mvarId! (Tactic.evalTactic (← `(tactic|
              ($intros; fun_induction $(mkIdent timedName):ident $explicitIds* <;>
                (try unfold $(mkIdent c):ident) <;>
                (try simp only [$lemmas,*]) <;> (try (repeat' split))))))
          catch _ =>
            s.restore
            pure none
        -- A costed form that carries companions through a dependent match: functional induction
        -- on the source `c`, whose hypotheses quantify the companions (`instRecHyps`).
        let (gs, bySource) ← match byTimed with
          | some gs => pure (gs, false)
          | none => do
            let gs ← Tactic.run mv.mvarId! (Tactic.evalTactic (← `(tactic|
              ($intros; $srcInd <;>
                (try simp only [$lemmas,*]) <;> (try (repeat' split))))))
            pure (gs, true)
        let mut rem := []
        for g in gs do
          let g ← if bySource then instRecHyps timedName g else pure g
          let g ← rewriteRecHyps c g
          rem := rem ++ (← Tactic.run g (Tactic.evalTactic close))
        pure rem
      else Tactic.run mv.mvarId! (Tactic.evalTactic tac)
    let rem ← match closeMatch? with
      | some closeMatch => rem.flatMapM fun g => Tactic.run g (Tactic.evalTactic closeMatch)
      | none => pure rem
    let (mv, rem) ← match rem, tacIte? with
      | _ :: _, some tacIte => do
        let mv' ← mkFreshExprMVar eType
        let rem' ← Tactic.run mv'.mvarId! (Tactic.evalTactic tacIte)
        pure (if rem'.isEmpty then (mv', rem') else (mv, rem))
      | _, _ => pure (mv, rem)
    let (mv, rem) ← match rem, tacBind? with
      | _ :: _, some tacBind => do
        let mv' ← mkFreshExprMVar eType
        let rem' ← Tactic.run mv'.mvarId! (Tactic.evalTactic tacBind)
        pure (if rem'.isEmpty then (mv', rem') else (mv, rem))
      | _, _ => pure (mv, rem)
    let (mv, rem) ← match rem, tacBindDisch? with
      | _ :: _, some tacBindDisch => do
        let mv' ← mkFreshExprMVar eType
        let rem' ← Tactic.run mv'.mvarId! (Tactic.evalTactic tacBindDisch)
        pure (if rem'.isEmpty then (mv', rem') else (mv, rem))
      | _, _ => pure (mv, rem)
    let (mv, rem) ← match rem, tacDisch? with
      | _ :: _, some tacDisch => do
        let mv' ← mkFreshExprMVar eType
        let rem' ← Tactic.run mv'.mvarId! (Tactic.evalTactic tacDisch)
        let rem' ← match closeMatch? with
          | some closeMatch => rem'.flatMapM fun g => Tactic.run g (Tactic.evalTactic closeMatch)
          | none => pure rem'
        pure (if rem'.isEmpty then (mv', rem') else (mv, rem))
      | _, _ => pure (mv, rem)
    -- A goal left with a structure rebuilt from the projections of a state, one of which a case
    -- hypothesis rewrote (`{ cur := k + 1, env := s.cfg.env } = s.cfg` with `s.cfg.cur = k + 1`).
    let rem ← rem.filterM fun g => return !(← closeByCaseHypsRev g)
    unless rem.isEmpty do
      fail m!"the erasure theorem `{eraseName}` is not closed by unfolding and the erasure \
        lemmas; goals left:{indentD (MessageData.joinSep (rem.map (.ofGoal ·)) "\n")}"
    instantiateMVars mv
  if proof.hasSorry || proof.hasMVar then
    fail m!"the erasure theorem `{eraseName}` is not proved"
  let thm : TheoremVal :=
    { name := eraseName, levelParams := info.levelParams, type := eType, value := proof }
  addDecl (Declaration.thmDecl thm)
  -- A result holding functions: the erasure theorem for the costed tree followed by a
  -- continuation that depends on a result only through its erasure.
  if hatted then
    let levels := info.levelParams.map mkLevelParam
    let (bType, bValue) ← forallTelescope eType fun bs eq => do
      let some (_, lhs, rhs) := eq.eq? | fail m!"internal: `{eraseName}` is not an equation"
      let some T ← treeTy? (← inferType rhs) | fail m!"internal: the result of `{c}`"
      let E := lhs.getArg! (lhs.getAppNumArgs - 2)
      let εF ← epsFun T.result
      let ιF ← iotaFun T.result
      let some ht ← hatTy? T.result | fail m!"internal: the result of `{c}`"
      withLocalDeclD `β (mkSort Level.one) fun β => do
        let treeOf (a : Expr) : Expr := mkAppN (mkConst T.kind.tree)
          (T.params.set! (T.params.size - 1) a)
        withLocalDeclD `k (← mkArrow ht (treeOf β)) fun k => do
          let hkTy ← withLocalDeclD `y ht fun y => do
            mkForallFVars #[y] (← mkEq (mkApp k y)
              (mkApp k (mkApp ιF (mkApp εF y)).headBeta.headBeta))
          withLocalDeclD `hk hkTy fun hk => do
            let bindHat := if T.kind.tree == ``CatCrypt.Core.SPTree then
                ``CatCrypt.Core.SPTree.Timed.bind_hat
              else ``CatCrypt.Crypto.OracleAdv.Timed.bind_hat
            let pf ← mkAppM bindHat #[εF, ιF, E, rhs,
              mkAppN (mkConst eraseName levels) bs, k, hk]
            let ty ← inferType pf
            return (← mkForallFVars (bs ++ #[β, k, hk]) ty,
              ← mkLambdaFVars (bs ++ #[β, k, hk]) pf)
    let bindThm : TheoremVal :=
      { name := eraseName.appendAfter "_bind", levelParams := info.levelParams,
        type := bType, value := bValue }
    addDecl (Declaration.thmDecl bindThm)

/-- The callees of `v` with a costed form `n.suffix` other than `self`, as their erasure
theorems, with the erasure theorems `R.erase_timed_bind` of the callees whose results hold
functions. -/
partial def collectTimed (env : Environment) (suffix : Name) (v : Expr) (self : Name) :
    Array Name :=
  let eraseSuffix := Name.mkSimple ("erase_" ++ suffix.toString)
  v.getUsedConstants.foldl (init := #[]) fun acc n =>
    match n with
    | .str p s =>
      if n != self && s == suffix.toString then
        let thm := p ++ eraseSuffix
        let acc := if env.contains thm && !acc.contains thm then acc.push thm else acc
        let thmB := thm.appendAfter "_bind"
        let acc := if env.contains thmB && !acc.contains thmB then acc.push thmB else acc
        -- The projection lemmas `thm_<i>` of the costed value of a recursive data function.
        let projs := (List.range 64).map (fun i => thm.appendAfter s!"_{i}")
          |>.takeWhile env.contains
        projs.foldl (fun acc n => if acc.contains n then acc else acc.push n) acc
      else acc
    | _ => acc

/-- Add the definition `name`, settling its recursion as a `def`'s (`addTimedDefs`). -/
partial def addTimedDef (name : Name) (levelParams : List Name) (type value : Expr) :
    TermElabM Unit :=
  addTimedDefs levelParams #[(name, type, value)]

/-- Add the definitions `defs`, each a name, a type and a value, as one mutual block, settling
its recursion as a `mutual` block of `def`s'. In a `module` file the definitions are exposed,
so that importing modules unfold costed forms and costs, unless a value uses a declaration
private to the module (the matcher of a definition that is not exposed): the equation lemmas
of an exposed definition are stated in the exported environment, where that declaration is
unknown. -/
partial def addTimedDefs (levelParams : List Name) (defs : Array (Name × Expr × Expr)) :
    TermElabM Unit := do
  let name := defs[0]!.1
  let saved := (← getThe Core.State).messages
  modifyThe Core.State fun s => { s with messages := {} }
  let expose := (← getEnv).header.isModule &&
    !defs.any fun (_, _, value) => value.getUsedConstants.any isPrivateName
  let outcome ← try
      withExporting (isExporting := expose) <| addPreDefinitions ({}, {}) <|
        defs.map fun (declName, type, value) => {
          ref := .missing, kind := .def, levelParams,
          modifiers := { computeKind := .noncomputable }, declName,
          binders := .missing, type, value, termination := .none }
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

/-- Price `b` in `ctx` with each prefix of `ps` standing for a local function whose cost
companion is zero, so that each call of a listed method costs one plus its arguments. -/
partial def costWithUnits (ctx : Ctx) (ps : Array Expr) (b : Expr) : TermElabM Expr := do
  let rec go (i : Nat) (ctx : Ctx) (b : Expr) (us : Array (Expr × Expr)) : TermElabM Expr := do
    if h : i < ps.size then
      let p := ps[i]
      let t ← inferType p
      withLocalDeclD `unitMethod t fun u => do
        let zero ← forallTelescope (← whnfR t) fun ys _ => mkLambdaFVars ys (mkNatLit 0)
        let ctx := { ctx with locals := ctx.locals.insert u.fvarId! ⟨.fn, u, some zero⟩ }
        go (i + 1) ctx (b.replace fun s => if s == p then some u else none) (us.push (u, p))
    else
      let c ← costOf ctx b
      let c := us.foldl (fun c (u, p) => c.replaceFVar u p) c
      return (← Core.betaReduce c)
  go 0 ctx b #[]

/-- Derive and add the cost `c.timedCost` of the data function `c` (the command `derive_cost`
of `CatCryptCore.Tactics.DeriveCost`), charging the class methods `units` on local instances
one unit. The body priced is the one Lean keeps for the equation lemmas of `c`, in which a
recursive call is an application of `c`; it is priced by the cost being defined, so the cost
is defined by the recursion of `c`. -/
partial def deriveCostCore (units : Array Name) (c : Name) : TermElabM Unit := do
  let env ← getEnv
  let some info := env.find? c | throwError "derive_cost: unknown constant `{c}`"
  -- A member of a mutual block: the costs of the block are derived together.
  let block := mutualBlock env c
  if block.size > 1 then return ← deriveCostBlock units c block
  let costName := c ++ `timedCost
  if env.contains costName then throwError "derive_cost: `{costName}` already exists"
  let levels := info.levelParams.map mkLevelParam
  let value ← costValue c info
  let (cType, cValue) ← lambdaTelescope value fun xs b => do
    if (← treeTyH? (← inferType b)).isSome then
      throwError "derive_cost: the result of `{c}` is a tree; use `derive_timed`"
    for x in xs do
      if (← classify (← inferType x)) matches .tree | .treeFn then
        throwError "derive_cost: the binder `{x}` of `{c}` is a tree; use `derive_timed`"
    let paths ← recordFieldPaths units c xs b
    withBinders { top := xs.map (·.fvarId!) } xs fun ctx bs _ => do
      withFieldCosts paths fun fcs => do
        let cs := fcs.map (·.2)
        -- A recursive call passes the structures whose fields have cost companions unchanged.
        if !cs.isEmpty && ((Structural.eqnInfoExt.find? env c).isSome ||
            (WF.eqnInfoExt.find? env c).isSome) then
          let fixed := (List.range xs.size).filter fun i =>
            paths.any fun p => p.containsFVar xs[i]!.fvarId!
          let need := fixed.foldl (fun m i => max m (i + 1)) 0
          let bad := b.find? fun s => s.isAppOf c && s.getAppNumArgs ≥ need &&
            fixed.any fun i => s.getArg! i != xs[i]!
          if let some s := bad then
            throwError "derive_cost: the recursive call `{s}` changes a structure whose applied \
              fields are priced by cost companions"
        let cType ← mkForallFVars (bs ++ cs) (mkConst ``Nat)
        let ps ← unitPrefixes units b
        withLocalDeclD `rec (← mkForallFVars bs (mkConst ``Nat)) fun recF => do
          let cost ← costWithUnits { ctx with selfCosts := #[(c, recF)], fields := fcs } ps b
          let cost ← instantiateMVars cost
          if cost.hasMVar then
            throwError "derive_cost: the cost of `{c}` has unassigned universes"
          let self ← mkLambdaFVars bs (mkAppN (mkConst costName levels) (bs ++ cs))
          let cost ← Core.betaReduce (cost.replaceFVar recF self)
          return (cType, ← mkLambdaFVars (bs ++ cs) cost)
  addTimedDef costName info.levelParams cType cValue

/-- The members of the mutual block of the recursive function `c`, in the order of the block:
`#[c]` for a function outside a mutual block. -/
partial def mutualBlock (env : Environment) (c : Name) : Array Name :=
  let names := match Structural.eqnInfoExt.find? env c, WF.eqnInfoExt.find? env c with
    | some i, _ => i.declNames
    | _, some i => i.declNames
    | _, _ => #[]
  if names.contains c then names else #[c]

/-- Derive and add the costs `g.timedCost` of the members `g` of the mutual block `block` of the
data function `c` as one mutual definition, charging the class methods `units` on local
instances one unit. A call of a member is priced by the member's cost being defined, so the
costs are defined by the recursion of the block. Each cost takes, after the costed binders of its
member, the cost companions of the field paths of the block (`blockFieldPaths`), and a call of a
member passes the same companions. -/
partial def deriveCostBlock (units : Array Name) (c : Name) (block : Array Name) :
    TermElabM Unit := do
  let env ← getEnv
  let some cInfo := env.find? c | throwError "derive_cost: unknown constant `{c}`"
  let levels := cInfo.levelParams.map mkLevelParam
  for g in block do
    if env.contains (g ++ `timedCost) then
      throwError "derive_cost: `{g ++ `timedCost}` already exists"
  let members ← blockMembers c block
  let (shared, k) ← blockFieldPaths units c members
  let defs ← withLocalDeclsDND (members.map fun (_, _, t) => (`rec, t)) fun recFs => do
    let selfCosts := block.zip recFs
    members.mapM fun (g, value, _) => lambdaTelescope value fun xs b => do
      let pre := xs.extract 0 k
      let paths := shared.map (·.instantiateRev pre)
      for p in paths do
        try Meta.check p
        catch ex =>
          throwError "derive_cost: the field path `{p}` of the mutual block of `{c}` is not a \
            path of the binders of `{g}`:{indentD ex.toMessageData}"
      -- A call of a member passes the binders that the field paths mention unchanged.
      unless paths.isEmpty do
        let fixed := (List.range k).filter fun i =>
          paths.any fun p => p.containsFVar xs[i]!.fvarId!
        let need := fixed.foldl (fun m i => max m (i + 1)) 0
        let bad := b.find? fun s => block.any (s.isAppOf ·) && s.getAppNumArgs ≥ need &&
          fixed.any fun i => s.getArg! i != xs[i]!
        if let some s := bad then
          throwError "derive_cost: the call `{s}` in the mutual block of `{c}` changes a \
            structure whose applied fields are priced by cost companions"
      withBinders { top := xs.map (·.fvarId!) } xs fun ctx bs _ => do
        withFieldCosts paths fun fcs => do
          let cs := fcs.map (·.2)
          let cost ← costWithUnits { ctx with selfCosts, fields := fcs }
            (← unitPrefixes units b) b
          let cost ← instantiateMVars cost
          if cost.hasMVar then
            throwError "derive_cost: the cost of `{g}` has unassigned universes"
          -- Each local standing for the cost of a member is that member's cost at the same
          -- companions.
          let selfs ← (block.zip recFs).mapM fun (g', r) => do
            forallTelescope (← inferType r) fun ys _ =>
              mkLambdaFVars ys (mkAppN (mkConst (g' ++ `timedCost) levels) (ys ++ cs))
          let cost ← Core.betaReduce (cost.replaceFVars recFs selfs)
          return (g ++ `timedCost, ← mkForallFVars (bs ++ cs) (mkConst ``Nat),
            ← mkLambdaFVars (bs ++ cs) cost)
  addTimedDefs cInfo.levelParams defs

/-- The members `g` of the mutual block `block` of the data function `c`, each with the value
that `derive_cost` prices and the type of its cost without the costs of fields. -/
partial def blockMembers (c : Name) (block : Array Name) :
    TermElabM (Array (Name × Expr × Expr)) := do
  let env ← getEnv
  let some cInfo := env.find? c | throwError "derive_cost: unknown constant `{c}`"
  let mut members : Array (Name × Expr × Expr) := #[]
  for g in block do
    let some info := env.find? g
      | throwError "derive_cost: unknown constant `{g}` in the mutual block of `{c}`"
    unless info.levelParams == cInfo.levelParams do
      throwError "derive_cost: the members `{c}` and `{g}` of a mutual block have different \
        universe parameters"
    let value ← costValue g info
    let cType ← lambdaTelescope value fun xs b => do
      if (← treeTyH? (← inferType b)).isSome then
        throwError "derive_cost: the result of `{g}` is a tree; use `derive_timed`"
      for x in xs do
        if (← classify (← inferType x)) matches .tree | .treeFn then
          throwError "derive_cost: the binder `{x}` of `{g}` is a tree; use `derive_timed`"
      withBinders { top := xs.map (·.fvarId!) } xs fun _ bs _ =>
        mkForallFVars bs (mkConst ``Nat)
    members := members.push (g, value, cType)
  return members

/-- The field paths whose cost companions the costs of the members `members` of the mutual
block of `c` take: the field paths of every member, in the order in which pricing passes reach
them, each abstracted over the first `k` binders of its member, where `k` is the least number of
binders of a member; returned with `k`. A path that mentions a later binder is refused. -/
partial def blockFieldPaths (units : Array Name) (c : Name)
    (members : Array (Name × Expr × Expr)) : TermElabM (Array Expr × Nat) := do
  let k := members.foldl (fun m (_, v, _) => min m v.getNumHeadLambdas)
    (members[0]?.map (·.2.1.getNumHeadLambdas) |>.getD 0)
  withLocalDeclsDND (members.map fun (_, _, t) => (`rec, t)) fun recFs => do
    let selfCosts := (members.map (·.1)).zip recFs
    let mut shared : Array Expr := #[]
    for (g, value, _) in members do
      let ps ← lambdaTelescope value fun xs b => do
        let paths ← recordFieldPaths units g xs b selfCosts
        let pre := xs.extract 0 k
        paths.mapM fun p => do
          let a := p.abstract pre
          if xs.any fun x => a.containsFVar x.fvarId! then
            throwError "derive_cost: `{g}`, in the mutual block of `{c}`, applies the field \
              `{p}` of a binder after the first {k} binders, which all members share"
          return a
      for a in ps do
        unless shared.contains a do shared := shared.push a
    return (shared, k)

/-- The value of the data function `c` that `derive_cost` prices: the body of its equation
lemmas, eta-expanded to all binders of its type through type definitions. -/
partial def costValue (c : Name) (info : ConstantInfo) : TermElabM Expr := do
  let env ← getEnv
  let body ← match Structural.eqnInfoExt.find? env c, WF.eqnInfoExt.find? env c, info with
    | some i, _, _ => pure i.value
    | _, some i, _ => pure i.value
    | _, _, .defnInfo d => pure d.value
    | _, _, _ => throwError "derive_cost: `{c}` has no definition to price"
  lambdaTelescope body fun xs b => do
    withTypeBinders (← instantiateForall info.type xs) fun ys _ =>
      mkLambdaFVars (xs ++ ys) (mkAppN b ys).headBeta

/-- The field paths of the binders `xs` of the data function `c` with body `b` that its cost
prices, in the order in which a pricing pass reaches them: the fields whose cost companions
the derived cost `c.timedCost` takes after its binders. -/
partial def recordFieldPaths (units : Array Name) (c : Name) (xs : Array Expr) (b : Expr)
    (others : Array (Name × Expr) := #[]) : TermElabM (Array Expr) := do
  withBinders { top := xs.map (·.fvarId!) } xs fun ctx bs _ => do
    let r ← IO.mkRef (#[] : Array Expr)
    let ps ← unitPrefixes units b
    withLocalDeclD `rec (← mkForallFVars bs (mkConst ``Nat)) fun recF => do
      try
        discard <| costWithUnits
          { ctx with selfCosts := #[(c, recF)] ++ others, fieldRec? := some r } ps b
      catch _ => pure ()
    r.get

/-- The field paths whose cost companions the derived cost of the data function `c` takes,
instantiated at the arguments `args` of a call of `c` at the universe levels `lvls`. -/
partial def calleeFieldPaths (c : Name) (lvls : List Level) (args : Array Expr) :
    TermElabM (Array Expr) := do
  let some info := (← getEnv).find? c | return #[]
  -- A member of a mutual block: the field paths shared by the block.
  let block := mutualBlock (← getEnv) c
  if block.size > 1 then
    let (shared, k) ← blockFieldPaths #[] c (← blockMembers c block)
    if shared.isEmpty then return #[]
    unless k ≤ args.size do
      fail m!"the cost of `{c}` takes the costs of fields, and `{c}` is applied to \
        {args.size} of the {k} arguments that its field paths take"
    return shared.map fun a =>
      (a.instantiateLevelParams info.levelParams lvls).instantiateRev (args.extract 0 k)
  let value := (← costValue c info).instantiateLevelParams info.levelParams lvls
  lambdaTelescope value fun xs b => do
    unless xs.size == args.size do
      fail m!"the cost of `{c}` takes the costs of fields, and `{c}` is applied to \
        {args.size} of its {xs.size} arguments"
    let ps ← recordFieldPaths #[] c xs b
    return ps.map (·.replaceFVars xs args)

end

/-- `derive_timed_fn R` defines the costed form `R.timed` of the reduction `R` and proves its
erasure theorem `R.erase_timed`; `derive_timed_fn (suffix := s) R` names them `R.s` and
`R.erase_s`. -/
syntax (name := deriveTimedFnCmd) "derive_timed_fn " ("(" &"suffix" " := " ident ") ")? ident :
  command

@[command_elab deriveTimedFnCmd]
def elabDeriveTimedFn : CommandElab := fun stx => do
  -- The optional group `(suffix := s)` is a node of five children when present.
  let suffix := if stx[1].getNumArgs == 5 then stx[1][3].getId else `timed
  let id := stx[2]
  liftTermElabM do
    let c ← realizeGlobalConstNoOverloadWithInfo id
    deriveTimed { suffix } c

end CatCrypt.Tactics.DeriveTimedFn

namespace CatCrypt.Tactics.DeriveReductionFn

open Lean Elab Meta Term Command
open CatCrypt.Tactics.DeriveReduction (compile_bind_pure_of_erase sumDispatch)

/-- Fail with the reason a derivation does not go through. -/
def fail {γ : Type} (what : MessageData) : MetaM γ :=
  throwError m!"derive_reduction: {what}"

/-- The attempt `x` run with a fresh heartbeat budget: its result, or its error with the state
before it restored. A runtime exception (a heartbeat timeout, the maximal recursion depth) is an
error of the attempt; an interrupt is rethrown. -/
def attempt {α : Type} (x : TermElabM α) : TermElabM (Except Exception α) := do
  let s ← saveState
  tryCatchRuntimeEx (Except.ok <$> withCurrHeartbeats x) fun e => do
    if e.isInterrupt then throw e
    s.restore
    return .error e

/-- The constructors of `SPComp`, at which unfolding stops. -/
def spCompCtors : Array Name :=
  #[``CatCrypt.Core.SPComp.pure, ``CatCrypt.Core.SPComp.bind, ``CatCrypt.Core.SPComp.sample,
    ``CatCrypt.Core.SPComp.get, ``CatCrypt.Core.SPComp.set, ``CatCrypt.Core.SPComp.fail]

/-- The computations sampling from a sub-distribution: `liftSDistr` and `sampleFrom`. -/
def sampleDistHeads : Array Name :=
  #[``CatCrypt.Core.liftSDistr, `CatCrypt.NonUniform.sampleFrom]

/-- The constants at which `normalize` stops: the constructors of `SPComp`, the heap reset
`SPComp.initHeap`, sampling from a sub-distribution, `ite`, `dite` and `SPTree.compile`. -/
def normalizeStops : Array Name :=
  spCompCtors ++ #[``CatCrypt.Crypto.SPComp.initHeap, ``ite, ``dite,
    ``CatCrypt.Core.SPTree.compile] ++ sampleDistHeads

/-- Sampling from a sub-distribution `μ`, `liftSDistr μ` or `sampleFrom μ`
(`CatCryptCore.NonUniform.Sample`, named without importing it): the distribution `μ`. -/
def sampleDist? (e : Expr) : Option Expr :=
  if e.getAppNumArgs == 2 && sampleDistHeads.any e.isAppOf then some e.appArg! else none

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
`CatCrypt.Tactics.DeriveTimedFn.bindArgsShared`: the non-atomic first-order data arguments are
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
  some <$> CatCrypt.Tactics.DeriveTimedFn.bindArgsShared v e.getAppArgs

/-- The application `f a₁ … aₙ` with the arguments pushed under the `let`s at the head of `f`:
`(let x := v; b) a ↦ let x := v; b a`, and the head of the innermost body beta-reduced. The
arguments are closed terms, so that no bound variable is captured. -/
partial def pushAppUnderLets (f : Expr) (args : Array Expr) : Expr :=
  match f with
  | .letE n t v b nd => .letE n t v (pushAppUnderLets b args) nd
  | .mdata _ b => pushAppUnderLets b args
  | f => (mkAppN f args).headBeta

/-- A dispatch on a sum, `Sum.elim f g x a₁ … aₙ`, `Sum.casesOn x f g a₁ … aₙ` or
`Sum.rec f g x a₁ … aₙ`, as a match: when `whnf` brings `x` to a constructor, the alternative
of that constructor at its field, applied to `a₁ … aₙ`; otherwise, when `n = 0`, the matcher
of `sumDispatch` on `x`. `none` when `e` is not such a dispatch, and on a scrutinee that is not
a constructor when `n > 0`: the match with the arguments passed into its alternatives equals
the dispatch only propositionally. -/
def sumDispatch? (e : Expr) : MetaM (Option Expr) := do
  let args := e.getAppArgs
  let some c := e.getAppFn.constName? | return none
  unless args.size ≥ 6 do return none
  -- the motive, the scrutinee and the two alternatives
  let (motive?, x, f, g) ←
    if c == ``Sum.elim then pure (none, args[5]!, args[3]!, args[4]!)
    else if c == ``Sum.casesOn then pure (some args[2]!, args[3]!, args[4]!, args[5]!)
    else if c == ``Sum.rec then pure (some args[2]!, args[5]!, args[3]!, args[4]!)
    else return none
  let rest := args.extract 6 args.size
  let x' ← whnf x
  if x'.isAppOfArity ``Sum.inl 3 then
    return some (mkAppN (mkApp f x'.appArg!).headBeta rest).headBeta
  if x'.isAppOfArity ``Sum.inr 3 then
    return some (mkAppN (mkApp g x'.appArg!).headBeta rest).headBeta
  -- A dispatch applied to further arguments is not definitionally the match with the
  -- arguments passed into its alternatives; it is left to the unfolding.
  unless rest.isEmpty do return none
  let motive ← match motive? with
    | some m => pure m
    | none =>
      let ty ← inferType e
      withLocalDeclD `x (← inferType x) fun y => mkLambdaFVars #[y] ty
  let d ← mkAppM ``sumDispatch #[motive, x, f, g]
  let some d' ← unfoldDefinition? d | return none
  return some d'.headBeta

/-- Bring the computation `e` to a head: a constructor of `SPComp`, `ite`, `dite`, a matcher,
`SPTree.compile`, a call of a recursive definition, a local or a `let`, or a stuck term. A
definition is unfolded by `unfoldShared?`, so that its arguments stay `let`s priced once. A
`let` chain applied to arguments (the body of a definition that returns a function after its
`let`s) is brought to a `let` by `pushAppUnderLets`. -/
partial def normalize (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if let .const c _ := e.getAppFn then
    if isRecursive (← getEnv) c then return e
  let e ← withConfig (fun c => { c with zeta := false }) <| whnfR e
  if e.isLet then return e
  if e.getAppFn.consumeMData.isLet && !e.hasLooseBVars then
    return ← normalize (pushAppUnderLets e.getAppFn e.getAppArgs)
  match e.getAppFn with
  | .const c _ =>
    if normalizeStops.contains c then return e
    if ← isMatcher c then return e
    if isRecursive (← getEnv) c then return e
    if monadOps.contains c then
      let e' ← withTransparency .instances (whnf e)
      if e' == e then return e
      return ← normalize e'
    if let some e' ← sumDispatch? e then return ← normalize e'
    if let some e' ← CatCrypt.Tactics.DeriveTimedFn.optionDispatch? e then
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
of a tree of a kind of `CatCrypt.Tactics.DeriveTimedFn.treeKinds` or of a function into such
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
  /-- The types of the binders and of the result, with their reducible definitions unfolded:
  a field path occurring in one of them is not abstracted. -/
  typePos : Array Expr := #[]
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
    if (← CatCrypt.Tactics.DeriveTimedFn.treeTy? b).isSome then return false
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

/-- The primitive projection `.proj S i s` of a projection-function application
`S.f ps s`, the form a field takes in an unfolded definition; `F` itself otherwise. -/
def projForm (env : Environment) (F : Expr) : Expr := Id.run do
  let .const c _ := F.getAppFn | return F
  let some info := env.getProjectionFnInfo? c | return F
  let some s := F.getAppArgs[info.numParams]? | return F
  unless F.getAppNumArgs == info.numParams + 1 do return F
  return .proj info.ctorName.getPrefix info.i s

/-- Replace each data-function field of `e` by its binder (second pass), or record it (first
pass). A data definition applied to a structure binder is unfolded first, by `unfoldShared?`,
when its body applies a data-function primitive found by the first pass (so that the field has
one binder and one cost companion), and with `ctx.unfold` always, so that the fields used in
its body are found. The search `mentionsKey` runs only when there are such primitives. The
parameters `ps` of a field `S.f ps s` of a binder are the arguments of the type of `s` and are
kept as they are (`keepParams`): a field abstracted in them would give `S.f` a structure of
another type than that of `s`. -/
partial def abstractData (ctx : RCtx) (e : Expr) : MetaM Expr := do
  let keys := (ctx.prims.filter (·.data)).map (·.key)
  let neg ← IO.mkRef ({} : Std.HashMap Expr Nat)
  -- The field application `x = S.f ps s a₁ … aₙ` with `s` and the `aᵢ` abstracted and the
  -- parameters `ps` unchanged.
  let keepParams (x : Expr) : MetaM TransformStep := do
    let f := x.getAppFn
    let .const fc _ := f | return .continue
    let some info := (← getEnv).getProjectionFnInfo? fc | return .continue
    let xs := x.getAppArgs
    unless info.numParams < xs.size do return .continue
    let rest ← (xs.extract info.numParams xs.size).mapM (abstractData ctx)
    return .done (mkAppN f (xs.extract 0 info.numParams ++ rest))
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
    unless ← isDataFnType (← inferType F) do return ← keepParams x
    -- A method of an algebraic operation class (or of `CryptoWord`) is one call of an
    -- abstract interface, priced at one unit by `derive_timed`: not a primitive.
    if let .const fc _ := F.getAppFn then
      if let some finfo := (← getEnv).getProjectionFnInfo? fc then
        if finfo.fromClass && CatCrypt.Tactics.DeriveTimedFn.isUnitMethod fc then
          return .continue
    -- A field path in the type of a binder or of the result (`P.relation` in
    -- `{xw // P.relation xw.1 xw.2 = true}`) stays a projection of its structure binder.
    let Fp := projForm (← getEnv) F
    if ctx.typePos.any fun t => (t.find? fun s => s == F || s == Fp).isSome then
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
      return (← CatCrypt.Tactics.DeriveTimedFn.treeTy? b).isSome
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
  CatCrypt.Tactics.DeriveTimedFn.addTimedDef name lps type value
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

/-- The types of the binders `xs` and the type `α`, with their reducible definitions unfolded
(`Groth16Rel P` to `{xw // P.relation xw.1 xw.2 = true}`): the type positions in which a field
path of the binders stays a projection. -/
def typePositions (xs : Array Expr) (α : Expr) : MetaM (Array Expr) := do
  let env ← getEnv
  let red (n : Name) : Bool := getReducibilityStatusCore env n == .reducible
  let tys := (← xs.mapM inferType).push α
  tys.mapM fun t => do deltaExpand (← instantiateMVars t) red

/-- Whether `v` is a field path of the binders `top`: a binder of `top`, or a structure
projection, applied to exactly its parameters and the structure, of a field path. A function
of a structure field applied to arguments (`deps.sha256 x`) is not a field path. -/
partial def isTopPath (env : Environment) (top : Array FVarId) (v : Expr) : Bool :=
  match v.consumeMData with
  | .fvar id => top.contains id
  | .proj _ _ s => isTopPath env top s
  | s =>
    match s.getAppFn with
    | .const c _ =>
      match env.getProjectionFnInfo? c with
      | some info => s.getAppNumArgs == info.numParams + 1 && isTopPath env top s.appArg!
      | none => false
    | _ => false

/-- Whether the type of one of the binders `xs` mentions the binder `x`. A computation binder
that the type of another binder depends on (`dsecret` in `hs : SPComp.IsPure dsecret` and in
`A : CPA_Adversary (M.params W dsecret hs)`) is a parameter of the reduction, not an
adversary. -/
def typeDependsOn (xs : Array Expr) (x : Expr) : MetaM Bool :=
  xs.anyM fun y => do
    if y == x then return false
    return (← instantiateMVars (← inferType y)).containsFVar x.fvarId!

/-- Whether the binder `x` of the binders `xs` is taken as an adversary: one of the binders
named `advNames`, or, when it is empty, a binder that the type of no other binder mentions. -/
def isAdvBinder (xs : Array Expr) (advNames : Array Name) (x : Expr) : MetaM Bool := do
  if advNames.isEmpty then return !(← typeDependsOn xs x)
  return advNames.contains (← x.fvarId!.getUserName).eraseMacroScopes

/-- The adversary positions of the binders `xs` of a computation: the arity of each binder
whose type is a function into `SPComp` (among the binders named `advNames`, or, when it is
empty, among the binders that the type of no other binder mentions). -/
def advPositions (xs : Array Expr) (advNames : Array Name) : MetaM (Array (Option Nat)) := do
  xs.mapM fun x => do
    let ar ← forallTelescope (← whnfR (← inferType x)) fun ys body => do
      return if (← spCompArg? body).isSome then some ys.size else none
    return if ← isAdvBinder xs advNames x then ar else none

/-- The binders of the computation `c`, as `deriveReduction` takes them: the binders of its
value eta-expanded through the type definitions of its type, continued in `k`. -/
def withCompBinders {γ : Type} (c : Name) (lvls : List Level)
    (k : Array Expr → TermElabM γ) : TermElabM γ := do
  let info ← getConstInfo c
  let type := info.type.instantiateLevelParams info.levelParams lvls
  forallTelescope type fun xs b => do
    CatCrypt.Tactics.DeriveTimedFn.withTypeBinders b fun ys _ => k (xs ++ ys)

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
    if (← CatCrypt.Tactics.DeriveTimedFn.keepsLet t v) && !(isTopPath (← getEnv) ctx.top v) then
      -- The first pass records the primitives of the value at the `let`, where a substituted
      -- value would have recorded them at its first use.
      if ctx.found?.isSome then discard <| abstractData ctx v
      -- The local is a `let` declaration, so that a field of a structure value applied through
      -- it reduces to the field's value (`normalize`) and its computations are found.
      return ← withLetDecl n t v fun x => do
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
    if let some μ := sampleDist? e then
      let k ← withLocalDeclD `b α fun b => mkLambdaFVars #[b] (mkRet α b)
      return mkApp4 (mkConst ``CatCrypt.Core.SPTree.sampleDist) α α μ k
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
  if let some μ := sampleDist? c' then
    let k' ← withLocalDeclD `b α fun b => do mkLambdaFVars #[b] (← cont b)
    return mkApp4 (mkConst ``CatCrypt.Core.SPTree.sampleDist) β α μ k'
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
  #[``CatCrypt.Core.SPTree.ret, ``CatCrypt.Core.SPTree.sample,
    ``CatCrypt.Core.SPTree.sampleDist, ``CatCrypt.Core.SPTree.get,
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
      -- The goal with the bound computation in its normal form: a dispatch on a sum below the
      -- bind (`(π.tensor π').start s a`, a `Sum.elim`) normalizes to the matcher of
      -- `sumDispatch`, which `isDefEq` does not unfold on a variable scrutinee.
      let g ← g.replaceTargetDefEq (← mkEq (mkCompile α t) (mkAppN r.getAppFn (rargs.set! 2 c₀)))
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
    if c == ``CatCrypt.Core.SPTree.sampleDist && targs.size == 4 then
      let (a, γ, μ, k) := (targs[0]!, targs[1]!, targs[2]!, targs[3]!)
      if r.isAppOfArity ``CatCrypt.Core.SPComp.bind 4 then
        let k₀ := rargs[3]!
        let h ← sub (← mkPointwise k k₀ 1 a) 1
        return ← close g (mkAppN (mkConst ``CatCrypt.Tactics.DeriveTimedFn.compile_sampleDist_eq)
          #[a, γ, μ, k, k₀, h])
      return ← close g
        (mkAppN (mkConst ``CatCrypt.Tactics.DeriveTimedFn.compile_sampleDist_ret) #[γ, μ])
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
  -- An induction hypothesis, instantiated at the arguments of the call when it is quantified
  -- (a recursive call under a binder, whose arguments that change in the recursion depend on
  -- the bound variable).
  let mut pf? : Option Expr := none
  for d in ← getLCtx do
    if pf?.isSome then break
    if d.isImplementationDetail then continue
    let s ← saveState
    let (ms, _, body) ← forallMetaTelescope (← instantiateMVars d.type)
    for e in ← CatCrypt.Tactics.DeriveTimedFn.conjEqns (mkAppN d.toExpr ms) body do
      let some (_, l, _) := (← instantiateMVars (← inferType e)).eq? | continue
      if ← isDefEq l lhs then
        let e ← instantiateMVars e
        unless e.hasExprMVar do
          pf? := some e
          break
    if pf?.isNone then s.restore
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

/-! ### Costed states -/

/-- The positions of the type parameters of the structure `S` that no other parameter depends
on: the parameters that its erasure relation through erasure maps (`S.Timed.ErasesHat`) takes
at a costed type. -/
def typeParamIdxs (S : Name) : TermElabM (Array Nat) :=
  CatCrypt.Tactics.DeriveTimedStructure.withCtor S fun ps _ _ => do
    let mut out := #[]
    for i in [0:ps.size] do
      let p := ps[i]!
      unless (← whnf (← inferType p)) == mkSort Level.one do continue
      let mut dep := false
      for j in [i+1:ps.size] do
        if (← inferType ps[j]!).containsFVar p.fvarId! then dep := true
      unless dep do out := out.push i
    return out

/-- The erasure `ε v : t` of the value `v` of the costed type of `t`, through the erasure maps
`ε : p̂ → p` of the type parameters `p` (the triples `(p, p̂, ε)` of `hs`): `ε v` at a parameter,
componentwise on a pair and by `Sum.map` on a sum, and `v` on a type that mentions no
parameter. -/
partial def epsParam (hs : Array (Expr × Expr × Expr)) (t v : Expr) : MetaM Expr := do
  let ps := hs.map (·.1)
  if !t.hasAnyFVar (fun f => ps.any (·.fvarId! == f)) then return v
  let tw ← whnfR t
  if tw.isFVar then
    if let some (_, _, e) := hs.find? (·.1 == tw) then return mkApp e v
  if tw.isAppOfArity ``Prod 2 then
    let a ← epsParam hs (tw.getArg! 0) (← mkAppM ``Prod.fst #[v])
    let b ← epsParam hs (tw.getArg! 1) (← mkAppM ``Prod.snd #[v])
    return ← mkAppM ``Prod.mk #[a, b]
  if tw.isAppOfArity ``Sum 2 then
    let side (c : Expr) : MetaM Expr := do
      withLocalDeclD `x (c.replaceFVars ps (hs.map (·.2.1))) fun x => do
        return (← mkLambdaFVars #[x] (← epsParam hs c x)).eta
    return ← mkAppM ``Sum.map #[← side (tw.getArg! 0), ← side (tw.getArg! 1), v]
  throwError "derive_erases_hat: the type `{t}` mentions a type parameter under a type \
    other than a product or a sum"

/-- Define `S.Timed.ErasesHat ps p̂s εs A' A` for a costed structure `A' : S.Timed ps[p̂s]` at
costed types `p̂` of the type parameters `p` of `S` (`typeParamIdxs`) with erasure maps
`ε : p̂ → p`, and `A : S ps`: the conjunction, over the fields of `S` that are not propositions,
of `ε (A'.f) = A.f` for a data field, of
`∀ ŷs, SPComp.bind (A'.f ŷs).erase.compile (fun y => SPComp.pure (ε y)) = A.f (ε ŷs)` for a
computation field, and of `∀ ŷs, (A'.f ŷs).erase = A.f (ε ŷs)` for a tree field whose result
mentions no type parameter. -/
def defineErasesHat (S : Name) : TermElabM Unit := do
  let env ← getEnv
  let some (.inductInfo iv) := env.find? S
    | throwError "derive_erases_hat: `{S}` is not an inductive type"
  unless env.contains (S ++ `Timed) do
    throwError "derive_erases_hat: `{S}` has no costed mirror; `derive_timed_structure {S}` \
      defines it"
  let lps := iv.levelParams
  let lvls := lps.map mkLevelParam
  let idx ← typeParamIdxs S
  let (type, value) ← CatCrypt.Tactics.DeriveTimedStructure.withCtor S fun ps rest fields => do
    unless (← CatCrypt.Tactics.DeriveTimedStructure.gateSetTypes ps rest fields).isEmpty do
      throwError "derive_erases_hat: `{S}` has fields of a circuit kind"
    let tps := idx.map (ps[·]!)
    let hatDecls ← tps.mapM fun p => do
      return ((← p.fvarId!.getUserName).eraseMacroScopes.appendAfter "Hat",
        fun (_ : Array Expr) => (pure (mkSort Level.one) : TermElabM Expr))
    withLocalDeclsD hatDecls fun hats => do
    let epsDecls ← (tps.zip hats).mapM fun (p, h) => do
      return (Name.mkSimple ("ε" ++ (← p.fvarId!.getUserName).eraseMacroScopes.toString),
        fun (_ : Array Expr) => (mkArrow h p : TermElabM Expr))
    withLocalDeclsD epsDecls fun eps => do
    let hs := (tps.zip (hats.zip eps)).map fun (p, h, e) => (p, h, e)
    let hatT (t : Expr) : Expr := t.replaceFVars tps hats
    let withHats (ys : Array Expr) (k : Array Expr → TermElabM Expr) : TermElabM Expr := do
      let decls ← ys.mapM fun y => do
        let t := hatT (← inferType y)
        return ((← y.fvarId!.getUserName).eraseMacroScopes,
          fun (_ : Array Expr) => (pure t : TermElabM Expr))
      withLocalDeclsD decls k
    let sT := mkAppN (mkConst S lvls) ps
    let tT := mkAppN (mkConst (S ++ `Timed) lvls) (ps.map hatT)
    withLocalDeclD `A' tT fun A' => withLocalDeclD `A sT fun A => do
      let conjs ← forallBoundedTelescope rest fields.size fun xs _ => do
        let mut conjs : Array Expr := #[]
        for x in xs, f in fields do
          let d ← inferType x
          let k ← CatCrypt.Tactics.DeriveTimedStructure.fieldKind d
          if !(k matches .prop) && xs.any (d.containsFVar ·.fvarId!) then
            throwError "derive_erases_hat: the type of the field `{f}` depends on a field"
          match k with
          | .prop => pure ()
          | .type => throwError "derive_erases_hat: `{S}` has the type field `{f}`"
          | .data | .bounded _ _ =>
            conjs := conjs.push
              (← mkEq (← epsParam hs d (← mkProjection A' f)) (← mkProjection A f))
          | .comp n =>
            conjs := conjs.push (← forallBoundedTelescope (← whnfR d) n fun ys b => do
              withHats ys fun yh => do
                let β := (← whnfR b).appArg!
                let m ← mkAppM ``CatCrypt.Core.SPTree.compile
                  #[← mkAppM ``CatCrypt.Core.SPTree.Timed.erase
                    #[mkAppN (← mkProjection A' f) yh]]
                let kf ← withLocalDeclD `y (hatT β) fun y => do
                  mkLambdaFVars #[y] (← mkAppM ``CatCrypt.Core.SPComp.pure
                    #[← epsParam hs β y])
                let lhs ← mkAppM ``CatCrypt.Core.SPComp.bind #[m, kf]
                let rhs := mkAppN (← mkProjection A f)
                  (← (ys.zip yh).mapM fun (y, z) => do epsParam hs (← inferType y) z)
                mkForallFVars yh (← mkEq lhs rhs))
          | .tree n =>
            conjs := conjs.push (← forallBoundedTelescope (← whnfR d) n fun ys b => do
              if b.hasAnyFVar (fun v => tps.any (·.fvarId! == v)) then
                throwError "derive_erases_hat: the result of the tree field `{f}` mentions a \
                  type parameter"
              let some T ← CatCrypt.Tactics.DeriveTimedFn.treeTy? b
                | throwError "derive_erases_hat: the field `{f}`"
              withHats ys fun yh => do
                let lhs := T.eraseE (mkAppN (← mkProjection A' f) yh)
                let rhs := mkAppN (← mkProjection A f)
                  (← (ys.zip yh).mapM fun (y, z) => do epsParam hs (← inferType y) z)
                mkForallFVars yh (← mkEq lhs rhs))
          | .circuit _ _ => throwError "derive_erases_hat: `{S}` has the circuit field `{f}`"
        return conjs
      let body := if conjs.isEmpty then Lean.mkConst ``True else mkAndN conjs.toList
      let bs := ps ++ hats ++ eps ++ #[A', A]
      return (← mkForallFVars bs (mkSort .zero), ← mkLambdaFVars bs body)
  CatCrypt.Tactics.DeriveTimedFn.addTimedDef (S ++ `Timed ++ `ErasesHat) lps type value

/-- The flat type of a type `t` of data holding functions: each structure with a costed mirror
(`mirrorStruct?`) replaced by the tuple of the flat types of its fields, through products and
sums; `none` when `t` has no such structure holding functions. The costed type of the flat type
is that of `t`, and a binder of a flat type is a binder with a costed value in `derive_timed`
(of kind `hat`), where a binder of a structure type keeps the convention of field paths. -/
partial def flatTy? (t : Expr) : MetaM (Option Expr) := do
  let some _ ← CatCrypt.Tactics.DeriveTimedFn.hatTy? t | return none
  let tw ← whnfR t
  let prod := tw.isAppOfArity ``Prod 2
  if prod || tw.isAppOfArity ``Sum 2 then
    let a := tw.getArg! 0
    let b := tw.getArg! 1
    let fa ← flatTy? a
    let fb ← flatTy? b
    if fa.isNone && fb.isNone then return none
    return some (← mkAppM (if prod then ``Prod else ``Sum) #[fa.getD a, fb.getD b])
  if let some m ← CatCrypt.Tactics.DeriveTimedFn.mirrorStruct? tw then
    let fs ← m.fieldTypes.mapM fun f => return (← flatTy? f).getD f
    return some (← CatCrypt.Tactics.DeriveTimedFn.mirrorType fs)
  return none

/-- The value of type `t` of the value `v` of its flat type (`flatTy?`): each tuple of fields
of a structure assembled by its constructor. -/
partial def unflatE (t v : Expr) : MetaM Expr := do
  let some _ ← flatTy? t | return v
  let tw ← whnfR t
  if tw.isAppOfArity ``Prod 2 then
    return ← mkAppM ``Prod.mk #[← unflatE (tw.getArg! 0) (← mkAppM ``Prod.fst #[v]),
      ← unflatE (tw.getArg! 1) (← mkAppM ``Prod.snd #[v])]
  if tw.isAppOfArity ``Sum 2 then
    let side (c : Expr) : MetaM Expr := do
      withLocalDeclD `x ((← flatTy? c).getD c) fun x => do
        mkLambdaFVars #[x] (← unflatE c x)
    return ← mkAppM ``Sum.map #[← side (tw.getArg! 0), ← side (tw.getArg! 1), v]
  if let some m ← CatCrypt.Tactics.DeriveTimedFn.mirrorStruct? tw then
    let n := m.fieldTypes.size
    let mut fs := #[]
    for i in [0:n] do
      fs := fs.push (← unflatE m.fieldTypes[i]!
        (← CatCrypt.Tactics.DeriveTimedFn.mirrorProj n i v))
    return mkAppN (mkConst m.ctor m.levels) (m.params ++ fs)
  return v

/-- The binders `ys` with each binder whose type has a flat type (`flatTy?`) replaced by a
binder of the flat type, continued in `k` with the new binders and, for each binder of `ys`,
its value in terms of them. -/
partial def withFlatBinders {γ : Type} (ys : Array Expr)
    (k : Array Expr → Array Expr → TermElabM γ) : TermElabM γ :=
  go 0 #[] #[]
where
  go (i : Nat) (ys' us : Array Expr) : TermElabM γ := do
    if h : i < ys.size then
      let y := ys[i]
      let t ← inferType y
      match ← flatTy? t with
      | none => go (i + 1) (ys'.push y) (us.push y)
      | some ft =>
        withLocalDeclD (← y.fvarId!.getUserName) ft fun y' => do
          go (i + 1) (ys'.push y') (us.push (← unflatE t y'))
    else k ys' us

/-- The field `i` of the constructor application `s`, when `s` is one. -/
def ctorField? (s : Expr) (i : Nat) : MetaM (Option Expr) := do
  let s := s.consumeMData
  let .const k _ := s.getAppFn | return none
  let some (.ctorInfo ci) := (← getEnv).find? k | return none
  unless s.getAppNumArgs == ci.numParams + ci.numFields do return none
  return s.getAppArgs[ci.numParams + i]?

/-- `e` with each projection of a constructor application reduced to the field, applied to
the remaining arguments. -/
def reduceProjCtor (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    if let .proj _ i s := e then
      if let some r ← ctorField? s i then return .visit r
    if let .const m _ := e.getAppFn then
      if let some info ← getProjectionFnInfo? m then
        let args := e.getAppArgs
        if h : info.numParams < args.size then
          if let some r ← ctorField? args[info.numParams] info.i then
            return .visit (mkAppN r (args.extract (info.numParams + 1) args.size)).headBeta
    return .continue)

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
  CatCrypt.Tactics.DeriveTimedFn.withBinders {} tBs fun tctx bs _ => do
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
    return (← CatCrypt.Tactics.DeriveTimedFn.fieldCostName p,
      fun _ => do CatCrypt.Tactics.DeriveTimedFn.companionType (← inferType p))
  withLocalDeclsD compDecls fun comps => do
  let compsOf (n : Name) : Array Expr :=
    match fieldPaths.find? (·.1 == n) with
    | some (_, ps) => ps.filterMap fun p => (allPaths.idxOf? p).map (comps[·]!)
    | none => #[]
  -- The erasure of the costed binder of the tree binder `fv`, compiled when `compile`.
  let erase (fv : Expr) (compile : Bool) : TermElabM Expr := do
    let v ← costed fv
    forallTelescope (← whnfR (← inferType fv)) fun ys bt => do
      let some T ← CatCrypt.Tactics.DeriveTimedFn.treeTy? bt | fail m!"internal: `{fv}`"
      let e := T.eraseE (mkAppN v ys)
      let e ← if compile then mkAppM ``CatCrypt.Core.SPTree.compile #[e] else pure e
      mkLambdaFVars ys e
  -- An adversary called in a type or data field is the compilation of the erasure of its
  -- costed binder, as in the erasure theorem.
  let advFvs := advs.map (mkFVar ·.orig)
  let advErased ← advs.mapM fun a => do
    if kept.contains a.tree then erase a.tree true else pure (mkFVar a.orig)
  -- The costed form.
  let mut mvals : Array Expr := #[]
  for fd in fields do
    match fd.kind with
    | .prop => pure ()
    | .type | .data =>
      let v ← Core.betaReduce (fd.value.replaceFVars advFvs advErased)
      for x in xs do
        if v.containsFVar x.fvarId! && !bs.contains x then
          fail m!"the field `{fd.name}` of the result mentions `{x}`, which the costed form \
            does not take"
      mvals := mvals.push v
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
  CatCrypt.Tactics.DeriveTimedFn.addTimedDef timedName levelParams
    (← mkForallFVars (bs ++ comps) resT)
    (← mkLambdaFVars (bs ++ comps) (mkAppN (mkConst mirrorCtor lvlsS) (qs ++ mvals)))
  -- The erasure theorem: the data primitives at their fields, the tree and computation
  -- primitives with hypotheses relating their costed binders to their fields.
  let bsInst := bs.map fun b => match dps.find? (·.fv == b) with
    | some p => p.key
    | none => b
  let argsC ← xs.mapM fun x => do
    match advs.find? (·.orig == x.fvarId!) with
    | some a => erase a.tree true
    | none => pure x
  let mut hypDecls : Array (Name × (Array Expr → TermElabM Expr)) := #[]
  for p in pps do
    let v ← costed p.fv
    let t ← forallTelescope (← whnfR (← inferType p.fv)) fun ys _ => do
      let some T ← CatCrypt.Tactics.DeriveTimedFn.treeTy? (← inferType (mkAppN p.fv ys)) |
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
  if pf.hasSorry || pf.hasExprMVar then
    fail m!"the erasure theorem `{c ++ `erase_timed}` is not proved"
  let newBs := bs.filter fun b => !tBs.contains b
  let eBs := xs.filter (fun x => (advs.find? (·.orig == x.fvarId!)).isNone) ++ newBs ++ comps ++
    hs
  addDecl (Declaration.thmDecl
    { name := c ++ `erase_timed, levelParams,
      type := ← mkForallFVars eBs goalTy, value := ← mkLambdaFVars eBs pf })

/-- Close the goal `g` by `rfl`, or else by rewriting with `Sum.map id id = id`. -/
def closeEpsGoal (g : MVarId) : TermElabM Unit := do
  let gs ← Lean.Elab.Tactic.run g do
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      first
        | rfl
        | (funext y; simp only [Sum.map_id_id, id_eq]; done)
        | (simp only [Sum.map_id_id, id_eq]; done)))
  unless gs.isEmpty do fail m!"internal: an erasure map is not closed"

/-- Define `c.timed` at the costed parameters of `S` from the costed forms `c.f.treeHat.timed`
of the computation fields, whose binders hold functions, and prove
`c.erase_timed : S.Timed.ErasesHat qs q̂s εs (c.timed …) (c …)`, with `q̂ = hatTy? q` and
`ε = epsFun q` at a parameter holding functions, and `q̂ = q`, `ε` the identity elsewhere. The
arguments are those of `assembleStruct`. -/
partial def assembleStructHat (c : Name) (levels : List Level) (levelParams : List Name)
    (S : Name) (lvlsS : List Level) (qs : Array Expr) (mirrorFields : Array Name)
    (fields : Array SField) (xs bsOrig : Array Expr) (advs : Array Adv)
    (kept : Array Expr) (ps : Array Prim) : TermElabM Unit := do
  let env ← getEnv
  let timedS := S ++ `Timed
  let ehName := timedS ++ `ErasesHat
  unless env.contains ehName do
    fail m!"the computation fields of `{c}` take data holding functions, whose erasure is \
      stated by `{ehName}`; `derive_erases_hat {S}` defines it"
  for fd in fields do
    if fd.kind matches .tree _ then
      fail m!"the tree field `{fd.name}` of a structure whose computation fields take data \
        holding functions"
  -- The costed parameters, and the arguments of the erasure relation.
  let tpIdx ← typeParamIdxs S
  let mut qsHat := qs
  for i in [0:qs.size] do
    if let some h ← CatCrypt.Tactics.DeriveTimedFn.hatTy? qs[i]! then
      unless tpIdx.contains i do
        fail m!"the parameter `{qs[i]!}` of `{S}` holds functions and is not a type parameter \
          that no other parameter depends on"
      qsHat := qsHat.set! i h
  let mut hatArgs : Array Expr := #[]
  let mut epsArgs : Array Expr := #[]
  for i in tpIdx do
    let q := qs[i]!
    hatArgs := hatArgs.push qsHat[i]!
    if (← CatCrypt.Tactics.DeriveTimedFn.hatTy? q).isSome then
      epsArgs := epsArgs.push (← CatCrypt.Tactics.DeriveTimedFn.epsFun q)
    else
      epsArgs := epsArgs.push (mkApp (Lean.mkConst ``id [Level.one]) q)
  let dps := ps.filter (·.data)
  let pps := ps.filter fun p => !p.data
  let cps := pps.filter fun p => !p.tree
  let tBs := kept ++ dps.map (·.fv) ++ pps.map (·.fv)
  CatCrypt.Tactics.DeriveTimedFn.withBinders {} tBs fun tctx bs _ => do
  let costed (fv : Expr) : TermElabM Expr := do
    let some info := tctx.locals.get? fv.fvarId! | fail m!"internal: `{fv}` has no costed form"
    return info.value
  let hatName (fd : SField) : Name := c ++ fd.name ++ `treeHat
  -- The field paths whose cost companions the costed forms of the fields take.
  let mut allPaths : Array Expr := #[]
  let mut fieldPaths : Array (Name × Array Expr) := #[]
  for fd in fields do
    unless fd.kind matches .comp _ do continue
    let fpName := hatName fd ++ `timed ++ `fieldPaths
    unless env.contains fpName do continue
    let paths ← withFlatBinders fd.ys fun ys' _ => do
      let some fp ← unfoldDefinition? (mkAppN (Lean.mkConst fpName levels) (tBs ++ ys'))
        | fail m!"internal: `{fpName}` does not unfold"
      let mut tup := fp.headBeta
      let mut paths := #[]
      while tup.isAppOfArity ``PProd.mk 4 do
        let p := tup.getArg! 2
        for y in ys' do
          if p.containsFVar y.fvarId! then
            fail m!"the costed form of the field `{fd.name}` takes the cost of the field `{p}`, \
              which depends on the arguments of the field"
        paths := paths.push p
        tup := (tup.getArg! 3).headBeta
      return paths
    for p in paths do
      unless allPaths.contains p do allPaths := allPaths.push p
    fieldPaths := fieldPaths.push (fd.name, paths)
  let compDecls ← allPaths.mapM fun p => do
    return (← CatCrypt.Tactics.DeriveTimedFn.fieldCostName p,
      fun _ => do CatCrypt.Tactics.DeriveTimedFn.companionType (← inferType p))
  withLocalDeclsD compDecls fun comps => do
  let compsOf (n : Name) : Array Expr :=
    match fieldPaths.find? (·.1 == n) with
    | some (_, ps) => ps.filterMap fun p => (allPaths.idxOf? p).map (comps[·]!)
    | none => #[]
  let erase (fv : Expr) (compile : Bool) : TermElabM Expr := do
    let v ← costed fv
    forallTelescope (← whnfR (← inferType fv)) fun ys bt => do
      let some T ← CatCrypt.Tactics.DeriveTimedFn.treeTy? bt | fail m!"internal: `{fv}`"
      let e := T.eraseE (mkAppN v ys)
      let e ← if compile then mkAppM ``CatCrypt.Core.SPTree.compile #[e] else pure e
      mkLambdaFVars ys e
  let advFvs := advs.map (mkFVar ·.orig)
  let advErased ← advs.mapM fun a => do
    if kept.contains a.tree then erase a.tree true else pure (mkFVar a.orig)
  -- The costed form, checked field by field against the mirror at the costed parameters.
  let mirrorCtor := (getStructureCtor env timedS).name
  let mut mty ← instantiateForall (← inferType (mkConst mirrorCtor lvlsS)) qsHat
  let mut mvals : Array Expr := #[]
  for fd in fields do
    match fd.kind with
    | .prop => pure ()
    | .type | .data =>
      let mut v ← Core.betaReduce (fd.value.replaceFVars advFvs advErased)
      for x in xs do
        if v.containsFVar x.fvarId! && !bs.contains x then
          fail m!"the field `{fd.name}` of the result mentions `{x}`, which the costed form \
            does not take"
      let .forallE _ d b _ ← whnf mty | fail m!"internal: the mirror of `{S}`"
      unless ← isDefEq (← inferType v) d do
        v := (← CatCrypt.Tactics.DeriveTimedFn.tv tctx v).2
        unless ← isDefEq (← inferType v) d do
          fail m!"the costed value of the field `{fd.name}` has type{indentExpr (← inferType v)}\n\
            and the mirror at the costed parameters takes{indentExpr d}"
      mvals := mvals.push v
      mty := b.instantiate1 v
    | _ =>
      let tc := Lean.mkConst (hatName fd ++ `timed) levels
      let fcs := compsOf fd.name
      let tcT ← instantiateForall (← inferType tc) bs
      let (fv, cv) ← forallBoundedTelescope tcT fd.ys.size fun yh _ => do
        unless yh.size == fd.ys.size do
          fail m!"the costed form of the field `{fd.name}` takes fewer arguments than the field"
        let call := mkAppN tc (bs ++ yh ++ fcs)
        return (← mkLambdaFVars yh (← mkAppM ``Prod.snd #[call]),
          ← mkLambdaFVars yh (← mkAppM ``Prod.fst #[call]))
      let .forallE _ d b _ ← whnf mty | fail m!"internal: the mirror of `{S}`"
      unless ← isDefEq (← inferType fv) d do
        fail m!"the costed form of the field `{fd.name}` has type{indentExpr (← inferType fv)}\n\
          and the mirror at the costed parameters takes{indentExpr d}"
      mvals := mvals.push fv
      mty := b.instantiate1 fv
      if mirrorFields.contains (fd.name.appendAfter "Cost") then
        let .forallE _ _ b' _ ← whnf mty | fail m!"internal: the mirror of `{S}`"
        mvals := mvals.push cv
        mty := b'.instantiate1 cv
  let resT := mkAppN (mkConst timedS lvlsS) qsHat
  let timedName := c ++ `timed
  CatCrypt.Tactics.DeriveTimedFn.addTimedDef timedName levelParams
    (← mkForallFVars (bs ++ comps) resT)
    (← mkLambdaFVars (bs ++ comps) (mkAppN (mkConst mirrorCtor lvlsS) (qsHat ++ mvals)))
  -- The erasure theorem.
  let bsInst := bs.map fun b => match dps.find? (·.fv == b) with
    | some p => p.key
    | none => b
  let argsC ← xs.mapM fun x => do
    match advs.find? (·.orig == x.fvarId!) with
    | some a => erase a.tree true
    | none => pure x
  let mut hypDecls : Array (Name × (Array Expr → TermElabM Expr)) := #[]
  for p in pps do
    let v ← costed p.fv
    let t ← forallTelescope (← whnfR (← inferType p.fv)) fun ys _ => do
      let some T ← CatCrypt.Tactics.DeriveTimedFn.treeTy? (← inferType (mkAppN p.fv ys)) |
        fail m!"internal: `{p.fv}`"
      let lhs := T.eraseE (mkAppN v ys)
      let lhs ← if p.tree then pure lhs else mkAppM ``CatCrypt.Core.SPTree.compile #[lhs]
      mkForallFVars ys (← mkEq lhs (mkAppN p.key ys))
    let n := (← p.fv.fvarId!.getUserName).eraseMacroScopes.appendBefore "h_"
    hypDecls := hypDecls.push (n, fun _ => pure t)
  withLocalDeclsD hypDecls fun hs => do
  let lhsA := mkAppN (mkConst timedName levels) (bsInst ++ comps)
  let rhsA := mkAppN (mkConst c levels) argsC
  let goalTy := mkAppN (mkConst ehName lvlsS) (qs ++ hatArgs ++ epsArgs ++ #[lhsA, rhsA])
  let some unfolded ← unfoldDefinition? goalTy | fail m!"internal: `{ehName}`"
  let unfolded := unfolded.headBeta
  -- The conjuncts, one for each field that is not a proposition.
  let nConj := (fields.filter fun fd => !(fd.kind matches .prop)).size
  let mut conjs : Array Expr := #[]
  let mut rest := unfolded
  for i in [0:nConj] do
    if i + 1 < nConj then
      unless rest.isAppOfArity ``And 2 do fail m!"internal: the erasure relation `{ehName}`"
      conjs := conjs.push (rest.getArg! 0)
      rest := rest.getArg! 1
    else conjs := conjs.push rest
  let compArgs ← bsOrig.mapM fun b => do
    match advs.find? (·.tree == b) with
    | some _ => erase b false
    | none => pure b
  let cArgs ← cps.mapM fun p => erase p.fv false
  let cHyps := (pps.zip hs).filterMap fun (p, h) => if p.tree then none else some h
  let mut proofs : Array Expr := #[]
  let mut j := 0
  for fd in fields do
    if fd.kind matches .prop then continue
    let C := conjs[j]!
    j := j + 1
    match fd.kind with
    | .comp _ =>
      let pf ← forallTelescope C fun yh body => do
        let some (_, lhs, _) := body.eq? | fail m!"internal: the conjunct of `{fd.name}`"
        let kf := lhs.appArg!
        let .lam yn yt kb ybi := kf | fail m!"internal: the conjunct of `{fd.name}`"
        let ε' := Expr.lam yn yt kb.appArg! ybi
        let some β ← spCompArg? (← inferType fd.body) | fail m!"internal: `{fd.name}`"
        let call := mkAppN (Lean.mkConst (hatName fd ++ `timed) levels)
          (bsInst ++ yh ++ compsOf fd.name)
        let X ← mkAppM ``Prod.snd #[call]
        let α := (← whnfR (← inferType X)).appArg!
        let ε ← CatCrypt.Tactics.DeriveTimedFn.epsFun β
        let hεT ← mkEq ε' ε
        let hεM ← mkFreshExprSyntheticOpaqueMVar hεT
        closeEpsGoal hεM.mvarId!
        let hε ← instantiateMVars hεM
        let h1 := mkAppN (Lean.mkConst (hatName fd ++ `erase_timed) levels)
          (bsInst ++ yh ++ compsOf fd.name)
        let some (_, _, t) := (← inferType h1).eq? | fail m!"internal: `{hatName fd}`"
        let εy ← (fd.ys.zip yh).mapM fun (y, z) => do
          CatCrypt.Tactics.DeriveTimedFn.epsE (← inferType y) z
        let h2 := mkAppN (mkConst (c ++ fd.name ++ `compile_tree) levels)
          (compArgs ++ cArgs ++ cHyps ++ εy)
        let some (_, _, cC) := (← inferType h2).eq? | fail m!"internal: `{fd.name}`"
        let pf := mkAppN (Lean.mkConst ``compile_bind_pure_of_erase)
          #[α, β, X, ε, ε', t, cC, hε, h1, h2]
        mkLambdaFVars yh (← mkExpectedTypeHint pf body)
      proofs := proofs.push pf
    | _ =>
      let mv ← mkFreshExprSyntheticOpaqueMVar C
      closeEpsGoal mv.mvarId!
      proofs := proofs.push (← instantiateMVars mv)
  let mut pf := if nConj == 0 then Lean.mkConst ``True.intro else proofs.back!
  if nConj > 1 then
    for i in (List.range (nConj - 1)).reverse do
      pf := mkApp4 (Lean.mkConst ``And.intro) conjs[i]!
        (mkAndN (conjs.extract (i + 1) conjs.size).toList) proofs[i]! pf
  pf ← mkExpectedTypeHint pf goalTy
  if pf.hasSorry || pf.hasExprMVar then
    fail m!"the erasure theorem `{c ++ `erase_timed}` is not proved"
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
      let t ← inferType x
      let ar ← forallTelescope (← whnfR t) fun ys body => do
        return if (← spCompArg? body).isSome then some ys.size else none
      let named ← isAdvBinder xs advNames x
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
          else if !(fd.kind matches .prop) then
            roots := roots.push fd.value
            -- An adversary called in a type or data field (a handler in an oracle program):
            -- its tree-valued binder is a binder of the costed form.
            for a in advs do
              if fd.value.containsFVar a.orig then roots := roots.push a.tree
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
          CatCrypt.Tactics.DeriveTimedFn.addTimedDef treeName levelParams
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
        -- The costed forms of the trees at the plain interface, and the assembly.
        let plainPath : TermElabM Unit := do
          for fd in fields, t in trees do
            let some _ := t | continue
            CatCrypt.Tactics.DeriveTimedFn.deriveTimed {} (c ++ fd.name ++ `tree)
          assembleStruct c levels levelParams S lvlsS qs mirrorFields fields xs bs advs kept ps
        -- A computation field whose binders hold functions: the costed state, through the
        -- tree `c.f.treeHat` over flat binders, when the structure has the erasure relation
        -- `S.Timed.ErasesHat` (`derive_erases_hat`) and the plain interface fails; a reduction
        -- that derives at the plain interface keeps it.
        let hatCapable ← fields.anyM fun fd => do
          unless fd.kind matches .comp _ do return false
          fd.ys.anyM fun y => do
            return (← CatCrypt.Tactics.DeriveTimedFn.hatTy? (← inferType y)).isSome
        let hatPath : TermElabM Unit := do
         for fd in fields, t in trees do
          let some t := t | continue
          if fd.kind matches .comp _ then
            -- The hat tree `c.f.treeHat` is a definition separate from `c.f.tree`:
            -- `derive_timed` gives the plain interface only to a tree named `R.f.tree` of a
            -- field `f` of the result structure of `R` (the name-based rule `fieldTree` in
            -- `CatCryptCore.Tactics.DeriveTimed`), so `c.f.treeHat.timed` takes the costed
            -- values of its flat binders.
            let hatName := c ++ fd.name ++ `treeHat
            withFlatBinders fd.ys fun ys' us => do
              let tH ← reduceProjCtor (t.replaceFVars fd.ys us)
              CatCrypt.Tactics.DeriveTimedFn.addTimedDef hatName levelParams
                (← mkForallFVars (tBs ++ ys') (← inferType tH))
                (← mkLambdaFVars (tBs ++ ys') tH)
            CatCrypt.Tactics.DeriveTimedFn.deriveTimed {} hatName
          else
            CatCrypt.Tactics.DeriveTimedFn.deriveTimed {} (c ++ fd.name ++ `tree)
         assembleStructHat c levels levelParams S lvlsS qs mirrorFields fields xs bs advs kept ps
        if hatCapable && (← getEnv).contains (S ++ `Timed ++ `ErasesHat) then
          -- Each interface is an attempt (`attempt`): a runtime exception of the plain
          -- interface leads to the costed state, and the error names both failures.
          match ← attempt plainPath with
          | .ok () => pure ()
          | .error e₁ =>
            match ← attempt hatPath with
            | .ok () => pure ()
            | .error e₂ =>
              throwError "derive_reduction: at the plain interface:{indentD e₁.toMessageData}\n\
                with the costed state:{indentD e₂.toMessageData}"
        else plainPath
    go 0 #[] #[] #[]

/-- Replace each call `recF as` of the local `recF` in `e` by `t as extra`. -/
partial def replaceRecCalls (recF t : Expr) (extra : Array Expr) (e : Expr) : Expr :=
  e.replace fun s =>
    if s.getAppFn == recF then
      some (mkAppN t (s.getAppArgs.map (replaceRecCalls recF t extra) ++ extra))
    else none

/-- The branch of the `if` (or `if h :`) `e` that a local hypothesis decides, with the proof of
`e = branch` by `ite_eq_left`, `ite_eq_right`, `dite_eq_left` or `dite_eq_right`; `none` when
`e` is not an `if` or no local proves its condition or the negation of its condition. -/
def decideIf? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let dep := e.isAppOfArity ``dite 5
  unless dep || e.isAppOfArity ``ite 5 do return none
  let args := e.getAppArgs
  let (α, c, inst, t, f) := (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ← isProp ty do continue
    let pos ← isDefEq ty c
    let neg ← if pos then pure false else isDefEq ty (mkNot c)
    unless pos || neg do continue
    let thm := if dep then (if pos then ``dite_eq_left else ``dite_eq_right)
      else (if pos then ``ite_eq_left else ``ite_eq_right)
    let step ← mkAppOptM thm #[some c, some inst, some d.toExpr, some α, some t, some f]
    let some (_, _, b) := (← inferType step).eq? | return none
    return some (step, b.headBeta)
  return none

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
    -- An `if` of the body decided by a hypothesis of the case (the induction of a recursion
    -- by `if`, well-founded or structural): the branch taken, by `dite_eq_left`, `dite_eq_right`,
    -- `ite_eq_left` or `ite_eq_right`.
    repeat
      let some (step, b) ← decideIf? body | break
      pf ← mkEqTrans pf step
      body := b
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
  CatCrypt.Tactics.DeriveTimedFn.addTimedDef treeName levelParams tType tValue
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
    CatCrypt.Tactics.DeriveTimedFn.withTypeBinders (← instantiateForall d.type xs) fun ys _ =>
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
  -- A tree-valued reduction (`PK → OracleAdv D R α`): the reduction is a tree of a registered
  -- kind after its binders, with the leading binders of its result among them, and its costed
  -- form is that of `derive_timed`.
  if ← lambdaTelescope value fun _ b => do
      return (← CatCrypt.Tactics.DeriveTimedFn.treeTy? (← inferType b)).isSome then
    if env.contains (c ++ `timed) then fail m!"`{c ++ `timed}` already exists"
    return ← CatCrypt.Tactics.DeriveTimedFn.deriveTimed {} c
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
      let t ← inferType x
      let ar ← forallTelescope (← whnfR t) fun ys body => do
        return if (← spCompArg? body).isSome then some ys.size else none
      let named ← isAdvBinder xs advNames x
      isAdv := isAdv.push (if named then ar else none)
    for n in advNames do
      unless ← xs.anyM (fun x => return (← x.fvarId!.getUserName).eraseMacroScopes == n) do
        fail m!"`{c}` has no binder `{n}`"
    for x in xs, ar in isAdv do
      if advNames.contains (← x.fvarId!.getUserName).eraseMacroScopes && ar.isNone then
        -- An adversary structure (an environment with computation fields): its fields are
        -- computation primitives, each a costed binder with a cost companion.
        let .const S _ := (← whnfR (← inferType x)).getAppFn
          | fail m!"the binder `{x}` is not a function into `SPComp` or a structure"
        unless isStructure env S && !isClass env S do
          fail m!"the binder `{x}` is not a function into `SPComp` or a structure"
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
        let typePos ← typePositions xs α
        let ctx₀ : RCtx := { advs, base := treeName, top, unfold, visiting, deriveRec, typePos }
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
            fail m!"the adversary `{mkFVar a.orig}` occurs outside a call position \
              in{indentExpr tree}"
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
    CatCrypt.Tactics.DeriveTimedFn.addTimedDef treeName info.levelParams tType tValue
  addDecl (Declaration.thmDecl
    { name := thmName, levelParams := info.levelParams, type := eType, value := eValue })
  CatCrypt.Tactics.DeriveTimedFn.deriveTimed {} treeName

/-- `derive_reduction_fn B` defines the computation tree `B.tree` of the reduction `B`, proves
`B.compile_tree`, and runs `derive_timed_fn B.tree`; `derive_reduction_fn B (adv := A₁ … Aₖ)`
takes the adversaries to be the binders `A₁ … Aₖ`. -/
syntax (name := deriveReductionCmd) "derive_reduction_fn " ident
  (" (" &"adv" " := " ident+ ")")? : command

/-- `derive_erases_hat_fn S` defines `S.Timed.ErasesHat`, the erasure relation of the costed
mirror of `S` at costed types of its type parameters, through erasure maps. -/
syntax (name := deriveErasesHatCmd) "derive_erases_hat_fn " ident : command

@[command_elab deriveErasesHatCmd]
def elabDeriveErasesHat : CommandElab := fun stx => do
  liftTermElabM do
    let S ← realizeGlobalConstNoOverloadWithInfo stx[1]
    defineErasesHat S

@[command_elab deriveReductionCmd]
def elabDeriveReduction : CommandElab := fun stx => do
  let advs : Array Name :=
    if stx[2].getNumArgs > 3 then stx[2][3].getArgs.map (·.getId) else #[]
  liftTermElabM do
    let c ← realizeGlobalConstNoOverloadWithInfo stx[1]
    -- The first attempt, then the attempt that unfolds the data definitions applied to a
    -- structure binder (`attempt`); the error names the failures of both, or the one failure
    -- when both attempts fail with the same message.
    match ← attempt (deriveReduction c advs) with
    | .ok () => pure ()
    | .error e₁ =>
      match ← attempt (deriveReduction c advs (unfold := true)) with
      | .ok () => pure ()
      | .error e₂ =>
        if (← e₁.toMessageData.toString) == (← e₂.toMessageData.toString) then throw e₁
        throwError "derive_reduction: the first attempt fails:{indentD e₁.toMessageData}\n\
          with the data definitions applied to a structure binder unfolded:\
          {indentD e₂.toMessageData}"

end CatCrypt.Tactics.DeriveReductionFn

end

/-! ## Time rules of a sampling node of a sub-distribution -/

namespace CatCrypt.Tactics.AutoTime.Fn

open CatCrypt.Core

variable {α β : Type} {P B : ℕ}

/-- The time of a sampling node of a sub-distribution: its unit and, for every sample, the step
cost and the time of the continuation. The second hypothesis bounds the unit on an empty
sample space. -/
theorem time_sampleDist {γ : Type} {μ : Prob.SDistr γ} {c : γ → ℕ} {k : γ → SPTree.Timed α}
    (h : ∀ b, P + 1 + c b + (k b).time ≤ B) (h₀ : P + 1 ≤ B) :
    P + (SPTree.Timed.sampleDist γ μ c k).time ≤ B := by
  rw [SPTree.Timed.time_sampleDist]
  have hs : (⨆ b, c b + (k b).time) ≤ B - P - 1 :=
    ciSup_le' fun b => by
      have := h b
      omega
  omega

/-- The step time of a sampling node of a sub-distribution followed by a costed bind. -/
theorem st_bind_sampleDist {γ : Type} {μ : Prob.SDistr γ} {c : γ → ℕ}
    {k : γ → SPTree.Timed α} {f : α → ℕ × SPTree.Timed β}
    (h : ∀ b, P + 1 + c b + SPTree.Timed.stepTime ((k b).bind f) ≤ B) (h₀ : P + 1 ≤ B) :
    P + SPTree.Timed.stepTime ((SPTree.Timed.sampleDist γ μ c k).bind f) ≤ B := by
  simp only [SPTree.Timed.bind, SPTree.Timed.stepTime, SPTree.Timed.time_sampleDist,
    Nat.zero_add]
  have hs : (⨆ b, c b + (SPTree.Timed.bind (k b) f).1 + (SPTree.Timed.bind (k b) f).2.time) ≤
      B - P - 1 :=
    ciSup_le' fun b => by
      have := h b
      simp only [SPTree.Timed.stepTime] at this
      omega
  omega

end CatCrypt.Tactics.AutoTime.Fn

namespace CatCrypt.Tactics.AutoTime.Fn

open CatCrypt.Core CatCrypt.Crypto

meta section

open Lean Meta Elab Tactic

/-- The forms of a time goal, by the subterm that carries the tree. -/
inductive Kind where
  /-- `P + SPTree.Timed.stepTime x ≤ B` -/
  | step
  /-- `P + t.time ≤ B` -/
  | time
  /-- `A.TimeBound (B - P)` -/
  | tb
  /-- `StepTimeBound x (B - P)` -/
  | stb

/-- The rule that closes a goal of kind `k` from a bound of its tree. -/
def Kind.ofRule : Kind → Name
  | .step => ``st_of
  | .time => ``time_of
  | .tb => ``tb_of
  | .stb => ``stb_of

/-- The left side of an inequality `l ≤ r` over `ℕ`. -/
def natLe? (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity ``LE.le 4 && (e.getArg! 0).isConstOf ``Nat then
    some (e.getArg! 2, e.getArg! 3)
  else none

/-- The tree of a bound of kind `k`: `y` in `stepTime y ≤ E`, `y.time ≤ E`, `y.TimeBound E`,
`StepTimeBound y E`. -/
def Kind.treeOf (k : Kind) (e : Expr) : Option Expr :=
  match k with
  | .step => do
    let (l, _) ← natLe? e
    guard (l.isAppOfArity ``SPTree.Timed.stepTime 2)
    return l.appArg!
  | .time => do
    let (l, _) ← natLe? e
    guard (l.isAppOfArity ``SPTree.Timed.time 2)
    return l.appArg!
  | .tb => if e.isAppOfArity ``OracleAdv.Timed.TimeBound 5 then some (e.getArg! 3) else none
  | .stb =>
    if e.isAppOfArity ``OracleAdv.Timed.StepTimeBound 5 then some (e.getArg! 3) else none

/-- Constants read as tree structure, never unfolded. -/
def structural : List Name :=
  [``Prod.mk, ``Prod.fst, ``Prod.snd, ``ite, ``dite, ``SPTree.Timed.bind,
    ``SPTree.Timed.map, ``SPTree.Timed.delay, ``SPTree.Timed.stepTime, ``SPTree.Timed.time,
    ``OracleAdv.Timed.bind, ``OracleAdv.Timed.delay, ``OracleAdv.Timed.TimeBound,
    ``OracleAdv.Timed.StepTimeBound]

/-- Whether the body of the definition `n` is visible and not recursive. -/
def unfoldableDef (n : Name) : MetaM Bool := do
  let env ← getEnv
  if structural.contains n then return false
  if env.contains (n ++ `_sunfold) then return false
  let some (.defnInfo d) := env.find? n | return false
  let rec_ := d.value.find? fun
    | .const m _ => m == ``WellFounded.fix || m.lastComponentAsString == "brecOn"
    | _ => false
  return rec_.isNone

/-- Whether the head of the tree `x` is a constructor or a constant read as tree structure:
the subtrees of such a root are below the root, where the time theorems of the environment
are sources. -/
def structuralRoot (x : Expr) : MetaM Bool := do
  let some n := x.getAppFn.constName? | return false
  if structural.contains n then return true
  return (← getEnv).find? n matches some (.ctorInfo _)

/-- The heartbeat budget, in thousands, of one reduction or case split of the procedure. -/
def stepHeartbeats : Nat := 50000

/-- `x` under its own budget of `stepHeartbeats` heartbeats (at most the enclosing budget);
`none`, with the state restored, when it fails or exceeds the budget. An interrupt is passed
on. -/
def capped {α : Type} (x : MetaM α) : MetaM (Option α) := do
  let s ← saveState
  let cap (c : Core.Context) : Core.Context :=
    let m := if c.maxHeartbeats == 0 then stepHeartbeats * 1000
      else min c.maxHeartbeats (stepHeartbeats * 1000)
    { c with maxHeartbeats := m }
  tryCatchRuntimeEx
    (withCurrHeartbeats <| withTheReader Core.Context cap (some <$> x))
    fun e => do
      if e.isInterrupt then throw e
      s.restore
      return none

/-- `whnfR e` under the budget of `capped`; `e` itself when the budget is exceeded. -/
def whnfC (e : Expr) : MetaM Expr := do
  return (← capped (whnfR e)).getD e

/-- `e` with every `let` and `have` binder replaced by its value (zeta-normal form). -/
def zetaAll (e : Expr) : CoreM Expr :=
  Core.transform e (pre := fun e => match e with
    | .letE _ _ v b _ => return .visit (b.instantiate1 v)
    | _ => return .continue)

/-- The tree `e` with its head definition unfolded, then reduced by `whnfR`, under the budget
of `capped`. Its inner `let` and `have` binders are kept; `liftLets` binds them in the
context. -/
def unfoldTree? (e : Expr) : MetaM (Option Expr) := do
  let some n := e.getAppFn.constName? | return none
  unless ← unfoldableDef n do return none
  let r ← capped do
    let some e' ← withDefault (unfoldDefinition? e) | return none
    return some (← whnfR e'.headBeta)
  return r.join

/-- The major premise of an application of a recursor or `casesOn`. -/
def recMajorArg? (e : Expr) : MetaM (Option Expr) := do
  let some n := e.getAppFn.constName? | return none
  let some info := (← getEnv).find? n | return none
  let idx? ← match info with
    | .recInfo r => pure (some r.getMajorIdx)
    | _ =>
      if isCasesOnRecursor (← getEnv) n then
        let ind ← getConstInfoInduct n.getPrefix
        pure (some (ind.numParams + 1 + ind.numIndices))
      else pure none
  let some i := idx? | return none
  return e.getAppArgs[i]?

/-- The local variable that an application of a recursor or `casesOn` analyses, when it is
one. -/
def recMajor? (e : Expr) : MetaM (Option FVarId) := do
  let some a ← recMajorArg? e | return none
  return if a.isFVar then some a.fvarId! else none

/-- The target of `g` with the subterm `x` replaced by the definitionally equal `x'`. -/
def replaceIn (g : MVarId) (x x' : Expr) : MetaM MVarId := do
  if x == x' then return g
  let t ← instantiateMVars (← g.getType)
  g.replaceTargetDefEq (t.replace fun e => if e == x then some x' else none)

/-- Apply the rule lemma `n` to `g`: its conclusion is unified with the target at reducible
transparency, each term of `hints` is assigned to the first unassigned argument whose type it
has, and the unassigned premises are returned. `none` when the rule does not apply. -/
def applyRule (g : MVarId) (n : Name) (hints : List Expr := []) :
    MetaM (Option (List MVarId)) := g.withContext do
  let s ← saveState
  let e ← mkConstWithFreshMVarLevels n
  let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType e)
  unless ← withReducible (isDefEq concl (← g.getType)) do
    s.restore
    return none
  for pf in hints do
    let pty ← inferType pf
    let mut done := false
    for m in ms do
      if done then break
      if ← m.mvarId!.isAssigned then continue
      if ← isDefEq (← inferType m) pty then
        m.mvarId!.assign pf
        done := true
    unless done do
      s.restore
      return none
  let mut gs := []
  for m in ms do
    let m := m.mvarId!
    unless ← m.isAssigned do
      unless ← isProp (← m.getType) do
        s.restore
        return none
      gs := gs ++ [m]
  g.assign (mkAppN e ms)
  return some gs

/-- The applications in `e` without loose bound variables. -/
partial def appsOf (e : Expr) (acc : Array Expr) : Array Expr :=
  match e with
  | .app f a =>
    let acc := if e.hasLooseBVars then acc else acc.push e
    appsOf a (appsOf f acc)
  | .mdata _ b => appsOf b acc
  | .lam _ t b _ => appsOf b (appsOf t acc)
  | .forallE _ t b _ => appsOf b (appsOf t acc)
  | .proj _ _ b =>
    let acc := if e.hasLooseBVars then acc else acc.push e
    appsOf b acc
  | _ => acc

/-- The pair `y` of a first projection `y.1`, as an application of `Prod.fst` or as a
primitive projection. -/
def fstOf? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``Prod.fst 3 then some e.appArg!
  else match e with
    | .proj ``Prod 0 y => some y
    | _ => none

/-- The pair `y` of a second projection `y.2`, as an application of `Prod.snd` or as a
primitive projection. -/
def sndOf? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``Prod.snd 3 then some e.appArg!
  else match e with
    | .proj ``Prod 1 y => some y
    | _ => none

/-- The first projection `o` with its pair replaced by `y`. -/
def withFstArg (o y : Expr) : Expr :=
  match o with
  | .proj n i _ => .proj n i y
  | _ => mkApp3 o.getAppFn (o.getArg! 0) (o.getArg! 1) y

/-- Bounded atoms: for every subterm `f a` of the target and every local hypothesis
`∀ x, f x ≤ b` without propositional premises, the instance `f a ≤ b[a/x]` is added to the
context. -/
def addBoundedAtoms (g : MVarId) : MetaM MVarId := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let subs := appsOf tgt #[]
  let mut g := g
  let mut added : Array Expr := #[]
  for ld in (← getLCtx) do
    if ld.isImplementationDetail then continue
    let ty ← instantiateMVars ld.type
    unless ty.isForall do continue
    let s0 ← saveState
    let (ms0, _, body0) ← forallMetaTelescopeReducing ty
    let some (pat, _) := natLe? body0 | s0.restore; continue
    let hd := pat.getAppFn
    let nargs := pat.getAppNumArgs
    let hasProp ← ms0.anyM fun m => do isProp (← inferType m)
    s0.restore
    if hasProp || !(hd.isConst || hd.isFVar || hd.isProj) then continue
    for s in subs do
      unless s.getAppNumArgs == nargs && s.getAppFn == hd do continue
      let s1 ← saveState
      let (ms, _, body) ← forallMetaTelescopeReducing ty
      let some (l, _) := natLe? body | s1.restore; continue
      if ← isDefEq l s then
        let pf ← instantiateMVars (mkAppN ld.toExpr ms)
        if pf.hasExprMVar then
          s1.restore
          continue
        let pty ← instantiateMVars (← inferType pf)
        s1.restore
        if added.contains pty then continue
        added := added.push pty
        let (_, g') ← (← g.assert `hb pty pf).intro1P
        g := g'
      else
        s1.restore
  return g

/-- The invariant `m.property` of every subterm `↑m` of the target, added to the context. -/
def addSubtypeFacts (g : MVarId) : MetaM MVarId := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let mut g := g
  let mut seen : Array Expr := #[]
  for s in appsOf tgt #[] do
    unless s.isAppOfArity ``Subtype.val 3 do continue
    let m := s.appArg!
    if seen.contains m then continue
    seen := seen.push m
    let pf ← mkAppM ``Subtype.property #[m]
    let pty ← instantiateMVars (← inferType pf)
    let (_, g') ← (← g.assert `hs pty.headBeta pf).intro1P
    g := g'
  return g

/-- Close an arithmetic leaf by `omega`, then (unless `omegaOnly`) `linarith`, then
`nlinarith`, after adding the bounded atoms and the invariants of subtype values. -/
def closeArithCore (g : MVarId) (omegaOnly : Bool := false) : TacticM Unit := do
  let g ← addBoundedAtoms g
  let g ← addSubtypeFacts g
  let om ← `(tactic| omega)
  let li ← `(tactic| linarith)
  let nl ← `(tactic| nlinarith)
  let tacs := if omegaOnly then #[om] else #[om, li, nl]
  for tac in tacs do
    let s ← saveState
    try
      setGoals [g]
      evalTactic tac
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()
    s.restore
  throwError "time_bound: arithmetic leaf not closed{indentExpr (← g.getType)}"

/-- The constants `s.t` for the tags `t` and the trailing parts `s` of the name `p` (its last
component, its last two, and so on), each resolved in the current namespaces and the open
declarations: the companion theorems of a definition `p` stated in another namespace than
`p`, as `simImpl.timeBound` in namespace `FOTransform` of `FOTransformU.simImpl.timed`. -/
def resolvedCompanions (p : Name) (tags : List Name) : CoreM (List Name) := do
  let comps := p.components
  let mut out : List Name := []
  for i in [0:comps.length] do
    let s := (comps.drop (comps.length - 1 - i)).foldl (· ++ ·) Name.anonymous
    for t in tags do
      for (c, fields) in ← resolveGlobalName (s ++ t) do
        if fields.isEmpty && (← getEnv).contains c && !out.contains c then
          out := out ++ [c]
  return out

/-- The theorems `N.timeBound_timed`, `N.timeBound` of the definition `N.timed` at the head
of `x`, `M.timeBound` of a head `M`, and `Ns.timeBound_f` of a combinator `Ns.f`
(`OracleAdv.Timed.timeBound_simulate` of `OracleAdv.Timed.simulate`). -/
def envSources (x : Expr) : MetaM (Array Expr) := do
  let x ← zetaReduce x
  let some n := x.getAppFn.constName? | return #[]
  let last := n.lastComponentAsString
  let cands :=
    (if last == "timed" then
      [n.getPrefix ++ `timeBound_timed, n.getPrefix ++ `timeBound] else []) ++
      [n ++ `timeBound, Name.str n.getPrefix ("timeBound_" ++ last)]
  let env ← getEnv
  let mut out := cands.filter env.contains
  if last == "timed" then
    for c in ← resolvedCompanions n.getPrefix [`timeBound_timed, `timeBound] do
      unless out.contains c do out := out ++ [c]
  out.toArray.mapM mkConstWithFreshMVarLevels

/-- Close the proposition `mid` from the context: a local hypothesis whose type unifies with
it, or, for `∀ x, l ≤ ?r` with `?r` unassigned and independent of `x`, reflexivity. -/
def closeByContext (mid : MVarId) : MetaM Bool := mid.withContext do
  let ty ← instantiateMVars (← mid.getType)
  for ld in (← getLCtx) do
    if ld.isImplementationDetail then continue
    let s ← saveState
    if ← isDefEq ty ld.type then
      mid.assign ld.toExpr
      return true
    s.restore
  let s ← saveState
  let ok ← forallTelescopeReducing ty fun xs body => do
    let some (l, r) := natLe? body | return false
    unless (← instantiateMVars r).getAppFn.isMVar do return false
    unless ← isDefEq r l do return false
    mid.assign (← mkLambdaFVars xs (← mkAppM ``Nat.le_refl #[l]))
    return true
  unless ok do s.restore
  return ok

/-- A proof of the query bound `body` (`A.erase.IsQueryBound ?q`) of the adversary `A = y.2`
of a costed definition `y = N.timed …` by the theorem `N.isQueryBound_erase`, found by name as
the time theorems of `envSources` are, with its propositional premises closed by the
context. -/
def queryBoundSource (body A : Expr) : MetaM (Option Expr) := do
  let some y := sndOf? A | return none
  let y ← zetaReduce y
  let some n := y.getAppFn.constName? | return none
  unless n.lastComponentAsString == "timed" do return none
  let exact := n.getPrefix ++ `isQueryBound_erase
  let mut names := if (← getEnv).contains exact then [exact] else []
  for c in ← resolvedCompanions n.getPrefix [`isQueryBound_erase] do
    unless names.contains c do names := names ++ [c]
  for c in names do
    let s ← saveState
    let e ← mkConstWithFreshMVarLevels c
    let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType e)
    if ← isDefEq concl body then
      let mut ok := true
      for m in ms do
        let mid := m.mvarId!
        if ← mid.isAssigned then continue
        unless ← isProp (← mid.getType) do continue
        unless ← closeByContext mid do
          ok := false
          break
      let pf ← instantiateMVars (mkAppN e ms)
      if ok && !pf.hasExprMVar then return some pf
    s.restore
  return none

/-- The lemmas `f.timedCost_eq`, `f.timedCost_le` of the registered cost `f.timedCost`. -/
def costLemmas (n : Name) : MetaM (Array Expr) := do
  match n with
  | .str p s =>
    let env ← getEnv
    [Name.str p (s ++ "_eq"), Name.str p (s ++ "_le")].filter env.contains
      |>.toArray.mapM mkConstWithFreshMVarLevels
  | _ => return #[]

/-- Registered costs: for every subterm `f.timedCost a` of the target, the instance at `a` of
`f.timedCost_eq` (an equation) or `f.timedCost_le` (a bound), with its premises closed by
`closeByContext`, is added to the context. -/
def addCostFacts (g : MVarId) : MetaM MVarId := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let mut g := g
  let mut added : Array Expr := #[]
  for s in appsOf tgt #[] do
    let some n := s.getAppFn.constName? | continue
    unless n.lastComponentAsString == "timedCost" do continue
    for c in ← costLemmas n do
      let st ← saveState
      let (ms, _, body) ← forallMetaTelescopeReducing (← inferType c)
      let lhs? := if body.isAppOfArity ``Eq 3 then some (body.getArg! 1)
        else (natLe? body).map (·.1)
      let some l := lhs? | st.restore; continue
      unless ← isDefEq l s do
        st.restore
        continue
      let mut ok := true
      for m in ms do
        let mid := m.mvarId!
        if ← mid.isAssigned then continue
        unless ← isProp (← mid.getType) do continue
        unless ← closeByContext mid do
          ok := false
          break
      let pf ← instantiateMVars (mkAppN c ms)
      if !ok || pf.hasExprMVar then
        st.restore
        continue
      let pty ← instantiateMVars (← inferType pf)
      if added.contains pty then continue
      added := added.push pty
      let (_, g') ← (← g.assert `hc pty pf).intro1P
      g := g'
  return g

/-- The costed bind `(ret a).bind f` reduced by the first equation of `SPTree.Timed.bind` to
`f a`, when its tree is syntactically a `ret` leaf. -/
def bindOfCtor? (x : Expr) : Option Expr :=
  let a := (x.getArg! 2).consumeMData
  if a.isAppOfArity ``SPTree.Timed.ret 2 then some (mkApp (x.getArg! 3) a.appArg!).headBeta
  else none

/-- The step cost `x.1` of a pair `x` whose head definition unfolds to a pair, replaced by the
first component of that pair, in the target. -/
def reduceStepCosts (g : MVarId) : MetaM MVarId := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let tgt' ← Meta.transform tgt (post := fun e => do
    let some y := fstOf? e | return .continue
    let mut x ← whnfC y
    for _ in [0:8] do
      if x.isAppOfArity ``Prod.mk 4 then break
      if x.isAppOf ``SPTree.Timed.delay || x.isAppOf ``OracleAdv.Timed.delay then
        match ← withDefault (unfoldDefinition? x) with
        | some x' => x ← whnfC x'.headBeta
        | none => break
      else if x.isAppOfArity ``SPTree.Timed.bind 4 then
        -- a costed bind of a tree whose root reduces to a constructor: one step of `bind`
        match bindOfCtor? x with
        | some x' => x := x'
        | none => break
      else
        match ← unfoldTree? x with
        | some x' => x := x'
        | none => break
    if x.isAppOfArity ``Prod.mk 4 then return .visit (x.getArg! 2)
    return .continue)
  if tgt' == tgt then return g
  g.replaceTargetDefEq tgt'

/-- The component `i` of the pair `y` when `y` is syntactically a pair. -/
def pairComponent? (y : Expr) (i : Nat) : Option Expr :=
  if y.isAppOfArity ``Prod.mk 4 then some (y.getArg! (2 + i)) else none

/-- A projection of a pair, applied to arguments: `(a, b).1 xs` is `a xs`, `(a, b).2 xs` is
`b xs`, beta-reduced. -/
def reduceProjApp? (e : Expr) : Option Expr :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn with
  | .proj ``Prod i y => (pairComponent? y i).map fun c => (mkAppN c args).headBeta
  | .const n _ =>
    if (n == ``Prod.fst || n == ``Prod.snd) && args.size ≥ 3 then
      let i := if n == ``Prod.fst then 0 else 1
      (pairComponent? args[2]! i).map fun c => (mkAppN c args[3:]).headBeta
    else none
  | _ => none

/-- Case analysis on a local variable, not a `let` variable, that a recursor or `casesOn` in
`x` analyses; `none` when there is none. -/
def recCases? (g : MVarId) (x : Expr) : MetaM (Option (List MVarId)) := g.withContext do
  for s in appsOf x #[] do
    let some a ← recMajorArg? s | continue
    -- a major premise `p.1` (a chain of pair projections of `p`): case analysis on `p`
    let mut r := a
    for _ in [0:16] do
      match fstOf? r <|> sndOf? r with
      | some y => r := y
      | none => break
    unless r.isFVar do continue
    let fv := r.fvarId!
    if ← fv.isLetVar then continue
    let some subgoals ← capped (g.cases fv) | continue
    return some (subgoals.toList.map (·.mvarId))
  return none

/-- An application with a constructor argument, reduced: a recursor or `casesOn` on a
constructor by iota reduction, and a number-valued application of a definition to its value
when that is a numeral (`Sum.elim (fun _ => 1) (fun _ => 0) (.inl q)` to `1`). -/
def reduceCtorArg? (e : Expr) : MetaM (Option Expr) := do
  let some n := e.getAppFn.constName? | return none
  if structural.contains n || e.hasLooseBVars then return none
  let env ← getEnv
  let isCtor (a : Expr) : Bool :=
    (a.getAppFn.constName?.bind env.find?) matches some (.ctorInfo _)
  if let some a ← recMajorArg? e then
    unless isCtor a do return none
    let r ← whnfC e
    return if r == e then none else some r
  unless e.getAppArgs.any isCtor do return none
  if env.find? n matches some (.ctorInfo _) then return none
  let some ty ← capped (inferType e) | return none
  unless ty.isConstOf ``Nat do return none
  -- one unfolding of the head, then reducible reduction (iota and matchers)
  let some (some r) ← capped (do
    let some e' ← withDefault (unfoldDefinition? e) | return none
    return some (← whnfR e'.headBeta)) | return none
  match r.nat? with
  | some k => return some (mkNatLit k)
  | none => match r.rawNatLit? with
    | some k => return some (mkNatLit k)
    | none => return none

/-- The target with projections of pairs (applied or not) and beta redexes reduced. -/
def reduceProjBeta (g : MVarId) : MetaM MVarId := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let tgt' ← Meta.transform tgt (post := fun e => do
    if e.isHeadBetaTarget then return .visit e.headBeta
    if let some e' := reduceProjApp? e then return .visit e'
    if let some e' ← reduceCtorArg? e then return .visit e'
    return .continue)
  if tgt' == tgt then return g
  g.replaceTargetDefEq tgt'

/-- The tree `(delay c x).2` read as `x.2`, repeatedly. -/
def sndThroughDelay (e : Expr) : MetaM Expr := do
  let mut e := e
  for _ in [0:8] do
    let some y := sndOf? e | return e
    unless y.isAppOfArity ``SPTree.Timed.delay 3 do return e
    e ← whnfC (← mkAppM ``Prod.snd #[y.appArg!])
  return e

/-- The root of a chain of pair projections. -/
partial def projRoot (e : Expr) : Expr :=
  match fstOf? e with
  | some y => projRoot y
  | none => match sndOf? e with
    | some y => projRoot y
    | none => e

/-- Case analysis on a Boolean local `b` that an `if b = true` of `x` tests, each case
simplified by `↓reduceIte`; `none` when there is no such local. -/
def boolCases? (g : MVarId) (x : Expr) : TacticM (Option (List MVarId)) := g.withContext do
  let cand := (appsOf x #[]).findSome? fun e =>
    if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then
      let c := e.getArg! 1
      if c.isAppOfArity ``Eq 3 && (c.getArg! 1).isFVar then some (c.getArg! 1) else none
    else none
  let some b := cand | return none
  unless (← whnfR (← inferType b)).isConstOf ``Bool do return none
  let s ← saveState
  let some subs ← capped (g.cases b.fvarId!) | return none
  let mut out : List MVarId := []
  for sg in subs do
    setGoals [sg.mvarId]
    try
      evalTactic (← `(tactic| simp only [Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]))
    catch _ => pure ()
    out := out ++ (← getGoals)
  if out.isEmpty && subs.isEmpty then
    s.restore
    return none
  return some out

/-- A leaf of an invariant: projections of pairs reduced, binders introduced, then `omega`
with the bounded atoms of the context, else a case analysis on a Boolean local, an `if` or a
`match`. -/
partial def invLeaf (g : MVarId) (fuel : Nat) : TacticM Unit := g.withContext do
  if fuel == 0 then throwError "time_bound: depth bound reached"
  let g ← reduceProjBeta g
  let tgt ← instantiateMVars (← g.getType)
  if tgt.isForall then
    let (_, g') ← g.intro1P
    invLeaf g' (fuel - 1)
    return
  if tgt.isAppOfArity ``And 2 then
    let some gs ← applyRule g ``And.intro | throwError "time_bound: no conjunction"
    for g' in gs do invLeaf g' (fuel - 1)
    return
  let s ← saveState
  try
    let g1 ← addBoundedAtoms g
    setGoals [g1]
    evalTactic (← `(tactic| omega))
    unless (← getUnsolvedGoals).isEmpty do throwError "time_bound: invariant leaf not closed"
  catch e =>
    s.restore
    if let some gs ← boolCases? g tgt then
      for g' in gs do invLeaf g' (fuel - 1)
      return
    if let some gs ← recCases? g tgt then
      for g' in gs do invLeaf g' (fuel - 1)
      return
    let some (some gs) ← capped (splitTarget? g) | throw e
    for g' in gs do invLeaf g' (fuel - 1)

/-! ### Let-bound values -/

/-- A linear bound over `ℕ`: a constant and atoms with their coefficients. -/
abbrev LinB := Nat × Array (Expr × Nat)

/-- The bound `a` with `k` times the atom `x` added. -/
def LinB.addAtom (a : LinB) (x : Expr) (k : Nat) : LinB :=
  match a.2.findIdx? (·.1 == x) with
  | some i => (a.1, a.2.modify i fun (y, j) => (y, j + k))
  | none => (a.1, a.2.push (x, k))

/-- The sum of two bounds. -/
def LinB.add (a b : LinB) : LinB :=
  b.2.foldl (fun acc (x, k) => acc.addAtom x k) (a.1 + b.1, a.2)

/-- The bound `a` multiplied by `k`. -/
def LinB.scale (k : Nat) (a : LinB) : LinB :=
  (k * a.1, a.2.map fun (x, j) => (x, k * j))

/-- The componentwise maximum of two bounds, a bound of both over `ℕ`. -/
def LinB.max (a b : LinB) : LinB :=
  b.2.foldl (fun acc (x, k) => match acc.2.findIdx? (·.1 == x) with
    | some i => (acc.1, acc.2.modify i fun (y, j) => (y, Nat.max j k))
    | none => (acc.1, acc.2.push (x, k))) (Nat.max a.1 b.1, a.2)

/-- The term `c + k₁ * x₁ + …` of a bound. -/
def LinB.toExpr (a : LinB) : MetaM Expr :=
  a.2.foldlM (init := mkNatLit a.1) fun acc (x, k) => do
    let t ← if k == 1 then pure x else mkAppM ``HMul.hMul #[mkNatLit k, x]
    mkAppM ``HAdd.hAdd #[acc, t]

/-- The natural number of a numeral. -/
def natNum? (e : Expr) : Option Nat :=
  match e.rawNatLit? with
  | some n => some n
  | none => e.nat?

/-- The linear form of a bound term: numerals, sums and products by numerals are read, every
other subterm is an atom. -/
partial def linOf (e : Expr) : LinB :=
  if let some n := natNum? e then (n, #[])
  else if e.isAppOfArity ``HAdd.hAdd 6 then (linOf (e.getArg! 4)).add (linOf (e.getArg! 5))
  else if e.isAppOfArity ``HMul.hMul 6 then
    match natNum? (e.getArg! 4) with
    | some k => (linOf (e.getArg! 5)).scale k
    | none => (0, #[(e, 1)])
  else (0, #[(e, 1)])

/-- The alternatives of a chain of pair projections applied to arguments: a projection of a
pair is reduced, a projection of an `if` is taken in each branch. -/
partial def projAlts (e : Expr) (fuel : Nat) : Array Expr := Id.run do
  if fuel == 0 then return #[e]
  let fn := e.getAppFn
  let args := e.getAppArgs
  let dec : Option (Nat × Expr × Array Expr × (Expr → Expr)) := match fn with
    | .proj ``Prod i y => some (i, y, args, fun y' => mkAppN (.proj ``Prod i y') args)
    | .const n _ =>
      if (n == ``Prod.fst || n == ``Prod.snd) && args.size ≥ 3 then
        let rest := args.extract 3 args.size
        some (if n == ``Prod.fst then 0 else 1, args[2]!, rest,
          fun y' => mkAppN (mkAppN fn (args.extract 0 2)) (#[y'] ++ rest))
      else none
    | _ => none
  let some (i, y, rest, rebuild) := dec | return #[e]
  let mut out := #[]
  for y' in projAlts y (fuel - 1) do
    let y' := y'.headBeta
    if y'.isAppOfArity ``Prod.mk 4 then
      out := out ++ projAlts (mkAppN (y'.getArg! (2 + i)) rest).headBeta (fuel - 1)
    else if y'.isAppOfArity ``ite 5 then
      out := out ++ projAlts (rebuild (y'.getArg! 3)) (fuel - 1) ++
        projAlts (rebuild (y'.getArg! 4)) (fuel - 1)
    else out := out.push (rebuild y')
  return out

/-- The bound `b[a/x]` of a local hypothesis `∀ x, l ≤ b` whose left side unifies with `e` at
reducible transparency. -/
def hypBound? (e : Expr) : MetaM (Option Expr) := do
  for ld in (← getLCtx) do
    if ld.isImplementationDetail then continue
    let ty ← instantiateMVars ld.type
    let s ← saveState
    let (ms, _, body) ← forallMetaTelescopeReducing ty
    let some (l, b) := natLe? body | s.restore; continue
    if ← ms.anyM fun m => do isProp (← inferType m) then s.restore; continue
    if ← withReducible (isDefEq l e) then
      let b ← instantiateMVars b
      s.restore
      unless b.hasExprMVar do return some b
    else s.restore
  return none

/-- The minor premises of a full application of a `casesOn` recursor; `none` for any other
term. -/
def casesOnAlts? (e : Expr) : MetaM (Option (Array Expr)) := do
  let some n := e.getAppFn.constName? | return none
  unless isCasesOnRecursor (← getEnv) n do return none
  let ind ← getConstInfoInduct n.getPrefix
  let first := ind.numParams + 1 + ind.numIndices + 1
  let args := e.getAppArgs
  unless args.size == first + ind.ctors.length do return none
  return some (args.extract first args.size)

/-- A proposed linear bound of the natural number `e`: sums, products by numerals, `if`
(the componentwise maximum of the branches), `match` and `casesOn` (the maximum of the
alternatives), projections of pairs and of `if`s, and the
bounds of local hypotheses `∀ x, l ≤ b` at the atoms. -/
partial def ubLin (e : Expr) (fuel : Nat) : MetaM (Option LinB) := do
  if fuel == 0 then return none
  let e := e.headBeta
  if let some n := natNum? e then return some (n, #[])
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let some a ← ubLin (e.getArg! 4) (fuel - 1) | return none
    let some b ← ubLin (e.getArg! 5) (fuel - 1) | return none
    return some (a.add b)
  if e.isAppOfArity ``HMul.hMul 6 then
    if let some k := natNum? (e.getArg! 4) then
      return (← ubLin (e.getArg! 5) (fuel - 1)).map (·.scale k)
  -- an `if a = a` is its first branch
  if (e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5) then
    let c := e.getArg! 1
    if c.isAppOfArity ``Eq 3 && c.getArg! 1 == c.getArg! 2 then
      let mut br := e.getArg! 3
      if e.isAppOfArity ``dite 5 then
        let u ← getLevel (c.getArg! 0)
        br := mkApp br (mkApp2 (mkConst ``Eq.refl [u]) (c.getArg! 0) (c.getArg! 1))
      return ← ubLin br (fuel - 1)
  if e.isAppOfArity ``ite 5 then
    let some a ← ubLin (e.getArg! 3) (fuel - 1) | return none
    let some b ← ubLin (e.getArg! 4) (fuel - 1) | return none
    return some (a.max b)
  -- `dite` and `match`: the maximum over the alternatives, whose bounds do not depend on the
  -- fields of the alternative
  let alts? ← if e.isAppOfArity ``dite 5 then pure (some #[e.getArg! 3, e.getArg! 4])
    else match ← matchMatcherApp? e with
      | some m => pure (some m.alts)
      | none => casesOnAlts? e
  if let some alts := alts? then
    let mut acc : Option LinB := none
    for alt in alts do
      let r ← lambdaTelescope alt fun xs b => do
        let some l ← ubLin b (fuel - 1) | return none
        if l.2.any fun (a, _) => xs.any fun x => a.containsFVar x.fvarId! then return none
        return some l
      let some l := r | return none
      acc := some (match acc with | some m => m.max l | none => l)
    return acc
  let alts := projAlts e 16
  unless alts.size == 1 && alts[0]! == e do
    let mut acc : Option LinB := none
    for a in alts do
      let some l ← ubLin a (fuel - 1) | return none
      acc := some (match acc with | some m => m.max l | none => l)
    return acc
  if let some b ← hypBound? e then return some (linOf b)
  if e.isFVar && (← whnfR (← inferType e)).isConstOf ``Nat then return some (0, #[(e, 1)])
  return none

/-- The cost companions of a value `e` of type `ty`: the chains of pair projections of `e`
whose type is `ℕ` (with `none`) or `X → ℕ` (with `some X`). -/
partial def compPaths (e ty : Expr) (d : Nat) : MetaM (Array (Expr × Option Expr)) := do
  if d == 0 then return #[]
  let ty ← whnfR ty
  if ty.isAppOfArity ``Prod 2 then
    let a ← compPaths (← mkAppM ``Prod.fst #[e]) (ty.getArg! 0) (d - 1)
    let b ← compPaths (← mkAppM ``Prod.snd #[e]) (ty.getArg! 1) (d - 1)
    return a ++ b
  if ty.isConstOf ``Nat then return #[(e, none)]
  if let .forallE _ X cod _ := ty then
    if !cod.hasLooseBVars && (← whnfR cod).isConstOf ``Nat then return #[(e, some X)]
  return #[]

/-- The statement `∀ u, p u ≤ B` (with `some X`, `u : X`) or `p ≤ B` (with `none`) for the
companion `p` of a let-bound local whose value form is `pv`, with the bound `B` proposed by
`ubLin` on `pv u`, independent of `u`. -/
def companionBound? (p pv : Expr) (X? : Option Expr) : MetaM (Option Expr) := do
  match X? with
  | some X => withLocalDeclD `u X fun u => do
    let some lin ← ubLin (mkApp pv u) 64 | return none
    if lin.2.any (·.1.containsFVar u.fvarId!) then return none
    let b ← lin.toExpr
    return some (← mkForallFVars #[u] (← mkAppM ``LE.le #[mkApp p u, b]))
  | none =>
    let some lin ← ubLin pv 64 | return none
    return some (← mkAppM ``LE.le #[p, ← lin.toExpr])

/-- Bounds of the cost companions of the let-bound local `x := v`, added to the context: for
each companion `π x` (`compPaths`), the statement of `companionBound?` on `π v`, proved by
`invLeaf` on `π v u`, with the bounds of the locals bound before `x` in the context. A
companion whose bound is not found or not proved gets no fact. -/
def addLetFacts (g : MVarId) (x : FVarId) : TacticM MVarId := g.withContext do
  let some v ← x.getValue? | return g
  let xe := mkFVar x
  let paths ← compPaths xe (← x.getType) 8
  let mut g := g
  for (p, X?) in paths do
    let g0 := g
    let r : Option MVarId ← g0.withContext do
      let some stmt ← companionBound? p (p.replaceFVar xe v) X? | return none
      let s ← saveState
      let m ← mkFreshExprMVar stmt
      try
        let g1 ← m.mvarId!.replaceTargetDefEq (stmt.replaceFVar xe v)
        invLeaf g1 32
        let pf ← instantiateMVars m
        let (_, g') ← (← g0.assert `hf stmt pf).intro1P
        return some g'
      catch _ =>
        s.restore
        return none
    if let some g' := r then g := g'
  return g

/-- Whether a `let` of type `t` is inlined rather than bound: costed trees and step-prefixed
trees (read structurally by the rules), natural numbers (read by `omega`) and proofs. -/
def inlineType (t : Expr) : MetaM Bool := do
  if (t.find? fun e => e.isConstOf ``SPTree.Timed || e.isConstOf ``OracleAdv.Timed).isSome then
    return true
  if (← whnfR t).isConstOf ``Nat then return true
  isProp t

/-- Whether a let-bound value is an atom, inlined rather than bound. -/
def atomicVal (v : Expr) : Bool :=
  v.isFVar || v.isConst || v.isLit || v.isSort || (natNum? v).isSome

/-- The number of nodes of `e`, at most `cap`. -/
partial def sizeCapped (e : Expr) (cap : Nat) : Nat :=
  if cap == 0 then 0 else
  match e with
  | .app f a => let n := sizeCapped f (cap - 1); n + 1 + sizeCapped a (cap - 1 - min n (cap - 1))
  | .lam _ t b _ | .forallE _ t b _ =>
    let n := sizeCapped t (cap - 1); n + 1 + sizeCapped b (cap - 1 - min n (cap - 1))
  | .letE _ t v b _ => sizeCapped t (cap - 1) + sizeCapped v (cap - 1) + sizeCapped b (cap - 1)
  | .mdata _ b => sizeCapped b cap
  | .proj _ _ b => 1 + sizeCapped b (cap - 1)
  | _ => 1

/-- The `let` and `have` nodes of `e` whose value and type have no loose bound variables. -/
def closedLets (e : Expr) : MetaM (Array Expr) := do
  let r ← IO.mkRef #[]
  e.forEach' fun s => do
    if let .letE _ t v _ _ := s then
      if !t.hasLooseBVars && !v.hasLooseBVars then r.modify (·.push s)
    return true
  r.get

/-- The goal `g` with the `let` and `have` binders of its target that do not depend on bound
variables taken out of the target: a binder of a tree, a number, a proof or an atom is inlined;
any other binder, the one with the smallest value first, becomes a let-bound local `x := v` of
the context, every binder of the same value and every occurrence of the value in the target are
replaced by `x`, and the bounds of the cost companions of `x` are added (`addLetFacts`). Each
value is thus read once, and the companions of later values are bounded from those of earlier
ones. -/
partial def liftLets (g : MVarId) (fuel : Nat := 64) : TacticM MVarId := g.withContext do
  if fuel == 0 then return g
  let tgt ← instantiateMVars (← g.getType)
  unless (tgt.find? Expr.isLet).isSome do return g
  let lets ← closedLets tgt
  if lets.isEmpty then return g
  let mut inl : Array Expr := #[]
  let mut best : Option (Expr × Nat) := none
  for l in lets do
    let .letE _ t v _ _ := l | continue
    if atomicVal v || (← inlineType t) then
      inl := inl.push l
    else
      let n := sizeCapped v 100000
      if best.all (n < ·.2) then best := some (l, n)
  if !inl.isEmpty then
    let tgt' ← Core.transform tgt (pre := fun e => match e with
      | .letE _ _ v b _ =>
        return if inl.contains e then .visit (b.instantiate1 v) else .continue
      | _ => return .continue)
    return ← liftLets (← g.replaceTargetDefEq tgt') (fuel - 1)
  let some (.letE n t v _ _, _) := best | return g
  let g1 ← g.define n t v
  let (x, g2) ← g1.intro1P
  let g4 ← g2.withContext do
    let xe := mkFVar x
    let tgt2 ← instantiateMVars (← g2.getType)
    let tgt3 ← Core.transform tgt2 (pre := fun e => do
      if let .letE _ _ v' b _ := e then
        if v' == v then return .visit (b.instantiate1 xe)
      if e == v then return .done xe
      return .continue)
    let g3 ← g2.replaceTargetDefEq tgt3
    addLetFacts g3 x
  liftLets g4 (fuel - 1)

/-- The summands of a sum, through products by numerals. -/
partial def linAtoms (e : Expr) (acc : Array Expr) : Array Expr :=
  if e.isAppOfArity ``HAdd.hAdd 6 then linAtoms (e.getArg! 5) (linAtoms (e.getArg! 4) acc)
  else if e.isAppOfArity ``HMul.hMul 6 && (natNum? (e.getArg! 4)).isSome then
    linAtoms (e.getArg! 5) acc
  else acc.push e

/-- Bounds of the case distinctions of an arithmetic leaf `l ≤ B`, added to the context: for
each summand `t` of `l` that is an `if`, an `if h :` or a `match`, the statement `t ≤ U` with
the bound `U` proposed by `ubLin` (the componentwise maximum of the bounds of the branches),
proved by `invLeaf` on `t ≤ U` alone. The leaf is then closed by linear arithmetic over these
summands as atoms, and its case distinctions are split one summand at a time, never all
together. -/
def addCaseFacts (g : MVarId) : TacticM MVarId := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let some (l, _) := natLe? tgt | return g
  let mut g := g
  let mut seen : Array Expr := #[]
  for t in linAtoms l #[] do
    unless t.isAppOfArity ``ite 5 || t.isAppOfArity ``dite 5 ||
      (← matchMatcherApp? t).isSome do continue
    if t.hasLooseBVars || t.hasExprMVar || seen.contains t then continue
    seen := seen.push t
    let some lin ← ubLin t 64 | continue
    let stmt ← mkAppM ``LE.le #[t, ← lin.toExpr]
    let s ← saveState
    let m ← mkFreshExprMVar stmt
    try
      invLeaf m.mvarId! 32
      let (_, g') ← (← g.assert `hi stmt (← instantiateMVars m)).intro1P
      g := g'
    catch _ => s.restore
  return g

/-- The summands of a sum. -/
partial def summands (e : Expr) (acc : Array Expr) : Array Expr :=
  if e.isAppOfArity ``HAdd.hAdd 6 then summands (e.getArg! 5) (summands (e.getArg! 4) acc)
  else acc.push e

/-- An arithmetic leaf `l ≤ B` with a summand `t.time` of a tree that the rules can consume
(a second projection or a definition with a visible body): the leaf read as the path `l`
without the summand followed by `t.time` (`arith_time`). -/
def timeAtom? (g : MVarId) : TacticM (Option MVarId) := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let some (l, b) := natLe? tgt | return none
  for s in summands l #[] do
    unless s.isAppOfArity ``SPTree.Timed.time 2 do continue
    let t := s.appArg!
    unless (sndOf? t).isSome || (← unfoldTree? t).isSome do continue
    let q := l.replace fun e => if e == s then some (mkNatLit 0) else none
    let st ← saveState
    try
      let gs ← g.apply (mkApp4 (mkConst ``arith_time) l q s b)
      let [he, h] := gs | throwError "time_bound: arith_time"
      setGoals [he]
      evalTactic (← `(tactic| omega))
      unless (← getUnsolvedGoals).isEmpty do throwError "time_bound: arith_time"
      return some h
    catch _ => st.restore
  return none

/-- The slack ladder of an inferred companion bound `e u ≤ c + N`. -/
def invSlack : List Nat := [0, 1, 2, 3, 4, 6, 8, 12, 16]

/-- Candidate leaf invariants of a bind `A.bind f` over values of type `α`: for every
companion `π a : X → ℕ` that the continuation `f a` reads (a chain of pair projections of the
bound value `a`) and every local hypothesis `∀ x : X, h x ≤ c`, the predicates
`fun a => ∀ u, π a u ≤ c + N` for `N` in `invSlack`, one list per companion and hypothesis. -/
def invCandidates (α f : Expr) : MetaM (Array (Array Expr)) := do
  withLocalDeclD `a α fun a => do
    let body ← zetaAll (← instantiateMVars (mkApp f a).headBeta)
    let mut paths : Array (Expr × Expr) := #[]
    for s in appsOf body #[] do
      unless (fstOf? s).isSome || (sndOf? s).isSome do continue
      unless projRoot s == a do continue
      if paths.any (·.1 == s) then continue
      let ty ← whnfR (← inferType s)
      let .forallE _ X cod _ := ty | continue
      if cod.hasLooseBVars then continue
      unless (← whnfR cod).isConstOf ``Nat do continue
      paths := paths.push (s, X)
    let mut out := #[]
    for (p, X) in paths do
      for ld in (← getLCtx) do
        if ld.isImplementationDetail || ld.fvarId == a.fvarId! then continue
        let ty ← instantiateMVars ld.type
        let .forallE _ X' b _ := ty | continue
        let some (l, r) := natLe? b | continue
        if r.hasLooseBVars then continue
        unless l.hasLooseBVars do continue
        -- a companion binder `h x`, or a companion `π h x` of a binder `h` that is not let-bound
        let root := if l.isApp then projRoot l.appFn! else l
        let rootOk ← if root.isFVar then do pure !(← root.fvarId!.isLetVar) else pure false
        unless l.getAppFn.isFVar || rootOk do continue
        unless ← isDefEq X X' do continue
        let mut ladder := #[]
        for n in invSlack do
          let q ← withLocalDeclD `u X fun u => do
            let bound ← mkAppM ``HAdd.hAdd #[r, mkNatLit n]
            mkForallFVars #[u] (← mkAppM ``LE.le #[(mkApp p u).headBeta, bound])
          ladder := ladder.push (← mkLambdaFVars #[a] q)
        out := out.push ladder
    return out

/-- The proposition `a ≤ b` over `ℕ`. -/
def mkNatLe (a b : Expr) : Expr :=
  mkApp4 (mkConst ``LE.le [Level.zero]) (mkConst ``Nat) (mkConst ``instLENat) a b

/-- Whether `m₁` and `m₂` are applications of the same matcher to the same discriminants,
without arguments after their alternatives. -/
def sameMatch (m₁ m₂ : MatcherApp) : MetaM Bool := do
  unless m₁.matcherName == m₂.matcherName && m₁.discrs.size == m₂.discrs.size &&
    m₁.remaining.isEmpty && m₂.remaining.isEmpty && m₁.uElimPos?.isSome do return false
  for d₁ in m₁.discrs, d₂ in m₂.discrs do
    unless d₁ == d₂ do
      unless ← withReducible (isDefEq d₁ d₂) do return false
  return true

/-- The application `e` of a matcher reduced by iota at its pattern, beta-reduced; `e` when
it does not reduce. -/
def reduceMatch (e : Expr) : MetaM Expr := do
  match ← reduceMatcher? e with
  | .reduced e' => return e'.headBeta
  | _ => return e

/-- `g : a ≤ b` reduced by `rule` (`Nat.add_le_add`, `max_le_max`, `ite_le_ite_of`,
`ite_le_max_of`) to the comparisons of its parts; `none` when the conclusion of the rule does
not match the target. -/
def splitLe (g : MVarId) (rule : Name) : MetaM (Option (MVarId × MVarId)) := do
  let s ← saveState
  match ← applyRule g rule with
  | some [g₁, g₂] => return some (g₁, g₂)
  | _ =>
    s.restore
    return none

mutual

/-- `a ≤ b` by the structure of the two costs: reflexivity; two matches of the same
discriminants by `matchLe`; two sums by `Nat.add_le_add`, two maxima by `max_le_max`, an `if`
against the `if` on the same condition or the maximum of two branches by `ite_le_ite_of` or
`ite_le_max_of`, each with its parts compared; else `omega` with the bounded atoms of the
context. -/
partial def cmpLe (g : MVarId) (fuel : Nat) : TacticM Unit := g.withContext do
  if fuel == 0 then throwError "time_bound: depth bound reached"
  let tgt ← zetaAll (← instantiateMVars (← g.getType))
  let some (a, b) := natLe? tgt | throwError "time_bound: not a comparison{indentExpr tgt}"
  let a := a.headBeta
  let b := b.headBeta
  let g ← g.replaceTargetDefEq (mkNatLe a b)
  if a == b then
    g.assign (mkApp (mkConst ``Nat.le_refl) a)
    return
  if let some m₁ ← matchMatcherApp? a then
    let m₂? ← match ← matchMatcherApp? b with
      | some m₂ => do pure (if ← sameMatch m₁ m₂ then some m₂ else none)
      | none => pure none
    -- the matches compared by cases, or the match of `a` against the bound `b` by cases
    let s ← saveState
    try
      matchLe g m₁ m₂? b (fuel - 1)
      return
    catch _ => s.restore
  let rule? : Option Name :=
    if a.isAppOfArity ``HAdd.hAdd 6 && b.isAppOfArity ``HAdd.hAdd 6 then some ``Nat.add_le_add
    else if a.isAppOfArity ``Max.max 4 && b.isAppOfArity ``Max.max 4 then some ``max_le_max
    else if a.isAppOfArity ``ite 5 && b.isAppOfArity ``ite 5 && a.getArg! 1 == b.getArg! 1 then
      some ``ite_le_ite_of
    else if a.isAppOfArity ``ite 5 && b.isAppOfArity ``Max.max 4 then some ``ite_le_max_of
    else none
  if let some rule := rule? then
    let s ← saveState
    try
      if let some (g₁, g₂) ← splitLe g rule then
        cmpLe g₁ (fuel - 1)
        cmpLe g₂ (fuel - 1)
        return
    catch _ => pure ()
    s.restore
  -- a cost against a maximum: against one of its arguments
  if b.isAppOfArity ``Max.max 4 then
    for rule in [``le_max_of_le_left, ``le_max_of_le_right] do
      let s ← saveState
      try
        if let some [g₁] ← applyRule g rule then
          cmpLe g₁ (fuel - 1)
          return
      catch _ => pure ()
      s.restore
  closeArithCore (← addCostFacts g) (omegaOnly := true)

/-- `m₁ ≤ b` by the matcher of `m₁`: with the motive `fun ds => m₁[ds] ≤ m₂[ds]` when `b` is
the match `m₂` of the same matcher on the same discriminants, else `fun ds => m₁[ds] ≤ b`; at
each alternative the two sides are reduced at the pattern and compared by `cmpLe`. -/
partial def matchLe (g : MVarId) (m₁ : MatcherApp) (m₂? : Option MatcherApp) (b : Expr)
    (fuel : Nat) : TacticM Unit := g.withContext do
  let some pos := m₁.uElimPos? | throwError "time_bound: match without a motive universe"
  let motive ← forallBoundedTelescope (← inferType m₁.motive) m₁.discrs.size fun xs _ => do
    let rhs := match m₂? with
      | some m₂ => { m₂ with discrs := xs }.toExpr
      | none => b
    mkLambdaFVars xs (mkNatLe { m₁ with discrs := xs }.toExpr rhs)
  let lvls := m₁.matcherLevels.set! pos Level.zero
  let f := mkAppN (mkConst m₁.matcherName lvls.toList) (m₁.params ++ #[motive] ++ m₁.discrs)
  let mut fty ← inferType f
  let mut alts : Array Expr := #[]
  for _ in m₁.altNumParams do
    let .forallE _ d b _ ← whnfD fty | throwError "time_bound: matcher type"
    let mv ← mkFreshExprSyntheticOpaqueMVar d
    alts := alts.push mv
    fty := b.instantiate1 mv
  let pf := mkAppN f alts
  unless ← isDefEq (← inferType pf) (← g.getType) do
    throwError "time_bound: matcher motive"
  g.assign pf
  for mv in alts, n in m₁.altNumParams do
    let (_, g') ← mv.mvarId!.introN n
    g'.withContext do
      let tgt := (← instantiateMVars (← g'.getType)).headBeta
      let some (a, b) := natLe? tgt | throwError "time_bound: alternative"
      cmpLe (← g'.replaceTargetDefEq (mkNatLe (← reduceMatch a) (← reduceMatch b))) fuel

end

/-- An arithmetic leaf `l ≤ r` with a summand `m₁` of `l` and a summand `m₂` of `r` that are
matches of the same discriminants, `m₁ ≤ m₂` proved by `cmpLe`: the leaf
`∀ x₁ y₁ …, x₁ ≤ y₁ → … → l[xᵢ/m₁ᵢ] ≤ r[yᵢ/m₂ᵢ]` with its binders introduced, which proves
`l ≤ r` from these facts. `none` when no pair is compared. -/
def matchFacts (g : MVarId) : TacticM (Option MVarId) := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let some (l, r) := natLe? tgt | return none
  let rs := linAtoms r #[]
  let mut pairs : Array (Expr × Expr × Expr) := #[]
  for t in linAtoms l #[] do
    if t.hasLooseBVars || t.hasExprMVar || pairs.any (·.1 == t) then continue
    let some m₁ ← matchMatcherApp? t | continue
    for u in rs do
      if u.hasLooseBVars || u.hasExprMVar then continue
      let some m₂ ← matchMatcherApp? u | continue
      unless ← sameMatch m₁ m₂ do continue
      let s ← saveState
      let mv ← mkFreshExprMVar (mkNatLe t u)
      try
        cmpLe mv.mvarId! 64
        pairs := pairs.push (t, u, ← instantiateMVars mv)
        break
      catch _ => s.restore
  if pairs.isEmpty then return none
  let n := pairs.size
  let decls := (Array.range (2 * n)).map fun i =>
    (Name.mkSimple s!"m{i}", fun _ => pure (mkConst ``Nat))
  let stmt ← withLocalDeclsD decls fun xs => do
    let sub (side : Nat) (e : Expr) : Expr := e.replace fun e' =>
      match pairs.findIdx? fun p => (if side == 0 then p.1 else p.2.1) == e' with
      | some i => some xs[2 * i + side]!
      | none => none
    let mut body := mkNatLe (sub 0 l) (sub 1 r)
    for i in (List.range n).reverse do
      body := mkForall `h .default (mkNatLe xs[2 * i]! xs[2 * i + 1]!) body
    mkForallFVars xs body
  let G ← mkFreshExprSyntheticOpaqueMVar stmt
  let args := (pairs.foldl (fun acc p => acc.push p.1 |>.push p.2.1) #[]) ++ pairs.map (·.2.2)
  let pf := mkAppN G args
  unless ← isDefEq (← inferType pf) tgt do return none
  g.assign pf
  let (_, g') ← G.mvarId!.introN (3 * n)
  return some g'

/-- The target with each step cost `(A.bind fun y => (0, ret (h y))).1` of a costed bind whose
continuation returns at zero cost rewritten to `0` (`SPTree.Timed.bind_ret_fst`); the goal
itself when there is none. The rewrite runs only when the target has such a step cost, read
syntactically (a lambda continuation whose body is a pair with first component `0`), and
without `zeta`, so that the `let`s of the target are not unfolded. -/
def rewriteBindRet (g : MVarId) : TacticM MVarId := do
  let tgt ← instantiateMVars (← g.getType)
  let zeroRet (f : Expr) : Bool := match f with
    | .lam _ _ b _ => b.isAppOfArity ``Prod.mk 4 && (b.getArg! 2).nat? == some 0
    | _ => false
  let has := (tgt.find? fun e => match fstOf? e with
    | some y => y.isAppOfArity ``SPTree.Timed.bind 4 && zeroRet (y.getArg! 3)
    | none => false).isSome
  unless has do return g
  let s ← saveState
  try
    setGoals [g]
    evalTactic (← `(tactic| simp -zeta only [CatCrypt.Core.SPTree.Timed.bind_ret_fst]))
    match ← getUnsolvedGoals with
    | [g'] => return g'
    | _ =>
      s.restore
      return g
  catch _ =>
    s.restore
    return g

/-- The fact `(A.bind g).1 ≤ c` (`bind_fst_le`) for a costed bind `x = A.bind g` whose
continuation has step costs `(g a).1` with a linear bound `c` (`ubLin`) that does not depend on
`a`, the premise `∀ a, (g a).1 ≤ c` proved by `invLeaf`; `none` when `x` is not such a bind. -/
def bindFstFact? (x : Expr) : TacticM (Option Expr) := do
  unless x.isAppOfArity ``SPTree.Timed.bind 4 do return none
  let A := x.getArg! 2
  let k := x.getArg! 3
  let .forallE n d _ _ ← whnfR (← inferType k) | return none
  let some stmt ← withLocalDeclD n d fun a => do
      let e ← mkAppM ``Prod.fst #[(mkApp k a).headBeta]
      let some l ← ubLin ((reduceProjApp? e).getD e) 64 | return none
      if l.2.any fun (t, _) => t.containsFVar a.fvarId! then return none
      return some (← mkForallFVars #[a] (mkNatLe e (← l.toExpr)))
    | return none
  let s ← saveState
  let m ← mkFreshExprMVar stmt
  try
    invLeaf m.mvarId! 32
    return some (← mkAppM ``bind_fst_le #[A, ← instantiateMVars m])
  catch _ =>
    s.restore
    return none

mutual

/-- An arithmetic leaf: the step costs of pairs are reduced (and the projections and constructor
applications they expose, when a step cost was reduced), each remaining step cost `x.1` of a
costed tree is bounded by a source of `x` (a costed bind `A.bind g` without a source by a bound
of the step costs of `g`, `bindFstFact?`), the matches of the same discriminants on its two
sides are compared by cases (`matchFacts`), and `closeArithCore` closes the goal. -/
partial def closeArith (g : MVarId) (env : Bool) (fuel : Nat) : TacticM Unit := do
  let s0 ← saveState
  let g0 := g
  let g1 ← reduceProjBeta g
  let g2 ← reduceStepCosts g1
  let g2 ← if g2 == g1 then pure g2 else reduceProjBeta g2
  let g ← liftLets (← rewriteBindRet g2)
  let mut g := g
  let tgt ← g.withContext do instantiateMVars (← g.getType)
  let mut seen : Array Expr := #[]
  for s in appsOf tgt #[] do
    let some x := fstOf? s | continue
    if seen.contains x then continue
    seen := seen.push x
    let xty ← g.withContext do whnfR (← inferType x)
    let snd := if xty.isAppOfArity ``Prod 2 then xty.getArg! 1 else xty
    let kind? : Option (Kind × Name) :=
      if snd.isAppOf ``SPTree.Timed then some (.step, ``fst_le_of_stepTime)
      else if snd.isAppOf ``OracleAdv.Timed then some (.stb, ``fst_le_of_stb)
      else none
    let some (k, lem) := kind? | continue
    let g0 := g
    let r ← g0.withContext do
      match ← findSource k x env fuel with
      | some pf =>
        let fact ← mkAppM lem #[pf]
        let (_, g') ← (← g0.assert `hx (← inferType fact) fact).intro1P
        pure (some g')
      | none =>
        let some fact ← bindFstFact? x | pure none
        let (_, g') ← (← g0.assert `hx (← inferType fact) fact).intro1P
        pure (some g')
    if let some g' := r then g := g'
  g ← addCostFacts g
  -- the matches of the same discriminants on the two sides, compared by cases
  let sm ← saveState
  if let some gm ← matchFacts g then
    try
      closeArithCore gm (omegaOnly := true)
      return
    catch _ => sm.restore
  let gc ← addCaseFacts g
  let s ← saveState
  try
    closeArithCore gc (omegaOnly := true)
  catch _ =>
    s.restore
    -- case distinctions of the leaf before `linarith` and `nlinarith`, whose failed searches
    -- on a leaf that a split closes are the expensive part of a leaf
    let tgtc ← gc.withContext do instantiateMVars (← gc.getType)
    -- an `if b = true` on a Boolean local: case analysis on `b`
    if let some gs ← boolCases? gc tgtc then
      for g' in gs do solve g' env (fuel - 1)
      return
    -- a recursor or `casesOn` on a local variable (a cost `Sum.rec (fun _ => 0) (fun _ => 0) r`
    -- of an answer `r`): case analysis on the variable, the cases reduced by iota
    if let some gs ← recCases? gc tgtc then
      for g' in gs do solve g' env (fuel - 1)
      return
    -- an `if` or `match` in the leaf: split on its condition or scrutinee
    if let some (some gs) ← capped (splitTarget? gc) then
      for g' in gs do solve g' env (fuel - 1)
      return
    let s2 ← saveState
    try
      closeArithCore gc
    catch e =>
      s2.restore
      -- the time of a tree that the rules consume, with the rest of the leaf as its path (on
      -- the leaf before its step costs are reduced, so that `fstSummand` finds them)
      s0.restore
      let some g' ← timeAtom? g0 | throw e
      solve g' env (fuel - 1)

/-- A premise of a source with metavariables in its type: by the context
(`closeByContext`); a time premise `∀ x, StepTimeBound (g x) ?t` (or another kind) by a
source of `g x` whose bound does not depend on `x`; a query bound `A.erase.IsQueryBound ?q`
of a costed adversary by `isQueryBound_of_timeBound` from a time bound of `A`. -/
partial def solvePremise (mid : MVarId) (env : Bool) (fuel : Nat) : TacticM Bool :=
    mid.withContext do
  if ← closeByContext mid then return true
  let ty ← instantiateMVars (← mid.getType)
  let s ← saveState
  let r ← forallTelescopeReducing ty fun xs body => do
    for k in [Kind.stb, .tb, .step, .time] do
      if let some x := k.treeOf body then
        if let some pf ← findSource k x env fuel then
          if ← isDefEq (← inferType pf) body then
            mid.assign (← mkLambdaFVars xs pf)
            return true
    if body.isAppOfArity ``OracleAdv.IsQueryBound 5 then
      let a := body.getArg! 3
      if a.isAppOfArity ``OracleAdv.Timed.erase 4 then
        if let some pf ← queryBoundSource body a.appArg! then
          mid.assign (← mkLambdaFVars xs pf)
          return true
        if let some pf ← findSource .tb a.appArg! env fuel then
          let q ← mkAppM ``OracleAdv.Timed.isQueryBound_of_timeBound #[pf]
          if ← isDefEq (← inferType q) body then
            mid.assign (← mkLambdaFVars xs q)
            return true
    return false
  unless r do s.restore
  return r

/-- A proof that the tree `x` of kind `k` is bounded, from a local hypothesis or (when `env`)
a theorem of `envSources`, with its premises closed by the context or by `solve`. -/
partial def findSource (k : Kind) (x : Expr) (env : Bool) (fuel : Nat) :
    TacticM (Option Expr) := do
  let locals ← (← getLCtx).getFVars.filterM fun f => do
    return !(← f.fvarId!.getDecl).isImplementationDetail
  let envs ← if env then envSources x else pure #[]
  let cands := locals ++ envs
  for c in cands do
    let s ← saveState
    try
      let cty ← instantiateMVars (← inferType c)
      let (ms, bis, body) ← forallMetaTelescopeReducing cty
      let some y := k.treeOf body | throwError "no"
      unless ← withReducible (isDefEq y x) do throwError "no"
      -- premises: the context first, then instances, then `solvePremise`, then the procedure
      for m in ms do
        let mid := m.mvarId!
        if ← mid.isAssigned then continue
        if ← isProp (← mid.getType) then
          discard <| closeByContext mid
      for m in ms, bi in bis do
        let mid := m.mvarId!
        if ← mid.isAssigned then continue
        if bi.isInstImplicit then
          mid.assign (← synthInstance (← mid.getType))
      for m in ms do
        let mid := m.mvarId!
        if ← mid.isAssigned then continue
        unless ← isProp (← mid.getType) do continue
        if ← solvePremise mid env (fuel - 1) then continue
        if (← instantiateMVars (← mid.getType)).hasExprMVar then continue
        solve mid env (fuel - 1)
      for m in ms do
        let mid := m.mvarId!
        if ← mid.isAssigned then continue
        unless ← isProp (← mid.getType) do throwError "no"
        if ← solvePremise mid env (fuel - 1) then continue
        if (← instantiateMVars (← mid.getType)).hasExprMVar then throwError "no"
        solve mid env (fuel - 1)
      let pf ← instantiateMVars (mkAppN c ms)
      if pf.hasExprMVar then throwError "no"
      return some pf
    catch _ =>
      s.restore
  -- the adversary `y.2` of a step-prefixed tree `y` bounded as a whole
  if let (.tb, some y) := (k, sndOf? x) then
    if let some pf ← findSource .stb y env fuel then
      return some (← mkAppM ``tb_snd_of_stb #[pf])
  return none

/-- A subtree that no structural rule consumes: a source, else the unfolding of its head
definition, else the simp set `time_bound_simps`, else (computation trees) an arithmetic
leaf. -/
partial def leaf (g : MVarId) (k : Kind) (x : Expr) (env : Bool) (fuel : Nat) :
    TacticM Unit := g.withContext do
  if let some pf ← findSource k x env fuel then
    if ← applyAndSolve g k.ofRule [pf] env fuel then return
  if let some x' ← unfoldTree? x then
    solve (← replaceIn g x x') true (fuel - 1)
    return
  let s ← saveState
  try
    setGoals [g]
    evalTactic (← `(tactic| simp only [time_bound_simps]))
    let gs ← getGoals
    for g' in gs do solve g' true (fuel - 1)
    return
  catch _ => s.restore
  match k with
  | .step | .time => closeArith g env fuel
  | _ => throwError "time_bound: no bound for the subtree{indentExpr x}"

/-- Apply the rule `n` and solve its premises. -/
partial def applyAndSolve (g : MVarId) (n : Name) (hints : List Expr) (env : Bool)
    (fuel : Nat) : TacticM Bool := do
  let some gs ← applyRule g n hints | return false
  for g' in gs do solve g' env (fuel - 1)
  return true

/-- Apply the rule `n`, failing when it does not apply. -/
partial def rule (g : MVarId) (n : Name) (env : Bool) (fuel : Nat) (hints : List Expr := []) :
    TacticM Unit := do
  unless ← applyAndSolve g n hints env fuel do
    throwError "time_bound: rule {n} does not apply to{indentExpr (← g.getType)}"

/-- Split a `match` at the head of the tree, or case on the local variable that a recursor or
`casesOn` at the head analyses, when there is one. -/
partial def splitMatch (g : MVarId) (x : Expr) (env : Bool) (fuel : Nat) : TacticM Bool := do
  if (← matchMatcherApp? x).isSome then
    let some (some gs) ← capped (splitTarget? g) | return false
    for g' in gs do solve g' env (fuel - 1)
    return true
  let some fv ← recMajor? x | return false
  let s ← saveState
  try
    let some subgoals ← capped (g.cases fv) | return false
    for sg in subgoals do solve sg.mvarId env (fuel - 1)
    return true
  catch _ =>
    s.restore
    return false

/-- A pair `(e, y.2)`: by `fstRule` when the step cost `e` has the summand `y.1` (with
`e = c + y.1` closed by `omega`), else by `plainRule`. -/
partial def pairRule (g : MVarId) (x : Expr) (plainRule fstRule : Name) (env : Bool)
    (fuel : Nat) : TacticM Unit := do
  let e := x.getArg! 2
  let snd0 := x.getArg! 3
  let snd ← if (sndOf? snd0).isSome then pure snd0 else whnfC snd0
  if let some y := sndOf? snd then
    let fsts := (appsOf e #[]).filter fun t => (fstOf? t).isSome
    for o in fsts do
      let s ← saveState
      if ← withReducible (isDefEq (fstOf? o).get! y) then
        let y1 := withFstArg o y
        let e' := e.replace fun t => if t == o then some y1 else none
        let c := e.replace fun t => if t == o then some (mkNatLit 0) else none
        let x' := mkApp4 x.getAppFn (x.getArg! 0) (x.getArg! 1) e' snd
        let g' ← replaceIn g x x'
        try
          if ← applyAndSolve g' fstRule [c] env fuel then return
        catch _ => pure ()
      s.restore
  rule g plainRule env fuel

/-- `P + stepTime x ≤ B`. -/
partial def stepCase (g : MVarId) (x : Expr) (env : Bool) (fuel : Nat) : TacticM Unit := do
  let x' ← whnfC x
  let g ← replaceIn g x x'
  g.withContext do
  if x'.isAppOfArity ``Prod.mk 4 then pairRule g x' ``st_pair ``st_pair_fst env fuel
  else if x'.isAppOf ``SPTree.Timed.delay then rule g ``st_delay env fuel
  else if x'.isAppOf ``SPTree.Timed.map then rule g ``st_map env fuel
  else if x'.isAppOfArity ``ite 5 then rule g ``st_ite env fuel
  else if x'.isAppOfArity ``dite 5 then rule g ``st_dite env fuel
  else if x'.isAppOfArity ``SPTree.Timed.bind 4 then
    let a := x'.getArg! 2
    let a' ← sndThroughDelay (← whnfC a)
    let a' := (← unfoldTree? a').getD a'
    let node : Option Name :=
      if a'.isAppOf ``SPTree.Timed.ret then some ``st_bind_ret
      else if a'.isAppOf ``SPTree.Timed.sample then some ``st_bind_sample
      else if a'.isAppOf ``SPTree.Timed.sampleDist then some ``st_bind_sampleDist
      else if a'.isAppOf ``SPTree.Timed.get then some ``st_bind_get
      else if a'.isAppOf ``SPTree.Timed.set then some ``st_bind_set
      else if a'.isAppOf ``SPTree.Timed.fail then some ``st_bind_fail
      else none
    match node with
    | some n => rule (← replaceIn g a a') n env fuel
    | none =>
      -- a bind after the tree `y.2` of a costed bind `y`, with `y.1` on the path
      for b in [a, a'] do
        if let some y := sndOf? b then
          if y.isAppOfArity ``SPTree.Timed.bind 4 then
            let s ← saveState
            if ← fstSummand (← replaceIn g a b) y ``st_snd_bind_fst env fuel then return
            s.restore
      let s ← saveState
      try
        rule g ``st_bind env fuel
      catch e =>
        s.restore
        -- the continuation bounded at the values satisfying an inferred leaf invariant
        if ← bindInv g x' env fuel then return
        throw e
  else if ← splitMatch g x' env fuel then return
  else if let some gs ← boolCases? g x' then
    for g' in gs do solve g' env (fuel - 1)
  else leaf g .step x' env fuel

/-- `AllRet Q t` by the rules `ar_*` on the visible structure of `t` (a definition unfolded, a
tree without visible leaves by `ar_any`); a leaf goal `Q a` by `solve`. -/
partial def arSolve (g : MVarId) (env : Bool) (fuel : Nat) : TacticM Unit := do
  if fuel == 0 then throwError "time_bound: depth bound reached"
  let g ← liftLets g
  g.withContext do
  let tgt0 ← instantiateMVars (← g.getType)
  let tgt ← Core.betaReduce tgt0
  let g ← if tgt == tgt0 then pure g else g.replaceTargetDefEq tgt
  if tgt.isForall then
    let (_, g') ← g.intro1P
    arSolve g' env (fuel - 1)
    return
  unless tgt.isAppOfArity ``SPTree.Timed.AllRet 3 do
    invLeaf g fuel
    return
  let t := tgt.appArg!
  let mut t1 ← sndThroughDelay (← whnfC t)
  if let some y := sndOf? t1 then
    if let some y' ← unfoldTree? y then
      t1 ← sndThroughDelay (← whnfC (← mkAppM ``Prod.snd #[y']))
  else if let some t2 ← unfoldTree? t1 then
    t1 := t2
  let g ← replaceIn g t t1
  let n? : Option Name :=
    if t1.isAppOf ``SPTree.Timed.ret then some ``ar_ret
    else if t1.isAppOf ``SPTree.Timed.sample then some ``ar_sample
    else if t1.isAppOf ``SPTree.Timed.get then some ``ar_get
    else if t1.isAppOf ``SPTree.Timed.set then some ``ar_set
    else if t1.isAppOf ``SPTree.Timed.load then some ``ar_load
    else if t1.isAppOf ``SPTree.Timed.fail then some ``ar_fail
    else if t1.isAppOfArity ``ite 5 then some ``ar_ite
    else if t1.isAppOfArity ``dite 5 then some ``ar_dite
    else match sndOf? t1 with
      | some b => if b.isAppOfArity ``SPTree.Timed.bind 4 then some ``ar_bind else none
      | none => none
  if let some n := n? then
    let some gs ← applyRule g n | throwError "time_bound: rule {n} does not apply"
    for g' in gs do arSolve g' env (fuel - 1)
    return
  if (← matchMatcherApp? t1).isSome then
    let some (some gs) ← capped (splitTarget? g) | throwError "time_bound: match not split"
    for g' in gs do arSolve g' env (fuel - 1)
    return
  let some gs ← applyRule g ``ar_any | throwError "time_bound: no leaf invariant"
  for g' in gs do arSolve g' env (fuel - 1)

/-- A bind `A.bind f` whose continuation is not bounded at every value: for each companion
that `f` reads and each hypothesis bounding a companion of its type (`invCandidates`), the
least slack of the ladder at which `arSolve` proves the leaf invariant of `A`; the invariants
found are conjoined and `st_bind_inv` applied. -/
partial def bindInv (g : MVarId) (x : Expr) (env : Bool) (fuel : Nat) : TacticM Bool :=
    g.withContext do
  let α := x.getArg! 0
  let A := x.getArg! 2
  let f := x.getArg! 3
  let cands ← invCandidates α f
  if cands.isEmpty then return false
  let mut proofs : Array Expr := #[]
  for ladder in cands do
    for q in ladder do
      let s ← saveState
      let m ← mkFreshExprMVar (← mkAppM ``SPTree.Timed.AllRet #[q, A])
      try
        arSolve m.mvarId! env (fuel - 1)
        proofs := proofs.push (← instantiateMVars m)
        break
      catch _ => s.restore
  if proofs.isEmpty then return false
  let mut pf := proofs[0]!
  for p in proofs[1:] do
    pf ← mkAppM ``SPTree.Timed.allRet_and #[pf, p]
  let s ← saveState
  try
    let some gs ← applyRule g ``st_bind_inv [pf] | return false
    let some hk := gs.getLast? | return false
    for g' in gs.dropLast do solve g' env (fuel - 1)
    let (_, g1) ← hk.intro1P
    let (hq, g2) ← g1.intro1P
    let g3 ← g2.withContext do
      let ty ← instantiateMVars (← hq.getType)
      g2.replaceLocalDeclDefEq hq (← Core.betaReduce ty)
    let g4 ← g3.casesAnd
    solve g4 env (fuel - 1)
    return true
  catch _ =>
    s.restore
    return false

/-- `P + t ≤ B` where `t` is the tree `y.2` or a bind after it, with the summand `y.1` in `P`
(up to reducible defeq): the rule `lem` (`time_snd_fst`, `st_snd_bind_fst`) reads the two
together, with `P` less the summand as its first free argument. -/
partial def fstSummand (g : MVarId) (y : Expr) (lem : Name) (env : Bool) (fuel : Nat) :
    TacticM Bool := g.withContext do
  let s0 ← saveState
  -- the summand `y.1` as it stands on the path, else after the step costs are reduced
  for reduce in [false, true] do
    let g ← if reduce then reduceStepCosts g else pure g
    let tgt ← instantiateMVars (← g.getType)
    let some (l, _) := natLe? tgt | s0.restore; return false
    unless l.isAppOfArity ``HAdd.hAdd 6 do s0.restore; return false
    let p := l.getArg! 4
    let fsts := (appsOf p #[]).filter fun t => (fstOf? t).isSome
    for o in fsts do
      let s ← saveState
      if ← withReducible (isDefEq (fstOf? o).get! y) then
        let y1 := withFstArg o y
        let p' := p.replace fun t => if t == o then some y1 else none
        let q := p.replace fun t => if t == o then some (mkNatLit 0) else none
        let g' ← replaceIn g p p'
        try
          if ← applyAndSolve g' lem [q] env fuel then return true
        catch _ => pure ()
      s.restore
    s0.restore
  return false

/-- `P + t.time ≤ B`. -/
partial def treeCase (g : MVarId) (t : Expr) (env : Bool) (fuel : Nat) : TacticM Unit := do
  let t1 ← whnfC t
  -- a stuck second projection keeps its form `Prod.snd y`
  let t' := if (sndOf? t1).isSome && (sndOf? t).isSome then t else t1
  let g ← replaceIn g t t'
  g.withContext do
  if t'.isAppOf ``SPTree.Timed.ret then rule g ``time_ret env fuel
  else if t'.isAppOf ``SPTree.Timed.sample then rule g ``time_sample env fuel
  else if t'.isAppOf ``SPTree.Timed.sampleDist then rule g ``time_sampleDist env fuel
  else if t'.isAppOf ``SPTree.Timed.get then rule g ``time_get env fuel
  else if t'.isAppOf ``SPTree.Timed.set then rule g ``time_set env fuel
  else if t'.isAppOf ``SPTree.Timed.fail then rule g ``time_fail env fuel
  else if t'.isAppOf ``SPTree.Timed.load then rule g ``time_load env fuel
  else if t'.isAppOfArity ``ite 5 then rule g ``time_ite env fuel
  else if t'.isAppOfArity ``dite 5 then rule g ``time_dite env fuel
  else if let some y := sndOf? t' then
    if ← fstSummand g y ``time_snd_fst env fuel then return
    rule g ``time_snd env fuel
  else if ← splitMatch g t' env fuel then return
  else leaf g .time t' env fuel

/-- `A.TimeBound (B - P)`. -/
partial def tbCase (g : MVarId) (a : Expr) (env : Bool) (fuel : Nat) : TacticM Unit := do
  let a' ← whnfC a
  let g ← replaceIn g a a'
  g.withContext do
  if a'.isAppOf ``OracleAdv.Timed.ret then rule g ``tb_ret env fuel
  else if a'.isAppOf ``OracleAdv.Timed.rand then rule g ``tb_rand env fuel
  else if a'.isAppOf ``OracleAdv.Timed.query then rule g ``tb_query env fuel
  else if a'.isAppOfArity ``ite 5 then rule g ``tb_ite env fuel
  else if a'.isAppOfArity ``dite 5 then rule g ``tb_dite env fuel
  else if (sndOf? a').isSome then rule g ``tb_snd env fuel
  else if ← splitMatch g a' env fuel then return
  else leaf g .tb a' env fuel

/-- `StepTimeBound x (B - P)`. -/
partial def stbCase (g : MVarId) (x : Expr) (env : Bool) (fuel : Nat) : TacticM Unit := do
  let x' ← whnfC x
  let g ← replaceIn g x x'
  g.withContext do
  if x'.isAppOfArity ``Prod.mk 4 then pairRule g x' ``stb_pair ``stb_pair_fst env fuel
  else if x'.isAppOf ``OracleAdv.Timed.delay then rule g ``stb_delay env fuel
  else if x'.isAppOfArity ``ite 5 then rule g ``stb_ite env fuel
  else if x'.isAppOfArity ``dite 5 then rule g ``stb_dite env fuel
  else if x'.isAppOfArity ``OracleAdv.Timed.bind 6 then
    let a := x'.getArg! 4
    let a' ← whnfC a
    let a' := (← unfoldTree? a').getD a'
    let node : Option Name :=
      if a'.isAppOf ``OracleAdv.Timed.ret then some ``stb_bind_ret
      else if a'.isAppOf ``OracleAdv.Timed.rand then some ``stb_bind_rand
      else if a'.isAppOf ``OracleAdv.Timed.query then some ``stb_bind_query
      else none
    match node with
    | some n => rule (← replaceIn g a a') n env fuel
    | none =>
      let some pf ← findSource .tb a env fuel |
        throwError "time_bound: no time bound for the adversary{indentExpr a}"
      rule g ``stb_bind env fuel [pf]
  else if ← splitMatch g x' env fuel then return
  else leaf g .stb x' env fuel

/-- One goal of the procedure. -/
partial def solve (g : MVarId) (env : Bool) (fuel : Nat) : TacticM Unit := do
  if fuel == 0 then throwError "time_bound: depth bound reached"
  let g ← liftLets g
  g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  if tgt.isForall then
    let (_, g') ← g.intro1P
    solve g' env (fuel - 1)
  else if tgt.isAppOfArity ``And 2 then rule g ``And.intro env fuel
  else if tgt.isConstOf ``True then g.assign (mkConst ``True.intro)
  else if let some (l, _) := natLe? tgt then
    if l.isAppOfArity ``SPTree.Timed.stepTime 2 then
      rule g ``st_start (env || (← structuralRoot l.appArg!)) fuel
    else if l.isAppOfArity ``SPTree.Timed.time 2 then
      rule g ``time_start (env || (← structuralRoot l.appArg!)) fuel
    else if l.isAppOfArity ``HAdd.hAdd 6 then
      let y := l.appArg!
      if y.isAppOfArity ``SPTree.Timed.stepTime 2 then stepCase g y.appArg! env fuel
      else if y.isAppOfArity ``SPTree.Timed.time 2 then treeCase g y.appArg! env fuel
      else closeArith g env fuel
    else closeArith g env fuel
  else if tgt.isAppOfArity ``OracleAdv.Timed.TimeBound 5 then
    if (tgt.getArg! 4).isAppOfArity ``HSub.hSub 6 then tbCase g (tgt.getArg! 3) env fuel
    else rule g ``tb_start (env || (← structuralRoot (tgt.getArg! 3))) fuel
  else if tgt.isAppOfArity ``OracleAdv.Timed.StepTimeBound 5 then
    if (tgt.getArg! 4).isAppOfArity ``HSub.hSub 6 then stbCase g (tgt.getArg! 3) env fuel
    else rule g ``stb_start (env || (← structuralRoot (tgt.getArg! 3))) fuel
  else
    let s ← saveState
    try
      g.assumption
    catch _ =>
      s.restore
      closeArith g env fuel

end

/-! ### Leaf invariants of costed oracle adversaries -/

/-- `OracleAdv.Timed.AllRet`, named without the import of its module. -/
def advAllRet : Name := `CatCrypt.Crypto.OracleAdv.Timed.AllRet

/-- The adversary `t` with its head brought to view: `(c, A).2` is `A`, `(delay c x).2` is
`x.2`, and a head definition (also below a second projection) is unfolded. A bind
`(A.bind f).2` is kept. -/
def advHead (t : Expr) : MetaM Expr := do
  let mut t ← whnfC t
  for _ in [0:32] do
    if let some y := sndOf? t then
      let y' ← whnfC y
      if y'.isAppOfArity ``Prod.mk 4 then t ← whnfC (y'.getArg! 3)
      else if y'.isAppOfArity ``OracleAdv.Timed.delay 5 then
        t ← whnfC (← mkAppM ``Prod.snd #[y'.getArg! 4])
      else if y'.isAppOfArity ``OracleAdv.Timed.bind 6 then
        return ← mkAppM ``Prod.snd #[y']
      else if let some y'' ← unfoldTree? y' then
        t ← whnfC (← mkAppM ``Prod.snd #[y''])
      else return ← mkAppM ``Prod.snd #[y']
    else if let some t' ← unfoldTree? t then t := t'
    else return t
  return t

/-- The names of the leaf-invariant theorems of the adversary `t`: `N.allRet_le` for
`t = (N.timed …).2`, and `Ns.allRet_f` for a combinator `Ns.f` at the head of `t`, each also
resolved in the current namespaces. -/
def allRetNames (t : Expr) : MetaM (List Name) := do
  let t ← zetaReduce t
  let mut out : List Name := []
  if let some y := sndOf? t then
    if let some n := y.getAppFn.constName? then
      if n.lastComponentAsString == "timed" then
        let ex := n.getPrefix ++ `allRet_le
        if (← getEnv).contains ex then out := out ++ [ex]
        for c in ← resolvedCompanions n.getPrefix [`allRet_le] do
          unless out.contains c do out := out ++ [c]
  if let some n := t.getAppFn.constName? then
    let tag := Name.mkSimple ("allRet_" ++ n.lastComponentAsString)
    let ex := n.getPrefix ++ tag
    if (← getEnv).contains ex && !out.contains ex then out := out ++ [ex]
    for (c, fields) in ← resolveGlobalName tag do
      if fields.isEmpty && (← getEnv).contains c && !out.contains c then out := out ++ [c]
  return out

mutual

/-- A proof of `AllRet ?Q t`, `?Q` possibly unassigned, by a local hypothesis or a theorem of
`allRetNames`, its premises closed by the context or (for leaf invariants) by `arSource`. -/
partial def arSource (Q t : Expr) (fuel : Nat) : TacticM (Option Expr) := do
  if fuel == 0 then return none
  if let some pf ← arSourceAt Q t fuel then return some pf
  let t' ← advHead t
  if t' == t then return none
  arSourceAt Q t' fuel

/-- `arSource` at the tree `t` as it stands. -/
partial def arSourceAt (Q t : Expr) (fuel : Nat) : TacticM (Option Expr) := do
  let locals ← (← getLCtx).getFVars.filterM fun f => do
    return !(← f.fvarId!.getDecl).isImplementationDetail
  let names ← allRetNames t
  let cands := locals ++ (← names.toArray.mapM fun n => mkConstWithFreshMVarLevels n)
  for c in cands do
    let s ← saveState
    try
      let (ms, _, body) ← forallMetaTelescopeReducing (← inferType c)
      unless body.isAppOfArity advAllRet 5 do throwError "no"
      unless ← isDefEq (body.getArg! 4) t do throwError "no"
      unless ← isDefEq (body.getArg! 3) Q do throwError "no"
      for m in ms do
        let mid := m.mvarId!
        if ← mid.isAssigned then continue
        let ty ← instantiateMVars (← mid.getType)
        unless ← isProp ty do continue
        if ty.isAppOfArity advAllRet 5 then
          let some pf ← arSource (ty.getArg! 3) (ty.getArg! 4) (fuel - 1) | throwError "no"
          mid.assign pf
        else unless ← closeByContext mid do throwError "no"
      let pf ← instantiateMVars (mkAppN c ms)
      if pf.hasExprMVar then throwError "no"
      return some pf
    catch _ => s.restore
  return none

/-- An arithmetic or propositional leaf of a leaf invariant: conjunctions and universal
statements are split, the conjunctions of the context are split, and the goal is closed by
`omega` with the bounded atoms of the context, after case splits. -/
partial def arLeaf (g : MVarId) (fuel : Nat) : TacticM Unit := do
  if fuel == 0 then throwError "allret_bound: depth bound reached"
  let g ← g.casesAnd
  let g ← reduceProjBeta g
  g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  if tgt.isForall then
    let (_, g') ← g.intro1P
    arLeaf g' (fuel - 1)
  else if tgt.isAppOfArity ``And 2 then
    let [g1, g2] ← g.apply (mkConst ``And.intro) | throwError "allret_bound: And"
    arLeaf g1 (fuel - 1)
    arLeaf g2 (fuel - 1)
  else if tgt.isConstOf ``True then g.assign (mkConst ``True.intro)
  else if tgt.isAppOfArity advAllRet 5 then arAdv g (fuel - 1)
  else
    let s ← saveState
    try
      g.assumption
      return
    catch _ => s.restore
    if tgt.isAppOfArity ``Eq 3 && !(tgt.getArg! 0).isConstOf ``Nat then
      if (← capped g.refl).isSome then return
      s.restore
    let g1 ← addBoundedAtoms g
    try
      setGoals [g1]
      evalTactic (← `(tactic| omega))
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()
    s.restore
    if let some gs ← recCases? g tgt then
      for g' in gs do arLeaf g' (fuel - 1)
      return
    let some (some gs) ← capped (splitTarget? g) |
      throwError "allret_bound: leaf not closed{indentExpr tgt}"
    for g' in gs do arLeaf g' (fuel - 1)

/-- `AllRet P t` for a costed oracle adversary `t`: a node by the definition of `AllRet`, an
`if` or `match` by a split, a bind `(A.bind f).2` by a leaf invariant of `A` from `arSource`
(`allRet_bind`) or by reducing the bind at a node, and any tree by a source (`allRet_mono`). -/
partial def arAdv (g : MVarId) (fuel : Nat) : TacticM Unit := do
  if fuel == 0 then throwError "allret_bound: depth bound reached"
  g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  unless tgt.isAppOfArity advAllRet 5 do
    arLeaf g (fuel - 1)
    return
  let P := tgt.getArg! 3
  let t0 := tgt.getArg! 4
  let t ← advHead t0
  let g ← replaceIn g t0 t
  let isNode := t.isAppOf ``OracleAdv.Timed.ret || t.isAppOf ``OracleAdv.Timed.rand ||
    t.isAppOf ``OracleAdv.Timed.query
  if isNode then
    let some tgt' ← capped (whnfD (← g.getType)) | throwError "allret_bound: node"
    arLeaf (← g.replaceTargetDefEq (← Core.betaReduce tgt')) (fuel - 1)
    return
  let inner := (sndOf? t).getD t
  if inner.isAppOfArity ``ite 5 || inner.isAppOfArity ``dite 5 ||
      (← matchMatcherApp? inner).isSome then
    if let some (some gs) ← capped (splitTarget? g) then
      for g' in gs do arAdv g' (fuel - 1)
      return
  if let some fv ← recMajor? inner then
    if let some subgoals ← capped (g.cases fv) then
      for sg in subgoals do arAdv sg.mvarId (fuel - 1)
      return
  -- a source for the whole tree
  let s ← saveState
  let Q ← mkFreshExprMVar (← inferType P)
  if let some pf ← arSource Q t fuel then
    let e ← mkConstWithFreshMVarLevels `CatCrypt.Crypto.OracleAdv.Timed.allRet_mono
    let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType e)
    if ← isDefEq concl (← g.getType) then
      let h := ms.back!
      if ← isDefEq h pf then
        g.assign (mkAppN e ms)
        for m in ms do
          unless ← m.mvarId!.isAssigned do arLeaf m.mvarId! (fuel - 1)
        return
  s.restore
  -- a bind: a leaf invariant of its first tree
  if let some b := sndOf? t then
    if b.isAppOfArity ``OracleAdv.Timed.bind 6 then
      let A := b.getArg! 4
      let α := b.getArg! 2
      let Q ← mkFreshExprMVar (← mkArrow α (mkSort .zero))
      let s1 ← saveState
      if let some pf ← arSource Q A fuel then
        let e ← mkConstWithFreshMVarLevels `CatCrypt.Crypto.OracleAdv.Timed.allRet_bind
        let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType e)
        if ← isDefEq concl (← g.getType) then
          let hA := ms[ms.size - 2]!
          if ← isDefEq hA pf then
            g.assign (mkAppN e ms)
            let hf := ms.back!.mvarId!
            let (_, g1) ← hf.intro1P
            let (hq, g2) ← g1.intro1P
            let g3 ← g2.withContext do
              g2.replaceLocalDeclDefEq hq (← Core.betaReduce (← instantiateMVars (← hq.getType)))
            arAdv g3 (fuel - 1)
            return
      s1.restore
      -- the first tree at a node: the bind reduced
      let A' ← advHead A
      if A'.isAppOf ``OracleAdv.Timed.ret || A'.isAppOf ``OracleAdv.Timed.rand ||
          A'.isAppOf ``OracleAdv.Timed.query then
        let b' := mkAppN b.getAppFn (b.getAppArgs.set! 4 A')
        let some t' ← capped (whnfD (← mkAppM ``Prod.snd #[b'])) |
          throwError "allret_bound: bind"
        let g' ← g.replaceTargetDefEq (mkAppN tgt.getAppFn (tgt.getAppArgs.set! 4 t'))
        arAdv g' (fuel - 1)
        return
  throwError "allret_bound: no leaf invariant for{indentExpr t}"

end

/-- `allret_bound` proves a leaf invariant `AllRet P t` of a costed oracle adversary `t`, as
the companion bounds `∀ x, y.2.1.2 x ≤ b + 3` of the states that a costed handler returns, from
the hypotheses bounding the companions it receives (see `arAdv`). -/
syntax (name := allRetBoundStx) "allret_bound_fn" : tactic

@[tactic allRetBoundStx] def evalAllRetBound : Tactic := fun _ => do
  let g ← getMainGoal
  let rest := (← getGoals).tail
  arLeaf g 256
  setGoals rest

/-- The depth bound of `time_bound`. -/
def maxDepth : Nat := 512

/-- `time_bound` proves `SPTree.Timed.stepTime x ≤ B`, `t.time ≤ B`,
`OracleAdv.Timed.StepTimeBound x n` and `A.TimeBound n` by consuming the costed tree node by
node, bounding the subtrees it cannot consume by local hypotheses or by the time theorems of
the definitions below the one named in the goal, and closing the arithmetic leaves by `omega`
or `linarith` with the bounded atoms of the context (see the module docstring). -/
syntax (name := timeBoundStx) "time_bound_fn" : tactic

@[tactic timeBoundStx] def evalTimeBound : Tactic := fun _ => do
  let g ← getMainGoal
  let rest := (← getGoals).tail
  solve g false maxDepth
  setGoals rest

end

end CatCrypt.Tactics.AutoTime.Fn

namespace CatCrypt.Tactics.DeriveTimeBound.Fn

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

/-- The bound of the `match` `m` whose alternatives are bounded by `k` (a step cost, a pair or
a tree): the maximum of the bounds of its alternatives, or, when a bound mentions a pattern
variable after the registered costs are replaced by closed forms, the `match` of the bounds of
its alternatives (`matchBound`). The bounds of the alternatives include the cost of the
dispatch that the costed form charges in each alternative. -/
def boundMatch (m : MatcherApp) (k : Expr → MetaM Expr) : MetaM Expr := do
  let mut acc : Option Expr := none
  let mut lams : Array Expr := #[]
  let mut dep := false
  for alt in m.alts, n in m.altNumParams do
    let (b, lam, d) ← lambdaBoundedTelescope alt n fun ys body => do
      let r ← instantiateMVars (← k body)
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
    | none => throwError "the bound depends on a matched value{indentExpr m.toExpr}"
  match acc with
  | some r => return r
  | none => throwError "a match without alternatives{indentExpr m.toExpr}"

/-- The bound of a case analysis `T.casesOn ps m x a₁ … aₖ` or `T.rec ps m a₁ … aₖ x` of a
non-recursive inductive type `T` with one motive and no argument after its major premise, whose
minor premises `aᵢ` (functions of the fields of constructor `i`) are bounded by `k`: the maximum
of the bounds of the minor premises (a cost of `Sum.map f g` on a bound value). `none` when `e`
is not such a case analysis or a bound of a minor premise mentions a field. -/
def casesBound? (e : Expr) (k : Expr → MetaM Expr) : MetaM (Option Expr) := do
  let some c := e.getAppFn.constName? | return none
  let env ← getEnv
  let args := e.getAppArgs
  let some (iv, start) ← (do
      if isCasesOnRecursor env c then
        let some (.inductInfo iv) := env.find? c.getPrefix | return none
        return some (iv, iv.numParams + 1 + iv.numIndices + 1)
      let some (.recInfo rv) := env.find? c | return none
      unless rv.numMotives == 1 do return none
      let some (.inductInfo iv) := env.find? rv.getMajorInduct | return none
      return some (iv, rv.numParams + 1) : MetaM (Option (InductiveVal × Nat)))
    | return none
  if iv.isRec then return none
  let nCtors := iv.ctors.length
  unless args.size == iv.numParams + 1 + iv.numIndices + 1 + nCtors do return none
  let mut acc : Option Expr := none
  for ctor in iv.ctors, i in [0:nCtors] do
    let some (.ctorInfo cv) := env.find? ctor | return none
    let some minor := args[start + i]? | return none
    let b? ← lambdaBoundedTelescope minor cv.numFields fun ys body => do
      if ys.size != cv.numFields then return none
      let r ← instantiateMVars (← k body)
      let r ← ys.foldlM (init := r) fun r y => rewriteCosts y.fvarId! r
      if ys.any fun y => r.containsFVar y.fvarId! then return none
      return some r
    let some b := b? | return none
    acc ← match acc with
      | none => pure (some b)
      | some a => if a == b then pure (some a) else some <$> mkMaxN a b
  return acc

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
    if !m.alts.isEmpty then return ← boundMatch m (boundCost bs)
  if let some r ← casesBound? e (boundCost bs) then return r
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
  -- a step dispatched by a `match`: the bounds of its alternatives (`boundMatch`)
  if let some m ← matchMatcherApp? x then
    if !m.alts.isEmpty then return ← boundMatch m (boundStep bs)
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
  if t.isAppOfArity ``SPTree.Timed.sampleDist 5 then
    let γ := t.getArg! 1
    let c := t.getArg! 3
    let k := t.getArg! 4
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
  -- a tree dispatched by a `match`: the bounds of its alternatives (`boundMatch`)
  if let some m ← matchMatcherApp? t then
    if !m.alts.isEmpty then return ← boundMatch m (boundTree bs)
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
      let tac ← `(tactic| time_bound_fn)
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

/-- The bounds with the hypothesis of each bounded binder. -/
abbrev HBounds := Array (FVarId × Expr × Role × Expr)

/-- `a ≤ b` over `ℕ`. -/
def mkNatLe (a b : Expr) : Expr :=
  mkApp4 (mkConst ``LE.le [Level.zero]) natE (mkConst ``instLENat) a b

/-- The maximum of the bounds `bs` folded from the left, with a proof of `bᵢ ≤ max` for each:
`max (… (max b₀ b₁) …) bₙ`. Equal neighbours are kept once, as in `boundCost`. -/
def maxChain (bs : Array Expr) : MetaM (Expr × Array Expr) := do
  let some b0 := bs[0]? | throwError "maxChain: no bound"
  let mut acc := b0
  let mut pfs : Array Expr := #[mkApp (mkConst ``Nat.le_refl) b0]
  for b in bs[1:] do
    if b == acc then
      pfs := pfs.push (mkApp (mkConst ``Nat.le_refl) b)
      continue
    let acc' ← mkMaxN acc b
    -- the earlier proofs lifted by `le_max_left`, the new bound by `le_max_right`
    let l ← mkAppM ``le_max_left #[acc, b]
    pfs ← pfs.mapM fun p => mkAppM ``le_trans #[p, l]
    pfs := pfs.push (← mkAppM ``le_max_right #[acc, b])
    acc := acc'
  return (acc, pfs)

/-- The equation `eqn` of a matcher at the application `l` of that matcher to the patterns of
its alternative, the overlap hypotheses taken from `ys`: the arguments of the alternative in
the right side, and the proof of `l = alt args`. -/
def eqnAt (eqn : Name) (l : Expr) (ys : Array Expr) : MetaM (Array Expr × Expr) := do
  let c ← mkConstWithFreshMVarLevels eqn
  let (ms, _, ty) ← forallMetaTelescopeReducing (← inferType c)
  unless ty.isAppOfArity ``Eq 3 do throwError "mirror: equation {eqn}"
  -- argument by argument: on a constructor pattern `isDefEq` would first reduce both matcher
  -- applications by iota, leaving `?h ()` against the body of the alternative
  let lhs := ty.getArg! 1
  let .const n₁ us₁ := lhs.getAppFn | throwError "mirror: equation {eqn}"
  let .const n₂ us₂ := l.getAppFn | throwError "mirror: equation {eqn} does not apply"
  unless n₁ == n₂ && us₁.length == us₂.length &&
      lhs.getAppNumArgs == l.getAppNumArgs do
    throwError "mirror: equation {eqn} does not apply"
  for u₁ in us₁, u₂ in us₂ do
    unless ← isLevelDefEq u₁ u₂ do throwError "mirror: equation {eqn}: universe"
  for a in lhs.getAppArgs, b in l.getAppArgs do
    unless ← isDefEq a b do throwError "mirror: equation {eqn} does not apply"
  for mv in ms do
    let mid := mv.mvarId!
    if ← mid.isAssigned then continue
    let t ← instantiateMVars (← mid.getType)
    let some y ← ys.findM? fun y => do isDefEq (← inferType y) t
      | throwError "mirror: overlap hypothesis of {eqn}"
    mid.assign y
  let args ← (ty.getArg! 2).getAppArgs.mapM instantiateMVars
  return (args, ← instantiateMVars (mkAppN c ms))

/-- A proof of `m[ds] ≤ rhs ds` by the splitter of the matcher of `m` with the motive
`fun ds => m[ds] ≤ rhs ds`: at alternative `i`, the equation `i` of the matcher reduces
`m[pat]` to the body of the alternative at its arguments, which `altPfs[i]` (a function of
the pattern variables of the alternative) bounds by `rhs`; when `rhsMatch`, `rhs` is a match
of the same matcher, reduced by the same equation. -/
def splitProof (m : MatcherApp) (rhs : Array Expr → Expr) (altPfs : Array Expr)
    (rhsMatch : Bool) : MetaM Expr := do
  let some pos := m.uElimPos? | throwError "mirror: match without a motive universe"
  let eqns ← Match.getEquationsFor m.matcherName
  let motive ← forallBoundedTelescope (← inferType m.motive) m.discrs.size fun xs _ =>
    mkLambdaFVars xs (mkNatLe { m with discrs := xs }.toExpr (rhs xs))
  let lvls := m.matcherLevels.set! pos Level.zero
  let f := mkAppN (mkConst eqns.splitterName lvls.toList) (m.params ++ #[motive] ++ m.discrs)
  let mut fty ← inferType f
  let mut alts : Array Expr := #[]
  for i in [0:m.alts.size] do
    let .forallE _ d b _ ← whnfD fty | throwError "mirror: splitter type"
    let pf ← forallTelescopeReducing d fun ys tgt => do
      let some (l, r) := CatCrypt.Tactics.AutoTime.natLe? tgt.headBeta
        | throwError "mirror: splitter alternative"
      let (args, eq₁) ← eqnAt eqns.eqnNames[i]! l ys
      let mut pf ← mkAppM ``le_trans #[← mkAppM ``Nat.le_of_eq #[eq₁], altPfs[i]!.beta args]
      if rhsMatch then
        let (_, eq₂) ← eqnAt eqns.eqnNames[i]! r ys
        pf ← mkAppM ``le_trans #[pf, ← mkAppM ``Nat.le_of_eq #[← mkEqSymm eq₂]]
      mkLambdaFVars ys pf
    alts := alts.push pf
    fty := b.instantiate1 pf
  return mkAppN f alts

/-- The closed form `r` of the registered cost `s = f.timedCost a` free of the variable `b`,
with a proof of `s ≤ r`: from `f.timedCost_eq` at `a` by `Nat.le_of_eq`, or from
`f.timedCost_le` at `a`, the propositional premises closed from the context
(`costClosedForm?` with its proof). -/
def costClosedFormPf? (b : FVarId) (s : Expr) : MetaM (Option (Expr × Expr)) := do
  let some n := s.getAppFn.constName? | return none
  for c in ← CatCrypt.Tactics.AutoTime.costLemmas n do
    let st ← saveState
    let (ms, _, body) ← forallMetaTelescopeReducing (← inferType c)
    let isEq := body.isAppOfArity ``Eq 3
    let side? := if isEq then some (body.getArg! 1, body.getArg! 2)
      else CatCrypt.Tactics.AutoTime.natLe? body
    let some (l, r) := side? | st.restore; continue
    if ← isDefEq l s then
      let ok ← ms.allM fun m => do
        let mid := m.mvarId!
        if ← mid.isAssigned then return true
        unless ← isProp (← mid.getType) do return true
        CatCrypt.Tactics.AutoTime.closeByContext mid
      let r ← instantiateMVars r
      let pf ← instantiateMVars (mkAppN c ms)
      if ok && !r.hasExprMVar && !pf.hasExprMVar && !r.containsFVar b then
        let pf ← if isEq then mkAppM ``Nat.le_of_eq #[pf] else pure pf
        return some (r, pf)
    st.restore
  return none

/-- The registered cost `s` with a proof of `s ≤ r`, `r` its replacement in the bound of
`boundCost`: for the pattern variables `pvs` of the enclosing matches, grouped by match from the
outermost, the innermost group first and each group in order, a registered cost that mentions
the variable is replaced by its closed form free of it, as `rewriteCosts` does at each
alternative. -/
def rewriteCostPf (pvs : Array (Array FVarId)) (s : Expr) : MetaM (Expr × Expr) := do
  let mut cur := s
  let mut pf := mkApp (mkConst ``Nat.le_refl) s
  for ys in pvs.reverse do
    for y in ys do
      let some n := cur.getAppFn.constName? | return (cur, pf)
      unless n.lastComponentAsString == "timedCost" && cur.containsFVar y do continue
      if let some (r, p) ← costClosedFormPf? y cur then
        pf ← mkAppM ``le_trans #[pf, p]
        cur := r
  return (cur, pf)

/-- The bound of a step cost `e : ℕ` with a proof of `e ≤ bound`, by the clauses of
`boundCost`; throws outside them. `pvs` are the pattern variables of the enclosing matches,
one group per match from the outermost (`rewriteCostPf`). -/
partial def mirrorCost (hs : HBounds) (pvs : Array (Array FVarId)) (e : Expr) :
    MetaM (Expr × Expr) := do
  let go := fun e => mirrorCost hs pvs e
  let e := e.headBeta
  match e with
  | .letE _ _ v b _ => go (b.instantiate1 v)
  | .mdata _ b => go b
  | _ =>
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let (a, pa) ← go (e.getArg! 4)
    let (b, pb) ← go (e.getArg! 5)
    return (mkAddN a b, ← mkAppM ``Nat.add_le_add #[pa, pb])
  if e.isAppOfArity ``HMul.hMul 6 then
    let (a, pa) ← go (e.getArg! 4)
    let (b, pb) ← go (e.getArg! 5)
    return (mkMulN a b, ← mkAppM ``Nat.mul_le_mul #[pa, pb])
  if e.isAppOfArity ``Max.max 4 then
    let (a, pa) ← go (e.getArg! 2)
    let (b, pb) ← go (e.getArg! 3)
    return (← mkMaxN a b, ← mkAppM ``max_le_max #[pa, pb])
  if e.isAppOfArity ``ite 5 then
    let (a, pa) ← go (e.getArg! 3)
    let (b, pb) ← go (e.getArg! 4)
    let pf := mkAppN (mkConst ``CatCrypt.Tactics.AutoTime.ite_le_max_of)
      #[e.getArg! 1, e.getArg! 2, e.getArg! 3, e.getArg! 4, a, b, pa, pb]
    return (← mkMaxN a b, pf)
  if (CatCrypt.Tactics.AutoTime.fstOf? e).isSome then
    throwError "mirror: the step cost of a subtree"
  if let .fvar f := e.getAppFn then
    if let some (_, v, .cost, h) := hs.find? (·.1 == f) then
      return (v, mkAppN h e.getAppArgs)
  if let some m ← matchMatcherApp? e then
    let mut bnds : Array Expr := #[]
    let mut pfs : Array Expr := #[]
    let mut lams : Array Expr := #[]
    let mut dep := false
    for alt in m.alts, n in m.altNumParams do
      let (b, pf, lam, d) ← lambdaBoundedTelescope alt n fun ys body => do
        let (r, p) ← mirrorCost hs (pvs.push (ys.map (·.fvarId!))) body
        let r ← instantiateMVars r
        let d := ys.any fun y => r.containsFVar y.fvarId!
        return (r, ← mkLambdaFVars ys p, ← mkLambdaFVars ys r, d)
      bnds := bnds.push b
      pfs := pfs.push pf
      lams := lams.push lam
      dep := dep || d
    if dep then
      let some mB ← matchBound m lams | throwError "mirror: no match of the bounds"
      let some mBm ← matchMatcherApp? mB | throwError "mirror: the match of the bounds"
      let pf ← splitProof m (fun xs => { mBm with discrs := xs }.toExpr) pfs true
      return (mB, pf)
    let (B, ups) ← maxChain bnds
    -- each alternative proof lifted to the maximum
    let mut pfs' : Array Expr := #[]
    for alt in m.alts, n in m.altNumParams, pf in pfs, up in ups do
      pfs' := pfs'.push (← lambdaBoundedTelescope alt n fun ys _ => do
        mkLambdaFVars ys (← mkAppM ``le_trans #[pf.beta ys, up]))
    return (B, ← splitProof m (fun _ => B) pfs' false)
  if let some n := e.getAppFn.constName? then
    if n.lastComponentAsString == "timedCost" && pvs.any (·.any e.containsFVar) then
      return ← rewriteCostPf pvs e
  return (e, mkApp (mkConst ``Nat.le_refl) e)

/-- The outcome of `mirrorTimeBound`. -/
inductive MirrorResult where
  /-- The theorem is declared. -/
  | proved
  /-- The tree is not a pure step. -/
  | outside
  /-- The tree is a pure step and the procedure stops for the reason `why`. -/
  | refused (why : MessageData)

/-- The time theorem of the costed tree `c` with a pure step body, proved along its bound. The
theorem states the bound `B` of `emitTimeBound` (`boundStep`), so the statement does not depend
on the procedure that proves it; `B₀ ≤ B` is proved by `omega` against `B` in projection-normal
form, which is definitionally `B`. -/
def mirrorTimeBound (c name : Name) : TermElabM MirrorResult := do
  let info ← getConstInfo c
  let lvls := info.levelParams.map mkLevelParam
  forallTelescope info.type fun xs _ => do
    withBounds xs 0 #[] #[] #[] fun bs vars hyps => do
      let hs : HBounds := (bs.zip hyps).map fun ((f, v, r), h) => (f, v, r, h)
      let x := mkAppN (Lean.mkConst c lvls) xs
      -- the pair as `boundStep` reads it
      let body ← reduceHead x
      unless body.isAppOfArity ``Prod.mk 4 do return .outside
      let t ← reduceHead (body.getArg! 3)
      unless t.isAppOfArity ``SPTree.Timed.ret 2 do return .outside
      let bound? : Except MessageData Expr ← try
          pure (.ok (← normalizeSum (← instantiateMVars (← boundStep bs x))))
        catch ex => pure (.error ex.toMessageData)
      let bound ← match bound? with
        | .ok b => pure b
        | .error why => return .refused m!"no bound: {why}"
      let e := body.getArg! 2
      let eP ← CatCrypt.Tactics.DeriveReduction.reduceProjCtor e
      let r : Except MessageData (Expr × Expr) ← try
          pure (.ok (← mirrorCost hs #[] eP))
        catch ex => pure (.error ex.toMessageData)
      let (b0, pe) ← match r with
        | .ok p => pure p
        | .error why => return .refused why
      let b0 ← instantiateMVars b0
      -- `B₀ ≤ B` by `omega`, `B` the bound of `boundStep` in projection-normal form
      let boundP ← CatCrypt.Tactics.DeriveReduction.reduceProjCtor bound
      let mv ← mkFreshExprSyntheticOpaqueMVar (mkNatLe b0 boundP)
      let gs ← try Tactic.run mv.mvarId! (Tactic.evalTactic (← `(tactic| omega)))
        catch _ => pure [mv.mvarId!]
      unless gs.isEmpty do
        return .refused m!"`omega` does not prove{indentExpr (mkNatLe b0 boundP)}"
      -- `stepTime x ≤ B` from `e ≤ B₀ ≤ B` by `st_start`, `st_pair` and `time_ret`, the body
      -- `(e, ret a)` of `x` read by the kernel through the definition of `x`
      let goal ← mkAppM ``LE.le #[← mkAppM ``SPTree.Timed.stepTime #[x], bound]
      let α := t.getArg! 0
      let h1 ← mkAppM ``Nat.le_trans #[pe, ← instantiateMVars mv]
      let h2 ← mkAppM ``Nat.le_trans #[← mkAppM ``Nat.le_of_eq #[← mkAppM ``Nat.zero_add #[e]], h1]
      let h3 := mkAppN (mkConst ``CatCrypt.Tactics.AutoTime.time_ret)
        #[α, mkAddN (mkNatLit 0) e, bound, t.getArg! 1, h2]
      let h4 ← mkAppM ``CatCrypt.Tactics.AutoTime.st_pair #[h3]
      let pf := mkAppN (mkConst ``CatCrypt.Tactics.AutoTime.st_start) #[α, bound, x, h4]
      let ty ← mkForallFVars (xs ++ vars ++ hyps) goal
      let v ← mkLambdaFVars (xs ++ vars ++ hyps) pf
      addDecl (Declaration.thmDecl
        { name, levelParams := info.levelParams, type := ty, value := v })
      return .proved

/-- `derive_time_bound R.tree` states and proves `R.tree.timeBound_timed`, the time theorem of
`R.tree.timed` (see the module docstring): along its bound for a pure step body
(`mirrorTimeBound`), else by `time_bound` (`emitTimeBound`); it fails with the reason when the
theorem is not proved, for a pure step with the reasons of both procedures. -/
syntax (name := deriveTimeBoundCmd) "derive_time_bound_fn " ident : command

@[command_elab deriveTimeBoundCmd]
def elabDeriveTimeBound : CommandElab := fun stx => do
  liftTermElabM do
    let t ← realizeGlobalConstNoOverloadWithInfo stx[1]
    let name := t ++ `timeBound_timed
    let r ← mirrorTimeBound (t ++ `timed) name
    if let .proved := r then return
    if let some why ← emitTimeBound (t ++ `timed) name then
      if let .refused w := r then
        throwError "`{name}` is not proved: {why}\nalong the bound of the pure step: {w}"
      throwError "`{name}` is not proved: {why}"

end

end CatCrypt.Tactics.DeriveTimeBound.Fn
