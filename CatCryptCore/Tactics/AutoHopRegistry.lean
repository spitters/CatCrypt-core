/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean

/-!
# The `hop_metric` registry

The attribute `@[hop_metric]` and the reading of a term as a registered distance
(`distView?`). The module imports only `Lean`: a module registers its distances with
`@[hop_metric]` by importing this module, and the procedures that use the registry
(`hop_chain` and `sum_atoms_le` in `CatCryptCore.Tactics.AutoArms`, the shape matcher of
`catcrypt_auto` in `CatCryptCore.Tactics.AutoDispatchCore`) read it.

`@[hop_metric]` accepts three kinds of declaration:

* a triangle lemma `d … x z ≤ d … x y + d … y z`; the positions of the two endpoints
  among the arguments of `d` are read off the statement, and the remaining arguments
  (types, a fixed adversary) are the context of the distance;
* a symmetry lemma `d … x y = d … y x`;
* a definition whose unfolding is a distance term (an advantage-valued definition such
  as `KA_Advantage`), or an equation `D … = d …` whose right side is one.
-/

public section

meta section

namespace CatCrypt.Tactics.AutoArms

open Lean Meta

/-- The role of a declaration registered with `@[hop_metric]`. -/
inductive HopKind where
  /-- A triangle lemma; the indices of the left and right endpoints among the arguments. -/
  | triangle (left right : Nat)
  /-- A symmetry lemma `d … x y = d … y x`. -/
  | symm
  /-- A definition unfolded by delta reduction. -/
  | unfoldDef
  /-- An equation `D … = d …`. -/
  | unfoldEq
  deriving Inhabited, BEq

/-- A registered declaration: its head constant, the arity of that head, and its role. -/
structure HopEntry where
  /-- The head constant: the distance for `triangle`/`symm`, the unfolded head otherwise. -/
  head : Name
  /-- The number of arguments of the head in the statement (`0` for `unfoldDef`). -/
  arity : Nat
  /-- The role of the declaration. -/
  kind : HopKind
  /-- The registered declaration. -/
  decl : Name
  deriving Inhabited

/-- The registry of `@[hop_metric]` declarations. -/
initialize hopMetricExt : SimpleScopedEnvExtension HopEntry (Array HopEntry) ←
  registerSimpleScopedEnvExtension { addEntry := Array.push, initial := #[] }

/-- The head constant and arguments of an application of a constant. -/
def appParts? (e : Expr) : Option (Name × Array Expr) :=
  match e.getAppFn with
  | .const n _ => some (n, e.getAppArgs)
  | _ => none

/-- The two sides of `a ≤ b`. -/
def leSides? (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity ``LE.le 4 then some (e.appFn!.appArg!, e.appArg!) else none

/-- The two sides of `a = b`. -/
def eqSides? (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity ``Eq 3 then some (e.appFn!.appArg!, e.appArg!) else none

/-- The two summands of `a + b`. -/
def addSides? (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity ``HAdd.hAdd 6 then some (e.appFn!.appArg!, e.appArg!) else none

/-- Classify a declaration for `@[hop_metric]`, or fail with the accepted shapes. -/
def classifyHop (decl : Name) : MetaM HopEntry := do
  let info ← getConstInfo decl
  if info matches .defnInfo _ then
    return { head := decl, arity := 0, kind := .unfoldDef, decl }
  forallTelescopeReducing info.type fun _ concl => do
    let concl ← whnfR concl
    if let some (l, r) := leSides? concl then
      if let some (r₁, r₂) := addSides? r then
        if let (some (h, la), some (h₁, a₁), some (h₂, a₂)) :=
            (appParts? l, appParts? r₁, appParts? r₂) then
          if h == h₁ && h == h₂ && la.size == a₁.size && la.size == a₂.size then
            let idx := (List.range la.size).toArray
            let lefts := idx.filter fun k => la[k]! == a₁[k]! && la[k]! != a₂[k]!
            let rights := idx.filter fun k => la[k]! == a₂[k]! && la[k]! != a₁[k]!
            if lefts.size == 1 && rights.size == 1 then
              let i := lefts[0]!
              let j := rights[0]!
              if a₁[j]! == a₂[i]! then
                return { head := h, arity := la.size, kind := .triangle i j, decl }
    if let some (l, r) := eqSides? concl then
      if let (some (h, la), some (h', ra)) := (appParts? l, appParts? r) then
        if h == h' && la.size == ra.size && l != r then
          return { head := h, arity := la.size, kind := .symm, decl }
        if h != h' then
          return { head := h, arity := la.size, kind := .unfoldEq, decl }
    throwError "hop_metric: `{decl}` is not a triangle lemma `d … x z ≤ d … x y + d … y z`, \
      a symmetry lemma `d … x y = d … y x`, an equation `D … = d …`, or a definition"

/-- `@[hop_metric]` registers a triangle lemma, a symmetry lemma, an unfolding equation,
or a definition to be unfolded, for use by `hop_chain`. -/
initialize registerBuiltinAttribute {
  name := `hop_metric
  descr := "Register a triangle lemma, symmetry lemma or unfolding for `hop_chain`"
  add := fun decl _ kind => MetaM.run' do
    hopMetricExt.add (← classifyHop decl) kind
  applicationTime := .afterTypeChecking
}

/-! ## Distance views -/

/-- A term read as a registered distance: the triangle entry of its head, the distance
term after unfolding, its arguments, and a proof that the original term equals it
(`none` when the two are definitionally equal by delta reduction). -/
structure DView where
  /-- The triangle entry of the distance. -/
  entry : HopEntry
  /-- The distance term. -/
  term : Expr
  /-- The arguments of the distance. -/
  args : Array Expr
  /-- A proof of `original = term`, if not definitional. -/
  pf : Option Expr

/-- The registered entries. -/
def hopEntries : MetaM (Array HopEntry) :=
  return hopMetricExt.getState (← getEnv)

/-- Instantiate a registered theorem with fresh metavariables: the applied proof and its
statement. -/
def instThm (decl : Name) : MetaM (Expr × Expr) := do
  let c ← mkConstWithFreshMVarLevels decl
  let (mvs, _, ty) ← forallMetaTelescopeReducing (← inferType c)
  return (mkAppN c mvs, ty)

/-- Compose an optional equation proof `a = b` with `b = c`. -/
def transOpt (p : Option Expr) (q : Option Expr) : MetaM (Option Expr) :=
  match p, q with
  | none, q => pure q
  | p, none => pure p
  | some p, some q => some <$> mkEqTrans p q

/-- Read `e` as a registered distance, unfolding registered definitions and equations
at the head at most `fuel` times. -/
partial def distView? (e : Expr) (fuel : Nat := 6) : MetaM (Option DView) := do
  let e ← instantiateMVars e
  let some (h, args) := appParts? e | return none
  let entries ← hopEntries
  for x in entries do
    if let .triangle _ _ := x.kind then
      if x.head == h && x.arity == args.size then
        return some { entry := x, term := e, args, pf := none }
  if fuel == 0 then return none
  for x in entries do
    if x.head != h then continue
    match x.kind with
    | .unfoldDef =>
      if let some e' ← unfoldDefinition? e then
        if let some v ← distView? e' (fuel - 1) then return some v
    | .unfoldEq =>
      if x.arity == args.size then
        let (p, ty) ← instThm x.decl
        if let some (l, r) := eqSides? ty then
          if ← isDefEq l e then
            let p ← instantiateMVars p
            if let some v ← distView? (← instantiateMVars r) (fuel - 1) then
              return some { v with pf := ← transOpt (some p) v.pf }
    | _ => pure ()
  return none

end CatCrypt.Tactics.AutoArms

end
