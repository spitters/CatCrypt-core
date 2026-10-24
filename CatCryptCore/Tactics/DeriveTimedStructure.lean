/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimed

/-!
# Costed mirrors of structures, with handler-priced fields

`derive_timed_structure S` takes a structure `S` whose fields are types, propositions, data,
trees of a registered tree kind (`CatCryptCore.Tactics.DeriveTimed`), computations
`SPComp β`, or values of a registered handler kind, each possibly under binders, and defines

* the costed mirror `S.Timed`, with the parameters of `S` and, field by field: a type field
  and a data field kept; a proposition field dropped; a field `f : X₁ → … → Xₙ → T` into
  trees or computations replaced by `f : X₁ → … → Xₙ → T'` with `T'` the costed tree type
  (`SPTree.Timed β` for `SPComp β`), followed by its cost companion
  `fCost : X₁ → … → Xₙ → ℕ`, the cost of computing the tree from its arguments (a number for
  `n = 0`);
* the erasure relation `S.Timed.Erases A' A`: some proofs of the proposition fields complete
  the fields of `A'`, with each tree field erased (`erase`, and `SPTree.compile` after it for a
  computation), to `A`; the mirror has no proof fields, so erasure is a relation and not a
  function;
* the time bound `S.Timed.TimeBound A' Ts`: for each tree or computation field `f` one bound
  `T_f` on the time of its step-prefixed costed trees `(A'.fCost ys, A'.f ys)`, the cost of
  computing the tree followed by its run (`OracleAdv.Timed.StepTimeBound` or
  `SPTree.Timed.stepTime`). The stages of a multi-stage adversary run separately, so their
  bounds are separate parameters and are not added.

This is the translation of a structure type in the call-by-value writer translation of the
design of `derive_timed`: the translation of a product is the product of the translations.

A proposition field may depend on any earlier field (a query bound on a tree field); in the
erasure relation it is stated about the erased fields. A type, data, tree or computation field
whose type depends on a proposition field or on a tree or computation field is refused.

## Handler kinds

A field whose result type is an application `H a₁ ⋯ aₖ` of a constant `H` is of a handler kind
when the environment holds one of the following families of declarations, read by name.

* A circuit kind: `H.handlerGateSet a₁ ⋯ aₖ`, the type of the gate set of the mirror;
  `H.handlerMirror a₁ ⋯ aₖ S`, the costed type over the gate set `S`; `H.handlerErases A' A`,
  the erasure relation of a costed value `A'` and a value `A`; and `H.handlerTime A' h`, the
  time of a run of `A'` under the handler cost `h`. A field `f : X₁ → ⋯ → Xₙ → H a₁ ⋯ aₖ` is
  mirrored as `f : X₁ → ⋯ → Xₙ → H.handlerMirror a₁ ⋯ aₖ fGS` with its cost companion `fCost`,
  where the gate set `fGS : H.handlerGateSet a₁ ⋯ aₖ` is a parameter of the mirror after the
  parameters of `S`, so its type may mention the parameters of `S` only. Its erasure is
  `∀ ys, H.handlerErases (A'.f ys) (A.f ys)`, and its conjunct of the time bound, with a
  handler cost `fHandler` and a bound `fTime` as parameters of `TimeBound`, is
  `∀ ys, A'.fCost ys + H.handlerTime (A'.f ys) fHandler ≤ fTime`.
* A bounded kind: `H.handlerBound v h T`, a time bound of the value `v` under the handler cost
  `h`. A field of this kind is kept as data; its conjunct of the time bound, with a handler
  cost `fHandler` and a bound `fTime` as parameters of `TimeBound`, is
  `∀ ys, H.handlerBound (A'.f ys) fHandler fTime`.

A structure `H` that is itself a handler kind (`DeepPackage`, `QAdv`) has no costed mirror and
is refused: a value of type `H` is priced by `H.handlerBound` or `H.handlerMirror`, wherever it
occurs as a field or as the result of a reduction.

The registered declarations are unfolded where they are applied, so the generated statements
mention the definitions they stand for. A gate set, a handler cost and a bound appear in this
order: the gate sets of the circuit fields after the parameters of `S`, and for each handler
field its handler cost before its bound.

The mirror is elaborated from its printed source. A parameter with an inaccessible name (an
anonymous instance binder of a `variable` command) is printed under an accessible name. The
mirror of a universe-polymorphic structure `S.{u₁, …, uₘ}` is declared as
`S.Timed.{u₁, …, uₘ}`, with the universe levels of the constants in its field types printed.

## Main definitions

* `derive_timed_structure S` — define `S.Timed`, `S.Timed.Erases`, `S.Timed.TimeBound`
-/

public section

meta section

namespace CatCrypt.Tactics.DeriveTimedStructure

open Lean Elab Meta Term Command
open CatCrypt.Tactics.DeriveTimed

/-- How a field of a structure is mirrored. -/
inductive FieldKind where
  /-- A proposition: dropped. -/
  | prop
  /-- A type: kept. -/
  | type
  /-- First-order data or a data function: kept. -/
  | data
  /-- A function of `n` arguments into a tree of a registered kind: a function into costed
  trees, with a cost companion. -/
  | tree (n : Nat)
  /-- A function of `n` arguments into `SPComp β`: a function into `SPTree.Timed β`, with a
  cost companion. -/
  | comp (n : Nat)
  /-- A function of `n` arguments into a value of the circuit kind `H`: a function into the
  costed type `H.handlerMirror` over a gate set, with a cost companion. -/
  | circuit (n : Nat) (H : Name)
  /-- A function of `n` arguments into a value of the bounded kind `H`: kept, with a conjunct
  `H.handlerBound` in the time bound. -/
  | bounded (n : Nat) (H : Name)
  deriving Inhabited, BEq

/-- The result type `H a₁ ⋯ aₖ` of a field of a handler kind: whether the kind is a circuit
kind, the constant `H` and the arguments `aᵢ`. -/
structure HandlerHead where
  circuit : Bool
  head : Name
  args : Array Expr
  deriving Inhabited

/-- The handler kind of the type `b`, read from the declarations `H.handlerGateSet` (a circuit
kind) and `H.handlerBound` (a bounded kind) of its head constant `H`, as written or after
reducible unfolding. -/
def handlerHead? (b : Expr) : MetaM (Option HandlerHead) := do
  let env ← getEnv
  let look (e : Expr) : Option HandlerHead :=
    match e.getAppFn with
    | .const H _ =>
      if env.contains (H ++ `handlerGateSet) then some ⟨true, H, e.getAppArgs⟩
      else if env.contains (H ++ `handlerBound) then some ⟨false, H, e.getAppArgs⟩
      else none
    | _ => none
  if let some r := look (← instantiateMVars b) then return some r
  return look (← whnfR b)

/-- The registered declaration `n` applied to the explicit arguments `args`, unfolded once and
beta-reduced. -/
def regApp (n : Name) (args : Array Expr) : MetaM Expr := do
  let e ← mkAppM n args
  match ← unfoldDefinition? e with
  | some e' => return e'.headBeta
  | none => return e

/-- The type of the handler cost of the registered declaration `n`: the type of its binder
`pos` from the end, which mentions no other binder and no universe parameter. -/
def handlerType (n : Name) (pos : Nat) : MetaM Expr := do
  let info ← getConstInfo n
  forallTelescope info.type fun xs _ => do
    unless pos ≤ xs.size && 0 < pos do
      throwError "derive_timed_structure: `{n}` has fewer than {pos} binders"
    let t ← inferType xs[xs.size - pos]!
    if xs.any (t.containsFVar ·.fvarId!) || t.hasLevelParam then
      throwError "derive_timed_structure: the handler cost of `{n}` has a dependent type `{t}`"
    return t

/-- The kind of a field of type `t`. -/
def fieldKind (t : Expr) : MetaM FieldKind := do
  if ← isProp t then return .prop
  if ← isTypeFormerType t then return .type
  forallTelescope (← whnfR t) fun ys b => do
    if (← treeTy? b).isSome then return .tree ys.size
    if ← isSPCompType b then return .comp ys.size
    if let some hh ← handlerHead? b then
      return if hh.circuit then .circuit ys.size hh.head else .bounded ys.size hh.head
    return .data

/-- The mirrored type of a field of type `t` and kind `k`; `gs` is the gate set of a field of a
circuit kind. -/
def mirrorType (t : Expr) (k : FieldKind) (gs : Expr := default) : MetaM Expr := do
  match k with
  | .tree _ => costedType t
  | .comp _ =>
    forallTelescope (← whnfR t) fun ys b => do
      let b ← whnfR b
      mkForallFVars ys (mkApp (mkConst ``CatCrypt.Core.SPTree.Timed) b.appArg!)
  | .circuit _ H =>
    forallTelescope (← whnfR t) fun ys b => do
      let some hh ← handlerHead? b
        | throwError "derive_timed_structure: `{b}` is not of a handler kind"
      mkForallFVars ys (← regApp (H ++ `handlerMirror) (hh.args.push gs))
  | _ => return t

/-- The source text of the type `t` in a declaration, with the universe levels of constants
when `univs` holds. -/
def typeText (t : Expr) (univs : Bool := false) : MetaM String := do
  let fmt ← withOptions (fun o => o.setBool `pp.fullNames true |>.setBool `pp.funBinderTypes true
    |>.setBool `pp.universes univs) (ppExpr t)
  return fmt.pretty 100000

/-- The mirrored value of the field `f` of kind `k` and type `t` of the costed structure `A'`:
the field itself for a type, data or a field of a bounded kind, its erasure for a tree or a
computation. -/
def erasedField (A' : Expr) (f : Name) (k : FieldKind) (t : Expr) : MetaM Expr := do
  let v ← mkProjection A' f
  match k with
  | .tree n =>
    forallBoundedTelescope (← whnfR t) n fun ys b => do
      let some T ← treeTy? b | throwError "derive_timed_structure: `{b}` is not a tree"
      mkLambdaFVars ys (T.eraseE (mkAppN v ys))
  | .comp n =>
    forallBoundedTelescope (← whnfR t) n fun ys _ => do
      mkLambdaFVars ys (← mkAppM ``CatCrypt.Core.SPTree.compile
        #[← mkAppM ``CatCrypt.Core.SPTree.Timed.erase #[mkAppN v ys]])
  | _ => return v

/-- The type `t` with each of its first `n` binder names that is inaccessible (the anonymous
instance binder `[SampleableType W]` of a `variable` command, named `inst✝`) replaced by an
accessible name `instᵢ` distinct from the other binder names, so that a printed binder parses. -/
def accessibleBinders (t : Expr) (n : Nat) : Expr :=
  let names := collect t n #[]
  go t 0 names
where
  collect (t : Expr) (n : Nat) (acc : Array Name) : Array Name :=
    match n, t with
    | n + 1, .forallE nm _ b _ => collect b n (acc.push nm)
    | _, _ => acc
  go (t : Expr) (i : Nat) (names : Array Name) : Expr :=
    match t with
    | .forallE nm d b bi =>
      if i < names.size then
        let nm' := if nm.hasMacroScopes || nm.isAnonymous then
            let base := nm.eraseMacroScopes
            let base := if base.isAnonymous then `inst else base
            fresh (base.appendIndexAfter i) names
          else nm
        .forallE nm' d (go b (i + 1) names) bi
      else t
    | _ => t
  fresh (c : Name) (names : Array Name) : Name :=
    if names.contains c then c.appendAfter "'" else c

/-- The constructor type of `S` after its parameters, the parameters, and the fields of `S` with
their kinds, continued in `k`. -/
def withCtor {β : Type} (S : Name)
    (k : Array Expr → Expr → Array Name → TermElabM β) : TermElabM β := do
  let env ← getEnv
  let some (.inductInfo iv) := env.find? S
    | throwError "derive_timed_structure: `{S}` is not an inductive type"
  let some sinfo := getStructureInfo? env S
    | throwError "derive_timed_structure: `{S}` is not a structure"
  let ctor ← getConstInfoCtor iv.ctors[0]!
  forallBoundedTelescope (accessibleBinders ctor.type iv.numParams) iv.numParams fun ps rest =>
    k ps rest sinfo.fieldNames

/-- The gate-set parameters of the mirror: for each field `f` of a circuit kind `H`, the name
`fGS` and the type `H.handlerGateSet a₁ ⋯ aₖ`, which mentions the parameters `ps` only. -/
def gateSetTypes (ps : Array Expr) (rest : Expr) (fields : Array Name) :
    MetaM (Array (Name × Expr)) :=
  forallBoundedTelescope rest fields.size fun xs _ => do
    let mut acc := #[]
    for x in xs, f in fields do
      let d ← inferType x
      match ← fieldKind d with
      | .circuit _ H =>
        let g ← forallTelescope (← whnfR d) fun _ b => do
          let some hh ← handlerHead? b
            | throwError "derive_timed_structure: `{b}` is not of a handler kind"
          regApp (H ++ `handlerGateSet) hh.args
        if g.hasAnyFVar (fun id => !ps.any (·.fvarId! == id)) then
          throwError "derive_timed_structure: the gate set `{g}` of the field `{f}` depends on \
            a field or on an argument of the field"
        acc := acc.push (f.appendAfter "GS", g)
      | _ => pure ()
    return acc

/-- The constructor type of `S` after its parameters, the parameters, the gate-set parameters
of the mirror and the fields of `S`, continued in `k`. -/
def withCtorGS {β : Type} [Inhabited β] (S : Name)
    (k : Array Expr → Array Expr → Expr → Array Name → TermElabM β) : TermElabM β :=
  withCtor S fun ps rest fields => do
    let gts ← gateSetTypes ps rest fields
    withLocalDeclsDND gts fun gss => k ps gss rest fields

/-- The source text of the costed mirror `S.Timed` of the structure `S`. A universe-polymorphic
`S` gives a mirror declared with the universe parameters of `S`, and the constants in its types
are printed with their universe levels. -/
def mirrorText (S : Name) : TermElabM String :=
  withCtorGS S fun ps gss rest fields => do
    let lps := (← getConstInfo S).levelParams
    let univs := !lps.isEmpty
    let typeText (t : Expr) : MetaM String := typeText t univs
    let univText := if univs then ".{" ++ ", ".intercalate (lps.map toString) ++ "}" else ""
    -- The binder kinds of the parameters are those of the type `S`, not of its constructor.
    let infos ← forallBoundedTelescope (← getConstInfo S).type ps.size fun qs _ =>
      qs.mapM fun q => q.fvarId!.getBinderInfo
    let mut binders := ""
    for p in ps, bi in infos do
      let d ← p.fvarId!.getDecl
      let ty ← typeText d.type
      binders := binders ++ match bi with
        | .implicit => s!" \{{d.userName} : {ty}}"
        | .instImplicit => s!" [{d.userName} : {ty}]"
        | .strictImplicit => s!" ⦃{d.userName} : {ty}⦄"
        | .default => s!" ({d.userName} : {ty})"
    for g in gss do
      let d ← g.fvarId!.getDecl
      binders := binders ++ s!" ({d.userName} : {← typeText d.type})"
    forallBoundedTelescope rest fields.size fun xs _ => do
      let mut text := ""
      let mut hidden : Array Expr := #[]
      let mut gi := 0
      for x in xs, f in fields do
        let d ← inferType x
        let k ← fieldKind d
        if !(k matches .prop) && hidden.any (d.containsFVar ·.fvarId!) then
          throwError "derive_timed_structure: the type of the field `{f}` depends on a proof \
            or a computation field"
        match k with
        | .prop => hidden := hidden.push x
        | .tree _ | .comp _ =>
          hidden := hidden.push x
          text := text ++ s!"\n  {f} : {← typeText (← mirrorType d k)}"
          text := text ++ s!"\n  {f.appendAfter "Cost"} : {← typeText (← companionType d)}"
        | .circuit _ _ =>
          hidden := hidden.push x
          text := text ++ s!"\n  {f} : {← typeText (← mirrorType d k gss[gi]!)}"
          text := text ++ s!"\n  {f.appendAfter "Cost"} : {← typeText (← companionType d)}"
          gi := gi + 1
        | _ => text := text ++ s!"\n  {f} : {← typeText d}"
      return s!"structure {`_root_ ++ S ++ `Timed}{univText}{binders} where{text}"

/-- Define the erasure relation `S.Timed.Erases A' A`: some proofs of the proposition fields of
`S` and some values of its circuit fields, each erasing the corresponding field of `A'`,
complete the erasures of the other fields of `A'` to `A`. -/
def defineErases (S : Name) (lvls : List Level) (lps : List Name) : TermElabM Unit := do
  let (type, value) ← withCtorGS S fun ps gss rest fields => do
    let sT := mkAppN (mkConst S lvls) ps
    let tT := mkAppN (mkConst (S ++ `Timed) lvls) (ps ++ gss)
    withLocalDeclD `A' tT fun A' => withLocalDeclD `A sT fun A => do
      let rec go (i : Nat) (ty : Expr) (vals proofs conjs : Array Expr) : TermElabM Expr := do
        if h : i < fields.size then
          let f := fields[i]
          let .forallE nm d b _ ← whnf ty
            | throwError "derive_timed_structure: unexpected constructor type"
          match ← fieldKind d with
          | .prop =>
            withLocalDeclD nm d fun p =>
              go (i + 1) (b.instantiate1 p) (vals.push p) (proofs.push p) conjs
          | .circuit n H =>
            let v ← mkProjection A' f
            withLocalDeclD nm d fun e => do
              let c ← forallBoundedTelescope (← whnfR d) n fun ys _ => do
                mkForallFVars ys (← regApp (H ++ `handlerErases) #[mkAppN v ys, mkAppN e ys])
              go (i + 1) (b.instantiate1 e) (vals.push e) (proofs.push e) (conjs.push c)
          | k =>
            let v ← erasedField A' f k d
            go (i + 1) (b.instantiate1 v) (vals.push v) proofs conjs
        else
          let eq ← mkEq A (mkAppN (mkConst (S.str "mk") lvls) (ps ++ vals))
          let mut body := mkAndN (conjs.push eq).toList
          for p in proofs.reverse do
            body ← mkAppM ``Exists #[← mkLambdaFVars #[p] body]
          return body
      let body ← go 0 rest #[] #[] #[]
      let bs := ps ++ gss ++ #[A', A]
      return (← mkForallFVars bs (mkSort .zero), ← mkLambdaFVars bs body)
  addTimedDef (S ++ `Timed ++ `Erases) lps type value

/-- Define the time bound `S.Timed.TimeBound A' Ts`: for each tree or computation field `f`
of `A'` a bound `T_f` on the time of the step-prefixed tree `(A'.fCost ys, A'.f ys)` at every
`ys`, the cost of computing the tree followed by its run; for each field of a circuit kind a
handler cost `h_f` and a bound `T_f` on `A'.fCost ys + H.handlerTime (A'.f ys) h_f`; for each
field of a bounded kind a handler cost `h_f` and a bound `T_f` with
`H.handlerBound (A'.f ys) h_f T_f`. -/
def defineTimeBound (S : Name) (lvls : List Level) (lps : List Name) : TermElabM Unit := do
  let (type, value) ← withCtorGS S fun ps gss rest fields => do
    let tT := mkAppN (mkConst (S ++ `Timed) lvls) (ps ++ gss)
    withLocalDeclD `A' tT fun A' => do
      let fs ← forallBoundedTelescope rest fields.size fun xs _ =>
        (xs.zip fields).mapM fun (x, f) => do
          let d ← inferType x
          return (f, d, ← fieldKind d)
      let rec go (i : Nat) (bounds conj : Array Expr) : TermElabM (Expr × Expr) := do
        if h : i < fs.size then
          let (f, _, k) := fs[i]
          match k with
          | .tree n | .comp n =>
            -- The field type may mention earlier type fields: instantiate it at `A'`.
            let v ← mkProjection A' f
            let cv ← mkProjection A' (f.appendAfter "Cost")
            let vt ← inferType v
            withLocalDeclD (f.appendAfter "Time") (mkConst ``Nat) fun T => do
              let tb ← forallBoundedTelescope (← whnfR vt) n fun ys b => do
                let b ← whnfR b
                let p ← mkAppM ``Prod.mk #[mkAppN cv ys, mkAppN v ys]
                let c ← if b.isAppOf ``CatCrypt.Crypto.OracleAdv.Timed then
                    mkAppM ``CatCrypt.Crypto.OracleAdv.Timed.StepTimeBound #[p, T]
                  else
                    mkAppM ``LE.le #[← mkAppM ``CatCrypt.Core.SPTree.Timed.stepTime #[p], T]
                mkForallFVars ys c
              go (i + 1) (bounds.push T) (conj.push tb)
          | .circuit n H =>
            let v ← mkProjection A' f
            let cv ← mkProjection A' (f.appendAfter "Cost")
            let vt ← inferType v
            let hTy ← handlerType (H ++ `handlerTime) 1
            withLocalDeclD (f.appendAfter "Handler") hTy fun hf =>
            withLocalDeclD (f.appendAfter "Time") (mkConst ``Nat) fun T => do
              let tb ← forallBoundedTelescope (← whnfR vt) n fun ys _ => do
                let t ← regApp (H ++ `handlerTime) #[mkAppN v ys, hf]
                mkForallFVars ys (← mkAppM ``LE.le #[mkNatAdd (mkAppN cv ys) t, T])
              go (i + 1) ((bounds.push hf).push T) (conj.push tb)
          | .bounded n H =>
            let v ← mkProjection A' f
            let vt ← inferType v
            let hTy ← handlerType (H ++ `handlerBound) 2
            withLocalDeclD (f.appendAfter "Handler") hTy fun hf =>
            withLocalDeclD (f.appendAfter "Time") (mkConst ``Nat) fun T => do
              let tb ← forallBoundedTelescope (← whnfR vt) n fun ys _ => do
                mkForallFVars ys (← regApp (H ++ `handlerBound) #[mkAppN v ys, hf, T])
              go (i + 1) ((bounds.push hf).push T) (conj.push tb)
          | _ => go (i + 1) bounds conj
        else
          let body := mkAndN conj.toList
          let bs := ps ++ gss ++ #[A'] ++ bounds
          return (← mkForallFVars bs (mkSort .zero), ← mkLambdaFVars bs body)
      go 0 #[] #[]
  addTimedDef (S ++ `Timed ++ `TimeBound) lps type value

/-- Define the costed mirror `S.Timed` of the structure `S`, its erasure relation
`S.Timed.Erases` and its time bound `S.Timed.TimeBound`. -/
def deriveTimedStructure (S : Name) : CommandElabM Unit := do
  let env ← getEnv
  for r in [`handlerBound, `handlerMirror] do
    if env.contains (S ++ r) then
      throwError "derive_timed_structure: `{S}` is a handler kind, priced by `{S ++ r}` \
        wherever a value of it occurs; it has no costed mirror"
  let text ← liftTermElabM (mirrorText S)
  let stx ← match Parser.runParserCategory (← getEnv) `command text with
    | .ok stx => pure stx
    | .error e => throwError "derive_timed_structure: the mirror does not parse: {e}\n{text}"
  elabCommand stx
  liftTermElabM do
    let some (.inductInfo iv) := (← getEnv).find? S | throwError "unknown `{S}`"
    let some (.inductInfo tv) := (← getEnv).find? (S ++ `Timed)
      | throwError "derive_timed_structure: `{S ++ `Timed}` was not defined"
    unless tv.levelParams.length == iv.levelParams.length do
      throwError "derive_timed_structure: the mirror of `{S}` has other universe parameters"
    let lvls := iv.levelParams.map mkLevelParam
    defineErases S lvls iv.levelParams
    defineTimeBound S lvls iv.levelParams

/-- `derive_timed_structure S` defines the costed mirror `S.Timed` of the structure `S`, with
`S.Timed.Erases` and `S.Timed.TimeBound`. -/
syntax (name := deriveTimedStructureCmd) "derive_timed_structure " ident : command

@[command_elab deriveTimedStructureCmd]
def elabDeriveTimedStructure : CommandElab := fun stx => do
  let S ← liftCoreM <| realizeGlobalConstNoOverload stx[1]
  deriveTimedStructure S

end CatCrypt.Tactics.DeriveTimedStructure

end

end
