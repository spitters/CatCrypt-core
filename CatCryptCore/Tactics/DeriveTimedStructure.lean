/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimed

/-!
# Costed mirrors of structures

`derive_timed_structure S` takes a structure `S` whose fields are types, propositions, data,
trees of a registered tree kind (`CatCryptCore.Tactics.DeriveTimed`) or computations
`SPComp β`, each possibly under binders, and defines

* the costed mirror `S.Timed`, with the parameters of `S` and, field by field: a type field
  and a data field kept; a proposition field dropped; a field `f : X₁ → … → Xₙ → T` into
  trees or computations replaced by `f : X₁ → … → Xₙ → T'` with `T'` the costed tree type
  (`SPTree.Timed β` for `SPComp β`), followed for `n > 0` by its cost companion
  `fCost : X₁ → … → Xₙ → ℕ`;
* the erasure relation `S.Timed.Erases A' A`: some proofs of the proposition fields complete
  the fields of `A'`, with each tree field erased (`erase`, and `SPTree.compile` after it for a
  computation), to `A`; the mirror has no proof fields, so erasure is a relation and not a
  function;
* the time bound `S.Timed.TimeBound A' Ts`: for each tree or computation field a bound on the
  time of its costed trees (`OracleAdv.Timed.TimeBound` or `SPTree.Timed.time`), and for each
  cost companion a bound on its values. The stages of a multi-stage adversary run separately,
  so their bounds are separate parameters and are not added.

This is the translation of a structure type in the call-by-value writer translation of the
design of `derive_timed`: the translation of a product is the product of the translations.

A field whose type depends on a proposition field or on a tree or computation field is
refused.

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
  trees, with a cost companion when `n > 0`. -/
  | tree (n : Nat)
  /-- A function of `n` arguments into `SPComp β`: a function into `SPTree.Timed β`, with a
  cost companion when `n > 0`. -/
  | comp (n : Nat)
  deriving Inhabited, BEq

/-- The kind of a field of type `t`. -/
def fieldKind (t : Expr) : MetaM FieldKind := do
  if ← isProp t then return .prop
  if ← isTypeFormerType t then return .type
  forallTelescope (← whnfR t) fun ys b => do
    if (← treeTy? b).isSome then return .tree ys.size
    if ← isSPCompType b then return .comp ys.size
    return .data

/-- The mirrored type of a field of type `t` and kind `k`. -/
def mirrorType (t : Expr) (k : FieldKind) : MetaM Expr := do
  match k with
  | .tree _ => costedType t
  | .comp _ =>
    forallTelescope (← whnfR t) fun ys b => do
      let b ← whnfR b
      mkForallFVars ys (mkApp (mkConst ``CatCrypt.Core.SPTree.Timed) b.appArg!)
  | _ => return t

/-- The source text of the type `t` in a declaration. -/
def typeText (t : Expr) : MetaM String := do
  let fmt ← withOptions (fun o => o.setBool `pp.fullNames true |>.setBool `pp.funBinderTypes true
    |>.setBool `pp.universes false) (ppExpr t)
  return fmt.pretty 100000

/-- The mirrored value of the field `f` of kind `k` and type `t` of the costed structure `A'`:
the field itself for a type or data, its erasure for a tree or a computation. -/
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
  forallBoundedTelescope ctor.type iv.numParams fun ps rest => k ps rest sinfo.fieldNames

/-- The source text of the costed mirror `S.Timed` of the structure `S`. -/
def mirrorText (S : Name) : TermElabM String :=
  withCtor S fun ps rest fields => do
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
    forallBoundedTelescope rest fields.size fun xs _ => do
      let mut text := ""
      let mut hidden : Array Expr := #[]
      for x in xs, f in fields do
        let d ← inferType x
        if hidden.any (d.containsFVar ·.fvarId!) then
          throwError "derive_timed_structure: the type of the field `{f}` depends on a proof \
            or a computation field"
        let k ← fieldKind d
        match k with
        | .prop => hidden := hidden.push x
        | .tree n | .comp n =>
          hidden := hidden.push x
          text := text ++ s!"\n  {f} : {← typeText (← mirrorType d k)}"
          if n > 0 then
            text := text ++ s!"\n  {f.appendAfter "Cost"} : {← typeText (← companionType d)}"
        | _ => text := text ++ s!"\n  {f} : {← typeText d}"
      return s!"structure {`_root_ ++ S ++ `Timed}{binders} where{text}"

/-- Define the erasure relation `S.Timed.Erases A' A`: some proofs of the proposition fields of
`S` complete the erasures of the fields of `A'` to `A`. -/
def defineErases (S : Name) (lvls : List Level) (lps : List Name) : TermElabM Unit := do
  let (type, value) ← withCtor S fun ps rest fields => do
    let sT := mkAppN (mkConst S lvls) ps
    let tT := mkAppN (mkConst (S ++ `Timed) lvls) ps
    withLocalDeclD `A' tT fun A' => withLocalDeclD `A sT fun A => do
      let rec go (i : Nat) (ty : Expr) (vals proofs : Array Expr) : TermElabM Expr := do
        if h : i < fields.size then
          let f := fields[i]
          let .forallE n d b _ ← whnf ty
            | throwError "derive_timed_structure: unexpected constructor type"
          match ← fieldKind d with
          | .prop =>
            withLocalDeclD n d fun p => go (i + 1) (b.instantiate1 p) (vals.push p) (proofs.push p)
          | k =>
            let v ← erasedField A' f k d
            go (i + 1) (b.instantiate1 v) (vals.push v) proofs
        else
          let mut body ← mkEq A (mkAppN (mkConst (S.str "mk") lvls) (ps ++ vals))
          for p in proofs.reverse do
            body ← mkAppM ``Exists #[← mkLambdaFVars #[p] body]
          return body
      let body ← go 0 rest #[] #[]
      return (← mkForallFVars (ps ++ #[A', A]) (mkSort .zero), ← mkLambdaFVars (ps ++ #[A', A]) body)
  addTimedDef (S ++ `Timed ++ `Erases) lps type value

/-- Define the time bound `S.Timed.TimeBound A' Ts`: for each tree or computation field `f`
of `A'` a bound `T_f` on its time, and for each cost companion `fCost` a bound `a_f`. -/
def defineTimeBound (S : Name) (lvls : List Level) (lps : List Name) : TermElabM Unit := do
  let (type, value) ← withCtor S fun ps rest fields => do
    let tT := mkAppN (mkConst (S ++ `Timed) lvls) ps
    withLocalDeclD `A' tT fun A' => do
      let fs ← forallBoundedTelescope rest fields.size fun xs _ =>
        (xs.zip fields).mapM fun (x, f) => do
          let d ← inferType x
          return (f, d, ← fieldKind d)
      let rec go (i : Nat) (bounds conj : Array Expr) : TermElabM (Expr × Expr) := do
        if h : i < fs.size then
          let (f, d, k) := fs[i]
          match k with
          | .tree n | .comp n =>
            -- The field type may mention earlier type fields: instantiate it at `A'`.
            let v ← mkProjection A' f
            let vt ← inferType v
            withLocalDeclD (f.appendAfter "Time") (mkConst ``Nat) fun T => do
              let tb ← forallBoundedTelescope (← whnfR vt) n fun ys b => do
                let b ← whnfR b
                let c ← if b.isAppOf ``CatCrypt.Crypto.OracleAdv.Timed then
                    mkAppM ``CatCrypt.Crypto.OracleAdv.Timed.TimeBound #[mkAppN v ys, T]
                  else
                    mkAppM ``LE.le #[← mkAppM ``CatCrypt.Core.SPTree.Timed.time #[mkAppN v ys], T]
                mkForallFVars ys c
              if n > 0 then
                let cv ← mkProjection A' (f.appendAfter "Cost")
                withLocalDeclD (f.appendAfter "CostBound") (mkConst ``Nat) fun a => do
                  let cb ← forallBoundedTelescope (← whnfR (← inferType cv)) n fun ys _ => do
                    mkForallFVars ys (← mkAppM ``LE.le #[mkAppN cv ys, a])
                  go (i + 1) (bounds.push T |>.push a) (conj.push tb |>.push cb)
              else go (i + 1) (bounds.push T) (conj.push tb)
          | _ => go (i + 1) bounds conj
        else
          let body := mkAndN conj.toList
          return (← mkForallFVars (ps ++ #[A'] ++ bounds) (mkSort .zero),
            ← mkLambdaFVars (ps ++ #[A'] ++ bounds) body)
      go 0 #[] #[]
  addTimedDef (S ++ `Timed ++ `TimeBound) lps type value

/-- Define the costed mirror `S.Timed` of the structure `S`, its erasure relation
`S.Timed.Erases` and its time bound `S.Timed.TimeBound`. -/
def deriveTimedStructure (S : Name) : CommandElabM Unit := do
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
