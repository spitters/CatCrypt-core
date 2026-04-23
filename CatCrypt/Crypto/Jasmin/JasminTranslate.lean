/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.JasminVar
import CatCrypt.Crypto.Jasmin.JasminOps
import CatCrypt.Deep.RawCode

/-!
# Jasmin → RawCode Translation

This file defines the translation from Jasmin programs (`InstrR`, `Cmd`)
to CatCrypt `RawCode`, following `jasmin_translate.v`.

## Architecture

The translation is structured as:
1. `translatePExpr` — expressions to RawCode returning typed values
2. `translateWriteLVal` — l-values write operations
3. `translateInstrR` — instructions to RawCode
4. `translateCmd` — command sequences

Function calls are handled by inlining (matching the Rocq approach).

## References

- `jasmin_translate.v`: lines 1712–4300
-/

namespace CatCrypt.Crypto.Jasmin

open CatCrypt.Deep (RawCode)
-- Note: we use CatCrypt.Core.Location explicitly to avoid ambiguity with Deep.Location

noncomputable section

/-! ## Translation Monad

We work in `RawCode TypedValue` for expressions and `RawCode (ULift Unit)` for
statements. All heap access goes through `TypedValue` to avoid type-level
dependence on `Location.ty`. -/

/-- Translation environment: translated function bodies for inlining. -/
structure TransEnv where
  fdefs : FunName → Option (ScopeId → List TypedValue → RawCode (ULift Unit))

/-- Translation result: updated scope + code. -/
structure TransResult where
  newSid : ScopeId
  code : RawCode (ULift Unit)

/-! ## Variable Read/Write via TypedValue

To avoid type mismatches between `Location.ty` and `SType.encode`, we
build specialized get/put operations that pattern-match on the variable
type and construct the appropriate RawCode directly. -/

/-- Locations for each Jasmin type. These are distinct from `translateVar`
    because they use concrete types that Lean can see through. -/
private def boolLoc (sid : ScopeId) (v : Var) : CatCrypt.Core.Location :=
  { id := varLocId sid v, ty := Bool }

private def intLoc (sid : ScopeId) (v : Var) : CatCrypt.Core.Location :=
  { id := varLocId sid v, ty := BitVec 64,
    fintype := CatCrypt.Crypto.instFintypeBitVec 64 }

private def arrLoc (sid : ScopeId) (v : Var) (n : Nat) : CatCrypt.Core.Location :=
  { id := varLocId sid v, ty := JArray n,
    fintype := JArray.instFintypeJArray n }

private def wordLoc (sid : ScopeId) (v : Var) (ws : WSize) : CatCrypt.Core.Location :=
  { id := varLocId sid v, ty := BitVec ws.bits,
    fintype := CatCrypt.Crypto.instFintypeBitVec ws.bits }

/-- Read a variable as a TypedValue. -/
def readVar (sid : ScopeId) (v : Var) : RawCode TypedValue :=
  match v.vtype with
  | .sbool =>
    RawCode.bind (RawCode.get (boolLoc sid v))
      fun x => RawCode.ret ⟨.sbool, x.down⟩
  | .sint =>
    RawCode.bind (RawCode.get (intLoc sid v))
      fun x => RawCode.ret ⟨.sint, wordToInt .U64 x.down⟩
  | .sarr n =>
    RawCode.bind (RawCode.get (arrLoc sid v n))
      fun x => RawCode.ret ⟨.sarr n, x.down⟩
  | .sword ws =>
    RawCode.bind (RawCode.get (wordLoc sid v ws))
      fun x => RawCode.ret ⟨.sword ws, x.down⟩

/-- Read a GVar. -/
def readGVar (sid : ScopeId) (gv : GVar) : RawCode TypedValue :=
  readVar sid gv.gv.var

/-- Write a TypedValue to a variable. -/
def writeVar (sid : ScopeId) (v : Var) (tv : TypedValue) : RawCode (ULift Unit) :=
  match v.vtype, tv with
  | .sbool, ⟨.sbool, val⟩ => RawCode.put (boolLoc sid v) val
  | .sint, ⟨.sint, val⟩ => RawCode.put (intLoc sid v) (intToWord .U64 val)
  | .sarr n, ⟨.sarr m, val⟩ =>
    if h : n = m then RawCode.put (arrLoc sid v n) (h ▸ val)
    else RawCode.ret ⟨()⟩
  | .sword ws1, ⟨.sword ws2, val⟩ =>
    if _h : ws1 = ws2 then
      RawCode.put (wordLoc sid v ws1) (truncateWord ws2 ws1 val)
    else RawCode.put (wordLoc sid v ws1) (truncateWord ws2 ws1 val)
  | _, _ => RawCode.ret ⟨()⟩

/-! ## Expression Translation -/

/-- Evaluate a unary operation. -/
def evalSop1 (op : SOp1) (v : TypedValue) : TypedValue :=
  match op, v with
  | .Oword_of_int ws, ⟨.sint, z⟩ => ⟨.sword ws, intToWord ws z⟩
  | .Oint_of_word ws, ⟨.sword ws', w⟩ =>
    if h : ws = ws' then ⟨.sint, wordToInt ws (h ▸ w)⟩ else ⟨.sint, 0⟩
  | .Ozeroext wso wsi, ⟨.sword ws, w⟩ =>
    if h : wsi = ws then ⟨.sword wso, zeroExtendWord wsi wso (h ▸ w)⟩
    else ⟨.sword wso, 0⟩
  | .Osignext wso wsi, ⟨.sword ws, w⟩ =>
    if h : wsi = ws then ⟨.sword wso, signExtendWord wsi wso (h ▸ w)⟩
    else ⟨.sword wso, 0⟩
  | .Onot, ⟨.sbool, b⟩ => ⟨.sbool, !b⟩
  | .Olnot ws, ⟨.sword ws', w⟩ =>
    if h : ws = ws' then ⟨.sword ws, ~~~(h ▸ w)⟩ else ⟨.sword ws, 0⟩
  | .Oneg ws, ⟨.sword ws', w⟩ =>
    if h : ws = ws' then ⟨.sword ws, -(h ▸ w)⟩ else ⟨.sword ws, 0⟩
  | _, v => v

/-- Evaluate a binary operation. -/
def evalSop2 (op : SOp2) (v1 v2 : TypedValue) : TypedValue :=
  match op, v1, v2 with
  | .Obeq, ⟨.sbool, a⟩, ⟨.sbool, b⟩ => ⟨.sbool, a == b⟩
  | .Oand, ⟨.sbool, a⟩, ⟨.sbool, b⟩ => ⟨.sbool, a && b⟩
  | .Oor, ⟨.sbool, a⟩, ⟨.sbool, b⟩ => ⟨.sbool, a || b⟩
  | .Oadd ws, ⟨.sword _, a⟩, ⟨.sword _, b⟩ =>
    ⟨.sword ws, a.truncate ws.bits + b.truncate ws.bits⟩
  | .Osub ws, ⟨.sword _, a⟩, ⟨.sword _, b⟩ =>
    ⟨.sword ws, a.truncate ws.bits - b.truncate ws.bits⟩
  | .Omul ws, ⟨.sword _, a⟩, ⟨.sword _, b⟩ =>
    ⟨.sword ws, a.truncate ws.bits * b.truncate ws.bits⟩
  | .Oland ws, ⟨.sword _, a⟩, ⟨.sword _, b⟩ =>
    ⟨.sword ws, a.truncate ws.bits &&& b.truncate ws.bits⟩
  | .Olor ws, ⟨.sword _, a⟩, ⟨.sword _, b⟩ =>
    ⟨.sword ws, a.truncate ws.bits ||| b.truncate ws.bits⟩
  | .Olxor ws, ⟨.sword _, a⟩, ⟨.sword _, b⟩ =>
    ⟨.sword ws, a.truncate ws.bits ^^^ b.truncate ws.bits⟩
  | .Olsr ws, ⟨.sword _, a⟩, ⟨.sword _, b⟩ =>
    ⟨.sword ws, a.truncate ws.bits >>> (b.truncate ws.bits).toNat⟩
  | .Olsl ws, ⟨.sword _, a⟩, ⟨.sword _, b⟩ =>
    ⟨.sword ws, a.truncate ws.bits <<< (b.truncate ws.bits).toNat⟩
  | .Oasr ws, ⟨.sword _, a⟩, ⟨.sword _, b⟩ =>
    ⟨.sword ws, BitVec.sshiftRight (a.truncate ws.bits) (b.truncate ws.bits).toNat⟩
  | .Oeq ws, ⟨.sword _, a⟩, ⟨.sword _, b⟩ =>
    ⟨.sbool, a.truncate ws.bits == b.truncate ws.bits⟩
  | .Oneq ws, ⟨.sword _, a⟩, ⟨.sword _, b⟩ =>
    ⟨.sbool, a.truncate ws.bits != b.truncate ws.bits⟩
  | _, v1, _ => v1

/-- Translate a Jasmin expression to RawCode returning a TypedValue. -/
def translatePExpr (sid : ScopeId) : PExpr → RawCode TypedValue
  | .Pconst z => .ret ⟨.sint, z⟩
  | .Pbool b => .ret ⟨.sbool, b⟩
  | .Parr_init n => .ret ⟨.sarr n, fun _ => 0⟩
  | .Pvar gv => readGVar sid gv
  | .Pget _aa ws x idx =>
    .bind (readGVar sid x) fun arrTv =>
    .bind (translatePExpr sid idx) fun idxTv =>
    match arrTv, idxTv with
    | ⟨.sarr _, arr⟩, ⟨.sint, i⟩ =>
      .ret ⟨.sword ws, JArray.getWord arr ws i.toNat⟩
    | _, _ => .ret ⟨.sword ws, 0⟩
  | .Psub _aa _ws _len x _idx =>
    .bind (readGVar sid x) fun arrTv => .ret arrTv
  | .Pload ws x off =>
    .bind (readVar sid x.var) fun _addrTv =>
    .bind (translatePExpr sid off) fun _offTv =>
    .bind (.get memLoc) fun memUl =>
      -- Simplified: read word at offset 0 from memory
      .ret ⟨.sword ws, JArray.getWord memUl.down ws 0⟩
  | .Papp1 op e =>
    .bind (translatePExpr sid e) fun v => .ret (evalSop1 op v)
  | .Papp2 op e1 e2 =>
    .bind (translatePExpr sid e1) fun v1 =>
    .bind (translatePExpr sid e2) fun v2 =>
    .ret (evalSop2 op v1 v2)
  | .PappN _op es => trPExprList sid es
  | .Pif _ty cond etrue efalse =>
    .bind (translatePExpr sid cond) fun condTv =>
    match condTv with
    | ⟨.sbool, true⟩ => translatePExpr sid etrue
    | ⟨.sbool, false⟩ => translatePExpr sid efalse
    | _ => translatePExpr sid etrue
where
  trPExprList (sid : ScopeId) : List PExpr → RawCode TypedValue
    | [] => .ret ⟨.sbool, false⟩
    | [e] => translatePExpr sid e
    | e :: es => .bind (translatePExpr sid e) fun _ => trPExprList sid es

/-- Evaluate a list of expressions, collecting all results. -/
def translatePExprAll (sid : ScopeId) : List PExpr → RawCode (List TypedValue)
  | [] => .ret []
  | e :: es =>
    .bind (translatePExpr sid e) fun v =>
    .bind (translatePExprAll sid es) fun vs =>
    .ret (v :: vs)

/-! ## L-Value Write Translation -/

/-- Write a typed value to an l-value. -/
def translateWriteLVal (sid : ScopeId) (lv : LVal) (tv : TypedValue) :
    RawCode (ULift Unit) :=
  match lv with
  | .Lnone _ _ => .ret ⟨()⟩
  | .Lvar x => writeVar sid x.var tv
  | .Lmem _ws _x _off => .ret ⟨()⟩  -- memory store (simplified)
  | .Laset _aa ws x idx =>
    .bind (readVar sid x.var) fun arrTv =>
    .bind (translatePExpr sid idx) fun idxTv =>
    match arrTv, idxTv, tv with
    | ⟨.sarr n, arr⟩, ⟨.sint, i⟩, ⟨.sword _, val⟩ =>
      writeVar sid x.var ⟨.sarr n, JArray.setWord arr ws i.toNat (val.truncate ws.bits)⟩
    | _, _, _ => .ret ⟨()⟩
  | .Lasub _ _ _ _ _ => .ret ⟨()⟩

/-- Write values to l-values pairwise. -/
def translateWriteLVals (sid : ScopeId) :
    List LVal → List TypedValue → RawCode (ULift Unit)
  | [], _ | _, [] => .ret ⟨()⟩
  | lv :: lvs, tv :: tvs =>
    .bind (translateWriteLVal sid lv tv) fun _ =>
    translateWriteLVals sid lvs tvs

/-! ## For-Loop -/

/-- Generate loop index range. -/
def loopRange (r : Range) : List Int :=
  match r.dir with
  | .UpTo => (List.range (r.hi - r.lo)).map fun j => ((j + r.lo : Nat) : Int)
  | .DownTo => (List.range (r.hi - r.lo)).map fun j => ((r.hi - 1 - j : Nat) : Int)

-- ## Instruction Translation

mutual
/-- Translate instructions. `fuel` bounds recursion depth. -/
def translateInstrR (env : TransEnv) (sid : ScopeId) (fuel : Nat) :
    InstrR → TransResult
  | .Cassgn lv _tag ty e =>
    { newSid := sid,
      code := .bind (translatePExpr sid e) fun tv =>
        translateWriteLVal sid lv ⟨ty, coerceValue tv.ty ty tv.val⟩ }
  | .Copn lvs _tag op es =>
    { newSid := sid,
      code := .bind (translatePExprAll sid es) fun args =>
        match execSopn (match op with | .Oasm aop => aop) args with
        | .ok results => translateWriteLVals sid lvs results
        | .unsupported _ => .ret ⟨()⟩ }
  | .Cif cond cthen celse =>
    let thenResult := translateCmd env cthen sid fuel
    let elseResult := translateCmd env celse thenResult.newSid fuel
    { newSid := elseResult.newSid,
      code := .bind (translatePExpr sid cond) fun condTv =>
        match condTv with
        | ⟨.sbool, true⟩ => thenResult.code
        | ⟨.sbool, false⟩ => elseResult.code
        | _ => thenResult.code }
  | .Cfor v range body =>
    let (sid', _) := freshId sid
    { newSid := sid',
      code := translateForLoop env sid v.var (loopRange range) body fuel }
  | .Cwhile _ _ _ => { newSid := sid, code := .fail }
  | .Ccall _ii _lvs fn args =>
    let (sid', sid'') := freshId sid
    { newSid := sid',
      code := .bind (translatePExprAll sid args) fun argVals =>
        match env.fdefs fn with
        | some body =>
          .bind (body sid'' argVals) fun _ => .ret ⟨()⟩
        | none => .ret ⟨()⟩ }

/-- Translate a for-loop by unrolling. -/
def translateForLoop (env : TransEnv) (sid : ScopeId) (v : Var)
    (indices : List Int) (body : Cmd) (fuel : Nat) : RawCode (ULift Unit) :=
  match indices with
  | [] => .ret ⟨()⟩
  | i :: rest =>
    .bind (writeVar sid v ⟨.sint, i⟩) fun _ =>
    let bodyResult := translateCmd env body sid fuel
    .bind bodyResult.code fun _ =>
    translateForLoop env sid v rest body fuel

/-- Translate a command (instruction sequence). -/
def translateCmd (env : TransEnv) (instrs : Cmd) (sid : ScopeId) (fuel : Nat) :
    TransResult :=
  match fuel with
  | 0 => { newSid := sid, code := .fail }
  | fuel' + 1 =>
    match instrs with
    | [] => { newSid := sid, code := .ret ⟨()⟩ }
    | i :: is =>
      let iResult := translateInstrR env sid fuel' i
      let restResult := translateCmd env is iResult.newSid fuel'
      { newSid := restResult.newSid,
        code := .bind iResult.code fun _ => restResult.code }
end

/-! ## Function Translation -/

/-- Translate a function: write args, execute body, read results. -/
def translateFun (env : TransEnv) (fd : FunDecl) (sid : ScopeId)
    (args : List TypedValue) (fuel : Nat) : RawCode (List TypedValue) :=
  let writeArgs := writeParams sid fd.params args
  let bodyResult := translateCmd env fd.body sid fuel
  .bind writeArgs fun _ =>
  .bind bodyResult.code fun _ =>
  readResults sid fd.results
where
  writeParams (sid : ScopeId) : List FunParam → List TypedValue → RawCode (ULift Unit)
    | [], _ | _, [] => .ret ⟨()⟩
    | p :: ps, v :: vs =>
      .bind (writeVar sid p.var.var v) fun _ => writeParams sid ps vs
  readResults (sid : ScopeId) : List VarI → RawCode (List TypedValue)
    | [] => .ret []
    | vi :: vis =>
      .bind (readVar sid vi.var) fun tv =>
      .bind (readResults sid vis) fun tvs => .ret (tv :: tvs)

/-- Build translation environment from program (bottom-up). -/
def buildTransEnv (prog : JasminProg) (fuel : Nat) : TransEnv :=
  prog.funcs.foldl (fun env fd =>
    { fdefs := fun fn =>
        if fn == fd.name then
          some (fun sid args =>
            .bind (translateFun env fd sid args fuel) fun _ => .ret ⟨()⟩)
        else env.fdefs fn }
  ) { fdefs := fun _ => none }

/-- Translate an entry function of a program. -/
def translateProg (prog : JasminProg) (entryFn : FunName)
    (args : List TypedValue) (fuel : Nat := 1000) :
    Option (RawCode (List TypedValue)) :=
  let env := buildTransEnv prog fuel
  match prog.getFun entryFn with
  | some fd => some (translateFun env fd 1 args fuel)
  | none => none

/-! ## Bridge Lemmas -/

@[simp] lemma translateVar_sword_ty (sid : ScopeId) (x : String) (ws : WSize) :
    (translateVar sid { vname := x, vtype := .sword ws }).ty = BitVec ws.bits := rfl

lemma readVar_sword_eq (sid : ScopeId) (x : String) (ws : WSize) :
    readVar sid { vname := x, vtype := .sword ws } =
    RawCode.bind (RawCode.get (translateVar sid { vname := x, vtype := .sword ws }))
      fun y => RawCode.ret ⟨.sword ws, y.down⟩ := rfl

lemma writeVar_sarr_eq (sid : ScopeId) (x : String) (n : Nat) (val : JArray n) :
    writeVar sid { vname := x, vtype := .sarr n } ⟨.sarr n, val⟩ =
    RawCode.put (translateVar sid { vname := x, vtype := .sarr n }) val := by
  simp only [writeVar, arrLoc, translateVar, ↓reduceDIte]

end

end CatCrypt.Crypto.Jasmin
