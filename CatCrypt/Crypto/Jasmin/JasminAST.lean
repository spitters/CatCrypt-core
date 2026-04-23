/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

/-!
# Jasmin Program AST

This file defines the Jasmin program AST types in Lean 4, following the
Rocq CatCrypt jasmin branch (`theories/Jasmin/jasmin_translate.v`).

These types represent the syntax of Jasmin programs as they appear after
parsing and before compilation. The translation to CatCrypt `RawCode` is
defined in `JasminTranslate.lean`.

## References

* "The Last Yard" (CPP 2024, Haselwarter et al.), eprint 2023/185
* jasmin-lang/jasmin compiler
* CatCrypt jasmin branch: `theories/Jasmin/jasmin_translate.v`
-/

namespace CatCrypt.Crypto.Jasmin

/-! ## Word Sizes -/

/-- Jasmin machine word sizes (in bits). -/
inductive WSize where
  | U8 | U16 | U32 | U64 | U128 | U256
  deriving DecidableEq, Repr, Inhabited

/-- Number of bits for a word size. -/
def WSize.bits : WSize → Nat
  | .U8   => 8
  | .U16  => 16
  | .U32  => 32
  | .U64  => 64
  | .U128 => 128
  | .U256 => 256

/-- Number of bytes for a word size. -/
def WSize.bytes : WSize → Nat
  | .U8   => 1
  | .U16  => 2
  | .U32  => 4
  | .U64  => 8
  | .U128 => 16
  | .U256 => 32

/-- The pointer size (64-bit). -/
def WSize.Uptr : WSize := .U64

/-! ## Jasmin Type System -/

/-- Jasmin semantic types.
    - `sbool`: Boolean values
    - `sint`: Arbitrary-precision integers
    - `sarr n`: Array of `n` bytes
    - `sword ws`: Machine word of size `ws` -/
inductive SType where
  | sbool : SType
  | sint : SType
  | sarr (n : Nat) : SType
  | sword (ws : WSize) : SType
  deriving DecidableEq, Repr, Inhabited

/-! ## Variables -/

/-- Variable information (source location, etc.). Opaque for our purposes. -/
structure VarInfo where
  dummy : Unit := ()
  deriving Inhabited, Repr

/-- Variable declaration: name + type. -/
structure Var where
  vname : String
  vtype : SType
  deriving DecidableEq, Repr, Inhabited

/-- Variable with source info. -/
structure VarI where
  var : Var
  info : VarInfo := {}
  deriving Inhabited, Repr

/-- Global variable reference (variable + is_global flag). -/
structure GVar where
  gv : VarI
  gs : Bool  -- true = global, false = local
  deriving Inhabited, Repr

/-- Function name. -/
structure FunName where
  name : String
  deriving DecidableEq, Repr, Inhabited

instance : BEq FunName := ⟨fun a b => a.name == b.name⟩

/-! ## Array Access Mode -/

/-- Array access mode: AAscale (scaled by word size) or AAdirect (byte-level). -/
inductive ArrAccess where
  | AAscale : ArrAccess
  | AAdirect : ArrAccess
  deriving DecidableEq, Repr, Inhabited

/-! ## Unary Operations -/

/-- Sign extension mode. -/
inductive SignExtend where
  | Sextend : SignExtend    -- sign-extend
  | Uextend : SignExtend    -- zero-extend
  deriving DecidableEq, Repr, Inhabited

/-- Unary operations. -/
inductive SOp1 where
  | Oword_of_int (ws : WSize) : SOp1           -- int → word
  | Oint_of_word (ws : WSize) : SOp1           -- word → int (unsigned)
  | Osignext (wso wsi : WSize) : SOp1          -- sign-extend
  | Ozeroext (wso wsi : WSize) : SOp1          -- zero-extend
  | Onot : SOp1                                -- boolean negation
  | Olnot (ws : WSize) : SOp1                  -- bitwise NOT
  | Oneg (ws : WSize) : SOp1                   -- arithmetic negation
  deriving DecidableEq, Repr, Inhabited

/-! ## Binary Operations -/

/-- Binary operations. -/
inductive SOp2 where
  | Obeq : SOp2                                 -- boolean equality
  | Oand : SOp2                                 -- boolean AND
  | Oor : SOp2                                  -- boolean OR
  | Oadd (ws : WSize) : SOp2                    -- word addition
  | Omul (ws : WSize) : SOp2                    -- word multiplication
  | Osub (ws : WSize) : SOp2                    -- word subtraction
  | Odiv (se : SignExtend) (ws : WSize) : SOp2  -- word division
  | Omod (se : SignExtend) (ws : WSize) : SOp2  -- word modulo
  | Oland (ws : WSize) : SOp2                   -- bitwise AND
  | Olor (ws : WSize) : SOp2                    -- bitwise OR
  | Olxor (ws : WSize) : SOp2                   -- bitwise XOR
  | Olsr (ws : WSize) : SOp2                    -- logical shift right
  | Olsl (ws : WSize) : SOp2                    -- logical shift left
  | Oasr (ws : WSize) : SOp2                    -- arithmetic shift right
  | Oeq (ws : WSize) : SOp2                     -- word equality
  | Oneq (ws : WSize) : SOp2                    -- word inequality
  | Olt (se : SignExtend) (ws : WSize) : SOp2   -- word less-than
  | Ole (se : SignExtend) (ws : WSize) : SOp2   -- word less-or-equal
  | Ogt (se : SignExtend) (ws : WSize) : SOp2   -- word greater-than
  | Oge (se : SignExtend) (ws : WSize) : SOp2   -- word greater-or-equal
  | Ovadd (ve ws : WSize) : SOp2                -- SIMD vector addition
  | Ovsub (ve ws : WSize) : SOp2                -- SIMD vector subtraction
  | Ovmul (ve ws : WSize) : SOp2                -- SIMD vector multiplication
  | Ovlsr (ve ws : WSize) : SOp2                -- SIMD vector logical shift right
  | Ovlsl (ve ws : WSize) : SOp2                -- SIMD vector logical shift left
  | Ovasr (ve ws : WSize) : SOp2                -- SIMD vector arithmetic shift right
  deriving DecidableEq, Repr, Inhabited

/-! ## N-ary Operations -/

/-- N-ary operations (e.g., SIMD pack). -/
inductive OpN where
  | Opack (ws pe : WSize) : OpN
  deriving DecidableEq, Repr, Inhabited

/-! ## Assembly Operations -/

/-- Assignment tags (how values are assigned). -/
inductive AssgnTag where
  | AT_none : AssgnTag     -- normal assignment
  | AT_keep : AssgnTag     -- keep destination flags
  | AT_rename : AssgnTag   -- register rename
  | AT_inline : AssgnTag   -- inline expansion
  | AT_phinode : AssgnTag  -- SSA phi node
  deriving DecidableEq, Repr, Inhabited

/-- Inlining hint for function calls. -/
inductive InlineInfo where
  | DoInline : InlineInfo
  | DoNotInline : InlineInfo
  deriving DecidableEq, Repr, Inhabited

/-- Assembly operation identifiers.
    We represent x86 operations as an opaque identifier since the semantics
    are defined separately in `JasminOps.lean`. -/
structure AsmOp where
  name : String
  deriving DecidableEq, Repr, Inhabited

instance : BEq AsmOp := ⟨fun a b => a.name == b.name⟩

/-- Combined assembly operation (sopn in Rocq). -/
inductive SOpn where
  | Oasm (op : AsmOp) : SOpn
  deriving DecidableEq, Repr, Inhabited

/-! ## Loop Direction -/

/-- For-loop direction. -/
inductive LoopDir where
  | UpTo : LoopDir    -- ascending
  | DownTo : LoopDir  -- descending
  deriving DecidableEq, Repr, Inhabited

/-- Loop range: direction × lower bound × upper bound. -/
structure Range where
  dir : LoopDir
  lo : Nat  -- simplified: use Nat indices for our purposes
  hi : Nat
  deriving Repr, Inhabited

/-! ## Expressions -/

/-- Jasmin program expressions. -/
inductive PExpr where
  | Pconst (z : Int) : PExpr
  | Pbool (b : Bool) : PExpr
  | Parr_init (n : Nat) : PExpr
  | Pvar (v : GVar) : PExpr
  | Pget (aa : ArrAccess) (ws : WSize) (x : GVar) (idx : PExpr) : PExpr
  | Psub (aa : ArrAccess) (ws : WSize) (len : Nat) (x : GVar) (idx : PExpr) : PExpr
  | Pload (ws : WSize) (x : VarI) (off : PExpr) : PExpr
  | Papp1 (op : SOp1) (e : PExpr) : PExpr
  | Papp2 (op : SOp2) (e1 e2 : PExpr) : PExpr
  | PappN (op : OpN) (es : List PExpr) : PExpr
  | Pif (ty : SType) (cond : PExpr) (etrue efalse : PExpr) : PExpr
  deriving Repr, Inhabited

/-! ## L-values (Assignment Targets) -/

/-- Left-values: targets of assignments. -/
inductive LVal where
  | Lnone (info : VarInfo) (ty : SType) : LVal
  | Lvar (x : VarI) : LVal
  | Lmem (ws : WSize) (x : VarI) (off : PExpr) : LVal
  | Laset (aa : ArrAccess) (ws : WSize) (x : VarI) (idx : PExpr) : LVal
  | Lasub (aa : ArrAccess) (ws : WSize) (len : Nat) (x : VarI) (idx : PExpr) : LVal
  deriving Repr, Inhabited

/-! ## Instructions -/

/-- Jasmin instruction body. Mutually recursive with `Cmd` (instruction sequence). -/
inductive InstrR where
  | Cassgn (lv : LVal) (tag : AssgnTag) (ty : SType) (e : PExpr) : InstrR
  | Copn (lvs : List LVal) (tag : AssgnTag) (op : SOpn) (es : List PExpr) : InstrR
  | Cif (cond : PExpr) (cthen celse : List InstrR) : InstrR
  | Cfor (v : VarI) (range : Range) (body : List InstrR) : InstrR
  | Cwhile (cbefore : List InstrR) (cond : PExpr) (cafter : List InstrR) : InstrR
  | Ccall (ii : InlineInfo) (lvs : List LVal) (fn : FunName) (args : List PExpr) : InstrR
  deriving Repr, Inhabited

/-- A command is a sequence of instructions. -/
abbrev Cmd := List InstrR

/-! ## Function and Program Declarations -/

/-- Function parameter/return declaration. -/
structure FunParam where
  var : VarI
  deriving Inhabited, Repr

/-- Function declaration. -/
structure FunDecl where
  name : FunName
  params : List FunParam
  body : Cmd
  results : List VarI
  deriving Inhabited

/-- A Jasmin program: a list of function declarations. -/
structure JasminProg where
  funcs : List FunDecl
  deriving Inhabited

namespace JasminProg

/-- Look up a function definition by name. -/
def getFun (p : JasminProg) (fn : FunName) : Option FunDecl :=
  p.funcs.find? (fun fd => fd.name == fn)

end JasminProg

end CatCrypt.Crypto.Jasmin
