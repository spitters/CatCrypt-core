/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.RustCmd

/-!
# Rust Source Emission from `RustCmd`

Counterpart to `RustCmdToJasmin.ppJasminProg`: produces a Rust source
string from a `RustCmd`. Together with `writeJasminProg` this closes the
bidirectional round-trip: one `RustCmd` → one Jasmin file AND one Rust file,
both proved-correct by `rustExecSimulates` family of theorems.

## Style

Curve-arithmetic leaves emit as straight-line Rust code taking tower-typed
parameters by reference (immutable for inputs, `&mut` for outputs). Calls
to leaf functions like `fp_mul` become regular Rust calls. `RCloneCall`
becomes an explicit `.clone()` on the source value.

This is the SHIP form — what actually gets fed into the `cryptoptbls12-rs`
crate for testing. Verified-correct by simulation against the same AST.
-/

namespace CatCrypt.Crypto.Jasmin.RustCmd

/-- Rust syntax for a `TowerType`. Maps to a type alias in the target crate. -/
def rustTowerType : TowerType → String
  | .TFp => "Fp"
  | .TFp2 => "Fp2"
  | .TFp6 => "Fp6"
  | .TFp12 => "Fp12"
  | .TU64 => "u64"
  | .TFp25519 => "Fp25519"
  | .TFp25519_64 => "Fp25519_64"
  -- Phase D/E/I/K (2026-05-03):
  | .TFpL25519 => "FpL25519"
  | .TFpP256 => "FpP256"
  | .TFp25519_4Bounded _ => "Fp25519_4Bounded"
  | .TFpGen name _ => "Fp_" ++ name
  | .TFp2Gen name _ => "Fp2_" ++ name
  | .TTuple a b => "(" ++ rustTowerType a ++ ", " ++ rustTowerType b ++ ")"
  | .TBytes n => "[u8; " ++ toString n ++ "]"
  | .TArr n t => "[" ++ rustTowerType t ++ "; " ++ toString n ++ "]"

/-- Rust-side variable name: `Located` just uses its `locVar` string. -/
def rustLocName (loc : Located) : String := loc.locVar

/-- Rust syntax for a direct `Located` reference, used as function argument.
    Function parameters are already typed `: &T` in the emitted signature,
    so we pass them by bare name; locals (declared `let mut x : T = T::zero()`)
    need a fresh `&` prefix.  `paramNames` lists the names of the enclosing
    function's input parameters. -/
def rustLocRef (paramNames : List String) (loc : Located) : String :=
  if paramNames.contains loc.locVar then rustLocName loc
  else "&" ++ rustLocName loc

/-- Rust syntax for a mutable reference, parameterised by whether the
    underlying variable is already a `&mut` function parameter. If it is,
    Rust's auto-reborrow lets us pass the name directly; otherwise we need
    `&mut name`. -/
def rustLocRefMut (resultNames : List String) (loc : Located) : String :=
  if resultNames.contains loc.locVar then rustLocName loc
  else "&mut " ++ rustLocName loc

private def rustIndent (n : Nat) (s : String) : String :=
  String.replicate n ' ' ++ s

/-- Emit a `RustCmd` as Rust source with given indent level.
    `paramNames` tracks the enclosing function's input parameter names
    (already typed `: &T` in the signature, so pass-as-arg is by bare
    name).  `resultNames` tracks output parameters (already `: &mut T`,
    so pass-as-dest is by bare name).  Locals declared via `RLetZero` or
    `RLetU64Zero` need fresh `&` / `&mut` prefixes. -/
partial def ppRustCmd (paramNames : List String) (resultNames : List String)
    (ind : Nat) : RustCmd → String
  | .RSkip => ""
  | .RSeq c1 c2 =>
      let s1 := ppRustCmd paramNames resultNames ind c1
      let s2 := ppRustCmd paramNames resultNames ind c2
      if s1.isEmpty then s2
      else if s2.isEmpty then s1
      else s1 ++ "\n" ++ s2
  | .RLetZero x t body =>
      -- Initializer: struct types use `T::zero()` (caller provides
      -- `impl FpZero for T`); array types use the literal form
      -- because `<[T; n]>::zero()` requires a parsed array type.
      -- For `TArr m (TBytes n)` we get `[[0u8; n]; m]`; for other
      -- nested arrays we fall back to `[T::zero(); m]` (the inner
      -- type must impl Copy + FpZero for this to compile).
      let initExpr := match t with
        | .TBytes n              => s!"[0u8; {n}]"
        | .TArr m (.TBytes n)    => s!"[[0u8; {n}]; {m}]"
        | .TArr m inner          => s!"[{rustTowerType inner}::zero(); {m}]"
        | _                      => rustTowerType t ++ "::zero()"
      let decl := rustIndent ind ("let mut " ++ x ++ " : " ++ rustTowerType t ++
                                   " = " ++ initExpr ++ ";")
      decl ++ "\n" ++ ppRustCmd paramNames resultNames ind body
  | .RLetU64Zero x body =>
      let decl := rustIndent ind ("let mut " ++ x ++ " : u64 = 0;")
      decl ++ "\n" ++ ppRustCmd paramNames resultNames ind body
  | .RScalarSet x v =>
      rustIndent ind (x ++ " = " ++ toString v ++ "u64;")
  | .RIfNz e ct cf =>
      let hdr := rustIndent ind ("if " ++ e ++ " != 0 {")
      let body1 := ppRustCmd paramNames resultNames (ind + 4) ct
      if cf matches .RSkip then
        hdr ++ "\n" ++ body1 ++ "\n" ++ rustIndent ind "}"
      else
        hdr ++ "\n" ++ body1 ++ "\n" ++ rustIndent ind "} else {" ++ "\n" ++
        ppRustCmd paramNames resultNames (ind + 4) cf ++ "\n" ++ rustIndent ind "}"
  | .RWhileNz e body =>
      rustIndent ind ("while " ++ e ++ " != 0 {") ++
      "\n" ++ ppRustCmd paramNames resultNames (ind + 4) body ++ "\n" ++ rustIndent ind "}"
  | .RFor x n body =>
      -- Bounded loop `for x in 0..n { body }`. `x` is a scalar (u64);
      -- `body` may read it. Translate to a Rust `for` over `0..n_u64`.
      rustIndent ind ("for " ++ x ++ " in 0u64.." ++ toString n ++ "u64 {") ++
      "\n" ++ ppRustCmd paramNames resultNames (ind + 4) body ++ "\n" ++ rustIndent ind "}"
  | .RCall f dest args =>
      let argStr := String.intercalate ", " (args.map (rustLocRef paramNames))
      rustIndent ind (f ++ "(" ++ rustLocRefMut resultNames dest ++
                        (if args.isEmpty then "" else ", " ++ argStr) ++ ");")
  | .RCallSwap f dest1 dest2 args =>
      let argStr := String.intercalate ", " (args.map (rustLocRef paramNames))
      rustIndent ind (f ++ "(" ++
                        rustLocRefMut resultNames dest1 ++ ", " ++
                        rustLocRefMut resultNames dest2 ++
                        (if args.isEmpty then "" else ", " ++ argStr) ++ ");")
  | .RCloneCall cv ct oldDest innerF dest args =>
      let cloneLine := rustIndent ind
        ("let mut " ++ cv ++ " : " ++ rustTowerType ct ++ " = " ++
         rustLocName oldDest ++ ".clone();")
      let argStr := String.intercalate ", " (args.map (rustLocRef paramNames))
      let callLine := rustIndent ind
        (innerF ++ "(" ++ rustLocRefMut resultNames dest ++
          (if args.isEmpty then "" else ", " ++ argStr) ++ ");")
      cloneLine ++ "\n" ++ callLine
  | .RLimbStore loc idx v =>
      rustIndent ind (rustLocName loc ++ ".limbs[" ++ toString idx ++ "] = " ++
                       toString v.toNat ++ "u64;")
  | .RAsmOp name dests args =>
      -- Phase F: emit a placeholder Rust comment naming the asm op.
      let dStr := String.intercalate ", " (dests.map (rustLocRefMut resultNames))
      let aStr := String.intercalate ", " (args.map (rustLocRef paramNames))
      rustIndent ind ("// asm " ++ name ++ "(" ++ dStr ++
        (if args.isEmpty then "" else " <- " ++ aStr) ++ ");")
  | .RCallN f dests args =>
      -- Phase G: multi-output call.  Pass all destinations as &mut, then args.
      let dStr := String.intercalate ", " (dests.map (rustLocRefMut resultNames))
      let aStr := String.intercalate ", " (args.map (rustLocRef paramNames))
      rustIndent ind (f ++ "(" ++ dStr ++
        (if args.isEmpty then "" else ", " ++ aStr) ++ ");")
  | .RSelect dst sel src0 src1 =>
      -- Phase H: CT-safe conditional select; render as a ternary.
      rustIndent ind (rustLocName dst ++ " = if " ++ sel ++ " == 0 { " ++
        rustLocName src0 ++ ".clone() } else { " ++ rustLocName src1 ++ ".clone() };")
  | .RAssert _ =>
      -- Phase L: zero-cost contract — emit nothing.
      ""
  | .RBlock body =>
      -- Phase M: scoped block.
      rustIndent ind "{" ++ "\n" ++
      ppRustCmd paramNames resultNames (ind + 4) body ++ "\n" ++
      rustIndent ind "}"
  | .RFnDef name params returns body cont =>
      -- Phase C: helper definition; emit a nested `fn` declaration
      -- followed by the continuation.
      let paramStr := String.intercalate ", "
        (params.map (fun p => p.locVar ++ " : &" ++ rustTowerType p.locSrc))
      let resultStr := String.intercalate ", "
        (returns.map (fun r => r.locVar ++ " : &mut " ++ rustTowerType r.locDst))
      let allParams :=
        if params.isEmpty then resultStr
        else if returns.isEmpty then paramStr
        else paramStr ++ ", " ++ resultStr
      let pNames := params.map (·.locVar)
      let rNames := returns.map (·.locVar)
      rustIndent ind ("fn " ++ name ++ "(" ++ allParams ++ ") {") ++ "\n" ++
      ppRustCmd pNames rNames (ind + 4) body ++ "\n" ++
      rustIndent ind "}" ++ "\n" ++
      ppRustCmd paramNames resultNames ind cont
  | .RFnCall f dests args =>
      -- Phase C: helper call; same shape as RCallN.
      let dStr := String.intercalate ", " (dests.map (rustLocRefMut resultNames))
      let aStr := String.intercalate ", " (args.map (rustLocRef paramNames))
      rustIndent ind (f ++ "(" ++ dStr ++
        (if args.isEmpty then "" else ", " ++ aStr) ++ ");")
  | .RTupleStore dst idx src =>
      -- Phase I: tuple component store; emit as `dst.idx = src.clone();`.
      rustIndent ind (rustLocName dst ++ "." ++ toString idx ++ " = " ++
        rustLocName src ++ ".clone();")
  | .RTupleLoad dst src idx =>
      -- Phase I: tuple component load; emit as `dst = src.idx.clone();`.
      rustIndent ind (rustLocName dst ++ " = " ++ rustLocName src ++ "." ++
        toString idx ++ ".clone();")
  | .RArrStore arr idxVar src =>
      -- Phase Ext: array element store.  When `src` is an owned
      -- `[u8; N]` (Copy), direct assignment copies by value.  When
      -- `src` is a function-parameter `&[u8; N]`, we need to deref.
      let srcExpr :=
        if paramNames.contains src.locVar then "*" ++ rustLocName src
        else rustLocName src
      rustIndent ind (rustLocName arr ++ "[" ++ idxVar ++ " as usize] = " ++
        srcExpr ++ ";")
  | .RArrLoad dst src idxVar =>
      -- Phase Ext: array element load.  When `dst` is an owned local,
      -- direct array-index assignment copies by value.  When `dst` is
      -- a function-output `&mut [u8; N]`, we need to deref.
      let dstExpr :=
        if resultNames.contains dst.locVar then "*" ++ rustLocName dst
        else rustLocName dst
      rustIndent ind (dstExpr ++ " = " ++ rustLocName src ++ "[" ++
        idxVar ++ " as usize];")
  | .RScalarSetExpr x e =>
      -- Phase Ext: assign SExpr value to scalar slot.
      rustIndent ind (x ++ " = " ++ e.ppRust ++ ";")
  | .RBytesSlice dst src start len =>
      -- Phase Ext2: compile-time byte-slice copy.  Emits
      -- `dst.copy_from_slice(&src[start..start+len])`.  When `src` is
      -- a function-parameter (already `&[u8; N]`), Rust accepts the
      -- direct slice without an additional `&` (auto-deref via the
      -- `Index<Range<usize>>` impl on `[u8]`); when it's an owned
      -- local, we need an explicit `&`.
      let srcExpr :=
        if paramNames.contains src.locVar
          then rustLocName src ++ "[" ++ toString start ++ ".." ++
                 toString (start + len) ++ "]"
          else "&" ++ rustLocName src ++ "[" ++ toString start ++ ".." ++
                 toString (start + len) ++ "]"
      let dstExpr :=
        if resultNames.contains dst.locVar then rustLocName dst
        else rustLocName dst
      rustIndent ind (dstExpr ++ ".copy_from_slice(&" ++ srcExpr ++ ");")

/-- Emit a full Rust function from a `RustCmd`, given name, inputs (as
    `(name, type)` pairs), outputs (same), and the body command. -/
def ppRustFunction (name : String)
    (params : List Located) (results : List Located)
    (c : RustCmd) : String :=
  let paramStr := String.intercalate ", "
    (params.map (fun p => p.locVar ++ " : &" ++ rustTowerType p.locSrc))
  let resultStr := String.intercalate ", "
    (results.map (fun r => r.locVar ++ " : &mut " ++ rustTowerType r.locDst))
  let allParams :=
    if params.isEmpty then resultStr
    else if results.isEmpty then paramStr
    else paramStr ++ ", " ++ resultStr
  let paramNames := params.map (·.locVar)
  let resultNames := results.map (·.locVar)
  "pub fn " ++ name ++ "(" ++ allParams ++ ") {\n" ++
  ppRustCmd paramNames resultNames 4 c ++ "\n}"

/-- Write the Rust source to a file. -/
def writeRustFunction (filename name : String)
    (params results : List Located) (c : RustCmd) : IO Unit := do
  IO.FS.writeFile filename (ppRustFunction name params results c)

end CatCrypt.Crypto.Jasmin.RustCmd
