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

/-- Rust-side variable name: `Located` just uses its `locVar` string. -/
def rustLocName (loc : Located) : String := loc.locVar

/-- Rust syntax for a direct `Located` reference, used as function argument. -/
def rustLocRef (loc : Located) : String := "&" ++ rustLocName loc

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
    `resultNames` tracks which outer-function parameters are already `&mut`
    and therefore don't need a fresh `&mut` prefix when passed as dest. -/
partial def ppRustCmd (resultNames : List String) (ind : Nat) : RustCmd → String
  | .RSkip => ""
  | .RSeq c1 c2 =>
      let s1 := ppRustCmd resultNames ind c1
      let s2 := ppRustCmd resultNames ind c2
      if s1.isEmpty then s2
      else if s2.isEmpty then s1
      else s1 ++ "\n" ++ s2
  | .RLetZero x t body =>
      let decl := rustIndent ind ("let mut " ++ x ++ " : " ++ rustTowerType t ++
                                   " = " ++ rustTowerType t ++ "::zero();")
      decl ++ "\n" ++ ppRustCmd resultNames ind body
  | .RLetU64Zero x body =>
      let decl := rustIndent ind ("let mut " ++ x ++ " : u64 = 0;")
      decl ++ "\n" ++ ppRustCmd resultNames ind body
  | .RScalarSet x v =>
      rustIndent ind (x ++ " = " ++ toString v ++ "u64;")
  | .RIfNz e ct cf =>
      let hdr := rustIndent ind ("if " ++ e ++ " != 0 {")
      let body1 := ppRustCmd resultNames (ind + 4) ct
      if cf matches .RSkip then
        hdr ++ "\n" ++ body1 ++ "\n" ++ rustIndent ind "}"
      else
        hdr ++ "\n" ++ body1 ++ "\n" ++ rustIndent ind "} else {" ++ "\n" ++
        ppRustCmd resultNames (ind + 4) cf ++ "\n" ++ rustIndent ind "}"
  | .RWhileNz e body =>
      rustIndent ind ("while " ++ e ++ " != 0 {") ++
      "\n" ++ ppRustCmd resultNames (ind + 4) body ++ "\n" ++ rustIndent ind "}"
  | .RCall f dest args =>
      let argStr := String.intercalate ", " (args.map rustLocRef)
      rustIndent ind (f ++ "(" ++ rustLocRefMut resultNames dest ++
                        (if args.isEmpty then "" else ", " ++ argStr) ++ ");")
  | .RCloneCall cv ct oldDest innerF dest args =>
      let cloneLine := rustIndent ind
        ("let mut " ++ cv ++ " : " ++ rustTowerType ct ++ " = " ++
         rustLocName oldDest ++ ".clone();")
      let argStr := String.intercalate ", " (args.map rustLocRef)
      let callLine := rustIndent ind
        (innerF ++ "(" ++ rustLocRefMut resultNames dest ++
          (if args.isEmpty then "" else ", " ++ argStr) ++ ");")
      cloneLine ++ "\n" ++ callLine
  | .RLimbStore loc idx v =>
      rustIndent ind (rustLocName loc ++ ".limbs[" ++ toString idx ++ "] = " ++
                       toString v.toNat ++ "u64;")

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
  let resultNames := results.map (·.locVar)
  "pub fn " ++ name ++ "(" ++ allParams ++ ") {\n" ++
  ppRustCmd resultNames 4 c ++ "\n}"

/-- Write the Rust source to a file. -/
def writeRustFunction (filename name : String)
    (params results : List Located) (c : RustCmd) : IO Unit := do
  IO.FS.writeFile filename (ppRustFunction name params results c)

end CatCrypt.Crypto.Jasmin.RustCmd
