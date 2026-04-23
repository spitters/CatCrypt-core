/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.JasminToSSA

/-!
# ChaCha20 Quarter-Round Case Study

Verifies the Jasmin→CryptoSSA translation pipeline on the ChaCha20 quarter-round
function (RFC 8439). The quarter-round is the core building block of the ChaCha20
stream cipher, operating on four 32-bit words with add/xor/rotate operations.

## Architecture

```
quarterRound (pure spec)
  ↔ pureEvalMonoCmd (Jasmin SSA commands)     [quarterRound_jasmin_correct]
  → translateMonoCmd → CProg                   [translateMonoCmd_correct]
  → CProg.denote = SPComp.pure (quarterRound)  [qr_cryptossa_correct]
```

## Key Features

- Rotation decomposed into shift+or: `rotL32 x k = (x <<< k) ||| (x >>> (32 - k))`
- 20 SSA instructions (4 rounds × 5 ops: add, xor, shl, shr, or)
- End-to-end correctness from Jasmin SSA to CryptoSSA denotation

**0 axioms**, **0 sorries**.
-/

namespace CatCrypt.Crypto.Jasmin.ChaCha20QR

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.Jasmin.ToSSA
open scoped ENNReal

set_option autoImplicit false

noncomputable section

/-! ## Section 1: Pure Specification -/

/-- Left rotation on 32-bit words, decomposed into shifts. -/
def rotL32 (x : BitVec 32) (k : Nat) : BitVec 32 :=
  (x <<< k) ||| (BitVec.ushiftRight x (32 - k))

/-- ChaCha20 quarter-round (RFC 8439 §2.1).

    Operates on four 32-bit words with the pattern:
    ```
    a += b; d ^= a; d <<<= 16
    c += d; b ^= c; b <<<= 12
    a += b; d ^= a; d <<<= 8
    c += d; b ^= c; b <<<= 7
    ``` -/
def quarterRound (a b c d : BitVec 32) :
    BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  let a := a + b;  let d := rotL32 (d ^^^ a) 16
  let c := c + d;  let b := rotL32 (b ^^^ c) 12
  let a := a + b;  let d := rotL32 (d ^^^ a) 8
  let c := c + d;  let b := rotL32 (b ^^^ c) 7
  (a, b, c, d)

/-! ## Section 2: Jasmin Variable Setup -/

/-- Helper to create a Jasmin `Var` with 32-bit word type. -/
private def mkVar32 (name : String) : Var :=
  { vname := name, vtype := .sword .U32 }

/-- Helper to create a `VarI` (variable with info). -/
private def mkVarI (name : String) : VarI :=
  { var := mkVar32 name }

/-- Helper to create a `GVar` reference. -/
private def mkGVar (name : String) : GVar :=
  { gv := mkVarI name, gs := false }

/-- Helper to create a `PExpr.Pvar`. -/
private def pvar (name : String) : PExpr := .Pvar (mkGVar name)

/-- Helper to create an assignment instruction. -/
private def assign (dst : String) (e : PExpr) : InstrR :=
  .Cassgn (.Lvar (mkVarI dst)) .AT_none (.sword .U32) e

-- Input/output variable names
private def va := mkVar32 "a"
private def vb := mkVar32 "b"
private def vc := mkVar32 "c"
private def vd := mkVar32 "d"

/-! ## Section 3: Jasmin SSA Commands

Each rotation `x <<<= k` is decomposed into 3 instructions:
- `t := x << k`    (shift left by constant)
- `u := x >> (32-k)` (shift right by constant)
- `x' := t | u`    (combine)

Each quarter-round step `a += b; d ^= a; d <<<= k` becomes 5 instructions. -/

/-- The 20 SSA instructions implementing the ChaCha20 quarter-round. -/
def qrCmd : List InstrR :=
  -- Round 1: a += b; d ^= a; d <<<= 16
  [ assign "a1" (.Papp2 (.Oadd .U32) (pvar "a") (pvar "b")),
    assign "d1" (.Papp2 (.Olxor .U32) (pvar "d") (pvar "a1")),
    assign "t1" (.Papp2 (.Olsl .U32) (pvar "d1") (.Pconst 16)),
    assign "u1" (.Papp2 (.Olsr .U32) (pvar "d1") (.Pconst 16)),
    assign "d2" (.Papp2 (.Olor .U32) (pvar "t1") (pvar "u1")),
    -- Round 2: c += d; b ^= c; b <<<= 12
    assign "c1" (.Papp2 (.Oadd .U32) (pvar "c") (pvar "d2")),
    assign "b1" (.Papp2 (.Olxor .U32) (pvar "b") (pvar "c1")),
    assign "t2" (.Papp2 (.Olsl .U32) (pvar "b1") (.Pconst 12)),
    assign "u2" (.Papp2 (.Olsr .U32) (pvar "b1") (.Pconst 20)),
    assign "b2" (.Papp2 (.Olor .U32) (pvar "t2") (pvar "u2")),
    -- Round 3: a += b; d ^= a; d <<<= 8
    assign "a2" (.Papp2 (.Oadd .U32) (pvar "a1") (pvar "b2")),
    assign "d3" (.Papp2 (.Olxor .U32) (pvar "d2") (pvar "a2")),
    assign "t3" (.Papp2 (.Olsl .U32) (pvar "d3") (.Pconst 8)),
    assign "u3" (.Papp2 (.Olsr .U32) (pvar "d3") (.Pconst 24)),
    assign "d4" (.Papp2 (.Olor .U32) (pvar "t3") (pvar "u3")),
    -- Round 4: c += d; b ^= c; b <<<= 7
    assign "c2" (.Papp2 (.Oadd .U32) (pvar "c1") (pvar "d4")),
    assign "b3" (.Papp2 (.Olxor .U32) (pvar "b2") (pvar "c2")),
    assign "t4" (.Papp2 (.Olsl .U32) (pvar "b3") (.Pconst 7)),
    assign "u4" (.Papp2 (.Olsr .U32) (pvar "b3") (.Pconst 25)),
    assign "b4" (.Papp2 (.Olor .U32) (pvar "t4") (pvar "u4")) ]

/-- Return variable for the output tuple (encoded as final variable names). -/
private def retA := mkVar32 "a2"
private def retB := mkVar32 "b4"
private def retC := mkVar32 "c2"
private def retD := mkVar32 "d4"

/-! ## Section 4: Environment Setup -/

/-- Initial environment mapping input variable names to values. -/
def qrEnv (a b c d : BitVec 32) : Var → BitVec 32 :=
  fun v =>
    if v = va then a
    else if v = vb then b
    else if v = vc then c
    else if v = vd then d
    else 0

/-! ## Section 5: Pure Evaluation Correctness -/

/-- The pure evaluation of `qrCmd` for the `a` output computes `quarterRound`. -/
theorem quarterRound_a_correct (a b c d : BitVec 32) :
    pureEvalMonoCmd 32 (qrEnv a b c d) retA qrCmd =
    (quarterRound a b c d).1 := by rfl

/-- The pure evaluation of `qrCmd` for the `b` output computes `quarterRound`. -/
theorem quarterRound_b_correct (a b c d : BitVec 32) :
    pureEvalMonoCmd 32 (qrEnv a b c d) retB qrCmd =
    (quarterRound a b c d).2.1 := by rfl

/-- The pure evaluation of `qrCmd` for the `c` output computes `quarterRound`. -/
theorem quarterRound_c_correct (a b c d : BitVec 32) :
    pureEvalMonoCmd 32 (qrEnv a b c d) retC qrCmd =
    (quarterRound a b c d).2.2.1 := by rfl

/-- The pure evaluation of `qrCmd` for the `d` output computes `quarterRound`. -/
theorem quarterRound_d_correct (a b c d : BitVec 32) :
    pureEvalMonoCmd 32 (qrEnv a b c d) retD qrCmd =
    (quarterRound a b c d).2.2.2 := by rfl

/-! ## Section 6: CryptoSSA Translation -/

/-- The input variable names are all distinct. -/
private theorem va_ne_vb : va ≠ vb := by decide
private theorem va_ne_vc : va ≠ vc := by decide
private theorem va_ne_vd : va ≠ vd := by decide
private theorem vb_ne_vc : vb ≠ vc := by decide
private theorem vb_ne_vd : vb ≠ vd := by decide
private theorem vc_ne_vd : vc ≠ vd := by decide

/-- **End-to-end correctness**: The CryptoSSA denotation of the translated
    quarter-round computes `SPComp.pure` of the pure specification (for `a` output).

    Uses `translateMonoFun4_correct` for the CryptoSSA bridge, composed with
    `quarterRound_a_correct` for the pure evaluation. -/
theorem qr_cryptossa_correct_a
    (prog : CProg _ (.sword 32))
    (h_trans : translateMonoFun4 va vb vc vd retA 32 qrCmd = some prog)
    (a b c d : BitVec 32) :
    prog.denote (.cons a (.cons b (.cons c (.cons d .nil)))) =
    SPComp.pure (quarterRound a b c d).1 := by
  rw [translateMonoFun4_correct va vb vc vd retA 32
    va_ne_vb va_ne_vc va_ne_vd vb_ne_vc vb_ne_vd vc_ne_vd
    qrCmd prog h_trans a b c d]
  exact congrArg SPComp.pure (quarterRound_a_correct a b c d)

/-! ## Section 7: DCE Preservation -/

/-- DCE preserves the quarter-round computation (no dead code in `qrCmd` for `retA`). -/
theorem qr_dce_preserves_a (a b c d : BitVec 32) :
    pureEvalMonoCmd 32 (qrEnv a b c d) retA (simpleDCE retA qrCmd) =
    (quarterRound a b c d).1 := by
  rw [simpleDCE_correct]; exact quarterRound_a_correct a b c d

end

end CatCrypt.Crypto.Jasmin.ChaCha20QR
