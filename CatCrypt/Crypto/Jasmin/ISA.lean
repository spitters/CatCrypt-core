/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.JasminTranslate

/-!
# ISA Abstraction for Jasmin Compiler Targets

Parametrize the Jasmin backend over instruction set architectures.
The front-end pipeline (constant folding, nop elimination) is ISA-independent.
The backend compiler correctness axiom is per-ISA.

## Main definitions

* `JasminISA` — Typeclass for ISA targets with assembly type and compiler
* `JasminISA.compilerCorrect` — Per-ISA compiler correctness axiom
* `X86ISA` — x86-64 instance (axiomized, no Lean ISA formalization exists)
* `AArch64ISA` — AArch64 instance (axiomized, connectable to LNSym)
* `RiscVISA` — RISC-V instance (axiomized, connectable to Sail)

## Architecture

```
                    front-end (ISA-independent, proved)
Jasmin source  ──→  constFold → nopElim → [deadCodeElim]
                                              │
                    backend (per-ISA)          ▼
                ┌─  x86-64:  JasminCompile → AsmProg   (axiomized)
                ├─  AArch64: JasminCompile → AsmProg   (connectable to LNSym)
                └─  RISC-V:  JasminCompile → AsmProg   (connectable to Sail)
```

## Connections to External Formalizations

| ISA | Lean 4 project | Status |
|-----|---------------|--------|
| AArch64 | `leanprover/LNSym` | Production-grade Armv8 semantics, hardware tested |
| RISC-V | Sail RISC-V model (Lean backend) | Official Sail → Lean 4 output target |
| x86 | — | No Lean 4 formalization exists |

The `AArch64ISA` and `RiscVISA` instances are axiomized here but can be
connected to concrete ISA semantics by instantiating `asmSemantics` with
LNSym or Sail definitions, then proving `compilerCorrect`.
-/

namespace CatCrypt.Crypto.Jasmin

set_option autoImplicit false

/-! ## ISA Typeclass

### Axiom Structure

Each ISA instance requires 4 axioms (12 total for 3 ISAs):
- **3 definitional axioms** per ISA: `AsmProg` (type), `compile` (function),
  `asmSemantics` (function). These are definitional — they would be concrete
  definitions given a formalization of the ISA in Lean 4. They are axioms only
  because the ISA implementation lives outside Lean (in hardware/OCaml/etc.).
- **1 substantive axiom** per ISA: `compilerCorrect`. This is the "last yard" —
  it asserts that the Jasmin compiler output has the same semantics as the
  source-level translation. This is the only axiom that requires actual proof
  effort to discharge (via LNSym for AArch64, Sail for RISC-V).

The `JasminISA` typeclass is the abstraction boundary. Client code (e.g.,
`AESEndToEnd.lean`) is parametric over `[JasminISA]` and works with any ISA. -/

/-- An instruction set architecture for the Jasmin compiler backend.
    Each ISA provides a type for compiled assembly programs, a compiler
    function, and a correctness axiom relating assembly semantics to
    the Jasmin source-level translation. -/
class JasminISA where
  /-- Type of compiled assembly programs for this ISA. -/
  AsmProg : Type
  /-- Jasmin compiler targeting this ISA. -/
  compile : JasminProg → Option AsmProg
  /-- Abstract semantics of an assembly program (returns a computation
      given an entry point and arguments). -/
  asmSemantics : AsmProg → FunName → List TypedValue → Option (CatCrypt.Deep.RawCode (List TypedValue))
  /-- Compiler correctness: if compilation succeeds, the assembly semantics
      agree with the Jasmin source-level translation for all entry points
      and arguments.

      This is the "last yard" axiom — it cannot be proved within Lean alone
      because it relates to an external compiler and ISA semantics. For x86
      it remains axiomized; for AArch64 and RISC-V, it can be connected to
      LNSym and Sail respectively. -/
  compilerCorrect : ∀ (p : JasminProg) (xp : AsmProg) (entry : FunName)
    (args : List TypedValue) (fuel : Nat),
    compile p = some xp →
    ∀ code, translateProg p entry args fuel = some code →
    asmSemantics xp entry args = some code

/-! ## x86-64 Instance -/

/-- x86-64 ISA instance. Fully axiomized — no Lean 4 formalization of
    x86 semantics exists. This matches the original Last Yard paper. -/
axiom X86AsmProg : Type
axiom x86Compile : JasminProg → Option X86AsmProg
axiom x86Semantics : X86AsmProg → FunName → List TypedValue →
  Option (CatCrypt.Deep.RawCode (List TypedValue))
axiom x86CompilerCorrect : ∀ (p : JasminProg) (xp : X86AsmProg) (entry : FunName)
  (args : List TypedValue) (fuel : Nat),
  x86Compile p = some xp →
  ∀ code, translateProg p entry args fuel = some code →
  x86Semantics xp entry args = some code

noncomputable instance X86ISA : JasminISA where
  AsmProg := X86AsmProg
  compile := x86Compile
  asmSemantics := x86Semantics
  compilerCorrect := x86CompilerCorrect

/-! ## AArch64 Instance

Connectable to [LNSym](https://github.com/leanprover/LNSym), which provides
production-grade Armv8 instruction semantics in Lean 4 with hardware
conformance testing. To connect:

1. Add `LNSym` as a lakefile dependency
2. Define `AArch64AsmProg` using LNSym's `ArmState` / `Program` types
3. Define `aarch64Semantics` via LNSym's step function
4. Prove `compilerCorrect` by relating Jasmin's translation to LNSym steps -/

axiom AArch64AsmProg : Type
axiom aarch64Compile : JasminProg → Option AArch64AsmProg
axiom aarch64Semantics : AArch64AsmProg → FunName → List TypedValue →
  Option (CatCrypt.Deep.RawCode (List TypedValue))
axiom aarch64CompilerCorrect : ∀ (p : JasminProg) (xp : AArch64AsmProg) (entry : FunName)
  (args : List TypedValue) (fuel : Nat),
  aarch64Compile p = some xp →
  ∀ code, translateProg p entry args fuel = some code →
  aarch64Semantics xp entry args = some code

noncomputable instance AArch64ISA : JasminISA where
  AsmProg := AArch64AsmProg
  compile := aarch64Compile
  asmSemantics := aarch64Semantics
  compilerCorrect := aarch64CompilerCorrect

/-! ## RISC-V Instance

Connectable to the official [Sail RISC-V model](https://github.com/riscv/sail-riscv)
via the Sail → Lean 4 backend. The Sail model covers RV32/RV64 with standard
extensions and is the reference model used by the RISC-V Foundation.

Also relevant: [risc0/risc0-lean4](https://github.com/risc0/risc0-lean4) for
zkVM-specialized RISC-V semantics. -/

axiom RiscVAsmProg : Type
axiom riscvCompile : JasminProg → Option RiscVAsmProg
axiom riscvSemantics : RiscVAsmProg → FunName → List TypedValue →
  Option (CatCrypt.Deep.RawCode (List TypedValue))
axiom riscvCompilerCorrect : ∀ (p : JasminProg) (xp : RiscVAsmProg) (entry : FunName)
  (args : List TypedValue) (fuel : Nat),
  riscvCompile p = some xp →
  ∀ code, translateProg p entry args fuel = some code →
  riscvSemantics xp entry args = some code

noncomputable instance RiscVISA : JasminISA where
  AsmProg := RiscVAsmProg
  compile := riscvCompile
  asmSemantics := riscvSemantics
  compilerCorrect := riscvCompilerCorrect

/-! ## ISA-Generic Security Theorem

The front-end pipeline correctness is ISA-independent (proved in
`PassFramework.lean` and `Pipeline.lean`). The backend is per-ISA via
the `JasminISA` typeclass. Combined, this gives:

```
∀ (isa : JasminISA),
  front-end correctness (proved) + backend correctness (per-ISA axiom)
  ⟹ end-to-end security
```

See `AES/AESEndToEnd.lean` for the concrete x86 instance of this pattern. -/

end CatCrypt.Crypto.Jasmin
