/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.PassFramework

/-!
# Dead Code Elimination Pass

Remove assignments to variables that are never subsequently read.

## Main definitions

* `exprVars` — Collect variables read by an expression
* `instrReads` / `instrWrites` — Variables read/written by an instruction
* `liveAfterCmd` — Backward liveness analysis
* `deadCodeElim` — Remove dead assignments

## Design

This implements a simplified backward liveness analysis:
1. Start from the set of "live-out" variables (those needed after the command)
2. Walk backwards through instructions
3. An assignment `v := e` is dead if `v` is not live after the assignment

The correctness proof requires a "heap frame" property: writing to a location
that is never subsequently read does not affect the result. This property
requires location tracking through the SPComp monad, which we axiomatize.
-/

namespace CatCrypt.Crypto.Jasmin

set_option autoImplicit false

/-! ## Variable Collection -/

/-- Collect variables referenced by an expression. -/
def exprVars : PExpr → List Var
  | .Pvar gv => [gv.gv.var]
  | .Pget _ _ x idx => x.gv.var :: exprVars idx
  | .Psub _ _ _ x idx => x.gv.var :: exprVars idx
  | .Pload _ x off => x.var :: exprVars off
  | .Papp1 _ e => exprVars e
  | .Papp2 _ e₁ e₂ => exprVars e₁ ++ exprVars e₂
  | .PappN _ es => (es.map exprVars).flatten
  | .Pif _ c et ef => exprVars c ++ exprVars et ++ exprVars ef
  | _ => []  -- Pconst, Pbool, Parr_init

/-- Variables written by an l-value. -/
def lvalWrites : LVal → List Var
  | .Lvar x => [x.var]
  | .Laset _ _ x _ => [x.var]
  | .Lasub _ _ _ x _ => [x.var]
  | _ => []  -- Lnone, Lmem

/-- Variables read by an l-value (from index expressions). -/
def lvalReads : LVal → List Var
  | .Lmem _ x off => x.var :: exprVars off
  | .Laset _ _ _ idx => exprVars idx
  | .Lasub _ _ _ _ idx => exprVars idx
  | _ => []

/-! ## Instruction-Level Analysis -/

/-- Variables written by an instruction (simplified: only Cassgn to Lvar). -/
def instrWrites : InstrR → List Var
  | .Cassgn lv _ _ _ => lvalWrites lv
  | .Copn lvs _ _ _ => (lvs.map lvalWrites).flatten
  | _ => []

/-- Variables read by an instruction. -/
def instrReads : InstrR → List Var
  | .Cassgn lv _ _ e => lvalReads lv ++ exprVars e
  | .Copn lvs _ _ es => (lvs.map lvalReads).flatten ++ (es.map exprVars).flatten
  | .Cif c th el => exprVars c ++ cmdReads th ++ cmdReads el
  | .Cfor _ _ body => cmdReads body
  | .Cwhile cb cond ca => cmdReads cb ++ exprVars cond ++ cmdReads ca
  | .Ccall _ lvs _ args => (lvs.map lvalReads).flatten ++ (args.map exprVars).flatten
where
  cmdReads : Cmd → List Var
    | [] => []
    | i :: is => instrReads i ++ cmdReads is

/-! ## Liveness Analysis -/

/-- Compute the set of live variables before a command,
    given the live variables after.
    Walk backwards: for each instruction, add reads and remove writes
    (if the write is to a variable that is not live after). -/
def liveBeforeCmd : Cmd → List Var → List Var
  | [], live => live
  | i :: is, liveOut =>
    let liveAfterRest := liveBeforeCmd is liveOut
    let reads := instrReads i
    let writes := instrWrites i
    reads ++ (liveAfterRest.filter fun v => !writes.contains v)

/-! ## Dead Code Elimination -/

/-- Check if an instruction is dead (writes only to non-live variables
    and has no side effects). Only eliminates `Cassgn` to `Lvar`. -/
def isDeadInstr (liveAfter : List Var) : InstrR → Bool
  | .Cassgn (.Lvar x) _ _ _ => !liveAfter.contains x.var
  | _ => false

/-- Remove dead assignments from a command, given the live-out variables. -/
def deadCodeElim (liveOut : List Var) : Cmd → Cmd
  | [] => []
  | i :: is =>
    let restElim := deadCodeElim liveOut is
    let liveAfterI := liveBeforeCmd is liveOut
    if isDeadInstr liveAfterI i then restElim
    else i :: restElim

/-! ## Correctness

Dead code elimination does **not** satisfy `CmdPassCorrect` because that predicate
requires full `SPComp` equality including output heap state:
```
CmdPassCorrect pass ↔
  ∀ env sid fuel cmd, (translateCmd env (pass cmd) ...).code.eval =
                      (translateCmd env cmd ...).code.eval
```
where `SPComp α = Heap → SDistr (α × Heap)`. Since DCE removes writes to dead
variables, the output heaps differ at those locations. This makes `CmdPassCorrect`
**false** for DCE.

The correct property is *contextual equivalence* restricted to live locations:
any continuation that only reads live-out variables observes the same behavior.
Formalizing this requires:

1. **Location independence**: Showing that a computation is independent of a set
   of heap locations (neither reads nor writes affect observable behavior)
2. **Frame property**: Writing to an independent location then running independent
   code yields the same observable output distribution
3. **Translation tracking**: `translateCmd` only accesses locations corresponding
   to variables in the command's read/write sets

These properties are standard in separation logic and verified compilers (e.g.,
Jasmin/EasyCrypt uses a frame rule on module memories). The definitions above
(`exprVars`, `instrReads`, `instrWrites`, `liveBeforeCmd`, `deadCodeElim`) are
the complete DCE implementation — only the correctness proof is omitted.

No axiom is introduced: the pass is available as an unverified optimization.
The constant folding and nop elimination passes are fully verified. -/

end CatCrypt.Crypto.Jasmin
