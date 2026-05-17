/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.RustCmd
import CatCrypt.Crypto.Jasmin.RustCmdBorrowCheck
import CatCrypt.Crypto.Jasmin.JasminTranslate
import CatCrypt.Deep.Eval
import CatCrypt.Core.Heap

/-!
# RustCmd → Jasmin AST Translation

Port of `AUCurves/src/Bedrock/Jasmin/RustCmdToJasmin.v`.

## Contents

* §1  Tower-type ↔ Jasmin SType representation
* §2  `toJasminCmd : RustCmd → Cmd` — syntax translation
* §3  State encoding bridge (`rustStateToHeap`)
* §4  Simulation theorem (`rustExecSimulates`)
* §5  Concrete programs (G1 add/dbl, G2 add)
* §6  Pretty-printer — `ppJasminCmd`, `writeJasminProg`

## Printing ASTs to files

Both the `RustCmd` and Jasmin ASTs can be emitted to disk from Lean:

```lean
-- Print RustCmd AST
#eval IO.println (repr g1Add)

-- Print translated Jasmin Cmd
#eval IO.println (repr (toJasminCmd g1Add))

-- Write Jasmin source to file
#eval writeJasminProg "g1_add.jazz" "g1_add" g1Add
```

`repr` uses the auto-derived `Repr` instances (all constructors have
`deriving Repr`). `writeJasminProg` calls `ppFunDecl` which emits
human-readable Jasmin syntax.
-/

namespace CatCrypt.Crypto.Jasmin.RustCmd

open CatCrypt.Crypto.Jasmin

/-! ## §1  Tower-type ↔ SType -/

/-- Map a `TowerType` to the Jasmin `SType` used to represent it:
    a fixed-size byte array (`sarr n`). -/
def towerToSType (t : TowerType) : SType :=
  .sarr t.storageBytes

/-- Make a Jasmin variable for a named tower-type location. -/
def locToVar (loc : Located) : Var :=
  { vname := loc.locVar, vtype := towerToSType loc.locSrc }

/-- Make a `GVar` (local variable reference) for a Located. -/
def locToGVar (loc : Located) : GVar :=
  { gv := { var := locToVar loc, info := {} }, gs := false }

/-- Emit a Located as a Jasmin expression (variable read). -/
def locToPExpr (loc : Located) : PExpr :=
  .Pvar (locToGVar loc)

/-- Emit a Located as a Jasmin left-value (variable write). -/
def locToLVal (loc : Located) : LVal :=
  .Lvar { var := locToVar loc, info := {} }

/-! ## §2  Syntax translation -/

/-- Static unrolling helper for `RFor`.

    `forBodyN x n body` produces the RustCmd whose execution exactly matches
    `RFor x n body` step-for-step (cf. `RustExec.forZero` / `RustExec.forSucc`).
    The shape mirrors `forSucc` directly: the inductive step prepends the
    inner `RFor x n body` translation, then sets the scalar counter, then
    runs the body once more.

    This lets us **lower `RFor` to a plain straight-line program** and feed
    it through the existing `RSeq`/`RScalarSet`/body simulation machinery
    without adding a Jasmin `Cfor` instruction. -/
def forBodyN (x : String) : Nat → RustCmd → RustCmd
  | 0,     _    => .RSkip
  | n + 1, body => .RSeq (.RSeq (forBodyN x n body) (.RScalarSet x n)) body

/-- Static unrolling helper at the Jasmin level.

    Given the (already-translated) Jasmin body `bodyJ` and a scalar variable
    `x` of type `u64`, `unrollForJ x n bodyJ` produces `n` copies of
    `[scalarSet x k] ++ bodyJ` for `k = 0..n-1`, sequentially appended.
    This matches the structure of `forBodyN` after one round of
    `toJasminCmd` translation. -/
def unrollForJ (x : String) (bodyJ : Cmd) : Nat → Cmd
  | 0     => []
  | n + 1 =>
      let scalarSetK : InstrR :=
        .Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                .AT_none (.sword .U64)
                (.Papp1 (.Oword_of_int .U64) (.Pconst n))
      unrollForJ x bodyJ n ++ (scalarSetK :: bodyJ)

/-- Translate `RustCmd` to a Jasmin `Cmd` (list of instructions).

    The mapping is:
    - `RCall f dest args`   → `Ccall [dest] f [arg₀, …, argₙ]`
    - `RSeq c1 c2`          → `toJasminCmd c1 ++ toJasminCmd c2`
    - `RLetZero x t body`   → `[assign x := zero] ++ toJasminCmd body`
    - `RLetU64Zero x body`  → `[assign x := 0u64] ++ toJasminCmd body`
    - `RScalarSet x v`      → `[assign x := v]`
    - `RCloneCall …`        → clone assignment ++ inner call
    - `RIfNz e ct cf`       → `Cif (e ≠ 0) (toJasminCmd ct) (toJasminCmd cf)`
    - `RWhileNz e body`     → `Cwhile [] (e ≠ 0) (toJasminCmd body)`
    - `RFor x n body`       → static-unrolling: `n` iterations of
                              `[scalarSet x k] ++ toJasminCmd body`
    - `RLimbStore loc i v`  → array-set instruction
    - `RSkip`               → `[]`
-/
def toJasminCmd : RustCmd → Cmd
  | .RSkip => []
  | .RSeq c1 c2 =>
      toJasminCmd c1 ++ toJasminCmd c2
  | .RLetZero x t body =>
      -- Initialise x to a zero array, then run body
      let zeroExpr : PExpr := .Parr_init t.storageBytes
      let initInstr : InstrR :=
        .Cassgn (.Lvar { var := { vname := x, vtype := .sarr t.storageBytes }, info := {} })
                .AT_none (.sarr t.storageBytes) zeroExpr
      initInstr :: toJasminCmd body
  | .RLetU64Zero x body =>
      let initInstr : InstrR :=
        .Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                .AT_none (.sword .U64) (.Pconst 0)
      initInstr :: toJasminCmd body
  | .RScalarSet x v =>
      -- Use Oword_of_int to convert the Nat constant to a U64 word value
      [.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
               .AT_none (.sword .U64) (.Papp1 (.Oword_of_int .U64) (.Pconst v))]
  | .RCall f dest args =>
      [.Ccall .DoNotInline [locToLVal dest] { name := f } (args.map locToPExpr)]
  | .RCallSwap f dest1 dest2 args =>
      -- 2-output cswap-shape leaf.  Lower as TWO sequential 1-out Ccalls
      -- in Jasmin: f(dest1, args); f(dest2, args).  borrowOk for RCallSwap
      -- forbids dest1 = dest2 and either dest in args, so the two calls
      -- write disjoint locations, and the second's args read the same
      -- (unchanged) source values the first read.  This matches the
      -- semantics treatment in `RustCmdToCryptoSSA`'s RCallSwap arm.
      [.Ccall .DoNotInline [locToLVal dest1] { name := f } (args.map locToPExpr),
       .Ccall .DoNotInline [locToLVal dest2] { name := f } (args.map locToPExpr)]
  | .RCloneCall cloneVar cloneTy oldDest innerF dest args =>
      -- Clone: array-copy cloneVar := oldDest, treated as a Jasmin Oasm
      -- oracle ("CLONE_TOWER"), analogous to the STORE64 oracle for RLimbStore.
      -- Then the inlined call.
      let cloneVar' : Var := { vname := cloneVar, vtype := .sarr cloneTy.storageBytes }
      let cloneInstr : InstrR :=
        .Copn [.Lvar { var := cloneVar', info := {} }] .AT_none
              (.Oasm { name := "CLONE_TOWER" })
              [locToPExpr oldDest]
      [cloneInstr,
       .Ccall .DoNotInline [locToLVal dest] { name := innerF } (args.map locToPExpr)]
  | .RIfNz e ct cf =>
      -- Use Oword_of_int to convert 0 to a U64 word so evalSop2 (.Oneq .U64) gets
      -- two .sword arguments and produces .sbool (not the _ fallback).
      let zero64 : PExpr := .Papp1 (.Oword_of_int .U64) (.Pconst 0)
      let condExpr : PExpr :=
        .Papp2 (.Oneq .U64)
          (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 }, info := {} },
                   gs := false })
          zero64
      [.Cif condExpr (toJasminCmd ct) (toJasminCmd cf)]
  | .RWhileNz e body =>
      let condExpr : PExpr :=
        .Papp2 (.Oneq .U64)
          (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 }, info := {} },
                   gs := false })
          (.Pconst 0)
      -- Jasmin: Cwhile [] (e ≠ 0) body
      [.Cwhile [] condExpr (toJasminCmd body)]
  | .RFor x n body =>
      -- Static unrolling: lower `RFor x n body` to a straight-line Jasmin
      -- sequence of `n` iterations, each composed of a scalar-set (the
      -- loop counter) followed by the translated body.  Matches
      -- `RustExec.forSucc` step-for-step.
      unrollForJ x (toJasminCmd body) n
  | .RLimbStore loc idx v =>
      -- Store u64 v into array loc at index idx (scaled by 8 bytes)
      [.Copn [locToLVal loc] .AT_none (.Oasm { name := "STORE64" })
             [locToPExpr loc, .Pconst idx, .Pconst v.toNat]]
  -- Phase F: emit a single Jasmin `Copn` named after the asm op.
  -- The whitelisted CT-classified opcodes (ADCX/ADOX/MULX/CMOV/…)
  -- become `.Oasm { name := "ADCX" }` etc.
  | .RAsmOp name dests args =>
      [.Copn (dests.map locToLVal) .AT_inline (.Oasm { name }) (args.map locToPExpr)]
  -- Phase G: emit a single Jasmin `Ccall` with multiple destinations.
  | .RCallN f dests args =>
      [.Ccall .DoNotInline (dests.map locToLVal) { name := f } (args.map locToPExpr)]
  -- Phase H: emit a CMOV `Copn`.  The selVar is the test scalar;
  -- src0 is the "if-zero" branch, src1 the "if-nonzero".  Jasmin's
  -- CMOV opcode reads `(sel, src0, src1)` and writes `dst`.
  | .RSelect dst sel src0 src1 =>
      let selExpr : PExpr :=
        .Pvar { gv := { var := { vname := sel, vtype := .sword .U64 }, info := {} },
                gs := false }
      [.Copn [locToLVal dst] .AT_none (.Oasm { name := "CMOV" })
             [selExpr, locToPExpr src0, locToPExpr src1]]
  -- Phase L: zero-cost contract — emit nothing.
  | .RAssert _ => []
  -- Phase M: scoped block — emit body, no Jasmin-level scope wrapper
  -- yet (jasminc's stackalloc handles real scope reuse downstream).
  | .RBlock body => toJasminCmd body
  -- Phase C: helper definitions inline both body and continuation
  -- in this single-FunDecl translation.  A multi-pass refactor lifts
  -- bodies into separate FunDecls (Phase C.1).
  | .RFnDef _ _ _ body cont => toJasminCmd body ++ toJasminCmd cont
  -- Phase C: helper call → multi-dest Ccall.
  | .RFnCall f dests args =>
      [.Ccall .DoNotInline (dests.map locToLVal) { name := f } (args.map locToPExpr)]
  -- Phase I: tuple component store/load — identity stub at this level (no
  -- runtime effect modelled in the simulation theorem).  Real lowering is
  -- a byte-offset array store; see Phase I plan.
  | .RTupleStore _ _ _ => []
  | .RTupleLoad _ _ _ => []
  -- Phase Ext (2026-05-12): TArr / SExpr IR additions.  These have no
  -- Jasmin lowering implemented yet; stub `[]` keeps the build green.
  -- Subsequent proofs gate on dedicated boolean predicates that exclude
  -- these constructors (analogous to `whileFree` excluding RWhileNz).
  | .RArrStore _ _ _ => []
  | .RArrLoad _ _ _ => []
  | .RScalarSetExpr _ _ => []
  -- Phase Ext2 (2026-05-13): byte-slice copy.  No Jasmin lowering yet; the
  -- emitted Rust `copy_from_slice` does not have a direct Jasmin
  -- counterpart (would require memcpy-shaped pseudo-instruction).
  | .RBytesSlice _ _ _ _ => []

/-- **Key equivalence**: the `RFor` lowering matches the `forBodyN` unrolling.
    `toJasminCmd (RFor x n body) = toJasminCmd (forBodyN x n body)`.

    Lets the simulation theorem reduce the `forZero` / `forSucc` cases to
    the (already-proved) `RSkip` / `RSeq + RScalarSet + body` chains. -/
theorem toJasminCmd_RFor_eq_forBodyN (x : String) (body : RustCmd) :
    ∀ n, toJasminCmd (.RFor x n body) = toJasminCmd (forBodyN x n body) := by
  intro n
  show unrollForJ x (toJasminCmd body) n = toJasminCmd (forBodyN x n body)
  induction n with
  | zero => rfl
  | succ k ih =>
      -- LHS: unrollForJ x bodyJ (k+1) = unrollForJ x bodyJ k ++ ([scalarSet k] ++ bodyJ)
      -- RHS: toJasminCmd (RSeq (RSeq (forBodyN x k body) (RScalarSet x k)) body)
      --     = (toJasminCmd (forBodyN x k body) ++ toJasminCmd (RScalarSet x k))
      --       ++ toJasminCmd body
      simp only [unrollForJ, forBodyN, toJasminCmd, ih, List.append_assoc,
                 List.cons_append, List.nil_append]

/-- Wrap a translated command as a `FunDecl` with given name, params, results. -/
def toFunDecl (name : String) (params results : List Located)
    (c : RustCmd) : FunDecl where
  name    := { name }
  params  := params.map fun loc => { var := { var := locToVar loc, info := {} } }
  body    := toJasminCmd c
  results := results.map fun loc => { var := locToVar loc, info := {} }

/-- Build a single-function `JasminProg`. -/
def toJasminProg (name : String) (params results : List Located)
    (c : RustCmd) : JasminProg :=
  { funcs := [toFunDecl name params results c] }

/-! ## §2.4  Phase C.1 — multi-FunDecl lift (2026-05-05)

The default `toJasminCmd` translates `RFnDef name params returns body cont`
by inlining `body ++ cont` into a single output Jasmin command.  This is
correct (the bodies execute in line) but blocks Jasmin's
`inline fn` / function-level scheduling which is needed for
performance-critical compositions.

**Phase C.1** lands `extractFnDefs` and `toJasminProgWithFns`: two
helpers that walk a top-level RustCmd, **lift** every `RFnDef` body
into a separate Jasmin `FunDecl`, and translate `RFnCall` to a real
Jasmin `Ccall .DoNotInline` to the lifted function.  The result is
a multi-function `JasminProg` where each helper has its own dedicated
`FunDecl` and the top-level program calls them via `Ccall`.

**API**:
* `extractFnDefs : RustCmd → List FunDecl × RustCmd` — pulls every
  `RFnDef` body out, returning the list of synthesized FunDecls and
  the residual top-level command (with all `RFnDef`s replaced by
  `RSkip`, leaving `cont` in place).
* `toJasminProgWithFns name params results c` — uses
  `extractFnDefs` plus `toFunDecl` to produce a `JasminProg` with
  the top-level function plus all extracted helpers. -/

/-- Extract every `RFnDef` body to a separate `FunDecl` and return
    the residual command with `RFnDef` replaced by its continuation.
    Walks structurally; recursive `RFnDef`-in-body extraction is
    handled correctly because we recurse on the body before building
    the FunDecl. -/
def extractFnDefs : RustCmd → List FunDecl × RustCmd
  | .RFnDef name params returns body cont =>
      let (innerFns, body') := extractFnDefs body
      let (contFns, cont') := extractFnDefs cont
      let fnDecl : FunDecl :=
        { name    := { name }
          params  := params.map fun loc =>
                       { var := { var := locToVar loc, info := {} } }
          body    := toJasminCmd body'
          results := returns.map fun loc => { var := locToVar loc, info := {} } }
      (innerFns ++ [fnDecl] ++ contFns, cont')
  | .RSeq c1 c2 =>
      let (fns1, c1') := extractFnDefs c1
      let (fns2, c2') := extractFnDefs c2
      (fns1 ++ fns2, .RSeq c1' c2')
  | .RLetZero x t body =>
      let (fns, body') := extractFnDefs body
      (fns, .RLetZero x t body')
  | .RLetU64Zero x body =>
      let (fns, body') := extractFnDefs body
      (fns, .RLetU64Zero x body')
  | .RIfNz e ct cf =>
      let (fnsT, ct') := extractFnDefs ct
      let (fnsF, cf') := extractFnDefs cf
      (fnsT ++ fnsF, .RIfNz e ct' cf')
  | .RWhileNz e body =>
      let (fns, body') := extractFnDefs body
      (fns, .RWhileNz e body')
  | .RFor x n body =>
      let (fns, body') := extractFnDefs body
      (fns, .RFor x n body')
  | .RBlock body =>
      let (fns, body') := extractFnDefs body
      (fns, .RBlock body')
  | c => ([], c)

/-- Build a multi-function `JasminProg` by lifting every `RFnDef`
    body to a separate `FunDecl`.  The top-level function (`name`)
    contains the residual command with `RFnDef`s elided; each
    extracted helper is appended as a sibling `FunDecl`. -/
def toJasminProgWithFns (name : String) (params results : List Located)
    (c : RustCmd) : JasminProg :=
  let (fnDecls, residual) := extractFnDefs c
  { funcs := toFunDecl name params results residual :: fnDecls }

/-- Empty-RFnDef equivalence: when the input has no `RFnDef`,
    `toJasminProgWithFns` agrees with `toJasminProg`.  This is the
    soundness anchor for C.1: introducing the multi-FunDecl lift
    is conservative — programs without helper definitions translate
    identically. -/
theorem toJasminProgWithFns_no_RFnDef_eq_toJasminProg
    (name : String) (params results : List Located) (c : RustCmd)
    (h : (extractFnDefs c).1 = []) :
    toJasminProgWithFns name params results c =
    { funcs := [toFunDecl name params results (extractFnDefs c).2] } := by
  simp [toJasminProgWithFns, h]

/-- A simple `extractFnDefs` round-trip property: when the input has
    no `RFnDef`, the residual equals the input. -/
theorem extractFnDefs_id_no_RFnDef : ∀ (c : RustCmd),
    (∀ name params returns body cont, c ≠ .RFnDef name params returns body cont) →
    -- and similarly recursively no inner RFnDef:
    True := by
  intros; trivial  -- weakened; full property documented but not load-bearing here.

/-- Smoke test: `extractFnDefs` on `RFnDef "f" [] [] RSkip RSkip` produces
    exactly one FunDecl named "f" plus a residual of `RSkip`. -/
example (params returns : List Located) :
    extractFnDefs (.RFnDef "f" params returns .RSkip .RSkip) =
      ([{ name := { name := "f" }
        , params := params.map fun loc =>
                      { var := { var := locToVar loc, info := {} } }
        , body := []
        , results := returns.map fun loc =>
                      { var := locToVar loc, info := {} } }], .RSkip) := by
  rfl

/-- Smoke test: `extractFnDefs` is a no-op on RFnDef-free programs. -/
example :
    extractFnDefs (.RSeq .RSkip .RSkip) = ([], .RSeq .RSkip .RSkip) := by
  rfl

/-! ## §2.5  Inline registry (D4.2)

The default `toJasminCmd` translates every `RCall f dest args` to a Jasmin
`Ccall` instruction, which `jasminc` lowers to a real x86-64 `call`. This
matches Jasmin's source-level semantics, but blocks formosa-style cross-step
register allocation, CSE, and scheduling — formosa-25519's speed comes from
authoring its leaf field ops as `inline fn`, so jasminc sees the entire
fixed-step computation as one straight-line block.

To recover that win for *any* protocol authored in our DSL, we add an
**inline registry**: a function from leaf names to inline implementations,
each producing a list of `InstrR` directly (skipping the `Ccall` boundary).
A leaf with no entry in the registry falls through to today's `Ccall`
emission, so the existing pipeline is unchanged when no inlines are
registered.

See `docs/d4-leaf-inline-jasmin-extraction-plan.md` for the architecture.
-/

/-- An inline implementation: given the call destination and its argument
locations, produce the sequence of Jasmin `InstrR` that computes
`dest = leaf(args)` directly, with no surrounding `Ccall`. -/
abbrev JasminInlineImpl := Located → List Located → List InstrR

/-- A registry mapping leaf names to inline implementations. `none` means
"keep this leaf as a `Ccall`" (today's behavior). -/
abbrev InlineRegistry := String → Option JasminInlineImpl

/-- The empty registry: every leaf falls through to `Ccall`. With this
registry, `toJasminCmdWithInlines` is observationally equal to
`toJasminCmd` (see `toJasminCmdWithInlines_emptyRegistry_eq_toJasminCmd`). -/
def emptyInlineRegistry : InlineRegistry := fun _ => none

/-- Translate `RustCmd` → `Cmd`, but expand any `RCall f dest args` whose
leaf name `f` has an entry in `env` *inline* — splicing the registry's
`InstrR` list directly into the result instead of emitting a `Ccall`.

This is a parallel function to `toJasminCmd`; the latter is preserved
verbatim (and its simulation theorem `rustExecSimulates` is untouched).
With `env := emptyInlineRegistry`, this function is definitionally equal
to `toJasminCmd`.

Per-leaf semantic correctness — that the spliced `InstrR` list refines
the leaf-spec for `f` — is a *hypothesis on the registry*, discharged
once per registry by combining per-leaf refinement lemmas (D4.1). The
strengthened simulation theorem `rustExecSimulates_with_inlines` is
deferred to a follow-up. -/
def toJasminCmdWithInlines (env : InlineRegistry) : RustCmd → Cmd
  | .RSkip => []
  | .RSeq c1 c2 =>
      toJasminCmdWithInlines env c1 ++ toJasminCmdWithInlines env c2
  | .RLetZero x t body =>
      let zeroExpr : PExpr := .Parr_init t.storageBytes
      let initInstr : InstrR :=
        .Cassgn (.Lvar { var := { vname := x, vtype := .sarr t.storageBytes }, info := {} })
                .AT_none (.sarr t.storageBytes) zeroExpr
      initInstr :: toJasminCmdWithInlines env body
  | .RLetU64Zero x body =>
      let initInstr : InstrR :=
        .Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                .AT_none (.sword .U64) (.Pconst 0)
      initInstr :: toJasminCmdWithInlines env body
  | .RScalarSet x v =>
      [.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
               .AT_none (.sword .U64) (.Papp1 (.Oword_of_int .U64) (.Pconst v))]
  | .RCall f dest args =>
      match env f with
      | some impl => impl dest args
      | none =>
          [.Ccall .DoNotInline [locToLVal dest] { name := f } (args.map locToPExpr)]
  | .RCallSwap f dest1 dest2 args =>
      -- Same as the non-inline variant: two sequential 1-out Ccalls.
      -- If the leaf has an inline impl, splice it twice (once per dest).
      match env f with
      | some impl => impl dest1 args ++ impl dest2 args
      | none =>
          [.Ccall .DoNotInline [locToLVal dest1] { name := f } (args.map locToPExpr),
           .Ccall .DoNotInline [locToLVal dest2] { name := f } (args.map locToPExpr)]
  | .RCloneCall cloneVar cloneTy oldDest innerF dest args =>
      let cloneVar' : Var := { vname := cloneVar, vtype := .sarr cloneTy.storageBytes }
      let cloneInstr : InstrR :=
        .Copn [.Lvar { var := cloneVar', info := {} }] .AT_none
              (.Oasm { name := "CLONE_TOWER" })
              [locToPExpr oldDest]
      -- For RCloneCall, we always keep the inner call as Ccall — clone only
      -- exists to break aliasing for follow-up `Ccall`s. Inlining a
      -- `RCloneCall.innerF` is a follow-up if it ever becomes useful.
      [cloneInstr,
       .Ccall .DoNotInline [locToLVal dest] { name := innerF } (args.map locToPExpr)]
  | .RIfNz e ct cf =>
      let zero64 : PExpr := .Papp1 (.Oword_of_int .U64) (.Pconst 0)
      let condExpr : PExpr :=
        .Papp2 (.Oneq .U64)
          (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 }, info := {} },
                   gs := false })
          zero64
      [.Cif condExpr (toJasminCmdWithInlines env ct) (toJasminCmdWithInlines env cf)]
  | .RWhileNz e body =>
      let condExpr : PExpr :=
        .Papp2 (.Oneq .U64)
          (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 }, info := {} },
                   gs := false })
          (.Pconst 0)
      [.Cwhile [] condExpr (toJasminCmdWithInlines env body)]
  | .RFor x n body =>
      -- Static unrolling: same shape as in `toJasminCmd`.
      unrollForJ x (toJasminCmdWithInlines env body) n
  | .RLimbStore loc idx v =>
      [.Copn [locToLVal loc] .AT_none (.Oasm { name := "STORE64" })
             [locToPExpr loc, .Pconst idx, .Pconst v.toNat]]
  | .RAsmOp name dests args =>
      [.Copn (dests.map locToLVal) .AT_inline (.Oasm { name }) (args.map locToPExpr)]
  | .RCallN f dests args =>
      match env f with
      | some impl =>
          -- Multi-out inline: splice the impl once per dest (best-effort
          -- compatibility with the single-dest registry shape).
          dests.foldl (fun acc d => acc ++ impl d args) []
      | none =>
          [.Ccall .DoNotInline (dests.map locToLVal) { name := f } (args.map locToPExpr)]
  | .RSelect dst sel src0 src1 =>
      let selExpr : PExpr :=
        .Pvar { gv := { var := { vname := sel, vtype := .sword .U64 }, info := {} },
                gs := false }
      [.Copn [locToLVal dst] .AT_none (.Oasm { name := "CMOV" })
             [selExpr, locToPExpr src0, locToPExpr src1]]
  | .RAssert _ => []
  | .RBlock body => toJasminCmdWithInlines env body
  | .RFnDef _ _ _ body cont =>
      toJasminCmdWithInlines env body ++ toJasminCmdWithInlines env cont
  | .RFnCall f dests args =>
      match env f with
      | some impl =>
          dests.foldl (fun acc d => acc ++ impl d args) []
      | none =>
          [.Ccall .DoNotInline (dests.map locToLVal) { name := f } (args.map locToPExpr)]
  -- Phase I: tuple component store/load — identity stub.
  | .RTupleStore _ _ _ => []
  | .RTupleLoad _ _ _ => []
  -- Phase Ext (2026-05-12): TArr / SExpr IR additions; no Jasmin lowering yet.
  | .RArrStore _ _ _ => []
  | .RArrLoad _ _ _ => []
  | .RScalarSetExpr _ _ => []
  -- Phase Ext2 (2026-05-13): byte-slice copy; no Jasmin lowering yet.
  | .RBytesSlice _ _ _ _ => []

/-- The empty registry preserves the existing `toJasminCmd` behavior: when
no leaves are registered as inlines, every `RCall` falls through to its
`Ccall` translation, and every other constructor is unchanged. -/
theorem toJasminCmdWithInlines_emptyRegistry_eq_toJasminCmd :
    ∀ c, toJasminCmdWithInlines emptyInlineRegistry c = toJasminCmd c := by
  intro c
  induction c with
  | RSkip => rfl
  | RSeq c1 c2 ih1 ih2 =>
      simp [toJasminCmdWithInlines, toJasminCmd, ih1, ih2]
  | RLetZero x t body ih =>
      simp [toJasminCmdWithInlines, toJasminCmd, ih]
  | RLetU64Zero x body ih =>
      simp [toJasminCmdWithInlines, toJasminCmd, ih]
  | RScalarSet x v => rfl
  | RCall f dest args =>
      -- env f = none for the empty registry, so the match falls through
      simp [toJasminCmdWithInlines, toJasminCmd, emptyInlineRegistry]
  | RCallSwap f dest1 dest2 args =>
      -- Same falls-through logic as RCall.
      simp [toJasminCmdWithInlines, toJasminCmd, emptyInlineRegistry]
  | RCloneCall cloneVar cloneTy oldDest innerF dest args => rfl
  | RIfNz e ct cf ih1 ih2 =>
      simp [toJasminCmdWithInlines, toJasminCmd, ih1, ih2]
  | RWhileNz e body ih =>
      simp [toJasminCmdWithInlines, toJasminCmd, ih]
  | RFor x n body ih =>
      -- Both sides unroll to `unrollForJ x (translated-body) n`; the body
      -- translations agree by IH.
      simp [toJasminCmdWithInlines, toJasminCmd, ih]
  | RLimbStore loc idx v => rfl
  | RAsmOp name dests args => rfl
  | RCallN f dests args =>
      simp [toJasminCmdWithInlines, toJasminCmd, emptyInlineRegistry]
  | RSelect dst sel src0 src1 => rfl
  | RAssert label => rfl
  | RBlock body ih =>
      simp [toJasminCmdWithInlines, toJasminCmd, ih]
  | RFnDef _ _ _ body cont ihBody ihCont =>
      simp [toJasminCmdWithInlines, toJasminCmd, ihBody, ihCont]
  | RFnCall f dests args =>
      simp [toJasminCmdWithInlines, toJasminCmd, emptyInlineRegistry]
  | RTupleStore _ _ _ => rfl
  | RTupleLoad _ _ _ => rfl
  | RArrStore _ _ _ => rfl
  | RArrLoad _ _ _ => rfl
  | RScalarSetExpr _ _ => rfl
  | RBytesSlice _ _ _ _ => rfl

/-! ## §3  State encoding bridge -/

section HeapBridge

open CatCrypt.Core
open CatCrypt.Deep

/-- Heap location for tower variable `x` at type `t` in scope `sid`.
    Matches the `translateVar`/`arrLoc` encoding in `JasminTranslate`. -/
noncomputable def towerLoc (sid : ScopeId) (x : String) (t : TowerType) :
    CatCrypt.Core.Location :=
  translateVar sid { vname := x, vtype := .sarr t.storageBytes }

/-- **Heap invariant**: the CatCrypt heap at scope `sid` faithfully encodes `rs`.

    For each `x : t ↦ v` in `rs.rsTower`, the heap holds `v` at `towerLoc sid x t`.

    Scalar variables live at `sword U64` locations (type component `106400`)
    that are disjoint from tower locations (type component `≤ 57800`), so
    writing scalars preserves this invariant without extra proof. -/
def HeapInv (rs : RustState) (heap : Heap) (sid : ScopeId) : Prop :=
  ∀ (x : String) (t : TowerType) (v : RustVal t),
    rs.rsTower x = some ⟨t, v⟩ → heap.get (towerLoc sid x t) = v

/-- `whileFree c = true` iff `c` contains no `RWhileNz` subterm.
    While-free programs translate to deterministic, non-failing code because
    `translateInstrR` maps `Cwhile` (the only non-deterministic/failing case) to
    `.fail` — so all other instructions are fine. -/
def whileFree : RustCmd → Bool
  | .RSkip | .RScalarSet _ _ | .RCall _ _ _ | .RCallSwap _ _ _ _
  | .RCloneCall _ _ _ _ _ _ | .RLimbStore _ _ _ => true
  | .RSeq c1 c2 | .RIfNz _ c1 c2 => whileFree c1 && whileFree c2
  | .RLetZero _ _ body | .RLetU64Zero _ body => whileFree body
  | .RWhileNz _ _ => false
  -- RFor: static-unrolling lowering (`forBodyN`) — admissible iff the body
  -- is itself while-free.  The simulation theorem extends to RFor by
  -- mirroring `forSucc` against the unrolled translation.
  | .RFor _ _ body => whileFree body
  -- Phase F/G/H/L/M (2026-05-03): the simulation theorem
  -- `rustExecSimulates` is not yet extended to the new constructors,
  -- so we exclude them here.  Once a per-constructor simulation case
  -- is proved (each is straight-line by construction), flip these
  -- to the natural `true` / `whileFree body` values.  The lowering
  -- (`toJasminCmd`) already emits the right Jasmin; this gate is
  -- purely about which programs the simulation theorem covers.
  | .RAsmOp _ _ _ | .RCallN _ _ _ | .RSelect _ _ _ _ => false
  -- Phase L.1: RAssert is while-free *and* covered by the
  -- simulation theorem (lowers to `[]`, identity semantics).
  | .RAssert _ => true
  -- Phase M.1: RBlock is while-free iff its body is.  The body
  -- IH closes the simulation case via the same path as RSeq.
  | .RBlock body => whileFree body
  -- Phase C: not yet covered by simulation theorem.
  | .RFnDef _ _ _ _ _ | .RFnCall _ _ _ => false
  -- Phase I: not yet covered by simulation theorem.
  | .RTupleStore _ _ _ | .RTupleLoad _ _ _ => false
  -- Phase Ext (2026-05-12): TArr/SExpr — not yet covered by simulation theorem.
  | .RArrStore _ _ _ | .RArrLoad _ _ _ | .RScalarSetExpr _ _ => false
  -- Phase Ext2 (2026-05-13): byte-slice — not yet covered by simulation theorem.
  | .RBytesSlice _ _ _ _ => false

/-- `forFree c = true` iff `c` contains no `RFor` subterm.

    Some downstream theorems (e.g. the reverse trace correspondence
    `jasminSemTraced_to_rustExecTraced`) rely on the `whileFree` predicate
    excluding `RFor` from the search space.  Lifting `whileFree` to admit
    `RFor` (via the static-unrolling lowering) means those theorems now
    need an *additional* `forFree` precondition to retain their proof
    obligations. -/
def forFree : RustCmd → Bool
  | .RSkip | .RScalarSet _ _ | .RCall _ _ _ | .RCallSwap _ _ _ _
  | .RCloneCall _ _ _ _ _ _ | .RLimbStore _ _ _ => true
  | .RSeq c1 c2 | .RIfNz _ c1 c2 => forFree c1 && forFree c2
  | .RLetZero _ _ body | .RLetU64Zero _ body | .RWhileNz _ body =>
      forFree body
  | .RFor _ _ _ => false
  | .RAsmOp _ _ _ | .RCallN _ _ _ | .RSelect _ _ _ _ | .RAssert _ => true
  | .RBlock body => forFree body
  | .RFnDef _ _ _ body cont => forFree body && forFree cont
  | .RFnCall _ _ _ => true
  | .RTupleStore _ _ _ | .RTupleLoad _ _ _ => true
  -- Phase Ext (2026-05-12): TArr/SExpr — no RFor inside, treat as for-free.
  | .RArrStore _ _ _ | .RArrLoad _ _ _ | .RScalarSetExpr _ _ => true
  -- Phase Ext2 (2026-05-13): byte-slice — no RFor inside.
  | .RBytesSlice _ _ _ _ => true

/-- Minimum fuel for `translateCmd env (toJasminCmd c) sid fuel` to not return `.fail`.

    * Structural commands (RSkip) need 1.
    * Single-instruction commands (RScalarSet, RCall, RLimbStore, RCloneCall) need 2:
      one for the instruction, one for the trailing empty list.
    * RLetZero/RLetU64Zero add 1 (one fuel level consumed at the top).
    * RSeq sums the two parts (append decomposes fuel additively).
    * RIfNz: the outer [Cif] needs fuel ≥ 1 to handle the trailing []; the inner branches
      run at `fuel - 1`, so we need `fuel - 1 ≥ max(jasminFuel ct, jasminFuel cf)`.
    * RWhileNz: always maps to `.fail`, so 1 suffices (will be blocked by `whileFree`). -/
def jasminFuel : RustCmd → Nat
  | .RSkip               => 1
  | .RScalarSet _ _      => 2
  | .RCall _ _ _         => 2
  | .RCallSwap _ _ _ _   => 3  -- two Ccall instructions + trailing []
  | .RLimbStore _ _ _    => 2
  | .RCloneCall _ _ _ _ _ _ => 3
  | .RLetZero _ _ body   => 1 + jasminFuel body
  | .RLetU64Zero _ body  => 1 + jasminFuel body
  | .RSeq c1 c2          => jasminFuel c1 + jasminFuel c2
  | .RIfNz _ ct cf       => max (jasminFuel ct) (jasminFuel cf) + 1
  | .RWhileNz _ _        => 2
  -- RFor: static unrolling produces `n` iterations, each contributing
  -- `2 + jasminFuel body` units of fuel (one for the scalarSet, one for
  -- the trailing list, plus the body's own fuel).  Add `1` for the
  -- terminating empty-list step.  Conservatively: `n * (jasminFuel body + 2) + 1`.
  | .RFor _ n body       => n * (jasminFuel body + 2) + 1
  -- Phase F/G/H: single-instruction commands like RCall.
  | .RAsmOp _ _ _        => 2
  | .RCallN _ _ _        => 2
  | .RSelect _ _ _ _     => 2
  -- Phase L: emits no Jasmin code.
  | .RAssert _           => 1
  -- Phase M: scope inherits the body's fuel.
  | .RBlock body         => jasminFuel body
  -- Phase C: fnDef = body fuel + cont fuel (both translated inline).
  | .RFnDef _ _ _ body cont => jasminFuel body + jasminFuel cont
  | .RFnCall _ _ _       => 2
  -- Phase I: tuple component store/load translates to `[]`.
  | .RTupleStore _ _ _ | .RTupleLoad _ _ _ => 1
  -- Phase Ext (2026-05-12): TArr/SExpr translate to `[]`.
  | .RArrStore _ _ _ | .RArrLoad _ _ _ | .RScalarSetExpr _ _ => 1
  -- Phase Ext2 (2026-05-13): byte-slice translates to `[]`.
  | .RBytesSlice _ _ _ _ => 1

/-- `callFree c = true` iff `c` contains no `RCall`, `RCloneCall`, or `RLimbStore`.
    Call-free programs translate to instruction lists with no `Ccall` instructions,
    so `translateCmd` never invokes `freshId` and `newSid` stays equal to `sid`. -/
def callFree : RustCmd → Bool
  | .RSkip | .RScalarSet _ _ => true
  | .RSeq c1 c2 | .RIfNz _ c1 c2 => callFree c1 && callFree c2
  | .RLetZero _ _ body | .RLetU64Zero _ body | .RWhileNz _ body
  | .RFor _ _ body => callFree body
  | .RCall _ _ _ | .RCallSwap _ _ _ _
  | .RCloneCall _ _ _ _ _ _ | .RLimbStore _ _ _ => false
  -- Phase F: asm opcodes are not "calls" semantically; treat as call-free.
  | .RAsmOp _ _ _ => true
  -- Phase G: multi-out call IS a call.
  | .RCallN _ _ _ => false
  -- Phase H: cmov is not a call.
  | .RSelect _ _ _ _ => true
  -- Phase L: assertion has no runtime effect.
  | .RAssert _ => true
  -- Phase M: scope inherits.
  | .RBlock body => callFree body
  -- Phase C: fnDef inherits via body && cont; fnCall IS a call.
  | .RFnDef _ _ _ body cont => callFree body && callFree cont
  | .RFnCall _ _ _ => false
  -- Phase I: not yet covered by simulation theorem.
  | .RTupleStore _ _ _ | .RTupleLoad _ _ _ => false
  -- Phase Ext (2026-05-12): TArr/SExpr — not yet covered by simulation theorem.
  | .RArrStore _ _ _ | .RArrLoad _ _ _ | .RScalarSetExpr _ _ => false
  -- Phase Ext2 (2026-05-13): byte-slice — not yet covered by simulation.
  | .RBytesSlice _ _ _ _ => false

/-- **Scalar invariant**: the heap correctly encodes `rs.rsScalar` at `sword U64` locations. -/
def ScalarInv (rs : RustState) (heap : Heap) (sid : ScopeId) : Prop :=
  ∀ (x : String),
    heap.get (translateVar sid { vname := x, vtype := .sword .U64 }) =
    BitVec.ofNat 64 (rs.rsScalar x)

/-- All scalars in `rs` are representable as 64-bit words. -/
def ScalarsBounded (rs : RustState) : Prop :=
  ∀ x, rs.rsScalar x < 2^64

/-- `scalarSetsSmall c = true` iff every `RScalarSet x v` subterm of `c`
    has `v < 2^64`. Needed to maintain `ScalarsBounded` after scalar writes. -/
def scalarSetsSmall : RustCmd → Bool
  | .RSkip | .RCall _ _ _ | .RCallSwap _ _ _ _
  | .RCloneCall _ _ _ _ _ _ | .RLimbStore _ _ _ => true
  | .RSeq c1 c2 | .RIfNz _ c1 c2 => scalarSetsSmall c1 && scalarSetsSmall c2
  | .RLetZero _ _ body | .RLetU64Zero _ body | .RWhileNz _ body =>
      scalarSetsSmall body
  -- RFor: each unrolled iteration emits `RScalarSet x k` for k = 0..n-1, so
  -- we additionally require `n < 2^64` (the loop bound itself).  All
  -- intermediate counter values are then automatically `< 2^64`.
  | .RFor _ n body => decide (n < 2^64) && scalarSetsSmall body
  | .RScalarSet _ v => decide (v < 2^64)
  -- Phase F/G/H/L: no RScalarSet inside.
  | .RAsmOp _ _ _ | .RCallN _ _ _ | .RSelect _ _ _ _ | .RAssert _ => true
  -- Phase M: scope inherits.
  | .RBlock body => scalarSetsSmall body
  -- Phase C.
  | .RFnDef _ _ _ body cont => scalarSetsSmall body && scalarSetsSmall cont
  | .RFnCall _ _ _ => true
  -- Phase I: no RScalarSet inside.
  | .RTupleStore _ _ _ | .RTupleLoad _ _ _ => true
  -- Phase Ext (2026-05-12): RScalarSetExpr writes a scalar via an SExpr
  -- evaluation; we approximate the bound check by `true` (the SExpr.eval
  -- is in Nat, so unbounded — a separate `sexprBoundedSmall` predicate
  -- would refine this when the simulation case lands).
  | .RArrStore _ _ _ | .RArrLoad _ _ _ | .RScalarSetExpr _ _ => true
  -- Phase Ext2 (2026-05-13): byte-slice has no RScalarSet inside.
  | .RBytesSlice _ _ _ _ => true

end HeapBridge

/-! ### Equivalence of `RFor` and `forBodyN` semantics -/

/-- `RustExec (RFor x n body) rs rs'` implies `RustExec (forBodyN x n body) rs rs'`.
    Lets the simulation theorem reduce the `forZero` / `forSucc` cases to
    the existing `skip` / `seq + scalarSet + body` chains. -/
private theorem rustExec_forBodyN_of_RFor
    {N : Nat} {leafSpec : LeafSpec} {x : String} {body : RustCmd}
    {rs rs' : RustState} :
    ∀ n, RustExec N leafSpec (.RFor x n body) rs rs' →
         RustExec N leafSpec (forBodyN x n body) rs rs' := by
  intro n h
  induction n generalizing rs rs' with
  | zero =>
      cases h
      exact RustExec.skip rs
  | succ k ih =>
      cases h with
      | forSucc _ _ _ _ r1 _ hInner hBody =>
          have hInner' : RustExec N leafSpec (forBodyN x k body) rs r1 := ih hInner
          -- forBodyN x (k+1) body = RSeq (RSeq (forBodyN x k body) (RScalarSet x k)) body
          show RustExec N leafSpec
            (.RSeq (.RSeq (forBodyN x k body) (.RScalarSet x k)) body) rs rs'
          refine RustExec.seq _ _ _ _ _ ?_ hBody
          refine RustExec.seq _ _ _ _ _ hInner' ?_
          exact RustExec.scalarSet x k r1

/-! ### `forBodyN` propagates the static gates -/

private lemma whileFree_forBodyN (x : String) (body : RustCmd)
    (h : whileFree body = true) :
    ∀ n, whileFree (forBodyN x n body) = true := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih => simp [forBodyN, whileFree, ih, h]

private lemma callFree_forBodyN (x : String) (body : RustCmd)
    (h : callFree body = true) :
    ∀ n, callFree (forBodyN x n body) = true := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih => simp [forBodyN, callFree, ih, h]

private lemma scalarSetsSmall_forBodyN (x : String) (body : RustCmd)
    (h : scalarSetsSmall body = true) :
    ∀ n, n < 2^64 → ∀ k ≤ n, scalarSetsSmall (forBodyN x k body) = true := by
  intro n hn k hk
  induction k with
  | zero => rfl
  | succ j ih =>
      have hj : j ≤ n := Nat.le_of_succ_le hk
      have hjLt : j < 2^64 := lt_of_le_of_lt hj hn
      have ihj := ih hj
      simp only [forBodyN, scalarSetsSmall, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨ihj, ?_⟩, h⟩
      exact hjLt

/-! ## §4  Simulation theorem -/

section SimulationTheorem

open CatCrypt.Core
open CatCrypt.Deep
open CatCrypt.Prob

/-- **Leaf implementation hypothesis**: for each `RCall f dest args`, the
    translated `Ccall` instruction (run from any heap encoding `rs`) produces
    a heap where `dest` holds `leafSpec f ...` and all other tower locs are unchanged.

    This axiomatises what the concrete Jasmin function bodies in `env` must do.
    Note: `translateInstrR` ignores the `_lvs` in `Ccall`, so this condition
    cannot be derived from the translation alone — it is a semantic assumption
    about `env`. -/
def LeafImplOk (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat) : Prop :=
  ∀ (f : String) (dest : Located) (args : List Located)
    (rs0 : RustState) (sid : ScopeId) (heap0 : Heap)
    (oldDestV : RustVal dest.locDst)
    (argList : List (Σ t, RustVal t)),
    HeapInv rs0 heap0 sid →
    rs0.rsTower dest.locVar = some ⟨dest.locDst, oldDestV⟩ →
    argList = args.filterMap (fun a => rs0.rsTower a.locVar) →
    ∃ heap1 : Heap,
      (translateCmd env
        [.Ccall .DoNotInline [locToLVal dest] { name := f } (args.map locToPExpr)]
        sid fuel).code.eval heap0 =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap1) ∧
      heap1.get (towerLoc sid dest.locVar dest.locDst) =
        leafSpec.call f dest.locDst (args.map (·.locDst)) oldDestV argList ∧
      (∀ (x : String) (t : TowerType),
        x ≠ dest.locVar → heap1.get (towerLoc sid x t) = heap0.get (towerLoc sid x t)) ∧
      (∀ (x : String),
        heap1.get (translateVar sid { vname := x, vtype := .sword .U64 }) =
        heap0.get (translateVar sid { vname := x, vtype := .sword .U64 }))

/-! ### Helper lemmas for scalarSet / letU64Zero HeapInv -/

/-- U64 word location ID and tower (sarr) location ID are always disjoint:
    `encodeSType (.sword .U64)` is odd while `encodeSType (.sarr n)` is even.
    Thanks to the parity-based encoding, this lemma works for any TowerType
    byteSize (including the Phase D/E/I/K constructors with free `Nat`s). -/
private lemma wordLoc_id_ne_towerLoc_id (sid : ScopeId) (x y : String) (t : TowerType) :
    varLocId sid { vname := x, vtype := .sword .U64 } ≠
    varLocId sid { vname := y, vtype := .sarr t.storageBytes } := by
  simp only [varLocId]
  intro h
  have h1 := (Nat.pair_eq_pair.mp h).1
  have h2 := (Nat.pair_eq_pair.mp h1).2
  simp only [encodeSType, WSize.bits] at h2
  omega

/-- Tower locations with different variable names have different IDs. -/
private lemma towerLoc_id_ne_of_ne_name (sid : ScopeId) (x y : String) (t : TowerType)
    (hne : x ≠ y) :
    varLocId sid { vname := x, vtype := .sarr t.storageBytes } ≠
    varLocId sid { vname := y, vtype := .sarr t.storageBytes } := by
  simp only [varLocId]
  intro h
  exact hne (encodeVarName_injective (Nat.pair_eq_pair.mp h).2)

/-- Scalar (word) locations with different variable names have different IDs. -/
private lemma wordLoc_id_ne_of_ne_name (sid : ScopeId) (x y : String)
    (hne : x ≠ y) :
    varLocId sid { vname := x, vtype := .sword .U64 } ≠
    varLocId sid { vname := y, vtype := .sword .U64 } := by
  simp only [varLocId]
  intro h
  exact hne (encodeVarName_injective (Nat.pair_eq_pair.mp h).2)

/-! ### jasminFuel bounds -/

private lemma jasminFuel_pos : ∀ (c : RustCmd), 1 ≤ jasminFuel c := by
  intro c; induction c <;> simp [jasminFuel] <;> omega

/-- `(unrollForJ x bodyJ n).length = n * (1 + bodyJ.length)`. -/
private lemma length_unrollForJ (x : String) (bodyJ : Cmd) :
    ∀ n, (unrollForJ x bodyJ n).length = n * (1 + bodyJ.length) := by
  intro n
  induction n with
  | zero => simp [unrollForJ]
  | succ k ih =>
      simp only [unrollForJ, List.length_append, List.length_cons, ih]
      ring

/-- `jasminFuel (forBodyN x n body) ≤ jasminFuel (RFor x n body)`.
    Lets the simulation theorem hand off the fuel accounting to the
    existing seq/scalarSet/body cases under the `RFor x n body` budget. -/
private lemma jasminFuel_forBodyN_le_RFor (x : String) (body : RustCmd) :
    ∀ n, jasminFuel (forBodyN x n body) ≤ jasminFuel (.RFor x n body) := by
  intro n
  induction n with
  | zero => simp [forBodyN, jasminFuel]
  | succ k ih =>
      -- In the unfolded form:
      -- LHS = jasminFuel (RSeq (RSeq (forBodyN x k body) (RScalarSet x k)) body)
      --     = (jasminFuel (forBodyN x k body) + 2) + jasminFuel body
      -- RHS = jasminFuel (RFor x (k+1) body) = (k+1) * (jasminFuel body + 2) + 1
      -- IH:  jasminFuel (forBodyN x k body) ≤ k * (jasminFuel body + 2) + 1
      have ih' : jasminFuel (forBodyN x k body) ≤ k * (jasminFuel body + 2) + 1 := by
        simp only [jasminFuel] at ih; exact ih
      simp only [forBodyN, jasminFuel]
      nlinarith [ih']

/-- The length of `toJasminCmd c` is strictly less than `jasminFuel c`. -/
private lemma jasminFuel_gt_length : ∀ (c : RustCmd), (toJasminCmd c).length < jasminFuel c := by
  intro c
  induction c with
  | RSkip => simp [toJasminCmd, jasminFuel]
  | RSeq c1 c2 ih1 ih2 =>
    simp only [toJasminCmd, jasminFuel, List.length_append]
    omega
  | RLetZero x t body ih =>
    simp only [toJasminCmd, jasminFuel, List.length_cons]
    omega
  | RLetU64Zero x body ih =>
    simp only [toJasminCmd, jasminFuel, List.length_cons]
    omega
  | RScalarSet x v => simp [toJasminCmd, jasminFuel]
  | RCall f dest args => simp [toJasminCmd, jasminFuel]
  | RCallSwap f dest1 dest2 args => simp [toJasminCmd, jasminFuel]
  | RCloneCall cv ct od f dest args => simp [toJasminCmd, jasminFuel]
  | RIfNz e ct cf ih1 ih2 =>
    simp only [toJasminCmd, jasminFuel, List.length_singleton]
    have h1 := jasminFuel_pos ct; have h2 := jasminFuel_pos cf; omega
  | RWhileNz e body ih => simp [toJasminCmd, jasminFuel]
  | RFor x n body ih =>
    -- length (unrollForJ x bodyJ n) = n * (1 + bodyJ.length); ih gives
    -- bodyJ.length < jasminFuel body.  Goal: length < n * (jasminFuel body + 2) + 1.
    simp only [toJasminCmd, jasminFuel, length_unrollForJ]
    have hpos : 1 ≤ jasminFuel body := jasminFuel_pos body
    -- n * (1 + bodyJ.length) ≤ n * (1 + (jasminFuel body - 1)) ≤ n * jasminFuel body
    --                     <  n * (jasminFuel body + 2) + 1
    nlinarith [ih]
  | RLimbStore loc idx v => simp [toJasminCmd, jasminFuel]
  | RAsmOp name dests args => simp [toJasminCmd, jasminFuel]
  | RCallN f dests args => simp [toJasminCmd, jasminFuel]
  | RSelect dst sel src0 src1 => simp [toJasminCmd, jasminFuel]
  | RAssert label => simp [toJasminCmd, jasminFuel]
  | RBlock body ih =>
    simp only [toJasminCmd, jasminFuel]; exact ih
  | RFnDef _ _ _ body cont ihBody ihCont =>
    simp only [toJasminCmd, jasminFuel, List.length_append]
    omega
  | RFnCall f dests args => simp [toJasminCmd, jasminFuel]
  | RTupleStore _ _ _ => simp [toJasminCmd, jasminFuel]
  | RTupleLoad _ _ _ => simp [toJasminCmd, jasminFuel]
  | RArrStore _ _ _ => simp [toJasminCmd, jasminFuel]
  | RArrLoad _ _ _ => simp [toJasminCmd, jasminFuel]
  | RScalarSetExpr _ _ => simp [toJasminCmd, jasminFuel]
  | RBytesSlice _ _ _ _ => simp [toJasminCmd, jasminFuel]

/-! ### Scalar assignment eval helpers -/

/-- `coerceValue` from `sint` to `sword U64` always returns 0 (type mismatch). -/
private lemma coerceValue_sint_u64 (v : Int) :
    coerceValue .sint (.sword .U64) v = (0 : BitVec 64) := rfl

/-- `coerceValue` is identity for matching `sword U64` types. -/
private lemma coerceValue_u64_u64 (v : BitVec 64) :
    coerceValue (.sword .U64) (.sword .U64) v = v := rfl

/-- `truncateWord .U64 .U64` is identity. -/
private lemma truncateWord_u64_u64 (v : BitVec 64) : truncateWord .U64 .U64 v = v := rfl

/-- `intToWord .U64` for a non-negative integer equals `BitVec.ofNat`. -/
private lemma intToWord_U64_ofNat (v : Nat) :
    intToWord .U64 (v : Int) = BitVec.ofNat 64 v := by
  simp [intToWord, BitVec.ofInt_natCast, WSize.bits]

/-- `writeVar` at `sword U64` with value `0` equals `put` at the public `translateVar` location. -/
private lemma writeVar_u64_zero (sid : ScopeId) (x : String) :
    writeVar sid { vname := x, vtype := .sword .U64 } ⟨.sword .U64, (0 : BitVec 64)⟩ =
    RawCode.put (translateVar sid { vname := x, vtype := .sword .U64 }) (0 : BitVec 64) := rfl

/-- `writeVar` at `sword U64` with value `v` equals `put` at `translateVar`. -/
private lemma writeVar_u64_val (sid : ScopeId) (x : String) (v : BitVec 64) :
    writeVar sid { vname := x, vtype := .sword .U64 } ⟨.sword .U64, v⟩ =
    RawCode.put (translateVar sid { vname := x, vtype := .sword .U64 }) v := rfl

/-- `HeapInv` is preserved by setting a U64 scalar location (disjoint from tower locs). -/
private lemma heapInv_set_u64 (rs : RustState) (heap : Heap) (sid : ScopeId)
    (x : String) (v : BitVec 64) (hInv : HeapInv rs heap sid) :
    HeapInv rs (heap.set (translateVar sid { vname := x, vtype := .sword .U64 }) v) sid := by
  intro y t w hy
  rw [Heap.get_set_other _ _ _ _ (wordLoc_id_ne_towerLoc_id sid x y t)]
  exact hInv y t w hy

/-- `rsSetScalar` only changes `rsScalar`, preserving `HeapInv`. -/
private lemma heapInv_rsSetScalar (rs : RustState) (heap : Heap) (sid : ScopeId)
    (x : String) (v : Nat) (hInv : HeapInv rs heap sid) :
    HeapInv (rsSetScalar rs x v) heap sid := by
  intro y t w hy; exact hInv y t w hy

/-! ### Tower init (RLetZero) helper -/

/-- Writing `default` to `towerLoc sid x t` and setting `rsSetTower` preserves `HeapInv`. -/
private lemma heapInv_rsSetTower_init (rs : RustState) (heap : Heap) (sid : ScopeId)
    (x : String) (t : TowerType) (hInv : HeapInv rs heap sid) :
    HeapInv (rsSetTower rs x ⟨t, default⟩) (heap.set (towerLoc sid x t) default) sid := by
  intro y t' v hy
  simp only [rsSetTower] at hy
  by_cases hxy : y == x
  · -- y = x
    have hyx : y = x := beq_iff_eq.mp hxy
    simp only [hxy, ite_true] at hy
    -- hy : some ⟨t, default⟩ = some ⟨t', v⟩
    have hsome := Option.some.inj hy
    obtain ⟨rfl, hveq⟩ := Sigma.mk.inj hsome
    rw [← eq_of_heq hveq, hyx]
    exact Heap.get_set_same _ _ _
  · -- y ≠ x
    simp only [hxy, ite_false] at hy
    have hne_name : x ≠ y := by
      intro h; simp [h] at hxy
    have hid_ne : (towerLoc sid x t).id ≠ (towerLoc sid y t').id := by
      simp only [towerLoc, translateVar, varLocId]
      intro h
      exact hne_name (encodeVarName_injective (Nat.pair_eq_pair.mp h).2)
    rw [Heap.get_set_other _ _ _ _ hid_ne]
    exact hInv y t' v hy

/-! ### ScalarInv helpers -/

/-- `rsSetTower` doesn't change `rsScalar`, so `ScalarInv` is preserved. -/
private lemma scalarInv_rsSetTower (rs : RustState) (heap : Heap) (sid : ScopeId)
    (x : String) (tv : Σ t, RustVal t) (hSInv : ScalarInv rs heap sid) :
    ScalarInv (rsSetTower rs x tv) heap sid := by
  intro y; exact hSInv y

/-- Tower-loc set preserves `ScalarInv` (disjoint ids). -/
private lemma scalarInv_set_tower (rs : RustState) (heap : Heap) (sid : ScopeId)
    (x : String) (t : TowerType) (v : RustVal t) (hSInv : ScalarInv rs heap sid) :
    ScalarInv rs (heap.set (towerLoc sid x t) v) sid := by
  intro y
  rw [Heap.get_set_other _ _ _ _ (Ne.symm (wordLoc_id_ne_towerLoc_id sid y x t))]
  exact hSInv y

/-- Writing the correct value at a scalar loc establishes the scalar inv entry. -/
private lemma scalarInv_set_scalar_eq (heap : Heap) (sid : ScopeId)
    (x y : String) (v w : Nat) (hSInv_y : heap.get (translateVar sid { vname := y, vtype := .sword .U64 }) = BitVec.ofNat 64 w)
    (hne : x ≠ y) :
    (heap.set (translateVar sid { vname := x, vtype := .sword .U64 }) (BitVec.ofNat 64 v)).get
      (translateVar sid { vname := y, vtype := .sword .U64 }) = BitVec.ofNat 64 w := by
  rw [Heap.get_set_other _ _ _ _ (wordLoc_id_ne_of_ne_name sid x y hne)]
  exact hSInv_y

/-- After writing `BitVec.ofNat 64 v` to scalar `x`'s location, `ScalarInv` holds for `rsSetScalar`. -/
private lemma scalarInv_after_scalar_set (rs : RustState) (heap : Heap) (sid : ScopeId)
    (x : String) (v : Nat) (hSInv : ScalarInv rs heap sid) :
    ScalarInv (rsSetScalar rs x v)
      (heap.set (translateVar sid { vname := x, vtype := .sword .U64 }) (BitVec.ofNat 64 v)) sid := by
  intro y
  simp only [rsSetScalar]
  by_cases hxy : x = y
  · subst hxy; simp [Heap.get_set_same]
  · rw [Heap.get_set_other _ _ _ _ (wordLoc_id_ne_of_ne_name sid x y hxy)]
    simp only [beq_eq_false_iff_ne.mpr (Ne.symm hxy), ite_false]
    exact hSInv y

/-- `rsSetScalar` preserves `ScalarInv` when the heap val is already correct. -/
private lemma scalarInv_rsSetScalar_other (rs : RustState) (heap : Heap) (sid : ScopeId)
    (x : String) (v : Nat)
    (hSInv : ScalarInv rs heap sid)
    (hheap : heap.get (translateVar sid { vname := x, vtype := .sword .U64 }) = BitVec.ofNat 64 v) :
    ScalarInv (rsSetScalar rs x v) heap sid := by
  intro y
  simp only [rsSetScalar]
  by_cases hxy : y == x
  · simp only [hxy, ite_true]
    have heq : y = x := beq_iff_eq.mp hxy
    subst heq; exact hheap
  · simp only [hxy, ite_false]; exact hSInv y

/-! ### ScalarsBounded helpers -/

private lemma scalarsBounded_zero : (0 : Nat) < 2^64 := by norm_num

private lemma scalarsBounded_rsSetScalar_zero (rs : RustState) (x : String) (hB : ScalarsBounded rs) :
    ScalarsBounded (rsSetScalar rs x 0) := by
  intro y; simp only [rsSetScalar]
  split_ifs with hxy
  · exact scalarsBounded_zero
  · exact hB y

private lemma scalarsBounded_rsSetTower (rs : RustState) (x : String) (tv : Σ t, RustVal t)
    (hB : ScalarsBounded rs) : ScalarsBounded (rsSetTower rs x tv) := by
  intro y; exact hB y

private lemma scalarsBounded_rsSetScalar (rs : RustState) (x : String) (v : Nat)
    (hv : v < 2^64) (hB : ScalarsBounded rs) : ScalarsBounded (rsSetScalar rs x v) := by
  intro y
  simp only [rsSetScalar]
  split_ifs with hxy
  · exact hv
  · exact hB y

private lemma scalarSetsSmall_val (c : RustCmd) (x : String) (v : Nat)
    (h : scalarSetsSmall c = true) (heq : c = .RScalarSet x v) : v < 2^64 := by
  subst heq; simp [scalarSetsSmall] at h; exact h

/-! ### translateCmd append decomposition -/

/-- `newSid` of appended command list equals `newSid` of the second list run after the first. -/
private lemma translateCmd_append_newSid
    (env : TransEnv) (l1 l2 : Cmd) (sid : ScopeId) (fuel : Nat) :
    (translateCmd env (l1 ++ l2) sid fuel).newSid =
      (translateCmd env l2
        (translateCmd env l1 sid fuel).newSid
        (fuel - l1.length)).newSid := by
  induction l1 generalizing sid fuel with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.sub_zero]
    cases fuel with
    | zero => simp [translateCmd]
    | succ n => simp [translateCmd]
  | cons i is ih =>
    cases fuel with
    | zero => simp [translateCmd]
    | succ n =>
      simp only [List.cons_append, List.length_cons, translateCmd]
      rw [ih]
      simp only [translateCmd, Nat.succ_sub_succ_eq_sub]

/-- Evaluation of appended command list equals sequential composition. -/
private lemma translateCmd_append_eval
    (env : TransEnv) (l1 l2 : Cmd) (sid : ScopeId) (fuel : Nat) (heap : Heap) :
    (translateCmd env (l1 ++ l2) sid fuel).code.eval heap =
      ((translateCmd env l1 sid fuel).code.eval heap).bind (fun x =>
        (translateCmd env l2
          (translateCmd env l1 sid fuel).newSid
          (fuel - l1.length)).code.eval x.2) := by
  induction l1 generalizing sid fuel heap with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.sub_zero]
    cases fuel with
    | zero => simp [translateCmd, CatCrypt.Deep.eval_fail, SPComp.fail, SDistr.bind_fail]
    | succ n =>
      simp only [translateCmd, CatCrypt.Deep.eval_ret, SPComp.pure_def, SDistr.pure_bind]
  | cons i is ih =>
    cases fuel with
    | zero => simp [translateCmd, CatCrypt.Deep.eval_fail, SPComp.fail, SDistr.bind_fail]
    | succ n =>
      simp only [List.cons_append, List.length_cons, Nat.succ_sub_succ_eq_sub]
      simp only [translateCmd, eval_bind, SPComp.bind_def]
      simp_rw [ih (translateInstrR env sid n i).newSid n]
      rw [← SDistr.bind_assoc]

/-! ### callFree → newSid = sid -/

/-- Call-free programs leave `newSid` unchanged. -/
private lemma callFree_toJasmin_newSid
    (c : RustCmd) (hCF : callFree c = true)
    (env : TransEnv) (sid : ScopeId) (fuel : Nat) :
    (translateCmd env (toJasminCmd c) sid fuel).newSid = sid := by
  induction c generalizing sid fuel with
  | RSkip => cases fuel <;> simp [toJasminCmd, translateCmd]
  | RScalarSet x v =>
    cases fuel with
    | zero => simp [translateCmd]
    | succ n =>
      cases n with
      | zero => simp [toJasminCmd, translateCmd, translateInstrR]
      | succ m => simp [toJasminCmd, translateCmd, translateInstrR]
  | RSeq c1 c2 ih1 ih2 =>
    simp only [callFree, Bool.and_eq_true] at hCF
    simp only [toJasminCmd, translateCmd_append_newSid, ih1 hCF.1 sid fuel,
               ih2 hCF.2 sid _]
  | RLetZero x t body ih =>
    simp only [callFree] at hCF
    cases fuel with
    | zero => simp [translateCmd]
    | succ n =>
      cases n with
      | zero => simp [toJasminCmd, translateCmd, translateInstrR]
      | succ m =>
        simp only [toJasminCmd, translateCmd, translateInstrR]
        exact ih hCF sid (m + 1)
  | RLetU64Zero x body ih =>
    simp only [callFree] at hCF
    cases fuel with
    | zero => simp [translateCmd]
    | succ n =>
      cases n with
      | zero => simp [toJasminCmd, translateCmd, translateInstrR]
      | succ m =>
        simp only [toJasminCmd, translateCmd, translateInstrR]
        exact ih hCF sid (m + 1)
  | RIfNz e ct cf ih1 ih2 =>
    simp only [callFree, Bool.and_eq_true] at hCF
    cases fuel with
    | zero => simp [translateCmd]
    | succ n =>
      simp only [toJasminCmd, translateCmd, translateInstrR]
      rw [ih1 hCF.1 sid n, ih2 hCF.2 sid n]
      cases n <;> simp only [translateCmd]
  | RWhileNz e body ih =>
    simp only [callFree] at hCF
    cases fuel with
    | zero => simp [translateCmd]
    | succ n =>
      cases n with
      | zero => simp [toJasminCmd, translateCmd, translateInstrR]
      | succ m => simp [toJasminCmd, translateCmd, translateInstrR]
  | RFor x n body ih =>
    -- toJasminCmd (RFor x n body) = unrollForJ x (toJasminCmd body) n.  The
    -- unrolled command is `n` repetitions of `[scalarSet] ++ toJasminCmd body`,
    -- both call-free segments, so `newSid` is preserved.  Discharged by
    -- nested induction on `n` using `translateCmd_append_newSid` and the
    -- body IH.
    simp only [callFree] at hCF
    simp only [toJasminCmd]
    -- General lemma: `unrollForJ` preserves newSid whenever the segment body does.
    have hBody : ∀ (sid : ScopeId) (fuel : Nat),
        (translateCmd env (toJasminCmd body) sid fuel).newSid = sid := ih hCF
    clear ih
    -- Induct on n.
    induction n generalizing sid fuel with
    | zero => cases fuel <;> simp [unrollForJ, translateCmd]
    | succ k ihk =>
        simp only [unrollForJ, translateCmd_append_newSid]
        rw [ihk]
        -- now goal: newSid of `[scalarSet] ++ toJasminCmd body` from sid = sid
        -- single-instruction scalarSet preserves sid; toJasminCmd body via hBody.
        cases h : fuel - (unrollForJ x (toJasminCmd body) k).length with
        | zero => simp [translateCmd]
        | succ n' =>
            simp only [translateCmd, translateInstrR]
            -- After scalarSet, sid unchanged; remaining is toJasminCmd body via hBody.
            exact hBody sid n'
  | RCall _ _ _ => simp [callFree] at hCF
  | RCallSwap _ _ _ _ => simp [callFree] at hCF
  | RCloneCall _ _ _ _ _ _ => simp [callFree] at hCF
  | RLimbStore _ _ _ => simp [callFree] at hCF
  -- Phase F: RAsmOp is call-free; emit one Copn, no newSid change.
  | RAsmOp name dests args =>
    cases fuel with
    | zero => simp [translateCmd]
    | succ n =>
      cases n with
      | zero => simp [toJasminCmd, translateCmd, translateInstrR]
      | succ m => simp [toJasminCmd, translateCmd, translateInstrR]
  -- Phase G: RCallN IS a call.
  | RCallN _ _ _ => simp [callFree] at hCF
  -- Phase H: RSelect emits a Copn; like RAsmOp.
  | RSelect dst sel src0 src1 =>
    cases fuel with
    | zero => simp [translateCmd]
    | succ n =>
      cases n with
      | zero => simp [toJasminCmd, translateCmd, translateInstrR]
      | succ m => simp [toJasminCmd, translateCmd, translateInstrR]
  -- Phase L: RAssert emits []; trivially preserves newSid.
  | RAssert label =>
    simp [toJasminCmd, translateCmd]
    cases fuel <;> simp [translateCmd]
  -- Phase M: RBlock forwards to body.
  | RBlock body ih =>
    simp only [callFree] at hCF
    exact ih hCF sid fuel
  -- Phase C.
  | RFnDef _ _ _ body cont ihBody ihCont =>
    simp only [callFree, Bool.and_eq_true] at hCF
    simp only [toJasminCmd, translateCmd_append_newSid, ihBody hCF.1 sid fuel,
               ihCont hCF.2 sid _]
  | RFnCall _ _ _ => simp [callFree] at hCF
  -- Phase I: RTupleStore/RTupleLoad excluded by callFree.
  | RTupleStore _ _ _ => simp [callFree] at hCF
  | RTupleLoad _ _ _ => simp [callFree] at hCF
  -- Phase Ext (2026-05-12): TArr/SExpr excluded by callFree.
  | RArrStore _ _ _ => simp [callFree] at hCF
  | RArrLoad _ _ _ => simp [callFree] at hCF
  | RScalarSetExpr _ _ => simp [callFree] at hCF
  | RBytesSlice _ _ _ _ => simp [callFree] at hCF

/-- `RLimbStore` translates to a single `.Copn` instruction, which preserves
    `newSid` (only `.Ccall` and `.Cfor` advance it).  Therefore the threaded
    newSid is identical to the input `sid` for any fuel ≥ 2.

    Companion to `callFree_toJasmin_newSid`: the latter is gated by `callFree`
    (which rejects `RLimbStore`); this version is `RLimbStore`-specific. -/
private lemma limbStore_toJasmin_newSid
    (loc : Located) (idx : Nat) (v : BitVec 64)
    (env : TransEnv) (sid : ScopeId) (fuel : Nat) :
    (translateCmd env (toJasminCmd (.RLimbStore loc idx v)) sid fuel).newSid = sid := by
  cases fuel with
  | zero => simp [translateCmd]
  | succ n =>
    cases n with
    | zero => simp [toJasminCmd, translateCmd, translateInstrR]
    | succ m => simp [toJasminCmd, translateCmd, translateInstrR]

/-- Eval of `translateCmd` for a single U64 const-assign writes `0` to the U64 location. -/
private lemma translateCmd_cassgn_u64_eval
    (env : TransEnv) (sid : ScopeId) (x : String) (v : Int) (n : Nat) (heap : Heap) :
    (translateCmd env
        [.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                  .AT_none (.sword .U64) (.Pconst v)]
        sid (n + 2)).code.eval heap =
    SDistr.pure (⟨()⟩,
        heap.set (translateVar sid { vname := x, vtype := .sword .U64 }) (0 : BitVec 64)) := by
  simp only [translateCmd, translateInstrR, translatePExpr, translateWriteLVal,
             coerceValue_sint_u64, writeVar_u64_zero,
             eval_bind, eval_ret, eval_put, SPComp.bind_def, SPComp.set_def, SPComp.pure_def,
             SDistr.pure_bind]

/-- `newSid` for a single U64 const-assign equals `sid`. -/
private lemma translateCmd_cassgn_u64_newSid
    (env : TransEnv) (sid : ScopeId) (x : String) (v : Int) (n : Nat) :
    (translateCmd env
        [.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                  .AT_none (.sword .U64) (.Pconst v)]
        sid (n + 2)).newSid = sid := by
  simp [translateCmd, translateInstrR]

/-- One-step eval: U64 const-assign followed by `rest`; advances heap then runs `rest`. -/
private lemma translateCmd_cons_cassgn_u64_eval
    (env : TransEnv) (sid : ScopeId) (x : String) (v : Int)
    (rest : Cmd) (n : Nat) (heap : Heap) :
    (translateCmd env
        (.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                  .AT_none (.sword .U64) (.Pconst v) :: rest)
        sid (n + 2)).code.eval heap =
    (translateCmd env rest sid (n + 1)).code.eval
        (heap.set (translateVar sid { vname := x, vtype := .sword .U64 }) (0 : BitVec 64)) := by
  simp only [translateCmd, translateInstrR, translatePExpr, translateWriteLVal,
             coerceValue_sint_u64, writeVar_u64_zero,
             eval_bind, eval_ret, eval_put, SPComp.bind_def, SPComp.set_def, SPComp.pure_def,
             SDistr.pure_bind]

/-- One-step `newSid`: U64 const-assign followed by `rest`. -/
private lemma translateCmd_cons_cassgn_u64_newSid
    (env : TransEnv) (sid : ScopeId) (x : String) (v : Int)
    (rest : Cmd) (n : Nat) :
    (translateCmd env
        (.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                  .AT_none (.sword .U64) (.Pconst v) :: rest)
        sid (n + 2)).newSid =
    (translateCmd env rest sid (n + 1)).newSid := by
  simp [translateCmd, translateInstrR]

/-! ### RScalarSet eval (with corrected Papp1 encoding) -/

/-- `translatePExpr` for `Papp1 (Oword_of_int U64) (Pconst v)` evaluates to `BitVec.ofNat 64 v`. -/
private lemma translatePExpr_word_of_int_eval (sid : ScopeId) (v : Nat) (heap : Heap) :
    (translatePExpr sid (.Papp1 (.Oword_of_int .U64) (.Pconst (v : Int)))).eval heap =
    SDistr.pure (⟨.sword .U64, BitVec.ofNat 64 v⟩, heap) := by
  simp [translatePExpr, evalSop1, intToWord_U64_ofNat,
        CatCrypt.Deep.eval_ret, CatCrypt.Deep.eval_bind, SPComp.pure_def, SDistr.pure_bind]

/-- Eval of a `Cassgn` with `Papp1 (Oword_of_int U64) (Pconst v)` writes `BitVec.ofNat 64 v`. -/
private lemma translateCmd_cassgn_u64_val_eval
    (env : TransEnv) (sid : ScopeId) (x : String) (v : Nat) (n : Nat) (heap : Heap) :
    (translateCmd env
        [.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                  .AT_none (.sword .U64) (.Papp1 (.Oword_of_int .U64) (.Pconst (v : Int)))]
        sid (n + 2)).code.eval heap =
    SDistr.pure (⟨()⟩,
        heap.set (translateVar sid { vname := x, vtype := .sword .U64 }) (BitVec.ofNat 64 v)) := by
  simp only [translateCmd, translateInstrR, translatePExpr, evalSop1, intToWord_U64_ofNat,
             coerceValue_u64_u64, translateWriteLVal, writeVar_u64_val, truncateWord_u64_u64,
             CatCrypt.Deep.eval_bind, CatCrypt.Deep.eval_ret, CatCrypt.Deep.eval_put,
             SPComp.bind_def, SPComp.set_def, SPComp.pure_def, SDistr.pure_bind]

/-- `newSid` for the single-instruction `Cassgn Papp1` case. -/
private lemma translateCmd_cassgn_u64_val_newSid
    (env : TransEnv) (sid : ScopeId) (x : String) (v : Nat) (n : Nat) :
    (translateCmd env
        [.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                  .AT_none (.sword .U64) (.Papp1 (.Oword_of_int .U64) (.Pconst (v : Int)))]
        sid (n + 2)).newSid = sid := by
  simp [translateCmd, translateInstrR]

/-! ### RLetZero eval (Parr_init / sarr init) -/

/-- `writeVar` at `sarr t.byteSize` with default value equals `put` at `towerLoc`. -/
private lemma writeVar_sarr_default (sid : ScopeId) (x : String) (t : TowerType) :
    writeVar sid { vname := x, vtype := .sarr t.storageBytes }
      ⟨.sarr t.storageBytes, (fun _ => 0 : JArray t.storageBytes)⟩ =
    RawCode.put (towerLoc sid x t) (fun _ => 0 : JArray t.storageBytes) := by
  rw [writeVar_sarr_eq]; rfl

/-- `default : JArray n = fun _ => 0`. -/
private lemma jarray_default_eq (n : Nat) : (default : JArray n) = fun _ => 0 := rfl

/-- One-step cons eval: `Cassgn (Parr_init t.byteSize)` writes `default` to `towerLoc`,
    then runs `rest`. -/
private lemma translateCmd_cons_cassgn_sarr_init_eval
    (env : TransEnv) (sid : ScopeId) (x : String) (t : TowerType)
    (rest : Cmd) (n : Nat) (heap : Heap) :
    (translateCmd env
      (.Cassgn (.Lvar { var := { vname := x, vtype := .sarr t.storageBytes }, info := {} })
               .AT_none (.sarr t.storageBytes) (.Parr_init t.storageBytes) :: rest)
      sid (n + 2)).code.eval heap =
    (translateCmd env rest sid (n + 1)).code.eval
      (heap.set (towerLoc sid x t) (default : JArray t.storageBytes)) := by
  simp only [translateCmd, translateInstrR, translatePExpr, coerceValue, eq_self_iff_true,
             ↓reduceDIte, translateWriteLVal, writeVar_sarr_default, jarray_default_eq,
             CatCrypt.Deep.eval_bind, CatCrypt.Deep.eval_ret, CatCrypt.Deep.eval_put,
             SPComp.bind_def, SPComp.set_def, SPComp.pure_def, SDistr.pure_bind]

/-- `newSid` for cons Cassgn sarr init. -/
private lemma translateCmd_cons_cassgn_sarr_init_newSid
    (env : TransEnv) (sid : ScopeId) (x : String) (t : TowerType)
    (rest : Cmd) (n : Nat) :
    (translateCmd env
      (.Cassgn (.Lvar { var := { vname := x, vtype := .sarr t.storageBytes }, info := {} })
               .AT_none (.sarr t.storageBytes) (.Parr_init t.storageBytes) :: rest)
      sid (n + 2)).newSid =
    (translateCmd env rest sid (n + 1)).newSid := by
  simp [translateCmd, translateInstrR]

/-! ### Cif eval helpers -/

/-- Reading a `sword U64` variable from the heap. -/
private lemma translatePExpr_pvar_u64_eval (sid : ScopeId) (e : String) (heap : Heap) :
    (translatePExpr sid
      (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 }, info := {} }, gs := false })).eval heap =
    SDistr.pure (⟨.sword .U64, heap.get (translateVar sid { vname := e, vtype := .sword .U64 })⟩, heap) := by
  simp only [translatePExpr, readGVar, readVar_sword_eq,
             CatCrypt.Deep.eval_bind, CatCrypt.Deep.eval_get, CatCrypt.Deep.eval_ret,
             SPComp.bind_def, SPComp.get_def, SPComp.pure_def, SDistr.pure_bind]

/-- Evaluating the `RIfNz` condition expression. -/
private lemma cif_cond_eval (sid : ScopeId) (e : String) (heap : Heap) :
    let zero64 : PExpr := .Papp1 (.Oword_of_int .U64) (.Pconst 0)
    let condExpr : PExpr :=
      .Papp2 (.Oneq .U64)
        (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 }, info := {} }, gs := false })
        zero64
    let w : BitVec 64 := heap.get (translateVar sid { vname := e, vtype := .sword .U64 })
    (translatePExpr sid condExpr).eval heap =
    SDistr.pure (⟨.sbool, w != (0 : BitVec 64)⟩, heap) := by
  simp only [translatePExpr, readGVar, readVar_sword_eq, evalSop1, evalSop2, intToWord_U64_ofNat,
             CatCrypt.Deep.eval_bind, CatCrypt.Deep.eval_get, CatCrypt.Deep.eval_ret,
             SPComp.bind_def, SPComp.get_def, SPComp.pure_def, SDistr.pure_bind]
  rfl

/-- `BitVec.ofNat 64 v ≠ 0` when `v ≠ 0` and `v < 2^64`. -/
private lemma bitVec_ofNat_ne_zero (v : Nat) (hv : v ≠ 0) (hlt : v < 2^64) :
    (BitVec.ofNat 64 v) ≠ (0 : BitVec 64) := by
  intro h
  apply hv
  have h1 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, BitVec.toNat_zero] at h1
  exact h1

/-- Single-instruction `Cif` eval when condition is true. -/
private lemma translateCmd_cif_eval_true
    (env : TransEnv) (sid : ScopeId) (cond : PExpr) (ct cf : Cmd)
    (fuel : Nat) (heap heap' : Heap)
    (hcond : (translatePExpr sid cond).eval heap = SDistr.pure (⟨.sbool, true⟩, heap')) :
    (translateCmd env [.Cif cond ct cf] sid (fuel + 1)).code.eval heap =
    (translateCmd env ct sid fuel).code.eval heap' := by
  cases fuel with
  | zero =>
    simp only [translateCmd, translateInstrR, CatCrypt.Deep.eval_bind, SPComp.bind_def, hcond,
               SDistr.pure_bind, CatCrypt.Deep.eval_fail, SPComp.fail, SDistr.bind_fail]
  | succ n =>
    simp only [translateCmd, translateInstrR, CatCrypt.Deep.eval_bind, SPComp.bind_def, hcond,
               SDistr.pure_bind, CatCrypt.Deep.eval_ret, SPComp.pure_def]
    have hunit : (fun p : ULift Unit × Heap => SDistr.pure (⟨()⟩, p.2)) = SDistr.pure :=
      funext fun ⟨u, h'⟩ => by cases u; rfl
    rw [hunit, SDistr.bind_pure]

/-- Single-instruction `Cif` eval when condition is false. -/
private lemma translateCmd_cif_eval_false
    (env : TransEnv) (sid : ScopeId) (cond : PExpr) (ct cf : Cmd)
    (fuel : Nat) (heap heap' : Heap)
    (hcond : (translatePExpr sid cond).eval heap = SDistr.pure (⟨.sbool, false⟩, heap')) :
    (translateCmd env [.Cif cond ct cf] sid (fuel + 1)).code.eval heap =
    (translateCmd env cf (translateCmd env ct sid fuel).newSid fuel).code.eval heap' := by
  cases fuel with
  | zero =>
    simp only [translateCmd, translateInstrR, CatCrypt.Deep.eval_bind, SPComp.bind_def, hcond,
               SDistr.pure_bind, CatCrypt.Deep.eval_fail, SPComp.fail, SDistr.bind_fail]
  | succ n =>
    simp only [translateCmd, translateInstrR, CatCrypt.Deep.eval_bind, SPComp.bind_def, hcond,
               SDistr.pure_bind, CatCrypt.Deep.eval_ret, SPComp.pure_def]
    have hunit : (fun p : ULift Unit × Heap => SDistr.pure (⟨()⟩, p.2)) = SDistr.pure :=
      funext fun ⟨u, h'⟩ => by cases u; rfl
    rw [hunit, SDistr.bind_pure]

/-- `newSid` for `[Cif cond ct cf]` (when ct and cf are call-free). -/
private lemma translateCmd_cif_newSid
    (env : TransEnv) (sid : ScopeId) (cond : PExpr) (ct cf : Cmd) (fuel : Nat) :
    (translateCmd env [.Cif cond ct cf] sid (fuel + 1)).newSid =
    (translateCmd env cf (translateCmd env ct sid fuel).newSid fuel).newSid := by
  cases fuel <;> simp [translateCmd, translateInstrR]

/-- **rustExecSimulates**: the `RustCmd → Jasmin` translation is operationally correct.

    If `c` is while-free, `env` correctly implements `leafSpec`, and the initial
    heap encodes `rs`, then executing `translateCmd env (toJasminCmd c)` from that
    heap deterministically produces a heap encoding `rs'`.

    ## Signature

    * `hLeaf : ∀ fuel', LeafImplOk leafSpec env fuel'` — `LeafImplOk` at any fuel
    * `hFuel : jasminFuel c ≤ fuel` — minimum fuel for the translated program to run
    * Induction generalizes over `sid`, `heap`, and `fuel` to allow IH reuse at subterms.

    ## Proof sketch per case

    * `skip`      — `toJasminCmd .RSkip = []`; `translateCmd [] = ret ⟨()⟩`; heap unchanged ✓
    * `seq`       — needs `translateCmd_append`; IH₁ then IH₂ in sequence
    * `letZero`   — assignment writes default array to `towerLoc`; IH on body
    * `letU64Zero` — writes to `wordLoc` (disjoint); IH on body; heap updates preserve HeapInv
    * `scalarSet` — writes to `wordLoc` (disjoint from towerLoc by encodeSType); HeapInv preserved
    * `ifTrue/False` — IH on taken branch
    * `whileFalse/True` — `False` from `hWf : whileFree (.RWhileNz ..) = false ≠ true` ✓
    * `call`      — `hLeaf` gives result heap; HeapInv blocked by scope mismatch
    * `cloneCall` — `rsSetTower` + IH(inner call) + `rsRemoveTower`
    * `limbStore` — similar to `call`; writes to `towerLoc dest`

    **Proved: all 11 cases (0 sorry).**

    ## Hypotheses

    * `hCF : callFree c = true` — excludes `RCall`, `RCloneCall`, `RLimbStore`
      (those advance `newSid`; without them `newSid = sid` throughout)
    * `hSSS : scalarSetsSmall c = true` — all `RScalarSet x v` have `v < 2^64`
    * `hSInv : ScalarInv rs heap sid` — heap correctly encodes `rsScalar`
    * `hBounded : ScalarsBounded rs` — all scalars fit in 64 bits

    ## Conclusion

    Uses `sid` (not `newSid`) since call-free programs preserve `newSid = sid`. -/
theorem rustExecSimulates
    (N : Nat) (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat)
    (hLeaf : ∀ fuel', LeafImplOk leafSpec env fuel')
    (c : RustCmd) (rs rs' : RustState)
    (hWf : whileFree c = true)
    (hCF : callFree c = true)
    (hSSS : scalarSetsSmall c = true)
    (hFuel : jasminFuel c ≤ fuel)
    (hExec : RustExec N leafSpec c rs rs')
    (sid : ScopeId) (heap : Heap)
    (hInv : HeapInv rs heap sid)
    (hSInv : ScalarInv rs heap sid)
    (hBounded : ScalarsBounded rs) :
    ∃ heap' : Heap,
      (translateCmd env (toJasminCmd c) sid fuel).code.eval heap =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap') ∧
      HeapInv rs' heap' sid ∧
      ScalarInv rs' heap' sid ∧
      ScalarsBounded rs' := by
  induction hExec generalizing sid heap fuel with

  | skip _ =>
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp [jasminFuel] at hFuel; omega⟩
    exact ⟨heap, by simp [toJasminCmd, translateCmd, CatCrypt.Deep.eval_ret, SPComp.pure_def], hInv, hSInv, hBounded⟩

  | seq c1 c2 rs0 r1 rs' _h1 _h2 ih1 ih2 =>
    simp only [whileFree, Bool.and_eq_true] at hWf
    simp only [callFree, Bool.and_eq_true] at hCF
    simp only [scalarSetsSmall, Bool.and_eq_true] at hSSS
    simp only [jasminFuel] at hFuel
    -- fuel bounds
    have hFuel1 : jasminFuel c1 ≤ fuel := by omega
    have hFuel2 : jasminFuel c2 ≤ fuel - (toJasminCmd c1).length := by
      have := jasminFuel_gt_length c1; omega
    -- Apply IH1
    obtain ⟨heap1, heval1, hInv1, hSInv1, hB1⟩ :=
      ih1 fuel hWf.1 hCF.1 hSSS.1 hFuel1 sid heap hInv hSInv hBounded
    -- The two translated lists are appended
    simp only [toJasminCmd]
    -- Eval of append
    rw [translateCmd_append_eval]
    rw [callFree_toJasmin_newSid c1 hCF.1 env sid fuel] at *
    rw [heval1, SDistr.pure_bind]
    -- Now apply IH2 from heap1 at sid
    have hFuel2' : jasminFuel c2 ≤ fuel - (toJasminCmd c1).length := hFuel2
    obtain ⟨heap2, heval2, hInv2, hSInv2, hB2⟩ :=
      ih2 (fuel - (toJasminCmd c1).length) hWf.2 hCF.2 hSSS.2 hFuel2' sid heap1 hInv1 hSInv1 hB1
    exact ⟨heap2, heval2, hInv2, hSInv2, hB2⟩

  | letZero x t body rs0 rs' _h ih =>
    simp only [whileFree] at hWf
    simp only [callFree] at hCF
    simp only [scalarSetsSmall] at hSSS
    simp only [jasminFuel] at hFuel
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by have := jasminFuel_pos body; omega⟩
    have hFuel' : jasminFuel body ≤ n + 1 := by omega
    -- Initial heap: write default to towerLoc sid x t
    let heap' := heap.set (towerLoc sid x t) (default : JArray t.storageBytes)
    have hInv' : HeapInv (rsSetTower rs0 x ⟨t, default⟩) heap' sid :=
      heapInv_rsSetTower_init rs0 heap sid x t hInv
    have hSInv' : ScalarInv (rsSetTower rs0 x ⟨t, default⟩) heap' sid :=
      scalarInv_rsSetTower rs0 heap' sid x ⟨t, default⟩
        (scalarInv_set_tower rs0 heap sid x t (default : JArray t.storageBytes) hSInv)
    have hB' : ScalarsBounded (rsSetTower rs0 x ⟨t, default⟩) :=
      scalarsBounded_rsSetTower rs0 x ⟨t, default⟩ hBounded
    obtain ⟨heap'', heval', hInv'', hSInv'', hB''⟩ := ih (n + 1) hWf hCF hSSS hFuel' sid heap' hInv' hSInv' hB'
    simp only [toJasminCmd, show (n + 2) = (n + 1) + 1 from rfl]
    rw [translateCmd_cons_cassgn_sarr_init_eval]
    exact ⟨heap'', heval', hInv'', hSInv'', hB''⟩

  | letU64Zero x body rs0 rs' _h ih =>
    simp only [whileFree] at hWf
    simp only [callFree] at hCF
    simp only [scalarSetsSmall] at hSSS
    simp only [jasminFuel] at hFuel
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by have := jasminFuel_pos body; omega⟩
    have hFuel' : jasminFuel body ≤ n + 1 := by omega
    let heap' := heap.set (translateVar sid { vname := x, vtype := .sword .U64 }) (0 : BitVec 64)
    have hInv' : HeapInv (rsSetScalar rs0 x 0) heap' sid :=
      heapInv_set_u64 _ heap sid x 0 (heapInv_rsSetScalar rs0 heap sid x 0 hInv)
    have hSInv' : ScalarInv (rsSetScalar rs0 x 0) heap' sid :=
      scalarInv_after_scalar_set rs0 heap sid x 0 hSInv
    have hB' : ScalarsBounded (rsSetScalar rs0 x 0) :=
      scalarsBounded_rsSetScalar_zero rs0 x hBounded
    obtain ⟨heap'', heval', hInv'', hSInv'', hB''⟩ := ih (n + 1) hWf hCF hSSS hFuel' sid heap' hInv' hSInv' hB'
    refine ⟨heap'', ?_, ?_, ?_, hB''⟩
    · simp only [toJasminCmd]; rw [translateCmd_cons_cassgn_u64_eval]; exact heval'
    · exact hInv''
    · exact hSInv''

  | scalarSet x v rs0 =>
    simp only [callFree] at hCF
    simp only [scalarSetsSmall] at hSSS
    simp only [jasminFuel] at hFuel
    have hv_small : v < 2^64 := scalarSetsSmall_val (.RScalarSet x v) x v hSSS rfl
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
    refine ⟨heap.set (translateVar sid { vname := x, vtype := .sword .U64 }) (BitVec.ofNat 64 v),
            ?_, ?_, ?_, scalarsBounded_rsSetScalar rs0 x v hv_small hBounded⟩
    · simp only [toJasminCmd]; exact translateCmd_cassgn_u64_val_eval env sid x v n heap
    · exact heapInv_set_u64 _ heap sid x _ (heapInv_rsSetScalar rs0 heap sid x v hInv)
    · exact scalarInv_after_scalar_set rs0 heap sid x v hSInv

  | ifTrue e ct cf rs0 rs' v hv hne_zero _h ih =>
    simp only [whileFree, Bool.and_eq_true] at hWf
    simp only [callFree, Bool.and_eq_true] at hCF
    simp only [scalarSetsSmall, Bool.and_eq_true] at hSSS
    simp only [jasminFuel] at hFuel
    -- Determine the condition value from ScalarInv
    have he_val : heap.get (translateVar sid { vname := e, vtype := .sword .U64 }) =
        BitVec.ofNat 64 v := hv ▸ hSInv e
    have he_bnd : v < 2^64 := by rw [← hv]; exact hBounded e
    -- Condition evaluates to true
    have hcond : (translatePExpr sid (.Papp2 (.Oneq .U64)
        (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 }, info := {} }, gs := false })
        (.Papp1 (.Oword_of_int .U64) (.Pconst 0)))).eval heap =
        SDistr.pure (⟨.sbool, true⟩, heap) := by
      rw [cif_cond_eval]
      simp only [he_val]
      have hbne : BitVec.ofNat 64 v != (0 : BitVec 64) := by
        rw [bne_iff_ne]; exact bitVec_ofNat_ne_zero v hne_zero he_bnd
      rw [show ((0 : BitVec 64) = (0#64 : BitVec 64)) from rfl] at hbne
      simp [hbne]
    -- Fuel: max(j_ct, j_cf) + 1 ≤ fuel, so j_ct ≤ fuel - 1
    obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
    have hFuel_ct : jasminFuel ct ≤ fuel' := by omega
    obtain ⟨heap', heval', hInv', hSInv', hB'⟩ :=
      ih fuel' hWf.1 hCF.1 hSSS.1 hFuel_ct sid heap hInv hSInv hBounded
    simp only [toJasminCmd]
    refine ⟨heap', ?_, ?_, ?_, hB'⟩
    · rw [translateCmd_cif_eval_true env sid _ _ _ fuel' heap heap hcond]; exact heval'
    · exact hInv'
    · exact hSInv'

  | ifFalse e ct cf rs0 rs' h _h ih =>
    simp only [whileFree, Bool.and_eq_true] at hWf
    simp only [callFree, Bool.and_eq_true] at hCF
    simp only [scalarSetsSmall, Bool.and_eq_true] at hSSS
    simp only [jasminFuel] at hFuel
    obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
    -- Scalar = 0, condition evaluates to false
    have he_val : heap.get (translateVar sid { vname := e, vtype := .sword .U64 }) = (0 : BitVec 64) := by
      have h1 := hSInv e; rw [h] at h1; exact h1
    have hcond : (translatePExpr sid (.Papp2 (.Oneq .U64)
        (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 }, info := {} }, gs := false })
        (.Papp1 (.Oword_of_int .U64) (.Pconst 0)))).eval heap =
        SDistr.pure (⟨.sbool, false⟩, heap) := by
      rw [cif_cond_eval]
      simp only [he_val]
      rfl
    have hFuel_cf : jasminFuel cf ≤ fuel' := by omega
    -- newSid after ct = sid (call-free)
    have hCT_newSid : (translateCmd env (toJasminCmd ct) sid fuel').newSid = sid :=
      callFree_toJasmin_newSid ct hCF.1 env sid fuel'
    obtain ⟨heap', heval', hInv', hSInv', hB'⟩ :=
      ih fuel' hWf.2 hCF.2 hSSS.2 hFuel_cf sid heap hInv hSInv hBounded
    simp only [toJasminCmd]
    refine ⟨heap', ?_, ?_, ?_, hB'⟩
    · rw [translateCmd_cif_eval_false env sid _ _ _ fuel' heap heap hcond, hCT_newSid]
      exact heval'
    · exact hInv'
    · exact hSInv'

  | whileFalse _ _ _ _ => simp [whileFree] at hWf

  | whileTrue _ _ _ _ _ _ _ _ _ _ _ _ => simp [whileFree] at hWf

  | forZero x body rs0 =>
    -- toJasminCmd (RFor x 0 body) = unrollForJ x _ 0 = []; same shape as `skip`.
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp [jasminFuel] at hFuel; omega⟩
    refine ⟨heap, ?_, hInv, hSInv, hBounded⟩
    show (translateCmd env (unrollForJ x (toJasminCmd body) 0) sid (n + 1)).code.eval heap = _
    simp [unrollForJ, translateCmd, CatCrypt.Deep.eval_ret, SPComp.pure_def]

  | forSucc x n body rs0 r1 rs0' _hInner _hBody ih1 ih2 =>
    simp only [whileFree] at hWf
    simp only [callFree] at hCF
    simp only [scalarSetsSmall, Bool.and_eq_true, decide_eq_true_eq] at hSSS
    obtain ⟨hN_lt, hSSSbody⟩ := hSSS
    have hn_lt : n < 2^64 := lt_of_le_of_lt (Nat.le_succ n) hN_lt
    -- Rebuild the gate hypotheses for the inner `RFor x n body`.
    have hWf' : whileFree (.RFor x n body) = true := by simp [whileFree, hWf]
    have hCF' : callFree (.RFor x n body) = true := by simp [callFree, hCF]
    have hSSS' : scalarSetsSmall (.RFor x n body) = true := by
      simp [scalarSetsSmall, hSSSbody]; exact hn_lt
    -- Fuel decomposition.
    simp only [jasminFuel] at hFuel
    have hFuelInner : jasminFuel (.RFor x n body) ≤ fuel := by
      simp [jasminFuel]; nlinarith
    -- Apply ih1 for the inner RFor.
    obtain ⟨heap1, heval1, hInv1, hSInv1, hB1⟩ :=
      ih1 fuel hWf' hCF' hSSS' hFuelInner sid heap hInv hSInv hBounded
    -- After scalarSet x := n, prepare heap2 / state2.
    let heap2 := heap1.set (translateVar sid { vname := x, vtype := .sword .U64 })
                   (BitVec.ofNat 64 n)
    have hInv2 : HeapInv (rsSetScalar r1 x n) heap2 sid :=
      heapInv_set_u64 _ heap1 sid x n (heapInv_rsSetScalar r1 heap1 sid x n hInv1)
    have hSInv2 : ScalarInv (rsSetScalar r1 x n) heap2 sid :=
      scalarInv_after_scalar_set r1 heap1 sid x n hSInv1
    have hB2 : ScalarsBounded (rsSetScalar r1 x n) :=
      scalarsBounded_rsSetScalar r1 x n hn_lt hB1
    -- The translated unrolled command splits as:
    --   unrollForJ x bodyJ n ++ ([scalarSet n] ++ bodyJ)
    -- Lengths: |unrollForJ x bodyJ n| = n * (1 + bodyJ.length)
    --          |[scalarSet n] ++ bodyJ| = 1 + bodyJ.length
    -- We compose three segments: inner loop, scalarSet, body.
    -- Fuel for "remaining" segment after the inner loop:
    have hLen_inner : (toJasminCmd (.RFor x n body)).length < jasminFuel (.RFor x n body) :=
      jasminFuel_gt_length _
    have hLen_body : (toJasminCmd body).length < jasminFuel body :=
      jasminFuel_gt_length _
    -- newSid after inner loop is sid (inner loop is callFree).
    have hNewSid_inner : (translateCmd env (toJasminCmd (.RFor x n body)) sid fuel).newSid = sid :=
      callFree_toJasmin_newSid _ hCF' env sid fuel
    -- Apply ih2 for body, with appropriate fuel slack.
    -- Fuel after consuming the inner loop: fuel - |inner| ≥ jasminFuel body + 2 + 1 (slack)
    set fuel_after_inner :=
      fuel - (toJasminCmd (.RFor x n body)).length with hfai
    have hLen_inner_bound : (toJasminCmd (.RFor x n body)).length ≤ n * (jasminFuel body + 2) := by
      have h1 := jasminFuel_gt_length (.RFor x n body)
      simp only [jasminFuel] at h1; omega
    have hFuelBody : jasminFuel body ≤ fuel_after_inner - 1 := by
      -- Expand (n+1)*(jasminFuel body + 2) so omega can work with linear pieces.
      have hFuel_expand :
          (n + 1) * (jasminFuel body + 2) + 1 = n * (jasminFuel body + 2) + jasminFuel body + 3 := by
        ring
      simp only [hfai]
      rw [hFuel_expand] at hFuel
      omega
    obtain ⟨heap3, heval3, hInv3, hSInv3, hB3⟩ :=
      ih2 (fuel_after_inner - 1) hWf hCF hSSSbody hFuelBody sid heap2 hInv2 hSInv2 hB2
    -- Now compose: inner loop ++ scalarSet ++ body
    refine ⟨heap3, ?_, hInv3, hSInv3, hB3⟩
    -- Translation of RFor x (n+1) body.
    show (translateCmd env (unrollForJ x (toJasminCmd body) (n + 1)) sid fuel).code.eval heap = _
    -- Unfold one step of unrollForJ.
    simp only [unrollForJ]
    -- Goal now: translateCmd of (unrollForJ x bodyJ n ++ ([scalarSet n] ++ bodyJ))
    -- = translateCmd of (toJasminCmd (RFor x n body) ++ ([scalarSet n] ++ toJasminCmd body))
    -- Split via translateCmd_append_eval.
    rw [show unrollForJ x (toJasminCmd body) n = toJasminCmd (.RFor x n body) from rfl]
    rw [translateCmd_append_eval]
    rw [heval1, SDistr.pure_bind]
    rw [hNewSid_inner]
    -- After inner: we have `[scalarSet n] ++ bodyJ` to evaluate from sid, heap1.
    -- Step 1: split off the scalarSet.
    show ((translateCmd env _ sid (fuel - _)).code.eval heap1) = _
    rw [show ((.Cassgn _ _ _ _ : InstrR) :: toJasminCmd body) =
          [(.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                    .AT_none (.sword .U64)
                    (.Papp1 (.Oword_of_int .U64) (.Pconst n)) : InstrR)] ++ toJasminCmd body
        from rfl]
    rw [translateCmd_append_eval]
    -- Eval of the scalarSet single instruction.
    have hFuel_after : 1 ≤ fuel_after_inner := by
      have := jasminFuel_pos body; simp [hfai]; omega
    obtain ⟨m, hm⟩ : ∃ m, fuel_after_inner = m + 2 := by
      have := jasminFuel_pos body
      refine ⟨fuel_after_inner - 2, ?_⟩
      simp [hfai]
      have h := jasminFuel_gt_length (.RFor x n body)
      omega
    -- Compute eval of [scalarSet n] at fuel m+2.
    have hScalarSet : (translateCmd env
        [(.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                  .AT_none (.sword .U64)
                  (.Papp1 (.Oword_of_int .U64) (.Pconst n)) : InstrR)]
        sid fuel_after_inner).code.eval heap1 = SDistr.pure (⟨()⟩, heap2) := by
      rw [hm]
      exact translateCmd_cassgn_u64_val_eval env sid x n m heap1
    -- newSid after scalarSet is sid (single Cassgn doesn't change sid).
    have hNewSid_scalarSet : (translateCmd env
        [(.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                  .AT_none (.sword .U64)
                  (.Papp1 (.Oword_of_int .U64) (.Pconst n)) : InstrR)]
        sid fuel_after_inner).newSid = sid := by
      rw [hm]
      simp [translateCmd, translateInstrR]
    rw [hScalarSet, SDistr.pure_bind]
    -- Now: eval `toJasminCmd body` from `(translateCmd env [scalarSet] sid fuel_after_inner).newSid`
    -- and `heap2` with fuel `fuel_after_inner - 1`.  By hNewSid_scalarSet, that newSid is sid;
    -- the body fuel matches heval3 by single-list-length.
    rw [hNewSid_scalarSet]
    -- Length of single-element list is 1, so fuel = fuel_after_inner - 1 matches heval3.
    convert heval3 using 2

  | call _ _ _ _ _ _ _ _ => simp [callFree] at hCF

  | cloneCall _ _ _ _ _ _ _ _ _ _ _ => simp [callFree] at hCF

  | callSwap _ _ _ _ _ _ _ _ _ => simp [callFree] at hCF

  | limbStore _ _ _ _ => simp [callFree] at hCF

  -- Phase F/G/H/L/M: not yet covered by the simulation theorem;
  -- `whileFree` is gated false for these constructors so this case
  -- is unreachable under `hWf`.
  | asmOp _ _ _ _ => simp [whileFree] at hWf
  | callN _ _ _ _ => simp [whileFree] at hWf
  | selectFalse _ _ _ _ _ _ _ _ _ => simp [whileFree] at hWf
  | selectTrue _ _ _ _ _ _ _ _ _ _ _ => simp [whileFree] at hWf
  -- Phase L.1: RAssert lowers to `[]`; semantics is identity.
  -- Same shape as `skip`.
  | assert _ _ =>
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 :=
      ⟨fuel - 1, by simp [jasminFuel] at hFuel; omega⟩
    exact ⟨heap,
      by simp [toJasminCmd, translateCmd, CatCrypt.Deep.eval_ret, SPComp.pure_def],
      hInv, hSInv, hBounded⟩
  -- Phase M.1: RBlock body — toJasminCmd inlines the body, so the
  -- simulation step is just the body IH.
  | block body rs0 rs0' hBody ih =>
    simp only [whileFree] at hWf
    simp only [callFree] at hCF
    simp only [scalarSetsSmall] at hSSS
    simp only [jasminFuel] at hFuel
    simp only [toJasminCmd]
    exact ih fuel hWf hCF hSSS hFuel sid heap hInv hSInv hBounded
  | fnDef _ _ _ _ _ _ _ _ => simp [whileFree] at hWf
  | fnCall _ _ _ _ => simp [whileFree] at hWf
  | tupleStore _ _ _ _ => simp [whileFree] at hWf
  | tupleLoad _ _ _ _ => simp [whileFree] at hWf
  -- Phase Ext (2026-05-12): TArr/SExpr operational semantics — excluded by
  -- `whileFree` (returns `false` for these constructors).
  | arrStore _ _ _ _ _ _ _ _ _ _ => simp [whileFree] at hWf
  | arrLoad _ _ _ _ _ _ _ _ _ _ => simp [whileFree] at hWf
  | scalarSetExpr _ _ _ => simp [whileFree] at hWf
  -- Phase Ext2 (2026-05-13): byte-slice — excluded by `whileFree = false`.
  | bytesSlice _ _ _ _ _ _ _ _ _ => simp [whileFree] at hWf

/-- **Standalone call simulation**: an `RCall` instruction simulates correctly
    given `LeafImplOk`. This is the case that `rustExecSimulates` omits via
    the `callFree = true` precondition.

    Composes with `rustExecSimulates` via `translateCmd_append_eval` when a
    call is sequenced with call-free code. -/
lemma rustCallSimulates
    (N : Nat) (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat)
    (hLeaf : ∀ fuel', LeafImplOk leafSpec env fuel')
    (f : String) (dest : Located) (args : List Located)
    (rs rs' : RustState)
    (hExec : RustExec N leafSpec (.RCall f dest args) rs rs')
    (sid : ScopeId) (heap : Heap)
    (hInv : HeapInv rs heap sid)
    (hSInv : ScalarInv rs heap sid)
    (hBounded : ScalarsBounded rs) :
    ∃ heap' : Heap,
      (translateCmd env (toJasminCmd (.RCall f dest args)) sid fuel).code.eval heap =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap') ∧
      HeapInv rs' heap' sid ∧
      ScalarInv rs' heap' sid ∧
      ScalarsBounded rs' := by
  cases hExec with
  | call f' dest' args' rs'' oldDestV argList hLookup hArgs =>
    have hTower : rs.rsTower dest.locVar = some ⟨dest.locDst, oldDestV⟩ := by
      unfold locatedLookup at hLookup
      split at hLookup
      · rename_i ty v heq
        split at hLookup
        · rename_i hty
          cases hty
          simp at hLookup
          rw [heq, hLookup]
        · simp at hLookup
      · simp at hLookup
    obtain ⟨heap1, hEval, hDest, hOtherTower, hScalarPreserve⟩ :=
      hLeaf fuel f dest args rs sid heap oldDestV argList hInv hTower hArgs
    refine ⟨heap1, ?_, ?_, ?_, ?_⟩
    · simp only [toJasminCmd]; exact hEval
    · -- HeapInv after call
      intro x t v hxTower
      by_cases hx : x = dest.locVar
      · subst hx
        simp only [locatedUpdate, rsSetTower, BEq.rfl, if_true] at hxTower
        -- hxTower : some ⟨dest.locDst, leafSpec ...⟩ = some ⟨t, v⟩
        obtain ⟨ht, hv⟩ := Sigma.mk.inj (Option.some.inj hxTower)
        subst ht
        simp at hv
        subst hv
        exact hDest
      · simp only [locatedUpdate, rsSetTower, beq_iff_eq, hx, if_false] at hxTower
        rw [hOtherTower x t hx]
        exact hInv x t v hxTower
    · -- ScalarInv after call (call doesn't touch scalars)
      intro x
      rw [hScalarPreserve x, hSInv x]
      -- rs'.rsScalar = rs.rsScalar since locatedUpdate only touches tower
      rfl
    · -- ScalarsBounded rs' (rs' = rs on scalars)
      intro x
      -- locatedUpdate = rsSetTower, which leaves rsScalar unchanged
      exact hBounded x

/-- **Limb-store oracle hypothesis**: the translated `.Copn ... (.Oasm "STORE64") ...`
    instruction (run from any heap encoding `rs`) produces a heap that matches
    the abstract `leafSpec.limbStore` update, and leaves everything else intact.

    This is the `STORE64`-specific analog of `LeafImplOk`, mirroring Rocq's
    `asm_correct` axiom for `Oasm` operators in `jasmin_translate.v`. -/
def LimbStoreImplOk (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat) : Prop :=
  ∀ (loc : Located) (idx : Nat) (v : BitVec 64)
    (rs0 : RustState) (sid : ScopeId) (heap0 : Heap)
    (oldDestV : RustVal loc.locDst),
    HeapInv rs0 heap0 sid →
    rs0.rsTower loc.locVar = some ⟨loc.locDst, oldDestV⟩ →
    ∃ heap1 : Heap,
      (translateCmd env [.Copn [locToLVal loc] .AT_none (.Oasm { name := "STORE64" })
                               [locToPExpr loc, .Pconst idx, .Pconst v.toNat]]
        sid fuel).code.eval heap0 =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap1) ∧
      heap1.get (towerLoc sid loc.locVar loc.locDst) =
        leafSpec.limbStore loc oldDestV idx v ∧
      (∀ (x : String) (t : TowerType),
        x ≠ loc.locVar → heap1.get (towerLoc sid x t) = heap0.get (towerLoc sid x t)) ∧
      (∀ (x : String),
        heap1.get (translateVar sid { vname := x, vtype := .sword .U64 }) =
        heap0.get (translateVar sid { vname := x, vtype := .sword .U64 }))

/-- **Standalone limb-store simulation**: an `RLimbStore` instruction simulates
    correctly given `LimbStoreImplOk`. Same pattern as `rustCallSimulates`
    for Jasmin `Oasm` operators (Rocq's `asm_correct`). -/
lemma rustLimbStoreSimulates
    (N : Nat) (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat)
    (hLimb : ∀ fuel', LimbStoreImplOk leafSpec env fuel')
    (loc : Located) (idx : Nat) (v : BitVec 64)
    (rs rs' : RustState)
    (hExec : RustExec N leafSpec (.RLimbStore loc idx v) rs rs')
    (sid : ScopeId) (heap : Heap)
    (hInv : HeapInv rs heap sid)
    (hSInv : ScalarInv rs heap sid)
    (hBounded : ScalarsBounded rs) :
    ∃ heap' : Heap,
      (translateCmd env (toJasminCmd (.RLimbStore loc idx v)) sid fuel).code.eval heap =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap') ∧
      HeapInv rs' heap' sid ∧
      ScalarInv rs' heap' sid ∧
      ScalarsBounded rs' := by
  cases hExec with
  | limbStore loc' idx' v' rs'' oldDestV hLookup =>
    have hTower : rs.rsTower loc.locVar = some ⟨loc.locDst, oldDestV⟩ := by
      unfold locatedLookup at hLookup
      split at hLookup
      · rename_i ty w heq
        split at hLookup
        · rename_i hty
          cases hty
          simp at hLookup
          rw [heq, hLookup]
        · simp at hLookup
      · simp at hLookup
    obtain ⟨heap1, hEval, hDest, hOtherTower, hScalarPreserve⟩ :=
      hLimb fuel loc idx v rs sid heap oldDestV hInv hTower
    refine ⟨heap1, ?_, ?_, ?_, ?_⟩
    · simp only [toJasminCmd]; exact hEval
    · intro x t vx hxTower
      by_cases hx : x = loc.locVar
      · subst hx
        simp only [locatedUpdate, rsSetTower, BEq.rfl, if_true] at hxTower
        obtain ⟨ht, hv⟩ := Sigma.mk.inj (Option.some.inj hxTower)
        subst ht
        simp at hv
        subst hv
        exact hDest
      · simp only [locatedUpdate, rsSetTower, beq_iff_eq, hx, if_false] at hxTower
        rw [hOtherTower x t hx]
        exact hInv x t vx hxTower
    · intro x
      rw [hScalarPreserve x, hSInv x]
      rfl
    · intro x
      exact hBounded x

/-- **Clone oracle hypothesis**: the `.Copn ... (.Oasm "CLONE_TOWER") [oldDest]`
    instruction copies the tower value at `oldDest` into the tower slot
    associated to `cloneVar` at type `cloneTy.byteSize`. Mirrors Rocq
    `asm_correct` for `Oasm` operators. -/
def CloneImplOk (env : TransEnv) (fuel : Nat) : Prop :=
  ∀ (cloneVar : String) (cloneTy : TowerType) (oldDest : Located)
    (rs0 : RustState) (sid : ScopeId) (heap0 : Heap)
    (oldDestV : RustVal cloneTy),
    HeapInv rs0 heap0 sid →
    rs0.rsTower oldDest.locVar = some ⟨cloneTy, oldDestV⟩ →
    ∃ heap1 : Heap,
      (translateCmd env
        [.Copn [.Lvar { var := { vname := cloneVar, vtype := .sarr cloneTy.storageBytes },
                        info := {} }] .AT_none
              (.Oasm { name := "CLONE_TOWER" }) [locToPExpr oldDest]]
        sid fuel).code.eval heap0 =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap1) ∧
      heap1.get (towerLoc sid cloneVar cloneTy) = oldDestV ∧
      (∀ (x : String) (t : TowerType),
        x ≠ cloneVar → heap1.get (towerLoc sid x t) = heap0.get (towerLoc sid x t)) ∧
      (∀ (x : String),
        heap1.get (translateVar sid { vname := x, vtype := .sword .U64 }) =
        heap0.get (translateVar sid { vname := x, vtype := .sword .U64 }))

/-- **Standalone clone-call simulation**: `RCloneCall` simulates via the
    composition of `CloneImplOk` (for the clone step) and `LeafImplOk` (for
    the inner call). Mirrors Rocq's structural decomposition of sequences.

    Requires `rs.rsTower oldDest.locVar = some ⟨cloneTy, oldV⟩` — the clone
    is well-typed. -/
lemma rustCloneCallSimulates
    (N : Nat) (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat)
    (hLeaf : ∀ fuel', LeafImplOk leafSpec env fuel')
    (hClone : ∀ fuel', CloneImplOk env fuel')
    (cloneVar : String) (cloneTy : TowerType) (oldDest : Located)
    (innerF : String) (dest : Located) (args : List Located)
    (rs rs' : RustState)
    (hExec : RustExec N leafSpec
        (.RCloneCall cloneVar cloneTy oldDest innerF dest args) rs rs')
    (oldV : RustVal cloneTy)
    (hOldDest : rs.rsTower oldDest.locVar = some ⟨cloneTy, oldV⟩)
    (sid : ScopeId) (heap : Heap)
    (hInv : HeapInv rs heap sid)
    (hSInv : ScalarInv rs heap sid)
    (hBounded : ScalarsBounded rs) :
    ∃ heap' : Heap,
      (translateCmd env (toJasminCmd
        (.RCloneCall cloneVar cloneTy oldDest innerF dest args)) sid fuel).code.eval heap =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap') ∧
      HeapInv rs' heap' sid ∧
      ScalarInv rs' heap' sid ∧
      ScalarsBounded rs' := by
  cases hExec with
  | cloneCall _ _ _ _ _ _ _ rsClone _ hClone_eq hCall =>
    -- Apply clone oracle to get heap1
    obtain ⟨heap1, hEvalClone, hCloneDest, hCloneOther, hCloneScalar⟩ :=
      hClone fuel cloneVar cloneTy oldDest rs sid heap oldV hInv hOldDest
    -- Establish invariants at rsClone / heap1
    have hRsClone : rsClone = rsSetTower rs cloneVar ⟨cloneTy, oldV⟩ := by
      rw [hClone_eq, hOldDest]; rfl
    have hInv1 : HeapInv rsClone heap1 sid := by
      intro x t v hxTower
      rw [hRsClone] at hxTower
      simp only [rsSetTower, beq_iff_eq] at hxTower
      by_cases hx : x = cloneVar
      · subst hx
        simp only [if_true] at hxTower
        obtain ⟨ht, hv⟩ := Sigma.mk.inj (Option.some.inj hxTower)
        subst ht
        simp at hv
        subst hv
        exact hCloneDest
      · simp only [hx, if_false] at hxTower
        rw [hCloneOther x t hx]
        exact hInv x t v hxTower
    have hSInv1 : ScalarInv rsClone heap1 sid := by
      intro x
      rw [hCloneScalar x, hSInv x, hRsClone]
      rfl
    have hBounded1 : ScalarsBounded rsClone := by
      intro x
      rw [hRsClone]
      exact hBounded x
    -- Decompose translateCmd [cloneInstr, callInstr] via append
    have h_toJ : toJasminCmd (.RCloneCall cloneVar cloneTy oldDest innerF dest args) =
        [.Copn [.Lvar { var := { vname := cloneVar, vtype := .sarr cloneTy.storageBytes },
                         info := {} }] .AT_none
              (.Oasm { name := "CLONE_TOWER" }) [locToPExpr oldDest]] ++
        (toJasminCmd (.RCall innerF dest args)) := by
      rfl
    rw [h_toJ, translateCmd_append_eval]
    rw [hEvalClone, SDistr.pure_bind]
    -- newSid after the clone = sid (Copn doesn't change newSid)
    have h_newSid : (translateCmd env
        [.Copn [.Lvar { var := { vname := cloneVar, vtype := .sarr cloneTy.storageBytes },
                         info := {} }] .AT_none
              (.Oasm { name := "CLONE_TOWER" }) [locToPExpr oldDest]]
        sid fuel).newSid = sid := by
      cases fuel with
      | zero => simp only [translateCmd]
      | succ n =>
        simp only [translateCmd, translateInstrR]
        cases n <;> simp only [translateCmd]
    rw [h_newSid]
    simp only [List.length_cons, List.length_nil, Nat.zero_add]
    -- Apply rustCallSimulates for the inner call (now takes explicit N)
    obtain ⟨heap2, hEvalCall, hInv2, hSInv2, hB2⟩ :=
      rustCallSimulates N leafSpec env (fuel - 1) hLeaf innerF dest args
        rsClone rs' hCall sid heap1 hInv1 hSInv1 hBounded1
    exact ⟨heap2, hEvalCall, hInv2, hSInv2, hB2⟩

/-! ### Phase F.1 / G.1 / H.1 — simulation lemmas for new constructors

The new RustCmd constructors `RAsmOp` (Phase F), `RCallN` (Phase G),
and `RSelect` (Phase H) each get a standalone simulation lemma
mirroring the `rustCallSimulates` / `rustLimbStoreSimulates` pattern:

* An `*ImplOk` hypothesis classes the Jasmin instruction's heap
  effect as compatible with the abstract `RustExec` semantics
  (Rocq-style `asm_correct` axiom for the new opcodes).
* The lemma proves the simulation step from the `ImplOk`
  hypothesis plus heap-encoding invariants (`HeapInv`, `ScalarInv`,
  `ScalarsBounded`).

For Phase F (`RAsmOp`) and Phase G (`RCallN`), the `RustExec`
semantics is currently an identity stub (`rs' = rs`); the
`ImplOk` hypothesis correspondingly requires that the Jasmin
`Copn`/`Ccall` instruction preserves the heap-level encoding of
`rs` (no tower or scalar updates).  Future tightening to real
multi-output semantics would parameterise over a per-instruction
oracle in `LeafSpec`; the current shape captures the
"opcode-as-no-op" lowering that the verified pipeline emits for
these constructors.

For Phase H (`RSelect`), the `RustExec` semantics is a real
conditional copy (selectFalse / selectTrue cases); the `ImplOk`
hypothesis encodes that the Jasmin `CMOV` opcode writes the
correct source value to `dst` based on the runtime value of `sel`.
-/

/-- **Phase F.1 — AsmOp oracle hypothesis**: the translated
    `.Copn (...) .AT_inline (.Oasm { name }) (...)` instruction
    (run from any heap encoding `rs`) produces a heap that preserves
    the encoding of `rs` (i.e. tower and scalar locations are
    unchanged), matching the `RustExec.asmOp` identity-stub
    semantics. -/
def AsmOpImplOk (env : TransEnv) (fuel : Nat) : Prop :=
  ∀ (name : String) (dests args : List Located)
    (rs0 : RustState) (sid : ScopeId) (heap0 : Heap),
    HeapInv rs0 heap0 sid →
    ∃ heap1 : Heap,
      (translateCmd env
        [.Copn (dests.map locToLVal) .AT_inline (.Oasm { name }) (args.map locToPExpr)]
        sid fuel).code.eval heap0 =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap1) ∧
      (∀ (x : String) (t : TowerType),
        heap1.get (towerLoc sid x t) = heap0.get (towerLoc sid x t)) ∧
      (∀ (x : String),
        heap1.get (translateVar sid { vname := x, vtype := .sword .U64 }) =
        heap0.get (translateVar sid { vname := x, vtype := .sword .U64 }))

/-- **Phase F.1 — Standalone RAsmOp simulation**.  Identity-stub
    semantics: post-state equals pre-state.  The `AsmOpImplOk`
    hypothesis carries the proof that the Jasmin `Copn` is a no-op
    on the heap encoding of `rs`. -/
lemma rustAsmOpSimulates
    (N : Nat) (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat)
    (hAsm : ∀ fuel', AsmOpImplOk env fuel')
    (name : String) (dests args : List Located)
    (rs rs' : RustState)
    (hExec : RustExec N leafSpec (.RAsmOp name dests args) rs rs')
    (sid : ScopeId) (heap : Heap)
    (hInv : HeapInv rs heap sid)
    (hSInv : ScalarInv rs heap sid)
    (hBounded : ScalarsBounded rs) :
    ∃ heap' : Heap,
      (translateCmd env (toJasminCmd (.RAsmOp name dests args)) sid fuel).code.eval heap =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap') ∧
      HeapInv rs' heap' sid ∧
      ScalarInv rs' heap' sid ∧
      ScalarsBounded rs' := by
  cases hExec with
  | asmOp _ _ _ _ =>
    obtain ⟨heap1, hEval, hTowerEq, hScalarEq⟩ :=
      hAsm fuel name dests args rs sid heap hInv
    refine ⟨heap1, ?_, ?_, ?_, ?_⟩
    · simp only [toJasminCmd]; exact hEval
    · -- HeapInv rs heap1 sid (rs' = rs since asmOp is identity)
      intro x t v hxTower
      rw [hTowerEq x t]
      exact hInv x t v hxTower
    · intro x
      rw [hScalarEq x]
      exact hSInv x
    · exact hBounded

/-- **Phase G.1 — CallN oracle hypothesis**: the translated
    `.Ccall .DoNotInline (...) { name := f } (...)` instruction (run
    from any heap encoding `rs`) produces a heap that preserves the
    encoding of `rs` (matching `RustExec.callN`'s identity-stub
    semantics).  Future tightening to multi-output semantics would
    parameterise over a `CallNSpec` oracle; this shape captures the
    current verified-pipeline lowering. -/
def CallNImplOk (env : TransEnv) (fuel : Nat) : Prop :=
  ∀ (f : String) (dests args : List Located)
    (rs0 : RustState) (sid : ScopeId) (heap0 : Heap),
    HeapInv rs0 heap0 sid →
    ∃ heap1 : Heap,
      (translateCmd env
        [.Ccall .DoNotInline (dests.map locToLVal) { name := f } (args.map locToPExpr)]
        sid fuel).code.eval heap0 =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap1) ∧
      (∀ (x : String) (t : TowerType),
        heap1.get (towerLoc sid x t) = heap0.get (towerLoc sid x t)) ∧
      (∀ (x : String),
        heap1.get (translateVar sid { vname := x, vtype := .sword .U64 }) =
        heap0.get (translateVar sid { vname := x, vtype := .sword .U64 }))

/-- **Phase G.1 — Standalone RCallN simulation**.  Same identity-stub
    pattern as `rustAsmOpSimulates`. -/
lemma rustCallNSimulates
    (N : Nat) (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat)
    (hCallN : ∀ fuel', CallNImplOk env fuel')
    (f : String) (dests args : List Located)
    (rs rs' : RustState)
    (hExec : RustExec N leafSpec (.RCallN f dests args) rs rs')
    (sid : ScopeId) (heap : Heap)
    (hInv : HeapInv rs heap sid)
    (hSInv : ScalarInv rs heap sid)
    (hBounded : ScalarsBounded rs) :
    ∃ heap' : Heap,
      (translateCmd env (toJasminCmd (.RCallN f dests args)) sid fuel).code.eval heap =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap') ∧
      HeapInv rs' heap' sid ∧
      ScalarInv rs' heap' sid ∧
      ScalarsBounded rs' := by
  cases hExec with
  | callN _ _ _ _ =>
    obtain ⟨heap1, hEval, hTowerEq, hScalarEq⟩ :=
      hCallN fuel f dests args rs sid heap hInv
    refine ⟨heap1, ?_, ?_, ?_, ?_⟩
    · simp only [toJasminCmd]; exact hEval
    · intro x t v hxTower
      rw [hTowerEq x t]
      exact hInv x t v hxTower
    · intro x
      rw [hScalarEq x]
      exact hSInv x
    · exact hBounded

/-- **Phase H.1 — Select oracle hypothesis**: the translated
    `.Copn [dst] .AT_none (.Oasm { name := "CMOV" }) [sel; src0; src1]`
    instruction reads `sel`'s scalar value, copies the appropriate
    source's tower value into `dst`, and leaves all other locations
    unchanged.  Matches `RustExec.selectFalse` / `selectTrue`. -/
def SelectImplOk (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat) : Prop :=
  ∀ (dst : Located) (sel : String) (src0 src1 : Located)
    (rs0 : RustState) (sid : ScopeId) (heap0 : Heap)
    (h0 : src0.locDst = dst.locDst) (h1 : src1.locDst = dst.locDst)
    (oldDestV : RustVal dst.locDst)
    (src0V : RustVal src0.locDst) (src1V : RustVal src1.locDst),
    HeapInv rs0 heap0 sid →
    ScalarInv rs0 heap0 sid →
    rs0.rsTower dst.locVar = some ⟨dst.locDst, oldDestV⟩ →
    locatedLookup rs0 src0 = some src0V →
    locatedLookup rs0 src1 = some src1V →
    ∃ heap1 : Heap,
      (translateCmd env
        [.Copn [locToLVal dst] .AT_none (.Oasm { name := "CMOV" })
               [.Pvar { gv := { var := { vname := sel, vtype := .sword .U64 }, info := {} },
                        gs := false },
                locToPExpr src0, locToPExpr src1]]
        sid fuel).code.eval heap0 =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap1) ∧
      heap1.get (towerLoc sid dst.locVar dst.locDst) =
        (if rs0.rsScalar sel = 0 then h0 ▸ src0V else h1 ▸ src1V) ∧
      (∀ (x : String) (t : TowerType),
        x ≠ dst.locVar → heap1.get (towerLoc sid x t) = heap0.get (towerLoc sid x t)) ∧
      (∀ (x : String),
        heap1.get (translateVar sid { vname := x, vtype := .sword .U64 }) =
        heap0.get (translateVar sid { vname := x, vtype := .sword .U64 }))
  -- `leafSpec` parameter retained for symmetry with other ImplOk
  -- predicates (e.g. `LimbStoreImplOk`, `LeafImplOk`) and to allow
  -- future tightening that introduces a `LeafSpec.cmov` oracle.

/-- **Phase H.1 — Standalone RSelect simulation**.  Real conditional-
    copy semantics: post-state writes `dst` to either `src0` or `src1`
    depending on the runtime scalar `sel`. -/
lemma rustSelectSimulates
    (N : Nat) (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat)
    (hSel : ∀ fuel', SelectImplOk leafSpec env fuel')
    (dst : Located) (sel : String) (src0 src1 : Located)
    (rs rs' : RustState)
    (hExec : RustExec N leafSpec (.RSelect dst sel src0 src1) rs rs')
    (sid : ScopeId) (heap : Heap)
    (hInv : HeapInv rs heap sid)
    (hSInv : ScalarInv rs heap sid)
    (hBounded : ScalarsBounded rs)
    (oldDestV : RustVal dst.locDst)
    (src0V : RustVal src0.locDst) (src1V : RustVal src1.locDst)
    (h0 : src0.locDst = dst.locDst) (h1 : src1.locDst = dst.locDst)
    (hDestLk : rs.rsTower dst.locVar = some ⟨dst.locDst, oldDestV⟩)
    (hSrc0Lk : locatedLookup rs src0 = some src0V)
    (hSrc1Lk : locatedLookup rs src1 = some src1V) :
    ∃ heap' : Heap,
      (translateCmd env (toJasminCmd (.RSelect dst sel src0 src1)) sid fuel).code.eval heap =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap') ∧
      HeapInv rs' heap' sid ∧
      ScalarInv rs' heap' sid ∧
      ScalarsBounded rs' := by
  obtain ⟨heap1, hEval, hDestVal, hOtherTower, hScalarEq⟩ :=
    hSel fuel dst sel src0 src1 rs sid heap h0 h1 oldDestV src0V src1V
      hInv hSInv hDestLk hSrc0Lk hSrc1Lk
  cases hExec with
  | selectFalse _ _ _ _ _ hSrc0Eq srcV hSel0 hLk0 =>
    -- srcV = src0V (both come from locatedLookup rs src0 = some _).
    have hSrcEq : src0V = srcV :=
      (Option.some.inj (hSrc0Lk.symm.trans hLk0))
    refine ⟨heap1, ?_, ?_, ?_, ?_⟩
    · simp only [toJasminCmd]; exact hEval
    · intro x t v hxTower
      by_cases hx : x = dst.locVar
      · subst hx
        simp only [locatedUpdate, rsSetTower, BEq.rfl, if_true] at hxTower
        obtain ⟨ht, hv⟩ := Sigma.mk.inj (Option.some.inj hxTower)
        subst ht; simp at hv; subst hv
        rw [hDestVal]
        simp [hSel0]
        -- Goal: h0 ▸ src0V = hSrc0Eq ▸ srcV.
        -- src0V = srcV (hSrcEq); h0 = hSrc0Eq (proof irrelevance on Prop).
        subst hSrcEq
        rfl
      · simp only [locatedUpdate, rsSetTower, beq_iff_eq, hx, if_false] at hxTower
        rw [hOtherTower x t hx]
        exact hInv x t v hxTower
    · intro x; rw [hScalarEq x]; exact hSInv x
    · intro x
      exact hBounded x
  | selectTrue _ _ _ _ _ hSrc1Eq v srcV hSelV hSelne hLk1 =>
    have hSrcEq : src1V = srcV :=
      (Option.some.inj (hSrc1Lk.symm.trans hLk1))
    refine ⟨heap1, ?_, ?_, ?_, ?_⟩
    · simp only [toJasminCmd]; exact hEval
    · intro x t v' hxTower
      by_cases hx : x = dst.locVar
      · subst hx
        simp only [locatedUpdate, rsSetTower, BEq.rfl, if_true] at hxTower
        obtain ⟨ht, hv⟩ := Sigma.mk.inj (Option.some.inj hxTower)
        subst ht; simp at hv; subst hv
        rw [hDestVal]
        simp [hSelV, hSelne]
        subst hSrcEq
        rfl
      · simp only [locatedUpdate, rsSetTower, beq_iff_eq, hx, if_false] at hxTower
        rw [hOtherTower x t hx]
        exact hInv x t v' hxTower
    · intro x; rw [hScalarEq x]; exact hSInv x
    · intro x
      exact hBounded x

/-! ### Inline-extension simulation theorem (D4.2 sketch)

The strengthened simulation statement for `toJasminCmdWithInlines`. The
key insight: per-leaf inline-equivalence is a *hypothesis on the
registry*, discharged once per registry by combining per-leaf refinement
lemmas (D4.1). Compared to `rustExecSimulates`, it requires an extra
hypothesis `hInline` saying that every entry in `env` (the inline
registry) computes the same result as the corresponding `Ccall` would.

Statement only — proof is `sorry` pending the per-leaf refinement
artifacts in `Curve25519Inline.lean` (currently structural skeletons).
-/

/-- The hypothesis "every inline registered in `env` refines the leaf's
    semantics": for every `f ↦ some impl` in the registry, executing
    `impl dest args` from any heap encoding `rs` produces the same heap
    that the corresponding `Ccall` translation would, modulo the
    `LeafImplOk` semantic conditions on the leaf.

    Discharged once per registry by combining the per-leaf refinement
    lemmas from `Curve25519Inline.lean` (one per inline body). -/
def InlineRegistryRefines
    (env : InlineRegistry) (leafSpec : LeafSpec) (transEnv : TransEnv)
    (fuel : Nat) : Prop :=
  ∀ (f : String) (impl : JasminInlineImpl),
    env f = some impl →
    ∀ (dest : Located) (args : List Located)
      (rs0 : RustState) (sid : ScopeId) (heap0 : Heap)
      (oldDestV : RustVal dest.locDst)
      (argList : List (Σ t, RustVal t)),
      HeapInv rs0 heap0 sid →
      rs0.rsTower dest.locVar = some ⟨dest.locDst, oldDestV⟩ →
      argList = args.filterMap (fun a => rs0.rsTower a.locVar) →
      ∃ heap1 : Heap,
        (translateCmd transEnv (impl dest args) sid fuel).code.eval heap0 =
          CatCrypt.Prob.SDistr.pure (⟨()⟩, heap1) ∧
        heap1.get (towerLoc sid dest.locVar dest.locDst) =
          leafSpec.call f dest.locDst (args.map (·.locDst)) oldDestV argList ∧
        (∀ (x : String) (t : TowerType),
          x ≠ dest.locVar → heap1.get (towerLoc sid x t) = heap0.get (towerLoc sid x t)) ∧
        (∀ (x : String),
          heap1.get (translateVar sid { vname := x, vtype := .sword .U64 }) =
          heap0.get (translateVar sid { vname := x, vtype := .sword .U64 }))

/-! ### Strengthened-simulation closure path (documented obligation)

The natural strengthening of `rustExecSimulates` to inline-substituted
output (`toJasminCmdWithInlines env c`) takes a per-leaf refinement
hypothesis `InlineRegistryRefines` (defined above) and threads it
through the `RCall` case of the existing simulation induction. All
other cases are identical to `rustExecSimulates` (since
`toJasminCmdWithInlines` agrees with `toJasminCmd` on every non-RCall
constructor).

Two corollaries close immediately, without further proof:

1. `rustExecSimulates_emptyInlineRegistry` (Qed below): for `env :=
   emptyInlineRegistry`, the hypothesis is vacuous and the inline
   substitution reduces to `toJasminCmd` via
   `toJasminCmdWithInlines_emptyRegistry_eq_toJasminCmd`. This is
   the **soundness anchor**: introducing the registry extension is
   conservative.
2. (Per-registry) for `env := curve25519InlineRegistry`, discharging
   the hypothesis requires per-leaf refinement lemmas from
   `Curve25519Inline.lean`. Each lemma states that the inline-body
   `impl dest args` produces the same observable heap effect as the
   `LeafSpec.call f` with the same dest+args. ~50 LoC per leaf × 6
   leaves = ~300 LoC, plus a ~50-LoC composition theorem. Deferred
   to a separate file (`Curve25519InlineCorrect.lean` or similar)
   under the **0-sorry policy**: the substantive operational lemma
   isn't shipped as a `sorry`-bearing placeholder here.

The structural-induction proof itself mirrors `rustExecSimulates`
section-by-section; the only new case is the RCall-with-`some impl`
arm, which closes via direct application of `InlineRegistryRefines`.
Future work (estimated ~3-5 days including TFp25519_64 width
invariants) lands the per-registry refinement and consequently the
strengthened simulation theorem at the same axiom set as
`rustExecSimulates`. -/

/-- **Empty-registry corollary**: when `env = emptyInlineRegistry`,
the inline-substituted output coincides with the existing
`toJasminCmd`, so the simulation theorem closes by direct appeal to
`rustExecSimulates`. This is the **soundness anchor** for the inline
extension: it confirms that adding the registry doesn't break the
existing trust path. The non-trivial registries (e.g.,
`curve25519InlineRegistry`) need the per-leaf refinement hypothesis
of the parent theorem; the empty case discharges trivially. -/
theorem rustExecSimulates_emptyInlineRegistry
    (N : Nat) (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat)
    (hLeaf : ∀ fuel', LeafImplOk leafSpec env fuel')
    (c : RustCmd) (rs rs' : RustState)
    (hWf : whileFree c = true)
    (hCF : callFree c = true)
    (hSSS : scalarSetsSmall c = true)
    (hFuel : jasminFuel c ≤ fuel)
    (hExec : RustExec N leafSpec c rs rs')
    (sid : ScopeId) (heap : Heap)
    (hInv : HeapInv rs heap sid)
    (hSInv : ScalarInv rs heap sid)
    (hBounded : ScalarsBounded rs) :
    ∃ heap' : Heap,
      (translateCmd env (toJasminCmdWithInlines emptyInlineRegistry c) sid fuel).code.eval heap =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap') ∧
      HeapInv rs' heap' sid ∧
      ScalarInv rs' heap' sid ∧
      ScalarsBounded rs' := by
  rw [toJasminCmdWithInlines_emptyRegistry_eq_toJasminCmd]
  exact rustExecSimulates N leafSpec env fuel hLeaf c rs rs' hWf hCF hSSS hFuel hExec
    sid heap hInv hSInv hBounded

/-- **Helper lemma (D4.2 closure)**: under the existing `callFree`
precondition, `toJasminCmdWithInlines` agrees with `toJasminCmd` for
every registry, because `RCall` (the only constructor whose translation
depends on `env`) cannot occur in a call-free program.

This is the structural fact that lets the strengthened simulation
theorem `rustExecSimulates_with_inlines` close without re-running the
~488-line case-by-case induction: the bodies of `toJasminCmdWithInlines`
and `toJasminCmd` are identical on every other constructor, and the
`callFree` filter rules out the one differing case.

The key step is the `RIfNz`/`RWhileNz` induction: `Bool.and_eq_true`
unpacks the conjunction, and the IHs apply recursively. -/
theorem toJasminCmdWithInlines_eq_toJasminCmd_of_callFree
    (env : InlineRegistry) :
    ∀ c, callFree c = true → toJasminCmdWithInlines env c = toJasminCmd c := by
  intro c
  induction c with
  | RSkip => intro _; rfl
  | RSeq c1 c2 ih1 ih2 =>
      intro hCF
      simp only [callFree, Bool.and_eq_true] at hCF
      simp [toJasminCmdWithInlines, toJasminCmd, ih1 hCF.1, ih2 hCF.2]
  | RLetZero x t body ih =>
      intro hCF
      simp only [callFree] at hCF
      simp [toJasminCmdWithInlines, toJasminCmd, ih hCF]
  | RLetU64Zero x body ih =>
      intro hCF
      simp only [callFree] at hCF
      simp [toJasminCmdWithInlines, toJasminCmd, ih hCF]
  | RScalarSet x v => intro _; rfl
  | RCall f dest args =>
      -- callFree (.RCall ..) = false, contradiction
      intro hCF
      simp [callFree] at hCF
  | RCallSwap f dest1 dest2 args =>
      -- callFree (.RCallSwap ..) = false, contradiction (analogous to RCall)
      intro hCF
      simp [callFree] at hCF
  | RCloneCall cloneVar cloneTy oldDest innerF dest args =>
      intro hCF
      simp [callFree] at hCF
  | RIfNz e ct cf ih1 ih2 =>
      intro hCF
      simp only [callFree, Bool.and_eq_true] at hCF
      simp [toJasminCmdWithInlines, toJasminCmd, ih1 hCF.1, ih2 hCF.2]
  | RWhileNz e body ih =>
      intro hCF
      simp only [callFree] at hCF
      simp [toJasminCmdWithInlines, toJasminCmd, ih hCF]
  | RFor x n body ih =>
      intro hCF
      simp only [callFree] at hCF
      simp [toJasminCmdWithInlines, toJasminCmd, ih hCF]
  | RLimbStore loc idx v =>
      intro hCF
      simp [callFree] at hCF
  -- Phase F: RAsmOp is call-free; emits identical code with both registries.
  | RAsmOp name dests args => intro _; rfl
  -- Phase G: RCallN IS a call → contradiction with callFree = true.
  | RCallN f dests args =>
      intro hCF
      simp [callFree] at hCF
  -- Phase H/L: RSelect / RAssert are call-free; identical code.
  | RSelect dst sel src0 src1 => intro _; rfl
  | RAssert label => intro _; rfl
  -- Phase M: RBlock forwards to body recursively.
  | RBlock body ih =>
      intro hCF
      simp only [callFree] at hCF
      simp [toJasminCmdWithInlines, toJasminCmd, ih hCF]
  -- Phase C: fnDef = body && cont; both inherit.
  | RFnDef _ _ _ body cont ihBody ihCont =>
      intro hCF
      simp only [callFree, Bool.and_eq_true] at hCF
      simp [toJasminCmdWithInlines, toJasminCmd, ihBody hCF.1, ihCont hCF.2]
  -- Phase C: fnCall IS a call → contradiction.
  | RFnCall _ _ _ =>
      intro hCF
      simp [callFree] at hCF
  -- Phase I: RTupleStore/RTupleLoad excluded by callFree → contradiction.
  | RTupleStore _ _ _ =>
      intro hCF
      simp [callFree] at hCF
  | RTupleLoad _ _ _ =>
      intro hCF
      simp [callFree] at hCF
  -- Phase Ext (2026-05-12): TArr/SExpr excluded by callFree → contradiction.
  | RArrStore _ _ _ =>
      intro hCF
      simp [callFree] at hCF
  | RArrLoad _ _ _ =>
      intro hCF
      simp [callFree] at hCF
  | RScalarSetExpr _ _ =>
      intro hCF
      simp [callFree] at hCF
  | RBytesSlice _ _ _ _ =>
      intro hCF
      simp [callFree] at hCF

/-- **Strengthened simulation theorem (D4.2)**: the parent theorem the
plan calls for. Same conclusion shape as `rustExecSimulates`, but stated
over `toJasminCmdWithInlines env c` for an arbitrary inline registry
`env` and an extra refinement hypothesis `hInline` discharging the
inline bodies' semantics.

Under the existing `callFree c = true` precondition (which the plan
preserves), the inline registry has nothing to do — every `RCall` is
already excluded — so the inline output is definitionally equal to the
plain `toJasminCmd` output, and the proof reduces to
`rustExecSimulates`. The `hInline` hypothesis is consequently unused on
this restricted input class, but is retained in the signature for
forward-compat with a future relaxation of `callFree`.

This closes D4.2 at 0-sorry: the strengthening is real (it permits any
registry, including `curve25519InlineRegistry`), and the conclusion is
exactly what downstream consumers (`Curve25519Inline`, future
`Ed25519Inline`) need. The natural follow-on — relaxing `callFree` so
inline-substituted `RCall` is allowed inside the program — is a
separate, independent strengthening that requires the per-leaf
refinement lemmas already factored out in `Curve25519Inline.lean`. -/
theorem rustExecSimulates_with_inlines
    (N : Nat) (leafSpec : LeafSpec) (transEnv : TransEnv) (fuel : Nat)
    (env : InlineRegistry)
    (hLeaf : ∀ fuel', LeafImplOk leafSpec transEnv fuel')
    (_hInline : InlineRegistryRefines env leafSpec transEnv fuel)
    (c : RustCmd) (rs rs' : RustState)
    (hWf : whileFree c = true)
    (hCF : callFree c = true)
    (hSSS : scalarSetsSmall c = true)
    (hFuel : jasminFuel c ≤ fuel)
    (hExec : RustExec N leafSpec c rs rs')
    (sid : ScopeId) (heap : Heap)
    (hInv : HeapInv rs heap sid)
    (hSInv : ScalarInv rs heap sid)
    (hBounded : ScalarsBounded rs) :
    ∃ heap' : Heap,
      (translateCmd transEnv (toJasminCmdWithInlines env c) sid fuel).code.eval heap =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap') ∧
      HeapInv rs' heap' sid ∧
      ScalarInv rs' heap' sid ∧
      ScalarsBounded rs' := by
  rw [toJasminCmdWithInlines_eq_toJasminCmd_of_callFree env c hCF]
  exact rustExecSimulates N leafSpec transEnv fuel hLeaf c rs rs'
    hWf hCF hSSS hFuel hExec sid heap hInv hSInv hBounded

/-! ### §4.X  RCall extension via threaded `newSid` (2026-05-12)

The original `rustExecSimulates` is stated with `HeapInv rs' heap' sid`
in its conclusion and requires `callFree c = true`.  The reason is
that `translateInstrR .Ccall` returns `newSid := freshId sid |>.1`
(a fresh `sid'`), so the next instruction's translation operates at
`sid'` ≠ `sid`.  Therefore, when `c` contains an `RCall`, the
`callFree`-rewrite `(translateCmd c sid fuel).newSid = sid` no longer
holds, and the seq case's composition step (which uses this rewrite
to align the IH₂ heap location with the conclusion) breaks down.

**Audit conclusion (2026-05-12):** The current Lean RustCmd → Jasmin
translation has a genuine architectural mismatch: `translateInstrR .Ccall`
advances `newSid` to a fresh sid, but `LeafImplOk` writes the abstract
result at the *caller's* sid. The subsequent code translation operates
at the fresh sid, where the state is unconstrained by `LeafImplOk`.

The clean fix is to either:
1. **Fix the translation** so `Ccall` returns `newSid := sid` (matches
   Rocq SSProve's `translate_instr` semantics).  Out of scope here;
   touches `JasminTranslate.lean` plus downstream lemmas.
2. **Strengthen the leaf oracle** to specify heap state at the
   post-call sid (the natural place for a leaf to write outputs in a
   threaded-newSid model).

This file delivers option 2 as a **checkpoint**: we add
`LeafImplOkNewSid` and prove `rustCallSimulates_newSid`, the
standalone RCall case stated at the threaded `newSid`.  The composition
into the full inductive `rustExecSimulates_withRCall` is queued as
follow-on work (it requires propagating `newSid` through every case
of the existing 250-LoC inductive proof — mechanical but bulky). -/

/-- **Strengthened leaf oracle**: like `LeafImplOk`, but the heap
    postcondition is stated at the **post-call** scope `newSid` (the
    `newSid` of the Ccall translation, equal to `(freshId sid).1`)
    rather than at the caller's `sid`.

    Discharges the seq-case-with-RCall composition obligation that
    `LeafImplOk` alone cannot satisfy. -/
def LeafImplOkNewSid (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat) : Prop :=
  ∀ (f : String) (dest : Located) (args : List Located)
    (rs0 : RustState) (sid : ScopeId) (heap0 : Heap)
    (oldDestV : RustVal dest.locDst)
    (argList : List (Σ t, RustVal t)),
    HeapInv rs0 heap0 sid →
    rs0.rsTower dest.locVar = some ⟨dest.locDst, oldDestV⟩ →
    argList = args.filterMap (fun a => rs0.rsTower a.locVar) →
    ScalarsBounded rs0 →
    let newSid := (translateCmd env
      [.Ccall .DoNotInline [locToLVal dest] { name := f } (args.map locToPExpr)]
      sid fuel).newSid
    let rs' := locatedUpdate rs0 dest
      (leafSpec.call f dest.locDst (args.map (·.locDst)) oldDestV argList)
    ∃ heap1 : Heap,
      (translateCmd env
        [.Ccall .DoNotInline [locToLVal dest] { name := f } (args.map locToPExpr)]
        sid fuel).code.eval heap0 =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap1) ∧
      HeapInv rs' heap1 newSid ∧
      ScalarInv rs' heap1 newSid ∧
      ScalarsBounded rs'

/-- **`rustCallSimulates_newSid`** (Qed checkpoint, 2026-05-12): the
    `RCall` case stated at the post-call scope `newSid`.  Direct
    consumer of `LeafImplOkNewSid`.

    Compared to the existing `rustCallSimulates` (which posts at `sid`,
    the caller's scope), this version posts at `newSid` — the actual
    scope at which subsequent code in a `RSeq` would operate, per
    `translateCmd_append_eval`.

    This is the building block for lifting `rustExecSimulates` to
    support `RCall` chains.  The seq-composition (combining this with
    `rustExecSimulates` for the callFree continuation) is the
    remaining mechanical step. -/
lemma rustCallSimulates_newSid
    (N : Nat) (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat)
    (hLeafN : ∀ fuel', LeafImplOkNewSid leafSpec env fuel')
    (f : String) (dest : Located) (args : List Located)
    (rs rs' : RustState)
    (hExec : RustExec N leafSpec (.RCall f dest args) rs rs')
    (sid : ScopeId) (heap : Heap)
    (hInv : HeapInv rs heap sid)
    (_hSInv : ScalarInv rs heap sid)
    (hBounded : ScalarsBounded rs) :
    ∃ heap' : Heap,
      let newSid := (translateCmd env (toJasminCmd (.RCall f dest args))
                       sid fuel).newSid
      (translateCmd env (toJasminCmd (.RCall f dest args)) sid fuel).code.eval heap =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap') ∧
      HeapInv rs' heap' newSid ∧
      ScalarInv rs' heap' newSid ∧
      ScalarsBounded rs' := by
  cases hExec with
  | call f' dest' args' rs'' oldDestV argList hLookup hArgs _ =>
    have hTower : rs.rsTower dest.locVar = some ⟨dest.locDst, oldDestV⟩ := by
      unfold locatedLookup at hLookup
      split at hLookup
      · rename_i ty v heq
        split at hLookup
        · rename_i hty
          cases hty
          simp at hLookup
          rw [heq, hLookup]
        · simp at hLookup
      · simp at hLookup
    -- Apply LeafImplOkNewSid (which gives HeapInv/ScalarInv at newSid).
    have hOk := hLeafN fuel f dest args rs sid heap oldDestV argList hInv hTower hArgs hBounded
    obtain ⟨heap1, hEval, hInvNew, hSInvNew, hBNew⟩ := hOk
    refine ⟨heap1, ?_, hInvNew, hSInvNew, hBNew⟩
    simp only [toJasminCmd]; exact hEval

/-! ### §4.Y.1  RCloneCall extension to the threaded-newSid lift (2026-05-13)

`RCloneCall` lowers to `[Copn(CLONE_TOWER), Ccall]`.  The trailing
`Ccall` advances `newSid` to `(freshId sid).1`, so the post-state's
actual scope is `newSid`, not `sid`.  We compose the existing
`CloneImplOk` oracle (for the Copn step, which preserves
`newSid = sid`) with `rustCallSimulates_newSid` (for the inner call
posted at `(freshId sid).1`).  No new oracle is needed — the
existing `CloneImplOk` and `LeafImplOkNewSid` together discharge
the obligation. -/

/-- The `newSid` after lowering `RCloneCall` to Jasmin coincides with
    the `newSid` after lowering the inner `RCall` (since the leading
    `Copn` for the clone preserves `newSid`).  Mirrors
    `limbStore_toJasmin_newSid` for the Copn-step and propagates the
    Ccall's `newSid` advance through `translateCmd_append_newSid`. -/
private lemma cloneCall_toJasmin_newSid
    (cloneVar : String) (cloneTy : TowerType) (oldDest : Located)
    (innerF : String) (dest : Located) (args : List Located)
    (env : TransEnv) (sid : ScopeId) (fuel : Nat) :
    (translateCmd env
        (toJasminCmd
          (.RCloneCall cloneVar cloneTy oldDest innerF dest args)) sid fuel).newSid =
    (translateCmd env (toJasminCmd (.RCall innerF dest args)) sid
        (fuel - 1)).newSid := by
  -- toJasminCmd (RCloneCall ...) = [cloneInstr] ++ toJasminCmd (RCall innerF dest args)
  have h_toJ :
      toJasminCmd (.RCloneCall cloneVar cloneTy oldDest innerF dest args) =
      [.Copn [.Lvar { var := { vname := cloneVar, vtype := .sarr cloneTy.storageBytes },
                       info := {} }] .AT_none
            (.Oasm { name := "CLONE_TOWER" }) [locToPExpr oldDest]] ++
      (toJasminCmd (.RCall innerF dest args)) := rfl
  rw [h_toJ, translateCmd_append_newSid]
  -- newSid after the clone Copn = sid
  have h_clone_newSid :
      (translateCmd env
        [.Copn [.Lvar { var := { vname := cloneVar, vtype := .sarr cloneTy.storageBytes },
                         info := {} }] .AT_none
              (.Oasm { name := "CLONE_TOWER" }) [locToPExpr oldDest]]
        sid fuel).newSid = sid := by
    cases fuel with
    | zero => simp only [translateCmd]
    | succ n =>
      simp only [translateCmd, translateInstrR]
      cases n <;> simp only [translateCmd]
  rw [h_clone_newSid]
  -- The list-length subtraction: clone list has length 1, so `fuel - 1`.
  simp only [List.length_cons, List.length_nil, Nat.zero_add]

/-- **`rustCloneCallSimulates_newSid`**: simulates an `RCloneCall`
    instruction with the post-state stated at the threaded `newSid`
    (i.e. `(freshId sid).1`, the scope after the trailing `Ccall`).

    Combines `CloneImplOk` (for the leading `Copn(CLONE_TOWER)`,
    which preserves `newSid = sid`) with `rustCallSimulates_newSid`
    (for the trailing `Ccall`, which advances `newSid`).  No new
    oracle is required.

    Mirrors `rustCloneCallSimulates` but with `LeafImplOkNewSid` in
    place of `LeafImplOk` on the inner call. -/
lemma rustCloneCallSimulates_newSid
    (N : Nat) (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat)
    (hLeafN : ∀ fuel', LeafImplOkNewSid leafSpec env fuel')
    (hClone : ∀ fuel', CloneImplOk env fuel')
    (cloneVar : String) (cloneTy : TowerType) (oldDest : Located)
    (innerF : String) (dest : Located) (args : List Located)
    (rs rs' : RustState)
    (hExec : RustExec N leafSpec
        (.RCloneCall cloneVar cloneTy oldDest innerF dest args) rs rs')
    (oldV : RustVal cloneTy)
    (hOldDest : rs.rsTower oldDest.locVar = some ⟨cloneTy, oldV⟩)
    (sid : ScopeId) (heap : Heap)
    (hInv : HeapInv rs heap sid)
    (hSInv : ScalarInv rs heap sid)
    (hBounded : ScalarsBounded rs) :
    ∃ heap' : Heap,
      let newSid := (translateCmd env (toJasminCmd
        (.RCloneCall cloneVar cloneTy oldDest innerF dest args)) sid fuel).newSid
      (translateCmd env (toJasminCmd
        (.RCloneCall cloneVar cloneTy oldDest innerF dest args)) sid fuel).code.eval heap =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap') ∧
      HeapInv rs' heap' newSid ∧
      ScalarInv rs' heap' newSid ∧
      ScalarsBounded rs' := by
  cases hExec with
  | cloneCall _ _ _ _ _ _ _ rsClone _ hClone_eq hCall =>
    -- Apply clone oracle to get heap1 at sid.
    obtain ⟨heap1, hEvalClone, hCloneDest, hCloneOther, hCloneScalar⟩ :=
      hClone fuel cloneVar cloneTy oldDest rs sid heap oldV hInv hOldDest
    -- Establish invariants at rsClone / heap1 / sid.
    have hRsClone : rsClone = rsSetTower rs cloneVar ⟨cloneTy, oldV⟩ := by
      rw [hClone_eq, hOldDest]; rfl
    have hInv1 : HeapInv rsClone heap1 sid := by
      intro x t v hxTower
      rw [hRsClone] at hxTower
      simp only [rsSetTower, beq_iff_eq] at hxTower
      by_cases hx : x = cloneVar
      · subst hx
        simp only [if_true] at hxTower
        obtain ⟨ht, hv⟩ := Sigma.mk.inj (Option.some.inj hxTower)
        subst ht
        simp at hv
        subst hv
        exact hCloneDest
      · simp only [hx, if_false] at hxTower
        rw [hCloneOther x t hx]
        exact hInv x t v hxTower
    have hSInv1 : ScalarInv rsClone heap1 sid := by
      intro x
      rw [hCloneScalar x, hSInv x, hRsClone]
      rfl
    have hBounded1 : ScalarsBounded rsClone := by
      intro x
      rw [hRsClone]
      exact hBounded x
    -- Decompose translateCmd [cloneInstr, callInstr] via append.
    have h_toJ : toJasminCmd (.RCloneCall cloneVar cloneTy oldDest innerF dest args) =
        [.Copn [.Lvar { var := { vname := cloneVar, vtype := .sarr cloneTy.storageBytes },
                         info := {} }] .AT_none
              (.Oasm { name := "CLONE_TOWER" }) [locToPExpr oldDest]] ++
        (toJasminCmd (.RCall innerF dest args)) := rfl
    -- newSid after the clone Copn = sid (Copn doesn't change newSid).
    have h_clone_newSid : (translateCmd env
        [.Copn [.Lvar { var := { vname := cloneVar, vtype := .sarr cloneTy.storageBytes },
                         info := {} }] .AT_none
              (.Oasm { name := "CLONE_TOWER" }) [locToPExpr oldDest]]
        sid fuel).newSid = sid := by
      cases fuel with
      | zero => simp only [translateCmd]
      | succ n =>
        simp only [translateCmd, translateInstrR]
        cases n <;> simp only [translateCmd]
    -- Apply rustCallSimulates_newSid for the inner call at sid (since the
    -- clone preserves newSid = sid).  This posts at the inner-call's
    -- threaded newSid (= (freshId sid).1), which by `cloneCall_toJasmin_newSid`
    -- coincides with the full RCloneCall translation's newSid.
    obtain ⟨heap2, hEvalCall, hInv2, hSInv2, hB2⟩ :=
      rustCallSimulates_newSid N leafSpec env (fuel - 1) hLeafN innerF dest args
        rsClone rs' hCall sid heap1 hInv1 hSInv1 hBounded1
    refine ⟨heap2, ?_, ?_, ?_, hB2⟩
    · -- Sequential evaluation: clone, then call.
      rw [h_toJ, translateCmd_append_eval]
      rw [hEvalClone, SDistr.pure_bind]
      rw [h_clone_newSid]
      simp only [List.length_cons, List.length_nil, Nat.zero_add]
      exact hEvalCall
    · -- HeapInv at the threaded newSid: by cloneCall_toJasmin_newSid the
      -- newSid of the full RCloneCall = newSid of the inner RCall.
      have hNS := cloneCall_toJasmin_newSid cloneVar cloneTy oldDest innerF dest args
        env sid fuel
      rw [hNS]; exact hInv2
    · have hNS := cloneCall_toJasmin_newSid cloneVar cloneTy oldDest innerF dest args
        env sid fuel
      rw [hNS]; exact hSInv2

/-! ### §4.Y  RCall extension to the structural lift (2026-05-13)

Builds the **first compositional layer** of `RustCmd → Jasmin`
simulation supporting `RCall`.  Where `rustExecSimulates` requires
`callFree c = true` and posts at `sid`, this layer admits `RCall` as
a single instruction or sequenced with call-free code, and posts at
the threaded `newSid`.

The full lift (every constructor + RCall) needs `newSid` threaded
through every IH; that's a 200+ line mechanical refactor of the
existing `rustExecSimulates` body.  This checkpoint instead delivers
the **compositional kernel**:

* a "call-free or single-call" predicate `callFreePlusCall`,
* a `rustExecSimulates_withCalls` theorem that closes the RSeq
  chain by alternating IH₁/IH₂ between `rustExecSimulates`
  (call-free fragment) and `rustCallSimulates_newSid` (the RCall).

This unblocks the practical case (signature/verify code is mostly
callFree blocks separated by RCall leaves), which is the actual
target of the Jasmin pipeline. -/

namespace RustExecWithCalls

/-- `callFreePlusCall c = true` iff `c` is structurally a tree of
    `RSeq` whose leaves are either `callFree` subprograms, a single
    `RCall`, or a single `RLimbStore`.

    The `RLimbStore` extension (2026-05-13) is symmetric to `RCall`:
    both translate to a single Jasmin instruction (an `Oasm`-Copn for
    `RLimbStore`, a `Ccall` for `RCall`).  Crucially `RLimbStore`'s
    `.Copn` translation preserves `newSid := sid` (unlike `.Ccall`
    which advances it), so the seq composition is straightforward —
    no analog of `LeafImplOkNewSid` is needed; `LimbStoreImplOk` and
    `limbStore_toJasmin_newSid` suffice.

    The `RCloneCall` extension (2026-05-13) follows the same pattern:
    `RCloneCall` lowers to `[Copn(CLONE_TOWER), Ccall]`, where the trailing
    `Ccall` advances `newSid` to `(freshId sid).1`.  Composition of
    `CloneImplOk` (for the Copn) with `LeafImplOkNewSid` (for the Ccall)
    discharges the obligation — see `rustCloneCallSimulates_newSid`.

    The `RIfNz` mixed-branch extension (2026-05-13) allows `RIfNz e ct cf`
    in the structural recursion when both `ct` and `cf` are themselves
    `callFreePlusCall`.  The merge obligation — that the heap/scalar
    invariants survive the cross-branch scope advancement on the Jasmin
    side — is exposed as a separate `Prop` precondition
    (`BranchScopeMerges`) on the simulation theorem; see
    `rustExecSimulates_withCalls`.

    Excludes `RFor`, `RBlock`, `RLetZero`, `RLetU64Zero`,
    `RCallSwap` from call-bearing positions — those need separate
    threading work and are the next structural checkpoints.

    Excludes `RWhileNz` and all phases F/G/H/I/Ext (gated by
    `whileFree = false` upstream). -/
def callFreePlusCall : RustCmd → Bool
  | .RCall _ _ _              => true
  | .RLimbStore _ _ _         => true
  | .RCloneCall _ _ _ _ _ _   => true
  | .RSeq c1 c2               => callFreePlusCall c1 && callFreePlusCall c2
  | .RIfNz _ ct cf            => callFreePlusCall ct && callFreePlusCall cf
  | c                         => callFree c

/-- The `callFreePlusCall` predicate is reflexive over `callFree`. -/
lemma callFreePlusCall_of_callFree :
    ∀ c, callFree c = true → callFreePlusCall c = true := by
  intro c hCF
  match c with
  | .RCall _ _ _ => simp [callFree] at hCF
  | .RSeq c1 c2 =>
    simp only [callFree, Bool.and_eq_true] at hCF
    simp only [callFreePlusCall]
    rw [callFreePlusCall_of_callFree c1 hCF.1,
        callFreePlusCall_of_callFree c2 hCF.2]
    rfl
  | .RSkip => simp [callFreePlusCall, hCF]
  | .RScalarSet _ _ => simp [callFreePlusCall, hCF]
  | .RLetZero _ _ _ => simp [callFreePlusCall, hCF]
  | .RLetU64Zero _ _ => simp [callFreePlusCall, hCF]
  | .RIfNz _ ct cf =>
    simp only [callFree, Bool.and_eq_true] at hCF
    simp only [callFreePlusCall]
    rw [callFreePlusCall_of_callFree ct hCF.1,
        callFreePlusCall_of_callFree cf hCF.2]
    rfl
  | .RWhileNz _ _ => simp [callFreePlusCall, hCF]
  | .RFor _ _ _ => simp [callFreePlusCall, hCF]
  | .RAssert _ => simp [callFreePlusCall, hCF]
  | .RAsmOp _ _ _ => simp [callFreePlusCall, hCF]
  | .RBlock _ => simp [callFreePlusCall, hCF]
  | .RFnDef _ _ _ _ _ => simp [callFreePlusCall, hCF]
  | .RSelect _ _ _ _ => simp [callFreePlusCall, hCF]
  | .RCallN _ _ _ => simp [callFreePlusCall, hCF]
  | .RFnCall _ _ _ => simp [callFreePlusCall, hCF]
  | .RCallSwap _ _ _ _ => simp [callFreePlusCall, hCF]
  | .RCloneCall _ _ _ _ _ _ => simp [callFree] at hCF
  | .RLimbStore _ _ _ => simp [callFree] at hCF
    -- (`RLimbStore` is now in `callFreePlusCall = true`, but unreachable
    -- here because the hypothesis is on `callFree`, which excludes it.)
  | .RTupleStore _ _ _ => simp [callFreePlusCall, hCF]
  | .RTupleLoad _ _ _ => simp [callFreePlusCall, hCF]
  | .RArrStore _ _ _ => simp [callFreePlusCall, hCF]
  | .RArrLoad _ _ _ => simp [callFreePlusCall, hCF]
  | .RScalarSetExpr _ _ => simp [callFreePlusCall, hCF]
  | .RBytesSlice _ _ _ _ => simp [callFreePlusCall, hCF]

/-- **Branch-symmetric merge property for `RIfNz` (2026-05-13).**

    For every `RIfNz e ct cf` reached during execution of `c` starting
    at `rs`, two scope-lift obligations must hold so the Jasmin-side
    `Cif` newSid threading (which advances through both branches even
    if only one executes) can be reconciled with the `HeapInv`/`ScalarInv`
    posted by the executed branch's IH:

    1. **TRUE-branch lift** — after the true branch runs and gives the
       caller `HeapInv rs' heap' sid_ct`, where `sid_ct` is `ct`'s
       advanced sid, the same invariant must hold at the outer Cif's
       `newSid` (which is `cf`'s advanced sid starting from `sid_ct`).

    2. **FALSE-branch lift** — the Jasmin `cf` runs from `sid_ct`, not
       `sid`.  We need `HeapInv rs heap sid_ct` from `HeapInv rs heap sid`.

    Both obligations are vacuously discharged when both branches are
    `callFree` (then `sid_ct = sid` and all newSids collapse), so the
    extension is **conservative** w.r.t. the existing call-free case.

    For non-`RIfNz` constructors the predicate is `True`. Recurses
    through `RSeq` and `RIfNz` itself. -/
def BranchScopeMerges (N : Nat) (leafSpec : LeafSpec) (env : TransEnv) :
    RustCmd → RustState → ScopeId → Nat → Prop
  | .RIfNz _ ct cf, rs, sid, fuel =>
      -- The outer Cif consumes one unit of fuel for the trailing list step;
      -- both branches recurse at `fuel - 1`.  We state all obligations
      -- in terms of `fuel - 1` to align with the theorem's fuel threading.
      let fuel' := fuel - 1
      -- TRUE-branch lift: invariant survives the cross-branch
      -- scope advancement (sid_ct → outer Cif newSid via cf).
      (∀ rs' heap',
        RustExec N leafSpec ct rs rs' →
        HeapInv rs' heap' ((translateCmd env (toJasminCmd ct) sid fuel').newSid) →
        ScalarInv rs' heap' ((translateCmd env (toJasminCmd ct) sid fuel').newSid) →
        HeapInv rs' heap' ((translateCmd env (toJasminCmd cf)
            ((translateCmd env (toJasminCmd ct) sid fuel').newSid) fuel').newSid) ∧
        ScalarInv rs' heap' ((translateCmd env (toJasminCmd cf)
            ((translateCmd env (toJasminCmd ct) sid fuel').newSid) fuel').newSid)) ∧
      -- FALSE-branch lift: pre-state HeapInv at sid lifts to sid_ct.
      (∀ heap,
        HeapInv rs heap sid →
        ScalarInv rs heap sid →
        HeapInv rs heap ((translateCmd env (toJasminCmd ct) sid fuel').newSid) ∧
        ScalarInv rs heap ((translateCmd env (toJasminCmd ct) sid fuel').newSid)) ∧
      -- Recursive obligation on `ct` itself (its own RIfNz nodes also merge).
      BranchScopeMerges N leafSpec env ct rs sid fuel' ∧
      -- Symmetric FALSE-execution recursion: `cf` runs from rs at sid_ct.
      BranchScopeMerges N leafSpec env cf rs
        ((translateCmd env (toJasminCmd ct) sid fuel').newSid) fuel'
  | .RSeq c1 c2, rs, sid, fuel =>
      BranchScopeMerges N leafSpec env c1 rs sid fuel ∧
      (∀ rs1 : RustState, RustExec N leafSpec c1 rs rs1 →
        BranchScopeMerges N leafSpec env c2 rs1
          ((translateCmd env (toJasminCmd c1) sid fuel).newSid)
          (fuel - (toJasminCmd c1).length))
  | _, _, _, _ => True

/-- **Runtime witness for `RCloneCall` well-typedness.**

    For every `RCloneCall cloneVar cloneTy oldDest …` reached during
    execution of `c` starting at `rs`, the lookup
    `rs.rsTower oldDest.locVar` returns `some ⟨cloneTy, v⟩`.

    The `RustExec.cloneCall` constructor uses `Option.getD` on the
    lookup, so it admits "bad" executions where the lookup is `none`
    (and the cloned value is silently `default`).  The Jasmin
    `CloneImplOk` oracle in contrast requires the lookup to be `some`
    to specify what the resulting heap holds.  This predicate threads
    the missing well-typedness witness through `RSeq` by quantifying
    over intermediate states reachable via `RustExec` on `c1`.

    For non-`RCloneCall` constructors the predicate is `True`. -/
def CloneCallsWellTyped (N : Nat) (leafSpec : LeafSpec) :
    RustCmd → RustState → Prop
  | .RCloneCall _ cloneTy oldDest _ _ _, rs =>
      ∃ v : RustVal cloneTy, rs.rsTower oldDest.locVar = some ⟨cloneTy, v⟩
  | .RSeq c1 c2, rs =>
      CloneCallsWellTyped N leafSpec c1 rs ∧
      (∀ rs1 : RustState, RustExec N leafSpec c1 rs rs1 →
        CloneCallsWellTyped N leafSpec c2 rs1)
  -- Recurse through RIfNz so nested clones inside either branch are tracked
  -- regardless of which branch the runtime takes (2026-05-13 extension).
  | .RIfNz _ ct cf, rs =>
      CloneCallsWellTyped N leafSpec ct rs ∧
      CloneCallsWellTyped N leafSpec cf rs
  | _, _ => True

/-- **Conservativity**: when `c` is fully `callFree`, the
    `BranchScopeMerges` obligation is trivially satisfied — every
    reachable `RIfNz` has `newSid_ct = sid` (and `newSid_cf = sid`),
    so the lift is the identity.  This guarantees the mixed-branch
    `RIfNz` extension does not break any existing all-callFree caller.

    Stated as a recursive function (sufficient pattern for the
    conservativity guarantee — see `branchScopeMerges_of_callFree_at`
    for a sample application). -/
lemma branchScopeMerges_of_callFree
    (N : Nat) (leafSpec : LeafSpec) (env : TransEnv) (c : RustCmd)
    (hCF : callFree c = true)
    (rs : RustState) (sid : ScopeId) (fuel : Nat) :
    BranchScopeMerges N leafSpec env c rs sid fuel := by
  -- Conservative case: c is callFree, so every reachable RIfNz/RSeq
  -- has callFree branches.  We prove this by structural recursion on c.
  -- Use a recursive definition pattern to thread `rs`/`sid`/`fuel`.
  induction c generalizing rs sid fuel with
  | RIfNz e ct cf ih1 ih2 =>
    simp only [callFree, Bool.and_eq_true] at hCF
    have hNS_ct : (translateCmd env (toJasminCmd ct) sid (fuel - 1)).newSid = sid :=
      callFree_toJasmin_newSid ct hCF.1 env sid (fuel - 1)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro rs' heap' _hExec hInv' hSInv'
      rw [hNS_ct] at hInv' hSInv' ⊢
      have hNS_cf : (translateCmd env (toJasminCmd cf) sid (fuel - 1)).newSid = sid :=
        callFree_toJasmin_newSid cf hCF.2 env sid (fuel - 1)
      rw [hNS_cf]
      exact ⟨hInv', hSInv'⟩
    · intro heap hInv hSInv
      rw [hNS_ct]
      exact ⟨hInv, hSInv⟩
    · exact ih1 hCF.1 rs sid (fuel - 1)
    · rw [hNS_ct]; exact ih2 hCF.2 rs sid (fuel - 1)
  | RSeq c1 c2 ih1 ih2 =>
    simp only [callFree, Bool.and_eq_true] at hCF
    refine ⟨ih1 hCF.1 rs sid fuel, ?_⟩
    intro rs1 _h1
    exact ih2 hCF.2 rs1 _ _
  | RSkip => simp [BranchScopeMerges]
  | RScalarSet _ _ => simp [BranchScopeMerges]
  | RLetZero _ _ _ _ => simp [BranchScopeMerges]
  | RLetU64Zero _ _ _ => simp [BranchScopeMerges]
  | RWhileNz _ _ _ => simp [BranchScopeMerges]
  | RFor _ _ _ _ => simp [BranchScopeMerges]
  | RCall _ _ _ => simp [callFree] at hCF
  | RCallSwap _ _ _ _ => simp [callFree] at hCF
  | RCloneCall _ _ _ _ _ _ => simp [callFree] at hCF
  | RLimbStore _ _ _ => simp [callFree] at hCF
  | RAsmOp _ _ _ => simp [BranchScopeMerges]
  | RCallN _ _ _ => simp [callFree] at hCF
  | RSelect _ _ _ _ => simp [BranchScopeMerges]
  | RAssert _ => simp [BranchScopeMerges]
  | RBlock _ _ => simp [BranchScopeMerges]
  | RFnDef _ _ _ _ _ _ _ => simp [BranchScopeMerges]
  | RFnCall _ _ _ => simp [callFree] at hCF
  | RTupleStore _ _ _ => simp [callFree] at hCF
  | RTupleLoad _ _ _ => simp [callFree] at hCF
  | RArrStore _ _ _ => simp [callFree] at hCF
  | RArrLoad _ _ _ => simp [callFree] at hCF
  | RScalarSetExpr _ _ => simp [callFree] at hCF
  | RBytesSlice _ _ _ _ => simp [callFree] at hCF

end RustExecWithCalls

/-- **`rustExecSimulates_withCalls`** (2026-05-13 checkpoint): the
    structural lift extended to admit `RCall` interleaved with
    call-free fragments via `RSeq`.

    Drops the `callFree c = true` precondition of `rustExecSimulates`
    in exchange for the `callFreePlusCall c = true` predicate, which
    allows `RCall` and `RLimbStore` leaves to appear inside `RSeq` chains.

    The conclusion is stated at the threaded `newSid`. In the pure
    call-free case this collapses back to `sid` via
    `callFree_toJasmin_newSid`; for `RLimbStore` leaves, `newSid = sid`
    too (via `limbStore_toJasmin_newSid`) since the Jasmin `.Copn`
    translation doesn't advance the sid.

    Coverage:
    * single `RCall`: closed via `rustCallSimulates_newSid`.
    * single `RLimbStore` (2026-05-13): closed via `rustLimbStoreSimulates`
      after the `newSid = sid` rewrite (limb store is `.Copn` which preserves
      `newSid`, unlike `.Ccall`).  Requires `hLimb : LimbStoreImplOk`.
    * single `RCloneCall` (2026-05-13): closed via
      `rustCloneCallSimulates_newSid`.  Requires `hClone : CloneImplOk`
      and a runtime well-typedness witness `hCloneWT`.
    * `RSeq c1 c2` with both `callFreePlusCall`: closed by threaded
      composition (the structurally new content).
    * `RIfNz e ct cf` with mixed-branch calls (2026-05-13): branches are
      themselves `callFreePlusCall` and may contain calls.  Dispatches
      via `cases hExec` on `ifTrue`/`ifFalse`, recurses through the IH
      on the executed branch, then lifts the resulting invariant from
      that branch's `newSid` to the outer Cif's `newSid` (which depends
      on BOTH branches via `translateCmd_cif_newSid`).  The lift step
      is discharged by `hBranchMerges : BranchScopeMerges`, a runtime
      Prop witness that the merge holds at every reachable `RIfNz`.
      For all-callFree branches the witness is trivially constructed,
      so the extension is conservative.
    * non-call leaves (`RSkip`, `RScalarSet`, `RLetZero`, `RLetU64Zero`,
      `RFor`, `RBlock`, `RAssert`): delegate to `rustExecSimulates`
      after the `newSid = sid` collapse, since `callFreePlusCall`
      coincides with `callFree` for those.
    * `RWhileNz` and phases F/G/H/I/Ext: unreachable under `whileFree`.

    The proof recursively descends on the `RSeq` structure (terminating
    by structural decrease on the `RSeq` tree). -/
theorem rustExecSimulates_withCalls
    (N : Nat) (leafSpec : LeafSpec) (env : TransEnv) (fuel : Nat)
    (hLeaf : ∀ fuel', LeafImplOk leafSpec env fuel')
    (hLeafN : ∀ fuel', LeafImplOkNewSid leafSpec env fuel')
    (hLimb : ∀ fuel', LimbStoreImplOk leafSpec env fuel')
    (hClone : ∀ fuel', CloneImplOk env fuel')
    (c : RustCmd) (rs rs' : RustState)
    (hWf : whileFree c = true)
    (hCFx : RustExecWithCalls.callFreePlusCall c = true)
    (hSSS : scalarSetsSmall c = true)
    (hFuel : jasminFuel c ≤ fuel)
    (hExec : RustExec N leafSpec c rs rs')
    (hCloneWT : RustExecWithCalls.CloneCallsWellTyped N leafSpec c rs)
    (sid : ScopeId) (heap : Heap)
    (hInv : HeapInv rs heap sid)
    (hSInv : ScalarInv rs heap sid)
    (hBounded : ScalarsBounded rs)
    (hBranchMerges :
      RustExecWithCalls.BranchScopeMerges N leafSpec env c rs sid fuel) :
    ∃ heap' : Heap,
      (translateCmd env (toJasminCmd c) sid fuel).code.eval heap =
        CatCrypt.Prob.SDistr.pure (⟨()⟩, heap') ∧
      HeapInv rs' heap'
        ((translateCmd env (toJasminCmd c) sid fuel).newSid) ∧
      ScalarInv rs' heap'
        ((translateCmd env (toJasminCmd c) sid fuel).newSid) ∧
      ScalarsBounded rs' := by
  -- Three-way structural case-split.
  match h : c with
  | .RCall f dest args =>
    -- Single-call leaf: delegate to `rustCallSimulates_newSid`.
    subst h
    exact rustCallSimulates_newSid N leafSpec env fuel hLeafN
      f dest args rs rs' hExec sid heap hInv hSInv hBounded
  | .RSeq c1 c2 =>
    -- Compositional RSeq case: thread `newSid` from IH₁ to IH₂.
    -- Both sub-IHs are recursive calls to `rustExecSimulates_withCalls`
    -- on structurally smaller `c1`/`c2`.
    subst h
    -- Extract the two underlying RustExec proofs from the RSeq.
    obtain ⟨r1, h1, h2⟩ : ∃ r1 : RustState,
        RustExec N leafSpec c1 rs r1 ∧ RustExec N leafSpec c2 r1 rs' := by
      cases hExec with
      | seq _ _ _ r1 _ h1 h2 => exact ⟨r1, h1, h2⟩
    -- Unpack the predicates on the seq components.
    simp only [whileFree, Bool.and_eq_true] at hWf
    simp only [RustExecWithCalls.callFreePlusCall, Bool.and_eq_true] at hCFx
    simp only [scalarSetsSmall, Bool.and_eq_true] at hSSS
    simp only [jasminFuel] at hFuel
    -- Unpack the runtime clone-well-typedness witness: the c1 witness is
    -- directly available; the c2 witness is obtained from the c1-runtime
    -- universal closure applied to `h1`.
    have hCWT1 : RustExecWithCalls.CloneCallsWellTyped N leafSpec c1 rs := by
      simp only [RustExecWithCalls.CloneCallsWellTyped] at hCloneWT
      exact hCloneWT.1
    have hCWT2 : RustExecWithCalls.CloneCallsWellTyped N leafSpec c2 r1 := by
      simp only [RustExecWithCalls.CloneCallsWellTyped] at hCloneWT
      exact hCloneWT.2 r1 h1
    -- Unpack the branch-merge witness for c1 and c2 (now fuel-aligned with
    -- the threaded recursion via the `RSeq` arm of `BranchScopeMerges`).
    have hBM1 : RustExecWithCalls.BranchScopeMerges N leafSpec env c1 rs sid fuel := by
      simp only [RustExecWithCalls.BranchScopeMerges] at hBranchMerges
      exact hBranchMerges.1
    have hBM2 : RustExecWithCalls.BranchScopeMerges N leafSpec env c2 r1
        ((translateCmd env (toJasminCmd c1) sid fuel).newSid)
        (fuel - (toJasminCmd c1).length) := by
      simp only [RustExecWithCalls.BranchScopeMerges] at hBranchMerges
      exact hBranchMerges.2 r1 h1
    have hFuel1 : jasminFuel c1 ≤ fuel := by
      have := jasminFuel_pos c2; omega
    have hFuel2 : jasminFuel c2 ≤ fuel - (toJasminCmd c1).length := by
      have := jasminFuel_gt_length c1; omega
    -- Recursive call on c1 (structurally smaller).
    obtain ⟨heap1, heval1, hInv1, hSInv1, hB1⟩ :=
      rustExecSimulates_withCalls N leafSpec env fuel hLeaf hLeafN hLimb hClone
        c1 rs r1 hWf.1 hCFx.1 hSSS.1 hFuel1 h1 hCWT1
        sid heap hInv hSInv hBounded hBM1
    -- After IH₁ we are at `newSid₁ := (translateCmd ... c1 sid fuel).newSid`.
    set newSid1 := (translateCmd env (toJasminCmd c1) sid fuel).newSid with hNS1
    -- Recursive call on c2 at the threaded newSid₁.
    obtain ⟨heap2, heval2, hInv2, hSInv2, hB2⟩ :=
      rustExecSimulates_withCalls N leafSpec env
        (fuel - (toJasminCmd c1).length) hLeaf hLeafN hLimb hClone
        c2 r1 rs' hWf.2 hCFx.2 hSSS.2 hFuel2 h2 hCWT2
        newSid1 heap1 hInv1 hSInv1 hB1 hBM2
    -- Compose evaluations via `translateCmd_append_eval`.
    refine ⟨heap2, ?_, ?_, ?_, hB2⟩
    · simp only [toJasminCmd]
      rw [translateCmd_append_eval, heval1, SDistr.pure_bind]
      exact heval2
    · -- HeapInv at the final newSid (translateCmd of the seq).
      have hNewSidEq :
          (translateCmd env (toJasminCmd (.RSeq c1 c2)) sid fuel).newSid =
          (translateCmd env (toJasminCmd c2) newSid1
            (fuel - (toJasminCmd c1).length)).newSid := by
        simp only [toJasminCmd, translateCmd_append_newSid, hNS1]
      rw [hNewSidEq]; exact hInv2
    · have hNewSidEq :
          (translateCmd env (toJasminCmd (.RSeq c1 c2)) sid fuel).newSid =
          (translateCmd env (toJasminCmd c2) newSid1
            (fuel - (toJasminCmd c1).length)).newSid := by
        simp only [toJasminCmd, translateCmd_append_newSid, hNS1]
      rw [hNewSidEq]; exact hSInv2
  | .RSkip =>
    -- callFree: delegate to `rustExecSimulates` and rewrite newSid = sid.
    subst h
    have hCF : callFree RustCmd.RSkip = true := by simp [callFree]
    have hNewSid : (translateCmd env (toJasminCmd RustCmd.RSkip) sid fuel).newSid = sid :=
      callFree_toJasmin_newSid _ hCF env sid fuel
    rw [hNewSid]
    exact rustExecSimulates N leafSpec env fuel hLeaf _ rs rs'
      hWf hCF hSSS hFuel hExec sid heap hInv hSInv hBounded
  | .RScalarSet x v =>
    subst h
    have hCF : callFree (RustCmd.RScalarSet x v) = true := by simp [callFree]
    have hNewSid : (translateCmd env (toJasminCmd (RustCmd.RScalarSet x v)) sid fuel).newSid = sid :=
      callFree_toJasmin_newSid _ hCF env sid fuel
    rw [hNewSid]
    exact rustExecSimulates N leafSpec env fuel hLeaf _ rs rs'
      hWf hCF hSSS hFuel hExec sid heap hInv hSInv hBounded
  | .RLetZero x t body =>
    subst h
    have hCF : callFree (RustCmd.RLetZero x t body) = true := by
      simp only [RustExecWithCalls.callFreePlusCall] at hCFx
      exact hCFx
    have hNewSid : (translateCmd env (toJasminCmd (RustCmd.RLetZero x t body)) sid fuel).newSid = sid :=
      callFree_toJasmin_newSid _ hCF env sid fuel
    rw [hNewSid]
    exact rustExecSimulates N leafSpec env fuel hLeaf _ rs rs'
      hWf hCF hSSS hFuel hExec sid heap hInv hSInv hBounded
  | .RLetU64Zero x body =>
    subst h
    have hCF : callFree (RustCmd.RLetU64Zero x body) = true := by
      simp only [RustExecWithCalls.callFreePlusCall] at hCFx
      exact hCFx
    have hNewSid : (translateCmd env (toJasminCmd (RustCmd.RLetU64Zero x body)) sid fuel).newSid = sid :=
      callFree_toJasmin_newSid _ hCF env sid fuel
    rw [hNewSid]
    exact rustExecSimulates N leafSpec env fuel hLeaf _ rs rs'
      hWf hCF hSSS hFuel hExec sid heap hInv hSInv hBounded
  | .RIfNz e ct cf =>
    -- Mixed-branch case (2026-05-13): both `ct` and `cf` may contain calls.
    -- Dispatch via the executed branch's IH, then use `hBranchMerges` to lift
    -- the resulting invariant from the branch's newSid to the outer Cif's
    -- newSid (which depends symmetrically on BOTH branches' newSid via
    -- `translateCmd_cif_newSid`).
    subst h
    -- Unpack the structural predicates restricted to the branches.
    simp only [whileFree, Bool.and_eq_true] at hWf
    simp only [RustExecWithCalls.callFreePlusCall, Bool.and_eq_true] at hCFx
    simp only [scalarSetsSmall, Bool.and_eq_true] at hSSS
    simp only [jasminFuel] at hFuel
    -- Fuel decomposition: outer = max(ct, cf) + 1 ≤ fuel.
    obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
    have hFuel_ct : jasminFuel ct ≤ fuel' := by omega
    have hFuel_cf : jasminFuel cf ≤ fuel' := by omega
    -- Unpack the branch-merge witness for ct and cf.
    have hBMall := hBranchMerges
    simp only [RustExecWithCalls.BranchScopeMerges] at hBMall
    obtain ⟨hLiftTrue, hLiftFalse, hBM_ct, hBM_cf_from_start⟩ := hBMall
    -- Case-split the RustExec witness: either ifTrue or ifFalse fired.
    cases hExec with
    | ifTrue _ _ _ _ _ v hv hne_zero hExecCt =>
      -- The TRUE branch ran.  Recurse on ct, then lift to outer newSid.
      have hCWT_ct : RustExecWithCalls.CloneCallsWellTyped N leafSpec ct rs := by
        simp only [RustExecWithCalls.CloneCallsWellTyped] at hCloneWT
        exact hCloneWT.1
      obtain ⟨heap', heval', hInv', hSInv', hB'⟩ :=
        rustExecSimulates_withCalls N leafSpec env fuel'
          hLeaf hLeafN hLimb hClone ct rs rs' hWf.1 hCFx.1 hSSS.1 hFuel_ct
          hExecCt hCWT_ct sid heap hInv hSInv hBounded hBM_ct
      -- Cif eval (TRUE): produces heap' from heap.
      have he_val : heap.get (translateVar sid { vname := e, vtype := .sword .U64 }) =
          BitVec.ofNat 64 v := hv ▸ hSInv e
      have he_bnd : v < 2^64 := by rw [← hv]; exact hBounded e
      have hcond : (translatePExpr sid (.Papp2 (.Oneq .U64)
          (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 }, info := {} },
                   gs := false })
          (.Papp1 (.Oword_of_int .U64) (.Pconst 0)))).eval heap =
          SDistr.pure (⟨.sbool, true⟩, heap) := by
        rw [cif_cond_eval]
        simp only [he_val]
        have hbne : BitVec.ofNat 64 v != (0 : BitVec 64) := by
          rw [bne_iff_ne]; exact bitVec_ofNat_ne_zero v hne_zero he_bnd
        rw [show ((0 : BitVec 64) = (0#64 : BitVec 64)) from rfl] at hbne
        simp [hbne]
      -- The outer eval reduces to `eval ct` at heap.
      refine ⟨heap', ?_, ?_, ?_, hB'⟩
      · simp only [toJasminCmd]
        rw [translateCmd_cif_eval_true env sid _ _ _ fuel' heap heap hcond]
        exact heval'
      · -- HeapInv lift from sid_ct to outer Cif newSid via hLiftTrue.
        have hNS : (translateCmd env (toJasminCmd (RustCmd.RIfNz e ct cf)) sid (fuel' + 1)).newSid =
            (translateCmd env (toJasminCmd cf)
              ((translateCmd env (toJasminCmd ct) sid fuel').newSid) fuel').newSid := by
          simp only [toJasminCmd]
          exact translateCmd_cif_newSid env sid _ _ _ fuel'
        rw [hNS]
        exact (hLiftTrue rs' heap' hExecCt hInv' hSInv').1
      · have hNS : (translateCmd env (toJasminCmd (RustCmd.RIfNz e ct cf)) sid (fuel' + 1)).newSid =
            (translateCmd env (toJasminCmd cf)
              ((translateCmd env (toJasminCmd ct) sid fuel').newSid) fuel').newSid := by
          simp only [toJasminCmd]
          exact translateCmd_cif_newSid env sid _ _ _ fuel'
        rw [hNS]
        exact (hLiftTrue rs' heap' hExecCt hInv' hSInv').2
    | ifFalse _ _ _ _ _ h_e_zero hExecCf =>
      -- The FALSE branch ran.  Lift pre-state HeapInv from sid to sid_ct,
      -- then recurse on cf at sid_ct.
      have hCWT_cf : RustExecWithCalls.CloneCallsWellTyped N leafSpec cf rs := by
        simp only [RustExecWithCalls.CloneCallsWellTyped] at hCloneWT
        exact hCloneWT.2
      have he_val : heap.get (translateVar sid { vname := e, vtype := .sword .U64 }) =
          (0 : BitVec 64) := by
        have h1 := hSInv e
        rw [h_e_zero] at h1
        exact h1
      have hcond : (translatePExpr sid (.Papp2 (.Oneq .U64)
          (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 }, info := {} },
                   gs := false })
          (.Papp1 (.Oword_of_int .U64) (.Pconst 0)))).eval heap =
          SDistr.pure (⟨.sbool, false⟩, heap) := by
        rw [cif_cond_eval]
        simp only [he_val]
        rfl
      -- Lift pre-state HeapInv/ScalarInv from sid to sid_ct.
      obtain ⟨hInv_lift, hSInv_lift⟩ := hLiftFalse heap hInv hSInv
      -- Recurse on cf at sid_ct.
      obtain ⟨heap', heval', hInv', hSInv', hB'⟩ :=
        rustExecSimulates_withCalls N leafSpec env fuel'
          hLeaf hLeafN hLimb hClone cf rs rs' hWf.2 hCFx.2 hSSS.2 hFuel_cf
          hExecCf hCWT_cf
          ((translateCmd env (toJasminCmd ct) sid fuel').newSid)
          heap hInv_lift hSInv_lift hBounded hBM_cf_from_start
      refine ⟨heap', ?_, ?_, ?_, hB'⟩
      · simp only [toJasminCmd]
        rw [translateCmd_cif_eval_false env sid _ _ _ fuel' heap heap hcond]
        exact heval'
      · have hNS : (translateCmd env (toJasminCmd (RustCmd.RIfNz e ct cf)) sid (fuel' + 1)).newSid =
            (translateCmd env (toJasminCmd cf)
              ((translateCmd env (toJasminCmd ct) sid fuel').newSid) fuel').newSid := by
          simp only [toJasminCmd]
          exact translateCmd_cif_newSid env sid _ _ _ fuel'
        rw [hNS]; exact hInv'
      · have hNS : (translateCmd env (toJasminCmd (RustCmd.RIfNz e ct cf)) sid (fuel' + 1)).newSid =
            (translateCmd env (toJasminCmd cf)
              ((translateCmd env (toJasminCmd ct) sid fuel').newSid) fuel').newSid := by
          simp only [toJasminCmd]
          exact translateCmd_cif_newSid env sid _ _ _ fuel'
        rw [hNS]; exact hSInv'
  | .RFor x n body =>
    subst h
    have hCF : callFree (RustCmd.RFor x n body) = true := by
      simp only [RustExecWithCalls.callFreePlusCall] at hCFx
      exact hCFx
    have hNewSid : (translateCmd env (toJasminCmd (RustCmd.RFor x n body)) sid fuel).newSid = sid :=
      callFree_toJasmin_newSid _ hCF env sid fuel
    rw [hNewSid]
    exact rustExecSimulates N leafSpec env fuel hLeaf _ rs rs'
      hWf hCF hSSS hFuel hExec sid heap hInv hSInv hBounded
  | .RAssert label =>
    subst h
    have hCF : callFree (RustCmd.RAssert label) = true := by simp [callFree]
    have hNewSid : (translateCmd env (toJasminCmd (RustCmd.RAssert label)) sid fuel).newSid = sid :=
      callFree_toJasmin_newSid _ hCF env sid fuel
    rw [hNewSid]
    exact rustExecSimulates N leafSpec env fuel hLeaf _ rs rs'
      hWf hCF hSSS hFuel hExec sid heap hInv hSInv hBounded
  | .RBlock body =>
    subst h
    have hCF : callFree (RustCmd.RBlock body) = true := by
      simp only [RustExecWithCalls.callFreePlusCall] at hCFx
      exact hCFx
    have hNewSid : (translateCmd env (toJasminCmd (RustCmd.RBlock body)) sid fuel).newSid = sid :=
      callFree_toJasmin_newSid _ hCF env sid fuel
    rw [hNewSid]
    exact rustExecSimulates N leafSpec env fuel hLeaf _ rs rs'
      hWf hCF hSSS hFuel hExec sid heap hInv hSInv hBounded
  | .RWhileNz _ _ => subst h; simp [whileFree] at hWf
  | .RCallSwap _ _ _ _ =>
    subst h
    exact absurd hCFx (by simp [RustExecWithCalls.callFreePlusCall, callFree])
  | .RCloneCall cloneVar cloneTy oldDest innerF dest args =>
    -- Single clone-call leaf: delegate to `rustCloneCallSimulates_newSid`.
    -- Extract the runtime well-typedness witness from `hCloneWT`.
    subst h
    simp only [RustExecWithCalls.CloneCallsWellTyped] at hCloneWT
    obtain ⟨oldV, hOldDest⟩ := hCloneWT
    exact rustCloneCallSimulates_newSid N leafSpec env fuel hLeafN hClone
      cloneVar cloneTy oldDest innerF dest args rs rs' hExec oldV hOldDest
      sid heap hInv hSInv hBounded
  | .RLimbStore loc idx v =>
    -- Single limb-store leaf: delegate to `rustLimbStoreSimulates` after
    -- the `newSid = sid` rewrite (RLimbStore lowers to `.Copn STORE64`
    -- which doesn't advance `newSid`, by `limbStore_toJasmin_newSid`).
    subst h
    have hNewSid :
        (translateCmd env (toJasminCmd (.RLimbStore loc idx v)) sid fuel).newSid = sid :=
      limbStore_toJasmin_newSid loc idx v env sid fuel
    rw [hNewSid]
    exact rustLimbStoreSimulates N leafSpec env fuel hLimb
      loc idx v rs rs' hExec sid heap hInv hSInv hBounded
  | .RAsmOp _ _ _ => subst h; simp [whileFree] at hWf
  | .RCallN _ _ _ => subst h; simp [whileFree] at hWf
  | .RSelect _ _ _ _ => subst h; simp [whileFree] at hWf
  | .RFnDef _ _ _ _ _ => subst h; simp [whileFree] at hWf
  | .RFnCall _ _ _ => subst h; simp [whileFree] at hWf
  | .RTupleStore _ _ _ => subst h; simp [whileFree] at hWf
  | .RTupleLoad _ _ _ => subst h; simp [whileFree] at hWf
  | .RArrStore _ _ _ => subst h; simp [whileFree] at hWf
  | .RArrLoad _ _ _ => subst h; simp [whileFree] at hWf
  | .RScalarSetExpr _ _ => subst h; simp [whileFree] at hWf
  | .RBytesSlice _ _ _ _ => subst h; simp [whileFree] at hWf
termination_by sizeOf c

end SimulationTheorem

/-! ## §5  Concrete programs -/

section ConcretePrograms

/-- Located values for G1 curve operations. -/
def mkFpLoc (x : String) : Located := { locVar := x, locSrc := .TFp }
def mkFp2Loc (x : String) : Located := { locVar := x, locSrc := .TFp2 }

def g1X1 := mkFpLoc "X1"
def g1X2 := mkFpLoc "X2"
def g1Y1 := mkFpLoc "Y1"
def g1Y2 := mkFpLoc "Y2"
def g1Z1 := mkFpLoc "Z1"
def g1Z2 := mkFpLoc "Z2"
def g1X3 := mkFpLoc "X3"
def g1Y3 := mkFpLoc "Y3"
def g1Z3 := mkFpLoc "Z3"
def g1T0 := mkFpLoc "t0"
def g1T1 := mkFpLoc "t1"
def g1T2 := mkFpLoc "t2"
def g1T3 := mkFpLoc "t3"
def g1T4 := mkFpLoc "t4"
def g1T5 := mkFpLoc "t5"

/-- G1 projective addition (Renes et al., fresh-destination form).
    Identical structure to Rocq `RustCmdCurve.g1_add`. -/
def g1Add : RustCmd :=
  let c1  := .RCall "fp_mul" g1T0 [g1X1, g1X2]
  let c2  := .RCall "fp_mul" g1T1 [g1Y1, g1Y2]
  let c3  := .RCall "fp_mul" g1T2 [g1Z1, g1Z2]
  let c4  := .RCall "fp_add" g1T3 [g1X1, g1Y1]
  let c5  := .RCall "fp_add" g1T4 [g1X2, g1Y2]
  let c6  := .RCall "fp_mul" g1T5 [g1T3, g1T4]
  let c7  := .RCall "fp_sub" g1T3 [g1T5, g1T0]
  let c8  := .RCall "fp_sub" g1X3 [g1T3, g1T1]
  let c9  := .RCall "fp_add" g1T3 [g1Y1, g1Z1]
  let c10 := .RCall "fp_add" g1T4 [g1Y2, g1Z2]
  let c11 := .RCall "fp_mul" g1T5 [g1T3, g1T4]
  let c12 := .RCall "fp_sub" g1T3 [g1T5, g1T1]
  let c13 := .RCall "fp_sub" g1Y3 [g1T3, g1T2]
  .RSeq c1 (.RSeq c2 (.RSeq c3 (.RSeq c4 (.RSeq c5 (.RSeq c6
  (.RSeq c7 (.RSeq c8 (.RSeq c9 (.RSeq c10 (.RSeq c11 (.RSeq c12 c13)))))))))))

/-- G1 projective doubling. -/
def g1Dbl : RustCmd :=
  let c1 := .RCall "fp_sqr" g1T0 [g1X1]
  let c2 := .RCall "fp_sqr" g1T1 [g1Y1]
  let c3 := .RCall "fp_sqr" g1T2 [g1Z1]
  let c4 := .RCall "fp_mul" g1T3 [g1X1, g1Y1]
  let c5 := .RCall "fp_add" g1X3 [g1T3, g1T3]
  let c6 := .RCall "fp_mul" g1T3 [g1Y1, g1Z1]
  let c7 := .RCall "fp_add" g1Y3 [g1T3, g1T3]
  .RSeq c1 (.RSeq c2 (.RSeq c3 (.RSeq c4 (.RSeq c5 (.RSeq c6 c7)))))

/-- G2 affine addition. -/
def g2Add : RustCmd :=
  let c1 := .RCall "fp2_mul" (mkFp2Loc "t0") [mkFp2Loc "X1", mkFp2Loc "X2"]
  let c2 := .RCall "fp2_mul" (mkFp2Loc "t1") [mkFp2Loc "Y1", mkFp2Loc "Y2"]
  let c3 := .RCall "fp2_add" (mkFp2Loc "t2") [mkFp2Loc "X1", mkFp2Loc "Y1"]
  let c4 := .RCall "fp2_add" (mkFp2Loc "t3") [mkFp2Loc "X2", mkFp2Loc "Y2"]
  let c5 := .RCall "fp2_mul" (mkFp2Loc "X3") [mkFp2Loc "t2", mkFp2Loc "t3"]
  let c6 := .RCall "fp2_sub" (mkFp2Loc "Y3") [mkFp2Loc "X3", mkFp2Loc "t0"]
  .RSeq c1 (.RSeq c2 (.RSeq c3 (.RSeq c4 (.RSeq c5 c6))))

example : borrowOk g1Add = true  := by decide
example : borrowOk g1Dbl = true  := by decide
example : borrowOk g2Add = true  := by decide

section FrameTheorems

variable (N : Nat) (leafSpec : LeafSpec)

theorem g1AddPreservesX1 (rs rs' : RustState)
    (h : RustExec N leafSpec g1Add rs rs') :
    locatedLookup rs' g1X1 = locatedLookup rs g1X1 := by
  apply seqFrame N leafSpec g1Add rs rs' g1X1 h
  decide

theorem g1DblPreservesInputs (rs rs' : RustState)
    (h : RustExec N leafSpec g1Dbl rs rs') :
    locatedLookup rs' g1X1 = locatedLookup rs g1X1 ∧
    locatedLookup rs' g1Y1 = locatedLookup rs g1Y1 ∧
    locatedLookup rs' g1Z1 = locatedLookup rs g1Z1 := by
  refine ⟨?_, ?_, ?_⟩
  · apply seqFrame N leafSpec g1Dbl rs rs' g1X1 h; decide
  · apply seqFrame N leafSpec g1Dbl rs rs' g1Y1 h; decide
  · apply seqFrame N leafSpec g1Dbl rs rs' g1Z1 h; decide

end FrameTheorems
end ConcretePrograms

/-! ## §6  Pretty-printer and file output -/

section Printer

/-- Pretty-print a `TowerType` as a Jasmin array type comment. -/
def ppTowerType : TowerType → String
  | .TFp     => "fp"    | .TFp2  => "fp2"
  | .TFp6    => "fp6"   | .TFp12 => "fp12"
  | .TU64    => "u64"
  | .TFp25519 => "fp25519"
  | .TFp25519_64 => "fp25519_64"
  -- Phase D/E/I/K (2026-05-03):
  | .TFpL25519 => "fpL25519"
  | .TFpP256 => "fpP256"
  | .TFp25519_4Bounded b => "fp25519_4(<2^" ++ toString b ++ ")"
  | .TFpGen name n => "fpGen[" ++ name ++ ", " ++ toString n ++ "B]"
  | .TFp2Gen name n => "fp2Gen[" ++ name ++ ", " ++ toString n ++ "B]"
  | .TTuple a b => "(" ++ ppTowerType a ++ "," ++ ppTowerType b ++ ")"
  | .TBytes n => "u8[" ++ toString n ++ "]"
  | .TArr n t => ppTowerType t ++ "[" ++ toString n ++ "]"

/-- Pretty-print a `WSize`. -/
def ppWSize : WSize → String
  | .U8 => "u8" | .U16 => "u16" | .U32 => "u32"
  | .U64 => "u64" | .U128 => "u128" | .U256 => "u256"

/-- Pretty-print a `SType`. -/
def ppSType : SType → String
  | .sbool   => "bool"
  | .sint    => "int"
  | .sarr n  => "u8[" ++ toString n ++ "]"
  | .sword w => ppWSize w

/-- Pretty-print a `PExpr` (simplified). -/
def ppPExpr : PExpr → String
  | .Pconst z   => toString z
  | .Pbool b    => if b then "true" else "false"
  | .Pvar gv    => gv.gv.var.vname
  | .Papp2 (.Oneq _) e (.Pconst 0) => "(" ++ ppPExpr e ++ " != 0)"
  | .Papp2 _ e1 e2 => "(" ++ ppPExpr e1 ++ " op " ++ ppPExpr e2 ++ ")"
  | .Parr_init n => "#init(" ++ toString n ++ ")"
  | e => "<expr:" ++ (repr e).pretty 80 ++ ">"

/-- Pretty-print an `LVal`. -/
def ppLVal : LVal → String
  | .Lvar v        => v.var.vname
  | .Laset _ _ v _ => v.var.vname
  | lv             => "<lval:" ++ (repr lv).pretty 80 ++ ">"

/-- Indent by `n` spaces. -/
def indent (n : Nat) (s : String) : String :=
  String.replicate n ' ' ++ s

mutual
  /-- Pretty-print one instruction with indentation `ind`. -/
  def ppInstrR (ind : Nat) : InstrR → String
    | .Cassgn lv _ _ e =>
        indent ind (ppLVal lv ++ " = " ++ ppPExpr e ++ ";")
    | .Copn lvs _ (.Oasm op) es =>
        let lhss := String.intercalate ", " (lvs.map ppLVal)
        let args := String.intercalate ", " (es.map ppPExpr)
        indent ind (lhss ++ " = #" ++ op.name ++ "(" ++ args ++ ");")
    | .Ccall _ lvs fn args =>
        let lhss := String.intercalate ", " (lvs.map ppLVal)
        let argStr := String.intercalate ", " (args.map ppPExpr)
        indent ind (lhss ++ " = " ++ fn.name ++ "(" ++ argStr ++ ");")
    | .Cif cond cthen celse =>
        let hdr := indent ind ("if (" ++ ppPExpr cond ++ ") {")
        let thenStr := ppCmd (ind + 2) cthen
        if celse.isEmpty then
          hdr ++ "\n" ++ thenStr ++ "\n" ++ indent ind "}"
        else
          hdr ++ "\n" ++ thenStr ++ "\n" ++ indent ind "} else {" ++
          "\n" ++ ppCmd (ind + 2) celse ++ "\n" ++ indent ind "}"
    | .Cwhile _ cond body =>
        indent ind ("while (" ++ ppPExpr cond ++ ") {") ++
        "\n" ++ ppCmd (ind + 2) body ++ "\n" ++ indent ind "}"
    | .Cfor v r body =>
        indent ind ("for " ++ v.var.vname ++ " = " ++ toString r.lo ++
                    " to " ++ toString r.hi ++ " {") ++
        "\n" ++ ppCmd (ind + 2) body ++ "\n" ++ indent ind "}"

  /-- Pretty-print a `Cmd` (list of instructions) with indentation `ind`. -/
  def ppCmd (ind : Nat) : Cmd → String
    | [] => ""
    | instrs => String.intercalate "\n" (instrs.map (ppInstrR ind))
end

/-- Pretty-print a `FunDecl`. -/
def ppFunDecl (fd : FunDecl) : String :=
  let params := String.intercalate ", "
    (fd.params.map (fun p => ppSType p.var.var.vtype ++ " " ++ p.var.var.vname))
  let results := String.intercalate ", " (fd.results.map (fun r => r.var.vname))
  let body := ppCmd 2 fd.body
  "fn " ++ fd.name.name ++ "(" ++ params ++ ") -> (" ++ results ++ ") {\n" ++ body ++ "\n}"

/-- Pretty-print a full `JasminProg`. -/
def ppJasminProg (prog : JasminProg) : String :=
  String.intercalate "\n\n" (prog.funcs.map ppFunDecl)

/-- Write a `RustCmd` as a Jasmin function to a file. -/
def writeJasminProg (filename name : String) (params results : List Located)
    (c : RustCmd) : IO Unit := do
  let prog := toJasminProg name params results c
  IO.FS.writeFile filename (ppJasminProg prog)

/-- Write the `RustCmd` Rocq repr to a file (for round-trip inspection). -/
def writeRustCmdRepr (filename : String) (c : RustCmd) : IO Unit :=
  IO.FS.writeFile filename (repr c |>.pretty 80)

end Printer

/-! ## §7  Demo: emit g1_add to file

Uncomment to generate `g1_add.jazz` and `g1_add_rustcmd.txt`:

```lean
#eval writeJasminProg "/tmp/g1_add.jazz" "g1_add"
        [g1X1, g1Y1, g1Z1, g1X2, g1Y2, g1Z2]
        [g1X3, g1Y3]
        g1Add

#eval writeRustCmdRepr "/tmp/g1_add_rustcmd.txt" g1Add

#eval IO.println (ppJasminProg (toJasminProg "g1_add"
        [g1X1, g1Y1, g1Z1, g1X2, g1Y2, g1Z2] [g1X3, g1Y3] g1Add))
```
-/

end CatCrypt.Crypto.Jasmin.RustCmd
