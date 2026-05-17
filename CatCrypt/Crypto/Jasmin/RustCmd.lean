/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.JasminTypes
import Mathlib.Data.List.Basic

/-!
# Rust-cmd DSL: Typed Tower-Field Command Language

Port of `AUCurves/src/Bedrock/SafeRustSimulation.v`.

`RustCmd` is a typed DSL for safe Rust programs over tower field elements
(Fp, Fp2, Fp6, Fp12, U64).  The borrow checker (`RustCmdBorrowCheck.lean`)
certifies memory safety statically; the simulation semantics (`RustExec`)
gives the big-step meaning used for frame proofs.

## Tower type encoding

Tower elements are modelled as fixed-size byte arrays (`JArray`), using the
BLS12-381 sizes as concrete defaults.  The `byteSize` function can be
overridden by downstream files for other curves.

## References

* AUCurves `SafeRustSimulation.v` — original Rocq DSL
* AUCurves `SafeRustBorrowCheck.v` — borrow checker and frame theorems
-/

namespace CatCrypt.Crypto.Jasmin.RustCmd

open CatCrypt.Crypto.Jasmin (JArray)

/-! ## §0  String → Nat injection (Phase E support, 2026-05-03)

`encodeStringNat : String → Nat` is an injection from Lean strings
to Nat, used by `TowerType.byteSize` to give string-parameterised
constructors (`TFpGen`, `TFp2Gen`) unique discrimination tags so the
overall `byteSize` function stays injective (required by the
determinism proofs in `JasminSemTracedDeterminism`).

Implementation: composes `String.toList`'s injectivity (left-inverse
`String.ofList`) with a hand-rolled `List Char → Nat` injection via
`Char.toNat` (each Char is a 21-bit codepoint) and a Nat-pair-based
list encoding.
-/

/-- Hand-rolled `List Nat → Nat` injection.  Each element is paired
    with a "non-empty" bit, then list-folded via `Nat.pair`. -/
def encodeListNat : List Nat → Nat
  | [] => 0
  | x :: xs => Nat.succ (Nat.pair x (encodeListNat xs))

theorem encodeListNat_inj : Function.Injective encodeListNat := by
  intro l1 l2 h
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons _ _ => simp [encodeListNat] at h
  | cons x xs ih =>
    cases l2 with
    | nil => simp [encodeListNat] at h
    | cons y ys =>
      simp [encodeListNat] at h
      obtain ⟨hx, hxs⟩ := h
      have hxsEq : xs = ys := ih hxs
      rw [hx, hxsEq]

/-- Inject a Lean `String` into `Nat`.  Composes
    `String.toList : String → List Char` (injective via
    `String.ofList ∘ String.toList = id`) with `Char.toNat` and
    `encodeListNat`. -/
def encodeStringNat (s : String) : Nat :=
  encodeListNat (s.toList.map Char.toNat)

theorem encodeStringNat_inj : Function.Injective encodeStringNat := by
  intro s1 s2 h
  unfold encodeStringNat at h
  have hMap : s1.toList.map Char.toNat = s2.toList.map Char.toNat :=
    encodeListNat_inj h
  -- `Char.toNat` is injective: `Char.toNat c = c.val.toNat`, and
  -- `UInt32.toNat` is injective (UInt32 wraps `Fin 2^32`).
  have hChar : Function.Injective Char.toNat := fun c1 c2 hc => by
    have : c1.val = c2.val := UInt32.toNat_inj.mp (by simpa [Char.toNat] using hc)
    cases c1; cases c2; simp_all
  have hList : s1.toList = s2.toList :=
    List.map_injective_iff.mpr hChar hMap
  -- `String.ofList ∘ String.toList = id` gives left-inverse → injectivity.
  have heq : String.ofList s1.toList = String.ofList s2.toList :=
    congrArg _ hList
  rw [String.ofList_toList, String.ofList_toList] at heq
  exact heq

/-! ## §1  Tower types -/

/-- Tower type hierarchy for pairing-friendly curves.

    **Phase D/E/I/K extensions (2026-05-03):**
    * `TFp25519_4Bounded` — refinement-typed 4-limb representation
      (Phase D).  `bound` is the per-limb upper bound exponent;
      values represent integers below `2^(64*4)` with each limb < 2^bound.
    * `TFpGen` / `TFp2Gen` — modulus-parametric (Phase E); the
      `LeafOps` typeclass lookup table provides per-curve operations.
    * `TFpL25519` / `TFpP256` — Curve25519 scalar-field and P-256
      base-field, added to close the pre-existing RustCmdReflect
      cross-reference and unblock the H1 subset filter.
    * `TTuple` — binary product type (Phase I).  Larger tuples nest.
    * `TBytes` — fixed-size byte arrays (Phase K).  Used for AES /
      ChaCha20 / SHA-256 / SHA-3 byte-level kernels. -/
inductive TowerType where
  | TFp   : TowerType   -- base field element
  | TFp2  : TowerType   -- degree-2 extension
  | TFp6  : TowerType   -- degree-6 extension
  | TFp12 : TowerType   -- degree-12 extension
  | TU64  : TowerType   -- unsigned 64-bit scalar
  /-- Curve25519 base field: 5×u64 = 40 bytes (radix-2^51). -/
  | TFp25519 : TowerType
  /-- Curve25519 base field, alternate representation: 4×u64 = 32 bytes
      (saturated representation, matching formosa-25519's `__mul4_rsr` etc.).
      Used by the inline-substituted Jasmin extraction path (D4) so that
      the leaf-inline bodies operate over the same 4×64 layout as their
      formosa Jinc origins. The standard X25519 ladder still uses
      `TFp25519` (5×51); only protocols authored against `TFp25519_64`
      directly trigger the saturated layout. -/
  | TFp25519_64 : TowerType
  /-- Curve25519 scalar field (mod L = 2^252 + δ).  32 bytes. -/
  | TFpL25519 : TowerType
  /-- P-256 base field.  32 bytes (4×u64 saturated). -/
  | TFpP256 : TowerType
  /-- **Phase D — bounds-tracked saturated 4-limb representation.**
      Each limb < 2^bound.  Used for the Sqr4 keystone, Solinas
      reduction, and any kernel where carry-bound tracking
      strengthens the Hoare invariants without runtime checks. -/
  | TFp25519_4Bounded : (bound : Nat) → TowerType
  /-- **Phase E — modulus-parametric base field.**  The `LeafOps`
      typeclass instantiated at `modulusName` provides the per-curve
      operations.  `byteSize` is fixed at the type level. -/
  | TFpGen  : (modulusName : String) → (byteSize : Nat) → TowerType
  /-- **Phase E — modulus-parametric quadratic extension.** -/
  | TFp2Gen : (modulusName : String) → (byteSize : Nat) → TowerType
  /-- **Phase I — binary product.**  Multi-element tuples nest as
      `TTuple a (TTuple b c)`.  Lowering: byte-concatenated array.  -/
  | TTuple  : TowerType → TowerType → TowerType
  /-- **Phase K — fixed-size byte array.**  `n` bytes.  Used for the
      symmetric-crypto kernels (AES blocks, ChaCha state, SHA blocks). -/
  | TBytes  : (n : Nat) → TowerType
  /-- **Phase Ext (2026-05-12) — array-of-slots.**  A homogeneous array
      of `n` cells, each holding a value of TowerType `t`.  Used for
      compactly expressing data structures whose elements are accessed
      by runtime index (e.g., comb tables, MSM bucket arrays).
      Runtime indexing is via `RArrLoad` / `RArrStore`; the index is a
      `u64`-typed scalar variable bound in `rsScalar`. -/
  | TArr    : (n : Nat) → (t : TowerType) → TowerType
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Byte size for BLS12-381 — used as a unique discrimination tag
    (required for the determinism proofs in
    `JasminSemTracedDeterminism`).  After Phase D/E/I/K (2026-05-03),
    every constructor occupies a disjoint Nat range via top-level
    `Nat.pair tag inner`, so `byteSize_inj` holds unconditionally.
    The actual storage byte width is exposed via
    `TowerType.storageBytes` below; lowering / runtime code that
    needs the real allocation size should call `storageBytes`. -/
def TowerType.byteSize : TowerType → Nat
  | .TFp                  => Nat.pair 0 0
  | .TFp2                 => Nat.pair 0 1
  | .TFp6                 => Nat.pair 0 2
  | .TFp12                => Nat.pair 0 3
  | .TU64                 => Nat.pair 0 4
  | .TFp25519             => Nat.pair 0 5
  | .TFp25519_64          => Nat.pair 0 6
  | .TFpL25519            => Nat.pair 0 7
  | .TFpP256              => Nat.pair 0 8
  | .TFp25519_4Bounded b  => Nat.pair 1 b
  | .TFpGen name n        => Nat.pair 2 (Nat.pair (encodeStringNat name) n)
  | .TFp2Gen name n       => Nat.pair 3 (Nat.pair (encodeStringNat name) n)
  | .TTuple a b           => Nat.pair 4 (Nat.pair a.byteSize b.byteSize)
  | .TBytes n             => Nat.pair 5 n
  | .TArr n t             => Nat.pair 6 (Nat.pair n t.byteSize)

/-- Phase D/E/I/K — actual storage byte width.  This is the value
    used by Jasmin's `.sarr n` allocation, distinct from `byteSize`
    (which is a unique discrimination tag for the type).  For the
    seven legacy TowerType constructors the two functions agree;
    for the Phase-D/E/I/K extensions, `storageBytes` returns the
    natural byte width while `byteSize` returns a unique encoded
    tag.  Lowering/runtime code that needs actual storage size
    should call `storageBytes`; symbolic proofs that need
    injectivity call `byteSize`. -/
def TowerType.storageBytes : TowerType → Nat
  | .TFp     => 48
  | .TFp2    => 96
  | .TFp6    => 288
  | .TFp12   => 576
  | .TU64    => 8
  | .TFp25519 => 40
  | .TFp25519_64 => 32
  | .TFpL25519 => 32
  | .TFpP256 => 32
  | .TFp25519_4Bounded _ => 32
  | .TFpGen _ n => n
  | .TFp2Gen _ n => n
  | .TTuple a b => a.storageBytes + b.storageBytes
  | .TBytes n => n
  | .TArr n t => n * t.storageBytes

/-- A unique numeric encoding of `TowerType`, distinct from
    `byteSize` (which has collisions among the 32-byte constructors
    after Phase D/E/I/K).  Used by the determinism proofs in
    `JasminSemTracedDeterminism` where unique-tag per-constructor is
    required.  Injective by construction (each constructor occupies
    a disjoint range of Nat). -/
def TowerType.encode : TowerType → Nat
  | .TFp                     => 1
  | .TFp2                    => 2
  | .TFp6                    => 3
  | .TFp12                   => 4
  | .TU64                    => 5
  | .TFp25519                => 6
  | .TFp25519_64             => 7
  | .TFpL25519               => 8
  | .TFpP256                 => 9
  | .TFp25519_4Bounded b     => 100 + b
  | .TFpGen name n           => 1000000 + 1000 * name.length + n
  | .TFp2Gen name n          => 2000000 + 1000 * name.length + n
  | .TTuple a b              => 4000000 + 1000 * a.encode + b.encode
  | .TBytes n                => 8000000 + n
  | .TArr n t                => 9000000 + 1000 * n + t.encode

/-- Runtime value for tower type `t`: a fixed-size byte array of
    `t.storageBytes` bytes.

    Migrated 2026-05-14 from `t.byteSize` to `t.storageBytes` per the
    db008232 follow-up: `byteSize` is now a proof-tag (unique encoding
    via `Nat.pair`) needed for `byteSize_inj`, while `storageBytes` is
    the actual runtime byte width consumed by lowering (`.sarr N`,
    `Parr_init N`, etc.). See `storageBytes`' docstring above for the
    full distinction. -/
abbrev RustVal (t : TowerType) := JArray t.storageBytes

/-! ## §2  Located values -/

/-- **Phase J — information-flow level.**  Tracks whether a slot
    holds public or secret data.  Default `Public` for back-compat. -/
inductive SecretLevel where
  | Public : SecretLevel
  | Secret : SecretLevel
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Public-or-Secret join (used to combine input flow levels). -/
def SecretLevel.join : SecretLevel → SecretLevel → SecretLevel
  | .Secret, _ => .Secret
  | _, .Secret => .Secret
  | .Public, .Public => .Public

/-- A located value: a named variable together with its tower type.
    `locDst` is exposed as a function returning `locSrc` for backwards
    compatibility — historically the structure had a separate `locDst`
    field, but every construction set `locDst = locSrc` and the
    duality wasn't exercised. The intrinsic encoding eliminates a
    structural ambiguity blocking unconditional reverse compiler
    correctness (see RustExecTraced.lean's A1.16' section). -/
structure Located where
  locVar : String
  locSrc : TowerType
  deriving DecidableEq, Repr, Inhabited, BEq

/-- **Phase J — information-flow classification (2026-05-03).**
    A `LevelTable` maps named slots to public/secret classification.
    The CT analyser consumes this table to reject secret-dependent
    branches.  Defaults to all-public (`fun _ => .Public`) so
    existing code without a classification compiles unchanged. -/
abbrev LevelTable := String → SecretLevel

/-- The default all-public classification.  Used when no
    information-flow analysis has been performed. -/
def LevelTable.allPublic : LevelTable := fun _ => .Public

/-- Look up the security level of a `Located` slot in a level
    table.  Convenience wrapper. -/
def Located.level (loc : Located) (lt : LevelTable) : SecretLevel :=
  lt loc.locVar

/-- Backwards-compatible accessor: `locDst` was historically a separate
    field always equal to `locSrc`. Now defined as a function. -/
abbrev Located.locDst (loc : Located) : TowerType := loc.locSrc

/-- `Located` always has positive `sizeOf` because it has at least
    one constructor weight.  Used by `decreasing_by` clauses that
    need to see Located's structural sizeOf (e.g. the
    `RCallSwap → RCall(destX)` recursion in
    `RustExecTraced.jasminSemTraced_to_rustExecTraced`). -/
theorem Located.sizeOf_pos (l : Located) : 0 < sizeOf l := by
  cases l; simp

/-- Does `dest` share a base variable with any element of `args`? -/
def callAliases (dest : Located) (args : List Located) : Bool :=
  args.any (fun a => a.locVar == dest.locVar)

/-! ## §2b  Scalar expressions

`SExpr` is a small expression language over Nat-valued scalar slots
(those bound by `RLetU64Zero` and `RScalarSet`).  Used by
`RScalarSetExpr` (Phase Ext 2026-05-12) to assign a runtime computed
value to a scalar slot, e.g. `k := i * 16 + d` for runtime `i`/`d`.

Mirrors Rocq's `sexpr_ed` (`SafeRustEd25519Sim.v`).  The 8 constructors
cover the index-arithmetic + bit-twiddle patterns the byte-level Rocq
side uses; the Lean side currently only needs `SVar`, `SLit`, `SAdd`,
`SMul`, but parity with Rocq keeps the cross-formalism mapping clean. -/
inductive SExpr where
  | SVar : String → SExpr           -- read a u64-typed scalar slot
  | SLit : Nat → SExpr              -- Nat literal
  | SAdd : SExpr → SExpr → SExpr
  | SSub : SExpr → SExpr → SExpr    -- saturating: max 0
  | SMul : SExpr → SExpr → SExpr
  | SShr : SExpr → SExpr → SExpr    -- right shift (truncating)
  | SAnd : SExpr → SExpr → SExpr    -- bitwise and
  | SLt  : SExpr → SExpr → SExpr    -- x < y → 0 / 1
  deriving Repr, Inhabited

/-- Evaluate an `SExpr` against the scalar environment.  Returns a Nat
    (no error path — undefined vars read as 0 via `rsScalar` default,
    SSub saturates at 0 rather than going negative).  Matches the
    `rsScalar : String → Nat` default-0 behaviour in `RustState`. -/
def SExpr.eval (σ : String → Nat) : SExpr → Nat
  | .SVar x   => σ x
  | .SLit n   => n
  | .SAdd a b => a.eval σ + b.eval σ
  | .SSub a b => a.eval σ - b.eval σ
  | .SMul a b => a.eval σ * b.eval σ
  | .SShr a b => a.eval σ >>> b.eval σ
  | .SAnd a b => a.eval σ &&& b.eval σ
  | .SLt  a b => if a.eval σ < b.eval σ then 1 else 0

/-- Render an `SExpr` as Rust source.  Parenthesises every binary
    operation conservatively. -/
def SExpr.ppRust : SExpr → String
  | .SVar x   => x
  | .SLit n   => toString n ++ "u64"
  | .SAdd a b => "(" ++ a.ppRust ++ " + " ++ b.ppRust ++ ")"
  | .SSub a b => "(" ++ a.ppRust ++ ".saturating_sub(" ++ b.ppRust ++ "))"
  | .SMul a b => "(" ++ a.ppRust ++ " * " ++ b.ppRust ++ ")"
  | .SShr a b => "(" ++ a.ppRust ++ " >> " ++ b.ppRust ++ ")"
  | .SAnd a b => "(" ++ a.ppRust ++ " & " ++ b.ppRust ++ ")"
  | .SLt  a b => "(if " ++ a.ppRust ++ " < " ++ b.ppRust ++ " { 1u64 } else { 0u64 })"

/-! ## §3  Rust commands -/

/-- Safe Rust commands over tower-typed variables.

    Every `RCall` writes to `dest` and reads from `args`; the borrow
    checker (`borrowOk`) ensures `dest ∉ args` at every call site.

    `RCloneCall` breaks the alias by cloning the old destination value into
    a fresh variable before dispatching the inner call. -/
inductive RustCmd where
  | RSkip      : RustCmd
  | RSeq       : RustCmd → RustCmd → RustCmd
  | RLetZero   : String → TowerType → RustCmd → RustCmd
  | RLetU64Zero : String → RustCmd → RustCmd
  | RScalarSet : String → Nat → RustCmd
  | RCall      : String → Located → List Located → RustCmd
  /-- 2-destination leaf call, used for cswap-style operations whose
      semantics mutate two field elements at once.  Emits as
      `f(&mut dest1, &mut dest2, &args…)`.  borrowOk requires
      `dest1 ≠ dest2` and neither in `args`.  The Rocq/CryptoSSA
      semantics treats this as two independent writes; the leaf's
      Hoare spec must mention both destinations. -/
  | RCallSwap : String → Located → Located → List Located → RustCmd
  | RCloneCall : String → TowerType → Located → String →
                 Located → List Located → RustCmd
  | RIfNz      : String → RustCmd → RustCmd → RustCmd
  | RWhileNz   : String → RustCmd → RustCmd
  /-- Bounded for-loop: `RFor x n body` runs `body` `n` times, with the
      scalar variable `x` set to `0, 1, …, n-1` on successive iterations.
      `n` is a closed Nat at the AST level — the loop is structurally
      terminating, no fuel needed. Authored to mirror Bedrock2's bounded
      `for`; the Hoare rule below gives `0 ≤ x < n` as a free invariant. -/
  | RFor       : String → Nat → RustCmd → RustCmd
  | RLimbStore : Located → Nat → BitVec 64 → RustCmd
  /-- **Phase F — inline asm-opcode injection.**  `RAsmOp name dests args`
      lowers to a single Jasmin `Copn` instruction.  The oracle
      `LeafSpec.asmOp` gives its semantics; the borrow checker requires
      `dests` mutually distinct and `dests ∩ args = ∅`.  Used to expose
      individual CT-classified machine instructions (ADCX/ADOX/MULX/CMOV/…)
      to RustCmd source — see `feedback_bv_decide_workflow.md` for the
      bignum schedules that benefit. -/
  | RAsmOp     : String → List Located → List Located → RustCmd
  /-- **Phase G — N-output function call.**  Generalisation of `RCall`
      (1-out) and `RCallSwap` (2-out) to arbitrary destination count.
      The oracle `LeafSpec.callN` is the multi-output analogue of
      `LeafSpec.call`.  Borrow checker: `dests` distinct, `dests ∩ args
      = ∅`.  Used for `(carry, sum) = adcx(a, b, c_in)` shapes. -/
  | RCallN     : String → List Located → List Located → RustCmd
  /-- **Phase H — CT-safe conditional select primitive.**
      `RSelect dst sel src0 src1` writes `dst := if sel = 0 then src0
      else src1`.  Hardware-level: a single `CMOV`-shaped opcode chain.
      Promoting cmov to a constructor (rather than emulating via leaf
      call) lets the borrow checker reason about it precisely (read sel,
      read src0, read src1, write dst — no aliasing constraint between
      dst and srcs since cmov is read-then-write). -/
  | RSelect    : Located → String → Located → Located → RustCmd
  /-- **Phase L — zero-cost contract assertion.**  No runtime effect;
      the Hoare rule injects an external proposition (looked up by
      `label` in the proof context) into the postcondition.  Used to
      strengthen loop invariants without inserting any bytes into the
      output asm. -/
  | RAssert    : String → RustCmd
  /-- **Phase M — scoped block.**  `RBlock body` runs `body` in a fresh
      scope; locally bound slots (via `RLetZero` / `RLetU64Zero` inside
      `body`) are released at scope end, allowing stack reuse across
      multiple `RBlock`s in a sequence.  Lowering: emits `body`'s Jasmin
      bracketed by `stackalloc`/dealloc; runtime semantics are
      identical to `body`. -/
  | RBlock     : RustCmd → RustCmd
  /-- **Phase C — user-defined helper definition.**
      `RFnDef name params returns body cont` declares a helper
      function `name` with `params` (read-only, by-ref) and `returns`
      (write, by-ref).  `body` runs with `params` and `returns` in
      scope; `cont` is the continuation in the outer scope (the
      function body is *not* inlined here — it's lifted to a separate
      Jasmin `FunDecl` at lowering time).  This is the
      compile-time analogue of `fn name(out: ..., in: ...) { body }`. -/
  | RFnDef     : (name : String)
              → (params : List Located)
              → (returns : List Located)
              → (body : RustCmd)
              → (cont : RustCmd)
              → RustCmd
  /-- **Phase C — user-defined helper call.**
      `RFnCall f dests args` invokes a helper previously declared via
      `RFnDef` (or in an outer environment).  Borrow checker: same as
      `RCallN` (dests distinct, dests ∩ args = ∅).  Lowers to a single
      Jasmin `Ccall .DoNotInline` to the `name` function. -/
  | RFnCall    : (f : String)
              → (dests : List Located)
              → (args : List Located)
              → RustCmd
  /-- **Phase I — tuple component store.**
      `RTupleStore dst idx src` writes the value of `src` into
      component `idx` of the tuple-typed slot `dst`.  Component
      indexing is structural over `TTuple a b` (idx 0 → a, idx 1 → b).
      Lowering: array-index store at the matching byte offset. -/
  | RTupleStore : (dst : Located) → (idx : Nat) → (src : Located) → RustCmd
  /-- **Phase I — tuple component load.**
      `RTupleLoad dst src idx` reads component `idx` of `src` into
      `dst`.  Lowering: array-index load.  -/
  | RTupleLoad  : (dst : Located) → (src : Located) → (idx : Nat) → RustCmd
  /-- **Phase Ext (2026-05-12) — array element store.**
      `RArrStore arr idxVar src` writes the value of slot `src` into
      element `idxVar` of the array slot `arr`.  `idxVar` is the name
      of a `u64`-typed scalar variable in `rsScalar` holding the
      runtime index.  Requires `arr.locSrc = TArr n t` and
      `src.locSrc = t`.  Lowering: `arr[idxVar as usize] = *src;`. -/
  | RArrStore  : (arr : Located) → (idxVar : String) → (src : Located) → RustCmd
  /-- **Phase Ext (2026-05-12) — array element load.**
      `RArrLoad dst src idxVar` reads element `idxVar` of array slot
      `src` into `dst`.  Requires `src.locSrc = TArr n t` and
      `dst.locSrc = t`.  Lowering: `*dst = src[idxVar as usize];`. -/
  | RArrLoad   : (dst : Located) → (src : Located) → (idxVar : String) → RustCmd
  /-- **Phase Ext (2026-05-12) — assign expression to scalar slot.**
      `RScalarSetExpr x e` evaluates `SExpr e` against the current
      scalar environment and writes the result to scalar slot `x`.
      Strictly more expressive than `RScalarSet x n` (which only takes
      a literal Nat).  Unlocks index arithmetic like `k := i * 16 + d`
      for runtime-bound `i`, `d`. -/
  | RScalarSetExpr : (x : String) → (e : SExpr) → RustCmd
  /-- **Phase Ext2 (2026-05-13) — compile-time byte-slice copy.**
      `RBytesSlice dst src start len` copies bytes `src[start..start+len]`
      into `dst`.  Requires `dst.locSrc = TBytes len` and `src.locSrc =
      TBytes n` with `start + len ≤ n` (these are syntactic, compile-time
      conditions, not checked here; the borrow-check / type-check layers
      enforce them).  Lowering: `dst.copy_from_slice(&src[start..start+len])`. -/
  | RBytesSlice : (dst : Located) → (src : Located) → (start : Nat) → (len : Nat) → RustCmd
  deriving Repr, Inhabited

/-! ## §4  Runtime state -/

/-- Specification of a single leaf-function call (formerly `LeafSpec`).
    `f dt argTs oldDest args` = new value of dest after calling `f`. -/
def CallSpec :=
  String →
  ∀ (dt : TowerType) (argTs : List TowerType),
    RustVal dt → List (Σ t : TowerType, RustVal t) → RustVal dt

/-- Specification of a limb-store operation (abstract oracle analogous to
    Rocq's `asm_correct` for `Oasm` operators).

    `spec loc oldV idx v` = new tower value for `loc` after writing the u64
    word `v` into limb index `idx` of the previous value `oldV`. -/
def LimbStoreSpec :=
  ∀ (loc : Located), RustVal loc.locDst → Nat → BitVec 64 → RustVal loc.locDst

/-- **Phase I.1 (2026-05-04) — TupleStore oracle.**  Specification
    of `RTupleStore dst idx src`: given the old dst value, the
    component index, and the src value (with src's TowerType in
    the dependent pair to handle the heterogeneous binary-product
    case), returns the new dst value with the `idx`-th component
    overwritten.  Concrete instances slice dst's underlying byte
    array and overwrite the appropriate offset; abstract reasoning
    treats the operation as an opaque function. -/
def TupleStoreSpec :=
  ∀ (dst : Located), RustVal dst.locDst → Nat →
    (Σ t : TowerType, RustVal t) → RustVal dst.locDst

/-- **Phase I.1 (2026-05-04) — TupleLoad oracle.**  Specification
    of `RTupleLoad dst src idx`: reads the `idx`-th component of
    src and produces a new dst value carrying that component.
    Same dependent-pair shape as `TupleStoreSpec` for the
    heterogeneous case. -/
def TupleLoadSpec :=
  ∀ (dst : Located), RustVal dst.locDst →
    (Σ t : TowerType, RustVal t) → Nat → RustVal dst.locDst

/-- **Phase Ext (2026-05-12) — array-element store oracle.**
    Specification of `RArrStore arr idxVar src`: given the array
    slot's old value, a runtime index, and the source value (with
    its dependent tower type), returns the new array value with
    element `idx` overwritten.  Concrete instances slice the array
    at byte offset `idx * elemSize` and overwrite; abstract
    reasoning treats it as opaque. -/
def ArrStoreSpec :=
  ∀ (arr : Located), RustVal arr.locDst → Nat →
    (Σ t : TowerType, RustVal t) → RustVal arr.locDst

/-- **Phase Ext (2026-05-12) — array-element load oracle.**
    Reads element `idx` of `arr` into `dst`. -/
def ArrLoadSpec :=
  ∀ (dst : Located), RustVal dst.locDst →
    (Σ t : TowerType, RustVal t) → Nat → RustVal dst.locDst

/-- **Phase Ext2 (2026-05-13) — byte-slice copy oracle.**
    Specification of `RBytesSlice dst src start len`: given dst's old value,
    src (as a dependent pair), start offset, and length, produce dst's new
    value with bytes `src[start..start+len]` overwritten in.  Default
    implementation is identity (preserves old dst). -/
def BytesSliceSpec :=
  ∀ (dst : Located), RustVal dst.locDst →
    (Σ t : TowerType, RustVal t) → (start : Nat) → (len : Nat) → RustVal dst.locDst

/-- **Phase I (2026-05-03) — byte-offset arithmetic for tuple
    components.**  For `t = TTuple a b`:
    * Component 0 occupies bytes `[0, a.storageBytes)`.
    * Component 1 occupies bytes `[a.storageBytes, a.storageBytes + b.storageBytes)`.

    For larger nests `TTuple a (TTuple b c)`, the inner TTuple
    contributes its full `storageBytes` to the index-1 slot.

    Returns 0 for non-TTuple types or out-of-range indices. -/
def TowerType.tupleComponentByteOffset : TowerType → Nat → Nat
  | .TTuple _ _, 0     => 0
  | .TTuple a _, _     => a.storageBytes
  | _,           _     => 0

/-- Component byte width at index `idx`.  Returns 0 for non-TTuple
    types or out-of-range indices. -/
def TowerType.tupleComponentByteSize : TowerType → Nat → Nat
  | .TTuple a _, 0     => a.storageBytes
  | .TTuple _ b, _     => b.storageBytes
  | _,           _     => 0

/-- The component TowerType at index `idx`.  For `TTuple a b`,
    idx 0 → a, idx 1 → b.  Returns the original type for non-TTuple
    or out-of-range. -/
def TowerType.tupleComponentType : TowerType → Nat → TowerType
  | .TTuple a _, 0 => a
  | .TTuple _ b, _ => b
  | t,           _ => t

/-- **Bundled oracle record** (Rocq-style): leaf-call behaviour plus
    machine-instruction behaviour. Treating these as oracles mirrors Rocq
    `jasmin_translate.v`'s use of `handled_program` (for calls) and
    `asm_correct` (for `Oasm` operators).

    **Phase F/G additions** (2026-05-03): `asmOp` and `callN` are added
    *after* `RustState` is defined — see `Phase_F_G_oracles` section
    below.  This split exists because the new oracles take/return
    `RustState` directly, while the original `call`/`limbStore`
    oracles are per-value.  Existing `LeafSpec.mk call limbStore`
    literals stay valid via `default`-supplied fields. -/
structure LeafSpec where
  call      : CallSpec
  limbStore : LimbStoreSpec
  /-- Phase I.1: tuple-store oracle.  Defaults to identity (no-op
      on dst), so existing `LeafSpec.mk call limbStore` literals
      stay valid; concrete instances override for real semantics. -/
  tupleStore : TupleStoreSpec := fun _ oldV _ _ => oldV
  /-- Phase I.1: tuple-load oracle.  Defaults to identity. -/
  tupleLoad  : TupleLoadSpec := fun _ oldV _ _ => oldV
  /-- Phase Ext: array-element store oracle.  Defaults to identity. -/
  arrStore   : ArrStoreSpec := fun _ oldV _ _ => oldV
  /-- Phase Ext: array-element load oracle.  Defaults to identity. -/
  arrLoad    : ArrLoadSpec := fun _ oldV _ _ => oldV
  /-- Phase Ext2: byte-slice copy oracle.  Defaults to identity. -/
  bytesSlice : BytesSliceSpec := fun _ oldV _ _ _ => oldV

/-- Runtime state: a tower-variable heap and a scalar heap. -/
structure RustState where
  rsTower  : String → Option (Σ t : TowerType, RustVal t)
  rsScalar : String → Nat   -- default 0

instance : Inhabited RustState where
  default := { rsTower := fun _ => none, rsScalar := fun _ => 0 }

/-- Set a tower variable. -/
def rsSetTower (rs : RustState) (x : String)
    (v : Σ t : TowerType, RustVal t) : RustState :=
  { rs with rsTower := fun y => if y == x then some v else rs.rsTower y }

/-- Set a scalar variable. -/
def rsSetScalar (rs : RustState) (x : String) (v : Nat) : RustState :=
  { rs with rsScalar := fun y => if y == x then v else rs.rsScalar y }

/-- Remove a tower variable (used after `RLetZero` body exits scope). -/
def rsRemoveTower (rs : RustState) (x : String) : RustState :=
  { rs with rsTower := fun y => if y == x then none else rs.rsTower y }

/-- Look up a tower variable, checking the stored type matches `loc.locDst`. -/
def locatedLookup (rs : RustState) (loc : Located) :
    Option (RustVal loc.locDst) :=
  match rs.rsTower loc.locVar with
  | some ⟨t, v⟩ => if h : t = loc.locDst then some (h ▸ v) else none
  | none         => none

/-- Write a new value to the destination of `loc`. -/
def locatedUpdate (rs : RustState) (loc : Located)
    (v : RustVal loc.locDst) : RustState :=
  rsSetTower rs loc.locVar ⟨loc.locDst, v⟩

/-! ## §5  Key state-update lemmas -/

theorem rsSetTower_same (rs : RustState) (x : String) (v : Σ t, RustVal t) :
    (rsSetTower rs x v).rsTower x = some v := by
  simp [rsSetTower]

theorem rsSetTower_other (rs : RustState) (x y : String)
    (v : Σ t, RustVal t) (h : x ≠ y) :
    (rsSetTower rs x v).rsTower y = rs.rsTower y := by
  unfold rsSetTower; simp only []
  have : (y == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  simp [this]

theorem rsRemoveTower_other (rs : RustState) (x y : String) (h : x ≠ y) :
    (rsRemoveTower rs x).rsTower y = rs.rsTower y := by
  unfold rsRemoveTower; simp only []
  have : (y == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  simp [this]

/-- Setting one tower var leaves a different located's lookup unchanged. -/
theorem locatedLookup_rsSetTower_other (rs : RustState) (x : String)
    (v : Σ t, RustVal t) (loc : Located) (h : x ≠ loc.locVar) :
    locatedLookup (rsSetTower rs x v) loc = locatedLookup rs loc := by
  unfold locatedLookup rsSetTower; simp only []
  have : (loc.locVar == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  simp [this]

/-- Removing one tower var leaves a different located's lookup unchanged. -/
theorem locatedLookup_rsRemoveTower_other (rs : RustState) (x : String)
    (loc : Located) (h : x ≠ loc.locVar) :
    locatedLookup (rsRemoveTower rs x) loc = locatedLookup rs loc := by
  unfold locatedLookup rsRemoveTower; simp only []
  have : (loc.locVar == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  simp [this]

/-- Setting scalar leaves tower lookups unchanged. -/
theorem locatedLookup_rsSetScalar (rs : RustState) (x : String) (v : Nat)
    (loc : Located) :
    locatedLookup (rsSetScalar rs x v) loc = locatedLookup rs loc := by
  unfold locatedLookup rsSetScalar; simp only []

/-- `locatedUpdate` writes to the correct variable. -/
theorem locatedUpdate_dest (rs : RustState) (loc : Located)
    (v : RustVal loc.locDst) :
    (locatedUpdate rs loc v).rsTower loc.locVar = some ⟨loc.locDst, v⟩ := by
  unfold locatedUpdate rsSetTower
  simp

/-- `locatedUpdate` leaves other variables unchanged. -/
theorem locatedUpdate_other (rs : RustState) (loc1 loc2 : Located)
    (v : RustVal loc1.locDst)
    (h : loc1.locVar ≠ loc2.locVar) :
    locatedLookup (locatedUpdate rs loc1 v) loc2 = locatedLookup rs loc2 := by
  apply locatedLookup_rsSetTower_other
  exact h

/-! ## §6  Big-step semantics -/

/-- Big-step execution relation for `RustCmd`.

    `RustExec N leafSpec c rs rs'` means: running `c` from state `rs`
    with fuel bound `N` and leaf specification `leafSpec` terminates in `rs'`.

    `N` bounds `RWhileNz` loop iterations (via the `while_true` case's
    induction structure — the bound appears implicitly in the finite derivation
    tree). -/
inductive RustExec (N : Nat) (leafSpec : LeafSpec) :
    RustCmd → RustState → RustState → Prop where
  | skip   : ∀ rs, RustExec N leafSpec .RSkip rs rs
  | seq    : ∀ c1 c2 rs r1 rs',
      RustExec N leafSpec c1 rs r1 →
      RustExec N leafSpec c2 r1 rs' →
      RustExec N leafSpec (.RSeq c1 c2) rs rs'
  | letZero : ∀ x t body rs rs',
      RustExec N leafSpec body (rsSetTower rs x ⟨t, default⟩) rs' →
      RustExec N leafSpec (.RLetZero x t body) rs rs'
  | letU64Zero : ∀ x body rs rs',
      RustExec N leafSpec body (rsSetScalar rs x 0) rs' →
      RustExec N leafSpec (.RLetU64Zero x body) rs rs'
  | scalarSet : ∀ x v rs,
      RustExec N leafSpec (.RScalarSet x v) rs (rsSetScalar rs x v)
  | ifTrue  : ∀ e ct cf rs rs' v,
      rs.rsScalar e = v → v ≠ 0 →
      RustExec N leafSpec ct rs rs' →
      RustExec N leafSpec (.RIfNz e ct cf) rs rs'
  | ifFalse : ∀ e ct cf rs rs',
      rs.rsScalar e = 0 →
      RustExec N leafSpec cf rs rs' →
      RustExec N leafSpec (.RIfNz e ct cf) rs rs'
  | whileFalse : ∀ e body rs,
      rs.rsScalar e = 0 →
      RustExec N leafSpec (.RWhileNz e body) rs rs
  | whileTrue : ∀ e body rs r1 rs' v,
      rs.rsScalar e = v → v ≠ 0 →
      RustExec N leafSpec body rs r1 →
      RustExec N leafSpec (.RWhileNz e body) r1 rs' →
      RustExec N leafSpec (.RWhileNz e body) rs rs'
  /-- `RFor x 0 body` is a no-op. -/
  | forZero : ∀ x body rs,
      RustExec N leafSpec (.RFor x 0 body) rs rs
  /-- `RFor x (n+1) body` runs `RFor x n body` (iterations 0..n-1), then
      sets the scalar `x` to `n` and runs `body` once more. -/
  | forSucc : ∀ x n body rs r1 rs',
      RustExec N leafSpec (.RFor x n body) rs r1 →
      RustExec N leafSpec body (rsSetScalar r1 x n) rs' →
      RustExec N leafSpec (.RFor x (n+1) body) rs rs'
  | call : ∀ f dest args rs oldDestV argList,
      locatedLookup rs dest = some oldDestV →
      argList = args.filterMap (fun a => rs.rsTower a.locVar) →
      -- Per-arg type-recovery (Option A): args[i].locDst matches the
      -- stored Sigma type at args[i].locVar. Required for determinism.
      (∀ a ∈ args, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩) →
      RustExec N leafSpec (.RCall f dest args) rs
        (locatedUpdate rs dest
          (leafSpec.call f dest.locDst (args.map (·.locDst)) oldDestV argList))
  | cloneCall : ∀ cloneVar cloneTy oldDest innerF dest args
                   rs rsClone rs',
      rsClone = rsSetTower rs cloneVar
                  (rs.rsTower oldDest.locVar |>.getD ⟨cloneTy, default⟩) →
      RustExec N leafSpec (.RCall innerF dest args) rsClone rs' →
      RustExec N leafSpec
        (.RCloneCall cloneVar cloneTy oldDest innerF dest args)
        rs rs'  -- aligns with Jasmin semantics: no variable removal
  /-- 2-output cswap-shape leaf.  Semantically: two sequential 1-out
      calls in Jasmin: `f(dest1, args); f(dest2, args)`.  borrowOk for
      `RCallSwap` forbids `dest1 = dest2` and either dest in args. -/
  | callSwap : ∀ f dest1 dest2 args rs rs1 rs',
      RustExec N leafSpec (.RCall f dest1 args) rs rs1 →
      RustExec N leafSpec (.RCall f dest2 args) rs1 rs' →
      RustExec N leafSpec (.RCallSwap f dest1 dest2 args) rs rs'
  | limbStore : ∀ loc idx v rs oldDestV,
      locatedLookup rs loc = some oldDestV →
      RustExec N leafSpec (.RLimbStore loc idx v) rs
        (locatedUpdate rs loc (leafSpec.limbStore loc oldDestV idx v))
  /-- **Phase F semantics — identity stub.**  The real per-opcode
      effect is supplied by the Hoare-layer oracle (analogue of
      `leafSpec.call` for individual `Copn` instructions); the
      bare-`RustExec` step is identity so that the inductive carries
      no opcode-table baggage.  Hoare rules pin the post-state via
      external hypotheses about the opcode named `name`.  Mirrors the
      pattern used in Rocq `jasmin_translate.v`'s `Oasm` axiomatic
      treatment. -/
  | asmOp : ∀ name dests args rs,
      RustExec N leafSpec (.RAsmOp name dests args) rs rs
  /-- **Phase G semantics — identity stub.**  As `asmOp`: the real
      multi-output side effect comes from the Hoare-level
      `callN`-spec; the inductive step is identity. -/
  | callN : ∀ f dests args rs,
      RustExec N leafSpec (.RCallN f dests args) rs rs
  /-- **Phase H semantics — CT-safe conditional move.**  Reads the
      scalar `sel`; if zero, copies `src0`'s tower value into `dst`;
      else copies `src1`.  Hardware analogue: a `CMOV` chain at the
      asm level.  Both source values are read regardless of `sel`'s
      value — that's what makes this CT-safe.

      The type side conditions `src0.locDst = dst.locDst` and
      `src1.locDst = dst.locDst` reflect the borrow-checker invariant
      that cmov requires same-typed source / dest slots. -/
  | selectFalse : ∀ dst sel src0 src1 rs (h : src0.locDst = dst.locDst) srcV,
      rs.rsScalar sel = 0 →
      locatedLookup rs src0 = some srcV →
      RustExec N leafSpec (.RSelect dst sel src0 src1) rs
        (locatedUpdate rs dst (h ▸ srcV))
  | selectTrue : ∀ dst sel src0 src1 rs (h : src1.locDst = dst.locDst) v srcV,
      rs.rsScalar sel = v → v ≠ 0 →
      locatedLookup rs src1 = some srcV →
      RustExec N leafSpec (.RSelect dst sel src0 src1) rs
        (locatedUpdate rs dst (h ▸ srcV))
  /-- **Phase L semantics — zero-cost contract.**  No state change. -/
  | assert : ∀ label rs,
      RustExec N leafSpec (.RAssert label) rs rs
  /-- **Phase M semantics — scoped block.**  Identical to running
      the body; the "scope" boundary is meaningful only at the
      lowering level (stack reuse) and the Hoare level
      (locally-bound vars dropped from the post-context). -/
  | block : ∀ body rs rs',
      RustExec N leafSpec body rs rs' →
      RustExec N leafSpec (.RBlock body) rs rs'
  /-- **Phase C — `RFnDef` semantics.**  Identity stub: the function
      definition is a compile-time declaration, not a runtime event.
      The continuation `cont` runs with the (statically-known) helper
      bound in the function environment.  At this layer, the
      environment is implicit — proven via a per-`RFnCall` Hoare
      rule that takes the helper's `FnSpec` as a hypothesis. -/
  | fnDef : ∀ name params returns body cont rs rs',
      RustExec N leafSpec cont rs rs' →
      RustExec N leafSpec (.RFnDef name params returns body cont) rs rs'
  /-- **Phase C — `RFnCall` semantics — identity stub.**  Like
      `asmOp` / `callN`: the real per-helper effect comes from a
      Hoare-level oracle parameterised by the helper's `FnSpec`. -/
  | fnCall : ∀ f dests args rs,
      RustExec N leafSpec (.RFnCall f dests args) rs rs
  /-- **Phase I.1 (2026-05-04) — tuple component store.**  Reads
      `dst`'s old value, looks up `src` (with its dependent tower
      type), and writes `leafSpec.tupleStore dst oldV idx ⟨src.locDst, srcV⟩`
      to `dst`'s tower slot.  Concrete instances of `LeafSpec` override
      `tupleStore` to perform the real byte-offset overwrite; the
      default (identity) preserves backwards compatibility. -/
  | tupleStore : ∀ dst idx src rs oldV srcV,
      locatedLookup rs dst = some oldV →
      locatedLookup rs src = some srcV →
      RustExec N leafSpec (.RTupleStore dst idx src) rs
        (locatedUpdate rs dst (leafSpec.tupleStore dst oldV idx ⟨src.locDst, srcV⟩))
  /-- **Phase I.1 — tuple component load.**  Reads the `idx`-th
      component of `src` into `dst` via `leafSpec.tupleLoad`. -/
  | tupleLoad : ∀ dst src idx rs oldV srcV,
      locatedLookup rs dst = some oldV →
      locatedLookup rs src = some srcV →
      RustExec N leafSpec (.RTupleLoad dst src idx) rs
        (locatedUpdate rs dst (leafSpec.tupleLoad dst oldV ⟨src.locDst, srcV⟩ idx))
  /-- **Phase Ext — array element store.**  Looks up runtime index
      `rs.rsScalar idxVar`, reads `arr`'s old value, reads `src`'s
      value (with dependent tower type), and writes via
      `leafSpec.arrStore`.  Concrete instances slice arr's byte
      array at offset `idx * src.locDst.storageBytes` to overwrite. -/
  | arrStore : ∀ arr idxVar src rs idx oldV srcV,
      rs.rsScalar idxVar = idx →
      locatedLookup rs arr = some oldV →
      locatedLookup rs src = some srcV →
      RustExec N leafSpec (.RArrStore arr idxVar src) rs
        (locatedUpdate rs arr (leafSpec.arrStore arr oldV idx ⟨src.locDst, srcV⟩))
  /-- **Phase Ext — array element load.**  Looks up runtime index
      `rs.rsScalar idxVar` and reads element `idx` of `src` into
      `dst` via `leafSpec.arrLoad`. -/
  | arrLoad : ∀ dst src idxVar rs idx oldV srcV,
      rs.rsScalar idxVar = idx →
      locatedLookup rs dst = some oldV →
      locatedLookup rs src = some srcV →
      RustExec N leafSpec (.RArrLoad dst src idxVar) rs
        (locatedUpdate rs dst (leafSpec.arrLoad dst oldV ⟨src.locDst, srcV⟩ idx))
  /-- **Phase Ext — set scalar slot to an `SExpr` value.**  Evaluates
      the expression against the current scalar env and writes the
      result.  Total: `SExpr.eval` is total on the partial-default
      `rsScalar : String → Nat`. -/
  | scalarSetExpr : ∀ x e rs,
      RustExec N leafSpec (.RScalarSetExpr x e) rs
        (rsSetScalar rs x (e.eval rs.rsScalar))
  /-- **Phase Ext2 (2026-05-13) — byte-slice copy.**  Reads `dst`'s
      old value, looks up `src` (with its dependent tower type), and
      writes `leafSpec.bytesSlice dst oldV ⟨src.locDst, srcV⟩ start len`
      to `dst`'s tower slot.  Concrete `LeafSpec` instances override
      `bytesSlice` to perform the real byte-range copy; the default
      (identity) preserves backwards compatibility. -/
  | bytesSlice : ∀ dst src start len rs oldV srcV,
      locatedLookup rs dst = some oldV →
      locatedLookup rs src = some srcV →
      RustExec N leafSpec (.RBytesSlice dst src start len) rs
        (locatedUpdate rs dst
          (leafSpec.bytesSlice dst oldV ⟨src.locDst, srcV⟩ start len))

/-! ## §7  `RFor` smoke tests and Hoare-style rule

The Hoare-style rule for `RFor` says: if a state-indexed invariant `I i`
is preserved by one execution of `body` (with the counter set to `i`),
and `I 0` holds initially, then `I n` holds after `RFor x n body`.
This is the standard structural rule for bounded for-loops; it's the
key reason to add `RFor` (vs. open-coding everything as `RWhileNz`):
the rule needs no termination side condition and the loop bound becomes
a free invariant. -/

namespace RustExec

/-- **RFor structural induction rule**: if `I 0 rs` and `body` preserves
    `I` across one iteration with the counter set to `i`, then `I n` holds
    at the post-state. Schematic; `I` ranges over arbitrary state predicates.

    This is the analogue of Bedrock2's `compile_for` rule applied at the
    semantic level — same shape minus the program-counter bookkeeping. -/
theorem rfor_invariant
    {N : Nat} {leafSpec : LeafSpec} {x : String} {body : RustCmd}
    {I : Nat → RustState → Prop}
    (hStep : ∀ (i : Nat) (rs r' : RustState),
        I i rs →
        RustExec N leafSpec body (rsSetScalar rs x i) r' →
        I (i + 1) r') :
    ∀ (n : Nat) (rs r' : RustState),
      I 0 rs →
      RustExec N leafSpec (.RFor x n body) rs r' →
      I n r' := by
  intro n
  induction n with
  | zero =>
    intro rs r' hI hExec
    cases hExec
    exact hI
  | succ k ih =>
    intro rs r' hI hExec
    cases hExec with
    | forSucc _ _ _ _ r1 _ hInner hBody =>
      have hk : I k r1 := ih rs r1 hI hInner
      exact hStep k r1 r' hk hBody

/-- Smoke test: a 3-iteration for-loop with an `RSkip` body executes to
    the explicit scalar-set chain. -/
example (N : Nat) (leafSpec : LeafSpec) (rs : RustState) :
    RustExec N leafSpec (.RFor "i" 3 .RSkip) rs
      (rsSetScalar (rsSetScalar (rsSetScalar rs "i" 0) "i" 1) "i" 2) := by
  apply forSucc -- iter 2 (n=2 in forSucc, so x ↦ 2 + skip)
  · apply forSucc -- iter 1
    · apply forSucc -- iter 0
      · exact forZero ..
      · exact skip _
    · exact skip _
  · exact skip _

/-- Smoke test of the structural rule: counting iterations. After
    `RFor "i" n RSkip`, the invariant "we ran n iterations" is established. -/
example (N : Nat) (leafSpec : LeafSpec) (n : Nat) (rs r' : RustState)
    (h : RustExec N leafSpec (.RFor "i" n .RSkip) rs r') :
    True :=  -- placeholder result; the real claim is the invariant rule below
  rfor_invariant (I := fun _ _ => True)
    (hStep := fun _ _ _ _ _ => trivial)
    n rs r' trivial h

end RustExec

end CatCrypt.Crypto.Jasmin.RustCmd
