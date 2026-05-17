/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Core.Code
import CatCrypt.Crypto.SDist
import CatCrypt.Crypto.CryptoWord

/-!
# CryptoSSA: An SSA IR for Cryptographic Compilation

A self-contained SSA (Static Single Assignment) intermediate representation designed
for cryptographic security proofs, with denotational semantics into `SPComp`.

The design mirrors lean-mlir's `Dialect { Op, Ty, m }` and `Com` structure (opencompl),
using intrinsically-typed De Bruijn indices and A-normal form. Structurally compatible
for future lean-mlir integration.

## Key features

* **Intrinsically typed**: well-formedness is enforced by construction
* **A-normal form**: all intermediate results are let-bound (like lean-mlir's `Com`)
* **Denotational semantics**: `CProg.denote` maps programs to `SPComp` computations
* **Observational equivalence**: `progEquiv` and `progSdist` for security reasoning

## Architecture

```
CryptoTy  ─── types (bit, unit, pair, sum, sword n)
CryptoOp  ─── operations (xor, sample, etc.)
CVar      ─── intrinsically-typed De Bruijn variables
CExpr     ─── expressions (operations applied to variables)
CProg     ─── programs in A-normal form (let-binding + return)
HVec      ─── heterogeneous valuation (typed environment)
```

## References

* lean-mlir (opencompl): `Dialect`, `Com`, `PeepholeRewrite`
* Barthe et al., "Secure Compilation of Side-Channel Countermeasures", POPL 2025

**0 axioms**, **0 sorries**.
-/

namespace CatCrypt.Crypto.SecureCompilation.CryptoSSA

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

set_option autoImplicit true -- SSA IR: many context/type variables

/-! ## Section 1: Type System -/

/-- Types in the CryptoSSA IR.

    Mirrors lean-mlir's `Ty` parameter for a `Dialect`. -/
inductive CryptoTy where
  /-- Single bit (Bool). Used for OTP message/key/ciphertext. -/
  | bit
  /-- Unit type. -/
  | unit
  /-- Product type. -/
  | pair (a b : CryptoTy)
  /-- Sum (coproduct) type. Used for UC output channels (out ⊕ leak). -/
  | sum (a b : CryptoTy)
  /-- Machine word (BitVec n). Bridges to Jasmin's `sword ws` via `WSize.bits`. -/
  | sword (n : Nat)
  /-- Fixed-size memref (array) of `sword 64` limbs. Used for tower/limb
      storage: a BLS12-381 Fp element is `memref 6` (6 × 64-bit limbs).
      Mirrors MLIR's `memref<n×i64>`. -/
  | memref (n : Nat)
  deriving DecidableEq, Repr

/-- Denotation of CryptoSSA types into Lean types.
    `@[reducible]` so type class resolution can see through it (needed for BitVec ops). -/
@[reducible] def CryptoTy.denote : CryptoTy → Type
  | .bit => Bool
  | .unit => Unit
  | .pair a b => a.denote × b.denote
  | .sum a b => a.denote ⊕ b.denote
  | .sword n => BitVec n
  | .memref n => Fin n → BitVec 64

instance : Nonempty CryptoTy.bit.denote := ⟨false⟩
instance : Nonempty CryptoTy.unit.denote := ⟨()⟩
instance {a b : CryptoTy} [Nonempty a.denote] [Nonempty b.denote] :
    Nonempty (CryptoTy.pair a b).denote :=
  ⟨(Classical.arbitrary _, Classical.arbitrary _)⟩
instance {a : CryptoTy} [Nonempty a.denote] {b : CryptoTy} :
    Nonempty (CryptoTy.sum a b).denote := ⟨.inl (Classical.arbitrary _)⟩
instance {n : Nat} : Nonempty (CryptoTy.sword n).denote := ⟨0⟩
instance {n : Nat} : Nonempty (CryptoTy.memref n).denote := ⟨fun _ => 0⟩

/-- Recursive default witness for `CryptoTy.denote`. -/
def CryptoTy.default : (t : CryptoTy) → t.denote
  | .bit => false
  | .unit => ()
  | .pair a b => (default a, default b)
  | .sum a _ => Sum.inl (default a)
  | .sword _ => 0
  | .memref _ => fun _ => 0

instance {t : CryptoTy} : Nonempty t.denote := ⟨CryptoTy.default t⟩

/-! ## Section 2: Typing Contexts and Variables -/

/-- Typing context: a list of CryptoSSA types (De Bruijn, like lean-mlir's `Ctxt`). -/
abbrev Ctx := List CryptoTy

/-- Intrinsically-typed De Bruijn variable reference.

    `CVar Γ t` witnesses that type `t` appears at a specific position in `Γ`. -/
inductive CVar : Ctx → CryptoTy → Type where
  /-- The most recently bound variable. -/
  | here {Γ : Ctx} {t : CryptoTy} : CVar (t :: Γ) t
  /-- A variable bound earlier (shift by one). -/
  | there {Γ : Ctx} {s t : CryptoTy} : CVar Γ t → CVar (s :: Γ) t

/-- Boolean equality on CVar (De Bruijn index comparison). -/
def CVar.beq : CVar Γ t → CVar Γ t → Bool
  | .here, .here => true
  | .here, .there _ => false
  | .there _, .here => false
  | .there a, .there b => CVar.beq a b

theorem CVar.beq_eq_true_iff (a b : CVar Γ t) : a.beq b = true ↔ a = b := by
  induction a with
  | here => cases b <;> simp [beq]
  | there _ ih => cases b with
    | here => simp [beq]
    | there b => simp [beq, ih b]

instance : BEq (CVar Γ t) := ⟨CVar.beq⟩

instance : DecidableEq (CVar Γ t) :=
  fun a b => decidable_of_iff _ (CVar.beq_eq_true_iff a b)

/-! ## Section 3: Heterogeneous Valuation -/

/-- Heterogeneous vector of typed values, one per context entry.

    `HVec Γ` assigns a value of type `t.denote` to each entry `t` in `Γ`. -/
inductive HVec : Ctx → Type where
  /-- Empty valuation for empty context. -/
  | nil : HVec []
  /-- Extend valuation with a new value. -/
  | cons {Γ : Ctx} {t : CryptoTy} : t.denote → HVec Γ → HVec (t :: Γ)

/-- Look up the value of a variable in a valuation. -/
def CVar.lookup : CVar Γ t → HVec Γ → t.denote
  | .here, .cons v _ => v
  | .there x, .cons _ vs => x.lookup vs

/-- Extend a valuation with a new value at the head. -/
def HVec.extend (V : HVec Γ) (val : t.denote) : HVec (t :: Γ) :=
  .cons val V

/-! ## Section 3b: Heterogeneous Vector (typed)

Generic heterogeneous vector indexed by a `List CryptoTy`, with a per-element
type function `f`. Structurally identical to `VIR.HVector` so the translation
to VIR `Expr` is a trivial map (no list-vs-HVector shape mismatch).

Introduced 2026-05-14 as part of the `extCall` HVector refactor. -/

/-- A heterogeneous list of items indexed by `List CryptoTy`, with a per-tag
    type function. -/
inductive CHVector (f : CryptoTy → Type) : List CryptoTy → Type where
  | nil : CHVector f []
  | cons {t : CryptoTy} {ts : List CryptoTy} :
      f t → CHVector f ts → CHVector f (t :: ts)

namespace CHVector

/-- Map a CHVector pointwise. -/
def map {f g : CryptoTy → Type} (h : ∀ {t}, f t → g t) :
    {ts : List CryptoTy} → CHVector f ts → CHVector g ts
  | [], .nil => .nil
  | _ :: _, .cons x xs => .cons (h x) (map h xs)

end CHVector

/-- Convert a runtime-typed `List (Σ t, f t)` into a typed pair
    `(argTys, CHVector f argTys)`. The `argTys` is the projected first
    components in order. Used for migrating call sites that previously
    accumulated `List (Σ t : CryptoTy, CVar Γ t)`. -/
def listSigmaToCHVector {f : CryptoTy → Type} :
    (xs : List (Σ t : CryptoTy, f t)) →
    Σ argTys : List CryptoTy, CHVector f argTys
  | [] => ⟨[], .nil⟩
  | ⟨t, v⟩ :: rest =>
    match listSigmaToCHVector rest with
    | ⟨ts, hv⟩ => ⟨t :: ts, .cons v hv⟩

/-! ## Section 4: Expressions and Programs -/

/-- Expression in A-normal form: an operation applied to variable arguments.

    Each constructor corresponds to a CryptoSSA operation with its signature.
    Pure operations return values directly; impure ones (sampling) use `SPComp`. -/
inductive CExpr (Γ : Ctx) : CryptoTy → Type where
  /-- Boolean constant. -/
  | constBit (v : Bool) : CExpr Γ .bit
  /-- Unit constant. -/
  | constUnit : CExpr Γ .unit
  /-- XOR of two bits: `a ⊕ b`. -/
  | xor (a b : CVar Γ .bit) : CExpr Γ .bit
  /-- AND of two bits. -/
  | and (a b : CVar Γ .bit) : CExpr Γ .bit
  /-- OR of two bits. -/
  | or (a b : CVar Γ .bit) : CExpr Γ .bit
  /-- NOT of a bit. -/
  | not (a : CVar Γ .bit) : CExpr Γ .bit
  /-- Equality test on bits. -/
  | eqBit (a b : CVar Γ .bit) : CExpr Γ .bit
  /-- Construct a pair. -/
  | mkPair (a : CVar Γ s) (b : CVar Γ t) : CExpr Γ (.pair s t)
  /-- First projection of a pair. -/
  | fst (v : CVar Γ (.pair s t)) : CExpr Γ s
  /-- Second projection of a pair. -/
  | snd (v : CVar Γ (.pair s t)) : CExpr Γ t
  /-- Left injection into a sum. -/
  | inl (v : CVar Γ s) : CExpr Γ (.sum s t)
  /-- Right injection into a sum. -/
  | inr (v : CVar Γ t) : CExpr Γ (.sum s t)
  /-- Sample a uniform random bit. -/
  | sampleBit : CExpr Γ .bit
  /-- BitVec constant. -/
  | bvConst (v : BitVec n) : CExpr Γ (.sword n)
  /-- Bitwise XOR on BitVec. -/
  | bvXor (a b : CVar Γ (.sword n)) : CExpr Γ (.sword n)
  /-- Bitwise AND on BitVec. -/
  | bvAnd (a b : CVar Γ (.sword n)) : CExpr Γ (.sword n)
  /-- Bitwise OR on BitVec. -/
  | bvOr (a b : CVar Γ (.sword n)) : CExpr Γ (.sword n)
  /-- Bitwise NOT on BitVec. -/
  | bvNot (a : CVar Γ (.sword n)) : CExpr Γ (.sword n)
  /-- Addition on BitVec (mod 2^n). -/
  | bvAdd (a b : CVar Γ (.sword n)) : CExpr Γ (.sword n)
  /-- Subtraction on BitVec (mod 2^n). -/
  | bvSub (a b : CVar Γ (.sword n)) : CExpr Γ (.sword n)
  /-- Multiplication on BitVec (mod 2^n). -/
  | bvMul (a b : CVar Γ (.sword n)) : CExpr Γ (.sword n)
  /-- Equality test on BitVec → bit. -/
  | bvEq (a b : CVar Γ (.sword n)) : CExpr Γ .bit
  /-- Left shift by constant amount. -/
  | bvShiftL (a : CVar Γ (.sword n)) (k : Nat) : CExpr Γ (.sword n)
  /-- Right shift by constant amount. -/
  | bvShiftR (a : CVar Γ (.sword n)) (k : Nat) : CExpr Γ (.sword n)
  /-- Add-with-carry-in-zero on BitVec. Returns (carry-out, sum) as a pair
      of BitVecs (carry represented as `BitVec n` with `0` or `1`).
      Models Jasmin's multi-output `#ADD_64` intrinsic. -/
  | bvAdd64 (a b : CVar Γ (.sword n)) : CExpr Γ (.pair (.sword n) (.sword n))
  /-- Add-with-carry on BitVec. Takes (a, b, cin) and returns (cout, sum)
      as a pair of BitVecs (carries represented as `BitVec n` with `0` or `1`;
      `cin` is treated as non-zero ↦ true, zero ↦ false).
      Models Jasmin's multi-output `#ADC_64` intrinsic. -/
  | bvAdc (a b cin : CVar Γ (.sword n)) : CExpr Γ (.pair (.sword n) (.sword n))
  /-- Sample uniform random BitVec. -/
  | sampleBv (n : Nat) : CExpr Γ (.sword n)
  /-- Conditional move: if-then-else on a bit condition.
      `ite c a b = a when c, else b`. Pure; total.
      Roadmap item #5 from `docs/cryptossa-next-steps.md`: enables
      `Pif` translation from JasminToSSA and `RIfThenElse` from RustCmd. -/
  | ite (c : CVar Γ .bit) (a b : CVar Γ t) : CExpr Γ t
  /-- Initialise a fresh memref of length `n` with all-zero limbs.
      Models RustCmd's `RLetZero`/`RLetU64Zero` for tower storage. -/
  | memrefZero (n : Nat) : CExpr Γ (.memref n)
  /-- Functional store: return a new memref equal to `arr` with index `i`
      updated to `v`. SSA form of RustCmd's `RLimbStore`. -/
  | memrefSet {n : Nat} (arr : CVar Γ (.memref n)) (i : Fin n)
      (v : CVar Γ (.sword 64)) : CExpr Γ (.memref n)
  /-- Functional load: read limb `i` from the memref. -/
  | memrefGet {n : Nat} (arr : CVar Γ (.memref n)) (i : Fin n) :
      CExpr Γ (.sword 64)
  /-- External call to a named oracle (e.g., fiat-crypto leaf like
      `fp_mul`). `args` is a typed heterogeneous vector of vars indexed by
      the declared `argTys`. Denotation here is opaque (returns a default
      value from `retTy.denote`); concrete semantics is supplied via a
      `CallEnv` when needed for proofs, or via `func.call` in textual MLIR.

      Refactored 2026-05-14: `args` now carries its types intrinsically as
      a `CHVector`, eliminating the previous `List (Σ t, CVar Γ t)` shape
      and the convention `args.map Sigma.fst = argTys`. This unblocks the
      `CryptoSSA → VIR` translation for `extCall`. -/
  | extCall (name : String) (retTy : CryptoTy)
      {argTys : List CryptoTy}
      (args : CHVector (fun t => CVar Γ t) argTys) : CExpr Γ retTy

/-- Program in A-normal form (like lean-mlir's `Com`).

    Every intermediate result is explicitly let-bound, producing a De Bruijn context
    that grows with each binding. -/
inductive CProg : Ctx → CryptoTy → Type where
  /-- Return a variable's value. -/
  | ret (v : CVar Γ t) : CProg Γ t
  /-- Let-bind an expression and continue with the result in scope. -/
  | letBind (e : CExpr Γ t) (body : CProg (t :: Γ) s) : CProg Γ s

/-! ## Section 5: Denotational Semantics -/

/-- Classify whether an expression is pure (deterministic, no heap effects). -/
def CExpr.isPure : CExpr Γ t → Bool
  | .sampleBit => false
  | .sampleBv _ => false
  | .ite _ _ _ => true
  | .memrefZero _ => true
  | .memrefSet _ _ _ => true
  | .memrefGet _ _ => true
  | .extCall _ _ _ => true  -- oracle: deterministic but opaque
  | _ => true

/-- Denote an expression as an `SPComp` computation. -/
noncomputable def CExpr.denote : CExpr Γ t → HVec Γ → SPComp t.denote
  | .constBit v, _ => SPComp.pure v
  | .constUnit, _ => SPComp.pure ()
  | .xor a b, V => SPComp.pure (Bool.xor (a.lookup V) (b.lookup V))
  | .and a b, V => SPComp.pure (a.lookup V && b.lookup V)
  | .or a b, V => SPComp.pure (a.lookup V || b.lookup V)
  | .not a, V => SPComp.pure (!a.lookup V)
  | .eqBit a b, V => SPComp.pure (Bool.xor (a.lookup V) (b.lookup V) |>.not)
  | .mkPair a b, V => SPComp.pure (a.lookup V, b.lookup V)
  | .fst v, V => SPComp.pure (v.lookup V).1
  | .snd v, V => SPComp.pure (v.lookup V).2
  | .inl v, V => SPComp.pure (.inl (v.lookup V))
  | .inr v, V => SPComp.pure (.inr (v.lookup V))
  | .sampleBit, _ => SPComp.sample Bool
  | .bvConst v, _ => SPComp.pure v
  | .bvXor a b, V => SPComp.pure (a.lookup V ^^^ b.lookup V)
  | .bvAnd a b, V => SPComp.pure (a.lookup V &&& b.lookup V)
  | .bvOr a b, V => SPComp.pure (a.lookup V ||| b.lookup V)
  | .bvNot a, V => SPComp.pure (~~~a.lookup V)
  | .bvAdd a b, V => SPComp.pure (a.lookup V + b.lookup V)
  | .bvSub a b, V => SPComp.pure (a.lookup V - b.lookup V)
  | .bvMul a b, V => SPComp.pure (a.lookup V * b.lookup V)
  | .bvEq a b, V => SPComp.pure (decide (a.lookup V = b.lookup V))
  | .bvShiftL a k, V => SPComp.pure (a.lookup V <<< k)
  | .bvShiftR a k, V => SPComp.pure (BitVec.ushiftRight (a.lookup V) k)
  | .bvAdd64 a b, V =>
      let p := BitVec.adc (a.lookup V) (b.lookup V) false
      SPComp.pure ((if p.fst then (1 : BitVec _) else 0), p.snd)
  | .bvAdc a b cin, V =>
      let p := BitVec.adc (a.lookup V) (b.lookup V) ((cin.lookup V).toNat ≠ 0)
      SPComp.pure ((if p.fst then (1 : BitVec _) else 0), p.snd)
  | .sampleBv n, _ => SPComp.sample (BitVec n)
  | .ite c a b, V => SPComp.pure (if c.lookup V then a.lookup V else b.lookup V)
  | .memrefZero _, _ => SPComp.pure (fun _ => 0)
  | .memrefSet arr i v, V => SPComp.pure
      (fun j => if j = i then v.lookup V else (arr.lookup V) j)
  | .memrefGet arr i, V => SPComp.pure ((arr.lookup V) i)
  | .extCall _ retTy _, _ =>
      -- Opaque denotation: returns the recursive `CryptoTy.default`
      -- witness. Concrete semantics is supplied by a `CallEnv` (future
      -- work) or by a textual MLIR emission as `func.call @<name>`.
      -- We use `CryptoTy.default` rather than `Classical.arbitrary` so
      -- that the value is computational (no `Classical.choice` axiom)
      -- and definitionally matches the VIR-side denotation in
      -- `CatCryptDialect`, enabling Qed of `toVIRExpr_denote_pure`.
      SPComp.pure (CryptoTy.default retTy)

/-- Denote a program as an `SPComp` computation.

    Sequentially evaluates let-bindings, extending the valuation at each step. -/
noncomputable def CProg.denote : CProg Γ t → HVec Γ → SPComp t.denote
  | .ret v, V => SPComp.pure (v.lookup V)
  | .letBind e body, V => SPComp.bind (e.denote V) (fun val => body.denote (V.extend val))

/-! ## Section 6: Semantic Properties -/

/-- Pure expression denotation: if the expression is pure, the result is
    independent of the heap. -/
theorem CExpr.denote_pure_eq {Γ : Ctx} {t : CryptoTy}
    (e : CExpr Γ t) (h : e.isPure = true) (V : HVec Γ) :
    ∃ v : t.denote, e.denote V = SPComp.pure v := by
  cases e with
  | constBit v => exact ⟨v, rfl⟩
  | constUnit => exact ⟨(), rfl⟩
  | xor a b => exact ⟨Bool.xor (a.lookup V) (b.lookup V), rfl⟩
  | and a b => exact ⟨a.lookup V && b.lookup V, rfl⟩
  | or a b => exact ⟨a.lookup V || b.lookup V, rfl⟩
  | not a => exact ⟨!a.lookup V, rfl⟩
  | eqBit a b => exact ⟨(Bool.xor (a.lookup V) (b.lookup V)).not, rfl⟩
  | mkPair a b => exact ⟨(a.lookup V, b.lookup V), rfl⟩
  | fst v => exact ⟨(v.lookup V).1, rfl⟩
  | snd v => exact ⟨(v.lookup V).2, rfl⟩
  | inl v => exact ⟨.inl (v.lookup V), rfl⟩
  | inr v => exact ⟨.inr (v.lookup V), rfl⟩
  | sampleBit => simp [isPure] at h
  | bvConst v => exact ⟨v, rfl⟩
  | bvXor a b => exact ⟨a.lookup V ^^^ b.lookup V, rfl⟩
  | bvAnd a b => exact ⟨a.lookup V &&& b.lookup V, rfl⟩
  | bvOr a b => exact ⟨a.lookup V ||| b.lookup V, rfl⟩
  | bvNot a => exact ⟨~~~a.lookup V, rfl⟩
  | bvAdd a b => exact ⟨a.lookup V + b.lookup V, rfl⟩
  | bvSub a b => exact ⟨a.lookup V - b.lookup V, rfl⟩
  | bvMul a b => exact ⟨a.lookup V * b.lookup V, rfl⟩
  | bvEq a b => exact ⟨decide (a.lookup V = b.lookup V), rfl⟩
  | bvShiftL a k => exact ⟨a.lookup V <<< k, rfl⟩
  | bvShiftR a k => exact ⟨BitVec.ushiftRight (a.lookup V) k, rfl⟩
  | bvAdd64 a b =>
      let p := BitVec.adc (a.lookup V) (b.lookup V) false
      exact ⟨((if p.fst then (1 : BitVec _) else 0), p.snd), rfl⟩
  | bvAdc a b cin =>
      let p := BitVec.adc (a.lookup V) (b.lookup V) ((cin.lookup V).toNat ≠ 0)
      exact ⟨((if p.fst then (1 : BitVec _) else 0), p.snd), rfl⟩
  | sampleBv _ => simp [isPure] at h
  | ite c a b => exact ⟨if c.lookup V then a.lookup V else b.lookup V, rfl⟩
  | memrefZero _ => exact ⟨fun _ => 0, rfl⟩
  | memrefSet arr i v =>
      exact ⟨fun j => if j = i then v.lookup V else (arr.lookup V) j, rfl⟩
  | memrefGet arr i => exact ⟨(arr.lookup V) i, rfl⟩
  | extCall _ _ _ => exact ⟨CryptoTy.default t, rfl⟩

/-- Pure expression denotation simplifies: bind with pure body is just substitution. -/
theorem CExpr.denote_pure_bind {Γ : Ctx} {t s : CryptoTy}
    (e : CExpr Γ t) (_hp : e.isPure = true) (V : HVec Γ)
    (v : t.denote) (hv : e.denote V = SPComp.pure v)
    (k : t.denote → SPComp s.denote) :
    SPComp.bind (e.denote V) k = k v := by
  rw [hv, SPComp.pure_bind]

/-! ## Section 7: Observational Equivalence and Distance -/

/-- Observational equivalence of CryptoSSA programs: equal denotation for all valuations. -/
def progEquiv (p q : CProg Γ t) : Prop :=
  ∀ V : HVec Γ, p.denote V = q.denote V

/-- Statistical distance between CryptoSSA programs:
    supremum over all valuations of the sdist. -/
noncomputable def progSdist (p q : CProg Γ t) : ℝ≥0∞ :=
  ⨆ V : HVec Γ, sdist (fun (_ : Unit) => p.denote V) (fun (_ : Unit) => q.denote V)

/-! ## Section 8: Basic Properties of progEquiv -/

@[refl]
theorem progEquiv_refl (p : CProg Γ t) : progEquiv p p :=
  fun _ => rfl

@[symm]
theorem progEquiv_symm {p q : CProg Γ t} (h : progEquiv p q) : progEquiv q p :=
  fun V => (h V).symm

theorem progEquiv_trans {p q r : CProg Γ t}
    (h₁ : progEquiv p q) (h₂ : progEquiv q r) : progEquiv p r :=
  fun V => (h₁ V).trans (h₂ V)

/-- progEquiv implies progSdist = 0. -/
theorem progSdist_of_equiv {p q : CProg Γ t} (h : progEquiv p q) :
    progSdist p q = 0 := by
  simp only [progSdist]
  apply le_antisymm
  · apply iSup_le; intro V
    have : (fun (_ : Unit) => p.denote V) = (fun (_ : Unit) => q.denote V) :=
      funext fun _ => h V
    rw [this, sdist_self]
  · exact zero_le _

/-- progSdist is symmetric. -/
theorem progSdist_symm (p q : CProg Γ t) : progSdist p q = progSdist q p := by
  simp only [progSdist]
  congr 1; funext V; exact sdist_sym _ _

/-- progSdist satisfies the triangle inequality. -/
theorem progSdist_triangle (p q r : CProg Γ t) :
    progSdist p r ≤ progSdist p q + progSdist q r := by
  apply iSup_le; intro V
  calc sdist (fun _ => p.denote V) (fun _ => r.denote V)
      ≤ sdist (fun _ => p.denote V) (fun _ => q.denote V) +
        sdist (fun _ => q.denote V) (fun _ => r.denote V) :=
        sdist_triangle _ _ _
    _ ≤ progSdist p q + progSdist q r :=
        add_le_add (le_iSup_of_le V le_rfl) (le_iSup_of_le V le_rfl)

/-! ## Section 9: Denotation Simplification Lemmas -/

/-- Denotation of a let-binding with a pure expression simplifies to substitution. -/
theorem CProg.denote_letBind_pure {Γ : Ctx} {t s : CryptoTy}
    (e : CExpr Γ t) (body : CProg (t :: Γ) s) (V : HVec Γ)
    (v : t.denote) (hv : e.denote V = SPComp.pure v) :
    (CProg.letBind e body).denote V = body.denote (V.extend v) := by
  simp only [CProg.denote, hv, SPComp.pure_bind]

/-- Denotation of a return is pure. -/
@[simp]
theorem CProg.denote_ret (v : CVar Γ t) (V : HVec Γ) :
    (CProg.ret v).denote V = SPComp.pure (v.lookup V) := rfl

/-- Denotation of a let-binding unfolds to bind. -/
@[simp]
theorem CProg.denote_letBind (e : CExpr Γ t) (body : CProg (t :: Γ) s) (V : HVec Γ) :
    (CProg.letBind e body).denote V =
    SPComp.bind (e.denote V) (fun val => body.denote (V.extend val)) := rfl

/-! ## Section 10: XOR Bijection (Key for OTP) -/

/-- XOR with a fixed Bool is a bijection.
    This is the core argument for OTP security. -/
def xorBij (m : Bool) : Bool ≃ Bool where
  toFun k := xor k m
  invFun c := xor c m
  left_inv k := by cases k <;> cases m <;> rfl
  right_inv c := by cases c <;> cases m <;> rfl

/-- Sampling a bit and XORing with a constant has the same distribution
    as sampling directly. This lifts the bijection to SPComp. -/
theorem sample_xor_eq_sample (m : Bool) :
    SPComp.bind (SPComp.sample Bool) (fun k => SPComp.pure (Bool.xor k m)) =
    SPComp.bind (SPComp.sample Bool) (fun c => SPComp.pure c) := by
  have : (fun k => SPComp.pure (Bool.xor k m)) = (fun k => (SPComp.pure ∘ (xorBij m)) k) := rfl
  rw [this, show SPComp.pure ∘ (xorBij m) = fun k => SPComp.pure (id ((xorBij m) k)) from rfl]
  rw [SPComp.sample_bind_pure_equiv (xorBij m) id]
  simp [id]

/-- More general version: sampling and XOR-then-f equals sampling and f. -/
theorem sample_xor_bind_eq (m : Bool) (k : Bool → SPComp γ) :
    SPComp.bind (SPComp.sample Bool) (fun b => k (Bool.xor b m)) =
    SPComp.bind (SPComp.sample Bool) k :=
  SPComp.sample_bind_equiv (xorBij m) k

/-! ## Section 11: Program Size -/

/-- Number of let-bindings in a program. -/
def CProg.size : CProg Γ t → Nat
  | .ret _ => 0
  | .letBind _ body => 1 + body.size

end CatCrypt.Crypto.SecureCompilation.CryptoSSA
