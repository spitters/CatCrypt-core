/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.Tree

/-!
# Syntax of the deep language D

D is a typed call-by-value λ-calculus with ground data, recursion schemes and the effects of
`SPComp`. Its cost model is that of the weak call-by-value λ-calculus L of Forster and Kunze
(Forster, Kunze, *A certifying extraction with time bounds from Coq to call-by-value
λ-calculus*, ITP 2019; Forster, Kunze, Roth, *The weak call-by-value λ-calculus is reasonable
for both time and space*, POPL 2020): time is the number of β-steps, extended here with
primitive operations and with effect nodes of unit cost (`SPTree.queryCost`). A primitive
operation costs `Prim.cost`: on `ℕ`, its cost in the bit lengths `Nat.size` of its arguments
(logarithmic cost); on `Bool` and fixed-width words, one step. The evaluator and the
cost semantics are in `CatCryptCore.Complexity.D.Semantics` and
`CatCryptCore.Complexity.D.Cost`.

## Terms

Terms `Tm Γ τ` are intrinsically typed and scoped: `Γ : List Ty` is the context, a variable
`Var Γ τ` is a de Bruijn index into it. The constructors are variables, `lam`, `app`, `letE`
and `seq`; literals `natLit` and `lit` (ground values of type `FTy`); primitive operations
`prim` (`Prim`); pairs with `fst`, `snd`; sums with `inl`, `inr` and `case`; `ite`; lists with
`nil`, `cons` and the constructor match `lcase`; the recursion schemes `foldl` (over a list)
and `iter` (over `ℕ`); the effects `sample`, `get`, `set`, `query` and `fail`. An effect is an
expression in call-by-value style (Moggi's λc): `letE (sample f) b` samples and continues with
the D-term `b`, which is the continuation of the effect.

## Recursion

D has no general fixed point. Recursion is structural, through `foldl` and `iter`, so that
every term denotes a total function and the evaluator is defined by structural recursion on
the term without fuel. For the reflection of Lean definitions (G3b) this means that a
definition by structural recursion on `List` or `ℕ` is reflected through `foldl`, `iter` or
`lcase`; a definition by well-founded recursion is reflected only after a bound on its
recursion depth is supplied, as an `iter` whose state carries a sum type for termination.

## The `TExpr` fragment

The constructs of hax-lean's typed IR `TExpr` map to D as follows (the structural embedding is
row G3d):

* `lit`: `natLit` or `lit` (`bool`, and `uintLit`/`sintLit`/`int` at the word width given by
  the type annotation); `unitVal`: `lit .unit ()`;
* `var name`: `var` at the de Bruijn index of `name`;
* `letBind name val body`: `letE val body`; `seq e1 e2`: `seq e1 e2`;
* `lam params body`: nested `lam` (over a tuple of the parameters when uncurried);
* `app f args`: `app` of the function's variable (or `prim` for a registered operation) to the
  tuple of the arguments;
* `tuple elems`: nested `pair`; `proj e i`: a chain of `fst`/`snd`;
* `ifThenElse c t e`: `ite`;
* `match_ scrut arms` on `ImpPat`: `wildcard` and `varPat` by `letE`; `tuplePat` by
  projections; `somePat`/`nonePat` and `okPat`/`errPat` by `case` on `sum unit a` and
  `sum a e`; `litPat` by `ite` on an equality `prim`; `ctorPat` by `case` on the sum of the
  constructors' products;
* the functionalized loops `forFold`, `forFoldRev` (and their `Return` forms) by `foldl` over
  the range or `iter` over its length; `whileFold` by `iter` with a bound on the number of
  iterations; `cfBreak`, `cfContinue`, `earlyReturn` and `questionMark` by a `sum`-typed loop
  state (`ControlFlow` and `Result` as sums);
* `ann e` and `namedProj` by the translation of `e`; `borrow`, `deref`, `assign` and the
  imperative loops do not occur after functionalization.

## Main definitions

* `Ty`, `Val`: the types and their values; a function value is a Lean function
  `Val a → CTree (Val b)` into costed trees.
* `Var`, `Env`: variables and environments.
* `Prim`, `Prim.apply`, `Prim.cost`: the primitive operations, their functions and their
  costs.
* `Tm`: the terms; `Tm.compose`: precomposition of function terms.
* `Ren`, `Ren.lift`, `Tm.rename`, `Tm.weaken`: renamings of variables, renaming of a term,
  and a closed term in any context; `Env.comp`: an environment read through a renaming.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D

/-! ## Types and values -/

/-- The types of D. -/
inductive Ty : Type where
  /-- A finite ground type. -/
  | base (f : FTy)
  /-- The natural numbers. -/
  | nat
  /-- Products. -/
  | prod (a b : Ty)
  /-- Sums. -/
  | sum (a b : Ty)
  /-- Call-by-value functions, effectful. -/
  | arr (a b : Ty)
  /-- Lists. -/
  | list (a : Ty)
  deriving DecidableEq

namespace Ty

/-- The unit type. -/
abbrev unit : Ty := base .unit
/-- The booleans. -/
abbrev bool : Ty := base .bool
/-- Words of `w` bits. -/
abbrev word (w : ℕ) : Ty := base (.word w)
/-- The residues modulo `n + 1`. -/
abbrev fin (n : ℕ) : Ty := base (.fin n)

/-- First-order types: no function type occurs. -/
def FO : Ty → Prop
  | base _ => True
  | nat => True
  | prod a b => a.FO ∧ b.FO
  | sum a b => a.FO ∧ b.FO
  | arr _ _ => False
  | list a => a.FO

end Ty

/-- The values of a type. A function value is a Lean function into costed trees; the
evaluator produces such functions only from `lam`, so their costs are those of the bodies. -/
def Val : Ty → Type
  | .base f => f.den
  | .nat => ℕ
  | .prod a b => Val a × Val b
  | .sum a b => Val a ⊕ Val b
  | .arr a b => Val a → CTree (Val b)
  | .list a => List (Val a)

/-! ## Variables and environments -/

/-- De Bruijn variables: `Var Γ τ` is a position of `τ` in `Γ`. -/
inductive Var : List Ty → Ty → Type where
  /-- The innermost variable. -/
  | here {Γ : List Ty} {τ : Ty} : Var (τ :: Γ) τ
  /-- A variable under one more binder. -/
  | there {Γ : List Ty} {σ τ : Ty} : Var Γ τ → Var (σ :: Γ) τ

theorem Var.mem {Γ : List Ty} {τ : Ty} : Var Γ τ → τ ∈ Γ
  | .here => List.mem_cons_self
  | .there x => List.mem_cons_of_mem _ x.mem

/-- Environments: a value for every variable of the context. -/
def Env (Γ : List Ty) : Type := (τ : Ty) → Var Γ τ → Val τ

/-- The empty environment. -/
def Env.nil : Env [] := fun _ x => nomatch x

/-- Extend an environment by a value for the innermost variable. -/
def Env.cons {Γ : List Ty} {τ : Ty} (v : Val τ) (ρ : Env Γ) : Env (τ :: Γ) :=
  fun _ x => match x with
    | .here => v
    | .there y => ρ _ y

/-! ## Primitive operations -/

/-- The primitive operations on `ℕ`, `Bool`, fixed-width words and the residues
`Fin (n + 1)`. Binary operations take a pair. -/
inductive Prim : Ty → Ty → Type where
  | natAdd : Prim (.prod .nat .nat) .nat
  | natSub : Prim (.prod .nat .nat) .nat
  | natMul : Prim (.prod .nat .nat) .nat
  | natDiv : Prim (.prod .nat .nat) .nat
  | natMod : Prim (.prod .nat .nat) .nat
  | natEq : Prim (.prod .nat .nat) .bool
  | natLt : Prim (.prod .nat .nat) .bool
  | bnot : Prim .bool .bool
  | band : Prim (.prod .bool .bool) .bool
  | bor : Prim (.prod .bool .bool) .bool
  | bxor : Prim (.prod .bool .bool) .bool
  | wadd (w : ℕ) : Prim (.prod (.word w) (.word w)) (.word w)
  | wsub (w : ℕ) : Prim (.prod (.word w) (.word w)) (.word w)
  | wmul (w : ℕ) : Prim (.prod (.word w) (.word w)) (.word w)
  | wand (w : ℕ) : Prim (.prod (.word w) (.word w)) (.word w)
  | wor (w : ℕ) : Prim (.prod (.word w) (.word w)) (.word w)
  | wxor (w : ℕ) : Prim (.prod (.word w) (.word w)) (.word w)
  | wnot (w : ℕ) : Prim (.word w) (.word w)
  | wshl (w : ℕ) : Prim (.prod (.word w) .nat) (.word w)
  | wshr (w : ℕ) : Prim (.prod (.word w) .nat) (.word w)
  | weq (w : ℕ) : Prim (.prod (.word w) (.word w)) .bool
  | wult (w : ℕ) : Prim (.prod (.word w) (.word w)) .bool
  | wofNat (w : ℕ) : Prim .nat (.word w)
  | wtoNat (w : ℕ) : Prim (.word w) .nat
  | wcast (w v : ℕ) : Prim (.word w) (.word v)
  | finAdd (n : ℕ) : Prim (.prod (.fin n) (.fin n)) (.fin n)
  | finSub (n : ℕ) : Prim (.prod (.fin n) (.fin n)) (.fin n)
  | finMul (n : ℕ) : Prim (.prod (.fin n) (.fin n)) (.fin n)
  | finEq (n : ℕ) : Prim (.prod (.fin n) (.fin n)) .bool
  | finLt (n : ℕ) : Prim (.prod (.fin n) (.fin n)) .bool
  | finOfNat (n : ℕ) : Prim .nat (.fin n)
  | finToNat (n : ℕ) : Prim (.fin n) .nat

/-- The function computed by a primitive operation. -/
def Prim.apply {a b : Ty} : Prim a b → Val a → Val b
  | .natAdd => fun (x : ℕ × ℕ) => x.1 + x.2
  | .natSub => fun (x : ℕ × ℕ) => x.1 - x.2
  | .natMul => fun (x : ℕ × ℕ) => x.1 * x.2
  | .natDiv => fun (x : ℕ × ℕ) => x.1 / x.2
  | .natMod => fun (x : ℕ × ℕ) => x.1 % x.2
  | .natEq => fun (x : ℕ × ℕ) => (decide (x.1 = x.2) : Bool)
  | .natLt => fun (x : ℕ × ℕ) => (decide (x.1 < x.2) : Bool)
  | .bnot => fun (x : Bool) => !x
  | .band => fun (x : Bool × Bool) => x.1 && x.2
  | .bor => fun (x : Bool × Bool) => x.1 || x.2
  | .bxor => fun (x : Bool × Bool) => x.1 ^^ x.2
  | .wadd w => fun (x : BitVec w × BitVec w) => x.1 + x.2
  | .wsub w => fun (x : BitVec w × BitVec w) => x.1 - x.2
  | .wmul w => fun (x : BitVec w × BitVec w) => x.1 * x.2
  | .wand w => fun (x : BitVec w × BitVec w) => x.1 &&& x.2
  | .wor w => fun (x : BitVec w × BitVec w) => x.1 ||| x.2
  | .wxor w => fun (x : BitVec w × BitVec w) => x.1 ^^^ x.2
  | .wnot w => fun (x : BitVec w) => x.not
  | .wshl w => fun (x : BitVec w × ℕ) => x.1 <<< x.2
  | .wshr w => fun (x : BitVec w × ℕ) => x.1 >>> x.2
  | .weq w => fun (x : BitVec w × BitVec w) => (decide (x.1 = x.2) : Bool)
  | .wult w => fun (x : BitVec w × BitVec w) => BitVec.ult x.1 x.2
  | .wofNat w => fun (x : ℕ) => BitVec.ofNat w x
  | .wtoNat w => fun (x : BitVec w) => x.toNat
  | .wcast w v => fun (x : BitVec w) => x.setWidth v
  | .finAdd n => fun (x : Fin (n + 1) × Fin (n + 1)) => x.1 + x.2
  | .finSub n => fun (x : Fin (n + 1) × Fin (n + 1)) => x.1 - x.2
  | .finMul n => fun (x : Fin (n + 1) × Fin (n + 1)) => x.1 * x.2
  | .finEq n => fun (x : Fin (n + 1) × Fin (n + 1)) => (decide (x.1 = x.2) : Bool)
  | .finLt n => fun (x : Fin (n + 1) × Fin (n + 1)) => (decide (x.1 < x.2) : Bool)
  | .finOfNat n => fun (x : ℕ) => (⟨x % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩ : Fin (n + 1))
  | .finToNat n => fun (x : Fin (n + 1)) => x.val

/-- The cost of a primitive operation at an argument, in evaluation steps. On `ℕ` it is
logarithmic in the bit lengths `Nat.size` of the arguments: addition, subtraction and the
comparisons cost `max (size x) (size y) + 1`, multiplication, division and remainder cost
`size x * size y + 1` (schoolbook). The operations on `Bool` and on `w`-bit words cost one
step, the word-RAM convention for a fixed word width. The shifts `wshl` and `wshr` cost one
step although their amount is a natural number: an amount of at least `w` gives the zero word,
so only amounts below the word width are meaningful. `wofNat` costs one step: it reads the
low `w` bits of its argument. The operations on the residues `Fin (n + 1)` cost in the bit
length `s = Nat.size (n + 1)` of the modulus, since the modulus may grow with a security
parameter: addition, subtraction and the comparisons `s + 1`, multiplication `s * s + 1`,
reduction of a natural number `x` (`finOfNat`) `size x * s + 1`; reading the representative
(`finToNat`) costs one step. -/
def Prim.cost {a b : Ty} : Prim a b → Val a → ℕ
  | .natAdd => fun (x : ℕ × ℕ) => max x.1.size x.2.size + 1
  | .natSub => fun (x : ℕ × ℕ) => max x.1.size x.2.size + 1
  | .natMul => fun (x : ℕ × ℕ) => x.1.size * x.2.size + 1
  | .natDiv => fun (x : ℕ × ℕ) => x.1.size * x.2.size + 1
  | .natMod => fun (x : ℕ × ℕ) => x.1.size * x.2.size + 1
  | .natEq => fun (x : ℕ × ℕ) => max x.1.size x.2.size + 1
  | .natLt => fun (x : ℕ × ℕ) => max x.1.size x.2.size + 1
  | .bnot => fun _ => 1
  | .band => fun _ => 1
  | .bor => fun _ => 1
  | .bxor => fun _ => 1
  | .wadd _ => fun _ => 1
  | .wsub _ => fun _ => 1
  | .wmul _ => fun _ => 1
  | .wand _ => fun _ => 1
  | .wor _ => fun _ => 1
  | .wxor _ => fun _ => 1
  | .wnot _ => fun _ => 1
  | .wshl _ => fun _ => 1
  | .wshr _ => fun _ => 1
  | .weq _ => fun _ => 1
  | .wult _ => fun _ => 1
  | .wofNat _ => fun _ => 1
  | .wtoNat _ => fun _ => 1
  | .wcast _ _ => fun _ => 1
  | .finAdd n => fun _ => (n + 1).size + 1
  | .finSub n => fun _ => (n + 1).size + 1
  | .finMul n => fun _ => (n + 1).size * (n + 1).size + 1
  | .finEq n => fun _ => (n + 1).size + 1
  | .finLt n => fun _ => (n + 1).size + 1
  | .finOfNat n => fun (x : ℕ) => x.size * (n + 1).size + 1
  | .finToNat _ => fun _ => 1

theorem Prim.fo {a b : Ty} (p : Prim a b) : a.FO ∧ b.FO := by
  cases p <;> simp [Ty.FO]

/-! ## Terms -/

/-- Intrinsically typed and scoped terms of D. -/
inductive Tm : List Ty → Ty → Type where
  | var {Γ : List Ty} {τ : Ty} : Var Γ τ → Tm Γ τ
  | lam {Γ : List Ty} {a b : Ty} : Tm (a :: Γ) b → Tm Γ (.arr a b)
  | app {Γ : List Ty} {a b : Ty} : Tm Γ (.arr a b) → Tm Γ a → Tm Γ b
  | letE {Γ : List Ty} {a b : Ty} : Tm Γ a → Tm (a :: Γ) b → Tm Γ b
  | seq {Γ : List Ty} {a b : Ty} : Tm Γ a → Tm Γ b → Tm Γ b
  | natLit {Γ : List Ty} (n : ℕ) : Tm Γ .nat
  | lit {Γ : List Ty} (f : FTy) (v : f.den) : Tm Γ (.base f)
  | prim {Γ : List Ty} {a b : Ty} (p : Prim a b) : Tm Γ a → Tm Γ b
  | pair {Γ : List Ty} {a b : Ty} : Tm Γ a → Tm Γ b → Tm Γ (.prod a b)
  | fst {Γ : List Ty} {a b : Ty} : Tm Γ (.prod a b) → Tm Γ a
  | snd {Γ : List Ty} {a b : Ty} : Tm Γ (.prod a b) → Tm Γ b
  | inl {Γ : List Ty} {a b : Ty} : Tm Γ a → Tm Γ (.sum a b)
  | inr {Γ : List Ty} {a b : Ty} : Tm Γ b → Tm Γ (.sum a b)
  | case {Γ : List Ty} {a b c : Ty} :
      Tm Γ (.sum a b) → Tm (a :: Γ) c → Tm (b :: Γ) c → Tm Γ c
  | ite {Γ : List Ty} {c : Ty} : Tm Γ .bool → Tm Γ c → Tm Γ c → Tm Γ c
  | nil {Γ : List Ty} {a : Ty} : Tm Γ (.list a)
  | cons {Γ : List Ty} {a : Ty} : Tm Γ a → Tm Γ (.list a) → Tm Γ (.list a)
  | lcase {Γ : List Ty} {a c : Ty} :
      Tm Γ (.list a) → Tm Γ c → Tm (a :: .list a :: Γ) c → Tm Γ c
  | foldl {Γ : List Ty} {a c : Ty} :
      Tm Γ (.arr (.prod c a) c) → Tm Γ c → Tm Γ (.list a) → Tm Γ c
  | iter {Γ : List Ty} {c : Ty} : Tm Γ .nat → Tm Γ (.arr c c) → Tm Γ c → Tm Γ c
  | sample {Γ : List Ty} (f : FTy) : Tm Γ (.base f)
  | get {Γ : List Ty} (n : ℕ) (f : FTy) : Tm Γ (.base f)
  | set {Γ : List Ty} (n : ℕ) (f : FTy) : Tm Γ (.base f) → Tm Γ .unit
  | query {Γ : List Ty} (d r : FTy) : Tm Γ (.base d) → Tm Γ (.base r)
  | fail {Γ : List Ty} {τ : Ty} : Tm Γ τ

namespace Tm

/-- The composition combinator `λg. λf. λx. g (f x)`. -/
def composeT {Γ : List Ty} {a b c : Ty} :
    Tm Γ (.arr (.arr b c) (.arr (.arr a b) (.arr a c))) :=
  lam (lam (lam (app (var (.there (.there .here))) (app (var (.there .here)) (var .here)))))

/-- Precomposition of the function term `g` by the function term `f`. -/
def compose {Γ : List Ty} {a b c : Ty} (g : Tm Γ (.arr b c)) (f : Tm Γ (.arr a b)) :
    Tm Γ (.arr a c) :=
  app (app composeT g) f

end Tm

/-! ## Renaming and weakening -/

/-- Renamings from `Γ` to `Δ`: a variable of `Δ` for every variable of `Γ`. -/
def Ren (Γ Δ : List Ty) : Type := (τ : Ty) → Var Γ τ → Var Δ τ

/-- A renaming under one more binder. -/
def Ren.lift {Γ Δ : List Ty} {σ : Ty} (r : Ren Γ Δ) : Ren (σ :: Γ) (σ :: Δ) :=
  fun _ x => match x with
    | .here => .here
    | .there y => .there (r _ y)

/-- Renaming of the variables of a term. -/
def Tm.rename {Γ Δ : List Ty} {τ : Ty} : Tm Γ τ → Ren Γ Δ → Tm Δ τ
  | .var x, r => .var (r _ x)
  | .lam b, r => .lam (b.rename r.lift)
  | .app f x, r => .app (f.rename r) (x.rename r)
  | .letE e b, r => .letE (e.rename r) (b.rename r.lift)
  | .seq e b, r => .seq (e.rename r) (b.rename r)
  | .natLit n, _ => .natLit n
  | .lit f v, _ => .lit f v
  | .prim p x, r => .prim p (x.rename r)
  | .pair x y, r => .pair (x.rename r) (y.rename r)
  | .fst p, r => .fst (p.rename r)
  | .snd p, r => .snd (p.rename r)
  | .inl x, r => .inl (x.rename r)
  | .inr x, r => .inr (x.rename r)
  | .case s l rt, r => .case (s.rename r) (l.rename r.lift) (rt.rename r.lift)
  | .ite c t e, r => .ite (c.rename r) (t.rename r) (e.rename r)
  | .nil, _ => .nil
  | .cons x xs, r => .cons (x.rename r) (xs.rename r)
  | .lcase xs n c, r => .lcase (xs.rename r) (n.rename r) (c.rename r.lift.lift)
  | .foldl f i xs, r => .foldl (f.rename r) (i.rename r) (xs.rename r)
  | .iter n f i, r => .iter (n.rename r) (f.rename r) (i.rename r)
  | .sample f, _ => .sample f
  | .get n f, _ => .get n f
  | .set n f x, r => .set n f (x.rename r)
  | .query d r' x, r => .query d r' (x.rename r)
  | .fail, _ => .fail

/-- A closed term in any context. -/
def Tm.weaken {Γ : List Ty} {τ : Ty} (t : Tm [] τ) : Tm Γ τ :=
  t.rename fun _ x => nomatch x

/-- An environment read through a renaming. -/
def Env.comp {Γ Δ : List Ty} (ρ : Env Δ) (r : Ren Γ Δ) : Env Γ := fun _ x => ρ _ (r _ x)

theorem Env.comp_lift {Γ Δ : List Ty} {σ : Ty} (ρ : Env Δ) (r : Ren Γ Δ) (v : Val σ) :
    (ρ.cons v).comp r.lift = (ρ.comp r).cons v := by
  funext τ x
  cases x <;> rfl

theorem Env.comp_lift_lift {Γ Δ : List Ty} {σ σ' : Ty} (ρ : Env Δ) (r : Ren Γ Δ)
    (u : Val σ') (v : Val σ) : ((ρ.cons u).cons v).comp r.lift.lift = ((ρ.comp r).cons u).cons v := by
  funext τ x
  rcases x with _ | (_ | _) <;> rfl

end CatCrypt.Complexity.D
