/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.Reflect
public import CatCryptCore.Complexity.D.Examples
public import CatCryptCore.Crypto.QueryBoundedUC

/-!
# Tests for `reflect_d`

Lean definitions reflected into D by `reflect_d`, each with its denotation theorem:

* the definitions behind D's examples (`CatCryptCore.Complexity.D.Examples`): the sum of a
  list by `List.foldl`, a function applied twice to the successor (on `ℕ` and on bytes) and a
  sampled byte XOR a key; their D-terms have the costs proved there (`sumBody_cost_le`,
  `twice_succ_cost`, `twice_succW_cost`, `xorSample_cost`);
* matches on `Option`, `Sum`, `List` and pairs, `if` on a compound condition, `Nat.iterate`, a
  `let`-bound function, an `Option` result;
* a parameter function and an adversary `BitVec 8 → SPComp Bool` in the context;
* reads and writes of a location;
* the distinguisher `exD` of `CatCryptCore.Crypto.QueryBoundedUC`;
* arithmetic, comparisons and casts on `ZMod 7` and `Fin 5`, the cost of a product of
  residues, and a sampled residue with a failure branch;
* the refusals of a recursive definition, of a type without representation and of a constant
  outside the fragment.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D.ReflectTest

open CatCrypt.Core CatCrypt.Complexity.D

/-- `BitVec w` is equivalent to `Fin (2 ^ w)`; the Mathlib of this toolchain has no
`Fintype (BitVec w)` instance. -/
local instance instFintypeBitVec (w : ℕ) : Fintype (BitVec w) :=
  Fintype.ofEquiv (Fin (2 ^ w))
    { toFun := BitVec.ofFin, invFun := BitVec.toFin,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }

/-! ## The examples of D -/

/-- The sum of a list. -/
def sumL (l : List ℕ) : ℕ := List.foldl (· + ·) 0 l

reflect_d sumL

example (l : List ℕ) :
    sumL.d.den (Env.nil.cons (τ := .list .nat) l) = .ret (sumL l) := sumL.d_den l

/-- The D-term of `sumL` costs what `Examples.sumBody` costs. -/
example (l : List ℕ) :
    sumL.d.cost (Env.nil.cons (τ := .list .nat) l) ≤ l.length * (l.sum.size + 2) := by
  have h : sumL.d.cost (Env.nil.cons (τ := .list .nat) l) =
      Examples.sumBody.cost (Env.nil.cons (τ := .list .nat) l) := rfl
  exact h ▸ Examples.sumBody_cost_le l

/-- A function applied twice to the successor. -/
def twiceSucc (n : ℕ) : ℕ := (fun (f : ℕ → ℕ) (x : ℕ) => f (f x)) (fun y => y + 1) n

reflect_d twiceSucc

example (n : ℕ) : twiceSucc.d.cost (Env.nil.cons (τ := .nat) n) =
    6 + max n.size 1 + max (n + 1).size 1 := by
  have h : twiceSucc.d.cost (Env.nil.cons (τ := .nat) n) =
      (Tm.app (Tm.app Examples.twice Examples.succT) (Tm.natLit n)).cost Env.nil := rfl
  exact h.trans (Examples.twice_succ_cost n)

/-- A function applied twice to the successor on bytes. -/
def twiceSuccW (x : BitVec 8) : BitVec 8 :=
  (fun (f : BitVec 8 → BitVec 8) (y : BitVec 8) => f (f y)) (fun y => y + 1) x

reflect_d twiceSuccW

example (x : BitVec 8) : twiceSuccW.d.cost (Env.nil.cons (τ := .word 8) x) = 6 := rfl

/-- A sampled byte XOR a key. -/
noncomputable def xorSampleL (k : BitVec 8) : SPComp (BitVec 8) := do
  let x ← SPComp.sample (BitVec 8)
  pure (x ^^^ k)

reflect_d xorSampleL

example (O : CTree.Oracle) (k : BitVec 8) :
    xorSampleL.d.denote O (Env.nil.cons (τ := .word 8) k) = xorSampleL k :=
  xorSampleL.d_den k O

example (k : BitVec 8) : xorSampleL.d.cost (Env.nil.cons (τ := .word 8) k) = 3 := by
  have h : xorSampleL.d.cost (Env.nil.cons (τ := .word 8) k) =
      (Examples.xorSample k).cost Env.nil := rfl
  exact h.trans (Examples.xorSample_cost k)

/-! ## Matches, conditions and recursion schemes -/

/-- A match on an `Option` parameter. -/
def optD (o : Option ℕ) (d : ℕ) : ℕ :=
  match o with
  | none => d
  | some x => x + d

reflect_d optD

example (o : Option ℕ) (d : ℕ) :
    optD.d.den ((Env.nil.cons (τ := .sum .unit .nat) (Reflect.optEnc o)).cons (τ := .nat) d) =
      .ret (optD o d) := optD.d_den o d

/-- A match on a sum, with an `if` in a branch. -/
def sumE (s : ℕ ⊕ Bool) : ℕ :=
  match s with
  | .inl n => n * 2
  | .inr b => if b = true then 1 else 0

reflect_d sumE

/-- A non-recursive match on a list. -/
def headOr (l : List ℕ) : ℕ :=
  match l with
  | [] => 0
  | x :: _ => x

reflect_d headOr

/-- `Nat.iterate` as `iter`. -/
def iterAdd (n : ℕ) : ℕ := Nat.iterate (fun x => x + 2) n 0

reflect_d iterAdd

/-- A compound condition. -/
def minN (a b : ℕ) : ℕ := if a ≤ b ∧ a ≠ 7 then a else b

reflect_d minN

/-- A match on a pair. -/
def swapP (p : ℕ × Bool) : Bool × ℕ :=
  let (a, b) := p
  (b, a + 1)

reflect_d swapP

/-- A `let`-bound function. -/
def letF (n : ℕ) : ℕ :=
  let g := fun y : ℕ => y * 3
  g (g n)

reflect_d letF

/-- An `Option` result. -/
def optRet (n : ℕ) : Option ℕ := if n = 0 then none else some (n - 1)

reflect_d optRet

example (n : ℕ) : optRet.d.den (Env.nil.cons (τ := .nat) n) = .ret (Reflect.optEnc (optRet n)) :=
  optRet.d_den n

/-! ## Function parameters -/

/-- A parameter function applied twice. -/
def applyA (A : ℕ → ℕ) (n : ℕ) : ℕ := A (A n + 1)

reflect_d applyA

/-- An adversary run on a masked byte. -/
noncomputable def advRun (A : BitVec 8 → SPComp Bool) (k : BitVec 8) : SPComp Bool := do
  let x ← SPComp.sample (BitVec 8)
  let b ← A (x ^^^ k)
  pure (!b)

reflect_d advRun

example (A : BitVec 8 → SPComp Bool) (g : Val (.arr (.word 8) .bool))
    (hA : ∀ v O, (g v).run O = A v) (k : BitVec 8) (O : CTree.Oracle) :
    advRun.d.denote O ((Env.nil.cons (τ := .arr (.word 8) .bool) g).cons (τ := .word 8) k) =
      advRun A k :=
  advRun.d_den A g hA k O

/-! ## State -/

/-- Read a byte, write its successor, return the byte. -/
noncomputable def getSet : SPComp (BitVec 8) := do
  let v : BitVec 8 ← SPComp.get ((FTy.word 8).loc 3)
  SPComp.set ((FTy.word 8).loc 3) (v + 1)
  pure v

reflect_d getSet

/-! ## A definition of the crypto tree -/

reflect_d CatCrypt.Crypto.QueryBoundedUC.exD

example (x : Unit ⊕ Bool) (O : CTree.Oracle) :
    CatCrypt.Crypto.QueryBoundedUC.exD.d.denote O (Env.nil.cons (τ := .sum .unit .bool) x) =
      CatCrypt.Crypto.QueryBoundedUC.exD x :=
  CatCrypt.Crypto.QueryBoundedUC.exD.d_den x O

/-- `exD` costs one branch. -/
example (x : Unit ⊕ Bool) :
    CatCrypt.Crypto.QueryBoundedUC.exD.d.cost (Env.nil.cons (τ := .sum .unit .bool) x) = 1 := by
  cases x <;> rfl

/-! ## Residues and failure -/

/-- An affine map on `ZMod 7`. -/
def zAffine (x y : ZMod 7) : ZMod 7 := 3 * x + y - 1

reflect_d zAffine

example (x y : ZMod 7) :
    zAffine.d.den ((Env.nil.cons (τ := .fin 6) x).cons (τ := .fin 6) y) =
      .ret (zAffine x y) :=
  zAffine.d_den x y

/-- A product of residues. -/
def zMul (x y : ZMod 7) : ZMod 7 := x * y

reflect_d zMul

/-- The product costs the square of the bit length of the modulus, plus one. -/
example (x y : ZMod 7) :
    zMul.d.cost ((Env.nil.cons (τ := .fin 6) x).cons (τ := .fin 6) y) =
      (6 + 1).size * (6 + 1).size + 1 := rfl

/-- Comparisons and the representative on `Fin 5`. -/
def finCmp (x y : Fin 5) : ℕ := if x = y ∨ x < y then x.val else y.val

reflect_d finCmp

example (x y : Fin 5) :
    finCmp.d.den ((Env.nil.cons (τ := .fin 4) x).cons (τ := .fin 4) y) = .ret (finCmp x y) :=
  finCmp.d_den x y

/-- The cast of a natural number into `ZMod 7`, and its representative. -/
def zCast (k : ℕ) : ℕ := ((k : ZMod 7) + 1).val

reflect_d zCast

example (k : ℕ) : zCast.d.den (Env.nil.cons (τ := .nat) k) = .ret (zCast k) :=
  zCast.d_den k

/-- A sampled residue squared, with failure at zero. -/
noncomputable def zSampleSq : SPComp (ZMod 7) := do
  let x ← SPComp.sample (ZMod 7)
  if x = 0 then SPComp.fail else pure (x * x)

reflect_d zSampleSq

example (O : CTree.Oracle) : zSampleSq.d.denote O Env.nil = zSampleSq :=
  zSampleSq.d_den O

/-! ## Refusals -/

/-- A definition by structural recursion. -/
def recLen : List ℕ → ℕ
  | [] => 0
  | _ :: xs => recLen xs + 1

/-- error: reflect_d: the recursion `List.brecOn` (use List.foldl or Nat.iterate) -/
#guard_msgs in
reflect_d recLen

/-- An operation on `Int`. -/
def intAdd (a b : Int) : Int := a + b

/-- error: reflect_d: the type `ℤ` has no representation in D -/
#guard_msgs in
reflect_d intAdd

/-- A rotation, which is not a primitive of D. -/
def rotL (x : BitVec 8) : BitVec 8 := x.rotateLeft 3

/-- error: reflect_d: the constant `BitVec.rotateLeft` in `x.rotateLeft 3` -/
#guard_msgs in
reflect_d rotL

end CatCrypt.Complexity.D.ReflectTest
