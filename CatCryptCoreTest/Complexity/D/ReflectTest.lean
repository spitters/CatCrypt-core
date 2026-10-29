/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.Reflect
public import CatCryptCoreTest.Complexity.D.Examples
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
  xorSampleL.d_den O k

/-- The emitted cost theorem: a sample, its β-step and one word operation. -/
example (k : BitVec 8) : xorSampleL.d.cost (Env.nil.cons (τ := .word 8) k) ≤ 3 :=
  (xorSampleL.d_cost k).trans
    (Nat.add_le_add_left (Nat.add_le_add_left (Finset.sup_le fun _ _ => le_refl 1) 1) 1)

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
    (O : CTree.Oracle) (hA : ∀ v, (g v).run O = A v) (k : BitVec 8) :
    advRun.d.denote O ((Env.nil.cons (τ := .arr (.word 8) .bool) g).cons (τ := .word 8) k) =
      advRun A k :=
  advRun.d_den O A g hA k

/-- The emitted cost theorem: an adversary call of cost at most `a` costs at most `a` plus the
sample, the word operation, the bind steps and the negation. -/
example (A : BitVec 8 → SPComp Bool) (a : ℕ) (g : Val (.arr (.word 8) .bool))
    (hC : ∀ v, (g v).cost ≤ a) (k : BitVec 8) :
    advRun.d.cost ((Env.nil.cons (τ := .arr (.word 8) .bool) g).cons (τ := .word 8) k) ≤
      a + 6 :=
  by
  refine (advRun.d_cost a A g hC k).trans (le_trans (Nat.add_le_add_left (Nat.add_le_add_left
    (Finset.sup_le (a := a + 4) fun v _ => ?_) 1) 1) (by omega))
  refine le_trans (Nat.add_le_add_left (Nat.add_le_add_left
    (Finset.sup_le (a := 1) fun _ _ => ?_) 1) _) ?_
  · simp only [Prim.cost]; omega
  · simp only [Prim.cost]; omega

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
  CatCrypt.Crypto.QueryBoundedUC.exD.d_den O x

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

/-- The product costs the square of the bit length of the modulus, plus one (the emitted
cost theorem). -/
example (x y : ZMod 7) :
    zMul.d.cost ((Env.nil.cons (τ := .fin 6) x).cons (τ := .fin 6) y) =
      (6 + 1).size * (6 + 1).size + 1 := by
  rw [zMul.d_cost x y]
  rfl

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

/-! ## Reductions over computation trees

Two trees of the shape `derive_reduction` builds: the type parameters are represented by finite
ground types (`FTy.den MF`), the primitives are function parameters, the adversary a
tree-valued parameter. `reflect_d` proves that the D-term means the compilation of the tree at
the oracle `O` of the adversary's hypothesis, and bounds its cost by the cost parameters of the
primitives and of the adversary. -/

/-- Sample a key of a generic type and call the adversary on its image under a primitive. -/
def sampleCall (M : Type) [Fintype M] [Nonempty M] (F : M → M) (A : M → SPTree Bool) :
    SPTree Bool :=
  SPTree.sample M inferInstance inferInstance fun k => A (F k)

reflect_d sampleCall

example (MF : FTy) (O : CTree.Oracle) (F : MF.den → MF.den) (gF : Val (.arr (.base MF) (.base MF)))
    (hF : ∀ v, gF v = .ret (F v)) (A : MF.den → SPTree Bool) (gA : Val (.arr (.base MF) .bool))
    (hA : ∀ v, (gA v).run O = (A v).compile) :
    (sampleCall.d MF).denote O ((Env.nil.cons (τ := .arr (.base MF) (.base MF)) gF).cons
      (τ := .arr (.base MF) .bool) gA) = (sampleCall MF.den F A).compile :=
  sampleCall.d_den MF O F gF hF A gA hA

/-- The cost theorem: the sample, the primitive at the key (cost `FCost`), the adversary call
(cost at most `ACost`) and four steps. -/
example (MF : FTy) (FCost : MF.den → ℕ) (ACost : ℕ) (F : MF.den → MF.den)
    (gF : Val (.arr (.base MF) (.base MF)))
    (hF : ∀ v, gF v = stepN CTree.tick (FCost v) (.ret (F v))) (A : MF.den → SPTree Bool)
    (gA : Val (.arr (.base MF) .bool)) (hA : ∀ v, (gA v).cost ≤ ACost) (f : ℕ)
    (hf : ∀ v, FCost v ≤ f) :
    (sampleCall.d MF).cost ((Env.nil.cons (τ := .arr (.base MF) (.base MF)) gF).cons
      (τ := .arr (.base MF) .bool) gA) ≤ f + ACost + 4 := by
  refine (sampleCall.d_cost MF FCost ACost F gF hF A gA hA).trans (le_trans
    (Nat.add_le_add_left (Nat.add_le_add_left
      (Finset.sup_le (a := f + ACost + 2) fun x _ => ?_) 1) 1) (by omega))
  have := hf x
  omega

/-- Run a key generator, then the adversary on the key and a sampled residue plus one. -/
def keygenBind (n : ℕ) (K : Type) [Fintype K] [Nonempty K] (gen : Unit → SPTree K)
    (A : K × Fin (n + 1) → SPTree Bool) : SPTree Bool :=
  (gen ()).bind fun pk =>
    SPTree.sample (Fin (n + 1)) inferInstance inferInstance fun r => A (pk, r + 1)

reflect_d keygenBind

example (n : ℕ) (KF : FTy) (O : CTree.Oracle) (gen : Unit → SPTree KF.den)
    (gG : Val (.arr .unit (.base KF))) (hG : ∀ v, (gG v).run O = (gen v).compile)
    (A : KF.den × Fin (n + 1) → SPTree Bool) (gA : Val (.arr (.prod (.base KF) (.fin n)) .bool))
    (hA : ∀ v, (gA v).run O = (A v).compile) :
    (keygenBind.d n KF).denote O ((Env.nil.cons (τ := .arr .unit (.base KF)) gG).cons
      (τ := .arr (.prod (.base KF) (.fin n)) .bool) gA) = (keygenBind n KF.den gen A).compile :=
  keygenBind.d_den n KF O gen gG hG A gA hA

/-- The cost theorem of the keygen-bind reduction. -/
example (n : ℕ) (KF : FTy) (GCost ACost : ℕ) (gen : Unit → SPTree KF.den)
    (gG : Val (.arr .unit (.base KF))) (hG : ∀ v, (gG v).cost ≤ GCost)
    (A : KF.den × Fin (n + 1) → SPTree Bool) (gA : Val (.arr (.prod (.base KF) (.fin n)) .bool))
    (hA : ∀ v, (gA v).cost ≤ ACost) :
    (keygenBind.d n KF).cost ((Env.nil.cons (τ := .arr .unit (.base KF)) gG).cons
      (τ := .arr (.prod (.base KF) (.fin n)) .bool) gA) ≤
      GCost + ACost + (n + 1).size + 6 := by
  refine (keygenBind.d_cost n KF GCost ACost gen gG hG A gA hA).trans (le_trans
    (Nat.add_le_add_left (Nat.add_le_add_left
      (Finset.sup_le (a := (n + 1).size + ACost + 4) fun v _ => ?_) 1) _) ?_)
  · refine le_trans (Nat.add_le_add_left (Nat.add_le_add_left
      (Finset.sup_le (a := (n + 1).size + ACost + 2) fun _ _ => ?_) 1) 1) (by omega)
    simp only [Prim.cost]; omega
  · omega

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
