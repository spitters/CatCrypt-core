/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.Reflect

/-!
# `reflect_d` on Lean inductive types and structural recursions

A Lean inductive type is represented by `mu T.dSig`, its values by `T.dEnc`; a constructor is
`con` of the table of its children, a case analysis and the match of a structural recursion are
the eliminator `fold`, a recursive call on a child the application of the recursive results at
its position, and a recursion whose other arguments change the eliminator at a function motive.
Each definition below is fresh and reflected with its denotation theorem:

* `Bin` (two children, indexed by `Bool`): `Bin.xorAll`, `Bin.isLeaf` (a case analysis),
  `Bin.mirror` (a recursion building values), `twoNodes` (constructors), `Bin.xorAcc` (an
  accumulator);
* `Tri` (three children, indexed by `fin 2`): `Tri.sum`;
* `Ask` (a function `Bool → Ask` of children and an `Option` field): `Ask.answer`,
  `Ask.depthAt` (a fixed argument);
* `Seq α` (a type parameter, at `BitVec 8`): `Seq.count` under `countPlus` (an instance argument
  and a fixed argument);
* `Fns` (a field holding a function, its pure closure): `Fns.applyAll`;
* refusals: a recursion over `List`, a type without a constructor without recursive argument, a
  nested inductive type.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D.ReflectIndTest

open Reflect

/-! ## Two children -/

/-- Binary trees of bytes; the node is declared first. -/
inductive Bin where
  | node (l : Bin) (x : BitVec 8) (r : Bin)
  | leaf

/-- The XOR of the bytes of a tree. -/
def Bin.xorAll : Bin → BitVec 8
  | .leaf => 0
  | .node l x r => x ^^^ (l.xorAll ^^^ r.xorAll)

reflect_d Bin.xorAll

/-- The signature: the leaf first, the node with a byte and two children. -/
example : Bin.dSig = .ext (.base .unit) (.word 8) (some .bool) := rfl

example (t : Bin) : Bin.xorAll.d.den (Env.nil.cons t.dEnc) = .ret t.xorAll := Bin.xorAll.d_den t

/-- The tree `5 (3 leaf leaf) leaf`. -/
def t2 : Bin := .node (.node .leaf 3 .leaf) 5 .leaf

/-- The cost on `t2`: as for the eliminator written by hand (`MuTest.xorT_cost`), a step at the
root, a β-step per application of a recursive result and the XORs. -/
example : Bin.xorAll.d.cost (Env.nil.cons t2.dEnc) = 9 := by decide +kernel

/-- Whether a tree is a leaf: a case analysis. -/
def Bin.isLeaf (t : Bin) : Bool :=
  match t with
  | .leaf => true
  | .node .. => false

reflect_d Bin.isLeaf

example (t : Bin) : Bin.isLeaf.d.den (Env.nil.cons t.dEnc) = .ret t.isLeaf := Bin.isLeaf.d_den t

/-- The mirror image: a recursion that builds values. -/
def Bin.mirror : Bin → Bin
  | .leaf => .leaf
  | .node l x r => .node r.mirror x l.mirror

reflect_d Bin.mirror

example (t : Bin) : Bin.mirror.d.den (Env.nil.cons t.dEnc) = .ret t.mirror.dEnc :=
  Bin.mirror.d_den t

/-- Two nodes built by the constructors. -/
def twoNodes (x : BitVec 8) : Bin := .node .leaf x (.node .leaf (x + 1) .leaf)

reflect_d twoNodes

example (x : BitVec 8) : twoNodes.d.den (Env.nil.cons x) = .ret (twoNodes x).dEnc :=
  twoNodes.d_den x

/-- The XOR of the bytes into an accumulator, the right child first. -/
def Bin.xorAcc : Bin → BitVec 8 → BitVec 8
  | .leaf, acc => acc
  | .node l x r, acc => l.xorAcc (r.xorAcc (acc ^^^ x))

reflect_d Bin.xorAcc

example (t : Bin) (acc : BitVec 8) :
    Bin.xorAcc.d.den ((Env.nil.cons t.dEnc).cons acc) = .ret (t.xorAcc acc) :=
  Bin.xorAcc.d_den t acc

/-! ## Three children -/

/-- Ternary trees with a Boolean at the leaves. -/
inductive Tri where
  | leaf (b : Bool)
  | node (a : Tri) (x : BitVec 4) (b : Tri) (c : Tri)

/-- The sum of the words and leaves of a tree. -/
def Tri.sum : Tri → BitVec 4
  | .leaf b => if b then 1 else 0
  | .node a x b c => x + a.sum + b.sum + c.sum

reflect_d Tri.sum

example : Tri.dSig = .ext (.base .bool) (.word 4) (some (.fin 2)) := rfl

example (t : Tri) : Tri.sum.d.den (Env.nil.cons t.dEnc) = .ret t.sum := Tri.sum.d_den t

/-! ## A function of children -/

/-- A query tree: a result, or a question with a continuation on its Boolean answer. -/
inductive Ask where
  | done (o : Option (BitVec 8))
  | ask (q : BitVec 8) (k : Bool → Ask)

/-- The result when every answer is `true`. -/
def Ask.answer : Ask → Option (BitVec 8)
  | .done o => o
  | .ask _ k => (k true).answer

reflect_d Ask.answer

example (t : Ask) : Ask.answer.d.den (Env.nil.cons t.dEnc) = .ret (optEnc t.answer) :=
  Ask.answer.d_den t

/-- The number of questions when every answer is `b`: the fixed argument `b`. -/
def Ask.depthAt (b : Bool) : Ask → ℕ
  | .done _ => 0
  | .ask _ k => (k b).depthAt b + 1

reflect_d Ask.depthAt

example (b : Bool) (t : Ask) :
    Ask.depthAt.d.den ((Env.nil.cons (τ := .bool) b).cons t.dEnc) = .ret (t.depthAt b) :=
  Ask.depthAt.d_den b t

/-! ## A field holding a function -/

/-- A list of byte functions: a field holds a function, represented by its pure closure. -/
inductive Fns where
  | nil
  | cons (f : BitVec 8 → BitVec 8) (rest : Fns)

/-- The composite of the functions applied to a byte, the head last. -/
def Fns.applyAll (x : BitVec 8) : Fns → BitVec 8
  | .nil => x
  | .cons f r => f (r.applyAll x)

reflect_d Fns.applyAll

example (x : BitVec 8) (t : Fns) :
    Fns.applyAll.d.den ((Env.nil.cons (τ := .word 8) x).cons t.dEnc) = .ret (t.applyAll x) :=
  Fns.applyAll.d_den x t

/-- The field of the signature is a function type of D. -/
example : Fns.dSig = .ext (.base .unit) (.arr (.word 8) (.word 8)) (some .unit) := rfl

/-! ## A type parameter -/

/-- Sequences of a type parameter. -/
inductive Seq (α : Type) where
  | nil
  | cons (a : α) (rest : Seq α)

/-- The number of occurrences of `y`. -/
def Seq.count {α : Type} [DecidableEq α] (y : α) : Seq α → ℕ
  | .nil => 0
  | .cons a r => (if a = y then 1 else 0) + r.count y

/-- A caller of the recursion at `BitVec 8`. -/
def countPlus (y : BitVec 8) (t : Seq (BitVec 8)) : ℕ := t.count y + 1

reflect_d countPlus

example (y : BitVec 8) (t : Seq (BitVec 8)) :
    countPlus.d.den ((Env.nil.cons (τ := .word 8) y).cons (Seq.dEnc (.word 8) t)) =
      .ret (countPlus y t) :=
  countPlus.d_den y t

/-! ## Refusals -/

/-- A recursion over `List`, which is a type of its own in D. -/
def lenL : List ℕ → ℕ
  | [] => 0
  | _ :: xs => lenL xs + 1

/--
error: reflect_d: the structural recursion `CatCrypt.Complexity.D.ReflectIndTest.lenL` over `List
  ℕ`, which is not a represented inductive type (use List.foldl or Nat.iterate)
-/
#guard_msgs in
reflect_d lenL

/-- A type whose every constructor has a child. -/
inductive Loop where
  | step (x : Loop) (b : Bool)

/-- A function on it, by structural recursion. -/
def Loop.flag : Loop → Bool
  | .step x b => b && x.flag

/-- error: reflect_d: the inductive type `CatCrypt.Complexity.D.ReflectIndTest.Loop` has no constructor without a recursive argument; the first constructor of a signature of D has none -/
#guard_msgs in
reflect_d Loop.flag

/-- A nested inductive type. -/
inductive Rose where
  | node (x : BitVec 8) (kids : List Rose)

/-- Its root. -/
def Rose.root : Rose → BitVec 8
  | .node x _ => x

/--
error: reflect_d: the inductive type `Rose` is not represented in D (universe parameters, indices, a mutual or a nested inductive type)
-/
#guard_msgs in
reflect_d Rose.root

end CatCrypt.Complexity.D.ReflectIndTest
