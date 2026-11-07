/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.TranslateDt

/-!
# Indexed inductive families of D: tests

Binary trees of bytes of depth at most `d`, for `d : Fin 3`: the family `dtree d = imu (fin 2)
dSig d`, whose signature at every depth has a leaf with a byte and a node with a byte and two
children at the depth below (`predF d`, the depth `0` its own predecessor).

* `xorI`: the XOR of the bytes of a tree of depth at most `2`, by the eliminator at the constant
  motive `word 8`; its denotation and cost on a tree of two levels, and the bound by the charges
  of `Tm.dt` at every tree (`xorI_cost_le_dt`, the soundness theorem at `ifold`).
* `mixI`: the eliminator at the motive family `mot`, a Boolean at depth `0` (whether the byte is
  zero) and a byte above: the steps at each depth are a table over the depths, each step reading
  the recursive results at the type of the depth below; its denotation on a tree of three levels
  and the bound by the charges of `Tm.dt` (`mixI_cost_le_dt`).
* `nodeI`: a node built by `icon` from the table of its children, at no cost (`nodeI_cost`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D.IMuTest

open CatCrypt.Core Tm

/-- The depth below `d`, `0` below `0`. -/
def predF : Fin 3 → Fin 3
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 0
  | ⟨_ + 2, _⟩ => 1

/-- The signature at depth `d`: a leaf with a byte, and a node with a byte and its two children,
indexed by `Bool`, at the depth below. -/
def dSig (d : Fin 3) : ISig (.fin 2) :=
  .ext (.base (.word 8)) (.word 8) (some .bool) fun _ => predF d

/-- Binary trees of bytes of depth at most `d`. -/
abbrev dtree (d : Fin 3) : Ty := .imu (.fin 2) dSig d

/-- The leaf at depth `d` with the byte `x`. -/
def leafI (d : Fin 3) (x : BitVec 8) : Val (dtree d) :=
  Container.IPW.mk d ⟨.inl (), x⟩ fun p => Empty.elim p

/-- The node at depth `d` with the byte `x` and the children `l` (at `false`) and `r`. -/
def nodeIV (d : Fin 3) (x : BitVec 8) (l r : Val (dtree (predF d))) : Val (dtree d) :=
  Container.IPW.mk d ⟨.inr (), x⟩ fun b => bif b then r else l

/-- The XOR of the bytes of a tree, at the constant motive `word 8`: the same steps at every
depth. -/
def xorI : Tm [dtree 2] (.word 8) :=
  ifold (c := fun _ => .word 8)
    (ptab fun _ => pair (lam (var .here))
      (lam (prim (.wxor 8) (pair (fst (var .here))
        (prim (.wxor 8)
          (pair (app (papp (f := .bool) (snd (snd (var .here))) false) (lit .unit ()))
            (app (papp (f := .bool) (snd (snd (var .here))) true) (lit .unit ()))))))))
    (var .here)

/-- A tree of two levels at depth `2`: `5 (3, 6)`. -/
def t2 : Val (dtree 2) := nodeIV 2 5 (leafI 1 3) (leafI 1 6)

theorem xorI_den : xorI.den (Env.nil.cons t2) = .ret (5 ^^^ (3 ^^^ 6) : BitVec 8) := by
  rfl

/-- The cost on `t2`: a step at the root, a β-step per application of a recursive result (two)
and two XORs; the steps at the leaves return their byte at no cost. -/
theorem xorI_cost : xorI.cost (Env.nil.cons t2) = 5 := by
  decide +kernel

theorem xorI_inDtFrag : xorI.InDtFrag := by
  simp [xorI, InDtFrag, Tm.Pure, headVar?, Ty.isArr, Prim.unitCost]

/-- The soundness theorem at the eliminator of an indexed family: the cost of `xorI` is bounded
by its allowance and the charges of `Tm.dt` at every tree. -/
theorem xorI_cost_le_dt {η : EnvHat [dtree 2]} {ρ : Env [dtree 2]} (hρ : SimEnv η ρ) :
    xorI.cost ρ ≤ xorI.allow + SPTree.Timed.stepTime (xorI.dt η) :=
  cost_le_dt xorI xorI_inDtFrag hρ

/-- The motive family: a Boolean at depth `0`, a byte above. -/
def mot : Fin 3 → Ty
  | ⟨0, _⟩ => .bool
  | _ => .word 8

/-- The steps at each depth: at depth `0` whether the byte is zero; at depth `1` the byte when
both children are zero bytes at depth `0`, else `0`; at depth `2` the XOR of the byte and the
results of the children. -/
def mixSteps : (d : Fin 3) →
    Tm [dtree 2] ((dSig d).stepsTy (fun d' => .imu (.fin 2) dSig d') mot (mot d))
  | ⟨0, _⟩ =>
    pair (lam (prim (.weq 8) (pair (var .here) (lit (.word 8) (0 : BitVec 8)))))
      (lam (prim (.weq 8) (pair (fst (var .here)) (lit (.word 8) (0 : BitVec 8)))))
  | ⟨1, _⟩ =>
    pair (lam (var .here))
      (lam (ite (prim .band (pair
          (app (papp (f := .bool) (snd (snd (var .here))) false) (lit .unit ()))
          (app (papp (f := .bool) (snd (snd (var .here))) true) (lit .unit ()))))
        (fst (var .here)) (lit (.word 8) (0 : BitVec 8))))
  | ⟨_ + 2, _⟩ =>
    pair (lam (var .here))
      (lam (prim (.wxor 8) (pair (fst (var .here))
        (prim (.wxor 8)
          (pair (app (papp (f := .bool) (snd (snd (var .here))) false) (lit .unit ()))
            (app (papp (f := .bool) (snd (snd (var .here))) true) (lit .unit ())))))))

/-- The eliminator at the motive family `mot`, at depth `2`. -/
def mixI : Tm [dtree 2] (.word 8) :=
  ifold (f := .fin 2) (S := dSig) (c := mot) (i := (2 : Fin 3)) (ptab mixSteps) (var .here)

/-- A tree of three levels: `1 (2 (0, 0), 4 (0, 1))`. -/
def t3 : Val (dtree 2) :=
  nodeIV 2 1 (nodeIV 1 2 (leafI 0 0) (leafI 0 0)) (nodeIV 1 4 (leafI 0 0) (leafI 0 1))

/-- At depth `1` the left subtree has two zero leaves (its byte `2`), the right one does not
(`0`); the root XORs its byte with both. -/
theorem mixI_den : mixI.den (Env.nil.cons t3) = .ret (1 ^^^ (2 ^^^ 0) : BitVec 8) := by
  rfl

theorem mixI_inDtFrag : mixI.InDtFrag := by
  simp only [mixI, InDtFrag]
  refine ⟨fun d => ?_, rfl⟩
  rcases d with ⟨_ | _ | _ | n, hd⟩
  · simp [mixSteps, mot, InDtFrag, Tm.Pure, Ty.isArr, Prim.unitCost]
  · simp [mixSteps, mot, InDtFrag, Tm.Pure, headVar?, Ty.isArr, Prim.unitCost]
  · simp [mixSteps, mot, InDtFrag, Tm.Pure, headVar?, Ty.isArr, Prim.unitCost]
  · omega

/-- The soundness theorem at the eliminator into a motive family. -/
theorem mixI_cost_le_dt {η : EnvHat [dtree 2]} {ρ : Env [dtree 2]} (hρ : SimEnv η ρ) :
    mixI.cost ρ ≤ mixI.allow + SPTree.Timed.stepTime (mixI.dt η) :=
  cost_le_dt mixI mixI_inDtFrag hρ

/-- A node at depth `2` built by `icon` from the table of its two children, leaves at depth
`1`. -/
def nodeI : Tm [] (dtree 2) :=
  icon (f := .fin 2) (S := dSig) (i := (2 : Fin 3)) (inr (pair (lit (.word 8) (5 : BitVec 8))
    (ptab fun _ =>
      icon (f := .fin 2) (S := dSig) (i := (1 : Fin 3)) (inl (lit (.word 8) (3 : BitVec 8))))))

/-- The constructor and the table of leaves cost nothing. -/
theorem nodeI_cost : nodeI.cost Env.nil = 0 := by
  decide +kernel

end CatCrypt.Complexity.D.IMuTest
