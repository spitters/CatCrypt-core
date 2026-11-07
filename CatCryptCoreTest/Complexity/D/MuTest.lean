/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.TranslateDt

/-!
# Inductive types of D: tests

Binary trees of bytes, `tree = mu treeSig` with a leaf and a node holding a byte and two
children indexed by `Bool`.

* `xorT`: the XOR of the bytes of a tree by the eliminator; its denotation on a tree of two
  nodes (`xorT_den`), its cost (`xorT_cost`: a step per node visited, the β-step of each call of
  a recursive result and one per XOR), and the bound by the charges of `Tm.dt` from the
  soundness theorem at every tree (`xorT_cost_le_dt`).
* `xorT_den_all`: the denotation of `xorT` at every tree is the recursion `xorF`, by the rule of
  the eliminator (`Reflect.Den.fold`); `isLeafT_dsim`: a case analysis by the eliminator costs one
  step, by the linking rule of the eliminator (`TimedLink.DSim.fold`).
* `nodeT`: a node built by `con` from the table of its two children (`ptab`); the constructor
  and the table of leaves cost nothing (`nodeT_cost`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D.MuTest

open CatCrypt.Core Tm

/-- The signature of binary trees of bytes: a leaf, and a node with a byte and its children
indexed by `Bool`. -/
def treeSig : Sig := .ext (.base .unit) (.word 8) (some .bool)

/-- Binary trees of bytes. -/
abbrev tree : Ty := .mu treeSig

theorem treeSig_fo : treeSig.FO := ⟨trivial, trivial⟩

/-- The leaf. -/
def leafV : Val tree := WType.mk (.inl ()) fun p => Empty.elim p

/-- The node with the byte `n` and the children `l` (at `false`) and `r` (at `true`). -/
def nodeV (n : BitVec 8) (l r : Val tree) : Val tree :=
  WType.mk (.inr n) fun b => bif b then r else l

/-- The XOR of the bytes of a tree: `0` at the leaf, the byte XOR the results of the children
at a node. -/
def xorT : Tm [tree] (.word 8) :=
  fold treeSig_fo
    (pair (lam (lit (.word 8) (0 : BitVec 8)))
      (lam (prim (.wxor 8) (pair (fst (var .here))
        (prim (.wxor 8) (pair (app (snd (snd (var .here))) (lit .bool false))
          (app (snd (snd (var .here))) (lit .bool true))))))))
    (var .here)

/-- The tree of two nodes `5 (3 leaf leaf) leaf`. -/
def t2 : Val tree := nodeV 5 (nodeV 3 leafV leafV) leafV

theorem xorT_den : xorT.den (Env.nil.cons t2) = .ret (5 ^^^ 3 : BitVec 8) := by
  rfl

/-- The cost on `t2`: a step at the root, a β-step per call of a recursive result (four, two at
each node), and two XORs per node. -/
theorem xorT_cost : xorT.cost (Env.nil.cons t2) = 9 := by
  decide +kernel

theorem xorT_inDtFrag : xorT.InDtFrag := by
  simp [xorT, InDtFrag, Tm.Pure, headVar?, Ty.isArr, Prim.unitCost]

/-- The cost of `xorT` is bounded by its allowance and the charges of `Tm.dt` at every tree. -/
theorem xorT_cost_le_dt {η : EnvHat [tree]} {ρ : Env [tree]} (hρ : SimEnv η ρ) :
    xorT.cost ρ ≤ xorT.allow + SPTree.Timed.stepTime (xorT.dt η) :=
  cost_le_dt xorT xorT_inDtFrag hρ

/-- The XOR of the bytes of a tree, by recursion on the value. -/
def xorF : WType (Sig.den treeSig).2 → BitVec 8
  | ⟨.inl _, _⟩ => 0
  | ⟨.inr n, kids⟩ =>
    let m : BitVec 8 := n
    m ^^^ (xorF (kids false) ^^^ xorF (kids true))

/-- The denotation of `xorT` at every tree, by the rule of the eliminator: its step functions
denote `xorF` at every node whose recursive results are the values of `xorF` at its children. -/
theorem xorT_den_all (w : Val tree) : Reflect.Den xorT (Env.nil.cons w) (xorF w) := by
  unfold xorT
  exact Reflect.Den.fold treeSig_fo (Reflect.Den.pair (Reflect.Den.lam _ _) (Reflect.Den.lam _ _))
    (Reflect.Den.var .here _) fun a kids => by rcases a with _ | n <;> rfl

/-- Whether a tree is a leaf: a case analysis, the eliminator whose steps apply no recursive
result. -/
def isLeafT : Tm [tree] .bool :=
  fold treeSig_fo (pair (lam (lit .bool true)) (lam (lit .bool false))) (var .here)

/-- Whether a value is a leaf. -/
def isLeafF : WType (Sig.den treeSig).2 → Bool
  | ⟨.inl _, _⟩ => true
  | ⟨.inr _, _⟩ => false

/-- The case analysis costs one step plus its branch, here nothing: by the rule of the
eliminator at the cost `0` of every node. -/
theorem isLeafT_dsim (w : Val tree) :
    TimedLink.DSim 1 0 (1 + 0 + 0) isLeafT (Env.nil.cons w) (isLeafF w) := by
  unfold isLeafT
  exact TimedLink.DSim.fold (C := fun _ => 0) le_rfl treeSig_fo
    (gv := (((fun _ => .ret true) : Val (.arr .unit .bool)),
      ((fun _ => .ret false) : Val (.arr (Sig.altTy (.word 8) (some .bool) tree .bool) .bool))))
    (by rfl)
    (TimedLink.DSim.var .here) fun a _ _ _ => ⟨0, by rcases a with _ | n <;> rfl, le_rfl⟩

/-- A leaf built by `con`. -/
def leafT {Γ : List Ty} : Tm Γ tree := con treeSig_fo (inl (lit .unit ()))

/-- A node with the byte `5` and two leaves, its children a table over the positions. -/
def nodeT : Tm [] tree :=
  con treeSig_fo (inr (pair (lit (.word 8) (5 : BitVec 8)) (ptab fun _ => leafT)))

/-- A constructor is free, and so is the table of its children, whose components are leaves. -/
theorem nodeT_cost : nodeT.cost Env.nil = 0 := by
  decide +kernel

end CatCrypt.Complexity.D.MuTest
