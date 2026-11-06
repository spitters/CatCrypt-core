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
* `nodeT`: a node built by `con` from a function of its two children; the function is
  evaluated at both positions, a β-step and the conditional at each (`nodeT_cost`).
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

/-- A leaf built by `con`. -/
def leafT {Γ : List Ty} : Tm Γ tree := con treeSig_fo (inl (lit .unit ()))

/-- A node with the byte `5` and two leaves, its children given by a function of the
position. -/
def nodeT : Tm [] tree :=
  con treeSig_fo (inr (pair (lit (.word 8) (5 : BitVec 8)) (lam (ite (var .here) leafT leafT))))

/-- The children are tabulated at both positions: a β-step and the conditional at each. -/
theorem nodeT_cost : nodeT.cost Env.nil = 4 := by
  decide +kernel

end CatCrypt.Complexity.D.MuTest
