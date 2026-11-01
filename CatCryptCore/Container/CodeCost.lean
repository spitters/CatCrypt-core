/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.Code
public import CatCryptCore.Core.SPTreeFree
public import PolyFun.PFunctor.Free.WP.Charge
import CatCryptCore.Tactics.DeriveFreeSig

/-!
# Cost as an interpretation of codes

Besides the container interpretation `Code.interp c` and the relational lift `Code.Rel c R`, a
code `c` has a cost interpretation: a charge `χ : (Code.interp c).A → ℕ` of its operations gives
the cost fold `cost χ : FreeM (Code.interp c) α → ℕ∞`, the worst-case charge of a program tree:
a leaf costs `0`, a node at `a` costs `χ a` plus the supremum of the costs of its continuations.
It is PolyFun's charge fold `wpFold (OpSpec.charge χ) x (fun _ => 0)`, and its theorems hold for
every polynomial functor, so for every code.

The query cost of `SPTree` is an instance: it is the cost fold of `SPTree.opCost` at the code
of `SPTree`.

## Main definitions

* `Container.cost` — the cost fold of a charge;
* `Core.SPTreeCost.code`, `Core.SPTreeCost.codeCharge` — the code of `SPTree` and the charge
  `SPTree.opCost` on its positions.

## Main results

* `cost_pure`, `cost_liftBind` — the equations of the fold;
* `cost_bind_le_of_wpFold`, `cost_bind_le` — the cost of a bind is at most the cost of the
  program plus the supremum of the costs of the continuation at the returns satisfying an
  invariant of the program;
* `cost_mono` — monotonicity in the charge;
* `FreeRel.cost_eq` — invariance under the relational lift;
* `cost_mapLens_le`, `cost_mapLens_of_surjective`, `cost_freeMCongr_toLensEquiv` — the cost
  along a lens and along an equivalence of polynomial functors;
* `SPTreeCost.cost_equivCode`, `SPTreeCost.queryCost_le_cost`, `SPTreeCost.queryCost_eq_cost` —
  the query cost of `SPTree` as the cost fold at its code.

Search words: cost, charge, cost fold, worst-case cost, code, container, free monad, query cost.
-/

set_option autoImplicit false

@[expose] public section

universe u v u' v' w w'

namespace CatCrypt.Container

open PFunctor PFunctor.FreeM

variable {P : PFunctor.{u, v}} {Q : PFunctor.{u', v'}} {α : Type w} {β : Type w'}

/-! ## The cost fold -/

/-- The cost fold of the charge `χ`: the worst-case charge of a program tree, `0` at a leaf and
`χ a` plus the supremum over the directions of the continuations at a node at `a`. -/
noncomputable def cost (χ : P.A → ℕ) (x : P.FreeM α) : ℕ∞ :=
  wpFold (OpSpec.charge fun a => (χ a : ℕ∞)) x fun _ => 0

/-- A leaf costs nothing. -/
@[simp] theorem cost_pure (χ : P.A → ℕ) (a : α) : cost χ (FreeM.pure a : P.FreeM α) = 0 := rfl

/-- A node costs its charge plus the supremum of the costs of its continuations. -/
theorem cost_liftBind (χ : P.A → ℕ) (a : P.A) (k : P.B a → P.FreeM α) :
    cost χ (FreeM.liftBind a k) = χ a + ⨆ d, cost χ (k d) := rfl

/-- Every return of a program satisfies the trivial invariant. -/
theorem wpFold_demonic_true (x : P.FreeM α) : wpFold (OpSpec.demonic P) x fun _ => True := by
  induction x with
  | pure a => trivial
  | lift_bind a k ih => exact fun d => ih d

/-- **Cost of a bind.** When every return of `x` satisfies `I`, the cost of `x >>= f` is at most
the cost of `x` plus the supremum of the costs of `f a` over the returns `a` satisfying `I`. -/
theorem cost_bind_le_of_wpFold (χ : P.A → ℕ) {x : P.FreeM α} {f : α → P.FreeM β}
    {I : α → Prop} (hI : wpFold (OpSpec.demonic P) x I) :
    cost χ (x.bind f) ≤ cost χ x + ⨆ (a : α) (_ : I a), cost χ (f a) := by
  induction x with
  | pure a =>
    change cost χ (f a) ≤ 0 + _
    rw [zero_add]
    exact le_iSup₂ (f := fun a (_ : I a) => cost χ (f a)) a hI
  | lift_bind a k ih =>
    change (χ a : ℕ∞) + ⨆ d, cost χ ((k d).bind f) ≤ ((χ a : ℕ∞) + ⨆ d, cost χ (k d)) + _
    rw [add_assoc]
    refine add_le_add le_rfl (iSup_le fun d => (ih d (hI d)).trans ?_)
    exact add_le_add (le_iSup (fun d => cost χ (k d)) d) le_rfl

/-- The cost of a bind is at most the cost of the program plus the supremum of the costs of the
continuation. -/
theorem cost_bind_le (χ : P.A → ℕ) (x : P.FreeM α) (f : α → P.FreeM β) :
    cost χ (x.bind f) ≤ cost χ x + ⨆ a, cost χ (f a) := by
  refine (cost_bind_le_of_wpFold χ (wpFold_demonic_true x)).trans ?_
  exact add_le_add le_rfl (iSup_mono fun a => iSup_le fun _ => le_rfl)

/-- The cost fold is monotone in the charge. -/
theorem cost_mono {χ χ' : P.A → ℕ} (h : ∀ a, χ a ≤ χ' a) (x : P.FreeM α) :
    cost χ x ≤ cost χ' x := by
  induction x with
  | pure a => exact le_rfl
  | lift_bind a k ih =>
    change (χ a : ℕ∞) + ⨆ d, cost χ (k d) ≤ (χ' a : ℕ∞) + ⨆ d, cost χ' (k d)
    exact add_le_add (by exact_mod_cast h a) (iSup_mono ih)

/-- **Invariance under the relational lift.** Programs related by the lift of any relation have
the same cost. -/
theorem FreeRel.cost_eq {R : α → β → Prop} (χ : P.A → ℕ) {x : P.FreeM α} {y : P.FreeM β}
    (h : FreeRel P R x y) : cost χ x = cost χ y := by
  induction h with
  | pure _ => rfl
  | liftBind a _ ih => rw [cost_liftBind, cost_liftBind, iSup_congr ih]

/-! ## Cost along lenses -/

/-- The cost of a program mapped along a lens is at most the cost of the program at the charge
pulled back along the lens. -/
theorem cost_mapLens_le (l : Lens P Q) (χ : Q.A → ℕ) (x : P.FreeM α) :
    cost χ (x.mapLens l) ≤ cost (χ ∘ l.toFunA) x := by
  induction x with
  | pure a => exact le_rfl
  | lift_bind a k ih =>
    change (χ (l.toFunA a) : ℕ∞) + ⨆ d, cost χ ((k (l.toFunB a d)).mapLens l) ≤
      ((χ ∘ l.toFunA) a : ℕ∞) + ⨆ b, cost (χ ∘ l.toFunA) (k b)
    exact add_le_add le_rfl
      (iSup_le fun d => (ih _).trans (le_iSup (fun b => cost (χ ∘ l.toFunA) (k b)) _))

/-- Along a lens whose maps of directions are surjective, the cost of a mapped program is the
cost of the program at the charge pulled back along the lens. -/
theorem cost_mapLens_of_surjective (l : Lens P Q) (hl : ∀ a, Function.Surjective (l.toFunB a))
    (χ : Q.A → ℕ) (x : P.FreeM α) : cost χ (x.mapLens l) = cost (χ ∘ l.toFunA) x := by
  induction x with
  | pure a => rfl
  | lift_bind a k ih =>
    change (χ (l.toFunA a) : ℕ∞) + ⨆ d, cost χ ((k (l.toFunB a d)).mapLens l) =
      ((χ ∘ l.toFunA) a : ℕ∞) + ⨆ b, cost (χ ∘ l.toFunA) (k b)
    simp only [ih]
    rw [(hl a).iSup_comp (fun b => cost (χ ∘ l.toFunA) (k b))]
    rfl

/-- Along a lens whose maps of directions are surjective, the invariant on returns of a mapped
program is the invariant on returns of the program. -/
theorem wpFold_demonic_mapLens_iff (l : Lens P Q) (hl : ∀ a, Function.Surjective (l.toFunB a))
    (x : P.FreeM α) (I : α → Prop) :
    wpFold (OpSpec.demonic Q) (x.mapLens l) I ↔ wpFold (OpSpec.demonic P) x I := by
  induction x with
  | pure a => exact Iff.rfl
  | lift_bind a k ih =>
    change (∀ d, wpFold (OpSpec.demonic Q) ((k (l.toFunB a d)).mapLens l) I) ↔
      ∀ b, wpFold (OpSpec.demonic P) (k b) I
    simp only [ih]
    exact ((hl a).forall (p := fun b => wpFold (OpSpec.demonic P) (k b) I)).symm

/-- The cost along an equivalence of polynomial functors is the cost at the charge pulled back
along the equivalence of positions. -/
theorem cost_freeMCongr_toLensEquiv (e : P ≃ₚ Q) (χ : Q.A → ℕ) (x : P.FreeM α) :
    cost χ (freeMCongr (PFunctor.Equiv.toLensEquiv e) x) = cost (χ ∘ e.equivA) x :=
  cost_mapLens_of_surjective _ (fun a => (e.equivB a).symm.surjective) χ x

/-- The invariant on returns along an equivalence of polynomial functors. -/
theorem wpFold_demonic_freeMCongr_toLensEquiv_iff (e : P ≃ₚ Q) (x : P.FreeM α)
    (I : α → Prop) :
    wpFold (OpSpec.demonic Q) (freeMCongr (PFunctor.Equiv.toLensEquiv e) x) I ↔
      wpFold (OpSpec.demonic P) x I :=
  wpFold_demonic_mapLens_iff _ (fun a => (e.equivB a).symm.surjective) x I

/-- A bound `c + X ≤ t` with `c t : ℕ` splits into `c ≤ t` and `X ≤ t - c`. -/
theorem natCast_add_le_natCast_iff (c t : ℕ) (X : ℕ∞) :
    (c : ℕ∞) + X ≤ t ↔ c ≤ t ∧ X ≤ ((t - c : ℕ) : ℕ∞) := by
  constructor
  · intro h
    have hc : c ≤ t := by
      have : (c : ℕ∞) ≤ t := le_trans le_self_add h
      exact_mod_cast this
    refine ⟨hc, (ENat.add_le_add_iff_left (ENat.natCast_ne_top c)).1 ?_⟩
    rw [← Nat.cast_add, Nat.add_sub_cancel' hc]
    exact h
  · rintro ⟨hc, hX⟩
    calc (c : ℕ∞) + X ≤ (c : ℕ∞) + ((t - c : ℕ) : ℕ∞) := add_le_add le_rfl hX
      _ = t := by rw [← Nat.cast_add, Nat.add_sub_cancel' hc]

end CatCrypt.Container

/-! ## The query cost of `SPTree` -/

namespace CatCrypt.Core

open PFunctor PFunctor.FreeM CatCrypt.Container

derive_free_sig SPTree (namespace := SPTreeCost) (code := true)

namespace SPTreeCost

variable {α : Type}

/-- The operation of `SPTree.Sig` of an operation of the generated signature. -/
def Op.toSPTreeOp : SPTreeCost.Op → SPTree.Op
  | .sample β finβ neβ => .sample β finβ neβ
  | .sampleDist β μ => .sampleDist β μ
  | .get l => .get l
  | .set l v => .set l v
  | .fail => .fail
  | .load h₀ => .load h₀

/-- The charge `SPTree.opCost` on the positions of the code of `SPTree`. -/
def codeCharge (a : (Code.interp SPTreeCost.code).A) : ℕ :=
  SPTree.opCost (SPTreeCost.sigEquivCode.equivA.symm a).toSPTreeOp

/-- The cost fold over the generated signature is the charge fold of `SPTree.opCost`. -/
theorem cost_toFreeM (s : SPTree α) :
    cost (fun o : SPTreeCost.Op => SPTree.opCost o.toSPTreeOp) (SPTreeCost.toFreeM s) =
      cost SPTree.opCost (SPTree.toFreeM s) := by
  induction s with
  | ret a => rfl
  | fail => exact congrArg₂ (· + ·) rfl (iSup_congr fun d => d.elim)
  | sample β finβ neβ k ih => exact congrArg₂ (· + ·) rfl (iSup_congr ih)
  | sampleDist β μ k ih => exact congrArg₂ (· + ·) rfl (iSup_congr ih)
  | get l k ih => exact congrArg₂ (· + ·) rfl (iSup_congr ih)
  | set l v t ih => exact congrArg₂ (· + ·) rfl (iSup_congr fun _ => ih)
  | load h₀ t ih => exact congrArg₂ (· + ·) rfl (iSup_congr fun _ => ih)

/-- The cost fold of `codeCharge` at the code of `SPTree` is the charge fold of
`SPTree.opCost`. -/
theorem cost_equivCode (s : SPTree α) :
    cost codeCharge (SPTreeCost.equivCode s) = cost SPTree.opCost (SPTree.toFreeM s) := by
  have hχ : codeCharge ∘ SPTreeCost.sigEquivCode.equivA = fun o => SPTree.opCost o.toSPTreeOp :=
    funext fun o => by simp [codeCharge]
  rw [SPTreeCost.equivCode, Equiv.trans_apply, cost_freeMCongr_toLensEquiv, hχ]
  exact cost_toFreeM s

/-- `queryCost` is at most the cost fold of `codeCharge` at the code of `SPTree`. -/
theorem queryCost_le_cost (s : SPTree α) :
    (s.queryCost : ℕ∞) ≤ cost codeCharge (SPTreeCost.equivCode s) := by
  rw [cost_equivCode]
  exact SPTree.queryCost_le_wpFold s

/-- Under `QueryBdd`, `queryCost` is the cost fold of `codeCharge` at the code of `SPTree`. -/
theorem queryCost_eq_cost (s : SPTree α) (hs : s.QueryBdd) :
    (s.queryCost : ℕ∞) = cost codeCharge (SPTreeCost.equivCode s) := by
  rw [cost_equivCode]
  exact SPTree.queryCost_eq_wpFold s hs

end SPTreeCost

end CatCrypt.Core
