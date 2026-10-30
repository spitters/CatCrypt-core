/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Core.SPTree
public import Cslib.Foundations.Data.PFunctor.Free
public import PolyFun.PFunctor.Free.WP.Charge

/-!
# `SPTree` as a free monad over a polynomial functor

`SPTree α` is equivalent to `PFunctor.FreeM SPSig α`, the free monad over the polynomial functor
`SPSig` whose positions are the operations of `SPTree` and whose directions are their results.

## Main definitions

* `SPTree.SPOp` — the operations: `sample`, `sampleDist`, `get`, `set`, `fail`, `load`
* `SPTree.SPSig` — the polynomial functor `⟨SPOp, SPOp.dir⟩`
* `SPTree.toFreeM`, `SPTree.ofFreeM`, `SPTree.equivFreeM` — the equivalence
* `SPTree.spHandler` — each operation's computation in `SPComp`
* `SPTree.opCost` — the charge of an operation, the step of `queryCost`

## Main results

* `ofFreeM_toFreeM`, `toFreeM_ofFreeM` — the two round trips
* `compile_eq_liftM` — `compile` is `FreeM.liftM spHandler` after `toFreeM`
* `toFreeM_bind` — `toFreeM` carries `SPTree.bind` to `FreeM.bind`
* `queryCost_le_wpFold` — `queryCost` is at most the charge fold of `opCost` in `ℕ∞`
* `queryCost_eq_wpFold` — equality under `QueryBdd`

The charge fold is `wpFold (OpSpec.charge opCost)` over `ℕ∞`, PolyFun's worst-case charge
reading.
-/

@[expose] public section

namespace CatCrypt.Core

open CatCrypt.Prob PFunctor PFunctor.FreeM

namespace SPTree

variable {α β : Type}

/-! ## The signature -/

/-- The operations of `SPTree`, the positions of `SPSig`. -/
inductive SPOp : Type 1 where
  /-- Uniform sampling from a finite nonempty type. -/
  | sample (β : Type) (finβ : Fintype β) (neβ : Nonempty β)
  /-- Sampling from a sub-distribution. -/
  | sampleDist (β : Type) (μ : SDistr β)
  /-- Reading a location. -/
  | get (l : Location)
  /-- Writing a value to a location. -/
  | set (l : Location) (v : l.ty)
  /-- Failure. -/
  | fail
  /-- Replacing the heap. -/
  | load (h₀ : Heap)

/-- The result type of an operation, the directions of `SPSig`. -/
def SPOp.dir : SPOp → Type
  | .sample β _ _ => β
  | .sampleDist β _ => β
  | .get l => l.ty
  | .set _ _ => PUnit
  | .fail => PEmpty
  | .load _ => PUnit

/-- The polynomial functor of `SPTree` operations. -/
def SPSig : PFunctor.{1, 0} := ⟨SPOp, SPOp.dir⟩

/-! ## The equivalence -/

/-- The free-monad tree of an `SPTree`. -/
def toFreeM : SPTree α → FreeM SPSig α
  | .ret a => .pure a
  | .sample β finβ neβ k => .liftBind (SPOp.sample β finβ neβ) fun b => toFreeM (k b)
  | .sampleDist β μ k => .liftBind (SPOp.sampleDist β μ) fun b => toFreeM (k b)
  | .get l k => .liftBind (SPOp.get l) fun v => toFreeM (k v)
  | .set l v t => .liftBind (SPOp.set l v) fun _ => toFreeM t
  | .fail => .liftBind SPOp.fail PEmpty.elim
  | .load h₀ t => .liftBind (SPOp.load h₀) fun _ => toFreeM t

/-- The `SPTree` of a free-monad tree over `SPSig`. -/
def ofFreeM : FreeM SPSig α → SPTree α
  | .pure a => .ret a
  | .liftBind (.sample β finβ neβ) k => .sample β finβ neβ fun b => ofFreeM (k b)
  | .liftBind (.sampleDist β μ) k => .sampleDist β μ fun b => ofFreeM (k b)
  | .liftBind (.get l) k => .get l fun v => ofFreeM (k v)
  | .liftBind (.set l v) k => .set l v (ofFreeM (k PUnit.unit))
  | .liftBind .fail _ => .fail
  | .liftBind (.load h₀) k => .load h₀ (ofFreeM (k PUnit.unit))

/-- `ofFreeM` inverts `toFreeM`. -/
theorem ofFreeM_toFreeM (s : SPTree α) : ofFreeM (toFreeM s) = s := by
  induction s <;> simp only [toFreeM, ofFreeM, *]

/-- `toFreeM` inverts `ofFreeM`. -/
theorem toFreeM_ofFreeM : (x : FreeM SPSig α) → toFreeM (ofFreeM x) = x
  | .pure _ => rfl
  | .liftBind (.sample _ _ _) k => by
    simp only [ofFreeM, toFreeM]; congr 1; funext b; exact toFreeM_ofFreeM (k b)
  | .liftBind (.sampleDist _ _) k => by
    simp only [ofFreeM, toFreeM]; congr 1; funext b; exact toFreeM_ofFreeM (k b)
  | .liftBind (.get _) k => by
    simp only [ofFreeM, toFreeM]; congr 1; funext b; exact toFreeM_ofFreeM (k b)
  | .liftBind (.set _ _) k => by
    simp only [ofFreeM, toFreeM]; congr 1; funext b; exact toFreeM_ofFreeM (k b)
  | .liftBind .fail k => by
    simp only [ofFreeM, toFreeM]; congr 1; funext b; exact b.elim
  | .liftBind (.load _) k => by
    simp only [ofFreeM, toFreeM]; congr 1; funext b; exact toFreeM_ofFreeM (k b)

/-- `SPTree α` is equivalent to the free monad over `SPSig`. -/
def equivFreeM : SPTree α ≃ FreeM SPSig α where
  toFun := toFreeM
  invFun := ofFreeM
  left_inv := ofFreeM_toFreeM
  right_inv := toFreeM_ofFreeM

/-! ## Compilation as a handler -/

/-- The computation of each operation in `SPComp`; `load h₀` replaces the heap by `h₀`. -/
noncomputable def spHandler : (a : SPSig.A) → SPComp (SPSig.B a)
  | .sample β finβ neβ => letI := finβ; letI := neβ; SPComp.sample β
  | .sampleDist _ μ => liftSDistr μ
  | .get l => SPComp.get l
  | .set l v => SPComp.set l v
  | .fail => SPComp.fail
  | .load h₀ => fun _ => SDistr.pure (PUnit.unit, h₀)

/-- `compile` is the interpretation of the free-monad tree through `spHandler`. -/
theorem compile_eq_liftM (s : SPTree α) : (toFreeM s).liftM spHandler = s.compile := by
  induction s with
  | ret a => rfl
  | fail => simp only [toFreeM, FreeM.liftM, compile]; exact SPComp.fail_bind _
  | load h₀ t ih => simp only [toFreeM, FreeM.liftM, compile_load_eq_bind, ← ih]; rfl
  | _ => rename_i ih; simp only [toFreeM, FreeM.liftM, compile, ← ih]; rfl

/-! ## Bind -/

/-- `toFreeM` carries `SPTree.bind` to `FreeM.bind`. -/
theorem toFreeM_bind (s : SPTree α) (f : α → SPTree β) :
    toFreeM (s.bind f) = (toFreeM s).bind fun a => toFreeM (f a) := by
  induction s with
  | fail =>
    simp only [toFreeM, bind, FreeM.bind]; congr 1; funext b; exact b.elim
  | set l v t ih => simp only [toFreeM, bind, FreeM.bind, ih]
  | load h₀ t ih => simp only [toFreeM, bind, FreeM.bind, ih]
  | ret a => simp only [toFreeM, bind, FreeM.bind]
  | _ =>
    simp only [toFreeM, bind, FreeM.bind]
    congr 1; funext b; rename_i ih; exact ih b

/-! ## Query cost as a charge fold -/

/-- The charge of an operation: one per operation, `1 + |dom h₀|` for `load h₀`, and `0` for
`fail`. It is the step of `queryCost`. -/
def opCost : SPSig.A → ℕ
  | .fail => 0
  | .load h₀ => 1 + h₀.data.keys.card
  | _ => 1

/-- The cast of a supremum over a finite type is the supremum in `ℕ∞`. -/
theorem natCast_univ_sup {γ : Type} [Fintype γ] (f : γ → ℕ) :
    ((Finset.univ.sup f : ℕ) : ℕ∞) = ⨆ b, (f b : ℕ∞) := by
  rw [Finset.sup_univ_eq_ciSup, ENat.natCast_iSup (Set.finite_range f).bddAbove]

/-- `queryCost` is at most the charge fold of `opCost` in `ℕ∞`. -/
theorem queryCost_le_wpFold (s : SPTree α) :
    (s.queryCost : ℕ∞) ≤
      wpFold (OpSpec.charge fun a => (opCost a : ℕ∞)) (toFreeM s) (fun _ => 0) := by
  induction s with
  | ret a => simp [queryCost, toFreeM]
  | sample β finβ neβ k ih =>
    simp only [queryCost, toFreeM, wpFold, Nat.cast_add, Nat.cast_one, natCast_univ_sup]
    exact add_le_add (by simp [opCost]) (iSup_mono ih)
  | sampleDist β μ k ih =>
    simp only [queryCost, toFreeM, wpFold, Nat.cast_add, Nat.cast_one]
    refine add_le_add (by simp [opCost]) ?_
    by_cases hb : BddAbove (Set.range fun b => (k b).queryCost)
    · rw [ENat.natCast_iSup hb]; exact iSup_mono ih
    · rw [ciSup_of_not_bddAbove hb, csSup_empty]; simp
  | get l k ih =>
    simp only [queryCost, toFreeM, wpFold, Nat.cast_add, Nat.cast_one, natCast_univ_sup]
    exact add_le_add (by simp [opCost]) (iSup_mono ih)
  | set l v t ih =>
    have : Nonempty (SPSig.B (SPOp.set l v)) := ⟨PUnit.unit⟩
    simp only [queryCost, toFreeM, wpFold, Nat.cast_add, Nat.cast_one]
    unfold OpSpec.charge; rw [iSup_const]
    exact add_le_add (by simp [opCost]) ih
  | fail => simp [queryCost]
  | load h₀ t ih =>
    have : Nonempty (SPSig.B (SPOp.load h₀)) := ⟨PUnit.unit⟩
    simp only [queryCost, toFreeM, wpFold, Nat.cast_add, Nat.cast_one]
    unfold OpSpec.charge; rw [iSup_const]
    exact add_le_add (by simp [opCost]) ih

/-- Under `QueryBdd`, `queryCost` is the charge fold of `opCost` in `ℕ∞`. -/
theorem queryCost_eq_wpFold (s : SPTree α) (hs : s.QueryBdd) :
    (s.queryCost : ℕ∞) =
      wpFold (OpSpec.charge fun a => (opCost a : ℕ∞)) (toFreeM s) (fun _ => 0) := by
  induction s with
  | ret a => simp only [queryCost, toFreeM, wpFold, Nat.cast_zero]
  | sample β finβ neβ k ih =>
    simp only [QueryBdd] at hs
    simp only [queryCost, toFreeM, wpFold, Nat.cast_add, Nat.cast_one, natCast_univ_sup]
    exact congrArg₂ (· + ·) (by simp [opCost]) (iSup_congr fun b => ih b (hs b))
  | sampleDist β μ k ih =>
    simp only [QueryBdd] at hs
    simp only [queryCost, toFreeM, wpFold, Nat.cast_add, Nat.cast_one, ENat.natCast_iSup hs.1]
    exact congrArg₂ (· + ·) (by simp [opCost]) (iSup_congr fun b => ih b (hs.2 b))
  | get l k ih =>
    simp only [QueryBdd] at hs
    simp only [queryCost, toFreeM, wpFold, Nat.cast_add, Nat.cast_one, natCast_univ_sup]
    exact congrArg₂ (· + ·) (by simp [opCost]) (iSup_congr fun b => ih b (hs b))
  | set l v t ih =>
    simp only [QueryBdd] at hs
    have : Nonempty (SPSig.B (SPOp.set l v)) := ⟨PUnit.unit⟩
    simp only [queryCost, toFreeM, wpFold, Nat.cast_add, Nat.cast_one]
    unfold OpSpec.charge; rw [iSup_const]
    exact congrArg₂ (· + ·) (by simp [opCost]) (ih hs)
  | fail =>
    have : IsEmpty (SPSig.B SPOp.fail) := inferInstanceAs (IsEmpty PEmpty)
    simp only [queryCost, toFreeM, wpFold, Nat.cast_zero]
    unfold OpSpec.charge
    simp [opCost]
  | load h₀ t ih =>
    simp only [QueryBdd] at hs
    have : Nonempty (SPSig.B (SPOp.load h₀)) := ⟨PUnit.unit⟩
    simp only [queryCost, toFreeM, wpFold, Nat.cast_add, Nat.cast_one]
    unfold OpSpec.charge; rw [iSup_const]
    exact congrArg₂ (· + ·) (by simp [opCost]) (ih hs)

end SPTree

end CatCrypt.Core
