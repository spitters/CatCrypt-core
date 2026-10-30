/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Core.SPTreeFree
public import CatCryptCore.Core.SPTreeTimed
public import PolyFun.PFunctor.Handler.Sum
public import PolyFun.PFunctor.Handler.Free
import all CatCryptCore.Core.SPTreeTimed
import all CatCryptCore.Unary.ExpectedCost

/-!
# Costed `SPTree`s as free monads with a tick operation

`SPTree.Timed α` translates to the free monad `PFunctor.FreeM SPSigT α` of the polynomial
functor `SPSigT = SPSig + TickSig`, whose extra positions `tick n` charge `n` units and have one
direction. The translation `SPTree.Timed.toFreeMT` follows each direction `x` of a node with step
cost `c` by the tick `c x`.

## Main definitions

* `SPTree.TickSig`, `SPTree.SPSigT` — the tick polynomial and the ticked signature
* `SPTree.tickCost` — `opCost` at an operation of `SPSig`, `n` at `tick n`
* `SPTree.Timed.toFreeMT` — the tick tree of a costed tree
* `SPTree.eraseHandler` — the handler into `FreeM SPSig` that keeps operations and drops ticks
* `SPTree.costHandler` — the handler into `CostComp` that charges `opCost` per operation and
  `n` per tick

## Main results

* `SPTree.Timed.liftM_eraseHandler_toFreeMT`, `SPTree.Timed.erase_eq_liftM` — `erase` is
  interpretation by `eraseHandler`, transported along `SPTree.equivFreeM`
* `SPTree.Timed.time_le_wpFold` — `time` is at most the charge fold of `tickCost` in `ℕ∞`
* `SPTree.Timed.time_eq_wpFold` — equality under `TimeBdd`
* `SPTree.Timed.timeBound_of_isRollBound`, `SPTree.Timed.timeBound_of_wpFold_le` — the
  subtractive roll bound, equivalently the charge-fold bound, implies `TimeBound`, with no
  boundedness hypothesis
* `SPTree.Timed.liftM_costHandler_toFreeMT` — `compileTimed` is interpretation by `costHandler`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Core

open CatCrypt.Prob CatCrypt.Unary PFunctor PFunctor.FreeM

namespace SPTree

/-! ## The ticked signature -/

/-- The tick polynomial: a position `n : ℕ` charges `n` units and has one direction. -/
abbrev TickSig : PFunctor.{0, 0} := ⟨ℕ, fun _ => PUnit⟩

/-- The polynomial functor of costed `SPTree`s: `SPSig` with tick positions. -/
abbrev SPSigT : PFunctor.{1, 0} := SPSig + TickSig

/-- The charge of a position of `SPSigT`: `opCost a` at an operation `a`, `n` at `tick n`. -/
def tickCost : SPSigT.A → ℕ
  | .inl a => opCost a
  | .inr n => n

/-- The handler into `FreeM SPSig` that keeps each operation and answers each tick with `()`. -/
def eraseHandler : Handler (FreeM SPSig) SPSigT :=
  Handler.sum (Handler.id SPSig) fun _ => FreeM.pure PUnit.unit

/-- The `Pure` structure of `CostComp`: return at zero cost. -/
@[instance_reducible] noncomputable def costPure : Pure CostComp := ⟨CostComp.pure⟩

/-- The `Bind` structure of `CostComp`: sequential composition, adding the credits. -/
@[instance_reducible] noncomputable def costBind : Bind CostComp := ⟨CostComp.bind⟩

attribute [local instance] costPure costBind

/-- The handler into `CostComp`: an operation `a` runs `spHandler a` at price `opCost a`, and
`tick n` charges `n`. -/
noncomputable def costHandler : Handler CostComp SPSigT :=
  Handler.sum (fun a => CostComp.lift (spHandler a) (opCost a))
    fun n => CostComp.lift (SPComp.pure ()) n

namespace Timed

variable {α : Type}

/-! ## The tick tree -/

/-- The costed tree `s` as a tree of `SPSigT`: each direction `x` of a node with step cost `c`
is followed by the tick `c x`. -/
def toFreeMT : SPTree.Timed α → FreeM SPSigT α
  | ret a => .pure a
  | sample β finβ neβ c k => .liftBind (P := SPSigT) (.inl (.sample β finβ neβ)) fun b =>
      .liftBind (P := SPSigT) (.inr (c b)) fun _ => toFreeMT (k b)
  | sampleDist β μ c k => .liftBind (P := SPSigT) (.inl (.sampleDist β μ)) fun b =>
      .liftBind (P := SPSigT) (.inr (c b)) fun _ => toFreeMT (k b)
  | get l c k => .liftBind (P := SPSigT) (.inl (.get l)) fun v =>
      .liftBind (P := SPSigT) (.inr (c v)) fun _ => toFreeMT (k v)
  | set l v c t => .liftBind (P := SPSigT) (.inl (.set l v)) fun _ =>
      .liftBind (P := SPSigT) (.inr c) fun _ => toFreeMT t
  | fail => .liftBind (P := SPSigT) (.inl .fail) PEmpty.elim
  | load h₀ c t => .liftBind (P := SPSigT) (.inl (.load h₀)) fun _ =>
      .liftBind (P := SPSigT) (.inr c) fun _ => toFreeMT t

/-! ## Erasure as a handler -/

/-- Interpreting the tick tree by `eraseHandler` gives the tree of the erased costed tree. -/
theorem liftM_eraseHandler_toFreeMT (s : SPTree.Timed α) :
    (toFreeMT s).liftM eraseHandler = SPTree.toFreeM s.erase := by
  induction s with
  | ret a => rfl
  | fail =>
    change FreeM.bind (FreeM.lift (P := SPSig) SPOp.fail) _ = _
    simp only [FreeM.lift, FreeM.bind, erase, SPTree.toFreeM]
    congr 1; funext b; exact b.elim
  | set l v c t ih => exact congrArg (FreeM.liftBind _) (funext fun _ => ih)
  | load h₀ c t ih => exact congrArg (FreeM.liftBind _) (funext fun _ => ih)
  | _ => rename_i ih; exact congrArg (FreeM.liftBind _) (funext ih)

/-- `erase` is interpretation by `eraseHandler`, transported along `SPTree.equivFreeM`. -/
theorem erase_eq_liftM (s : SPTree.Timed α) :
    s.erase = SPTree.equivFreeM.symm ((toFreeMT s).liftM eraseHandler) := by
  rw [liftM_eraseHandler_toFreeMT]
  exact (SPTree.equivFreeM.symm_apply_apply _).symm

/-! ## Time as a charge fold -/

/-- `time` is at most the charge fold of `tickCost` in `ℕ∞`. -/
theorem time_le_wpFold (s : SPTree.Timed α) :
    (s.time : ℕ∞) ≤
      wpFold (OpSpec.charge fun a => (tickCost a : ℕ∞)) (toFreeMT s) (fun _ => 0) := by
  induction s with
  | ret a => simp [time, toFreeMT]
  | sample β finβ neβ c k ih =>
    have : ∀ n, Nonempty (SPSigT.B (.inr n)) := fun _ => ⟨PUnit.unit⟩
    simp only [time, toFreeMT, wpFold_liftBind, OpSpec.charge_apply, iSup_const, tickCost,
      opCost, Nat.cast_add, Nat.cast_one, natCast_univ_sup]
    exact add_le_add le_rfl (iSup_mono fun b => add_le_add le_rfl (ih b))
  | sampleDist β μ c k ih =>
    have : ∀ n, Nonempty (SPSigT.B (.inr n)) := fun _ => ⟨PUnit.unit⟩
    simp only [time, toFreeMT, wpFold_liftBind, OpSpec.charge_apply, iSup_const, tickCost,
      opCost, Nat.cast_add, Nat.cast_one]
    refine add_le_add le_rfl ?_
    by_cases hb : BddAbove (Set.range fun b => c b + (k b).time)
    · rw [ENat.natCast_iSup hb]
      exact iSup_mono fun b => by rw [Nat.cast_add]; exact add_le_add le_rfl (ih b)
    · rw [ciSup_of_not_bddAbove hb, csSup_empty]; simp
  | get l c k ih =>
    have : ∀ n, Nonempty (SPSigT.B (.inr n)) := fun _ => ⟨PUnit.unit⟩
    simp only [time, toFreeMT, wpFold_liftBind, OpSpec.charge_apply, iSup_const, tickCost,
      opCost, Nat.cast_add, Nat.cast_one, natCast_univ_sup]
    exact add_le_add le_rfl (iSup_mono fun b => add_le_add le_rfl (ih b))
  | set l v c t ih =>
    have : ∀ n, Nonempty (SPSigT.B (.inr n)) := fun _ => ⟨PUnit.unit⟩
    have : Nonempty (SPSigT.B (.inl (.set l v))) := ⟨PUnit.unit⟩
    simp only [time, toFreeMT, wpFold_liftBind, OpSpec.charge_apply, iSup_const, tickCost,
      opCost, Nat.cast_add, Nat.cast_one]
    exact add_le_add le_rfl (add_le_add le_rfl ih)
  | fail => simp [time]
  | load h₀ c t ih =>
    have : ∀ n, Nonempty (SPSigT.B (.inr n)) := fun _ => ⟨PUnit.unit⟩
    have : Nonempty (SPSigT.B (.inl (.load h₀))) := ⟨PUnit.unit⟩
    simp only [time, toFreeMT, wpFold_liftBind, OpSpec.charge_apply, iSup_const, tickCost,
      opCost, Nat.cast_add, Nat.cast_one]
    exact add_le_add le_rfl (add_le_add le_rfl ih)

/-- Under `TimeBdd`, `time` is the charge fold of `tickCost` in `ℕ∞`. -/
theorem time_eq_wpFold (s : SPTree.Timed α) (hs : s.TimeBdd) :
    (s.time : ℕ∞) =
      wpFold (OpSpec.charge fun a => (tickCost a : ℕ∞)) (toFreeMT s) (fun _ => 0) := by
  induction s with
  | ret a => simp [time, toFreeMT]
  | sample β finβ neβ c k ih =>
    have : ∀ n, Nonempty (SPSigT.B (.inr n)) := fun _ => ⟨PUnit.unit⟩
    simp only [TimeBdd] at hs
    simp only [time, toFreeMT, wpFold_liftBind, OpSpec.charge_apply, iSup_const, tickCost,
      opCost, Nat.cast_add, Nat.cast_one, natCast_univ_sup]
    exact congrArg₂ (· + ·) rfl (iSup_congr fun b => congrArg₂ (· + ·) rfl (ih b (hs b)))
  | sampleDist β μ c k ih =>
    have : ∀ n, Nonempty (SPSigT.B (.inr n)) := fun _ => ⟨PUnit.unit⟩
    simp only [TimeBdd] at hs
    simp only [time, toFreeMT, wpFold_liftBind, OpSpec.charge_apply, iSup_const, tickCost,
      opCost, Nat.cast_add, Nat.cast_one, ENat.natCast_iSup hs.1]
    exact congrArg₂ (· + ·) rfl (iSup_congr fun b => congrArg₂ (· + ·) rfl (ih b (hs.2 b)))
  | get l c k ih =>
    have : ∀ n, Nonempty (SPSigT.B (.inr n)) := fun _ => ⟨PUnit.unit⟩
    simp only [TimeBdd] at hs
    simp only [time, toFreeMT, wpFold_liftBind, OpSpec.charge_apply, iSup_const, tickCost,
      opCost, Nat.cast_add, Nat.cast_one, natCast_univ_sup]
    exact congrArg₂ (· + ·) rfl (iSup_congr fun b => congrArg₂ (· + ·) rfl (ih b (hs b)))
  | set l v c t ih =>
    have : ∀ n, Nonempty (SPSigT.B (.inr n)) := fun _ => ⟨PUnit.unit⟩
    have : Nonempty (SPSigT.B (.inl (.set l v))) := ⟨PUnit.unit⟩
    simp only [TimeBdd] at hs
    simp only [time, toFreeMT, wpFold_liftBind, OpSpec.charge_apply, iSup_const, tickCost,
      opCost, Nat.cast_add, Nat.cast_one, ih hs]
  | fail =>
    have : IsEmpty (SPSigT.B (.inl SPOp.fail)) := inferInstanceAs (IsEmpty PEmpty)
    simp only [time, toFreeMT, wpFold, Nat.cast_zero]
    unfold OpSpec.charge
    simp only [tickCost, opCost, iSup_of_empty, Nat.cast_zero, bot_eq_zero, add_zero]
  | load h₀ c t ih =>
    have : ∀ n, Nonempty (SPSigT.B (.inr n)) := fun _ => ⟨PUnit.unit⟩
    have : Nonempty (SPSigT.B (.inl (.load h₀))) := ⟨PUnit.unit⟩
    simp only [TimeBdd] at hs
    simp only [time, toFreeMT, wpFold_liftBind, OpSpec.charge_apply, iSup_const, tickCost,
      opCost, Nat.cast_add, Nat.cast_one, ih hs]

/-! ## Roll bounds give time bounds -/

/-- The subtractive roll bound with charge `tickCost` on the tick tree is a time bound. -/
theorem timeBound_of_isRollBound (s : SPTree.Timed α) (t : ℕ)
    (h : (toFreeMT s).IsRollBound t (fun a b => tickCost a ≤ b) (fun a b => b - tickCost a)) :
    s.TimeBound t := by
  induction s generalizing t with
  | ret a => trivial
  | fail => trivial
  | sample β finβ neβ c k ih =>
    simp only [toFreeMT, FreeM.isRollBound_liftBind_iff, tickCost, opCost] at h
    refine ⟨h.1, fun b => ⟨by have := (h.2 b).1; have := h.1; omega, ?_⟩⟩
    have hk := (h.2 b).2 PUnit.unit
    rw [Nat.sub_sub] at hk
    exact ih b _ hk
  | sampleDist β μ c k ih =>
    simp only [toFreeMT, FreeM.isRollBound_liftBind_iff, tickCost, opCost] at h
    refine ⟨h.1, fun b _ => ⟨by have := (h.2 b).1; have := h.1; omega, ?_⟩⟩
    have hk := (h.2 b).2 PUnit.unit
    rw [Nat.sub_sub] at hk
    exact ih b _ hk
  | get l c k ih =>
    simp only [toFreeMT, FreeM.isRollBound_liftBind_iff, tickCost, opCost] at h
    refine ⟨h.1, fun b => ⟨by have := (h.2 b).1; have := h.1; omega, ?_⟩⟩
    have hk := (h.2 b).2 PUnit.unit
    rw [Nat.sub_sub] at hk
    exact ih b _ hk
  | set l v c t' ih =>
    simp only [toFreeMT, FreeM.isRollBound_liftBind_iff, tickCost, opCost] at h
    refine ⟨by have := (h.2 PUnit.unit).1; have := h.1; omega, ?_⟩
    have hk := (h.2 PUnit.unit).2 PUnit.unit
    rw [Nat.sub_sub] at hk
    exact ih _ hk
  | load h₀ c t' ih =>
    simp only [toFreeMT, FreeM.isRollBound_liftBind_iff, tickCost, opCost] at h
    refine ⟨by have := (h.2 PUnit.unit).1; have := h.1; omega, ?_⟩
    have hk := (h.2 PUnit.unit).2 PUnit.unit
    rw [Nat.sub_sub] at hk
    exact ih _ hk

/-- A bound `t` on the charge fold of the tick tree is a time bound. -/
theorem timeBound_of_wpFold_le (s : SPTree.Timed α) (t : ℕ)
    (h : wpFold (OpSpec.charge fun a => ((tickCost a : ℕ) : ℕ∞)) (toFreeMT s) (fun _ => 0) ≤ t) :
    s.TimeBound t :=
  timeBound_of_isRollBound s t ((FreeM.isRollBound_iff_wpFold_charge _ _ _).2 h)

/-! ## Compilation as a handler -/

/-- `compileTimed` is interpretation of the tick tree by `costHandler`. -/
theorem liftM_costHandler_toFreeMT (s : SPTree.Timed α) :
    (toFreeMT s).liftM costHandler = compileTimed s := by
  induction s with
  | ret a => rfl
  | fail =>
    simp only [toFreeMT, FreeM.liftM, compileTimed]
    change CostComp.bind (CostComp.lift SPComp.fail 0) _ = _
    unfold CostComp.bind CostComp.lift CostComp.fail
    simp only [SPComp.fail_bind]
  | load h₀ c t ih =>
    simp only [toFreeMT, FreeM.liftM, compileTimed, CostComp.loadC, ← ih]
    rfl
  | _ =>
    rename_i ih
    simp only [toFreeMT, FreeM.liftM, compileTimed, ← ih]
    rfl

end Timed

end SPTree

end CatCrypt.Core
