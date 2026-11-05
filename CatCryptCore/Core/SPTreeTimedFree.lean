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
public import CatCryptCore.ForMathlib.PFunctorChargeUnder
public import CatCryptCore.ForMathlib.PFunctorRestrict
public import CatCryptCore.Core.SPTreeTimedOps
public import CatCryptCore.XDijkstra.XTimedMonad
import all CatCryptCore.Core.SPTreeTimed
import all CatCryptCore.Unary.ExpectedCost

/-!
# Costed `SPTree`s as free monads with a tick operation

`SPTree.Timed α` translates to the free monad `PFunctor.FreeM SPSigT α` of the polynomial
functor `SPSigT = SPTree.Sig + TickSig`, whose extra positions `tick n` charge `n` units and have
one direction. The translation `SPTree.Timed.toFreeMT` follows each direction `x` of a node with
step cost `c` by the tick `c x`.

## Main definitions

* `SPTree.TickSig`, `SPTree.SPSigT` — the tick polynomial and the ticked signature
* `SPTree.tickCost` — `opCost` at an operation of `SPTree.Sig`, `n` at `tick n`
* `SPTree.spAllows` — the answers a handler can return: the support of `μ` at `sampleDist β μ`
* `SPTree.Timed.toFreeMT` — the tick tree of a costed tree
* `SPTree.eraseHandler` — the handler into `FreeM SPTree.Sig` that keeps operations and drops
  ticks
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
* `SPTree.Timed.timeBound_iff_wpFold_chargeUnder` — `TimeBound` is the bound on the charge fold
  of the tick tree over the answers allowed by `spAllows`
* `SPTree.Timed.le_and_timeBound_iff_wpFold_chargeUnder` — the step cost followed by a time
  bound is the bound on the charge fold of the step-prefixed tick tree `stepToFreeMT`
* `SPTree.Timed.wpFold_stepToFreeMT_bind` — the charge fold of a costed bind is the charge fold
  of the bind of the tick trees
* `SPTree.Timed.allRet_iff_wpFold_demonicUnder` — `AllRet` is the demonic fold of the tick tree
  with every answer allowed; `SPTree.Timed.wpFold_demonicUnder_spAllows_of_allRet` restricts it
  to the answers allowed by `spAllows`
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

/-- The polynomial functor of costed `SPTree`s: `SPTree.Sig` with tick positions. -/
abbrev SPSigT : PFunctor.{1, 0} := SPTree.Sig + TickSig

/-- The charge of a position of `SPSigT`: `opCost a` at an operation `a`, `n` at `tick n`. -/
def tickCost : SPSigT.A → ℕ
  | .inl a => opCost a
  | .inr n => n

/-- The answers of a position of `SPSigT` that its handler can return: the support of `μ` at
`sampleDist β μ`, every answer elsewhere. -/
def spAllows : (a : SPSigT.A) → SPSigT.B a → Prop
  | .inl (.sampleDist _ μ), b => b ∈ μ.support
  | _, _ => True

/-- The handler into `FreeM SPTree.Sig` that keeps each operation and answers each tick with
`()`. -/
def eraseHandler : Handler (FreeM SPTree.Sig) SPSigT :=
  Handler.sum (Handler.id SPTree.Sig) fun _ => FreeM.pure PUnit.unit

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
    change FreeM.bind (FreeM.lift (P := SPTree.Sig) SPTree.Op.fail) _ = _
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
    have : IsEmpty (SPSigT.B (.inl SPTree.Op.fail)) := inferInstanceAs (IsEmpty PEmpty)
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

/-- `TimeBound` is the bound on the charge fold of the tick tree over the answers allowed by
`spAllows`. -/
theorem timeBound_iff_wpFold_chargeUnder (s : SPTree.Timed α) (t : ℕ) :
    s.TimeBound t ↔
      wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) spAllows) (toFreeMT s)
        (fun _ => 0) ≤ t := by
  induction s generalizing t with
  | ret a => simp [TimeBound, toFreeMT]
  | fail =>
    exact iff_of_true trivial ((wpFold_chargeUnder_liftBind_le_iff _ _ _ _ _).2
      ⟨Nat.zero_le _, fun b => PEmpty.elim b⟩)
  | sample β finβ neβ c k ih =>
    simp only [TimeBound, toFreeMT, wpFold_chargeUnder_liftBind_le_iff, spAllows,
      Nat.sub_sub, tickCost, opCost] at ih ⊢
    simp only [ih]
    exact and_congr_right fun _ => forall_congr' fun b =>
      ⟨fun h _ => ⟨by omega, fun _ _ => h.2⟩, fun h => ⟨by have := (h trivial).1; omega,
        (h trivial).2 PUnit.unit trivial⟩⟩
  | sampleDist β μ c k ih =>
    simp only [TimeBound, toFreeMT, wpFold_chargeUnder_liftBind_le_iff, spAllows,
      Nat.sub_sub, tickCost, opCost] at ih ⊢
    simp only [ih]
    exact and_congr_right fun _ => forall_congr' fun b =>
      ⟨fun h hb => ⟨by have := (h hb).1; omega, fun _ _ => (h hb).2⟩,
        fun h hb => ⟨by have := (h hb).1; omega, (h hb).2 PUnit.unit trivial⟩⟩
  | get l c k ih =>
    simp only [TimeBound, toFreeMT, wpFold_chargeUnder_liftBind_le_iff, spAllows,
      Nat.sub_sub, tickCost, opCost] at ih ⊢
    simp only [ih]
    exact and_congr_right fun _ => forall_congr' fun b =>
      ⟨fun h _ => ⟨by omega, fun _ _ => h.2⟩, fun h => ⟨by have := (h trivial).1; omega,
        (h trivial).2 PUnit.unit trivial⟩⟩
  | set l v c t' ih =>
    simp only [TimeBound, toFreeMT, wpFold_chargeUnder_liftBind_le_iff, spAllows,
      Nat.sub_sub, tickCost, opCost] at ih ⊢
    simp only [ih]
    exact ⟨fun h => ⟨by have := h.1; omega,
        fun _ _ => ⟨by have := h.1; omega, fun _ _ => h.2⟩⟩,
      fun h => ⟨by have := h.1; have := (h.2 PUnit.unit trivial).1; omega,
        (h.2 PUnit.unit trivial).2 PUnit.unit trivial⟩⟩
  | load h₀ c t' ih =>
    simp only [TimeBound, toFreeMT, wpFold_chargeUnder_liftBind_le_iff, spAllows,
      Nat.sub_sub, tickCost, opCost] at ih ⊢
    simp only [ih]
    exact ⟨fun h => ⟨by have := h.1; omega,
        fun _ _ => ⟨by have := h.1; omega, fun _ _ => h.2⟩⟩,
      fun h => ⟨by have := h.1; have := (h.2 PUnit.unit trivial).1; omega,
        (h.2 PUnit.unit trivial).2 PUnit.unit trivial⟩⟩

/-! ## Step-prefixed trees, sequencing and leaves -/

/-- The step-prefixed tree `(c, s)` as a tree of `SPSigT`: the tick `c` followed by the tick
tree of `s`. -/
def stepToFreeMT (x : ℕ × SPTree.Timed α) : FreeM SPSigT α :=
  .liftBind (P := SPSigT) (.inr x.1) fun _ => toFreeMT x.2

/-- The charge fold of a step-prefixed tree, with every tick answer allowed, is its step cost
plus the charge fold of its tree. -/
theorem wpFold_chargeUnder_stepToFreeMT (allows : (a : SPSigT.A) → SPSigT.B a → Prop)
    (hA : ∀ n, allows (.inr n) PUnit.unit) (x : ℕ × SPTree.Timed α) (post : α → ℕ∞) :
    wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows) (stepToFreeMT x) post =
      x.1 + wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows)
        (toFreeMT x.2) post :=
  wpFold_chargeUnder_liftBind_const _ allows _ (hA x.1) _ post

/-- A bound `n` on the charge fold of the tick tree of `x` bounds `stepTime x`. -/
theorem stepTime_le_of_wpFold_le (x : ℕ × SPTree.Timed α) (n : ℕ)
    (h : wpFold (OpSpec.charge fun a => ((tickCost a : ℕ) : ℕ∞)) (stepToFreeMT x)
      (fun _ => 0) ≤ n) :
    stepTime x ≤ n := by
  rw [← OpSpec.chargeUnder_true, wpFold_chargeUnder_stepToFreeMT _ (fun _ => trivial),
    OpSpec.chargeUnder_true] at h
  have : ((x.1 + x.2.time : ℕ) : ℕ∞) ≤ n := by
    rw [Nat.cast_add]
    exact (add_le_add le_rfl (time_le_wpFold x.2)).trans h
  exact_mod_cast this

/-- The step cost followed by a time bound on the tree is the bound on the charge fold of the
step-prefixed tick tree over the answers allowed by `spAllows`. -/
theorem le_and_timeBound_iff_wpFold_chargeUnder (x : ℕ × SPTree.Timed α) (n : ℕ) :
    (x.1 ≤ n ∧ x.2.TimeBound (n - x.1)) ↔
      wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) spAllows) (stepToFreeMT x)
        (fun _ => 0) ≤ n := by
  rw [stepToFreeMT, wpFold_chargeUnder_liftBind_le_iff, timeBound_iff_wpFold_chargeUnder]
  exact and_congr_right fun _ => ⟨fun h _ _ => h, fun h => h PUnit.unit trivial⟩

/-- The time bound of a probabilistic tree is the worst-case charge of its tick tree restricted
to the supports of its sampling nodes. -/
theorem timeBound_iff_wpFold_charge_restrict (s : SPTree.Timed α) (t : ℕ) :
    s.TimeBound t ↔
      wpFold (OpSpec.charge (P := SPSigT.restrict spAllows)
          (fun a => ((tickCost a : ℕ) : ℕ∞)))
        ((toFreeMT s).restrict spAllows) (fun _ => 0) ≤ t := by
  rw [timeBound_iff_wpFold_chargeUnder, FreeM.wpFold_chargeUnder_eq_restrict]
  exact Iff.rfl

/-- The step cost followed by a time bound on the tree is the bound on the worst-case charge of
the step-prefixed tick tree restricted to the supports of its sampling nodes. -/
theorem le_and_timeBound_iff_wpFold_charge_restrict (x : ℕ × SPTree.Timed α) (n : ℕ) :
    (x.1 ≤ n ∧ x.2.TimeBound (n - x.1)) ↔
      wpFold (OpSpec.charge (P := SPSigT.restrict spAllows)
          (fun a => ((tickCost a : ℕ) : ℕ∞)))
        ((stepToFreeMT x).restrict spAllows) (fun _ => 0) ≤ n := by
  rw [le_and_timeBound_iff_wpFold_chargeUnder, FreeM.wpFold_chargeUnder_eq_restrict]
  exact Iff.rfl

/-- The bind clause of the tick tree: the charge fold of a costed bind is the charge fold of the
FreeM bind of the tick tree with the step-prefixed tick trees of the continuation, for every
`allows` admitting the tick answers. The costed bind merges the tick `c b` of an edge with the
step cost of the continuation, so this is an equation of folds. -/
theorem wpFold_stepToFreeMT_bind {β : Type} (allows : (a : SPSigT.A) → SPSigT.B a → Prop)
    (hA : ∀ n, allows (.inr n) PUnit.unit) (A : SPTree.Timed α) (f : α → ℕ × SPTree.Timed β)
    (post : β → ℕ∞) :
    wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows)
        (stepToFreeMT (A.bind f)) post =
      wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows)
        ((toFreeMT A).bind (stepToFreeMT ∘ f)) post := by
  have hstep : ∀ y : ℕ × SPTree.Timed β,
      wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows) (stepToFreeMT y)
        post =
      y.1 + wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows)
        (toFreeMT y.2) post :=
    fun y => wpFold_chargeUnder_stepToFreeMT allows hA y post
  have htick : ∀ {γ : Type} (n : ℕ) (y : FreeM SPSigT γ) (q : γ → ℕ∞),
      wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows)
        (FreeM.liftBind (P := SPSigT) (.inr n) fun _ => y) q =
      n + wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) allows) y q :=
    fun n y q => wpFold_chargeUnder_liftBind_const _ allows (.inr n) (hA n) y q
  rw [wpFold_bind']
  induction A with
  | ret a => rfl
  | fail =>
    rw [hstep]
    simp only [bind, Nat.cast_zero, zero_add]
    simp only [toFreeMT]
    exact congrArg _ (funext fun b => PEmpty.elim b)
  | sample γ finγ neγ c k ih =>
    rw [hstep]
    simp only [bind, toFreeMT, wpFold_liftBind, OpSpec.chargeUnder_apply, htick, Nat.cast_zero,
      zero_add]
    refine congrArg _ (iSup_congr fun b => iSup_congr fun _ => ?_)
    rw [← ih b, hstep, Nat.cast_add, add_assoc]
  | sampleDist γ μ c k ih =>
    rw [hstep]
    simp only [bind, toFreeMT, wpFold_liftBind, OpSpec.chargeUnder_apply, htick, Nat.cast_zero,
      zero_add]
    refine congrArg _ (iSup_congr fun b => iSup_congr fun _ => ?_)
    rw [← ih b, hstep, Nat.cast_add, add_assoc]
  | get l c k ih =>
    rw [hstep]
    simp only [bind, toFreeMT, wpFold_liftBind, OpSpec.chargeUnder_apply, htick, Nat.cast_zero,
      zero_add]
    refine congrArg _ (iSup_congr fun b => iSup_congr fun _ => ?_)
    rw [← ih b, hstep, Nat.cast_add, add_assoc]
  | set l v c t ih =>
    rw [hstep]
    simp only [bind, toFreeMT, wpFold_liftBind, OpSpec.chargeUnder_apply, htick, Nat.cast_zero,
      zero_add]
    refine congrArg _ (iSup_congr fun _ => iSup_congr fun _ => ?_)
    rw [← ih, hstep, Nat.cast_add, add_assoc]
  | load h₀ c t ih =>
    rw [hstep]
    simp only [bind, toFreeMT, wpFold_liftBind, OpSpec.chargeUnder_apply, htick, Nat.cast_zero,
      zero_add]
    refine congrArg _ (iSup_congr fun _ => iSup_congr fun _ => ?_)
    rw [← ih, hstep, Nat.cast_add, add_assoc]

/-- `AllRet Q s` is the demonic fold of `Q` over the tick tree of `s` with every answer
allowed. -/
theorem allRet_iff_wpFold_demonicUnder (Q : α → Prop) (s : SPTree.Timed α) :
    AllRet Q s ↔ wpFold (OpSpec.demonicUnder fun _ _ => True) (toFreeMT s) Q := by
  induction s with
  | ret a => rfl
  | fail => exact iff_of_true trivial fun b => PEmpty.elim b
  | sample _ _ _ _ k ih =>
    exact ⟨fun h b _ _ _ => (ih b).1 (h b), fun h b => (ih b).2 (h b trivial PUnit.unit trivial)⟩
  | sampleDist _ _ _ k ih =>
    exact ⟨fun h b _ _ _ => (ih b).1 (h b), fun h b => (ih b).2 (h b trivial PUnit.unit trivial)⟩
  | get _ _ k ih =>
    exact ⟨fun h b _ _ _ => (ih b).1 (h b), fun h b => (ih b).2 (h b trivial PUnit.unit trivial)⟩
  | set _ _ _ t ih =>
    exact ⟨fun h _ _ _ _ => ih.1 h, fun h => ih.2 (h PUnit.unit trivial PUnit.unit trivial)⟩
  | load _ _ t ih =>
    exact ⟨fun h _ _ _ _ => ih.1 h, fun h => ih.2 (h PUnit.unit trivial PUnit.unit trivial)⟩

/-- Every leaf invariant of `s` holds at the returns of its tick tree reachable under the
answers allowed by `spAllows`. -/
theorem wpFold_demonicUnder_spAllows_of_allRet {Q : α → Prop} {s : SPTree.Timed α}
    (h : AllRet Q s) : wpFold (OpSpec.demonicUnder spAllows) (toFreeMT s) Q :=
  wpFold_demonicUnder_of_le (fun _ _ _ => trivial) ((allRet_iff_wpFold_demonicUnder Q s).1 h)

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
