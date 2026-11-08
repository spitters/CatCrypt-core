/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCMonad.ConcurrentSys
public import CatCryptCore.Crypto.UCSimulatorCostGraded
public import CatCryptCore.Tactics.DeriveTimedStructure
import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
public import CatCryptCore.Crypto.OracleAdversaryFree
public import CatCryptCore.Core.SPTreeTimedFree
public import CatCryptCore.Tactics.AutoTime.Basic
public import CatCryptCore.Crypto.OracleAdversaryPotential
public import CatCryptCore.ForMathlib.ListLength

/-!
# Running time of the composite adversary system

The costed mirror `AdvSys.Timed` of adversary systems by `derive_timed_structure`, and the
costed form `AdvSys.comp.timed` of the composite adversary system by `derive_reduction`. The
composite `S.comp A` is the simulator of the dummy-adversary theorem
`UCMonad.ConcurrentSys.ucEmulatesSys_of_realizes` for the adversary `A`; its time is bounded
activation by activation by the times of `A` and `S`.

No module imports this file.

## Main definitions

* `AdvSys.Timed`, `AdvSys.Timed.Erases`, `AdvSys.Timed.TimeBound`: the costed mirror.
* `AdvSys.comp.timed`: the costed composite.
* `AdvSys.Timed.TimeBoundAt`: the time bound of a costed adversary system graded by the number
  of activations, on an invariant.
* `AdvSys.Timed.compInv`: the invariant of the composite state.

## Main results

* `AdvSys.comp.erase_timed`: the costed composite erases to `S.comp A`.
* `AdvSys.comp.timeBoundAt_timed`: activation `i` of the composite costs at most the costs of
  activation `i` of `A` and of `S`, plus two.
* `AdvSys.comp.timeBoundAt_timed_linear`: with `S` bounded by `a + b * i`, the composite is
  bounded by the time of `A` plus `a + 2 + b * i`.
-/

@[expose] public section

set_option autoImplicit false

derive_timed_structure CatCrypt.Crypto.UCTransparent.AdvSys

namespace CatCrypt.Crypto.UCTransparent

derive_reduction AdvSys.comp

open CatCrypt.Core

namespace AdvSys.Timed

variable {α σ : Type}

/-- The graded time bound of a costed adversary system on the invariant `Inv`, indexed by the
number of activations: the initial state satisfies `Inv 0`, and every `act` or `out` step from a
state of `Inv i` costs at most `T i` and returns states of `Inv (i + 1)`. -/
def TimeBoundAt {β X Y L L' : Type} (A : AdvSys.Timed β X Y L L') (Inv : ℕ → β → Prop)
    (T : ℕ → ℕ) : Prop :=
  Inv 0 A.init ∧
  (∀ i s x, Inv i s → SPTree.Timed.stepTime (A.actCost s x, A.act s x) ≤ T i ∧
    SPTree.Timed.AllRet (fun y => Inv (i + 1) y.1) (A.act s x)) ∧
  (∀ i s l, Inv i s → SPTree.Timed.stepTime (A.outCost s l, A.out s l) ≤ T i ∧
    SPTree.Timed.AllRet (fun y => Inv (i + 1) y.1) (A.out s l))

/-- The invariant of the composite state: each component satisfies its invariant at the same
activation count. -/
def compInv (InvA : ℕ → α → Prop) (InvS : ℕ → σ → Prop) (i : ℕ) (s : α × σ) : Prop :=
  InvA i s.1 ∧ InvS i s.2

end AdvSys.Timed

/-- **Running time of the composite adversary system**: activation `i` of the costed composite
`S.comp A` costs at most the cost of activation `i` of `A`, plus that of `S`, plus two. -/
theorem AdvSys.comp.timeBoundAt_timed {α σ AI AM AF LM LF Lk' : Type}
    (S : AdvSys σ AM AF LF LM) (A : AdvSys α AI AM LM Lk')
    (ST : AdvSys.Timed σ AM AF LF LM) (AT : AdvSys.Timed α AI AM LM Lk')
    (hS : ST.init = S.init) (hA : AT.init = A.init)
    {InvS : ℕ → σ → Prop} {InvA : ℕ → α → Prop} {TS TA : ℕ → ℕ}
    (hST : ST.TimeBoundAt InvS TS) (hAT : AT.TimeBoundAt InvA TA) :
    (AdvSys.comp.timed S A AT.act AT.actCost ST.act ST.actCost ST.out ST.outCost AT.out
      AT.outCost).TimeBoundAt (AdvSys.Timed.compInv InvA InvS)
      (fun i => TA i + TS i + 2) := by
  obtain ⟨hS0, hSa, hSo⟩ := hST
  obtain ⟨hA0, hAa, hAo⟩ := hAT
  refine ⟨⟨by simpa only [AdvSys.comp.timed, ← hA] using hA0,
    by simpa only [AdvSys.comp.timed, ← hS] using hS0⟩, fun i s x hs => ⟨?_, ?_⟩,
    fun i s l hs => ⟨?_, ?_⟩⟩
  · have := SPTree.Timed.stepTime_bind_bind_le 1 1 (AT.actCost s.1 x, AT.act s.1 x)
      (fun a => (ST.actCost s.2 a.2, ST.act s.2 a.2))
      (fun a b => (0, SPTree.Timed.ret ((a.1, b.1), b.2)))
      (hAa i s.1 x hs.1).1 (hAa i s.1 x hs.1).2 (fun a _ => (hSa i s.2 a.2 hs.2).1)
      (fun a _ => (hSa i s.2 a.2 hs.2).2) (TF := 0)
      (fun _ _ _ _ => by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret])
    simp only [AdvSys.comp.timed, AdvSys.comp.act.tree.timed, Prod.mk.eta] at this ⊢
    omega
  · simp only [AdvSys.comp.timed, AdvSys.comp.act.tree.timed, SPTree.Timed.delay,
      SPTree.Timed.allRet_bind]
    exact SPTree.Timed.allRet_mono (fun a ha => SPTree.Timed.allRet_mono
      (fun b hb => ⟨ha, hb⟩) _ (hSa i s.2 a.2 hs.2).2) _ (hAa i s.1 x hs.1).2
  · have := SPTree.Timed.stepTime_bind_bind_le 1 1 (ST.outCost s.2 l, ST.out s.2 l)
      (fun b => (AT.outCost s.1 b.2, AT.out s.1 b.2))
      (fun b a => (0, SPTree.Timed.ret ((a.1, b.1), a.2)))
      (hSo i s.2 l hs.2).1 (hSo i s.2 l hs.2).2 (fun b _ => (hAo i s.1 b.2 hs.1).1)
      (fun b _ => (hAo i s.1 b.2 hs.1).2) (TF := 0)
      (fun _ _ _ _ => by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret])
    simp only [AdvSys.comp.timed, AdvSys.comp.out.tree.timed, Prod.mk.eta] at this ⊢
    omega
  · simp only [AdvSys.comp.timed, AdvSys.comp.out.tree.timed, SPTree.Timed.delay,
      SPTree.Timed.allRet_bind]
    exact SPTree.Timed.allRet_mono (fun b hb => SPTree.Timed.allRet_mono
      (fun a ha => ⟨ha, hb⟩) _ (hAo i s.1 b.2 hs.1).2) _ (hSo i s.2 l hs.2).2

/-- **Running time of the simulator of the dummy-adversary theorem**: with `S` bounded by
`a + b * i` at activation `i`, activation `i` of the costed composite `S.comp A` costs at most
the cost of activation `i` of `A` plus `a + 2 + b * i`. -/
theorem AdvSys.comp.timeBoundAt_timed_linear {α σ AI AM AF LM LF Lk' : Type}
    (S : AdvSys σ AM AF LF LM) (A : AdvSys α AI AM LM Lk')
    (ST : AdvSys.Timed σ AM AF LF LM) (AT : AdvSys.Timed α AI AM LM Lk')
    (hS : ST.init = S.init) (hA : AT.init = A.init)
    {InvS : ℕ → σ → Prop} {InvA : ℕ → α → Prop} {TA : ℕ → ℕ} {a b : ℕ}
    (hST : ST.TimeBoundAt InvS fun i => a + b * i) (hAT : AT.TimeBoundAt InvA TA) :
    (AdvSys.comp.timed S A AT.act AT.actCost ST.act ST.actCost ST.out ST.outCost AT.out
      AT.outCost).TimeBoundAt (AdvSys.Timed.compInv InvA InvS)
      (fun i => TA i + (a + 2 + b * i)) := by
  have h := AdvSys.comp.timeBoundAt_timed S A ST AT hS hA hST hAT
  grind [AdvSys.Timed.TimeBoundAt]

end CatCrypt.Crypto.UCTransparent
