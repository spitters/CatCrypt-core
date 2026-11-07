/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SignalStackUC
public import CatCryptCore.Crypto.AKE.X3DHSquareTimed

/-!
# Running time of the simulator of the Signal stack

The simulator `chanSim π F` of `SignalStackUC.lean` is `Simulator.ofMultiHybrid (simSCOver π F)`:
a forwarding simulator `π` over `F_AKE` with its decisions read over `F_SC`. The simulator of the
Signal stack is `scSim G = chanSim (simProt G) x3dhFwd`. `derive_reduction simSCOver` gives the
costed form `simSCOver.timed`, in which the `start` step of the wrapped simulator is a costed
binder `start` with its cost companion, and `derive_simulator chanSim` and
`derive_simulator scSim` give the costed simulators, their erasure theorems and the time
theorems `chanSim.timeBound_timed` and `scSim.timeBound_timed` for a costed `start` of uniformly
bounded time.

**The time.** The costed form takes the reset `F.reset` and the phase `F.phase` of the
forwarding data with cost companions `resetCost`, `phaseCost`. A step of `simSCOver.timed`
costs at most `4 + tr + tp` more than the step of the wrapped costed simulator at the same state,
where `tr` and `tp` bound the costs of the reset and the phase (`simSCOver.timeBoundGraded_of`
and `chanSim.timeBoundGraded_of`, on any invariant of the wrapped steps preserved by the reset).
At the costed `start` of the X3DH simulator, whose `i`-th step costs at most `a + 40 i`
(`simProt.timeBoundGraded_timed`, the bound of `x3dhSim.timeBoundGraded_timed`), the `i`-th
activation of `scSim.timed` costs at most `a + 4 + tr + tp + 40 i`
(`scSim.timeBoundGraded_timed`, an instance of `chanSim.timeBoundGraded_of`): a polynomial in
the number of activations.

`derive_reduction simSC`, with the `start` step `simStart G` of the X3DH simulator reflected
again, is refused at the default heartbeats:

    derive_reduction: the first attempt fails:
      derive_reduction: at the plain interface:
        Tactic `simp` failed with a nested error:
        (deterministic) timeout at `simp`, maximum number of heartbeats (200000) has been reached

The restatement `simSC G = simSCOver (simProt G) x3dhFwd` (a definition of `SignalStackUC.lean`)
takes
the X3DH simulator as a parameter, so that its `start` step is a costed binder and its costed
form is that of `X3DHSquareTimed.lean`.

No module imports this file.

## Main results

* `simSCOver.timed`, `simSCOver.erase_timed` (derived): the costed wrapper and its erasure.
* `simSCOver.timeBoundGraded_of`: the graded time of the wrapper from that of the wrapped step.
* `chanSim.timed`, `chanSim.erase_timed`, `chanSim.timeBound_timed` (derived), and
  `chanSim.timeBoundGraded_of`: the costed simulator over `F_SC` of a forwarding simulator, its
  erasure, its uniform time and its graded time.
* `scSim.timed`, `scSim.erase_timed`, `scSim.timeBound_timed` (derived): the costed simulator,
  its erasure and its time for a uniformly bounded costed `start`.
* `scSim.timeBoundGraded_timed`: the graded time of `scSim.timed` at the costed X3DH simulator.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Messaging.SignalStackUC

open CatCrypt.Core CatCrypt.Crypto CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.AKE.X3DHSquare CatCrypt.Crypto.PAKE.DHExtract

derive_reduction simSCOver

derive_time_bound simSCOver.start.tree
derive_time_bound simSCOver.resume.tree
derive_time_bound simSCOver.finish.tree

/-- A costed tree `A` followed by a return at cost `2` and a return at cost `0`, after the step
cost `c`, runs within `c + A.time + 2`. -/
theorem stepTime_delay_bind_ret_le {α β γ : Type} (c : ℕ) (A : SPTree.Timed α) (g : α → β)
    (h : β → γ) :
    SPTree.Timed.stepTime (SPTree.Timed.delay
      (SPTree.Timed.delay c (A.bind fun y => (2, SPTree.Timed.ret (g y)))).1
      ((SPTree.Timed.delay c (A.bind fun y => (2, SPTree.Timed.ret (g y)))).2.bind
        fun y => (0, SPTree.Timed.ret (h y)))) ≤ c + A.time + 2 := by
  have h1 := SPTree.Timed.bind_ret_stepTime_le
    (SPTree.Timed.delay c (A.bind fun y => (2, SPTree.Timed.ret (g y)))) h
  have h2 := SPTree.Timed.stepTime_bind_le A (fun y => (2, SPTree.Timed.ret (g y))) 2
    (fun _ => by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret])
  simp only [SPTree.Timed.stepTime, SPTree.Timed.delay] at h1 h2 ⊢
  omega

/-- **Graded time of the wrapper.** If the costed `start` step of the wrapped simulator costs at
most `a + b i` from a state of the invariant `Inv i` and leads to states of `Inv (i + 1)`, and the
reset keeps the invariant, and the reset and the phase cost at most `tr` and `tp`, then each step
of `simSCOver.timed` costs at most `a + 4 + tr + tp + b i` after `i` activations. -/
theorem simSCOver.timeBoundGraded_of {K V AE R σ : Type}
    (π : MultiHybrid σ (HEv ⊕ AE) (HOut K ⊕ R) (FEv K) (FOut K)) (F : FwdData σ R)
    (start : σ → HEv ⊕ AE → SPTree.Timed (σ × (FEv K ⊕ (HOut K ⊕ R))))
    (startCost : σ → HEv ⊕ AE → ℕ) (resetCost phaseCost : σ → ℕ) (Inv : ℕ → σ → Prop)
    {a b tr tp : ℕ} (h0 : Inv 0 π.init)
    (hst : ∀ i s e, Inv i s → SPTree.Timed.stepTime (startCost s e, start s e) ≤ a + b * i ∧
      SPTree.Timed.AllRet (fun y => Inv (i + 1) y.1) (start s e))
    (hfwd : ∀ i (s : σ), Inv i s → Inv (i + 1) (F.reset s))
    (hr : ∀ s, resetCost s ≤ tr) (hp : ∀ s, phaseCost s ≤ tp) :
    (simSCOver.timed (V := V) π F F.reset resetCost F.phase phaseCost start
      startCost).TimeBoundGraded Inv (a + 4 + tr + tp) b := by
  refine ⟨h0, fun i s e hs => ⟨?_, ?_⟩, fun i s o hs => ⟨?_, ?_⟩, fun i s o hs => ⟨?_, ?_⟩⟩
  · obtain ⟨ht, -⟩ := hst i s e hs
    have h2 := SPTree.Timed.stepTime_bind_le (start s e)
      (fun x => (2, SPTree.Timed.ret (x.1, decK (V := V) x.2))) 2
      (fun _ => by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret])
    simp only [simSCOver.timed, simSCOver.start.tree.timed, SPTree.Timed.stepTime,
      SPTree.Timed.delay] at ht h2 ⊢
    omega
  · obtain ⟨-, hr⟩ := hst i s e hs
    simp only [simSCOver.timed, simSCOver.start.tree.timed, SPTree.Timed.delay]
    exact SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_mono (fun y hy => hy) _ hr)
  · have := hr s
    have := hp s
    simp only [simSCOver.timed, simSCOver.resume.tree.timed, SPTree.Timed.stepTime,
      SPTree.Timed.time_ret]
    omega
  · exact hfwd i s hs
  · have := hr s
    have := hp s
    simp only [simSCOver.timed, simSCOver.finish.tree.timed, SPTree.Timed.stepTime,
      SPTree.Timed.time_ret]
    omega
  · exact hfwd i s hs

derive_simulator chanSim

/-- **Graded time of the simulator over `F_SC` of a forwarding simulator.** If the costed `start`
step of `π` costs at most `a + b i` from a state of `Inv i` and leads to states of `Inv (i + 1)`,
the reset keeps the invariant, and the reset and the phase cost at most `tr` and `tp`, then the
`i`-th activation of `chanSim.timed` costs at most `a + 4 + tr + tp + b i`. -/
theorem chanSim.timeBoundGraded_of {K V AE R σ : Type}
    (π : MultiHybrid σ (HEv ⊕ AE) (HOut K ⊕ R) (FEv K) (FOut K)) (F : FwdData σ R)
    (resetCost phaseCost : σ → ℕ)
    (start : σ → HEv ⊕ AE → SPTree.Timed (σ × (FEv K ⊕ (HOut K ⊕ R))))
    (startCost : σ → HEv ⊕ AE → ℕ) (Inv : ℕ → σ → Prop) {a b tr tp : ℕ}
    (h0 : Inv 0 π.init)
    (hst : ∀ i s e, Inv i s → SPTree.Timed.stepTime (startCost s e, start s e) ≤ a + b * i ∧
      SPTree.Timed.AllRet (fun y => Inv (i + 1) y.1) (start s e))
    (hfwd : ∀ i (s : σ), Inv i s → Inv (i + 1) (F.reset s))
    (hr : ∀ s, resetCost s ≤ tr) (hp : ∀ s, phaseCost s ≤ tp) :
    (chanSim.timed (V := V) π F resetCost phaseCost start startCost).TimeBoundGraded
      (a + 4 + tr + tp) b :=
  ⟨Inv, simSCOver.timeBoundGraded_of π F start startCost resetCost phaseCost Inv h0 hst hfwd
    hr hp⟩

derive_simulator scSim

variable {S W K V : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K]
  [Inhabited K] (G : DHGroup S W)

/-- **Graded time of the simulator of the Signal stack.** At the costed `start` step of the X3DH
simulator, with the costs of `coe`, of the exponentiation and of `toFun` at most `tc`, `te`,
`tf`, and the costs of the reset and the phase of `x3dhFwd` at most `tr`, `tp`, the `i`-th
activation of `scSim.timed` costs at most `a + 4 + tr + tp + 40 i` with
`a = 200 + 20 tc + 20 te + 20 tf`, the bound `a + 40 i` of `x3dhSim.timeBoundGraded_timed`
plus the cost of the wrapper. -/
theorem scSim.timeBoundGraded_timed (coeCost : S ≃ W → S → ℕ) (expCost : W → S → ℕ)
    (toFunCost : S → ℕ) {tc te tf : ℕ} (hc : ∀ a b, coeCost a b ≤ tc)
    (he : ∀ a b, expCost a b ≤ te) (hf : ∀ a, toFunCost a ≤ tf)
    (resetCost phaseCost : SimSt S W K → ℕ) {tr tp : ℕ} (hr : ∀ s, resetCost s ≤ tr)
    (hp : ∀ s, phaseCost s ≤ tp) :
    (scSim.timed (V := V) G resetCost phaseCost
        (simProt.timed (K := K) G DFunLike.coe coeCost expCost toFunCost).start
        (simProt.timed G DFunLike.coe coeCost expCost toFunCost).startCost).TimeBoundGraded
      (200 + 20 * tc + 20 * te + 20 * tf + 4 + tr + tp) 40 := by
  obtain ⟨h0, hst, -, -⟩ :=
    simProt.timeBoundGraded_timed (K := K) G DFunLike.coe coeCost expCost toFunCost hc he hf
  exact chanSim.timeBoundGraded_of _ _ _ _ _ _ SimInv h0 hst
    (fun i s hs => ⟨hs.1.trans (Nat.le_succ i), hs.2.trans (Nat.le_succ i)⟩) hr hp

end CatCrypt.Crypto.Messaging.SignalStackUC
