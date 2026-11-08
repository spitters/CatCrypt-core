/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OTExtension.ALSZ
import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
import CatCryptCore.Tactics.AutoTime
public import CatCryptCore.Tactics.AutoTime.Basic
public import CatCryptCore.Tactics.DeriveSimulator
import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.DeriveTimeBound.Basic
public import CatCryptCore.Crypto.UCSimulatorTimed
public import CatCryptCore.Crypto.UCChannelLiftTimed
public import CatCryptCore.Crypto.OTExtension.IKNPPVWTimed
public import CatCryptCore.Crypto.UCConcreteTimed

/-!
# Time of the PRG reduction and of the simulators of ALSZ

`derive_reduction` builds the costed forms of the hop reduction `prgHybRed` of the PRG hybrids,
over its distinguisher `D`, and of the reduction of ALSZ to the PRG `alszRed`, over the keyed
world `W` of the environment (`alszPrgRed G i Z` is `alszRed G i` over the world of `Z`), with
their erasure theorems; `time_bound` gives their times: the time of `D` (of `W`) plus its call
cost plus a constant. The simulator `simA` of one base OT is certified by `derive_reduction`,
`derive_time_bound` and `derive_hybrid_time`, and the simulator `simALSZ` of ALSZ over the seed
OTs by `derive_simulator`.

The reduction `alszPrgRed G i Z` of the environment `Z` is `alszRed G i` over the keyed world of
`Z`, the environment reduction of `UCConcreteTimed` over the IKNP parties with a fixed key
`iknpK`: its tree `alszPrgRed.tree` is the tree of `alszRed` over `sysEnvTree`, its costed form is
derived by `derive_timed`, and its time is the time of the world (the time of the environment,
of one step of the keyed system per activation, the reset to the heap of the environment and a
constant) plus a constant (`alszPrgRed.tree.timeBound_timed`). No module imports this file.

## Main results

* `prgHybRed.tree.timed`, `prgHybRed.tree.erase_timed`, `prgHybRed.tree.timeBound_timed`.
* `alszRed.tree.timed`, `alszRed.tree.erase_timed`, `alszRed.tree.timeBound_timed`.
* `alszPrgRed.compile_tree`, `alszPrgRed.tree.timed`, `alszPrgRed.tree.erase_timed`,
  `alszPrgRed.tree.timeBound_timed`.
* `simA.timed`, `simA.erase_timed`, `simA.timeBound_timed`.
* `simALSZ.timed`, `simALSZ.erase_timed`, `simALSZ.timeBound_timed`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OT.ALSZ

open CatCrypt.Core

derive_reduction prgHybRed

derive_reduction alszRed

/-- **Time of the reduction of ALSZ to the PRG.** With a keyed world of time at most `t` and call
cost at most `c`, the reduction runs in time at most `t + c + 4`. -/
theorem alszRed.tree.timeBound_timed {κ m : ℕ} {Seed : Type}
    (G : Assumptions.PRGDef Seed (Fin m → Bool)) [Fintype Seed] [Inhabited Seed] (i : Fin κ)
    (W : IKNPSquare.IKNPKey κ m → SPTree.Timed Bool) (WCost : IKNPSquare.IKNPKey κ m → ℕ)
    (y : Fin m → Bool) (yCost : Fin m → ℕ) {t c : ℕ} (hW : ∀ k, (W k).time ≤ t)
    (hc : ∀ k, WCost k ≤ c) :
    SPTree.Timed.stepTime (alszRed.tree.timed G i W WCost y yCost) ≤ t + c + 4 := by
  time_bound

/-- **Time of the hop reduction.** With a distinguisher of time at most `t` and call cost at most
`c`, the hop reduction of the PRG hybrids runs in time at most `t + c + 3`. -/
theorem prgHybRed.tree.timeBound_timed {κ : ℕ} {Seed Out : Type} [Fintype Seed]
    [Nonempty Seed] [Fintype Out] [Nonempty Out] (G : Assumptions.PRGDef Seed Out)
    (D : (Fin κ → Out) → SPTree.Timed Bool) (DCost : (Fin κ → Out) → ℕ) (i : Fin κ) (y : Out)
    {t c : ℕ} (hD : ∀ x, (D x).time ≤ t) (hc : ∀ x, DCost x ≤ c) :
    SPTree.Timed.stepTime (prgHybRed.tree.timed G D DCost i y) ≤ t + c + 3 := by
  time_bound

section EnvRed

open CatCrypt.Crypto CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.OT.IKNPWake
open CatCrypt.Crypto.OT.IKNPSquare

variable {κ m : ℕ} {Seed K τ E O : Type} (G : Assumptions.PRGDef Seed (Fin m → Bool))
  [Fintype Seed] [Inhabited Seed]

/-- The computation tree of `alszPrgRed G i Z`: the tree of `alszRed G i` over the tree of the
environment reduction over a family `S` of systems indexed by the image `ofKey k` of the key
(the IKNP parties with the key, `iknpK`, at `ofKey = id` for the reduction), with a tree `step`
of the step of `S`. -/
noncomputable def alszPrgRed.tree (i : Fin κ) (ofKey : IKNPKey κ m → K) (S : K → Sys τ E O)
    {ζ : Type} (Z : UCConcrete.Env (Strat ζ E O) ζ) (next : ζ → SPTree (ζ × E))
    (step : K → τ → E → SPTree (τ × O)) (obs : ζ → O → SPTree ζ)
    (dist : ζ → SPTree Bool) (y : Fin m → Bool) : SPTree Bool :=
  alszRed.tree G i (fun k => sysEnvTree S Z next step obs dist (ofKey k)) y

/-- The tree of `alszPrgRed G i Z` at the IKNP parties with the key compiles to
`alszPrgRed G i Z`. -/
theorem alszPrgRed.compile_tree {M : Type} [AddCommGroup M] (H : Fin m → (Fin κ → Bool) → M)
    {P L LS LR : Type} (φS : IKNPSenderView κ m Unit → LS)
    (φR : IKNPReceiverView κ m M Unit × (Fin m → M) → LR) (ans : Option LS → Option LR → P → L)
    [NeZero κ] (i : Fin κ) {ζ : Type}
    (Z : UCConcrete.Env (Strat ζ (((InEv m M ⊕ WakeEv κ) ⊕ P) ⊕ AEv κ m M)
      ((InOut m M ⊕ L) ⊕ AOut m M)) ζ)
    {next : ζ → SPTree (ζ × (((InEv m M ⊕ WakeEv κ) ⊕ P) ⊕ AEv κ m M))}
    {step : IKNPKey κ m → (PSt κ m M × Unit) × SubSt κ m M →
      ((InEv m M ⊕ WakeEv κ) ⊕ P) ⊕ AEv κ m M →
        SPTree (((PSt κ m M × Unit) × SubSt κ m M) × ((InOut m M ⊕ L) ⊕ AOut m M))}
    {obs : ζ → (InOut m M ⊕ L) ⊕ AOut m M → SPTree ζ} {dist : ζ → SPTree Bool}
    (hn : ∀ z, (next z).compile = Z.input.next z)
    (hs : ∀ k t e, (step k t e).compile = (iknpK H φS φR ans k).step t e)
    (ho : ∀ z o, (obs z o).compile = Z.input.obs z o) (hd : ∀ z, (dist z).compile = Z.dist z)
    (y : Fin m → Bool) :
    (alszPrgRed.tree G i id (iknpK H φS φR ans) Z next step obs dist y).compile =
      alszPrgRed H φS φR ans G i Z y := by
  rw [alszPrgRed.tree, alszRed.compile_tree]
  exact congrArg (fun W => alszRed G i W y)
    (funext fun k => sysEnvTree_compile _ Z hn hs ho hd k)

derive_timed alszPrgRed.tree

/-- **Time of the reduction of the environment to the PRG.** For a costed strategy of `Z` with
its graded bounds, a costed step of the systems `S k` with the bound `tS i` of the step at round
`i`, a distinguisher of time at most `tD`, systems of cost at most `cS` and a key map of cost at
most `cK`, the reduction costs at most twice the time `B` of the keyed world (the reset to the
heap of `Z`, the time of the strategy over its `q = Z.input.rounds` activations, `tD`, the time
of `q` system steps, `9` per activation, `cS` and `6`), plus `cK` and `7`. -/
theorem alszPrgRed.tree.timeBound_timed (i : Fin κ) (ofKey : IKNPKey κ m → K)
    (ofKeyCost : IKNPKey κ m → ℕ) (S : K → Sys τ E O) (SCost : K → ℕ) {ζ : Type}
    (Z : UCConcrete.Env (Strat ζ E O) ζ) {next : ζ → SPTree.Timed (ζ × E)} {nextCost : ζ → ℕ}
    {step : K → τ → E → SPTree.Timed (τ × O)} {stepCost : K → τ → E → ℕ}
    {obs : ζ → O → SPTree.Timed ζ} {obsCost : ζ → O → ℕ} {dist : ζ → SPTree.Timed Bool}
    {distCost : ζ → ℕ} (y : Fin m → Bool) (yCost : Fin m → ℕ) {InvZ MidZ : ℕ → ζ → Prop}
    {InvS : ℕ → τ → Prop} {Ev : ℕ → E → Prop} {Out : ℕ → O → Prop} {tN tS tO : ℕ → ℕ}
    {tD cS cK : ℕ} (hZ : StratRunBound next nextCost obs obsCost InvZ MidZ Ev Out tN tO)
    (hS : ∀ k, SysRunBound (step k) (stepCost k) InvS Ev Out tS)
    (hz : InvZ 0 Z.input.init) (ht : ∀ k, InvS 0 (S k).init)
    (hd : ∀ z, InvZ Z.input.rounds z → SPTree.Timed.stepTime (distCost z, dist z) ≤ tD)
    (hSc : ∀ k, SCost k ≤ cS) (hK : ∀ k, ofKeyCost k ≤ cK) :
    SPTree.Timed.stepTime (alszPrgRed.tree.timed G i ofKey ofKeyCost S SCost Z next nextCost
        step stepCost obs obsCost dist distCost y yCost) ≤
      2 * (Z.heap.data.keys.card + (∑ j ∈ Finset.range Z.input.rounds, (tN j + tO j)) + tD +
        (∑ j ∈ Finset.range Z.input.rounds, tS j) + 9 * Z.input.rounds + cS + 6) + cK + 7 := by
  set B := Z.heap.data.keys.card + (∑ j ∈ Finset.range Z.input.rounds, (tN j + tO j)) + tD +
    (∑ j ∈ Finset.range Z.input.rounds, tS j) + 9 * Z.input.rounds + cS + 6 with hB
  have hk : ∀ k, SPTree.Timed.stepTime (sysEnvTree.timed S SCost Z next nextCost step stepCost
      obs obsCost dist distCost (ofKey k)) ≤ B := fun k => by
    have h := sysEnvTree.timeBound_timed S SCost Z (ofKey k) hZ (hS _) hz (ht _) hd
    have := hSc (ofKey k)
    omega
  have h := alszRed.tree.timeBound_timed G i
    (fun k => (sysEnvTree.timed S SCost Z next nextCost step stepCost obs obsCost dist distCost
      (ofKey k)).2)
    (fun k => 2 + ofKeyCost k + (sysEnvTree.timed S SCost Z next nextCost step stepCost obs
      obsCost dist distCost (ofKey k)).1) y yCost (t := B) (c := B + 2 + cK)
    (fun k => by
      have := hk k
      simp only [SPTree.Timed.stepTime] at this
      omega)
    (fun k => by
      have := hk k
      have := hK k
      simp only [SPTree.Timed.stepTime] at *
      omega)
  simp only [alszPrgRed.tree.timed, SPTree.Timed.stepTime_delay]
  omega

end EnvRed

end CatCrypt.Crypto.OT.ALSZ

derive_reduction CatCrypt.Crypto.OT.ALSZ.simA
derive_time_bound CatCrypt.Crypto.OT.ALSZ.simA.start.tree
derive_time_bound CatCrypt.Crypto.OT.ALSZ.simA.resume.tree
derive_time_bound CatCrypt.Crypto.OT.ALSZ.simA.finish.tree
derive_hybrid_time CatCrypt.Crypto.OT.ALSZ.simA
derive_simulator CatCrypt.Crypto.OT.ALSZ.simALSZ
