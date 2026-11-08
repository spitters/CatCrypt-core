/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OTExtension.IKNPSquare
import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
public import CatCryptCore.Crypto.UCSimulatorTimed
public import CatCryptCore.Tactics.DeriveSimulator
import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.DeriveTimeBound.Basic
public import CatCryptCore.Crypto.UCConcreteTimed

/-!
# Running time of the IKNP simulators and of the reduction to correlation-robust hashing

`derive_simulator` builds the costed forms, erasure theorems and time theorems of the two
simulators of `IKNPSquare.lean`, `iknpSimRecv` against a corrupt receiver and `iknpSimSend`
against a corrupt sender, together with those of the adversary-port simulator `postSim`; the
answer map of each simulator is a costed binder; `derive_hybrid_time` proves the time theorem
of the costed `postSim` from those of its steps. `derive_reduction` and `derive_time_bound`
build the costed form and the time theorem of the answer map `simSPost` of `iknpSimSend`.

`derive_reduction` builds the costed form `trigR.timed` of the triggered keyed system, and
`derive_time_bound` the time of its step. The tree of the environment reduction `iknpEnvCRRed` is
over `sysEnvTree` of `UCConcreteTimed`, and its time is the time of the environment, `4 t + 25`
per activation of the environment for an output map of cost at most `t`, the reset to the heap of
the environment and a constant.

No module imports this file.

## Main results

* `iknpEnvCRRed.compile_tree`, `iknpEnvCRRed.tree.timed`, `iknpEnvCRRed.tree.erase_timed`,
  `iknpEnvCRRed.tree.timeBound_timed`: the certificate of `iknpEnvCRRed`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OT.IKNPSquare

open CatCrypt.Core

derive_simulator iknpSimRecv
derive_simulator iknpSimSend
derive_reduction simSPost
derive_time_bound simSPost.tree
derive_hybrid_time postSim

open CatCrypt.Crypto.UCTransparent

derive_reduction trigR

derive_time_bound trigR.step.tree

/-- The computation tree of `iknpEnvCRRed`, over the key type `K`, the output map `out` of the
triggered system and a tree `step` of its step. -/
noncomputable def iknpEnvCRRed.tree {m : ℕ} {M K V : Type}
    (out : K → (Fin m → M × M) → (Fin m → Bool) → V) {ζ : Type}
    (Z : UCConcrete.Env (Strat ζ ((Fin m → M × M) ⊕ (Fin m → Bool)) (Bool ⊕ Option V)) ζ)
    (next : ζ → SPTree (ζ × ((Fin m → M × M) ⊕ (Fin m → Bool))))
    (step : K → FOTState m M → ((Fin m → M × M) ⊕ (Fin m → Bool)) →
      SPTree (FOTState m M × (Bool ⊕ Option V)))
    (obs : ζ → (Bool ⊕ Option V) → SPTree ζ) (dist : ζ → SPTree Bool) (k : K) : SPTree Bool :=
  sysEnvTree (trigR out).withKey Z next step obs dist k

/-- The tree of `iknpEnvCRRed` at the output map `crRView H` compiles to `iknpEnvCRRed H`. -/
theorem iknpEnvCRRed.compile_tree {κ m : ℕ} {M : Type} [AddCommGroup M]
    (H : Fin m → (Fin κ → Bool) → M) {ζ : Type}
    (Z : UCConcrete.Env (Strat ζ ((Fin m → M × M) ⊕ (Fin m → Bool))
      (Bool ⊕ Option (IKNPReceiverView κ m M Unit × (Fin m → M)))) ζ)
    {next : ζ → SPTree (ζ × ((Fin m → M × M) ⊕ (Fin m → Bool)))}
    {obs : ζ → (Bool ⊕ Option (IKNPReceiverView κ m M Unit × (Fin m → M))) → SPTree ζ}
    {dist : ζ → SPTree Bool} (hn : ∀ z, (next z).compile = Z.input.next z)
    (ho : ∀ z o, (obs z o).compile = Z.input.obs z o) (hd : ∀ z, (dist z).compile = Z.dist z)
    (th : (Fin m → Fin κ → Bool) × (Fin m → M)) :
    (iknpEnvCRRed.tree (crRView H) Z next (trigR.step.tree (crRView H)) obs dist th).compile =
      iknpEnvCRRed H Z th :=
  sysEnvTree_compile _ Z hn (fun k t e => trigR.step.compile_tree _ k t e) ho hd th

derive_timed iknpEnvCRRed.tree

/-- **Time of the reduction to correlation-robust hashing.** On the key `k`, for a costed strategy
of `Z` with its graded bounds, a distinguisher of time at most `tD` on its final states and an
output map of cost at most `t`, the reduction with the costed step of `trigR` costs at most the
reset to the heap of `Z`, the time of the strategy over its `q = Z.input.rounds` activations,
`tD`, `4 t + 25` per activation and `10`. The events and outputs of the system have no size
predicate: their types are finite for fixed `m` and `M`. -/
theorem iknpEnvCRRed.tree.timeBound_timed {m : ℕ} {M K V : Type}
    (out : K → (Fin m → M × M) → (Fin m → Bool) → V)
    {outCost : K → (Fin m → M × M) → (Fin m → Bool) → ℕ} {ζ : Type}
    (Z : UCConcrete.Env (Strat ζ ((Fin m → M × M) ⊕ (Fin m → Bool)) (Bool ⊕ Option V)) ζ)
    {next : ζ → SPTree.Timed (ζ × ((Fin m → M × M) ⊕ (Fin m → Bool)))} {nextCost : ζ → ℕ}
    {obs : ζ → (Bool ⊕ Option V) → SPTree.Timed ζ} {obsCost : ζ → (Bool ⊕ Option V) → ℕ}
    {dist : ζ → SPTree.Timed Bool} {distCost : ζ → ℕ} (k : K) {InvZ MidZ : ℕ → ζ → Prop}
    {tN tO : ℕ → ℕ} {tD t : ℕ}
    (hZ : StratRunBound next nextCost obs obsCost InvZ MidZ (fun _ _ => True) (fun _ _ => True)
      tN tO)
    (hz : InvZ 0 Z.input.init)
    (hd : ∀ z, InvZ Z.input.rounds z → SPTree.Timed.stepTime (distCost z, dist z) ≤ tD)
    (hout : ∀ k x r, outCost k x r ≤ t) :
    SPTree.Timed.stepTime
        (iknpEnvCRRed.tree.timed out outCost Z next nextCost (trigR.timed out outCost).step
          (trigR.timed out outCost).stepCost obs obsCost dist distCost k) ≤
      Z.heap.data.keys.card + (∑ i ∈ Finset.range Z.input.rounds, (tN i + tO i)) + tD +
        Z.input.rounds * (4 * t + 25) + 10 := by
  have hS : SysRunBound ((trigR.timed out outCost).step k) ((trigR.timed out outCost).stepCost k)
      (fun _ _ => True) (fun _ _ => True) (fun _ _ => True) (fun _ => 4 * t + 16) := by
    refine ⟨fun _ s e _ _ => ?_, fun _ s e _ _ =>
      SPTree.Timed.allRet_of_forall (fun _ => ⟨trivial, trivial⟩) _⟩
    have := trigR.step.tree.timeBound_timed out outCost k s e hout
    change SPTree.Timed.stepTime (trigR.step.tree.timed out outCost k s e) ≤ _
    omega
  have h := sysEnvTree.timeBound_timed (trigR out).withKey (fun _ => 2) Z k hZ hS hz trivial hd
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at h
  simp only [iknpEnvCRRed.tree.timed, SPTree.Timed.stepTime_delay]
  have : Z.input.rounds * (4 * t + 25) = Z.input.rounds * (4 * t + 16) + 9 * Z.input.rounds := by
    ring
  omega

end CatCrypt.Crypto.OT.IKNPSquare
