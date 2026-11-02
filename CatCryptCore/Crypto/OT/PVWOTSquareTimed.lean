/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OT.PVWOTSquare
public import CatCryptCore.Crypto.UCConcreteTimed

/-!
# Running time of the reduction of the PVW mode hop to DDH

The tree of the environment reduction `ddhEnvRed` of `PVWOTSquare.lean`, over `sysEnvTree` of
`UCConcreteTimed` and a tree of the step of the family `S` of systems, a parameter of the
reduction; its costed form by `derive_timed`; and its time: the time of the environment, the time
of one step of `S` per activation of the environment, the reset to the heap of the environment
and a constant.

No module imports this file.

## Main results

* `ddhEnvRed.compile_tree`, `ddhEnvRed.tree.timed`, `ddhEnvRed.tree.erase_timed`,
  `ddhEnvRed.tree.timeBound_timed`: the certificate of `ddhEnvRed`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OT.PVW

open CatCrypt.Core CatCrypt.Crypto CatCrypt.Crypto.UCTransparent CatCrypt.NonUniform
open CatCrypt.Examples

variable {gp : GroupParam} {τ E O : Type}

/-- The computation tree of `ddhEnvRed`, over a tree `step` of the step of `S` at the CRS of the
triple. -/
noncomputable def ddhEnvRed.tree (S : CRS gp → Sys τ E O) (t₀ : τ) {ζ : Type}
    (Z : UCConcrete.Env (Strat ζ E O) ζ) (next : ζ → SPTree (ζ × E))
    (step : gp.G × gp.G × gp.G → τ → E → SPTree (τ × O)) (obs : ζ → O → SPTree ζ)
    (dist : ζ → SPTree Bool) (tr : gp.G × gp.G × gp.G) : SPTree Bool :=
  sysEnvTree (fun tr => (crsKeyed id S t₀).withKey ⟨gp.generator, tr.1, tr.2.1, tr.2.2⟩) Z next
    step obs dist tr

/-- The tree of `ddhEnvRed` compiles to `ddhEnvRed`. -/
theorem ddhEnvRed.compile_tree (S : CRS gp → Sys τ E O) (t₀ : τ) {ζ : Type}
    (Z : UCConcrete.Env (Strat ζ E O) ζ) {next : ζ → SPTree (ζ × E)}
    {step : gp.G × gp.G × gp.G → τ → E → SPTree (τ × O)} {obs : ζ → O → SPTree ζ}
    {dist : ζ → SPTree Bool} (hn : ∀ z, (next z).compile = Z.input.next z)
    (hs : ∀ tr t e, (step tr t e).compile =
      (S ⟨gp.generator, tr.1, tr.2.1, tr.2.2⟩).step t e)
    (ho : ∀ z o, (obs z o).compile = Z.input.obs z o) (hd : ∀ z, (dist z).compile = Z.dist z)
    (tr : gp.G × gp.G × gp.G) :
    (ddhEnvRed.tree S t₀ Z next step obs dist tr).compile = ddhEnvRed S t₀ Z tr :=
  sysEnvTree_compile
    (fun tr : gp.G × gp.G × gp.G =>
      (crsKeyed id S t₀).withKey ⟨gp.generator, tr.1, tr.2.1, tr.2.2⟩)
    Z hn hs ho hd tr

derive_timed ddhEnvRed.tree

/-- **Time of the reduction to DDH.** On the triple `tr`, for a costed strategy of `Z` and a
costed step of `S` at the CRS of `tr` over the same interface, from initial states of their
invariants and with a distinguisher of time at most `tD` on the final states, the reduction costs
at most the reset to the heap of `Z`, the time of the strategy over its `q = Z.input.rounds`
activations, `tD`, the time of `q` steps of `S`, `9` per activation and `9`. -/
theorem ddhEnvRed.tree.timeBound_timed (S : CRS gp → Sys τ E O) (SCost : CRS gp → ℕ) (t₀ : τ)
    {ζ : Type} (Z : UCConcrete.Env (Strat ζ E O) ζ) {next : ζ → SPTree.Timed (ζ × E)}
    {nextCost : ζ → ℕ} {step : gp.G × gp.G × gp.G → τ → E → SPTree.Timed (τ × O)}
    {stepCost : gp.G × gp.G × gp.G → τ → E → ℕ} {obs : ζ → O → SPTree.Timed ζ}
    {obsCost : ζ → O → ℕ} {dist : ζ → SPTree.Timed Bool} {distCost : ζ → ℕ}
    (tr : gp.G × gp.G × gp.G) {InvZ MidZ : ℕ → ζ → Prop} {InvS : ℕ → τ → Prop}
    {Ev : ℕ → E → Prop} {Out : ℕ → O → Prop} {tN tS tO : ℕ → ℕ} {tD : ℕ}
    (hZ : StratRunBound next nextCost obs obsCost InvZ MidZ Ev Out tN tO)
    (hS : SysRunBound (step tr) (stepCost tr) InvS Ev Out tS)
    (hz : InvZ 0 Z.input.init) (ht : InvS 0 t₀)
    (hd : ∀ z, InvZ Z.input.rounds z → SPTree.Timed.stepTime (distCost z, dist z) ≤ tD) :
    SPTree.Timed.stepTime
        (ddhEnvRed.tree.timed S SCost t₀ Z next nextCost step stepCost obs obsCost dist distCost
          tr) ≤
      Z.heap.data.keys.card + (∑ i ∈ Finset.range Z.input.rounds, (tN i + tO i)) + tD +
        (∑ i ∈ Finset.range Z.input.rounds, tS i) + 9 * Z.input.rounds + 9 := by
  have h := sysEnvTree.timeBound_timed
    (fun tr => (crsKeyed id S t₀).withKey ⟨gp.generator, tr.1, tr.2.1, tr.2.2⟩) (fun _ => 2) Z tr
    hZ hS hz ht hd
  simp only [ddhEnvRed.tree.timed, SPTree.Timed.stepTime_delay]
  omega

end CatCrypt.Crypto.OT.PVW
