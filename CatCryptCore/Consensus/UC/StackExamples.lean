/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.UC.Stack
public import CatCryptCore.Consensus.PoSNSB.ProbExamples

@[expose] public section
set_option autoImplicit false

/-!
# The stack at the lottery parameters

The hypotheses of `UC.Stack.stack_realizes` hold for the protocols
`PoSNSB.LotteryInstance.P` (one honest party elected by the stake-weighted election `μ`, slot
kinds with `pH = 3/4` and `pA = 0` on the first `1000` of `2000` slots, `Hash = Fin M`) with
`W = 1000`, `d = 1000`, `w = 10`, `ε = 1/4`, and the gadget parameters `cfg`: the slot tree,
stake `1` for the party `some 0` and `0` for the observer `none`, the honest validator
`some 0`, epochs of one slot, the pruned positions `slotCut Block.sl 1000`, delivery bound
`1` and the schedule from round `2004`. Since `K + 2 ≤ 2000`, every round of the run is below
`2005`, the round from which `F_FinTree` requires finality liveness.

## Main results

* `instance_realizes`: for every phase count `K` with `K + 2 ≤ 2000`, every signature scheme,
  every adversary and every delay bound `Δ`, FFG over PoS-NSB realizes `F_FinTree` with bound
  `slotBound ν 2000 1000 10 (1/4) + q (q - 1) / 2 / M` with `q = 2 ^ (K + 2)`.
* `instance_realizes_lt_one`: with `M = 4 ^ (K + 5)` the same realization holds with a bound
  below `1` (`PoSNSB.LotteryInstance.instance_bound_lt_one`).
-/

namespace CatCryptCore.Consensus.UC.Stack.LotteryInstance

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent CatCrypt.NonUniform
open CatCryptCore.Consensus.UC.FTree CatCryptCore.Consensus.UC.Chain
open CatCryptCore.Consensus.UC.FFGGadget
open PoSNSB PoSNSB.LotteryInstance Corruption
open CatCrypt.Crypto.Signatures CatCrypt.Crypto.Assumptions
open scoped ENNReal

attribute [local instance] PoSNSB.Instance.corruption

variable (M : ℕ) [NeZero M] (Hz : ℕ)

/-- The gadget parameters: the slot tree of `P M Hz`, stake `1` for the party `some 0` and `0`
for the observer `none`, the honest validator `some 0`, slots of blocks, epochs of one slot,
the pruned positions `slotCut Block.sl 1000`, delivery bound `1`, and the schedule from round
`2004 = 2 E + (1000 + 2) + 1000` read off the position of `some 0`. -/
noncomputable def cfg : Cfg (Option (Fin 1)) (Block Unit (Fin M) (Fin 1)) :=
  ⟨slotTree (P M Hz), fun o => o.elim 0 fun _ => 1, {some 0}, Block.sl, 1,
    slotCut Block.sl 1000, 1, 2004, some 0⟩

theorem cfg_honest (o : Option (Fin 1)) : o ∈ (cfg M Hz).H ↔ honestP o := by
  rcases o with _ | p
  · simp [cfg, honestP]
  · simp [cfg, honestP, Fin.fin_one_eq_zero p]
    rfl

/-- **The stack at the lottery parameters** (composition plumbing). For every phase count `K`
with `K + 2 ≤ 2000`, every signature scheme, every adversary, every delay bound `Δ` and every
exploded output `exF`, with `W = 1000`, `d = 1000`, `w = 10`, `ε = 1/4`, the random oracle
`H` and the gadget parameters `cfg`, every hypothesis of `stack_realizes` holds, so FFG over
PoS-NSB realizes `F_FinTree` with bound
`slotBound ν 2000 1000 10 (1/4) + q (q - 1) / 2 / M` with `q = 2 ^ (K + 2)`, the collision
term bounded by `PoSNSB.LotteryInstance.collFinder_advantage_le`. -/
theorem instance_realizes (K : ℕ) (hK : K + 2 ≤ 2000) {PK SK Sig : Type}
    (Sch : PSigScheme (Block Unit (Fin M) (Fin 1)) PK SK Sig) [Sch.Deterministic]
    (A : Adversary Unit (Fin M) 1 2000 (K + 1) PK Sig) (Δ : ℕ)
    (exF : TreeView (Option (Fin 1)) (Block Unit (Fin M) (Fin 1))) :
    Realizes (stackReal (P M (K + 1)) Sch A (Tree M (K + 1)) (H M (K + 1)) (cd M (K + 1))
        (cfg M (K + 1)) K μ 1000 Δ exF)
      (ideal (stackF (P M (K + 1)) Sch A (Tree M (K + 1)) (H M (K + 1)) (cd M (K + 1)) μ 1000 K
          1000 10 (1 / 4) Δ (cfg M (K + 1)) exF)
        (stackSim (P M (K + 1)) Sch A (Tree M (K + 1)) (H M (K + 1)) (cd M (K + 1)) μ 1000 K
          1000 10 (1 / 4) Δ (cfg M (K + 1)) exF))
      (fun _ _ => slotBound ν 2000 1000 10 (1 / 4) +
        ((2 ^ (K + 2) * (2 ^ (K + 2) - 1) / 2 : ℕ) : ℝ≥0∞) / M) := by
  have h := stack_realizes (P M (K + 1)) Sch A (Tree M (K + 1)) (H M (K + 1)) (cd M (K + 1)) μ
    1000 K 1000 10 (1 / 4) Δ (cfg M (K + 1)) exF (protocolHyp M (K + 1)) (tree_longest M (K + 1))
    (by norm_num) (by norm_num) hK le_rfl (by norm_num)
    (by rw [pH_ν, pA_ν]; norm_num) (by rw [pH_ν, pA_ν]; norm_num)
    (by rw [pH_ν, pA_ν]; norm_num) rfl (Or.inr (by norm_num)) rfl rfl (cfg_honest M (K + 1)) rfl
    le_rfl le_rfl (by simp [cfg]) rfl
    (show 3 * FFG.stake (fun o : Option (Fin 1) => o.elim 0 fun _ => 1)
        (Finset.univ \ {some 0}) < FFG.totalStake fun o : Option (Fin 1) => o.elim 0 fun _ => 1
      by decide)
  simp only [posFail, Finset.sum_eq_zero fun i _ => forger_advantage_of_honest (P M (K + 1)) Sch
      A hcor (H M (K + 1)) (cd M (K + 1)) μ 1000 K i, add_zero] at h
  intro ζ Z
  exact (h ζ Z).trans (add_le_add_right (collFinder_advantage_le M K Sch A) _)

/-- **A bound below `1`** (composition plumbing). With `M = 4 ^ (K + 5)` hash values, the
realization of `instance_realizes` holds with a bound `ε_K < 1`. -/
theorem instance_realizes_lt_one (K : ℕ) (hK : K + 2 ≤ 2000) {PK SK Sig : Type}
    (Sch : PSigScheme (Block Unit (Fin (4 ^ (K + 5))) (Fin 1)) PK SK Sig) [Sch.Deterministic]
    (A : Adversary Unit (Fin (4 ^ (K + 5))) 1 2000 (K + 1) PK Sig) (Δ : ℕ)
    (exF : TreeView (Option (Fin 1)) (Block Unit (Fin (4 ^ (K + 5))) (Fin 1))) :
    ∃ ε : ℝ≥0∞, ε < 1 ∧
      Realizes (stackReal (P (4 ^ (K + 5)) (K + 1)) Sch A (Tree (4 ^ (K + 5)) (K + 1))
          (H (4 ^ (K + 5)) (K + 1)) (cd (4 ^ (K + 5)) (K + 1)) (cfg (4 ^ (K + 5)) (K + 1)) K μ
          1000 Δ exF)
        (ideal (stackF (P (4 ^ (K + 5)) (K + 1)) Sch A (Tree (4 ^ (K + 5)) (K + 1))
            (H (4 ^ (K + 5)) (K + 1)) (cd (4 ^ (K + 5)) (K + 1)) μ 1000 K 1000 10 (1 / 4) Δ
            (cfg (4 ^ (K + 5)) (K + 1)) exF)
          (stackSim (P (4 ^ (K + 5)) (K + 1)) Sch A (Tree (4 ^ (K + 5)) (K + 1))
            (H (4 ^ (K + 5)) (K + 1)) (cd (4 ^ (K + 5)) (K + 1)) μ 1000 K 1000 10 (1 / 4) Δ
            (cfg (4 ^ (K + 5)) (K + 1)) exF))
        (fun _ _ => ε) :=
  ⟨_, instance_bound_lt_one K, instance_realizes (4 ^ (K + 5)) K hK Sch A Δ exF⟩

end CatCryptCore.Consensus.UC.Stack.LotteryInstance
