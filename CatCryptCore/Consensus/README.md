# Consensus: Casper FFG over Nakamoto-style proof of stake

`CatCryptCore/Consensus/` formalizes the Casper FFG finality gadget running over a
Nakamoto-style proof-of-stake longest chain. It proves accountable safety of FFG for a
fixed and for a changing validator set. It ports the Coq development PoS-NSB of Thomsen
and Spitters [TS21]: chain growth, chain quality and common prefix for every execution
whose lottery satisfies slot conditions. It bounds the probability that these properties
fail for a random stake-weighted lottery, a random oracle and a signature scheme, with
forging reduced to EUF-CMA by explicit adversaries. It proves that FFG over
this chain is chain-forming, in agreement, v-valid and Δ-updated, the last with high
probability. Finally it composes the two layers in the universally composable style of
Afgjort [DMM+20] and Enig [KNTT22]: PoS-NSB realizes the tree functionality `F_Tree` in
the clock-and-network hybrid model, FFG in the `F_Tree`-hybrid model realizes the finality
functionality `F_FinTree` with advantage `0` when the adversarial stake is below one
third, and the stacked protocol realizes `F_FinTree` with the failure bound of the chain
layer. The numeric terms of every bound are information-theoretic (a Chernoff-Hoeffding
tail on the lottery and a birthday bound on the random oracle); the signature scheme
enters through the EUF-CMA advantages of explicit forgers. The namespace is
`CatCryptCore.Consensus`.

## Accountable safety of Casper FFG

Validators carry natural-number stake, thresholds are stated without division, and the
block tree is any reflexive and transitive ancestor relation. The slashing conditions
are E1 (two distinct votes with the same target epoch) and E2 (a vote surrounding another
vote of the same validator) [BG17, BHK+20].

| Statement | Lean |
|---|---|
| Two sets each holding at least two thirds of the stake intersect in at least one third of it. | [`quorum_intersection`](FFG.lean) |
| If two checkpoints on conflicting blocks are finalized, the validators violating E1 or E2 hold at least one third of the stake; the same for `k`-finalization (Gasper, Definition 4.3 and Theorem 4.4), with possibly different `k` for the two checkpoints. | [`accountable_safety`](FFG.lean), [`accountable_safety_kFinalized`](FFG.lean) |
| If less than one third of the stake is slashable, every justified checkpoint at an epoch not below that of a `k`-finalized checkpoint descends from it. | [`anc_of_kFinalized_of_justified`](FFG.lean) |
| Plausible liveness: an unslashable honest set holding two thirds of the stake, whose votes have sources not above a justified checkpoint `j`, finalizes a new checkpoint descending from `j` with explicit votes and stays unslashable. | [`plausible_liveness`](FFG.lean), [`plausible_liveness_of_highest`](FFG.lean) |
| With a validator set that changes between epochs, a link weighed by the set active at its source epoch, and `churn` the stake not held throughout the epochs up to the larger finalized epoch `E`: two conflicting finalized checkpoints give `W_stable ≤ 3 · stake_stable(slashable) + 2 · churn`. | [`accountable_safety_dynamic`](FFGDynamic.lean) |
| The same for checkpoints finalized from an anchor checkpoint of epoch `e₀`, with the churn taken over the epochs `e₀, …, E` only. | [`accountable_safety_dynamic_from`](FFGDynamic.lean), [`accountable_safety_envelope_from`](FFGDynamic.lean) |
| For every epoch `e ≤ E`, `W_e ≤ 3 · stake_e(slashable) + 3 · churn`; with zero churn the fixed-set bound holds at every epoch and the fixed-set theorem is recovered. | [`accountable_safety_dynamic_epoch`](FFGDynamic.lean), [`accountable_safety_of_churn_eq_zero`](FFGDynamic.lean), [`accountable_safety_const`](FFGDynamic.lean) |
| The churn is at most the sum of the per-epoch `ℓ¹` changes of the validator set. | [`churn_le_pathChurn`](FFGDynamic.lean) |
| Concrete vote sets: conflicting finalized checkpoints with a slashable set of stake `2` out of `4`, once through E1 only and once through E2 only; an honest vote set with a finalized checkpoint and no slashable validator; a schedule with churn `2` on which the fixed-set bound fails at every epoch and the dynamic bound holds. | [`doubleVotes_slashable`](FFGExamples.lean), [`surroundVotes_slashable`](FFGExamples.lean), [`honestVotes_slashable`](FFGExamples.lean), [`Example.dyn_slashable`](FFGDynamicExamples.lean) |

## PoS-NSB: chain growth, chain quality and common prefix

`PoSNSB/` ports the Coq development [PoS-NSB](https://github.com/AU-COBRA/PoS-NSB) of
[TS21], a Nakamoto-style proof of stake in the line of Ouroboros [KRDO17], with the chain
properties of Garay, Kiayias and Leonardos [GKL15]. Each file names the Coq file it ports
and lists its departures from the Coq proofs. The theorems take forging freedom and
collision freedom of the broadcast blocks as hypotheses; the probability layer below
discharges them.

| Statement | Lean |
|---|---|
| The protocol and execution model: blocks, chains, block trees with an abstract chain-selection rule, honest baking and receiving, a network with adversarial delays `1` or `2`, the step relation, and the characteristic string of the lottery. | [`SingleStep`](PoSNSB/Model.lean), [`BigStep`](PoSNSB/Model.lean), [`TreeType.LongestChainRule`](PoSNSB/Model.lean), [`charString`](PoSNSB/Model.lean) |
| Every reachable state satisfies the invariant on the execution order, the local states and the message delays; the honest tree only grows. | [`reachable_inv`](PoSNSB/Steps.lean), [`monotone_honest_tree`](PoSNSB/Invariants.lean) |
| Under the longest-chain rule, the chain selected in a tree with more blocks at a later slot is at least as long. | [`subset_leq_time_leq_chains`](PoSNSB/TreeChain.lean) |
| Chain growth: between two states, the honest tree chain grows by at least the number of slots in between with an honest leader; the same for the chains of two honest parties. | [`chain_growth_gen`](PoSNSB/ChainGrowth.lean), [`chain_growth`](PoSNSB/ChainGrowth.lean), [`chain_growth_parties`](PoSNSB/ChainGrowth.lean) |
| Chain quality: if in every long enough interval the slots with an honest leader outnumber those with an adversarial leader by `w`, every fragment of an honest party's chain contains at least `w - 1` honest blocks. | [`chain_quality_gen`](PoSNSB/ChainQuality.lean), [`chain_quality`](PoSNSB/ChainQuality.lean) |
| Timed common prefix: the blocks of slot at most `k` of an honest chain form a suffix of every later honest chain, unless for some `t₁ ≤ k` and some later slot `t₂` the super slots (one honest leader) in `[t₁ + 1, t₂ - 1)` are at most twice the adversarial slots in `[t₁ + 1, t₂ + 1)`. | [`timed_common_prefix_gen`](PoSNSB/CommonPrefix.lean), [`timed_common_prefix`](PoSNSB/CommonPrefix.lean) |

## Probability layer

| Statement | Lean |
|---|---|
| Hoeffding tail for an interval: the scores of the slots of `[a, b)` sum to at most `(b - a) E[s] - Δ` with probability at most `exp (-2 Δ² / (b - a))`. | [`interval_tail`](PoSNSB/Prob/Slots.lean) |
| A lottery electing each slot leader independently violates the slot conditions of chain growth, chain quality and common prefix with probability at most `slotBound`, a union bound of such tails over the intervals. | [`prob_slotBad_le`](PoSNSB/Prob/Slots.lean) |
| Stake-weighted leader election per slot: a slot has a leader with probability `φ`, and it is honest (adversarial) with probability `φ` times the honest (corrupt) stake fraction. | [`kindLaw_stakeElect_honest`](PoSNSB/Prob/Slots.lean), [`kindLaw_stakeElect_adversarial`](PoSNSB/Prob/Slots.lean) |
| A random oracle queried adaptively has a collision among its first `q` queries with probability at most `q (q - 1) / 2 / \|Hash\|`. | [`prob_ROCollision_le`](PoSNSB/Prob/Hash.lean) |
| The real execution with signed blocks coincides with the ideal execution, which is forging free by construction, until the adversary forges. | [`sTrace_ideal_eq`](PoSNSB/Prob/Protocol.lean), [`forging_free_ideal`](PoSNSB/Prob/Protocol.lean) |
| Forging reduces to EUF-CMA: for every adversary `A` and party `i` the explicit forger `forger A i` gives `Pr[forge] ≤ ∑ᵢ eufAdv (forger A i)`. | [`forger`](PoSNSB/Prob/Reduction.lean), [`prob_forge_le`](PoSNSB/Prob/Reduction.lean) |
| Security of PoS-NSB: for every adversary, chain growth, chain quality and common prefix hold for the first `K` phases except with probability at most `slotBound + q (q - 1) / 2 / \|Hash\| + ∑ᵢ eufAdv (forger A i)`. | [`pos_nsb_security`](PoSNSB/Prob.lean) |
| One honest party elected on the first `1000` of `2000` slots with active-slot probability `3/4`: `slotBound ≤ 1/16`, and with `\|Hash\| = 4 ^ (K + 5)` the total bound is below `1`. | [`LotteryInstance.slotBound_le`](PoSNSB/ProbExamples.lean), [`LotteryInstance.instance_security`](PoSNSB/ProbExamples.lean), [`LotteryInstance.instance_bound_lt_one`](PoSNSB/ProbExamples.lean) |

## Finality layer

An execution of the underlying chain is seen through the chain each party selects at each
time. Common prefix, chain growth and chain quality [GKL15] are hypotheses on these
traces; the conclusions are the finality properties of Afgjort [DMM+20] and Enig [KNTT22].

| Statement | Lean |
|---|---|
| The rule "a block is final once it is `k` deep" is a finality layer on every trace with common prefix `k`, and its finalized chain inherits chain growth and chain quality. | [`kDeep_finalityLayer`](Finality.lean), [`kDeep_of_traceGuard`](Finality.lean) |
| FFG over a chain: if the slashable validators hold less than one third of the stake, the checkpoints finalized by all parties respect epochs, form a chain and agree. | [`ffg_positionRespecting`](Finality.lean), [`ffg_chainForming`](Finality.lean), [`ffg_agreement`](Finality.lean) |
| v-validity: a finalized checkpoint is an epoch-boundary checkpoint of the selected chains of honest validators of stake at least `(2/3 - β) W`, with `β` the adversarial share; with unslashable honest validators and `β < 1/3`, the honestly finalized checkpoints form a chain. | [`ffg_vValidity`](FinalityValidity.lean), [`ffg_vValidity_share`](FinalityValidity.lean), [`ffg_honestFinalized_chain_of_share`](FinalityValidity.lean), [`ffg_finalityValidity`](FinalityValidity.lean) |
| Δ-updatedness: after the global stabilization time, with honest validators holding two thirds of the stake and following the voting schedule, every honest party holds a finalized epoch-boundary checkpoint of its chain at most `3 E + σ + d + Δ` slots behind the current slot. | [`finality_updated`](FinalityUpdated.lean), [`finality_updated_start`](FinalityUpdated.lean), [`finality_updated_tip`](FinalityUpdated.lean) |
| On the real PoS-NSB execution, with the honest voting schedule and the tip condition as hypotheses on every seed, Δ-updatedness fails with probability at most the failure bound of `pos_nsb_security`. | [`finality_updated_prob`](FinalityUpdatedProb.lean) |
| Concrete traces satisfy every hypothesis of these theorems and finalize a block. | [`Examples.ffg_nonvacuous`](FinalityExamples.lean), [`Examples.ffgValidity_nonvacuous_adversary`](FinalityValidity.lean), [`Examples.updated_nonvacuous`](FinalityUpdated.lean) |

## Universally composable stack

Composable treatments of Nakamoto-style ledgers in Canetti's framework [Can01] are those
of Badertscher, Maurer, Tschudi and Zikas [BMTZ17] and Ouroboros Genesis [BGK+18], and
Matt, Nielsen and Thomsen [MNT22] treat the flooding networks that disseminate blocks
under delayed adaptive corruptions. The
functionalities here are transparent functionalities in the sense of Afgjort and Enig: the
adversary drives every state change subject to a guard on the trace, and a violated guard
explodes the functionality. The framework is in
[`UCTransparent.lean`](../Crypto/UCTransparent.lean), hybrid composition
(`Hybrid.realizes_compose`) in [`UCTransparentHybrid.lean`](../Crypto/UCTransparentHybrid.lean),
the global clock and Δ-bounded network of Afgjort in
[`UCClockNetwork.lean`](../Crypto/UCClockNetwork.lean), and concrete UC emulation
(`UCEmulatesCSim`) in [`UCConcrete.lean`](../Crypto/UCConcrete.lean). Corruption is
static.

| Statement | Lean |
|---|---|
| The functionalities `F_Tree` and `F_FinTree` of Enig; their guards are safety properties; the copy simulator realizes each with advantage at most the probability that the real trace violates the guard. | [`fTree`](UC/FTree.lean), [`finTree`](UC/FTree.lean), [`fTree_guard_prefix`](UC/FTree.lean), [`fTree_realizes`](UC/FTree.lean), [`finTree_realizes`](UC/FTree.lean) |
| PoS-NSB with signed blocks, run over the clock-and-network functionality, realizes `F_Tree` with chain growth, chain quality and common prefix as trace properties, for every adversary, with advantage at most the failure bound of `pos_nsb_security`. | [`chain_realizes`](UC/Chain.lean), [`chain_UCEmulatesCSim`](UC/Chain.lean) |
| The FFG gadget on tree positions: with `1 ≤ Δ` and adversarial stake below one third, its reported trace satisfies the guard of `F_FinTree` (chain-forming, agreement, propagation within `Δ` rounds, `1`-validity with stake validity), and a block final for an honest party lies on every later honest position. | [`finTreeGuard_of_run`](UC/FinalityGadget.lean), [`Run.validity`](UC/FinalityGadget.lean), [`FinalOnHonestPos.agree`](UC/FinalityGadget.lean) |
| FFG in the `F_Tree`-hybrid model realizes `F_FinTree` with advantage `0` when the adversarial validators hold less than one third of the stake. | [`ffg_realizes`](UC/Finality.lean), [`ffg_UCEmulatesCSim`](UC/Finality.lean) |
| The stack: FFG over PoS-NSB realizes `F_FinTree` with the bound of `chain_realizes`. | [`stack_realizes`](UC/Stack.lean), [`stack_UCEmulatesCSim`](UC/Stack.lean) |
| At the lottery parameters above, the stack realizes `F_FinTree` with bound `slotBound + q (q - 1) / 2 / M`, which is below `1` for `M = 4 ^ (K + 5)`. | [`LotteryInstance.instance_realizes`](UC/StackExamples.lean), [`LotteryInstance.instance_realizes_lt_one`](UC/StackExamples.lean) |

## Relation to Ethereum

The FFG part corresponds to Gasper [BHK+20]: justification and `k`-finalization by
supermajority links, the slashing conditions E1 and E2, accountable safety and plausible
liveness, and the dynamic validator set, in which a link is weighed by the validators
active at its source epoch. Condition E2 here requires the surrounded vote to have its
source below its target, so the surround condition of Gasper and of the beacon-chain
specification slashes at least the validators slashed here and accountable safety carries
over to it; the docstring of [`FFG.lean`](FFG.lean) compares the two in detail. The
beacon chain selects its available chain with the LMD-GHOST fork choice, and RLMD-GHOST
[DZ24] is a variant that combines dynamic availability with asynchrony resilience. Here
the chain-selection rule is a parameter of the model, and the chain properties are proved
for the longest-chain rule: the composed protocol has the structure of the ebb-and-flow
protocols of Neu, Tas and Tse [NTT21], with the longest chain of PoS-NSB as the available
ledger and the FFG-finalized checkpoints as its finalized prefix. This is the original
Casper FFG design, a finality overlay on an existing chain [BG17].

## References

- [BG17] Vitalik Buterin and Virgil Griffith. Casper the Friendly Finality Gadget. 2017. arXiv:1710.09437.
- [BGK+18] Christian Badertscher, Peter Gaži, Aggelos Kiayias, Alexander Russell and Vassilis Zikas. Ouroboros Genesis: Composable Proof-of-Stake Blockchains with Dynamic Availability. ACM CCS 2018. doi:10.1145/3243734.3243848. IACR ePrint 2018/378.
- [BHK+20] Vitalik Buterin, Diego Hernandez, Thor Kamphefner, Khiem Pham, Zhi Qiao, Danny Ryan, Juhyeok Sin, Ying Wang and Yan X Zhang. Combining GHOST and Casper. 2020. arXiv:2003.03052.
- [BMTZ17] Christian Badertscher, Ueli Maurer, Daniel Tschudi and Vassilis Zikas. Bitcoin as a Transaction Ledger: A Composable Treatment. CRYPTO 2017. doi:10.1007/978-3-319-63688-7_11. IACR ePrint 2017/149. Journal version: Journal of Cryptology, 2024, doi:10.1007/s00145-024-09493-7.
- [Can01] Ran Canetti. Universally Composable Security: A New Paradigm for Cryptographic Protocols. FOCS 2001. doi:10.1109/SFCS.2001.959888. IACR ePrint 2000/067. Journal version: Universally Composable Security, Journal of the ACM, 2020, doi:10.1145/3402457.
- [DMM+20] Thomas Dinsdale-Young, Bernardo Magri, Christian Matt, Jesper Buus Nielsen and Daniel Tschudi. Afgjort: A Partially Synchronous Finality Layer for Blockchains. SCN 2020. doi:10.1007/978-3-030-57990-6_2. IACR ePrint 2019/504.
- [DZ24] Francesco D'Amato and Luca Zanolini. Recent Latest Message Driven GHOST: Balancing Dynamic Availability With Asynchrony Resilience. IEEE CSF 2024. doi:10.1109/CSF61375.2024.00001. arXiv:2302.11326 (2023).
- [GKL15] Juan Garay, Aggelos Kiayias and Nikos Leonardos. The Bitcoin Backbone Protocol: Analysis and Applications. EUROCRYPT 2015. doi:10.1007/978-3-662-46803-6_10. IACR ePrint 2014/765.
- [KNTT22] Simon Holmgaard Kamp, Jesper Buus Nielsen, Søren Eller Thomsen and Daniel Tschudi. Enig: Player Replaceable Finality Layers with Optimal Validity. 2022. IACR ePrint 2022/201.
- [KRDO17] Aggelos Kiayias, Alexander Russell, Bernardo David and Roman Oliynykov. Ouroboros: A Provably Secure Proof-of-Stake Blockchain Protocol. CRYPTO 2017. doi:10.1007/978-3-319-63688-7_12. IACR ePrint 2016/889.
- [MNT22] Christian Matt, Jesper Buus Nielsen and Søren Eller Thomsen. Formalizing Delayed Adaptive Corruptions and the Security of Flooding Networks. CRYPTO 2022. doi:10.1007/978-3-031-15979-4_14. IACR ePrint 2022/010.
- [NTT21] Joachim Neu, Ertem Nusret Tas and David Tse. Ebb-and-Flow Protocols: A Resolution of the Availability-Finality Dilemma. IEEE S&P 2021. doi:10.1109/SP40001.2021.00045. arXiv:2009.04987.
- [TS21] Søren Eller Thomsen and Bas Spitters. Formalizing Nakamoto-Style Proof of Stake. IEEE CSF 2021. doi:10.1109/CSF51468.2021.00042. arXiv:2007.12105. IACR ePrint 2020/917.
