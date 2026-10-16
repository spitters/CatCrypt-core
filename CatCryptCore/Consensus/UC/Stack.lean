/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.UC.Chain
public import CatCryptCore.Consensus.UC.Finality

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The stack: FFG over PoS-NSB realizes `F_FinTree`

Row C4c (STACK) of the Ethereum consensus plan. The Casper FFG gadget of row C4b, run over the
PoS-NSB protocol of row C4a in place of the ideal tree functionality `F_Tree`, realizes the
finality functionality `F_FinTree` with the advantage bound of C4a:
`slotBound ν n d w ε + q (q - 1) / 2 / |Hash| + ∑ᵢ eufAdv (forger P A ν W K i)`.

## The stacked protocol

`stackHybrid` is the gadget `ffgHybrid` of C4b instantiated with the interface of C4a: the tree
events are the events `Event Unit Unit` of the PoS-NSB hybrid protocol, its outputs are the
pairs `ChainOut` of a clock round and a tree view, the gadget reads the view component
(`Prod.snd`), and the exploded output of `F_Tree` is the exploded output `(0, initView)` of
`chainF`. `stackReal` runs this gadget with the real PoS-NSB protocol `chainReal` (itself
running with the reference clock and network) as its subroutine.

## The interface between the two layers

The two layers meet at the ideal world `ideal (chainF …) (chainSim …)` of C4a. The tree
functionality `treeF` of C4b, instantiated with the simulator `chainSim`, the view `vwC`, the
properties `chainP` and the exploded output `exC`, is `chainF` provided that the block tree of
the gadget parameters is the slot tree of C4a (`hT`) and that the honest validators of the
gadget are the honest parties of C4a (`hH`) (`treeF_eq_chainF`). No further adapter is needed:
the gadget reads the view of every output of `chainSim` from the output itself
(`chainSim_step_out`, with `ov = Prod.snd`), and the guard of `chainF` holds on the empty trace
(`chainP_guard_init`).

## Main results

* `treeF_eq_chainF`: the tree functionality of the gadget is `chainF`.
* `chainSim_step_out`: every step of `chainSim` outputs a function `chainOut` of its new state.
* `chainP_guard_init`: the guard of `F_Tree` holds on the empty trace of `chainSim`.
* `stack_realizes` (headline): under the hypotheses of `chain_realizes` and of `ffg_realizes`
  together with `hT` and `hH`, `stackReal` realizes `ideal (finF …) (ffgSim …)`, with bound the
  C4a bound.
* `stack_UCEmulatesCSim`: the same in the form `UCConcrete.UCEmulatesCSim`.
* `Instance.instance_realizes`: every hypothesis holds for the one-party instance of D2 with
  one honest validator.

## Modelling choices

* The composition is `Hybrid.realizes_compose` of `CatCryptCore.Crypto.UCTransparentHybrid`
  with the gadget as hybrid protocol, the real PoS-NSB protocol as the substituted system and
  the ideal world of `chainF` as the system it realizes. The bound of the gadget layer is `0`,
  so the bound of the stack is the C4a bound.
* The simulator is `ffgSim`, the gadget running with the ideal world of `chainF` and the
  PoS-NSB simulator `chainSim`. It is the copy simulator of the composed hybrid world, so the
  theorem carries the tag of composition plumbing.
-/

namespace CatCryptCore.Consensus.UC.Stack

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent CatCrypt.NonUniform
open CatCryptCore.Consensus.UC.FTree CatCryptCore.Consensus.Finality FFG
open CatCryptCore.Consensus.UC.Chain CatCryptCore.Consensus.UC.FFGGadget
open PoSNSB Parameters BlockParameters Corruption Execution ClockNet
open scoped ENNReal

section Stack

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] [Fintype Tx] [Fintype Hash]
  [Nonempty Hash] {np : ℕ} [Corruption (Fin np)] {n Hz : ℕ}
  {Sch : SigScheme (Block Tx Hash (Fin np))}
  (P : Protocol Tx Hash np n Hz) (A : Adversary Tx Hash np n Hz Sch) (Tree : TreeFamily P)

/-- The tree view of a state of the PoS-NSB simulator: the view of its protocol component. -/
def vwC (K : ℕ) (s : SimSt Tx Hash np n Hz Sch) :
    TreeView (Option (Fin np)) (Block Tx Hash (Fin np)) :=
  pView P A Tree K s.1

variable (Tx Hash np) in
/-- The exploded output of `chainF`: round `0` and the initial view. -/
def exC : ChainOut Tx Hash np := (0, initView)

/-- The output of the PoS-NSB simulator as a function of its new state: the round of the last
output of the ideal clock and network (`0` once it has exploded or before its first output),
and the view of the protocol component. -/
def chainOut (K : ℕ) (s : SimSt Tx Hash np n Hz Sch) : ChainOut Tx Hash np :=
  (if s.2.2.2 then 0 else ((s.2.2.1.getLast?).map fun x => x.2.1.1).getD 0, vwC P A Tree K s)

/-- **The stacked gadget**: the FFG gadget of C4b over the interface of C4a, reading the view
component of the outputs, with the exploded output of `chainF` and the initial view of the
PoS-NSB simulator. -/
noncomputable def stackHybrid (c : Cfg (Option (Fin np)) (Block Tx Hash (Fin np))) (K : ℕ)
    (ν : PMF SlotKind) (W Δ : ℕ) (exF : TreeView (Option (Fin np)) (Block Tx Hash (Fin np))) :
    Hybrid (GSt (Option (Fin np)) (Block Tx Hash (Fin np)))
      (Event Unit Unit × GAct (Option (Fin np)) (Block Tx Hash (Fin np)))
      (TreeView (Option (Fin np)) (Block Tx Hash (Fin np)))
      (Event Unit Unit) (ChainOut Tx Hash np) :=
  ffgHybrid c (exC Tx Hash np) Prod.snd exF (vwC P A Tree K (chainSim P A Tree K ν W Δ).init)

/-- **The stacked protocol**: the FFG gadget running with the real PoS-NSB protocol, which
runs with the reference clock and network. -/
noncomputable def stackReal (c : Cfg (Option (Fin np)) (Block Tx Hash (Fin np))) (K : ℕ)
    (ν : PMF SlotKind) (W Δ : ℕ) (exF : TreeView (Option (Fin np)) (Block Tx Hash (Fin np))) :=
  (stackHybrid P A Tree c K ν W Δ exF).withSub (chainReal P A Tree K ν W Δ)

/-- The tree functionality of the gadget over the PoS-NSB simulator is `chainF`, when the block
tree of the gadget is the slot tree and its honest validators are the honest parties of C4a. -/
theorem treeF_eq_chainF (c : Cfg (Option (Fin np)) (Block Tx Hash (Fin np))) (K : ℕ)
    (ν : PMF SlotKind) (W Δ d w : ℕ) (ε : ℝ) (hT : c.T = slotTree P)
    (hH : ∀ o, o ∈ c.H ↔ honestP o) :
    treeF c (chainSim P A Tree K ν W Δ) (vwC P A Tree K) (chainP ν d w ε) (exC Tx Hash np) =
      chainF P A Tree K ν W Δ d w ε := by
  have h : (fun o => o ∈ c.H) = honestP := funext fun o => propext (hH o)
  unfold treeF chainF
  rw [hT, h]
  rfl

/-- Every step of the PoS-NSB simulator outputs `chainOut` of its new state. -/
theorem chainSim_step_out (K : ℕ) (ν : PMF SlotKind) (W Δ : ℕ) (s : SimSt Tx Hash np n Hz Sch)
    (e : Event Unit Unit) :
    ∃ C : SPComp (SimSt Tx Hash np n Hz Sch), (chainSim P A Tree K ν W Δ).step s e =
      SPComp.bind C fun s' => SPComp.pure (s', chainOut P A Tree K s') := by
  refine ⟨SPComp.bind ((chainHybrid P A Tree K ν W).pre s.1 e) fun a =>
    SPComp.bind ((clockNet (M := Unit) H₁ Δ).proto.step s.2.1 a.2) fun q =>
      SPComp.pure (a.1, q.1, s.2.2.1 ++ [(a.2, q.2, q.1)],
        s.2.2.2 || !(clockNetF (M := Unit) H₁ Δ).guard (s.2.2.1 ++ [(a.2, q.2, q.1)])), ?_⟩
  simp only [chainSim, Hybrid.withSub, chainHybrid, ideal, SPComp.bind_assoc, SPComp.pure_bind]
  congr 1; funext a; congr 1; funext q
  simp only [chainOut, vwC, List.getLast?_concat, Option.map_some, Option.getD_some]
  split_ifs <;> rfl

/-- The guard of `F_Tree` holds on the empty trace of the PoS-NSB simulator, for every block
tree and every honesty predicate: the initial view has round `0` and no blocks. -/
theorem chainP_guard_init (K : ℕ) (ν : PMF SlotKind) (W Δ d w : ℕ) (ε : ℝ)
    (T : BlockTree (Block Tx Hash (Fin np))) (honest : Option (Fin np) → Prop) :
    FTreeGuard T (chainP ν d w ε) (traceOf (vwC P A Tree K) honest
      (chainSim P A Tree K ν W Δ).init
      ([] : Trace (SimSt Tx Hash np n Hz Sch) (Event Unit Unit) (ChainOut Tx Hash np))) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp [traceOf, stAt_nil, vwC, chainSim, chainHybrid, Hybrid.withSub, pView, initView, chainP,
      TreeTrace.TreesGrow, TreeTrace.PositionsInTrees, TreeTrace.chains, ChainTrace.ChainsInTree,
      TreeTrace.RoundsMonotone, TreeTrace.Agreement, Finality.Agreement, TreeTrace.finalized,
      TreeTrace.finChains, kDeep, SlotChainGrowth, NewRound, SlotChainQuality, SlotCommonPrefix,
      PoSNSB.fragment]

variable (ν : PMF SlotKind) (W K d w : ℕ) (ε : ℝ) (Δ : ℕ)
  (c : Cfg (Option (Fin np)) (Block Tx Hash (Fin np)))
  (exF : TreeView (Option (Fin np)) (Block Tx Hash (Fin np)))

/-- The finality functionality of the stack: `finF` of C4b over the PoS-NSB simulator. -/
noncomputable abbrev stackF :=
  finF c (chainSim P A Tree K ν W Δ) (vwC P A Tree K) (chainP ν d w ε) (exC Tx Hash np) Prod.snd
    exF

/-- The simulator of the stack: `ffgSim` of C4b over the PoS-NSB simulator. -/
noncomputable abbrev stackSim :=
  ffgSim c (chainSim P A Tree K ν W Δ) (vwC P A Tree K) (chainP ν d w ε) (exC Tx Hash np)
    Prod.snd exF

/-- **FFG over PoS-NSB realizes `F_FinTree` (row C4c)** (composition plumbing). Let the
hypotheses of `chain_realizes` hold for `P`, `Tree`, `ν`, `W`, `K`, `d`, `w`, `ε`, `q`, `next`;
let the gadget parameters `c` use the slot tree (`hT`) and have as honest validators the honest
parties of C4a (`hH`); let the guard of `F_Tree` imply that the pruned positions `c.cut` are
settled (`hset`); let `1 ≤ c.Δ`; and let the adversarial validators hold less than a third of
the total stake. Then for every adversary `A`, the FFG gadget running with the real PoS-NSB
protocol, the reference clock and the reference network (`stackReal`) realizes the ideal world
of `F_FinTree^P'` (`stackF`, with `P' = finality-respecting positions :: chainP`) with the
simulator `stackSim`: every environment has advantage at most
`slotBound ν n d w ε + q (q - 1) / 2 / |Hash| + ∑ᵢ eufAdv (forger P A ν W K i)`. -/
theorem stack_realizes (hP : ProtocolHyp P) (hTree : Tree.Longest)
    (hd : 1 ≤ d) (hwd : w ≤ d) (hWn : W + d ≤ n) (hn : K + 2 ≤ n) (hHz : K + 1 ≤ Hz)
    (hε : 0 ≤ ε) (hγ : 2 * pA ν ≤ pH ν) (hw : (w : ℝ) ≤ d * (pH ν - pA ν))
    (h3 : (3 : ℝ) ≤ d * (pH ν - 2 * pA ν)) (q : ℕ)
    (next : (Fin n → SlotKind) → (Fin np → Sch.PK × Sch.SK) →
      Querier (BlockDom Tx Hash np Hz) Hash)
    (hRO : ∀ ω : Seed Tx Hash np n Hz Sch, ∀ j ≤ K, letI := ω.params P; letI := ω.bparams P;
      ∀ b ∈ block_hist_gb (sTrace P ω A false j), ∃ k < q,
        query (next ω.κ ω.ks) ω.f k = encB Hz b)
    (hT : c.T = slotTree P) (hH : ∀ o, o ∈ c.H ↔ honestP o)
    (hset : ∀ X, FTreeGuard c.T (chainP ν d w ε) X → Settled c.cut X) (hΔ : 1 ≤ c.Δ)
    (hA : 3 * stake c.w (Finset.univ \ c.H) < totalStake c.w) :
    Realizes (stackReal P A Tree c K ν W Δ exF)
      (ideal (stackF P A Tree ν W K d w ε Δ c exF) (stackSim P A Tree ν W K d w ε Δ c exF))
      (fun _ _ => slotBound ν n d w ε + ((q * (q - 1) / 2 : ℕ) : ℝ≥0∞) / Fintype.card Hash +
        ∑ i : Fin np, eufAdv (forger P A ν W K i)) := by
  have hF := treeF_eq_chainF P A Tree c K ν W Δ d w ε hT hH
  have h₂ := chain_realizes P A Tree hP hTree ν W K d w ε Δ hd hwd hWn hn hHz hε hγ hw h3 q next
    hRO
  rw [← hF] at h₂
  have h₁ := ffg_realizes (chainSim_noFail P A Tree K ν W Δ) (chainOut P A Tree K)
    (fun _ => rfl) (chainP_guard_init P A Tree K ν W Δ d w ε _ _)
    (by simp only [chainP, List.mem_cons, List.not_mem_nil, or_false]
        rintro φ (rfl | rfl | rfl) <;> exact fun X f h => h)
    hset hΔ hA (chainSim_step_out P A Tree K ν W Δ) (ov := Prod.snd) (exF := exF)
    (exT := exC Tx Hash np) (vwT := vwC P A Tree K)
  intro ζ Z
  exact ((Hybrid.realizes_compose _ _ _ _ _ _ h₁ h₂) ζ Z).trans_eq (add_zero _)

/-- **The stack as concrete UC emulation** (`UCConcrete.UCEmulatesCSim`) (composition
plumbing): under the hypotheses of `stack_realizes`, with the environment strategy as honest
input, the environment's final state as output, empty leakage and the identity simulator map,
the view maps of `stackReal` and of the ideal world of `stackF` are at distance at most the C4a
bound for every environment. -/
theorem stack_UCEmulatesCSim (hP : ProtocolHyp P) (hTree : Tree.Longest)
    (hd : 1 ≤ d) (hwd : w ≤ d) (hWn : W + d ≤ n) (hn : K + 2 ≤ n) (hHz : K + 1 ≤ Hz)
    (hε : 0 ≤ ε) (hγ : 2 * pA ν ≤ pH ν) (hw : (w : ℝ) ≤ d * (pH ν - pA ν))
    (h3 : (3 : ℝ) ≤ d * (pH ν - 2 * pA ν)) (q : ℕ)
    (next : (Fin n → SlotKind) → (Fin np → Sch.PK × Sch.SK) →
      Querier (BlockDom Tx Hash np Hz) Hash)
    (hRO : ∀ ω : Seed Tx Hash np n Hz Sch, ∀ j ≤ K, letI := ω.params P; letI := ω.bparams P;
      ∀ b ∈ block_hist_gb (sTrace P ω A false j), ∃ k < q,
        query (next ω.κ ω.ks) ω.f k = encB Hz b)
    (hT : c.T = slotTree P) (hH : ∀ o, o ∈ c.H ↔ honestP o)
    (hset : ∀ X, FTreeGuard c.T (chainP ν d w ε) X → Settled c.cut X) (hΔ : 1 ≤ c.Δ)
    (hA : 3 * stake c.w (Finset.univ \ c.H) < totalStake c.w) (ζ V : Type) :
    UCEmulatesCSim ⟨Strat ζ (Event Unit Unit × GAct (Option (Fin np)) (Block Tx Hash (Fin np)))
        (TreeView (Option (Fin np)) (Block Tx Hash (Fin np))), ζ, Empty, Empty, V⟩
      (fun s => SPComp.bind (view (stackReal P A Tree c K ν W Δ exF) s) fun z =>
        SPComp.pure (Sum.inl z))
      (fun s => SPComp.bind (view (ideal (stackF P A Tree ν W K d w ε Δ c exF)
        (stackSim P A Tree ν W K d w ε Δ c exF)) s) fun z => SPComp.pure (Sum.inl z)) id
      (fun _ _ => slotBound ν n d w ε + ((q * (q - 1) / 2 : ℕ) : ℝ≥0∞) / Fintype.card Hash +
        ∑ i : Fin np, eufAdv (forger P A ν W K i)) :=
  (stack_realizes P A Tree ν W K d w ε Δ c exF hP hTree hd hwd hWn hn hHz hε hγ hw h3 q next hRO
    hT hH hset hΔ hA).toUCEmulatesCSim ζ V

end Stack

/-! ## A concrete instance -/

namespace Instance

open PoSNSB.Instance

attribute [local instance] PoSNSB.Instance.corruption

/-- The gadget parameters of the instance: the slot tree, stake `1` for the party `some 0` and
`0` for the observer `none`, the honest validator `some 0`, slots of blocks, epochs of one slot,
the empty pruned position, delivery bound `1`. -/
noncomputable def cfg : Cfg (Option (Fin 1)) (Block Unit Unit (Fin 1)) :=
  ⟨slotTree P, fun o => o.elim 0 fun _ => 1, {some 0}, Block.sl, 1, fun _ _ => [], 1⟩

/-- **Non-vacuity.** For the one-party instance of D2 of `Chain.Instance.instance_realizes`
(`W = 1`, `K = 0`, `d = 3`, `w = 1`, `ε = 0`, `q = 1`, delay bound `2`) and the gadget
parameters `cfg` (one honest validator holding the whole stake), every hypothesis of
`stack_realizes` holds, so FFG over PoS-NSB realizes `F_FinTree` with bound
`slotBound ν 4 3 1 0 + 0 / 1 + eufAdv (forger P A ν 1 0 0)`. -/
theorem instance_realizes :
    Realizes (stackReal P A Tree cfg 0 ν 1 2 initView)
      (ideal (stackF P A Tree ν 1 0 3 1 0 2 cfg initView)
        (stackSim P A Tree ν 1 0 3 1 0 2 cfg initView))
      (fun _ _ => slotBound ν 4 3 1 0 + ((1 * (1 - 1) / 2 : ℕ) : ℝ≥0∞) / Fintype.card Unit +
        ∑ i : Fin 1, eufAdv (forger P A ν 1 0 i)) := by
  obtain ⟨hP, hT, hd, hwd, hWn, hn, hHz, hε, hγ, hw, h3, hRO⟩ := instance_hyps
  refine stack_realizes P A Tree ν 1 0 3 1 0 2 cfg initView hP hT hd hwd hWn hn hHz hε hγ hw h3 1
    next hRO rfl ?_ (fun _ _ _ _ _ _ _ _ _ => List.nil_suffix) le_rfl (by decide)
  rintro (_ | p)
  · simp [cfg, honestP]
  · simp [cfg, honestP, Fin.fin_one_eq_zero p]
    rfl

end Instance

end CatCryptCore.Consensus.UC.Stack
