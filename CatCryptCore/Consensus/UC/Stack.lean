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

The Casper FFG gadget of `CatCryptCore.Consensus.UC.Finality`, run over the PoS-NSB protocol of
`CatCryptCore.Consensus.UC.Chain` in place of the ideal tree functionality `F_Tree`, realizes
the finality functionality `F_FinTree` with the advantage bound `posFail P Sch A H cd μ W K d w ε`
of `chain_realizes`: the slot bound plus `CR_Search_Advantage H (collFinder …)` plus the
EUF-CMA advantages `eufcmaAdvantage Sch.toSigScheme (toEUFAdversary (forger … i))`.

## The stacked protocol

`stackHybrid` is the gadget `ffgHybrid` instantiated with the interface of `chainReal`: the
tree events are the events `Event Unit Unit` of the PoS-NSB hybrid protocol, its outputs are
the pairs `ChainOut` of a clock round and a tree view, the gadget reads the view component
(`Prod.snd`), and the exploded output of `F_Tree` is the exploded output `(0, initView)` of
`chainF`. `stackReal` runs this gadget with the real PoS-NSB protocol `chainReal` (itself
running with the reference clock and network) as its subroutine.

## The interface between the two layers

The two layers meet at the ideal world `ideal (chainF …) (chainSim …)`. The tree
functionality `treeF` of the gadget, instantiated with the simulator `chainSim`, the stored
view `stView`, the properties `chainP` and the exploded output `exC`, is `chainF` provided that the
block tree of the gadget parameters is the slot tree (`hT`) and that the honest validators of
the gadget are the honest parties of `chainF` (`hH`) (`treeF_eq_chainF`). The gadget reads the
view of every output of `chainSim` from the output itself (`chainSim_step_out`, with
`ov = Prod.snd`), and the guard of `chainF` holds on the empty trace (`chainP_guard_init`).

The gadget votes on the pruned positions `slotCut Block.sl d`: the blocks of a position at
least `d` slots older than the round. The guard of `chainF` implies that these pruned
positions are settled (`settled_of_chainGuard`): the common prefix property of `chainP`
compares them with every later nonempty honest position, and the persistence of nonempty
honest positions in `chainP` makes every later honest position nonempty.

## Main results

* `settled_slotCut`, `settled_of_chainGuard`: slot common prefix and persistence of nonempty
  positions make the pruned positions `slotCut sl d` settled.
* `treeF_eq_chainF`: the tree functionality of the gadget is `chainF`.
* `chainSim_step_out`: every step of `chainSim` outputs a function `chainOut` of its new state.
* `chainP_guard_init`: the guard of `F_Tree` holds on the empty trace of `chainSim`.
* `stack_realizes` (headline): under the hypotheses of `chain_realizes` and of `ffg_realizes`,
  with `hT`, `hH` and the pruning `c.cut = slotCut Block.sl d`, `stackReal` realizes
  `ideal (finF …) (ffgSim …)`, with bound the bound of `chain_realizes`. The guard of `finF`
  contains `FinalOnHonestPos`: a block final for an honest party lies on every later honest
  position, so any two final blocks lie on one chain selected by an honest party
  (`FinalOnHonestPos.agree`).
* `stack_UCEmulatesCSim`: the same in the form `UCConcrete.UCEmulatesCSim`.
* `Instance.instance_realizes`: every hypothesis holds for the one-party instance
  `PoSNSB.Instance` with one honest validator.
* `Instance.run_finalizes`: a run of the gadget of the instance over views admitted by the
  guard of `chainF` finalizes the block of slot `1`, and its reported trace satisfies the guard
  of `finF`.

## Modelling choices

* The composition is `Hybrid.realizes_compose` of `CatCryptCore.Crypto.UCTransparentHybrid`
  with the gadget as hybrid protocol, the real PoS-NSB protocol as the substituted system and
  the ideal world of `chainF` as the system it realizes. The bound of the gadget layer is `0`,
  so the bound of the stack is the bound of `chain_realizes`.
* The simulator is `ffgSim`, the gadget running with the ideal world of `chainF` and the
  PoS-NSB simulator `chainSim`. It is the copy simulator of the composed hybrid world, so the
  theorem carries the tag of composition plumbing.
* The block tree of the guards is the slot order (`slotTree`), so `Agreement` of `F_FinTree`
  holds for every two blocks. Agreement of final blocks is carried by `FinalOnHonestPos`,
  which refers to the honest positions, the chains of the hash-linked trees of the parties.
-/

namespace CatCryptCore.Consensus.UC.Stack

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent CatCrypt.NonUniform
open CatCryptCore.Consensus.UC.FTree CatCryptCore.Consensus.Finality FFG
open CatCryptCore.Consensus.UC.Chain CatCryptCore.Consensus.UC.FFGGadget
open PoSNSB Parameters BlockParameters Corruption Execution ClockNet
open CatCrypt.Crypto.Signatures CatCrypt.Crypto.Assumptions
open scoped ENNReal

/-! ## Settled pruned positions -/

section Settled

variable {Party Blk : Type}

/-- The pruned position with slot map `sl` and depth `d`: the blocks of the position of `p`
whose slot is at least `d` before the round of the view. -/
def slotCut (sl : Blk → ℕ) (d : ℕ) (v : TreeView Party Blk) (p : Party) : List Blk :=
  (v.pos p).filter fun b => decide (sl b + d ≤ v.round)

/-- **Slot common prefix settles the pruned positions.** If the trace satisfies slot common
prefix with window `d` and nonempty honest positions persist, then the pruned positions
`slotCut sl d` are settled. -/
theorem settled_slotCut {sl : Blk → ℕ} {d : ℕ} {X : TreeTrace Party Blk}
    (hcp : SlotCommonPrefix sl d X) (hne : PosNonemptyPersists X) : Settled (slotCut sl d) X := by
  intro p q t t' hp hq htt
  by_cases hc : slotCut sl d (X.st t) p = []
  · rw [hc]; exact List.nil_suffix
  · obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ hc
    have hb' := List.mem_filter.1 hb
    have hd : d ≤ (X.st t).round := by have := of_decide_eq_true hb'.2; omega
    have e : slotCut sl d (X.st t) p =
        ((X.st t).pos p).filter fun b => decide (sl b ≤ (X.st t).round - d) := by
      refine List.filter_congr fun b _ => ?_
      simp only [decide_eq_decide]
      omega
    rw [e]
    exact hcp t t' _ p q htt (by omega) hp hq
      (hne p q t t' hp hq htt (List.ne_nil_of_mem hb'.1))

end Settled

section Stack

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} {PK SK Sig : Type}
  (P : Protocol Tx Hash np n Hz) (Sch : PSigScheme (Block Tx Hash (Fin np)) PK SK Sig)
  [Sch.Deterministic] (A : Adversary Tx Hash np n Hz PK Sig) (Tree : TreeFamily P)
  (H : HashScheme) (cd : H.Codec (BlockDom Tx Hash np Hz) Hash)

variable (Tx Hash np) in
/-- The exploded output of `chainF`: round `0` and the initial view. -/
def exC : ChainOut Tx Hash np := (0, initView)

/-- The output of the PoS-NSB simulator as a function of its new state: the round of the last
output of the ideal clock and network (`0` once it has exploded or before its first output),
and the view stored in the protocol component. -/
def chainOut (s : SimSt Tx Hash np n Hz PK SK) : ChainOut Tx Hash np :=
  (if s.2.2.2 then 0 else ((s.2.2.1.getLast?).map fun x => x.2.1.1).getD 0, stView s)

/-- **The stacked gadget**: the FFG gadget `ffgHybrid` over the interface of `chainReal`,
reading the view component of the outputs, with the exploded output of `chainF` and the
initial view of the PoS-NSB simulator. -/
noncomputable def stackHybrid (c : Cfg (Option (Fin np)) (Block Tx Hash (Fin np))) (K : ℕ)
    (μ : PMF (Option (Fin np))) (W Δ : ℕ)
    (exF : TreeView (Option (Fin np)) (Block Tx Hash (Fin np))) :
    Hybrid (GSt (Option (Fin np)) (Block Tx Hash (Fin np)))
      (Event Unit Unit × GAct (Option (Fin np)) (Block Tx Hash (Fin np)))
      (TreeView (Option (Fin np)) (Block Tx Hash (Fin np)))
      (Event Unit Unit) (ChainOut Tx Hash np) :=
  ffgHybrid c (exC Tx Hash np) Prod.snd exF (stView (chainSim P Sch A Tree H cd K μ W Δ).init)

/-- **The stacked protocol**: the FFG gadget running with the real PoS-NSB protocol, which
runs with the reference clock and network. -/
noncomputable def stackReal (c : Cfg (Option (Fin np)) (Block Tx Hash (Fin np))) (K : ℕ)
    (μ : PMF (Option (Fin np))) (W Δ : ℕ)
    (exF : TreeView (Option (Fin np)) (Block Tx Hash (Fin np))) :=
  (stackHybrid P Sch A Tree H cd c K μ W Δ exF).withSub (chainReal P Sch A Tree H cd K μ W Δ)

/-- The tree functionality of the gadget over the PoS-NSB simulator is `chainF`, when the block
tree of the gadget is the slot tree and its honest validators are the honest parties of `chainF`. -/
theorem treeF_eq_chainF (c : Cfg (Option (Fin np)) (Block Tx Hash (Fin np))) (K : ℕ)
    (μ : PMF (Option (Fin np))) (W Δ d w : ℕ) (ε : ℝ) (hT : c.T = slotTree P)
    (hH : ∀ o, o ∈ c.H ↔ honestP o) :
    treeF c (chainSim P Sch A Tree H cd K μ W Δ) stView (chainP (kindLaw μ) d w ε) (exC Tx Hash np) =
      chainF P Δ (kindLaw μ) d w ε := by
  have h : (fun o => o ∈ c.H) = honestP := funext fun o => propext (hH o)
  unfold treeF chainF
  rw [hT, h]
  rfl

/-- Every step of the PoS-NSB simulator outputs `chainOut` of its new state. -/
theorem chainSim_step_out (K : ℕ) (μ : PMF (Option (Fin np))) (W Δ : ℕ)
    (s : SimSt Tx Hash np n Hz PK SK) (e : Event Unit Unit) :
    ∃ C : SPComp (SimSt Tx Hash np n Hz PK SK), (chainSim P Sch A Tree H cd K μ W Δ).step s e =
      SPComp.bind C fun s' => SPComp.pure (s', chainOut s') := by
  refine ⟨SPComp.bind ((chainHybrid P Sch A Tree H cd K μ W).pre s.1 e) fun a =>
    SPComp.bind ((clockNet (M := Unit) H₁ Δ).proto.step s.2.1 a.2) fun q =>
      SPComp.pure (a.1, q.1, s.2.2.1 ++ [(a.2, q.2, q.1)],
        s.2.2.2 || !(clockNetF (M := Unit) H₁ Δ).guard (s.2.2.1 ++ [(a.2, q.2, q.1)])), ?_⟩
  simp only [chainSim, Hybrid.withSub, chainHybrid, ideal, SPComp.bind_assoc, SPComp.pure_bind]
  congr 1; funext a; congr 1; funext q
  simp only [chainOut, stView, List.getLast?_concat, Option.map_some, Option.getD_some]
  split_ifs <;> rfl

/-- The guard of `F_Tree` holds on the empty trace of the PoS-NSB simulator, for every block
tree and every honesty predicate: the initial view has round `0` and no blocks. -/
theorem chainP_guard_init (K : ℕ) (μ : PMF (Option (Fin np))) (W Δ d w : ℕ) (ε : ℝ)
    (ν : PMF SlotKind) (T : BlockTree (Block Tx Hash (Fin np)))
    (honest : Option (Fin np) → Prop) :
    FTreeGuard T (chainP ν d w ε) (traceOf stView honest
      (chainSim P Sch A Tree H cd K μ W Δ).init
      ([] : Trace (SimSt Tx Hash np n Hz PK SK) (Event Unit Unit) (ChainOut Tx Hash np))) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp [traceOf, stAt_nil, stView, chainSim, chainHybrid, Hybrid.withSub, initView, chainP,
      TreeTrace.TreesGrow, TreeTrace.PositionsInTrees, TreeTrace.chains, ChainTrace.ChainsInTree,
      TreeTrace.RoundsMonotone, TreeTrace.Agreement, Finality.Agreement, TreeTrace.finalized,
      TreeTrace.finChains, kDeep, SlotChainGrowth, NewRound, SlotChainQuality, SlotCommonPrefix,
      PoSNSB.fragment, PosNonemptyPersists]

omit [DecidableEq Tx] [DecidableEq Hash] in
/-- **The guard of `chainF` settles the pruned positions**: every tree trace that satisfies
the guard of `F_Tree^P` with `P = chainP` has settled pruned positions `slotCut Block.sl d`. -/
theorem settled_of_chainGuard (ν : PMF SlotKind) (d w : ℕ) (ε : ℝ)
    (T : BlockTree (Block Tx Hash (Fin np)))
    (X : TreeTrace (Option (Fin np)) (Block Tx Hash (Fin np)))
    (hX : FTreeGuard T (chainP ν d w ε) X) : Settled (slotCut Block.sl d) X :=
  settled_slotCut (hX.2.1 _ (by simp [chainP])) (hX.2.1 _ (by simp [chainP]))

variable (μ : PMF (Option (Fin np))) (W K d w : ℕ) (ε : ℝ) (Δ : ℕ)
  (c : Cfg (Option (Fin np)) (Block Tx Hash (Fin np)))
  (exF : TreeView (Option (Fin np)) (Block Tx Hash (Fin np)))

/-- The finality functionality of the stack: `finF` over the PoS-NSB simulator. -/
noncomputable abbrev stackF :=
  finF c (chainSim P Sch A Tree H cd K μ W Δ) stView (chainP (kindLaw μ) d w ε)
    (exC Tx Hash np) Prod.snd exF

/-- The simulator of the stack: `ffgSim` over the PoS-NSB simulator. -/
noncomputable abbrev stackSim :=
  ffgSim c (chainSim P Sch A Tree H cd K μ W Δ) stView (chainP (kindLaw μ) d w ε)
    (exC Tx Hash np) Prod.snd exF

/-- **FFG over PoS-NSB realizes `F_FinTree`** (composition plumbing). Let the hypotheses of
`chain_realizes` hold for `P`, `Sch`, `Tree`, `H`, `cd`, `μ`, `W`, `K`, `d`, `w`, `ε`; let the
gadget parameters `c` use the slot tree
(`hT`), have as honest validators the honest parties of `chainF` (`hH`), and vote on the
pruned positions `slotCut Block.sl d` (`hcut`); let `1 ≤ c.Δ`; and let the adversarial
validators hold less than a third of the total stake. Then for every adversary `A`, the FFG
gadget running with the real PoS-NSB protocol, the reference clock and the reference network
(`stackReal`) realizes the ideal world of `F_FinTree^P'` (`stackF`, with
`P' = finality-respecting positions :: FinalOnHonestPos :: chainP`) with the simulator
`stackSim`: every environment has advantage at most `posFail P Sch A H cd μ W K d w ε`, the
slot bound plus the collision-resistance advantage against `H` of the explicit collision finder
and the EUF-CMA advantages against `Sch` of the explicit forgers built from `A`. -/
theorem stack_realizes (hP : ProtocolHyp P) (hTree : Tree.Longest)
    (hwd : w ≤ d) (hWn : W + d ≤ n) (hn : K + 2 ≤ n) (hHz : K + 1 ≤ Hz)
    (hε : 0 ≤ ε) (hγ : 2 * pA (kindLaw μ) ≤ pH (kindLaw μ))
    (hw : (w : ℝ) ≤ d * (pH (kindLaw μ) - pA (kindLaw μ)))
    (h3 : (3 : ℝ) ≤ d * (pH (kindLaw μ) - 2 * pA (kindLaw μ)))
    (hT : c.T = slotTree P) (hH : ∀ o, o ∈ c.H ↔ honestP o)
    (hcut : c.cut = slotCut Block.sl d) (hΔ : 1 ≤ c.Δ)
    (hA : 3 * stake c.w (Finset.univ \ c.H) < totalStake c.w) :
    Realizes (stackReal P Sch A Tree H cd c K μ W Δ exF)
      (ideal (stackF P Sch A Tree H cd μ W K d w ε Δ c exF)
        (stackSim P Sch A Tree H cd μ W K d w ε Δ c exF))
      (fun _ _ => posFail P Sch A H cd μ W K d w ε) := by
  have hF := treeF_eq_chainF P Sch A Tree H cd c K μ W Δ d w ε hT hH
  have h₂ := chain_realizes P Sch A Tree H cd hP hTree μ W K d w ε Δ hwd hWn hn hHz hε hγ hw h3
  rw [← hF] at h₂
  have hset : ∀ X, FTreeGuard c.T (chainP (kindLaw μ) d w ε) X → Settled c.cut X :=
    fun X hX => by rw [hcut]; exact settled_of_chainGuard (kindLaw μ) d w ε c.T X hX
  have h₁ := ffg_realizes (chainSim_noFail P Sch A Tree H cd K μ W Δ) chainOut
    (fun _ => rfl) (chainP_guard_init P Sch A Tree H cd K μ W Δ d w ε (kindLaw μ) _ _)
    (by simp only [chainP, List.mem_cons, List.not_mem_nil, or_false]
        rintro φ (rfl | rfl | rfl | rfl) <;> exact fun X f h => h)
    hset hΔ hA (chainSim_step_out P Sch A Tree H cd K μ W Δ) (ov := Prod.snd) (exF := exF)
    (exT := exC Tx Hash np) (vwT := stView)
  intro ζ Z
  exact ((Hybrid.realizes_compose _ _ _ _ _ _ h₁ h₂) ζ Z).trans_eq (add_zero _)

/-- **The stack as concrete UC emulation** (`UCConcrete.UCEmulatesCSim`) (composition
plumbing): under the hypotheses of `stack_realizes`, with the environment strategy as honest
input, the environment's final state as output, empty leakage and the identity simulator map,
the view maps of `stackReal` and of the ideal world of `stackF` are at distance at most the
bound of `chain_realizes` for every environment. -/
theorem stack_UCEmulatesCSim (hP : ProtocolHyp P) (hTree : Tree.Longest)
    (hwd : w ≤ d) (hWn : W + d ≤ n) (hn : K + 2 ≤ n) (hHz : K + 1 ≤ Hz)
    (hε : 0 ≤ ε) (hγ : 2 * pA (kindLaw μ) ≤ pH (kindLaw μ))
    (hw : (w : ℝ) ≤ d * (pH (kindLaw μ) - pA (kindLaw μ)))
    (h3 : (3 : ℝ) ≤ d * (pH (kindLaw μ) - 2 * pA (kindLaw μ)))
    (hT : c.T = slotTree P) (hH : ∀ o, o ∈ c.H ↔ honestP o)
    (hcut : c.cut = slotCut Block.sl d) (hΔ : 1 ≤ c.Δ)
    (hA : 3 * stake c.w (Finset.univ \ c.H) < totalStake c.w) (ζ V : Type) :
    UCEmulatesCSim ⟨Strat ζ (Event Unit Unit × GAct (Option (Fin np)) (Block Tx Hash (Fin np)))
        (TreeView (Option (Fin np)) (Block Tx Hash (Fin np))), ζ, Empty, Empty, V⟩
      (fun s => SPComp.bind (view (stackReal P Sch A Tree H cd c K μ W Δ exF) s) fun z =>
        SPComp.pure (Sum.inl z))
      (fun s => SPComp.bind (view (ideal (stackF P Sch A Tree H cd μ W K d w ε Δ c exF)
        (stackSim P Sch A Tree H cd μ W K d w ε Δ c exF)) s) fun z =>
          SPComp.pure (Sum.inl z)) id
      (fun _ _ => posFail P Sch A H cd μ W K d w ε) :=
  (stack_realizes P Sch A Tree H cd μ W K d w ε Δ c exF hP hTree hwd hWn hn hHz hε hγ hw h3
    hT hH hcut hΔ hA).toUCEmulatesCSim ζ V

end Stack

/-! ## A concrete instance -/

namespace Instance

open PoSNSB.Instance

attribute [local instance] PoSNSB.Instance.corruption

/-- The gadget parameters of the instance: the slot tree, stake `1` for the party `some 0` and
`0` for the observer `none`, the honest validator `some 0`, slots of blocks, epochs of one slot,
the pruned positions `slotCut Block.sl 3`, delivery bound `1`. -/
noncomputable def cfg : Cfg (Option (Fin 1)) (Block Unit Unit (Fin 1)) :=
  ⟨slotTree P, fun o => o.elim 0 fun _ => 1, {some 0}, Block.sl, 1, slotCut Block.sl 3, 1⟩

theorem cfg_honest (o : Option (Fin 1)) : o ∈ cfg.H ↔ honestP o := by
  rcases o with _ | p
  · simp [cfg, honestP]
  · simp [cfg, honestP, Fin.fin_one_eq_zero p]
    rfl

/-- **Non-vacuity of the hypotheses** (composition plumbing). For the one-party instance of
`Chain.Instance.instance_realizes` (`W = 1`, `K = 0`, `d = 3`, `w = 1`, `ε = 0`, the random
function `H` with the identity codec `cd`, delay bound `2`) and the gadget parameters `cfg`
(one honest validator holding the whole stake, voting on `slotCut Block.sl 3`), every
hypothesis of `stack_realizes` holds, so FFG over PoS-NSB realizes `F_FinTree` with bound
`slotBound ν 4 3 1 0 + 0 / 1 + ∑ᵢ eufcmaAdvantage …`, the collision term bounded by
`Chain.Instance.collFinder_advantage_le`. -/
theorem instance_realizes :
    Realizes (stackReal P Sch A Tree H cd cfg 0 μ 1 2 initView)
      (ideal (stackF P Sch A Tree H cd μ 1 0 3 1 0 2 cfg initView)
        (stackSim P Sch A Tree H cd μ 1 0 3 1 0 2 cfg initView))
      (fun _ _ => slotBound ν 4 3 1 0 + ((1 * (1 - 1) / 2 : ℕ) : ℝ≥0∞) / Fintype.card Unit +
        ∑ i : Fin 1,
          eufcmaAdvantage Sch.toSigScheme (toEUFAdversary (forger Sch P A H cd μ 1 0 i))) := by
  obtain ⟨hP, hT, hwd, hWn, hn, hHz, hε, hγ, hw, h3⟩ := instance_hyps
  intro ζ Z
  exact (stack_realizes P Sch A Tree H cd μ 1 0 3 1 0 2 cfg initView hP hT hwd hWn hn hHz hε hγ
    hw h3 rfl cfg_honest rfl le_rfl (by decide) ζ Z).trans
    (add_le_add_left (add_le_add_right Chain.Instance.collFinder_advantage_le _) _)

/-! ### A run of the gadget of the instance that finalizes a block of slot `1` -/

/-- The block of slot `k` baked by the single party. -/
def bk (k : ℕ) : Block Unit Unit (Fin 1) := ⟨k, (), (), 0⟩

/-- The chain `[bk n, …, bk 0]`. -/
def bline : ℕ → List (Block Unit Unit (Fin 1))
  | 0 => [bk 0]
  | n + 1 => bk (n + 1) :: bline n

theorem bline_ne_nil (n : ℕ) : bline n ≠ [] := by
  cases n <;> simp [bline]

theorem length_bline (n : ℕ) : (bline n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [bline, ih]

theorem bline_suffix {n m : ℕ} (h : n ≤ m) : bline n <:+ bline m := by
  induction m, h using Nat.le_induction with
  | base => exact List.suffix_refl _
  | succ m _ ih => exact ih.trans (List.suffix_cons _ _)

theorem mem_bline {n : ℕ} {b : Block Unit Unit (Fin 1)} (h : b ∈ bline n) : b.sl ≤ n := by
  induction n with
  | zero => simp [bline] at h; subst h; rfl
  | succ n ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact le_rfl
    · exact (ih h).trans (Nat.le_succ n)

theorem bline_pairwise (n : ℕ) : (bline n).Pairwise fun b b' => b'.sl ≤ b.sl := by
  induction n with
  | zero => exact List.pairwise_singleton _ _
  | succ n ih =>
    exact List.pairwise_cons.2 ⟨fun b hb => (mem_bline hb).trans (Nat.le_succ n), ih⟩

theorem filter_bline (k n : ℕ) :
    (bline n).filter (fun b => decide (b.sl ≤ k)) = bline (min k n) := by
  induction n with
  | zero => simp [bline, bk]
  | succ n ih =>
    rw [bline, List.filter_cons, ih]
    by_cases h : n + 1 ≤ k
    · rw [if_pos (by simpa [bk] using h), min_eq_right h, min_eq_right (by omega : n ≤ k)]
      rfl
    · rw [if_neg (by simpa [bk] using h), min_eq_left (by omega : k ≤ n + 1),
        min_eq_left (by omega : k ≤ n)]

/-- The view at round `r`: every party has tree and position `bline r`, and no final blocks. -/
def sv (r : ℕ) : TreeView (Option (Fin 1)) (Block Unit Unit (Fin 1)) :=
  ⟨r, fun _ => bline r, fun _ => bline r, fun _ => []⟩

/-- **The views are admitted by `F_Tree`.** Every tree trace whose view at `t` is `sv (f t)`
for a monotone `f` satisfies the guard of `chainF` for the instance (`d = 3`, `w = 1`,
`ε = 0`). -/
theorem guard_sv (X : TreeTrace (Option (Fin 1)) (Block Unit Unit (Fin 1))) (f : ℕ → ℕ)
    (hf : Monotone f) (hX : ∀ t, X.st t = sv (f t)) :
    FTreeGuard (slotTree P) (chainP ν 3 1 0) X := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro p t t' _ h
    rw [hX, hX]
    exact (bline_suffix (hf h)).subset
  · intro p t _
    rw [hX]
    exact List.Subset.refl _
  · intro p t _
    show ((X.st t).pos p).Pairwise fun b b' => b'.sl ≤ b.sl
    rw [hX]
    exact bline_pairwise _
  · intro t t' h
    rw [hX, hX]
    exact hf h
  · simp only [chainP, List.mem_cons, List.not_mem_nil, or_false]
    rintro φ (rfl | rfl | rfl | rfl)
    · intro t₁ t₂ _ _ hd w' hw'
      rw [hX, hX] at hd hw' ⊢
      simp only [sv, length_bline] at hd hw' ⊢
      rw [pH_ν, sub_zero, one_mul] at hw'
      have h' : w' ≤ f t₂ - f t₁ := by exact_mod_cast hw'
      omega
    · intro _ _ _ _ _ _ _ _
      exact Nat.zero_le _
    · intro t₁ t₂ k p₁ p₂ ht _ _ _ _
      rw [hX, hX]
      show (bline (f t₁)).filter (fun b => decide (b.sl ≤ k)) <:+ bline (f t₂)
      rw [filter_bline]
      exact bline_suffix ((min_le_right _ _).trans (hf ht))
    · intro _ q _ t' _ _ _ _
      rw [hX]
      exact bline_ne_nil _
  · rintro p q t t' b b' i j _ _ ⟨C, hC, -⟩
    simp [TreeTrace.finChains, hX, sv] at hC

/-- The honest vote from the genesis checkpoint to the checkpoint `(bk 1, 1)`. -/
def x₁ : Vote (Option (Fin 1)) (Block Unit Unit (Fin 1)) := ⟨some 0, ⟨bk 0, 0⟩, ⟨bk 1, 1⟩⟩

/-- The honest vote from the checkpoint `(bk 1, 1)` to the checkpoint `(bk 2, 2)`. -/
def x₂ : Vote (Option (Fin 1)) (Block Unit Unit (Fin 1)) := ⟨some 0, ⟨bk 1, 1⟩, ⟨bk 2, 2⟩⟩

/-- The gadget state after the vote `x₁` at round `4`. -/
noncomputable def g₁ : GCore (Option (Fin 1)) (Block Unit Unit (Fin 1)) :=
  gstep cfg (ginit (sv 0)) (.hvote x₁) (sv 4)

/-- The gadget state after the vote `x₂` at round `5`. -/
noncomputable def g₂ : GCore (Option (Fin 1)) (Block Unit Unit (Fin 1)) :=
  gstep cfg g₁ (.hvote x₂) (sv 5)

/-- A run of the gadget of the instance: the views of rounds `0`, `4`, `5`, `6`; the honest
votes `x₁` at round `4` and `x₂` at round `5`; afterwards nothing changes. -/
noncomputable def runS : ℕ → GCore (Option (Fin 1)) (Block Unit Unit (Fin 1))
  | 0 => ginit (sv 0)
  | 1 => g₁
  | 2 => g₂
  | _ + 3 => gstep cfg g₂ .idle (sv 6)

/-- The rounds of the run. -/
def rd : ℕ → ℕ
  | 0 => 0
  | 1 => 4
  | 2 => 5
  | _ + 3 => 6

theorem rd_mono : Monotone rd := by
  intro a b h
  rcases a with _ | _ | _ | a <;> rcases b with _ | _ | _ | b <;> simp [rd] <;> omega

theorem runS_view (t : ℕ) : (runS t).view = sv (rd t) := by
  rcases t with _ | _ | _ | t
  · rfl
  · exact gstep_view _ _ _ _
  · exact gstep_view _ _ _ _
  · exact gstep_view _ _ _ _

theorem guard_runS : FTreeGuard (slotTree P) (chainP ν 3 1 0) (posTT cfg runS) :=
  guard_sv _ rd rd_mono runS_view

theorem runS_run : Run cfg runS where
  init_cast := rfl
  init_seen _ := rfl
  step t := by
    rcases t with _ | _ | _ | t
    · exact Or.inr ⟨.hvote x₁, sv 4, rfl⟩
    · exact Or.inr ⟨.hvote x₂, sv 5, rfl⟩
    · exact Or.inr ⟨.idle, sv 6, rfl⟩
    · exact Or.inl rfl
  rounds := guard_runS.1.2.2.2
  settled := settled_of_chainGuard ν 3 1 0 _ _ guard_runS

theorem honestOK_x₁ : HonestOK cfg (sv 4) ∅ x₁ := by
  refine ⟨by simp [cfg, x₁], by decide, by decide, ?_⟩
  simp [mem_slashable, DoubleVote, SurroundVote, x₁]

theorem honestOK_x₂ : HonestOK cfg (sv 5) {x₁} x₂ := by
  refine ⟨by simp [cfg, x₂], by decide, by decide, ?_⟩
  simp [mem_slashable, DoubleVote, SurroundVote, x₁, x₂]

theorem x₁_mem_cast : (x₁, 4) ∈ g₁.cast := by
  show (x₁, 4) ∈ (act cfg { ginit (sv 0) with view := sv 4 } (.hvote x₁)).cast
  simp only [act]
  split_ifs with h
  · exact Finset.mem_insert_self _ _
  · exact absurd (by simpa [GCore.votes, ginit] using honestOK_x₁) h

theorem x₂_mem_cast : (x₂, 5) ∈ g₂.cast := by
  have hv : g₁.votes = {x₁} := by
    show (act cfg { ginit (sv 0) with view := sv 4 } (.hvote x₁)).cast.image Prod.fst = {x₁}
    simp only [act]
    rw [if_pos (by simpa [GCore.votes, ginit] using honestOK_x₁)]
    simp [ginit]
  show (x₂, 5) ∈ (act cfg { g₁ with view := sv 5 } (.hvote x₂)).cast
  simp only [act]
  split_ifs with h
  · exact Finset.mem_insert_self _ _
  · exact absurd (show HonestOK cfg (sv 5) g₁.votes x₂ by rw [hv]; exact honestOK_x₂) h

/-- Both votes have been received by the honest party at time `3`. -/
theorem mem_seen {x : Vote (Option (Fin 1)) (Block Unit Unit (Fin 1))} {r : ℕ}
    (hx : (x, r) ∈ g₂.cast) (hr : r + 1 ≤ 6) : x ∈ (runS 3).seen (some 0) := by
  show x ∈ (gstep cfg g₂ .idle (sv 6)).seen (some 0)
  rw [gstep_seen]
  exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨(x, r), Finset.mem_filter.2 ⟨hx, hr⟩, rfl⟩)

theorem totalStake_cfg : totalStake cfg.w = 1 := rfl

/-- A vote set containing a vote of `some 0` for `s → t` has a supermajority link `s → t`, when
the epochs increase and the slots do not decrease. -/
theorem link_of_mem {S : Finset (Vote (Option (Fin 1)) (Block Unit Unit (Fin 1)))}
    {s t : Checkpoint (Block Unit Unit (Fin 1))} (hx : (⟨some 0, s, t⟩ : Vote _ _) ∈ S)
    (he : s.epoch < t.epoch) (hs : s.block.sl ≤ t.block.sl) :
    SupermajorityLink cfg.T cfg.w S s t := by
  refine ⟨he, hs, ?_⟩
  have hv : some 0 ∈ voters S s t := mem_voters.2 hx
  have := Finset.single_le_sum (f := cfg.w) (fun _ _ => Nat.zero_le _) hv
  rw [totalStake_cfg]
  change 1 ≤ stake cfg.w (voters S s t) at this
  omega

/-- **Non-vacuity of the conclusion.** The run `runS` of the gadget of the instance has views
admitted by the guard of `chainF`, its reported trace satisfies the guard of `F_FinTree^P'`
of the stack, and the block `bk 1` of slot `1`, distinct from the genesis block, is final for
the honest party at time `3`. -/
theorem run_finalizes :
    Run cfg runS ∧ FTreeGuard (slotTree P) (chainP ν 3 1 0) (posTT cfg runS) ∧
      FinTreeGuard cfg.T ((fun X => X.FinalityRespectingPos) :: FinalOnHonestPos ::
        chainP ν 3 1 0) cfg.Δ (suppF cfg) (finTT cfg runS) ∧
      bk 1 ≠ P.GB ∧ ∃ i, (finTT cfg runS).finalized 3 (some 0) (bk 1) i := by
  have hA : 3 * stake cfg.w (Finset.univ \ cfg.H) < totalStake cfg.w := by decide
  have hP : ∀ φ ∈ chainP (Tx := Unit) (Hash := Unit) (np := 1) ν 3 1 0, PosOnly φ := by
    simp only [chainP, List.mem_cons, List.not_mem_nil, or_false]
    rintro φ (rfl | rfl | rfl | rfl) <;> exact fun X f h => h
  refine ⟨runS_run, guard_runS, finTreeGuard_of_run runS_run le_rfl hA hP guard_runS.1
    guard_runS.2.1, by decide, ?_⟩
  set S := (runS 3).seen (some 0)
  have h₁ : x₁ ∈ S := mem_seen (runS_run.cast_mono (t := 1) (t' := 2) (by omega) x₁_mem_cast)
    (by omega)
  have h₂ : x₂ ∈ S := mem_seen x₂_mem_cast (by omega)
  have hJ : Justified cfg.T cfg.w S ⟨bk 1, 1⟩ :=
    Justified.link Justified.genesis (link_of_mem h₁ (by decide) (by decide))
  have hfin : Finalized cfg.T cfg.w S ⟨bk 1, 1⟩ :=
    ⟨hJ, ⟨bk 2, 2⟩, rfl, link_of_mem h₂ (by decide) (by decide)⟩
  have hmem : bk 1 ∈ finList cfg S :=
    mem_finList (by decide) hfin fun b' hb' =>
      runS_run.finalized_unique hA (Finalized.mono (runS_run.seen_subset 3 _) hfin)
        (Finalized.mono (runS_run.seen_subset 3 _) hb')
  obtain ⟨s, l, hsl⟩ := List.append_of_mem hmem
  refine ⟨l.length, l, ?_, rfl⟩
  show bk 1 :: l <:+ finList cfg S
  rw [hsl]
  exact List.suffix_append s _

end Instance

end CatCryptCore.Consensus.UC.Stack
