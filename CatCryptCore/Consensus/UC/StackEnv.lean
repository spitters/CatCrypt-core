/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.UC.ChainEnvRealize
public import CatCryptCore.Consensus.UC.Stack

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The stack driven by an environment: FFG over PoS-NSB realizes `F_FinTree`

The Casper FFG gadget of `CatCryptCore.Consensus.UC.Finality`, run over the PoS-NSB protocol
`chainRealE` of `CatCryptCore.Consensus.UC.ChainEnv`, which an environment drives with honest
transactions, phase entries with adversary indices and hash queries, realizes the finality
functionality `F_FinTree`. The bound against an environment `Z` of the stack is the failure
bound `posFailE … Z'` of `chain_realizesE` at the environment `Z'` of the PoS-NSB layer
obtained by running `Z` with the gadget (`Hybrid.reduceEnv`): the slot bound, the
collision-resistance advantage of the collision finder `collFinderE … Z'` and the EUF-CMA
advantages of the forgers `forgerE … Z' i`.

## The stacked protocol

`stackHybridE` is the gadget `ffgHybrid` over the interface of `chainRealE`: the tree events
are the environment inputs `EnvEv`, the outputs are the triples `EnvOut` of a clock round, a
tree view and a leakage, the gadget reads the view component, and the exploded output of
`F_Tree` is the exploded output `((0, initView), none)` of `chainFE`. `stackRealE` runs the
gadget with `chainRealE` as its subroutine.

## Main results

* `treeF_eq_chainFE`: the tree functionality of the gadget over `chainSimE` is `chainFE`.
* `chainSimE_step_out`: every step of `chainSimE` outputs the function `chainOutE` of its new
  state; the leakage of the output is the leakage stored in the state.
* `chainP_guard_initE`: the guard of `F_Tree` holds on the empty trace of `chainSimE`.
* `stack_realizesE` (headline): under the hypotheses of `chain_realizesE` and of
  `ffg_realizes`, `stackRealE` realizes `ideal (stackFE …) (stackSimE …)` with bound
  `posFailE … ((stackHybridE …).reduceEnv Z)` for every environment `Z`.
* `Instance.instance_realizesE`: every hypothesis holds for the one-party instance, and the
  collision term is `0` for every environment (`collFinderG_zero_advantage_eq_zero` of
  `CatCryptCore.Consensus.PoSNSB.Prob.Collision`): with `K = 0` the finder reads only the
  genesis block.
* `stack_boundE_of_rounds_eq_zero`: for the constant family of an adversary `A`, the
  transaction selection `P.txSel` and an environment without activations, the bound of
  `stack_realizesE` is the bound `posFail` of `stack_realizes`.
-/

namespace CatCryptCore.Consensus.UC.Stack

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent CatCrypt.NonUniform
open CatCryptCore.Consensus.UC.FTree CatCryptCore.Consensus.Finality FFG
open CatCryptCore.Consensus.UC.Chain CatCryptCore.Consensus.UC.FFGGadget
open CatCryptCore.Consensus.UC.ChainEnv
open PoSNSB Parameters BlockParameters Corruption Execution ClockNet
open CatCrypt.Crypto.Signatures CatCrypt.Crypto.Assumptions
open scoped ENNReal

section StackE

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} {PK SK Sig : Type}
  (P : Protocol Tx Hash np n Hz) (Sch : PSigScheme (Block Tx Hash (Fin np)) PK SK Sig)
  [Sch.Deterministic] {X S : Type} (F : AdvFamily X S Tx Hash np n Hz PK Sig) (x₀ : X)
  (dt : Slot → Fin np → Tx) (Tree : TreeFamily P)
  (H : HashScheme) (cd : H.Codec (BlockDom Tx Hash np Hz) Hash)

variable (Tx Hash np) in
/-- The exploded output of `chainFE`: round `0`, the initial view and no leakage. -/
def exCE : EnvOut Tx Hash np := ((0, initView), none)

/-- The view component of an output of the protocol driven by an environment. -/
def ovE (o : EnvOut Tx Hash np) : TreeView (Option (Fin np)) (Block Tx Hash (Fin np)) :=
  o.1.2

/-- The output of `chainSimE` as a function of its new state: the round of the last output of
the ideal clock and network (`0` once it has exploded or before its first output), the stored
view and the stored leakage. -/
def chainOutE (s : SimStE Tx Hash np n Hz PK SK X) : EnvOut Tx Hash np :=
  ((if s.2.2.2 then 0 else ((s.2.2.1.getLast?).map fun x => x.2.1.1).getD 0, stViewE s),
    s.1.2.2.2.2)

/-- **The stacked gadget driven by an environment**: the FFG gadget `ffgHybrid` over the
interface of `chainRealE`, reading the view component of the outputs, with the exploded output
of `chainFE` and the initial view of `chainSimE`. -/
noncomputable def stackHybridE (c : Cfg (Option (Fin np)) (Block Tx Hash (Fin np))) (K : ℕ)
    (μ : PMF (Option (Fin np))) (W Δ : ℕ)
    (exF : TreeView (Option (Fin np)) (Block Tx Hash (Fin np))) :
    Hybrid (GSt (Option (Fin np)) (Block Tx Hash (Fin np)))
      (EnvEv Tx Hash np Hz X × GAct (Option (Fin np)) (Block Tx Hash (Fin np)))
      (TreeView (Option (Fin np)) (Block Tx Hash (Fin np)))
      (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np) :=
  ffgHybrid c (exCE Tx Hash np) ovE exF
    (stViewE (chainSimE P Sch F x₀ dt Tree H cd K μ W Δ).init)

/-- **The stacked protocol driven by an environment**: the FFG gadget running with the
PoS-NSB protocol driven by the environment, which runs with the reference clock and network. -/
noncomputable def stackRealE (c : Cfg (Option (Fin np)) (Block Tx Hash (Fin np))) (K : ℕ)
    (μ : PMF (Option (Fin np))) (W Δ : ℕ)
    (exF : TreeView (Option (Fin np)) (Block Tx Hash (Fin np))) :=
  (stackHybridE P Sch F x₀ dt Tree H cd c K μ W Δ exF).withSub
    (chainRealE P Sch F x₀ dt Tree H cd K μ W Δ)

instance (c : Cfg (Option (Fin np)) (Block Tx Hash (Fin np))) (K : ℕ)
    (μ : PMF (Option (Fin np))) (W Δ : ℕ)
    (exF : TreeView (Option (Fin np)) (Block Tx Hash (Fin np))) :
    Lossless (stackRealE P Sch F x₀ dt Tree H cd c K μ W Δ exF) :=
  Hybrid.lossless_withSub _ _

/-- The tree functionality of the gadget over `chainSimE` is `chainFE`, when the block tree of
the gadget is the slot tree and its honest validators are the honest parties of `chainFE`. -/
theorem treeF_eq_chainFE (c : Cfg (Option (Fin np)) (Block Tx Hash (Fin np))) (K : ℕ)
    (μ : PMF (Option (Fin np))) (W Δ d w : ℕ) (ε : ℝ) (hT : c.T = slotTree P)
    (hH : ∀ o, o ∈ c.H ↔ honestP o) :
    treeF c (chainSimE P Sch F x₀ dt Tree H cd K μ W Δ) stViewE (chainP P (kindLaw μ) d w ε)
        (exCE Tx Hash np) =
      chainFE P Δ (kindLaw μ) d w ε := by
  have h : (fun o => o ∈ c.H) = honestP := funext fun o => propext (hH o)
  unfold treeF chainFE
  rw [hT, h]
  rfl

/-- Every step of `chainSimE` outputs `chainOutE` of its new state. -/
theorem chainSimE_step_out (K : ℕ) (μ : PMF (Option (Fin np))) (W Δ : ℕ)
    (s : SimStE Tx Hash np n Hz PK SK X) (e : EnvEv Tx Hash np Hz X) :
    ∃ C : SPComp (SimStE Tx Hash np n Hz PK SK X),
      (chainSimE P Sch F x₀ dt Tree H cd K μ W Δ).step s e =
        SPComp.bind C fun s' => SPComp.pure (s', chainOutE s') := by
  refine ⟨SPComp.bind ((chainHybridE P Sch F x₀ dt Tree K
      (sampleFrom (ofPMF (seedDist Sch H cd μ P.h0 W n))) (sampleFrom_ofPMF_noFail _)).pre s.1 e)
    fun a =>
    SPComp.bind ((clockNet (M := Unit) H₁ Δ).proto.step s.2.1 a.2) fun q =>
      SPComp.pure (a.1, q.1, s.2.2.1 ++ [(a.2, q.2, q.1)],
        s.2.2.2 || !(clockNetF (M := Unit) H₁ Δ).guard (s.2.2.1 ++ [(a.2, q.2, q.1)])), ?_⟩
  simp only [chainSimE, Hybrid.withSub, chainHybridE, ideal, SPComp.bind_assoc, SPComp.pure_bind]
  congr 1; funext a; congr 1; funext q
  simp only [chainOutE, stViewE, List.getLast?_concat, Option.map_some, Option.getD_some]
  split_ifs <;> rfl

/-- The tree trace of the empty trace of `chainSimE` is that of the empty trace of the
fixed-adversary simulator `chainSim`, for every adversary: the initial view at every time. -/
theorem traceOf_chainSimE_nil (A : Adversary Tx Hash np n Hz PK Sig) (K : ℕ)
    (μ : PMF (Option (Fin np))) (W Δ : ℕ) (honest : Option (Fin np) → Prop) :
    traceOf stViewE honest (chainSimE P Sch F x₀ dt Tree H cd K μ W Δ).init
        ([] : Trace (SimStE Tx Hash np n Hz PK SK X) (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) =
      traceOf stView honest (chainSim P Sch A Tree H cd K μ W Δ).init
        ([] : Trace (SimSt Tx Hash np n Hz PK SK) (Event Unit Unit) (ChainOut Tx Hash np)) := by
  simp only [traceOf, stAt, List.take_nil, List.getLast?_nil, Option.map_none, Option.getD_none]
  rfl

/-- The guard of `F_Tree` holds on the empty trace of `chainSimE`, for every block tree and
every honesty predicate, when the genesis block has slot `0`. -/
theorem chainP_guard_initE (K : ℕ) (μ : PMF (Option (Fin np))) (W Δ d w : ℕ) (ε : ℝ)
    (ν : PMF SlotKind) (T : BlockTree (Block Tx Hash (Fin np)))
    (honest : Option (Fin np) → Prop) (hGB : P.GB.sl = 0) :
    FTreeGuard T (chainP P ν d w ε) (traceOf stViewE honest
      (chainSimE P Sch F x₀ dt Tree H cd K μ W Δ).init
      ([] : Trace (SimStE Tx Hash np n Hz PK SK X) (EnvEv Tx Hash np Hz X)
        (EnvOut Tx Hash np))) := by
  rw [traceOf_chainSimE_nil P Sch F x₀ dt Tree H cd (F.at (scriptOfD x₀ ([] : List (LogEvOf X Tx Hash np Hz)))) K μ W Δ honest]
  exact chainP_guard_init P Sch _ Tree H cd K μ W Δ d w ε ν T honest hGB

variable (μ : PMF (Option (Fin np))) (W K d w : ℕ) (ε : ℝ) (Δ : ℕ)
  (c : Cfg (Option (Fin np)) (Block Tx Hash (Fin np)))
  (exF : TreeView (Option (Fin np)) (Block Tx Hash (Fin np)))

/-- The finality functionality of the stack driven by an environment: `finF` over `chainSimE`,
with chain-growth window `d + 2` and pruning depth `d`. -/
noncomputable abbrev stackFE :=
  finF c (chainSimE P Sch F x₀ dt Tree H cd K μ W Δ) stViewE (chainP P (kindLaw μ) d w ε)
    (exCE Tx Hash np) ovE exF (d + 2) d

/-- The simulator of the stack driven by an environment: `ffgSim` over `chainSimE`. -/
noncomputable abbrev stackSimE :=
  ffgSim c (chainSimE P Sch F x₀ dt Tree H cd K μ W Δ) stViewE (chainP P (kindLaw μ) d w ε)
    (exCE Tx Hash np) ovE exF

/-- **FFG over PoS-NSB driven by an environment realizes `F_FinTree`.** Let the hypotheses of
`chain_realizesE` hold, with `P.GB.sl = 0` and `4 ≤ w` unless `K + 1 < d + 2`; let the gadget
parameters `c` use the slot tree (`hT`) and the slots of blocks (`hsl`), have as honest
validators the honest parties of `chainFE` (`hH`), and vote on the pruned positions
`slotCut Block.sl d` (`hcut`); let `1 ≤ c.Δ`, `1 ≤ c.E`, `c.v₀ ∈ c.H`, and let the schedule start
at round `c.start = 2 E + (d + 2) + d`; and let the adversarial validators hold less than a
third of the total stake. Then for every adversary family `F`, the FFG gadget running with the
PoS-NSB protocol driven by the environment, the reference clock and the reference network
(`stackRealE`) realizes the ideal world of `F_FinTree^P'` (`stackFE`) with the simulator
`stackSimE`: every environment `Z` has advantage at most `posFailE … Z'` at the environment
`Z' = (stackHybridE …).reduceEnv Z` of the PoS-NSB layer, the slot bound plus the
collision-resistance advantage against `H` of the explicit collision finder `collFinderE … Z'`
and the EUF-CMA advantages against `Sch` of the explicit forgers `forgerE … Z' i`. -/
theorem stack_realizesE (hP : ProtocolHyp P) (hTree : Tree.Longest)
    (hwd : w ≤ d) (hWn : W + d ≤ n) (hn : K + 2 ≤ n) (hHz : K + 1 ≤ Hz)
    (hε : 0 ≤ ε) (hγ : 2 * pA (kindLaw μ) ≤ pH (kindLaw μ))
    (hw : (w : ℝ) ≤ d * (pH (kindLaw μ) - pA (kindLaw μ)))
    (h3 : (3 : ℝ) ≤ d * (pH (kindLaw μ) - 2 * pA (kindLaw μ)))
    (hGB : P.GB.sl = 0) (hw4 : K + 1 < d + 2 ∨ 4 ≤ w)
    (hT : c.T = slotTree P) (hsl : c.slot = Block.sl) (hH : ∀ o, o ∈ c.H ↔ honestP o)
    (hcut : c.cut = slotCut Block.sl d) (hΔ : 1 ≤ c.Δ) (hE : 1 ≤ c.E) (hv₀ : c.v₀ ∈ c.H)
    (hstart : c.start = 2 * c.E + (d + 2) + d)
    (hA : 3 * stake c.w (Finset.univ \ c.H) < totalStake c.w) :
    RealizesBound (stackRealE P Sch F x₀ dt Tree H cd c K μ W Δ exF)
      (ideal (stackFE P Sch F x₀ dt Tree H cd μ W K d w ε Δ c exF)
        (stackSimE P Sch F x₀ dt Tree H cd μ W K d w ε Δ c exF))
      (fun _ Z => posFailE P Sch F x₀ dt Tree H cd μ W K Δ d w ε
        ((stackHybridE P Sch F x₀ dt Tree H cd c K μ W Δ exF).reduceEnv Z)) := by
  have hF := treeF_eq_chainFE P Sch F x₀ dt Tree H cd c K μ W Δ d w ε hT hH
  have h₂ := chain_realizesE P Sch F x₀ dt Tree H cd hP hTree μ W K d w ε Δ hwd hWn hn hHz hε
    hγ hw h3 hGB hw4
  rw [← hF] at h₂
  have hset : ∀ X, FTreeGuard c.T (chainP P (kindLaw μ) d w ε) X → Settled c.cut X :=
    fun X hX => by rw [hcut]; exact settled_of_chainGuard P (kindLaw μ) d w ε c.T X hX
  have hLive : ∀ X, FTreeGuard c.T (chainP P (kindLaw μ) d w ε) X → LiveHyp c (d + 2) X :=
    fun X hX => by
      have h := hX.2.1 (fun X => X.LiveTrace (slotTree P) Block.sl (d + 2)) (by simp [chainP])
      show X.LiveTrace c.T c.slot (d + 2)
      rw [hT, hsl]
      exact h
  have hcut' : ∀ v p, c.cut v p = (v.pos p).filter fun b => decide (c.slot b + d ≤ v.round) :=
    fun v p => by rw [hcut, hsl]; rfl
  have h₁ := ffg_realizes
    (Hybrid.withSub_noFail _ _ (Hybrid.ideal_noFail _ _ fun _ _ => SPComp.pure_noFail _))
    chainOutE (fun _ => rfl)
    (chainP_guard_initE P Sch F x₀ dt Tree H cd K μ W Δ d w ε (kindLaw μ) _ _ hGB)
    (by simp only [chainP, List.mem_cons, List.not_mem_nil, or_false]
        rintro φ (rfl | rfl | rfl | rfl | rfl)
        · exact fun X f h => h
        · exact fun X f h => h
        · exact fun X f h => h
        · exact fun X f h => h
        · exact posOnly_liveTrace _ _ _)
    hset hΔ hA hLive hcut' hE hv₀ hstart (chainSimE_step_out P Sch F x₀ dt Tree H cd K μ W Δ)
    (ov := ovE) (exF := exF) (exT := exCE Tx Hash np) (vwT := stViewE)
  exact (RealizesBound.compose _ h₁ h₂).mono fun _ _ => (add_zero _).le

/-- **The zero-round environment recovers the fixed-adversary bound.** For the constant family
of an adversary `A`, the transaction selection `P.txSel` and an environment `Z` of the stack
without activations, the bound of `stack_realizesE` at `Z` is the bound `posFail` of
`stack_realizes` for `A`. -/
theorem stack_boundE_of_rounds_eq_zero (A : Adversary Tx Hash np n Hz PK Sig) {ζ : Type}
    (Z : Env (Strat ζ (EnvEv Tx Hash np Hz X × GAct (Option (Fin np)) (Block Tx Hash (Fin np)))
      (TreeView (Option (Fin np)) (Block Tx Hash (Fin np)))) ζ) (hZ : Z.input.rounds = 0) :
    posFailE P Sch (AdvFamily.const A) x₀ P.txSel Tree H cd μ W K Δ d w ε
        ((stackHybridE P Sch (AdvFamily.const A) x₀ P.txSel Tree H cd c K μ W Δ exF).reduceEnv
          Z) =
      posFail P Sch A H cd μ W K d w ε := by
  set Z' := (stackHybridE P Sch (AdvFamily.const A) x₀ P.txSel Tree H cd c K μ W Δ exF).reduceEnv Z
  have hZ' : Z'.input.rounds = 0 := hZ
  unfold posFailE posFail
  rw [← collFinder_adv_eq_env P Sch x₀ Tree H cd A μ W K Δ Z' hZ']
  simp only [← forger_adv_eq_env P Sch x₀ Tree H cd A μ W K Δ Z' hZ']

end StackE

/-! ## The one-party instance -/

namespace Instance

open PoSNSB.Instance

attribute [local instance] PoSNSB.Instance.corruption

variable {X S : Type} (F : AdvFamily X S Unit Unit 1 4 1 Unit Unit) (x₀ : X)
  (dt : Slot → Fin 1 → Unit)

/-- **Non-vacuity of the hypotheses.** For the one-party instance of `instance_realizes`
(`W = 1`, `K = 0`, `d = 3`, `w = 1`, `ε = 0`, the random function `H` with the identity codec
`cd`, delay bound `2`) and the gadget parameters `cfg`, every hypothesis of `stack_realizesE`
holds for every adversary family `F`, so FFG over PoS-NSB driven by an environment realizes
`F_FinTree` with bound `slotBound ν 4 3 1 0 + ∑ᵢ eufcmaAdvantage (forgerE … Z' i)` at the
reduced environment `Z'`: the collision term is `0` for every environment, since with `K = 0`
the collision finder reads only the genesis block. -/
theorem instance_realizesE :
    RealizesBound (stackRealE P Sch F x₀ dt Tree H cd cfg 0 μ 1 2 initView)
      (ideal (stackFE P Sch F x₀ dt Tree H cd μ 1 0 3 1 0 2 cfg initView)
        (stackSimE P Sch F x₀ dt Tree H cd μ 1 0 3 1 0 2 cfg initView))
      (fun _ Z => slotBound ν 4 3 1 0 +
        ∑ i : Fin 1, eufcmaAdvantage Sch.toSigScheme (toEUFAdversary
          (forgerE P Sch F x₀ dt Tree H cd μ 1 0 2
            ((stackHybridE P Sch F x₀ dt Tree H cd cfg 0 μ 1 2 initView).reduceEnv Z) i))) := by
  obtain ⟨hP, hT, hwd, hWn, hn, hHz, hε, hγ, hw, h3⟩ := instance_hyps
  refine (stack_realizesE P Sch F x₀ dt Tree H cd μ 1 0 3 1 0 2 cfg initView hP hT hwd hWn hn
    hHz hε hγ hw h3 rfl (Or.inl (by norm_num)) rfl rfl cfg_honest rfl le_rfl le_rfl
    (by simp [cfg]) rfl (by decide)).mono fun _ Z => le_of_eq ?_
  unfold posFailE collFinderE
  rw [collFinderG_zero_advantage_eq_zero, add_zero]
  rfl

end Instance

end CatCryptCore.Consensus.UC.Stack
