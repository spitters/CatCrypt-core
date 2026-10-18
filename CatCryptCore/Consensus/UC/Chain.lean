/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.UC.FTree
public import CatCryptCore.Consensus.PoSNSB.Prob
public import CatCryptCore.Consensus.FinalityUpdatedProb
public import CatCryptCore.Crypto.UCClockNetwork
public import CatCryptCore.NonUniform.UnaryRules

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# PoS-NSB realizes `F_Tree` in the clock-and-network hybrid model

The PoS-NSB protocol with signed blocks (`CatCryptCore.Consensus.PoSNSB.Prob`), run as a hybrid
protocol over the clock-and-network functionality of `CatCryptCore.Crypto.UCClockNetwork`,
realizes the tree functionality `F_Tree^P` of `CatCryptCore.Consensus.UC.FTree` whose trace
properties `P` are the chain growth, chain quality and common prefix properties of
`PoSNSB.pos_nsb_security`, the persistence of nonempty honest positions, and the properties of
the honest positions on which finality liveness rests (`TreeTrace.LiveTrace`). The distinguishing
advantage of every environment is at most the failure bound `posFail P Sch A H cd μ W K d w ε`
of `pos_nsb_security`: `slotBound (kindLaw μ) n d w ε` plus the collision-resistance advantage
`CR_Search_Advantage H (collFinder …)` plus the EUF-CMA advantages
`eufcmaAdvantage Sch.toSigScheme (toEUFAdversary (forger … i))`.

## The protocol

`chainHybrid P Sch A Tree H cd K μ W` is a hybrid protocol (`Hybrid`) with one call to the
clock-and-network functionality `clockNet H₁ Δ` per activation. Its state is an optional seed,
a phase counter and the view of the current phase. The first activation samples the seed `ω`
from `seedDist Sch H cd μ P.h0 W n` (the slot leaders, a hash function of the keyed family `H`
and the keys); every later activation runs one more phase of the real execution
`sTrace Sch P ω A false` and signals the end of the round to the clock exactly when the phase
is a `NextRound` step, so the clock round
follows the slot. Each activation stores the view of its phase in the state and outputs the
clock round and the stored view.

The view (`phaseView`) of a phase reports, for every party `some p`, its position: the chain its
local tree selects at the previous slot; for the observer party `none`, the honest tree chain
`honest_tree_chain`; the tree of a party is the set of blocks that have been on its position so
far; the round is the slot `t_now`; there are no final blocks. Phases after `K` are reported as
phase `K`, the horizon of the bound of `pos_nsb_security`.

## Main results

* `prBad_le_of_potential`: a bad-event bound by a potential that does not increase in
  expectation along the steps of a system and is at least `1` on bad states.
* `stable_slotChainGrowth`, `stable_slotChainQuality`, `stable_slotCommonPrefix`,
  `stable_posNonemptyPersists`, `FTree.stable_liveTrace`: the five trace properties are stable
  under truncation, so the
  guard is a safety property (`fTree_guard_prefix`) and explosion is permanent exactly as in
  `CatCryptCore.Consensus.UC.FTree`.
* `posAt_some_ne_nil`: the position of an initial party is nonempty at every phase.
* `guard_of_good`: when every honest party is an initial party, the genesis block has slot
  `0` and `4 ≤ w` (unless `K + 1 < d + 2`), on a seed on which chain growth, chain quality,
  common prefix and the tip condition hold (`Good`), the tree trace of every run prefix
  satisfies the guard of `F_Tree^P`; the liveness properties come from
  `Finality.seed_slotChainGrowth` and `Finality.seed_slotTip`.
* `guardFail_le`: the guard of `F_Tree^P` fails on the run of the hybrid world with probability
  at most the probability that `Good` fails under `seedDist`.
* `chain_realizes` (headline): for every adversary `A`, the protocol running with the reference
  clock and network realizes `ideal (chainF …) (chainSim …)`, with bound the failure bound of
  `pos_nsb_security`. It is `pos_nsb_security` in the form of a realization: the environment
  gives no inputs, the adversary `A` is the same in both worlds, the simulator stores the views
  and `chainF` reads them (`stView`), so `chainF` depends on neither `A` nor `Tree`, chain growth
  is that of the observer `none`, the views are constant after phase `K`, and the network of the
  clock-and-network functionality is not used.
  The statement is a `RealizesBound`, so the form `UCConcrete.UCEmulatesCSim` follows
  through `UCTransparent.UCFromRealizes` (`ucEmulatesCSim_of_UCFromRealizes`).
* `Instance.instance_realizes`: the hypotheses hold for the one-party instance
  `PoSNSB.Instance` with the random function, and the collision term is at most `0`
  (`Instance.collFinder_advantage_le`).

## Modelling choices

* The trace properties are stated on tree traces (`SlotChainGrowth`, `SlotChainQuality`,
  `SlotCommonPrefix`) with the vocabulary of `PoSNSB.Good`: slots of blocks, honest blocks, the
  `prune_time` of a chain. Chain growth is measured on the observer party from times that
  start a new round (`PoSNSB.Good` measures it from `Ready` states).
* `PosNonemptyPersists` holds because the honest parties are initial parties, whose positions
  are valid chains and so end in the genesis block; in the initial view `startView` every
  position is the genesis block.
* The guard of `F_Tree` must not depend on the seed. The ancestry relation of the block tree is
  therefore the slot order (`slotTree`): hash links depend on the hash function of the seed.
* The clock of `clockNet` drives the slots. The message delivery of PoS-NSB stays the internal
  buffer of the execution with adversarial delays `1` or `2`; no message is routed through the
  network of `clockNet`.
* The environment activates the protocol and observes its outputs; the adversary is the
  adversary `A` of the execution, which acts inside it. The simulator is the copy simulator of
  `CatCryptCore.Consensus.UC.FTree`: the protocol running with the ideal clock and network.
-/

namespace CatCryptCore.Consensus.UC.Chain

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent CatCrypt.NonUniform
open CatCryptCore.Consensus.UC.FTree CatCryptCore.Consensus.Finality FFG
open CatCrypt.Crypto.Signatures CatCrypt.Crypto.Assumptions
open scoped ENNReal

/-! ## A bad-event bound by a potential -/

section Potential

variable {τ ζ E O Ω : Type}

/-- If every continuation accepts with probability at most `c`, so does the bind. -/
theorem prTrue_bind_le_const {α : Type} (X : SPComp α) (K : α → SPComp Bool) (h₀ : Heap)
    (c : ℝ≥0∞) (hK : ∀ a h', prTrue (K a) h' ≤ c) : prTrue (SPComp.bind X K) h₀ ≤ c := by
  rw [prTrue_bind_eq_weighted]
  calc ∑' p, (X h₀ : PMF _) p * (match p with | some ⟨a, h'⟩ => prTrue (K a) h' | none => 0)
      ≤ ∑' p, (X h₀ : PMF _) p * c := by
        refine ENNReal.tsum_le_tsum fun p => ?_
        rcases p with _ | ⟨a, h'⟩
        · simp
        · exact mul_le_mul_right (hK a h') _
    _ = c := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Sampling from a `PMF` never fails. -/
theorem sampleFrom_ofPMF_noFail (μ : PMF Ω) : SPComp.NoFail (sampleFrom (ofPMF μ)) := by
  intro h
  simp only [sampleFrom_apply, SDistr.bind, PMF.bind_apply]
  refine ENNReal.tsum_eq_zero.2 fun o => ?_
  rcases o with _ | a
  · simp
  · simp [SDistr.pure, PMF.pure_apply]

/-- A bind after sampling from `μ` accepts with probability at most the `μ`-average of bounds
of the continuations. -/
theorem prTrue_bind_sampleFrom_le (μ : PMF Ω) (K : Ω → SPComp Bool) (h₀ : Heap)
    (b : Ω → ℝ≥0∞) (hK : ∀ ω, prTrue (K ω) h₀ ≤ b ω) :
    prTrue (SPComp.bind (sampleFrom (ofPMF μ)) K) h₀ ≤ ∑' ω, μ ω * b ω := by
  rw [prTrue_bind_sampleFrom]
  exact ENNReal.tsum_le_tsum fun ω => by rw [ofPMF_apply_some]; exact mul_le_mul_right (hK ω) _

open Classical in
/-- The `μ`-average of the indicator of the failure of `G` is the probability that `G`
fails. -/
theorem tsum_mul_ite_eq (μ : PMF Ω) (G : Ω → Prop) :
    ∑' ω, μ ω * (if G ω then 0 else 1) = μ.toOuterMeasure {ω | ¬G ω} := by
  rw [PMF.toOuterMeasure_apply]
  refine tsum_congr fun ω => ?_
  by_cases h : G ω <;> simp [h, Set.indicator]

/-- **Bad-event bound by a potential.** Let `Inv` be an invariant of the states of `S` and
`β` a potential such that `β` is at least `1` on invariant bad states, and every step from an
invariant state followed by a continuation that accepts with probability at most `β` of the
next state (on invariant next states) accepts with probability at most `β` of the current
state. Then every environment sets the bad flag with probability at most `β S.init`. -/
theorem prBad_le_of_potential (S : Sys τ E O) (bad : τ → Bool) (Inv : τ → Prop)
    (β : τ → ℝ≥0∞) (hinit : Inv S.init) (hbad : ∀ t, Inv t → bad t = true → 1 ≤ β t)
    (hstep : ∀ t e (K : τ × O → SPComp Bool) h, Inv t →
      (∀ p h', Inv p.1 → prTrue (K p) h' ≤ β p.1) → prTrue (SPComp.bind (S.step t e) K) h ≤ β t)
    (Z : Env (Strat ζ E O) ζ) : prBad S bad Z ≤ β S.init := by
  have key : ∀ n (z : ζ) (t : τ) (b : Bool) h, Inv t →
      prTrue (SPComp.bind (loop S bad Z.input n (z, t, b)) fun c => SPComp.pure c.2.2) h ≤
        if b then 1 else β t := by
    intro n
    induction n with
    | zero =>
      intro z t b h _
      simp only [loop, SPComp.pure_bind, prTrue_pure]
      cases b <;> simp
    | succ n ih =>
      intro z t b h ht
      cases b
      · simp only [loop, SPComp.bind_assoc, Bool.false_or, Bool.false_eq_true, if_false]
        refine prTrue_bind_le_const _ _ _ _ fun a h₁ => hstep _ _ _ _ ht fun p h₂ hp => ?_
        refine prTrue_bind_le_const _ _ _ _ fun z' h₃ => (ih _ _ _ _ hp).trans ?_
        cases hb : bad p.1
        · simp
        · simpa using hbad _ hp hb
      · simpa using prTrue_le_one _ _
  unfold prBad run
  refine (key _ _ _ _ _ hinit).trans ?_
  cases hb : bad S.init
  · simp
  · simpa using hbad _ hinit hb

end Potential

/-! ## Trace properties in the vocabulary of PoS-NSB -/

section Props

variable {Party Blk : Type}

/-- Time `t` starts a new round: the round at `t` is larger than the round one time step
before. -/
def NewRound (X : TreeTrace Party Blk) (t : ℕ) : Prop :=
  ∃ t₀, t = t₀ + 1 ∧ (X.st t₀).round < (X.st t).round

/-- **Chain growth** (`PoSNSB.CGGood`) of the position of the party `obs` with rate `ρ` and
window `d`: from a time `t₁` that starts a new round to a time `t₂ ≥ t₁` at least `d` rounds
later, the position grows by every `w'` with `w' ≤ ρ Δr`, where `Δr` is the number of rounds in
between. -/
def SlotChainGrowth (obs : Party) (ρ : ℝ) (d : ℕ) (X : TreeTrace Party Blk) : Prop :=
  ∀ t₁ t₂, t₁ ≤ t₂ → NewRound X t₁ → (X.st t₁).round + d ≤ (X.st t₂).round →
    ∀ w' : ℕ, (w' : ℝ) ≤ ρ * (((X.st t₂).round - (X.st t₁).round : ℕ) : ℝ) →
      ((X.st t₁).pos obs).length + w' ≤ ((X.st t₂).pos obs).length

/-- **Chain quality** (`PoSNSB.CQGood`) with slot map `sl`, honesty predicate `hb`, window `d`
and quality `w`: a fragment `b_j :: c ++ [b_i]` of the position of an honest party with
`sl b_i + 1 + d ≤ sl b_j` contains at least `w - 1` honest blocks. -/
def SlotChainQuality (sl : Blk → ℕ) (hb : Blk → Bool) (d w : ℕ) (X : TreeTrace Party Blk) :
    Prop :=
  ∀ t p, X.honest p → ∀ (bj bi : Blk) (c : List Blk),
    PoSNSB.fragment ([bj] ++ c ++ [bi]) ((X.st t).pos p) → sl bi + 1 + d ≤ sl bj →
      w - 1 ≤ (([bj] ++ c ++ [bi]).filter hb).length

/-- **Common prefix** (`PoSNSB.CPGood`) with slot map `sl` and window `d`: for honest parties
`p₁` at `t₁` and `p₂` at `t₂ ≥ t₁` with a nonempty position, and a slot `k` at least `d` slots
before the round at `t₁`, the blocks of slot at most `k` of the position of `p₁` form a suffix
of the position of `p₂`. -/
def SlotCommonPrefix (sl : Blk → ℕ) (d : ℕ) (X : TreeTrace Party Blk) : Prop :=
  ∀ t₁ t₂ (k : ℕ) p₁ p₂, t₁ ≤ t₂ → k + d ≤ (X.st t₁).round → X.honest p₁ → X.honest p₂ →
    (X.st t₂).pos p₂ ≠ [] →
      ((X.st t₁).pos p₁).filter (fun b => decide (sl b ≤ k)) <:+ (X.st t₂).pos p₂

/-- Nonempty positions persist: if an honest party has a nonempty position at `t`, then every
honest party has a nonempty position at every time `t' ≥ t`. -/
def PosNonemptyPersists (X : TreeTrace Party Blk) : Prop :=
  ∀ p q t t', X.honest p → X.honest q → t ≤ t' → (X.st t).pos p ≠ [] → (X.st t').pos q ≠ []

/-- A time that starts a new round in a truncated trace lies within the truncation. -/
theorem NewRound.le_of_clamp {X : TreeTrace Party Blk} {n t : ℕ} (h : NewRound (X.clamp n) t) :
    t ≤ n := by
  obtain ⟨t₀, rfl, hlt⟩ := h
  by_contra hc
  simp only [TreeTrace.clamp, min_eq_right (show n ≤ t₀ by omega),
    min_eq_right (show n ≤ t₀ + 1 by omega), lt_irrefl] at hlt

theorem stable_slotChainGrowth (obs : Party) (ρ : ℝ) (d : ℕ) :
    Stable (fun X : TreeTrace Party Blk => SlotChainGrowth obs ρ d X) := by
  intro X n h t₁ t₂ ht hnew hd w' hw'
  have h₁ : min t₁ n = t₁ := min_eq_left hnew.le_of_clamp
  obtain ⟨t₀, rfl, hlt⟩ := hnew
  simp only [TreeTrace.clamp, h₁] at hd hw' hlt ⊢
  refine h (t₀ + 1) (min t₂ n) (le_min ht (h₁ ▸ min_le_right _ _)) ⟨min t₀ n, ?_, hlt⟩ hd w' hw'
  have := h₁ ▸ min_le_right (t₀ + 1) n
  rw [min_eq_left (by omega)]

theorem stable_slotChainQuality (sl : Blk → ℕ) (hb : Blk → Bool) (d w : ℕ) :
    Stable (fun X : TreeTrace Party Blk => SlotChainQuality sl hb d w X) :=
  fun _ _ h _ p hp => h _ p hp

theorem stable_slotCommonPrefix (sl : Blk → ℕ) (d : ℕ) :
    Stable (fun X : TreeTrace Party Blk => SlotCommonPrefix sl d X) :=
  fun _ n h _ _ k p₁ p₂ ht => h _ _ k p₁ p₂ (min_le_min_right n ht)

theorem stable_posNonemptyPersists :
    Stable (fun X : TreeTrace Party Blk => PosNonemptyPersists X) :=
  fun _ n h p q _ _ hp hq ht => h p q _ _ hp hq (min_le_min_right n ht)

end Props

/-! ## Phases of the PoS-NSB execution -/

section Phase

open PoSNSB Parameters BlockParameters Corruption Execution

variable {Tx Hash Party AdvState : Type} [Parameters Party] [BlockParameters Tx Hash Party]
  [Execution Tx Hash Party AdvState] [Corruption Party] [DecidableEq Party]

theorem foldr_rcv_t_now (N : GlobalState Tx Hash Party AdvState) (ps : List Party) :
    (ps.foldr party_rcv_step_world N).t_now = N.t_now := by
  induction ps with
  | nil => rfl
  | cons p ps ih => rw [List.foldr_cons, rcv_t_now, ih]

theorem foldr_bake_t_now (N : GlobalState Tx Hash Party AdvState) (ps : List Party) :
    (ps.foldr party_bake_step_world N).t_now = N.t_now := by
  induction ps with
  | nil => rfl
  | cons p ps ih => rw [List.foldr_cons, bake_t_now, ih]

/-- A phase advances the slot by one exactly when it is a `NextRound` step. -/
theorem phaseStep_t_now_eq (N : GlobalState Tx Hash Party AdvState) :
    (phaseStep N).t_now = if N.progress = .Baked then N.t_now + 1 else N.t_now := by
  unfold phaseStep
  cases h : N.progress <;> simp [foldr_rcv_t_now, foldr_bake_t_now, inc_round, round_tick]

/-- A phase that advances the slot ends in a `Ready` state. -/
theorem phaseStep_ready (N : GlobalState Tx Hash Party AdvState)
    (h : (phaseStep N).t_now ≠ N.t_now) : (phaseStep N).progress = .Ready := by
  rw [phaseStep_t_now_eq] at h
  unfold phaseStep
  cases hp : N.progress <;> simp_all

end Phase

/-! ## The views of the PoS-NSB execution -/

section Views

open PoSNSB Parameters BlockParameters Corruption Execution

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} {PK SK Sig : Type}
  (P : Protocol Tx Hash np n Hz) (Sch : PSigScheme (Block Tx Hash (Fin np)) PK SK Sig)
  [Sch.Deterministic] (A : Adversary Tx Hash np n Hz PK Sig) (Tree : TreeFamily P)

/-- The slot after `j` phases of the real execution of the seed `ω`. -/
def roundAt (ω : Seed Tx Hash np n Hz PK SK) (j : ℕ) : ℕ :=
  letI := ω.params P; letI := ω.bparams P; (sTrace Sch P ω A false j).t_now

/-- The positions after `j` phases of the real execution of the seed `ω`: the chain the local
tree of party `p` selects at the previous slot (empty without a local state), and for the
observer `none` the honest tree chain. -/
def posAt (ω : Seed Tx Hash np n Hz PK SK) (j : ℕ) : Option (Fin np) → List (Block Tx Hash (Fin np))
  | none => letI := ω.params P; letI := ω.bparams P; letI := mkExec Sch false P ω A
      honest_tree_chain (Tree ω.L ω.f) (sTrace Sch P ω A false j)
  | some p => letI := ω.params P; letI := ω.bparams P
      ((sTrace Sch P ω A false j).state_map p).elim [] fun l =>
        l.tT.bestChain ((sTrace Sch P ω A false j).t_now - 1) l.tree

theorem posAt_some_of_eq (ω : Seed Tx Hash np n Hz PK SK) (j : ℕ) (p : Fin np) :
    letI := ω.params P; letI := ω.bparams P
    ∀ l, (sTrace Sch P ω A false j).state_map p = some l →
      posAt P Sch A Tree ω j (some p) = l.tT.bestChain ((sTrace Sch P ω A false j).t_now - 1) l.tree := by
  intro l hl
  simp only [posAt, hl, Option.elim]

theorem posAt_some_of_none (ω : Seed Tx Hash np n Hz PK SK) (j : ℕ) (p : Fin np) :
    letI := ω.params P; letI := ω.bparams P
    (sTrace Sch P ω A false j).state_map p = none → posAt P Sch A Tree ω j (some p) = [] := by
  intro hl
  simp only [posAt, hl, Option.elim]

/-- The position of an initial party is nonempty: it has a local state at every phase, and the
chain its tree selects is valid, so it ends in the genesis block. -/
theorem posAt_some_ne_nil (ω : Seed Tx Hash np n Hz PK SK) (j : ℕ) {p : Fin np} (hp : p ∈ P.IP) :
    posAt P Sch A Tree ω j (some p) ≠ [] := by
  let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec Sch false P ω A
  have hN := reachable_inv (reach_runTrace (Tx := Tx) (Hash := Hash) (Party := Fin np)
    (AdvState := A.AdvState) j)
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 ((hN.state_init p).2 hp)
  rw [posAt_some_of_eq P Sch A Tree ω j p l hl]
  intro h
  have := (l.tT.best_chain_valid l.tree ((sTrace Sch P ω A false j).t_now - 1)).2.1
  rw [h] at this
  exact this

/-- The position of a party is the chain of `Finality.seedChain`. -/
theorem posAt_some_eq_seedChain (ω : Seed Tx Hash np n Hz PK SK) (j : ℕ) (p : Fin np) :
    posAt P Sch A Tree ω j (some p) = seedChain P Sch A ω j p := by
  let _ := ω.params P; let _ := ω.bparams P
  unfold seedChain
  rcases h : (sTrace Sch P ω A false j).state_map p with _ | l
  · exact posAt_some_of_none P Sch A Tree ω j p h
  · exact posAt_some_of_eq P Sch A Tree ω j p l h

/-- The position of an initial party ends in the genesis block. -/
theorem gb_suffix_posAt (ω : Seed Tx Hash np n Hz PK SK) (j : ℕ) {p : Fin np} (hp : p ∈ P.IP) :
    [P.GB] <:+ posAt P Sch A Tree ω j (some p) := by
  let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec Sch false P ω A
  have hN := reachable_inv (reach_runTrace (Tx := Tx) (Hash := Hash) (Party := Fin np)
    (AdvState := A.AdvState) j)
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 ((hN.state_init p).2 hp)
  rw [posAt_some_of_eq P Sch A Tree ω j p l hl]
  exact valid_chain_suffix_gb (l.tT.best_chain_valid l.tree _)

/-- The view before the seed is drawn: round `0`, no blocks. It is the exploded output of
`F_Tree`. -/
def initView : TreeView (Option (Fin np)) (Block Tx Hash (Fin np)) :=
  ⟨0, fun _ => [], fun _ => [], fun _ => []⟩

/-- The initial view of the protocol: round `0`, the genesis block `P.GB` as the tree and the
position of every party, no final blocks. -/
def startView : TreeView (Option (Fin np)) (Block Tx Hash (Fin np)) :=
  ⟨0, fun _ => [P.GB], fun _ => [P.GB], fun _ => []⟩

/-- The view after `j` phases, reported as phase `min j K`: round the slot, positions
`posAt`, trees the blocks that have been on the positions so far, no final blocks. -/
def phaseView (K : ℕ) (ω : Seed Tx Hash np n Hz PK SK) (j : ℕ) :
    TreeView (Option (Fin np)) (Block Tx Hash (Fin np)) where
  round := roundAt P Sch A ω (min j K)
  tree o := (List.range (min j K + 1)).flatMap fun i => posAt P Sch A Tree ω i o
  pos := posAt P Sch A Tree ω (min j K)
  fin _ := []

/-- The honest parties of the tree trace: `some p` for `p` honest. The observer `none` is not
honest. -/
def honestP (o : Option (Fin np)) : Prop := ∃ p, o = some p ∧ CorruptionStatus p = .Honest

variable (Tx Hash) in
/-- The honest blocks. -/
def hbB (b : Block Tx Hash (Fin np)) : Bool := decide (CorruptionStatus b.bid = .Honest)

/-- The block tree of the guard: ancestry is the slot order, rooted at the genesis block. -/
def slotTree : BlockTree (Block Tx Hash (Fin np)) :=
  ⟨fun a b => a.sl ≤ b.sl, P.GB, fun _ => le_rfl, fun h h' => h.trans h'⟩

/-- The trace properties of `F_Tree`: the chain growth of `PoSNSB.Good` (of the observer, rate
`pH ν - ε`), chain quality and common prefix, the persistence of nonempty honest positions, and
the positions on which finality liveness rests (`TreeTrace.LiveTrace` for the slot tree, with
chain-growth window `d + 2`). -/
def chainP (ν : PMF SlotKind) (d w : ℕ) (ε : ℝ) :
    List (TreeTrace (Option (Fin np)) (Block Tx Hash (Fin np)) → Prop) :=
  [SlotChainGrowth none (pH ν - ε) d, SlotChainQuality Block.sl (hbB Tx Hash) d w,
    SlotCommonPrefix Block.sl d, PosNonemptyPersists,
    fun X => X.LiveTrace (slotTree P) Block.sl (d + 2)]

theorem chainP_stable (ν : PMF SlotKind) (d w : ℕ) (ε : ℝ) :
    ∀ φ ∈ chainP P ν d w ε, Stable φ := by
  simp only [chainP, List.mem_cons, List.not_mem_nil, or_false]
  rintro φ (rfl | rfl | rfl | rfl | rfl)
  exacts [stable_slotChainGrowth _ _ _, stable_slotChainQuality _ _ _ _,
    stable_slotCommonPrefix _ _, stable_posNonemptyPersists, stable_liveTrace _ _ _]

theorem roundAt_succ (ω : Seed Tx Hash np n Hz PK SK) (j : ℕ) :
    roundAt P Sch A ω (j + 1) = letI := ω.params P; letI := ω.bparams P
      if (sTrace Sch P ω A false j).progress = .Baked then roundAt P Sch A ω j + 1 else roundAt P Sch A ω j := by
  let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec Sch false P ω A
  exact (congrArg GlobalState.t_now (runTrace_succ (AdvState := A.AdvState) j)).trans
    (phaseStep_t_now_eq _)

theorem roundAt_mono (ω : Seed Tx Hash np n Hz PK SK) {j j' : ℕ} (h : j ≤ j') :
    roundAt P Sch A ω j ≤ roundAt P Sch A ω j' := by
  induction j', h using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => rw [roundAt_succ]; split_ifs <;> omega

theorem ready_of_roundAt_lt (ω : Seed Tx Hash np n Hz PK SK) (j : ℕ)
    (h : roundAt P Sch A ω j < roundAt P Sch A ω (j + 1)) :
    letI := ω.params P; letI := ω.bparams P; (sTrace Sch P ω A false (j + 1)).progress = .Ready := by
  let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec Sch false P ω A
  have e := runTrace_succ (Tx := Tx) (Hash := Hash) (Party := Fin np) (AdvState := A.AdvState) j
  show (runTrace A.AdvState (j + 1)).progress = .Ready
  rw [e]
  refine phaseStep_ready _ fun h' => ?_
  have : roundAt P Sch A ω (j + 1) = roundAt P Sch A ω j := by
    show (runTrace A.AdvState (j + 1)).t_now = (runTrace A.AdvState j).t_now
    rw [e]; exact h'
  omega

/-- The tree trace of a run prefix of length `m` of the seed `ω`: the initial view at time
`0`, and the view after `t - 1` phases at times `1 ≤ t ≤ m`. -/
def XT (K : ℕ) (ω : Seed Tx Hash np n Hz PK SK) (m : ℕ) :
    TreeTrace (Option (Fin np)) (Block Tx Hash (Fin np)) :=
  ⟨honestP, fun t => if t = 0 then startView P else phaseView P Sch A Tree K ω (min t m - 1)⟩

/-- **The guard on good seeds.** Let every honest party be an initial party (`hIP`), let the
genesis block have slot `0`, and let `4 ≤ w` unless the horizon is shorter than the
chain-growth window (`K + 1 < d + 2`). If chain growth, chain quality, common prefix and the
tip condition of `PoSNSB.Good` hold for the seed `ω`, the tree trace of every run prefix of
positive length satisfies the guard of `F_Tree^P` with `P = chainP`: it is well formed,
satisfies the five properties and the final blocks (there are none) agree. The liveness
property `LiveTrace` follows from `Finality.seed_slotChainGrowth` and `Finality.seed_slotTip`. -/
theorem guard_of_good (K : ℕ) (ν : PMF SlotKind) (d w : ℕ) (ε : ℝ)
    (hIP : ∀ p : Fin np, CorruptionStatus p = .Honest → p ∈ P.IP) (hGB : P.GB.sl = 0)
    (hw4 : K + 1 < d + 2 ∨ 4 ≤ w)
    (ω : Seed Tx Hash np n Hz PK SK) (hG : Good P Sch A Tree ν K d w ε ω) {m : ℕ} (hm : 1 ≤ m) :
    FTreeGuard (slotTree P) (chainP P ν d w ε) (XT P Sch A Tree K ω m) := by
  have hst : ∀ t, t ≠ 0 → (XT P Sch A Tree K ω m).st t = phaseView P Sch A Tree K ω (min t m - 1) :=
    fun t ht => if_neg ht
  have hst0 : (XT P Sch A Tree K ω m).st 0 = startView P := by simp [XT]
  have hin : (XT P Sch A Tree K ω m).chains.ChainsInTree (slotTree P) := by
    rintro p t ⟨q, rfl, -⟩
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp [TreeTrace.chains, hst0, startView]
    · simp only [TreeTrace.chains, hst t (by omega), phaseView]
      let _ := ω.params P; let _ := ω.bparams P
      rcases hl : (sTrace Sch P ω A false (min (min t m - 1) K)).state_map q with _ | l
      · rw [posAt_some_of_none P Sch A Tree ω _ q hl]; exact List.Pairwise.nil
      · rw [posAt_some_of_eq P Sch A Tree ω _ q l hl]
        exact (l.tT.best_chain_valid _ _).2.2.imp fun h => le_of_lt h
  have hsT : ∀ q : Fin np, CorruptionStatus q = .Honest → (seedTrace P Sch A K ω).honest q :=
    fun q hq => seedTrace_honest_of_init (hIP q hq) (by simp [is_honest, hq])
  refine ⟨⟨?_, ?_, hin, ?_⟩, ?_, ?_⟩
  · -- trees grow
    rintro p t t' ⟨q, rfl, hq⟩ htt b hb
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · rw [hst0] at hb
      obtain rfl : b = P.GB := List.mem_singleton.1 hb
      rcases Nat.eq_zero_or_pos t' with rfl | ht'
      · rw [hst0]; exact List.mem_singleton_self _
      · rw [hst t' (by omega)]
        exact List.mem_flatMap.2 ⟨0, List.mem_range.2 (Nat.succ_pos _),
          (gb_suffix_posAt P Sch A Tree ω 0 (hIP q hq)).subset (List.mem_singleton_self _)⟩
    · rw [hst t (by omega)] at hb
      rw [hst t' (by omega)]
      obtain ⟨i, hi, hb⟩ := List.mem_flatMap.1 hb
      refine List.mem_flatMap.2 ⟨i, ?_, hb⟩
      simp only [List.mem_range] at hi ⊢
      omega
  · -- positions in trees
    intro p t _ b hb
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · rw [hst0] at hb ⊢; exact hb
    · rw [hst t (by omega)] at hb ⊢
      exact List.mem_flatMap.2 ⟨_, List.mem_range.2 (Nat.lt_succ_self _), hb⟩
  · -- rounds do not decrease
    intro t t' htt
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp [hst0, startView]
    · rw [hst t (by omega), hst t' (by omega)]
      exact roundAt_mono P Sch A ω (by omega)
  · simp only [chainP, List.mem_cons, List.not_mem_nil, or_false]
    rintro φ (rfl | rfl | rfl | rfl | rfl)
    · -- chain growth
      intro t₁ t₂ ht hnew hd w' hw'
      obtain ⟨t₀, rfl, hlt⟩ := hnew
      have e₁ := hst (t₀ + 1) (by omega)
      have e₂ := hst t₂ (by omega)
      rw [e₁, e₂] at hd hw'
      rw [e₁] at hlt
      rw [e₁, e₂]
      have hready : letI := ω.params P; letI := ω.bparams P
          (sTrace Sch P ω A false (min (min (t₀ + 1) m - 1) K)).progress = .Ready := by
        rcases Nat.eq_zero_or_pos t₀ with rfl | h0
        · rw [show min (min (0 + 1) m - 1) K = 0 by omega]; rfl
        · rw [hst t₀ (by omega)] at hlt
          simp only [phaseView] at hlt
          have h1 : min (min (t₀ + 1) m - 1) K = min (min t₀ m - 1) K + 1 := by
            by_contra hc
            rw [show min (min (t₀ + 1) m - 1) K = min (min t₀ m - 1) K by omega] at hlt
            exact lt_irrefl _ hlt
          rw [h1]
          exact ready_of_roundAt_lt P Sch A ω _ (h1 ▸ hlt)
      exact hG.1 _ _ (by omega) (min_le_right _ _) hready hd w' hw'
    · -- chain quality
      rintro t _ ⟨q, rfl, hq⟩ bj bi c hfrag hsl
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · obtain ⟨s₁, s₃, h⟩ := hfrag
        rw [hst0] at h
        have := congrArg List.length h
        simp [startView] at this
        omega
      · rw [hst t (by omega)] at hfrag
        simp only [phaseView] at hfrag
        let _ := ω.params P; let _ := ω.bparams P
        rcases hl : (sTrace Sch P ω A false (min (min t m - 1) K)).state_map q with _ | l
        · rw [posAt_some_of_none P Sch A Tree ω _ q hl] at hfrag
          obtain ⟨s₁, s₃, h⟩ := hfrag
          simp at h
        · rw [posAt_some_of_eq P Sch A Tree ω _ q l hl] at hfrag
          exact hG.2.1 _ (min_le_right _ _) q l hl (decide_eq_true hq) bj bi c hfrag hsl
    · -- common prefix
      rintro t₁ t₂ k _ _ ht hk ⟨q₁, rfl, hq₁⟩ ⟨q₂, rfl, hq₂⟩ hne
      rcases Nat.eq_zero_or_pos t₁ with rfl | ht₁
      · rw [hst0]
        show [P.GB].filter (fun b => decide (b.sl ≤ k)) <:+ _
        by_cases hk' : P.GB.sl ≤ k
        · rw [List.filter_cons_of_pos (by simpa using hk'), List.filter_nil]
          rcases Nat.eq_zero_or_pos t₂ with rfl | ht₂
          · rw [hst0]; exact List.suffix_refl _
          · rw [hst t₂ (by omega)]; exact gb_suffix_posAt P Sch A Tree ω _ (hIP q₂ hq₂)
        · rw [List.filter_cons_of_neg (by simpa using hk'), List.filter_nil]
          exact List.nil_suffix
      · rw [hst t₁ (by omega)] at hk ⊢
        rw [hst t₂ (by omega)] at hne ⊢
        simp only [phaseView] at hk hne ⊢
        let _ := ω.params P; let _ := ω.bparams P
        rcases hl₂ : (sTrace Sch P ω A false (min (min t₂ m - 1) K)).state_map q₂ with _ | l₂
        · exact absurd (posAt_some_of_none P Sch A Tree ω _ q₂ hl₂) hne
        rcases hl₁ : (sTrace Sch P ω A false (min (min t₁ m - 1) K)).state_map q₁ with _ | l₁
        · rw [posAt_some_of_none P Sch A Tree ω _ q₁ hl₁]; simp
        rw [posAt_some_of_eq P Sch A Tree ω _ q₁ l₁ hl₁, posAt_some_of_eq P Sch A Tree ω _ q₂ l₂ hl₂]
        exact hG.2.2.1 _ _ k (by omega) (min_le_right _ _) hk q₁ q₂ l₁ l₂
          (decide_eq_true hq₁) (decide_eq_true hq₂) hl₁ hl₂
    · -- nonempty positions persist: honest positions are never empty
      rintro _ _ t t' - ⟨q, rfl, hq⟩ ht hne
      rcases Nat.eq_zero_or_pos t' with rfl | ht'
      · rw [hst0]; simp [startView]
      · rw [hst t' (by omega)]
        exact posAt_some_ne_nil P Sch A Tree ω _ (hIP q hq)
    · -- the positions on which finality liveness rests
      have hgrowth : 4 ≤ w →
          (seedTrace P Sch A K ω).SlotChainGrowth (seedNow P Sch A ω) Block.sl (d + 2) K :=
        fun h4 => seed_slotChainGrowth hGB hG.2.1 h4 (by omega) (seed_slotTip hG.2.2.2 le_rfl)
      have hpos : ∀ t q, t ≠ 0 → ((XT P Sch A Tree K ω m).st t).pos (some q) =
          seedChain P Sch A ω (min (min t m - 1) K) q := fun t q ht => by
        rw [hst t ht]; exact posAt_some_eq_seedChain P Sch A Tree ω _ q
      exact
        { growth := by
            rintro o t a ⟨q, rfl, hq⟩ ha
            rcases Nat.eq_zero_or_pos t with rfl | ht
            · rw [hst0] at ha; simp [startView] at ha
            · rw [hst t (by omega)] at ha
              change a + (d + 2) ≤ seedNow P Sch A ω (min (min t m - 1) K) at ha
              rw [hpos t q (by omega)]
              rcases hw4 with hK | h4
              · have h1 : seedNow P Sch A ω (min (min t m - 1) K) ≤ min (min t m - 1) K + 1 :=
                  sTrace_t_now P Sch A ω false _
                have h2 : min (min t m - 1) K ≤ K := min_le_right _ _
                omega
              · exact hgrowth h4 q _ a (hsT q hq) (min_le_right _ _) ha
          decreasing := by
            rintro o t ⟨q, rfl, hq⟩
            rcases Nat.eq_zero_or_pos t with rfl | ht
            · rw [hst0]; simp [startView]
            · rw [hpos t q (by omega)]
              let _ := ω.params P; let _ := ω.bparams P
              exact (seedChain_valid (hsT q hq) (min_le_right _ _)).2.2
          genesis_mem := by
            rintro o t ⟨q, rfl, hq⟩
            rcases Nat.eq_zero_or_pos t with rfl | ht
            · rw [hst0]; exact List.mem_singleton_self _
            · rw [hst t (by omega)]
              exact (gb_suffix_posAt P Sch A Tree ω _ (hIP q hq)).subset
                (List.mem_singleton_self _)
          genesis_slot := hGB
          inTree := hin
          round_zero := by rw [hst0]; rfl
          round_step := by
            intro t
            rcases Nat.eq_zero_or_pos t with rfl | ht
            · rw [hst0, hst 1 one_ne_zero]
              show roundAt P Sch A ω (min (min 1 m - 1) K) ≤ 0 + 1
              rw [show min (min 1 m - 1) K = 0 by omega]
              exact sTrace_t_now P Sch A ω false 0
            · rw [hst t (by omega), hst (t + 1) (by omega)]
              show roundAt P Sch A ω (min (min (t + 1) m - 1) K) ≤
                roundAt P Sch A ω (min (min t m - 1) K) + 1
              rcases (show min (min (t + 1) m - 1) K = min (min t m - 1) K ∨
                  min (min (t + 1) m - 1) K = min (min t m - 1) K + 1 by omega) with h | h
              · rw [h]; omega
              · rw [h, roundAt_succ]; split_ifs <;> omega }
  · -- agreement: there are no final blocks
    intro p q t t' b b' i j _ _ hb _
    obtain ⟨C, hC, -⟩ := hb
    have hfin : ∀ t p, ((XT P Sch A Tree K ω m).st t).fin p = [] := by
      intro t p; by_cases ht : t = 0 <;> simp [XT, ht, startView, phaseView]
    simp [TreeTrace.finChains, hfin] at hC

end Views

/-! ## The protocol in the clock-and-network hybrid model, and the simulator -/

section Protocol

open PoSNSB Parameters BlockParameters Corruption Execution ClockNet

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} {PK SK Sig : Type}
  (P : Protocol Tx Hash np n Hz) (Sch : PSigScheme (Block Tx Hash (Fin np)) PK SK Sig)
  [Sch.Deterministic] (A : Adversary Tx Hash np n Hz PK Sig) (Tree : TreeFamily P)
  (H : HashScheme) (cd : H.Codec (BlockDom Tx Hash np Hz) Hash)

/-- The single party of the clock: the scheduler of the phases. -/
abbrev H₁ : Finset Unit := {()}

/-- The clock request of the activation that runs phase `j + 1`: the end of the round is
signalled exactly when phase `j` is followed by the next round. -/
def clockReq (ω : Seed Tx Hash np n Hz PK SK) (j : ℕ) : CNEv Unit Unit :=
  letI := ω.params P; letI := ω.bparams P
  if (sTrace Sch P ω A false j).progress = .Baked then .inl ((), .signal) else .inl ((), .read)

variable (Tx Hash np) in
/-- The outputs to the environment: the clock round and the view. -/
abbrev ChainOut := ℕ × TreeView (Option (Fin np)) (Block Tx Hash (Fin np))

variable (Tx Hash np n Hz PK SK) in
/-- The states of the protocol: an optional seed, a phase counter and the view of the current
phase. -/
abbrev PSt :=
  Option (Seed Tx Hash np n Hz PK SK) × ℕ × TreeView (Option (Fin np)) (Block Tx Hash (Fin np))

variable (Tx Hash np n Hz PK SK) in
/-- The states of the simulator: a protocol state and a state of the ideal clock and network. -/
abbrev SimSt := PSt Tx Hash np n Hz PK SK ×
  (CNSt Unit Unit × Trace (CNSt Unit Unit) (CNEv Unit Unit) (CNOut Unit Unit) × Bool)

variable (Tx Hash np n Hz PK SK) in
/-- The traces of the simulator. -/
abbrev SimTr := Trace (SimSt Tx Hash np n Hz PK SK) (Event Unit Unit) (ChainOut Tx Hash np)

/-- **The PoS-NSB protocol as a hybrid protocol over the clock and the network.** The first
activation samples the seed from `seedDist Sch H cd μ P.h0 W n` and reads the clock; activation
`j + 2` runs phase `j + 1` of the real execution with adversary `A` and sends the clock request
`clockReq`. Each activation stores the view `phaseView` of its phase in the state; the output
is the clock round and the stored view. -/
noncomputable def chainHybrid (K : ℕ) (μ : PMF (Option (Fin np))) (W : ℕ) :
    Hybrid (PSt Tx Hash np n Hz PK SK) (Event Unit Unit) (ChainOut Tx Hash np)
      (CNEv Unit Unit) (CNOut Unit Unit) where
  init := (none, 0, startView P)
  pre s _ := match s.1 with
    | none => SPComp.bind (sampleFrom (ofPMF (seedDist Sch H cd μ P.h0 W n))) fun ω =>
        SPComp.pure ((some ω, 0, phaseView P Sch A Tree K ω 0), .inl ((), .read))
    | some ω => SPComp.pure ((some ω, s.2.1 + 1, phaseView P Sch A Tree K ω (s.2.1 + 1)),
        clockReq P Sch A ω s.2.1)
  post s o := SPComp.pure (s, (o.1, s.2.2))
  pre_noFail s _ := by
    rcases s with ⟨_ | ω, j, v⟩
    · exact Assumptions.SPComp.bind_noFail (sampleFrom_ofPMF_noFail _) fun _ =>
        SPComp.pure_noFail _
    · exact SPComp.pure_noFail _
  post_noFail _ _ := SPComp.pure_noFail _

/-- The real world: the hybrid protocol with the reference implementation of the clock and
the network (honest set `{()}`, delay bound `Δ`). -/
noncomputable def chainReal (K : ℕ) (μ : PMF (Option (Fin np))) (W Δ : ℕ) :=
  (chainHybrid P Sch A Tree H cd K μ W).withSub (clockNet (M := Unit) H₁ Δ).proto

/-- **The simulator** for the adversary `A`: the copy simulator of `F_Tree`, which
runs the hybrid protocol with the ideal clock and network and proposes its states, which
carry their views, to `F_Tree`. -/
noncomputable def chainSim (K : ℕ) (μ : PMF (Option (Fin np))) (W Δ : ℕ) :=
  (chainHybrid P Sch A Tree H cd K μ W).withSub (ideal (clockNetF (M := Unit) H₁ Δ) (clockNet H₁ Δ).proto)

/-- The initial state of the simulator: no seed, phase `0`, the initial view `startView`, and
the initial state of the ideal clock and network. -/
noncomputable def chainInit (Δ : ℕ) : SimSt Tx Hash np n Hz PK SK :=
  ((none, 0, startView P), (ideal (clockNetF (M := Unit) H₁ Δ) (clockNet H₁ Δ).proto).init)

/-- The stored view of a simulator state. -/
def stView (s : SimSt Tx Hash np n Hz PK SK) : TreeView (Option (Fin np)) (Block Tx Hash (Fin np)) :=
  s.1.2.2

/-- **The functionality** `F_Tree^P` over the states of the simulator, with the view stored in
the protocol component (`stView`), honest parties `honestP`, the slot tree, the properties
`chainP`, and exploded output `(0, initView)`. It depends on neither the adversary nor the
tree family. -/
noncomputable def chainF (Δ : ℕ) (ν : PMF SlotKind) (d w : ℕ) (ε : ℝ) :
    TFunc (SimSt Tx Hash np n Hz PK SK) (Event Unit Unit) (ChainOut Tx Hash np) :=
  fTree stView honestP (slotTree P) (chainP P ν d w ε) (chainInit P Δ)
    ((0, initView) : ChainOut Tx Hash np)

theorem chainSim_init (K : ℕ) (μ : PMF (Option (Fin np))) (W Δ : ℕ) :
    (chainSim P Sch A Tree H cd K μ W Δ).init = chainInit P Δ := rfl

theorem chainSim_noFail (K : ℕ) (μ : PMF (Option (Fin np))) (W Δ : ℕ) :
    ∀ s e, SPComp.NoFail ((chainSim P Sch A Tree H cd K μ W Δ).step s e) :=
  Hybrid.withSub_noFail _ _ (Hybrid.ideal_noFail _ _ fun _ _ => SPComp.pure_noFail _)

instance (K : ℕ) (μ : PMF (Option (Fin np))) (W Δ : ℕ) :
    Lossless (chainSim P Sch A Tree H cd K μ W Δ) :=
  ⟨chainSim_noFail P Sch A Tree H cd K μ W Δ⟩

instance (K : ℕ) (μ : PMF (Option (Fin np))) (W Δ : ℕ) :
    Lossless (chainReal P Sch A Tree H cd K μ W Δ) :=
  Hybrid.lossless_withSub _ _

/-- A step of the simulator from a state with seed `ω` is deterministic and runs one phase. -/
theorem chainSim_step_some (K : ℕ) (μ : PMF (Option (Fin np))) (W Δ : ℕ)
    (s : SimSt Tx Hash np n Hz PK SK) (ω : Seed Tx Hash np n Hz PK SK)
    (hs : s.1.1 = some ω) (e : Event Unit Unit) :
    ∃ x, (chainSim P Sch A Tree H cd K μ W Δ).step s e = SPComp.pure x ∧
      x.1.1 = (some ω, s.1.2.1 + 1, phaseView P Sch A Tree K ω (s.1.2.1 + 1)) := by
  obtain ⟨⟨o, j, v⟩, r⟩ := s
  simp only at hs
  subst hs
  simp only [chainSim, Hybrid.withSub, chainHybrid, ideal, DetFunc.proto, SPComp.pure_bind]
  exact ⟨_, rfl, rfl⟩

/-- A step of the simulator from a state without seed samples the seed. -/
theorem chainSim_step_none (K : ℕ) (μ : PMF (Option (Fin np))) (W Δ : ℕ)
    (s : SimSt Tx Hash np n Hz PK SK) (hs : s.1.1 = none) (e : Event Unit Unit) :
    ∃ x : Seed Tx Hash np n Hz PK SK → SimSt Tx Hash np n Hz PK SK × ChainOut Tx Hash np,
      (chainSim P Sch A Tree H cd K μ W Δ).step s e =
      SPComp.bind (sampleFrom (ofPMF (seedDist Sch H cd μ P.h0 W n))) (fun ω => SPComp.pure (x ω)) ∧
      ∀ ω, (x ω).1.1 = (some ω, 0, phaseView P Sch A Tree K ω 0) := by
  obtain ⟨⟨o, j, v⟩, r⟩ := s
  simp only at hs
  subst hs
  simp only [chainSim, Hybrid.withSub, chainHybrid, ideal, DetFunc.proto, SPComp.bind_assoc,
    SPComp.pure_bind]
  exact ⟨_, rfl, fun _ => rfl⟩

/-- The run-prefix invariant: up to its length, the trace visits the state without seed and
then the phases `0, 1, …` of the seed `ω`, each with its view. -/
def TrInv (K : ℕ) (μ : PMF (Option (Fin np))) (W Δ : ℕ) (ω : Seed Tx Hash np n Hz PK SK)
    (tr : SimTr Tx Hash np n Hz PK SK) : Prop :=
  ∀ t ≤ tr.length, (stAt (chainSim P Sch A Tree H cd K μ W Δ).init tr t).1 =
    if t = 0 then (none, 0, startView P) else (some ω, t - 1, phaseView P Sch A Tree K ω (t - 1))

theorem trInv_nil (K : ℕ) (μ : PMF (Option (Fin np))) (W Δ : ℕ) (ω : Seed Tx Hash np n Hz PK SK) :
    TrInv P Sch A Tree H cd K μ W Δ ω [] := by
  intro t ht
  obtain rfl : t = 0 := by simpa using ht
  rfl

theorem trInv_snoc (K : ℕ) (μ : PMF (Option (Fin np))) (W Δ : ℕ) (ω : Seed Tx Hash np n Hz PK SK)
    {tr : SimTr Tx Hash np n Hz PK SK} (h : TrInv P Sch A Tree H cd K μ W Δ ω tr)
    (x : Event Unit Unit × ChainOut Tx Hash np × SimSt Tx Hash np n Hz PK SK)
    (hx : x.2.2.1 = (some ω, tr.length, phaseView P Sch A Tree K ω tr.length)) :
    TrInv P Sch A Tree H cd K μ W Δ ω (tr ++ [x]) := by
  intro t ht
  rw [FTree.Example.stAt_snoc]
  simp only [List.length_append, List.length_singleton] at ht
  split_ifs with h₁ h₂
  · exact (h t h₁).trans (if_pos h₂)
  · exact (h t h₁).trans (if_neg h₂)
  · omega
  · obtain rfl : t = tr.length + 1 := by omega
    rw [hx]
    simp

/-- On a good seed, the guard of `F_Tree` holds on every run prefix of positive length, when
every honest party is an initial party, the genesis block has slot `0`, and `4 ≤ w` unless
`K + 1 < d + 2`. -/
theorem guard_true (K : ℕ) (μ : PMF (Option (Fin np))) (W Δ d w : ℕ) (ε : ℝ)
    (hIP : ∀ p : Fin np, CorruptionStatus p = .Honest → p ∈ P.IP) (hGB : P.GB.sl = 0)
    (hw4 : K + 1 < d + 2 ∨ 4 ≤ w)
    (ω : Seed Tx Hash np n Hz PK SK) (hG : Good P Sch A Tree (kindLaw μ) K d w ε ω)
    {tr : SimTr Tx Hash np n Hz PK SK} (htr : TrInv P Sch A Tree H cd K μ W Δ ω tr) (hlen : 1 ≤ tr.length) :
    (chainF P Δ (kindLaw μ) d w ε).guard tr = true := by
  rw [chainF, fTree_guard_iff]
  have e : traceOf stView honestP (chainInit P Δ) tr = XT P Sch A Tree K ω tr.length := by
    simp only [traceOf, XT, TreeTrace.mk.injEq, true_and]
    funext t
    rw [← stAt_min_length, stView, ← chainSim_init P Sch A Tree H cd K μ W Δ,
      htr _ (min_le_right _ _)]
    by_cases ht : t = 0
    · simp [ht]
    · rw [if_neg (by omega), if_neg ht]
  rw [e]
  exact guard_of_good P Sch A Tree K (kindLaw μ) d w ε hIP hGB hw4 ω hG hlen

/-- The invariant of the monitored simulator: before the seed, the trace is empty and the flag
unset; after it, the phase counter is the trace length minus one, the trace satisfies
`TrInv`, and the flag is unset if the seed is good. -/
def MInv (K : ℕ) (μ : PMF (Option (Fin np))) (W Δ d w : ℕ) (ε : ℝ)
    (m : SimSt Tx Hash np n Hz PK SK × SimTr Tx Hash np n Hz PK SK × Bool) : Prop :=
  (m.1.1.1 = none ∧ m.2.1 = [] ∧ m.2.2 = false) ∨
    ∃ ω, m.1.1.1 = some ω ∧ m.1.1.2.1 + 1 = m.2.1.length ∧
      TrInv P Sch A Tree H cd K μ W Δ ω m.2.1 ∧ (Good P Sch A Tree (kindLaw μ) K d w ε ω → m.2.2 = false)

open Classical in
/-- The potential: before the seed, the probability that the seed is bad; after it, `0` on a
good seed and `1` on a bad one. -/
noncomputable def pot (K : ℕ) (μ : PMF (Option (Fin np))) (W d w : ℕ) (ε : ℝ)
    (m : SimSt Tx Hash np n Hz PK SK) : ℝ≥0∞ :=
  m.1.1.elim ((seedDist Sch H cd μ P.h0 W n).toOuterMeasure
      {ω | ¬Good P Sch A Tree (kindLaw μ) K d w ε ω})
    fun ω => if Good P Sch A Tree (kindLaw μ) K d w ε ω then 0 else 1

/-- **Guard failure is bounded by the failure of `PoSNSB.Good`.** For every environment,
the guard of `F_Tree` fails on the run of the hybrid world with probability at most the
probability under `seedDist` that chain growth, chain quality or common prefix of
`PoSNSB.Good` fails, when every honest party is an initial party, the genesis block has slot
`0`, and `4 ≤ w` unless `K + 1 < d + 2`. -/
theorem guardFail_le (K : ℕ) (μ : PMF (Option (Fin np))) (W Δ d w : ℕ) (ε : ℝ)
    (hIP : ∀ p : Fin np, CorruptionStatus p = .Honest → p ∈ P.IP) (hGB : P.GB.sl = 0)
    (hw4 : K + 1 < d + 2 ∨ 4 ≤ w) {ζ : Type}
    (Z : Env (Strat ζ (Event Unit Unit) (ChainOut Tx Hash np)) ζ) :
    guardFail (chainSim P Sch A Tree H cd K μ W Δ) (chainF P Δ (kindLaw μ) d w ε).guard Z ≤
      (seedDist Sch H cd μ P.h0 W n).toOuterMeasure
        {ω | ¬Good P Sch A Tree (kindLaw μ) K d w ε ω} := by
  classical
  unfold guardFail
  refine prBad_le_of_potential _ _ (MInv P Sch A Tree H cd K μ W Δ d w ε)
    (fun m => pot P Sch A Tree H cd K μ W d w ε m.1) (Or.inl ⟨rfl, rfl, rfl⟩) ?_ ?_ Z
  · rintro m (⟨-, -, hb⟩ | ⟨ω, hs, -, -, hb⟩) h
    · simp [exploded, hb] at h
    · by_cases hg : Good P Sch A Tree (kindLaw μ) K d w ε ω
      · simp [exploded, hb hg] at h
      · simp [pot, hs, hg]
  · rintro ⟨s, tr, b⟩ e Kc h (⟨hs, htr, hb⟩ | ⟨ω, hs, hlen, htr, hb⟩) hK
    · simp only at hs htr hb
      subst htr hb
      obtain ⟨x, hx, hx1⟩ := chainSim_step_none P Sch A Tree H cd K μ W Δ s hs e
      simp only [monitor, hx, SPComp.bind_assoc, SPComp.pure_bind]
      refine (prTrue_bind_sampleFrom_le _ _ h
        (fun ω => if Good P Sch A Tree (kindLaw μ) K d w ε ω then 0 else 1) fun ω => ?_).trans
        (tsum_mul_ite_eq _ _).le |>.trans (by simp [pot, hs])
      have htr' : TrInv P Sch A Tree H cd K μ W Δ ω ([] ++ [(e, (x ω).2, (x ω).1)]) :=
        trInv_snoc P Sch A Tree H cd K μ W Δ ω (trInv_nil P Sch A Tree H cd K μ W Δ ω) _ (hx1 ω)
      refine (hK _ h (Or.inr ⟨ω, by simp [hx1], by simp [hx1], htr', fun hg => ?_⟩)).trans
        (by simp [pot, hx1])
      have hg' := guard_true P Sch A Tree H cd K μ W Δ d w ε hIP hGB hw4 ω hg htr' (by simp)
      rw [List.nil_append] at hg'
      simp [hg']
    · simp only at hs hlen htr hb
      obtain ⟨x, hx, hx1⟩ := chainSim_step_some P Sch A Tree H cd K μ W Δ s ω hs e
      simp only [monitor, hx, SPComp.pure_bind]
      by_cases hg : Good P Sch A Tree (kindLaw μ) K d w ε ω
      · have htr' : TrInv P Sch A Tree H cd K μ W Δ ω (tr ++ [(e, x.2, x.1)]) :=
          trInv_snoc P Sch A Tree H cd K μ W Δ ω htr _ (by rw [hx1, hlen])
        refine (hK _ h (Or.inr ⟨ω, by simp [hx1], by simp [hx1, hlen], htr', fun _ => ?_⟩)).trans
          (by simp [pot, hx1, hs, hg])
        simp [hb hg, guard_true P Sch A Tree H cd K μ W Δ d w ε hIP hGB hw4 ω hg htr' (by simp)]
      · exact (prTrue_le_one _ _).trans (by simp [pot, hs, hg])

/-- Under `ProtocolHyp`, every honest party is an initial party. -/
theorem honest_mem_IP (hP : ProtocolHyp P) :
    ∀ p : Fin np, CorruptionStatus p = .Honest → p ∈ P.IP :=
  fun p hp => hP.leader.honest_mem p (by simp [is_honest, hp])

/-- **PoS-NSB realizes `F_Tree` in the clock-and-network hybrid model.** Let the protocol `P` satisfy `ProtocolHyp`, the honest tree type `Tree` the
longest-chain rule, and the numbers and the leader election `μ` the conditions of
`pos_nsb_security`, let the hash function be `cd.hashOn k` for a uniform key `k` of the keyed
family `H`, and let the blocks be signed with the deterministic signature scheme `Sch`. Then
for every adversary `A`, the protocol running with the reference clock and network
(`chainReal`) realizes the ideal world of `F_Tree^P` (`chainF`, with `P` = chain growth, chain
quality, common prefix of `pos_nsb_security`, the persistence of nonempty honest positions,
and the positions on which finality liveness rests, `LiveTrace` with window `d + 2`) with the
copy simulator `chainSim`, when moreover the genesis block has slot `0` (`hGB`) and `4 ≤ w`
unless `K + 1 < d + 2` (`hw4`): every environment has advantage at most
`posFail P Sch A H cd μ W K d w ε`, the slot bound plus the collision-resistance advantage
against `H` of the explicit collision finder and the EUF-CMA advantages against `Sch` of the
explicit forgers built from `A`.

The statement is `pos_nsb_security` in the form of a realization. The environment gives no
inputs: it only activates the protocol, whose steps ignore the event, and observes the clock
round and the view. The adversary `A` acts inside the execution and is the same in both
worlds; the simulator `chainSim` runs the execution with `A` and stores the view of each
phase in its state, and the functionality `chainF` reads the stored view and depends on
neither `A` nor `Tree`. Chain growth is the property of the observer party `none`, whose
position is the honest tree chain; the views report phase `min j K`, so they are constant
after phase `K`. The network of the clock-and-network functionality carries no message; only
its clock is used. -/
theorem chain_realizes (hP : ProtocolHyp P) (hTree : Tree.Longest)
    (μ : PMF (Option (Fin np))) (W K d w : ℕ) (ε : ℝ) (Δ : ℕ)
    (hwd : w ≤ d) (hWn : W + d ≤ n) (hn : K + 2 ≤ n) (hHz : K + 1 ≤ Hz)
    (hε : 0 ≤ ε) (hγ : 2 * pA (kindLaw μ) ≤ pH (kindLaw μ))
    (hw : (w : ℝ) ≤ d * (pH (kindLaw μ) - pA (kindLaw μ)))
    (h3 : (3 : ℝ) ≤ d * (pH (kindLaw μ) - 2 * pA (kindLaw μ)))
    (hGB : P.GB.sl = 0 := by rfl)
    (hw4 : K + 1 < d + 2 ∨ 4 ≤ w := by first | exact Or.inr (by norm_num) | exact Or.inl (by omega)) :
    RealizesBound (chainReal P Sch A Tree H cd K μ W Δ)
      (ideal (chainF P Δ (kindLaw μ) d w ε) (chainSim P Sch A Tree H cd K μ W Δ))
      (fun _ _ => posFail P Sch A H cd μ W K d w ε) := by
  refine ⟨fun ζ Z => ?_⟩
  have h := clockNet_hybrid_compose H₁ Δ (chainHybrid P Sch A Tree H cd K μ W)
    (chainSim P Sch A Tree H cd K μ W Δ)
    (chainF P Δ (kindLaw μ) d w ε) (chainSim_noFail P Sch A Tree H cd K μ W Δ) rfl
    (fun _ _ _ => rfl) ζ Z
  exact h.trans ((guardFail_le P Sch A Tree H cd K μ W Δ d w ε (honest_mem_IP P hP) hGB hw4
    Z).trans
    (pos_nsb_security P Sch A Tree hP hTree H cd μ W K d w ε hwd hWn hn hHz hε hγ hw h3))

/-- The realization as concrete UC emulation (`UCConcrete.UCEmulatesCSim`) through
`UCFromRealizes`: with the environment strategy as honest input, the environment's final state
as output, empty leakage (the adversary acts inside the execution) and the identity simulator
map, the real and the ideal view maps are at distance at most the failure bound of
`pos_nsb_security` for every environment. -/
example (hP : ProtocolHyp P) (hTree : Tree.Longest)
    (μ : PMF (Option (Fin np))) (W K d w : ℕ) (ε : ℝ) (Δ : ℕ)
    (hwd : w ≤ d) (hWn : W + d ≤ n) (hn : K + 2 ≤ n) (hHz : K + 1 ≤ Hz)
    (hε : 0 ≤ ε) (hγ : 2 * pA (kindLaw μ) ≤ pH (kindLaw μ))
    (hw : (w : ℝ) ≤ d * (pH (kindLaw μ) - pA (kindLaw μ)))
    (h3 : (3 : ℝ) ≤ d * (pH (kindLaw μ) - 2 * pA (kindLaw μ)))
    (ζ V : Type) (hGB : P.GB.sl = 0 := by rfl)
    (hw4 : K + 1 < d + 2 ∨ 4 ≤ w := by first | exact Or.inr (by norm_num) | exact Or.inl (by omega)) :
    UCEmulatesCSim ⟨Strat ζ (Event Unit Unit) (ChainOut Tx Hash np), ζ, Empty, Empty, V⟩
      (fun s => SPComp.bind (view (chainReal P Sch A Tree H cd K μ W Δ) s) fun z =>
        SPComp.pure (Sum.inl z))
      (fun s => SPComp.bind (view (ideal (chainF P Δ (kindLaw μ) d w ε)
        (chainSim P Sch A Tree H cd K μ W Δ)) s) fun z => SPComp.pure (Sum.inl z)) id
      (fun _ _ => posFail P Sch A H cd μ W K d w ε) :=
  haveI := chain_realizes P Sch A Tree H cd hP hTree μ W K d w ε Δ hwd hWn hn hHz hε hγ hw
    h3 hGB hw4
  ucEmulatesCSim_of_UCFromRealizes _ _ ζ V fun _ _ => posFail P Sch A H cd μ W K d w ε

end Protocol

/-! ## A concrete instance -/

namespace Instance

open PoSNSB PoSNSB.Instance Corruption

attribute [local instance] PoSNSB.Instance.corruption

/-- The collision finder of the instance against the random function `H` has advantage at most
the birthday bound `1 (1 - 1) / 2 / |Unit| = 0`: in phase `0` the only block is the genesis
block, the first query of the querier that always asks for it. -/
theorem collFinder_advantage_le :
    CR_Search_Advantage H (collFinder Sch P A H cd μ 1 0) ≤
      ((1 * (1 - 1) / 2 : ℕ) : ℝ≥0∞) / Fintype.card Unit :=
  collFinder_advantage_randomFun_le Sch P A μ 1 0 1 (fun _ _ _ => encB 1 GB)
    fun ω j hj b hb => by
    obtain rfl : j = 0 := by omega
    simp only [sTrace, runTrace, Function.iterate_zero, id, block_hist_gb, block_history, N0,
      List.map_nil, List.mem_singleton] at hb
    subst hb
    exact ⟨0, by norm_num, rfl⟩

/-- **Non-vacuity.** For the one-party instance `PoSNSB.Instance` (one
honest party leading every slot, the longest-chain tree type, a trivial signature scheme, the
adversary that sends nothing, slot kinds `ν = kindLaw μ` concentrated on honest slots), with
`W = 1`, `K = 0`, `d = 3`, `w = 1`, `ε = 0`, the random function `H` with the identity codec
`cd` and delay bound `Δ = 2`, every hypothesis of `chain_realizes` holds, so the protocol
realizes `F_Tree` with bound `slotBound ν 4 3 1 0 + 0 / 1 + ∑ᵢ eufcmaAdvantage …`: the
collision finder `collFinder Sch P A H cd μ 1 0` only sees the genesis block, the first query
of a querier, and its advantage is at most the birthday bound `1 (1 - 1) / 2 / |Unit| = 0`. -/
theorem instance_realizes :
    Realizes (chainReal P Sch A Tree H cd 0 μ 1 2)
      (ideal (chainF P 2 ν 3 1 0) (chainSim P Sch A Tree H cd 0 μ 1 2))
      (fun _ _ => slotBound ν 4 3 1 0 + ((1 * (1 - 1) / 2 : ℕ) : ℝ≥0∞) / Fintype.card Unit +
        ∑ i : Fin 1,
          eufcmaAdvantage Sch.toSigScheme (toEUFAdversary (forger Sch P A H cd μ 1 0 i))) := by
  obtain ⟨hP, hT, hwd, hWn, hn, hHz, hε, hγ, hw, h3⟩ := instance_hyps
  intro ζ Z
  exact (chain_realizes P Sch A Tree H cd hP hT μ 1 0 3 1 0 2 hwd hWn hn hHz hε hγ hw h3 rfl
    (Or.inl (by norm_num)) ζ Z).trans (add_le_add_left (add_le_add_right collFinder_advantage_le _) _)

end Instance

end CatCryptCore.Consensus.UC.Chain
