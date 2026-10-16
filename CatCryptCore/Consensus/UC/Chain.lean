/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.UC.FTree
public import CatCryptCore.Consensus.PoSNSB.Prob
public import CatCryptCore.Crypto.UCClockNetwork
public import CatCryptCore.NonUniform.UnaryRules

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# PoS-NSB realizes `F_Tree` in the clock-and-network hybrid model

Row C4a of the Ethereum consensus plan. The PoS-NSB protocol with signed blocks (rows D1, D2),
run as a hybrid protocol over the clock-and-network functionality of row C2, realizes the tree
functionality `F_Tree^P` of row C3 whose trace properties `P` are the chain growth, chain
quality and common prefix properties of D2. The distinguishing advantage of every environment
is at most the D2 failure bound
`slotBound ν n d w ε + q (q - 1) / 2 / |Hash| + ∑ᵢ eufAdv (forger P A ν W K i)`.

## The protocol

`chainHybrid P A Tree K ν W` is a hybrid protocol (`Hybrid`) with one call to the
clock-and-network functionality `clockNet H₁ Δ` per activation. Its state is an optional seed
and a phase counter. The first activation samples the seed `ω` from `seedDist ν W n Hz Sch`
(the lottery, the random oracle and the keys); every later activation runs one more phase of
the real execution `sTrace P ω A false` and signals the end of the round to the clock exactly
when the phase is a `NextRound` step, so the clock round follows the slot. The output to the
environment is the clock round and the tree view of the new state.

The view (`pView`) of a state reports, for every party `some p`, its position: the chain its
local tree selects at the previous slot; for the observer party `none`, the honest tree chain
of D2; the tree of a party is the set of blocks that have been on its position so far; the
round is the slot `t_now`; there are no final blocks. Phases after `K` are reported as phase
`K`, the horizon of the D2 bound.

## Main results

* `prBad_le_of_potential`: a bad-event bound by a potential that does not increase in
  expectation along the steps of a system and is at least `1` on bad states.
* `guard_of_good`: on a seed on which chain growth, chain quality and common prefix of D2
  hold (`Good`), the tree trace of every run prefix satisfies the guard of `F_Tree^P`.
* `guardFail_le`: the guard of `F_Tree^P` fails on the run of the hybrid world with probability
  at most the probability that `Good` fails under `seedDist`.
* `chain_realizes` (headline): for every adversary `A`, the protocol running with the reference
  clock and network realizes `ideal (chainF …) (chainSim …)`, with bound the D2 failure bound.
* `chain_UCEmulatesCSim`: the same in the form `UCConcrete.UCEmulatesCSim`.
* `Instance.instance_realizes`: the hypotheses hold for the one-party instance of D2.

## Modelling choices

* The trace properties are stated on tree traces (`SlotChainGrowth`, `SlotChainQuality`,
  `SlotCommonPrefix`) with the vocabulary of D2: slots of blocks, honest blocks, the
  `prune_time` of a chain. Chain growth is measured on the observer party from times that
  start a new round (D2 measures it from `Ready` states).
* The guard of `F_Tree` must not depend on the seed. The ancestry relation of the block tree is
  therefore the slot order (`slotTree`): hash links depend on the random oracle of the seed.
* The clock of row C2 drives the slots. The message delivery of PoS-NSB stays D2's internal
  buffer with adversarial delays `1` or `2`; no message is routed through the network of
  `clockNet`.
* The environment activates the protocol and observes its outputs; the adversary is the D2
  adversary `A`, which acts inside the execution. The simulator is the copy simulator of C3: the
  protocol running with the ideal clock and network.
-/

namespace CatCryptCore.Consensus.UC.Chain

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent CatCrypt.NonUniform
open CatCryptCore.Consensus.UC.FTree CatCryptCore.Consensus.Finality FFG
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

/-- **Chain growth** (D2's `CGGood`) of the position of the party `obs` with rate `ρ` and
window `d`: from a time `t₁` that starts a new round to a time `t₂ ≥ t₁` at least `d` rounds
later, the position grows by every `w'` with `w' ≤ ρ Δr`, where `Δr` is the number of rounds in
between. -/
def SlotChainGrowth (obs : Party) (ρ : ℝ) (d : ℕ) (X : TreeTrace Party Blk) : Prop :=
  ∀ t₁ t₂, t₁ ≤ t₂ → NewRound X t₁ → (X.st t₁).round + d ≤ (X.st t₂).round →
    ∀ w' : ℕ, (w' : ℝ) ≤ ρ * (((X.st t₂).round - (X.st t₁).round : ℕ) : ℝ) →
      ((X.st t₁).pos obs).length + w' ≤ ((X.st t₂).pos obs).length

/-- **Chain quality** (D2's `CQGood`) with slot map `sl`, honesty predicate `hb`, window `d`
and quality `w`: a fragment `b_j :: c ++ [b_i]` of the position of an honest party with
`sl b_i + 1 + d ≤ sl b_j` contains at least `w - 1` honest blocks. -/
def SlotChainQuality (sl : Blk → ℕ) (hb : Blk → Bool) (d w : ℕ) (X : TreeTrace Party Blk) :
    Prop :=
  ∀ t p, X.honest p → ∀ (bj bi : Blk) (c : List Blk),
    PoSNSB.fragment ([bj] ++ c ++ [bi]) ((X.st t).pos p) → sl bi + 1 + d ≤ sl bj →
      w - 1 ≤ (([bj] ++ c ++ [bi]).filter hb).length

/-- **Common prefix** (D2's `CPGood`) with slot map `sl` and window `d`: for honest parties
`p₁` at `t₁` and `p₂` at `t₂ ≥ t₁` with a nonempty position, and a slot `k` at least `d` slots
before the round at `t₁`, the blocks of slot at most `k` of the position of `p₁` form a suffix
of the position of `p₂`. -/
def SlotCommonPrefix (sl : Blk → ℕ) (d : ℕ) (X : TreeTrace Party Blk) : Prop :=
  ∀ t₁ t₂ (k : ℕ) p₁ p₂, t₁ ≤ t₂ → k + d ≤ (X.st t₁).round → X.honest p₁ → X.honest p₂ →
    (X.st t₂).pos p₂ ≠ [] →
      ((X.st t₁).pos p₁).filter (fun b => decide (sl b ≤ k)) <:+ (X.st t₂).pos p₂

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
  {n Hz : ℕ} {Sch : SigScheme (Block Tx Hash (Fin np))}
  (P : Protocol Tx Hash np n Hz) (A : Adversary Tx Hash np n Hz Sch) (Tree : TreeFamily P)

/-- The slot after `j` phases of the real execution of the seed `ω`. -/
def roundAt (ω : Seed Tx Hash np n Hz Sch) (j : ℕ) : ℕ :=
  letI := ω.params P; letI := ω.bparams P; (sTrace P ω A false j).t_now

/-- The positions after `j` phases of the real execution of the seed `ω`: the chain the local
tree of party `p` selects at the previous slot (empty without a local state), and for the
observer `none` the honest tree chain. -/
def posAt (ω : Seed Tx Hash np n Hz Sch) (j : ℕ) : Option (Fin np) → List (Block Tx Hash (Fin np))
  | none => letI := ω.params P; letI := ω.bparams P; letI := mkExec false P ω A
      honest_tree_chain (Tree ω.κ ω.f) (sTrace P ω A false j)
  | some p => letI := ω.params P; letI := ω.bparams P
      ((sTrace P ω A false j).state_map p).elim [] fun l =>
        l.tT.bestChain ((sTrace P ω A false j).t_now - 1) l.tree

theorem posAt_some_of_eq (ω : Seed Tx Hash np n Hz Sch) (j : ℕ) (p : Fin np) :
    letI := ω.params P; letI := ω.bparams P
    ∀ l, (sTrace P ω A false j).state_map p = some l →
      posAt P A Tree ω j (some p) = l.tT.bestChain ((sTrace P ω A false j).t_now - 1) l.tree := by
  intro l hl
  simp only [posAt, hl, Option.elim]

theorem posAt_some_of_none (ω : Seed Tx Hash np n Hz Sch) (j : ℕ) (p : Fin np) :
    letI := ω.params P; letI := ω.bparams P
    (sTrace P ω A false j).state_map p = none → posAt P A Tree ω j (some p) = [] := by
  intro hl
  simp only [posAt, hl, Option.elim]

/-- The view before the seed is drawn: round `0`, no blocks. -/
def initView : TreeView (Option (Fin np)) (Block Tx Hash (Fin np)) :=
  ⟨0, fun _ => [], fun _ => [], fun _ => []⟩

/-- The view after `j` phases, reported as phase `min j K`: round the slot, positions
`posAt`, trees the blocks that have been on the positions so far, no final blocks. -/
def phaseView (K : ℕ) (ω : Seed Tx Hash np n Hz Sch) (j : ℕ) :
    TreeView (Option (Fin np)) (Block Tx Hash (Fin np)) where
  round := roundAt P A ω (min j K)
  tree o := (List.range (min j K + 1)).flatMap fun i => posAt P A Tree ω i o
  pos := posAt P A Tree ω (min j K)
  fin _ := []

/-- The view of a protocol state (optional seed, phase). -/
def pView (K : ℕ) (s : Option (Seed Tx Hash np n Hz Sch) × ℕ) :
    TreeView (Option (Fin np)) (Block Tx Hash (Fin np)) :=
  s.1.elim initView fun ω => phaseView P A Tree K ω s.2

/-- The honest parties of the tree trace: `some p` for `p` honest. The observer `none` is not
honest. -/
def honestP (o : Option (Fin np)) : Prop := ∃ p, o = some p ∧ CorruptionStatus p = .Honest

variable (Tx Hash) in
/-- The honest blocks. -/
def hbB (b : Block Tx Hash (Fin np)) : Bool := decide (CorruptionStatus b.bid = .Honest)

/-- The block tree of the guard: ancestry is the slot order, rooted at the genesis block. -/
def slotTree : BlockTree (Block Tx Hash (Fin np)) :=
  ⟨fun a b => a.sl ≤ b.sl, P.GB, fun _ => le_rfl, fun h h' => h.trans h'⟩

/-- The trace properties of `F_Tree`: D2's chain growth (of the observer, rate `pH ν - ε`),
chain quality and common prefix. -/
def chainP (ν : PMF SlotKind) (d w : ℕ) (ε : ℝ) :
    List (TreeTrace (Option (Fin np)) (Block Tx Hash (Fin np)) → Prop) :=
  [SlotChainGrowth none (pH ν - ε) d, SlotChainQuality Block.sl (hbB Tx Hash) d w,
    SlotCommonPrefix Block.sl d]

theorem chainP_stable (ν : PMF SlotKind) (d w : ℕ) (ε : ℝ) :
    ∀ φ ∈ chainP (Tx := Tx) (Hash := Hash) (np := np) ν d w ε, Stable φ := by
  simp only [chainP, List.mem_cons, List.not_mem_nil, or_false]
  rintro φ (rfl | rfl | rfl)
  exacts [stable_slotChainGrowth _ _ _, stable_slotChainQuality _ _ _ _,
    stable_slotCommonPrefix _ _]

theorem roundAt_succ (ω : Seed Tx Hash np n Hz Sch) (j : ℕ) :
    roundAt P A ω (j + 1) = letI := ω.params P; letI := ω.bparams P
      if (sTrace P ω A false j).progress = .Baked then roundAt P A ω j + 1 else roundAt P A ω j := by
  let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec false P ω A
  exact (congrArg GlobalState.t_now (runTrace_succ (AdvState := A.AdvState) j)).trans
    (phaseStep_t_now_eq _)

theorem roundAt_mono (ω : Seed Tx Hash np n Hz Sch) {j j' : ℕ} (h : j ≤ j') :
    roundAt P A ω j ≤ roundAt P A ω j' := by
  induction j', h using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => rw [roundAt_succ]; split_ifs <;> omega

theorem ready_of_roundAt_lt (ω : Seed Tx Hash np n Hz Sch) (j : ℕ)
    (h : roundAt P A ω j < roundAt P A ω (j + 1)) :
    letI := ω.params P; letI := ω.bparams P; (sTrace P ω A false (j + 1)).progress = .Ready := by
  let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec false P ω A
  have e := runTrace_succ (Tx := Tx) (Hash := Hash) (Party := Fin np) (AdvState := A.AdvState) j
  show (runTrace A.AdvState (j + 1)).progress = .Ready
  rw [e]
  refine phaseStep_ready _ fun h' => ?_
  have : roundAt P A ω (j + 1) = roundAt P A ω j := by
    show (runTrace A.AdvState (j + 1)).t_now = (runTrace A.AdvState j).t_now
    rw [e]; exact h'
  omega

/-- The tree trace of a run prefix of length `m` of the seed `ω`: the initial view at time
`0`, and the view after `t - 1` phases at times `1 ≤ t ≤ m`. -/
def XT (K : ℕ) (ω : Seed Tx Hash np n Hz Sch) (m : ℕ) :
    TreeTrace (Option (Fin np)) (Block Tx Hash (Fin np)) :=
  ⟨honestP, fun t => if t = 0 then initView else phaseView P A Tree K ω (min t m - 1)⟩

/-- **The guard on good seeds.** If chain growth, chain quality and common prefix of D2 hold for
the seed `ω`, the tree trace of every run prefix of positive length satisfies the guard of
`F_Tree^P` with `P = chainP`: it is well formed, satisfies the three properties and the final
blocks (there are none) agree. -/
theorem guard_of_good (K : ℕ) (ν : PMF SlotKind) (d w : ℕ) (ε : ℝ)
    (ω : Seed Tx Hash np n Hz Sch) (hG : Good P A Tree ν K d w ε ω) {m : ℕ} (hm : 1 ≤ m) :
    FTreeGuard (slotTree P) (chainP ν d w ε) (XT P A Tree K ω m) := by
  have hst : ∀ t, t ≠ 0 → (XT P A Tree K ω m).st t = phaseView P A Tree K ω (min t m - 1) :=
    fun t ht => if_neg ht
  have hst0 : (XT P A Tree K ω m).st 0 = initView := by simp [XT]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- trees grow
    intro p t t' _ htt b hb
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp [hst0, initView] at hb
    · rw [hst t (by omega)] at hb
      rw [hst t' (by omega)]
      obtain ⟨i, hi, hb⟩ := List.mem_flatMap.1 hb
      refine List.mem_flatMap.2 ⟨i, ?_, hb⟩
      simp only [List.mem_range] at hi ⊢
      omega
  · -- positions in trees
    intro p t _ b hb
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp [hst0, initView] at hb
    · rw [hst t (by omega)] at hb ⊢
      exact List.mem_flatMap.2 ⟨_, List.mem_range.2 (Nat.lt_succ_self _), hb⟩
  · -- positions are chains of the slot tree
    rintro p t ⟨q, rfl, -⟩
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp [TreeTrace.chains, hst0, initView]
    · simp only [TreeTrace.chains, hst t (by omega), phaseView]
      let _ := ω.params P; let _ := ω.bparams P
      rcases hl : (sTrace P ω A false (min (min t m - 1) K)).state_map q with _ | l
      · rw [posAt_some_of_none P A Tree ω _ q hl]; exact List.Pairwise.nil
      · rw [posAt_some_of_eq P A Tree ω _ q l hl]
        exact (l.tT.best_chain_valid _ _).2.2.imp fun h => le_of_lt h
  · -- rounds do not decrease
    intro t t' htt
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp [hst0, initView]
    · rw [hst t (by omega), hst t' (by omega)]
      exact roundAt_mono P A ω (by omega)
  · simp only [chainP, List.mem_cons, List.not_mem_nil, or_false]
    rintro φ (rfl | rfl | rfl)
    · -- chain growth
      intro t₁ t₂ ht hnew hd w' hw'
      obtain ⟨t₀, rfl, hlt⟩ := hnew
      have e₁ := hst (t₀ + 1) (by omega)
      have e₂ := hst t₂ (by omega)
      rw [e₁, e₂] at hd hw'
      rw [e₁] at hlt
      rw [e₁, e₂]
      have hready : letI := ω.params P; letI := ω.bparams P
          (sTrace P ω A false (min (min (t₀ + 1) m - 1) K)).progress = .Ready := by
        rcases Nat.eq_zero_or_pos t₀ with rfl | h0
        · rw [show min (min (0 + 1) m - 1) K = 0 by omega]; rfl
        · rw [hst t₀ (by omega)] at hlt
          simp only [phaseView] at hlt
          have h1 : min (min (t₀ + 1) m - 1) K = min (min t₀ m - 1) K + 1 := by
            by_contra hc
            rw [show min (min (t₀ + 1) m - 1) K = min (min t₀ m - 1) K by omega] at hlt
            exact lt_irrefl _ hlt
          rw [h1]
          exact ready_of_roundAt_lt P A ω _ (h1 ▸ hlt)
      exact hG.1 _ _ (by omega) (min_le_right _ _) hready hd w' hw'
    · -- chain quality
      rintro t _ ⟨q, rfl, hq⟩ bj bi c hfrag hsl
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · obtain ⟨s₁, s₃, h⟩ := hfrag
        simp [hst0, initView] at h
      · rw [hst t (by omega)] at hfrag
        simp only [phaseView] at hfrag
        let _ := ω.params P; let _ := ω.bparams P
        rcases hl : (sTrace P ω A false (min (min t m - 1) K)).state_map q with _ | l
        · rw [posAt_some_of_none P A Tree ω _ q hl] at hfrag
          obtain ⟨s₁, s₃, h⟩ := hfrag
          simp at h
        · rw [posAt_some_of_eq P A Tree ω _ q l hl] at hfrag
          exact hG.2.1 _ (min_le_right _ _) q l hl (decide_eq_true hq) bj bi c hfrag hsl
    · -- common prefix
      rintro t₁ t₂ k _ _ ht hk ⟨q₁, rfl, hq₁⟩ ⟨q₂, rfl, hq₂⟩ hne
      rcases Nat.eq_zero_or_pos t₁ with rfl | ht₁
      · simp [hst0, initView]
      · rw [hst t₁ (by omega)] at hk ⊢
        rw [hst t₂ (by omega)] at hne ⊢
        simp only [phaseView] at hk hne ⊢
        let _ := ω.params P; let _ := ω.bparams P
        rcases hl₂ : (sTrace P ω A false (min (min t₂ m - 1) K)).state_map q₂ with _ | l₂
        · exact absurd (posAt_some_of_none P A Tree ω _ q₂ hl₂) hne
        rcases hl₁ : (sTrace P ω A false (min (min t₁ m - 1) K)).state_map q₁ with _ | l₁
        · rw [posAt_some_of_none P A Tree ω _ q₁ hl₁]; simp
        rw [posAt_some_of_eq P A Tree ω _ q₁ l₁ hl₁, posAt_some_of_eq P A Tree ω _ q₂ l₂ hl₂]
        exact hG.2.2 _ _ k (by omega) (min_le_right _ _) hk q₁ q₂ l₁ l₂
          (decide_eq_true hq₁) (decide_eq_true hq₂) hl₁ hl₂
  · -- agreement: there are no final blocks
    intro p q t t' b b' i j _ _ hb _
    obtain ⟨C, hC, -⟩ := hb
    have hfin : ∀ t p, ((XT P A Tree K ω m).st t).fin p = [] := by
      intro t p; by_cases ht : t = 0 <;> simp [XT, ht, initView, phaseView]
    simp [TreeTrace.finChains, hfin] at hC

end Views

end CatCryptCore.Consensus.UC.Chain
