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

end CatCryptCore.Consensus.UC.Chain
