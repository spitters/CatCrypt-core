/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCTransparent
public import CatCryptCore.Consensus.FinalityExamples

@[expose] public section
set_option autoImplicit false

/-!
# The tree functionalities `F_Tree^P` and `F_FinTree^P'`

This file defines, as transparent functionalities in the sense of
`CatCrypt.Crypto.UCTransparent` (`TFunc`, `ideal`), the two functionalities of
Kamp, Nielsen, Thomsen and Tschudi, *Enig* (ePrint 2022/201), §3:

* `F_Tree^P` (`fTree`): every party has a tree of blocks, a position (its selected
  chain) and a list of final blocks, whose head is its last final block. The adversary
  grows the trees, sets the positions and the final blocks; a change is accepted only if
  the extended trace satisfies every trace property in `P`, and final blocks of honest
  parties that are not on one chain (`TreeTrace.Agreement`) make the functionality
  explode.
* `F_FinTree^P'` (`finTree`): the same tree, where the adversary declares blocks final
  subject to the finality guards chain-forming, agreement, propagation within `Δ` rounds, and either
  `k`-support (`finTreeK`) or `v`-validity (`finTreeV`).

## Model

* `TreeView Party Blk` — the state of the functionality: round, tree, position and
  final blocks of every party. Lists of blocks are newest first, as in PoS-NSB and in
  `Consensus.Finality`; ancestry is an `FFG.BlockTree`.
* `TreeTrace` — an execution seen through the functionality: honest parties and the
  view at each time. `TreeTrace.chains` is the position trace and `TreeTrace.finalized`
  the finalization (block `b` final at position `i` when `b` is at height `i` in the
  final list), both in the vocabulary of `Consensus.Finality`.
* `traceOf vw honest s₀ tr` — the tree trace of a trace `tr` whose states are mapped
  to views by `vw`; time `t` is the state after `t` activations, and times beyond the end
  of `tr` see the last state.
* `treeFunc vw honest G s₀ ex` — the transparent functionality with guard `G` on tree
  traces. Its state type `σ` is the state of the simulator; the functionality's own
  state is `vw s`. The guard depends on the trace only through the views.

## Trace properties

Reused from `Consensus.Finality`, applied to `chains` and `finalized`:
`CommonPrefix` (`ChainTrace.CommonPrefix`), `ChainQuality` (`ChainTrace.ChainQuality`),
positions in the block tree (`ChainTrace.ChainsInTree`, part of `WellFormed`),
finality-respecting positions (`Finality.FinalityRespecting`: a block final for an
honest party stays on its position), `ChainForming` (`Finality.ChainForming`),
`Agreement` (`Finality.Agreement`), and the depth predicate `Finality.kDeep` (for
`finalized` with depth `0` and for `KSupport`).

Defined in this file: `ChainGrowth` and `DeltaPropagated`, which measure time in rounds of
the view (`ChainTrace.ChainGrowth` measures it in steps of the trace, and a finite trace
extended by its last state violates it), `KSupport` and `Validity` (the support guards of
`F_FinTree`), the well-formedness conditions `TreesGrow`, `PositionsInTrees`,
`RoundsMonotone`, the clock condition `RoundStep`, and finality liveness `UpdatedWithin`
(every honest party has a final block whose slot is at most `L` rounds behind the current
round), a property that each prefix of the trace can check.

Naming: `Finality.PositionRespecting` (finality-respecting *positions* in the sense of
finalization indices) is a different property; Enig's finality-respecting positions (a
party's position extends its final blocks) is `Finality.FinalityRespecting`.

## Main results

* `fTree_guard_iff`, `finTree_guard_iff` — the guards unfold to the stated properties.
* `fTree_guard_prefix`, `finTree_guard_prefix` — the guards are safety properties: a
  guard that holds on a trace holds on each of its prefixes, provided every property of
  `P` is stable under truncation (`Stable`); all properties defined here are
  (`stable_*`). Hence explosion in `UCTransparent.ideal` is permanent exactly as the trace
  property is violated permanently.
* `ideal_step_live`, `ideal_step_exploded` — one step of the ideal world: before
  explosion it outputs the simulator's output iff the extended trace satisfies the
  guard, and the designated exploded output otherwise.
* The copy simulator, which runs the protocol and copies its tree, position and final
  blocks into the functionality, realizes `F_Tree^P` and `F_FinTree^P'` with advantage at
  most the probability that the real trace violates the guard: for a lossless protocol
  `π`, `RealizesBound π (ideal F π) (fun _ Z => guardFail π F.guard Z)` is found by
  instance search (`UCTransparent.realizesBound_of_guardFail` with `guardSim_copy`, from
  the up-to-bad lemma `adv_le_prBad` on the monitored run).
* `fTree_adv_eq_zero`, `finTree_adv_eq_zero` — the realization is perfect for every
  environment under which the real trace satisfies the guard almost surely.
* `prBad_eq_zero_of_invariant` — an invariant of the reachable states that excludes the
  bad states gives bad-event probability `0`.
* `Example.lineProto_fTree_adv`, `Example.lineProto_finTree_adv` — non-vacuity: a
  protocol whose single honest party extends the chain `[n, …, 0]` by one block per
  activation and finalizes the blocks two deep satisfies the guards of `F_Tree^P` (with
  common prefix, chain growth, chain quality and finality-respecting positions) and of
  `F_FinTree^P'` (with `k`-support and with `v`-validity) on every run, so the copy
  simulator realizes both perfectly against every environment.

## Modelling choices

In Enig, `F_Tree^P` ignores an adversarial input that would violate `P`, and explodes on
inconsistent `SetFinal` calls. `UCTransparent.ideal` has a single reaction to a guard failure:
explosion. The guard of `fTree` is therefore the conjunction of `P` and agreement of the
final blocks, and an input violating `P` explodes the functionality instead of being
ignored. For the copy simulator the two readings differ only on runs where the real trace
violates the guard, whose probability is the realization bound in both cases.
Corruption is static (`honest` is fixed for the run).
-/

namespace CatCryptCore.Consensus.UC.FTree

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent
open CatCryptCore.Consensus.Finality FFG
open scoped ENNReal

/-! ## Views and tree traces -/

/-- The state of the tree functionality: the current round and, for every party, its tree
of blocks, its position (selected chain, newest block first) and its final blocks
(newest first; the head is the last final block). -/
structure TreeView (Party Blk : Type) where
  /-- The current round. -/
  round : ℕ
  /-- The blocks in the tree of each party. -/
  tree : Party → List Blk
  /-- The position of each party: its selected chain, newest block first. -/
  pos : Party → List Blk
  /-- The final blocks of each party, newest first. -/
  fin : Party → List Blk

/-- The last final block of party `p`, if any. -/
def TreeView.lastFinal {Party Blk : Type} (v : TreeView Party Blk) (p : Party) : Option Blk :=
  (v.fin p).head?

/-- An execution seen through the tree functionality: the honest parties and the view at
each time. -/
structure TreeTrace (Party Blk : Type) where
  /-- The honest parties. -/
  honest : Party → Prop
  /-- The view at each time. -/
  st : ℕ → TreeView Party Blk

namespace TreeTrace

variable {Party Blk : Type} (X : TreeTrace Party Blk)

/-- The positions as a `ChainTrace` of `Consensus.Finality`. -/
def chains : ChainTrace Party Blk := ⟨X.honest, fun t p => (X.st t).pos p⟩

/-- The final-block lists as a `ChainTrace`. -/
def finChains : ChainTrace Party Blk := ⟨X.honest, fun t p => (X.st t).fin p⟩

/-- The finalization of the trace: at time `t` party `p` regards `b` as final at
position `i` when `b` is in its final list with `i` blocks below it (`kDeep 0` of the
final lists). -/
def finalized : Finalization Party Blk := kDeep 0 X.finChains

/-- The trace truncated at time `n`: times after `n` see the view at `n`. -/
def clamp (n : ℕ) : TreeTrace Party Blk := ⟨X.honest, fun t => X.st (min t n)⟩

/-! ### Well-formedness -/

/-- The trees of honest parties only grow. -/
def TreesGrow : Prop :=
  ∀ p t t', X.honest p → t ≤ t' → (X.st t).tree p ⊆ (X.st t').tree p

/-- The position of an honest party consists of blocks of its tree. -/
def PositionsInTrees : Prop :=
  ∀ p t, X.honest p → (X.st t).pos p ⊆ (X.st t).tree p

/-- Rounds do not decrease. -/
def RoundsMonotone : Prop :=
  ∀ t t', t ≤ t' → (X.st t).round ≤ (X.st t').round

/-- Well-formedness: trees grow, positions lie in the trees and are chains of `T`
(`ChainTrace.ChainsInTree`), and rounds do not decrease. -/
def WellFormed (T : BlockTree Blk) : Prop :=
  X.TreesGrow ∧ X.PositionsInTrees ∧ X.chains.ChainsInTree T ∧ X.RoundsMonotone

/-! ### Properties of the tree (the parameter `P` of `F_Tree^P`) -/

/-- Common prefix with parameter `k` of the positions (`ChainTrace.CommonPrefix`). -/
def CommonPrefix (k : ℕ) : Prop := X.chains.CommonPrefix k

/-- Chain growth with `g` blocks per `s` rounds: if the round at `t'` is at least `s`
rounds after the round at `t`, the position of honest `q` at `t'` is at least `g` blocks
longer than the position of honest `p` at `t`. -/
def ChainGrowth (s g : ℕ) : Prop :=
  ∀ p q t t', X.honest p → X.honest q → (X.st t).round + s ≤ (X.st t').round →
    ((X.st t).pos p).length + g ≤ ((X.st t').pos q).length

/-- Chain quality of the positions (`ChainTrace.ChainQuality`). -/
def ChainQuality (hb : Blk → Bool) (ℓ μ : ℕ) : Prop := X.chains.ChainQuality hb ℓ μ

/-- Finality-respecting positions: a block final for an honest party lies on its position
at every later time (`Finality.FinalityRespecting`). -/
def FinalityRespectingPos : Prop := FinalityRespecting X.chains X.finalized

/-! ### Finality guards (the parameter `P'` of `F_FinTree^P'`) -/

/-- Chain-forming: the final blocks of an honest party at one time form a chain of `T`
(`Finality.ChainForming`). -/
def ChainForming (T : BlockTree Blk) : Prop := Finality.ChainForming T X.chains X.finalized

/-- Agreement: all blocks final for honest parties lie on one chain of `T`
(`Finality.Agreement`). -/
def Agreement (T : BlockTree Blk) : Prop := Finality.Agreement T X.chains X.finalized

/-- Propagation of final blocks within `Δ` rounds: if `b` is final for honest `p` at `t`,
then at every time `t'` at least `Δ` rounds later every honest `q` has a final block that `b`
is an ancestor of. This is a safety-style propagation guard; it is distinct from the
liveness property `Finality.DeltaUpdated` (a finalized checkpoint close to the tip). -/
def DeltaPropagated (T : BlockTree Blk) (Δ : ℕ) : Prop :=
  ∀ p q t t' b i, X.honest p → X.honest q → X.finalized t p b i →
    (X.st t).round + Δ ≤ (X.st t').round → ∃ b' j, X.finalized t' q b' j ∧ T.anc b b'

/-- `k`-support: a block final for an honest party at `t` was at least `k` deep in the
position of some honest party at some time `t₀ ≤ t` (via `Finality.kDeep`). -/
def KSupport (k : ℕ) : Prop :=
  ∀ p t b i, X.honest p → X.finalized t p b i →
    ∃ q t₀ j, t₀ ≤ t ∧ X.honest q ∧ kDeep k X.chains t₀ q b j

/-- `v`-validity: a block final for an honest party at `t` was on the positions of at least
`v` honest parties, each at some time `t₀ ≤ t`. -/
def Validity (v : ℕ) : Prop :=
  ∀ p t b i, X.honest p → X.finalized t p b i →
    ∃ S : Finset Party, v ≤ S.card ∧ ∀ q ∈ S, X.honest q ∧ ∃ t₀ ≤ t, b ∈ (X.st t₀).pos q

/-! ### Clock and finality liveness -/

/-- The round advances by at most `1` per step. -/
def RoundStep : Prop :=
  ∀ t, (X.st (t + 1)).round ≤ (X.st t).round + 1

/-- Finality liveness from round `τ` with lag `L`: at every time whose round is at least `τ`,
every honest party has a final block whose slot (by `sl`) is at most `L` rounds behind the
current round. -/
def UpdatedWithin (sl : Blk → ℕ) (τ L : ℕ) : Prop :=
  ∀ p t, X.honest p → τ ≤ (X.st t).round → ∃ b ∈ (X.st t).fin p, (X.st t).round ≤ sl b + L

/-- The positions on which finality liveness rests, with block tree `T`, slots `sl` and
chain-growth window `σ`:

* `growth`: every window `(a, a + σ]` of slots with `a + σ` at most the current round contains
  the slot of a block of every honest position;
* `decreasing`: slots decrease strictly along honest positions;
* `genesis_mem`, `genesis_slot`: the genesis block, of slot `0`, is on every honest position;
* `inTree`: honest positions are chains of the block tree;
* `round_zero`, `round_step`: the round starts at `0` and advances by at most `1` per step. -/
structure LiveTrace (T : BlockTree Blk) (sl : Blk → ℕ) (σ : ℕ) : Prop where
  growth : ∀ p t a, X.honest p → a + σ ≤ (X.st t).round →
    ∃ b ∈ (X.st t).pos p, a < sl b ∧ sl b ≤ a + σ
  decreasing : ∀ p t, X.honest p → ((X.st t).pos p).Pairwise fun b b' => sl b' < sl b
  genesis_mem : ∀ p t, X.honest p → T.genesis ∈ (X.st t).pos p
  genesis_slot : sl T.genesis = 0
  inTree : X.chains.ChainsInTree T
  round_zero : (X.st 0).round = 0
  round_step : X.RoundStep

end TreeTrace

/-! ## Stability under truncation -/

section Stable

variable {Party Blk : Type}

/-- A trace property is stable when it is preserved by truncation (`TreeTrace.clamp`):
a safety property. -/
def Stable (φ : TreeTrace Party Blk → Prop) : Prop :=
  ∀ (X : TreeTrace Party Blk) (n : ℕ), φ X → φ (X.clamp n)

theorem stable_wellFormed (T : BlockTree Blk) :
    Stable (fun X : TreeTrace Party Blk => X.WellFormed T) := by
  rintro X n ⟨h1, h2, h3, h4⟩
  exact ⟨fun p t t' hp h => h1 p _ _ hp (min_le_min_right n h), fun p t hp => h2 p _ hp,
    fun p t hp => h3 p _ hp, fun t t' h => h4 _ _ (min_le_min_right n h)⟩

theorem stable_commonPrefix (k : ℕ) :
    Stable (fun X : TreeTrace Party Blk => X.CommonPrefix k) :=
  fun _ n h p q _ _ hp hq htt => h p q _ _ hp hq (min_le_min_right n htt)

theorem stable_chainGrowth (s g : ℕ) :
    Stable (fun X : TreeTrace Party Blk => X.ChainGrowth s g) :=
  fun _ _ h p q _ _ hp hq hr => h p q _ _ hp hq hr

theorem stable_chainQuality (hb : Blk → Bool) (ℓ μ : ℕ) :
    Stable (fun X : TreeTrace Party Blk => X.ChainQuality hb ℓ μ) :=
  fun _ _ h p _ i hp hi => h p _ i hp hi

theorem stable_finalityRespectingPos :
    Stable (fun X : TreeTrace Party Blk => X.FinalityRespectingPos) :=
  fun _ n h p _ _ b i hp htt hb => h p _ _ b i hp (min_le_min_right n htt) hb

theorem stable_chainForming (T : BlockTree Blk) :
    Stable (fun X : TreeTrace Party Blk => X.ChainForming T) :=
  fun _ _ h p _ b b' i j hp hb hb' hij => h p _ b b' i j hp hb hb' hij

theorem stable_agreement (T : BlockTree Blk) :
    Stable (fun X : TreeTrace Party Blk => X.Agreement T) :=
  fun _ _ h p q _ _ b b' i j hp hq hb hb' => h p q _ _ b b' i j hp hq hb hb'

theorem stable_deltaPropagated (T : BlockTree Blk) (Δ : ℕ) :
    Stable (fun X : TreeTrace Party Blk => X.DeltaPropagated T Δ) :=
  fun _ _ h p q _ _ b i hp hq hb hr => h p q _ _ b i hp hq hb hr

/-- A time `t₀ ≤ min t n` is not moved by truncation at `n`. -/
theorem min_eq_of_le_min {t₀ t n : ℕ} (h : t₀ ≤ min t n) : min t₀ n = t₀ :=
  min_eq_left (h.trans (min_le_right _ _))

theorem stable_kSupport (k : ℕ) :
    Stable (fun X : TreeTrace Party Blk => X.KSupport k) := by
  intro X n h p t b i hp hb
  obtain ⟨q, t₀, j, h₀, hq, hk⟩ := h p _ b i hp hb
  refine ⟨q, t₀, j, h₀.trans (min_le_left _ _), hq, ?_⟩
  have e := min_eq_of_le_min h₀
  simpa [kDeep, TreeTrace.chains, TreeTrace.clamp, e] using hk

theorem stable_validity (v : ℕ) :
    Stable (fun X : TreeTrace Party Blk => X.Validity v) := by
  intro X n h p t b i hp hb
  obtain ⟨S, hS, hq⟩ := h p _ b i hp hb
  refine ⟨S, hS, fun q hqS => ⟨(hq q hqS).1, ?_⟩⟩
  obtain ⟨t₀, h₀, hm⟩ := (hq q hqS).2
  exact ⟨t₀, h₀.trans (min_le_left _ _), by simpa [TreeTrace.clamp, min_eq_of_le_min h₀] using hm⟩

theorem stable_roundStep : Stable (fun X : TreeTrace Party Blk => X.RoundStep) := by
  intro X n h t
  change (X.st (min (t + 1) n)).round ≤ (X.st (min t n)).round + 1
  rcases Nat.lt_or_ge t n with ht | ht
  · rw [min_eq_left (show t + 1 ≤ n by omega), min_eq_left ht.le]
    exact h t
  · rw [min_eq_right (show n ≤ t + 1 by omega), min_eq_right ht]
    omega

theorem stable_updatedWithin (sl : Blk → ℕ) (τ L : ℕ) :
    Stable (fun X : TreeTrace Party Blk => X.UpdatedWithin sl τ L) :=
  fun _ n h p t hp hτ => h p (min t n) hp hτ

theorem stable_liveTrace (T : BlockTree Blk) (sl : Blk → ℕ) (σ : ℕ) :
    Stable (fun X : TreeTrace Party Blk => X.LiveTrace T sl σ) := fun X n h =>
  { growth := fun p t a hp ha => h.growth p (min t n) a hp ha
    decreasing := fun p t hp => h.decreasing p (min t n) hp
    genesis_mem := fun p t hp => h.genesis_mem p (min t n) hp
    genesis_slot := h.genesis_slot
    inTree := fun p t hp => h.inTree p (min t n) hp
    round_zero := by
      change (X.st (min 0 n)).round = 0
      rw [Nat.zero_min]; exact h.round_zero
    round_step := stable_roundStep X n h.round_step }

/-- Conjunctions of stable properties are stable. -/
theorem Stable.and {φ ψ : TreeTrace Party Blk → Prop} (hφ : Stable φ) (hψ : Stable ψ) :
    Stable (fun X => φ X ∧ ψ X) :=
  fun X n h => ⟨hφ X n h.1, hψ X n h.2⟩

/-- The conjunction of a list of stable properties is stable. -/
theorem stable_all {P : List (TreeTrace Party Blk → Prop)} (hP : ∀ φ ∈ P, Stable φ) :
    Stable (fun X => ∀ φ ∈ P, φ X) :=
  fun X n h φ hφ => hP φ hφ X n (h φ hφ)

end Stable

/-! ## Tree traces of transparent traces and the functionalities -/

section Func

variable {Party Blk σ E O : Type}

/-- The state after the first `t` entries of the trace `tr`, from the initial state `s₀`;
for `t` beyond the length of `tr`, the last state. -/
def stAt (s₀ : σ) (tr : Trace σ E O) (t : ℕ) : σ :=
  ((tr.take t).getLast?.map fun x => x.2.2).getD s₀

/-- The tree trace of the trace `tr`, with views `vw` and honest parties `honest`. -/
def traceOf (vw : σ → TreeView Party Blk) (honest : Party → Prop) (s₀ : σ)
    (tr : Trace σ E O) : TreeTrace Party Blk :=
  ⟨honest, fun t => vw (stAt s₀ tr t)⟩

/-- The transparent functionality with guard `G` on tree traces: initial state `s₀`,
exploded output `ex`. The guard is `G` on the tree trace (decided classically). -/
noncomputable def treeFunc (vw : σ → TreeView Party Blk) (honest : Party → Prop)
    (G : TreeTrace Party Blk → Prop) (s₀ : σ) (ex : O) : TFunc σ E O where
  init := s₀
  guard tr := @decide (G (traceOf vw honest s₀ tr)) (Classical.propDecidable _)
  exploded := ex

/-- The guard of `F_Tree^P`: well-formedness, every property of `P`, and agreement of the
final blocks (its failure is Enig's `Exploded`). -/
def FTreeGuard (T : BlockTree Blk) (P : List (TreeTrace Party Blk → Prop))
    (X : TreeTrace Party Blk) : Prop :=
  X.WellFormed T ∧ (∀ φ ∈ P, φ X) ∧ X.Agreement T

/-- The guard of `F_FinTree^P'`: well-formedness, every tree property of `P`,
chain-forming, agreement, propagation within `Δ` rounds, and the support guard `supp`. -/
def FinTreeGuard (T : BlockTree Blk) (P : List (TreeTrace Party Blk → Prop)) (Δ : ℕ)
    (supp : TreeTrace Party Blk → Prop) (X : TreeTrace Party Blk) : Prop :=
  X.WellFormed T ∧ (∀ φ ∈ P, φ X) ∧ X.ChainForming T ∧ X.Agreement T ∧
    X.DeltaPropagated T Δ ∧ supp X

/-- `F_Tree^P` as a transparent functionality. -/
noncomputable def fTree (vw : σ → TreeView Party Blk) (honest : Party → Prop)
    (T : BlockTree Blk) (P : List (TreeTrace Party Blk → Prop)) (s₀ : σ) (ex : O) :
    TFunc σ E O :=
  treeFunc vw honest (FTreeGuard T P) s₀ ex

/-- `F_FinTree^P'` as a transparent functionality, with support guard `supp`. -/
noncomputable def finTree (vw : σ → TreeView Party Blk) (honest : Party → Prop)
    (T : BlockTree Blk) (P : List (TreeTrace Party Blk → Prop)) (Δ : ℕ)
    (supp : TreeTrace Party Blk → Prop) (s₀ : σ) (ex : O) : TFunc σ E O :=
  treeFunc vw honest (FinTreeGuard T P Δ supp) s₀ ex

/-- `F_FinTree^P'` with `k`-support. -/
noncomputable abbrev finTreeK (vw : σ → TreeView Party Blk) (honest : Party → Prop)
    (T : BlockTree Blk) (P : List (TreeTrace Party Blk → Prop)) (Δ k : ℕ) (s₀ : σ)
    (ex : O) : TFunc σ E O :=
  finTree vw honest T P Δ (fun X => X.KSupport k) s₀ ex

/-- `F_FinTree^P'` with `v`-validity. -/
noncomputable abbrev finTreeV (vw : σ → TreeView Party Blk) (honest : Party → Prop)
    (T : BlockTree Blk) (P : List (TreeTrace Party Blk → Prop)) (Δ v : ℕ) (s₀ : σ)
    (ex : O) : TFunc σ E O :=
  finTree vw honest T P Δ (fun X => X.Validity v) s₀ ex

theorem treeFunc_guard_iff (vw : σ → TreeView Party Blk) (honest : Party → Prop)
    (G : TreeTrace Party Blk → Prop) (s₀ : σ) (ex : O) (tr : Trace σ E O) :
    (treeFunc vw honest G s₀ ex).guard tr = true ↔ G (traceOf vw honest s₀ tr) := by
  simp [treeFunc]

/-- The guard of `F_Tree^P` holds on `tr` iff its tree trace is well formed, satisfies every
property of `P`, and the final blocks of honest parties agree. -/
theorem fTree_guard_iff (vw : σ → TreeView Party Blk) (honest : Party → Prop)
    (T : BlockTree Blk) (P : List (TreeTrace Party Blk → Prop)) (s₀ : σ) (ex : O)
    (tr : Trace σ E O) :
    (fTree vw honest T P s₀ ex).guard tr = true ↔
      (traceOf vw honest s₀ tr).WellFormed T ∧ (∀ φ ∈ P, φ (traceOf vw honest s₀ tr)) ∧
        (traceOf vw honest s₀ tr).Agreement T :=
  treeFunc_guard_iff _ _ _ _ _ _

/-- The guard of `F_FinTree^P'` holds on `tr` iff its tree trace is well formed, satisfies
every property of `P`, and is chain-forming, in agreement, propagates final blocks within `Δ` rounds and is supported. -/
theorem finTree_guard_iff (vw : σ → TreeView Party Blk) (honest : Party → Prop)
    (T : BlockTree Blk) (P : List (TreeTrace Party Blk → Prop)) (Δ : ℕ)
    (supp : TreeTrace Party Blk → Prop) (s₀ : σ) (ex : O) (tr : Trace σ E O) :
    (finTree vw honest T P Δ supp s₀ ex).guard tr = true ↔
      FinTreeGuard T P Δ supp (traceOf vw honest s₀ tr) :=
  treeFunc_guard_iff _ _ _ _ _ _

/-! ### Prefixes -/

/-- Appending entries does not change the states at times up to the old length. -/
theorem stAt_append_of_le (s₀ : σ) (tr l : Trace σ E O) {t : ℕ} (ht : t ≤ tr.length) :
    stAt s₀ (tr ++ l) t = stAt s₀ tr t := by
  simp [stAt, List.take_append_of_le_length ht]

/-- Truncating time at the length of the trace does not change the state. -/
theorem stAt_min_length (s₀ : σ) (tr : Trace σ E O) (t : ℕ) :
    stAt s₀ tr (min t tr.length) = stAt s₀ tr t := by
  rcases le_total t tr.length with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h]
    simp [stAt, List.take_of_length_le h]

/-- The tree trace of a prefix is the truncation of the tree trace of the whole trace. -/
theorem traceOf_prefix (vw : σ → TreeView Party Blk) (honest : Party → Prop) (s₀ : σ)
    (tr l : Trace σ E O) :
    traceOf vw honest s₀ tr = (traceOf vw honest s₀ (tr ++ l)).clamp tr.length := by
  simp only [traceOf, TreeTrace.clamp, TreeTrace.mk.injEq, true_and]
  funext t
  rw [stAt_append_of_le s₀ tr l (min_le_right _ _), stAt_min_length]

/-- For a stable guard `G`, the guard of `treeFunc` holds on every prefix of a trace on
which it holds. -/
theorem treeFunc_guard_prefix (vw : σ → TreeView Party Blk) (honest : Party → Prop)
    {G : TreeTrace Party Blk → Prop} (hG : Stable G) (s₀ : σ) (ex : O)
    {tr tr' : Trace σ E O} (hpre : tr <+: tr')
    (h : (treeFunc vw honest G s₀ ex).guard tr' = true) :
    (treeFunc vw honest G s₀ ex).guard tr = true := by
  obtain ⟨l, rfl⟩ := hpre
  rw [treeFunc_guard_iff] at h ⊢
  rw [traceOf_prefix vw honest s₀ tr l]
  exact hG _ _ h

/-- The guard of `F_Tree^P` is a safety property: if every property of `P` is stable, the
guard holds on every prefix of a trace on which it holds. -/
theorem fTree_guard_prefix (vw : σ → TreeView Party Blk) (honest : Party → Prop)
    (T : BlockTree Blk) {P : List (TreeTrace Party Blk → Prop)} (hP : ∀ φ ∈ P, Stable φ)
    (s₀ : σ) (ex : O) {tr tr' : Trace σ E O} (hpre : tr <+: tr')
    (h : (fTree vw honest T P s₀ ex).guard tr' = true) :
    (fTree vw honest T P s₀ ex).guard tr = true :=
  treeFunc_guard_prefix vw honest
    ((stable_wellFormed T).and ((stable_all hP).and (stable_agreement T))) s₀ ex hpre h

/-- The guard of `F_FinTree^P'` is a safety property: if every property of `P` and the
support guard are stable, the guard holds on every prefix of a trace on which it holds. -/
theorem finTree_guard_prefix (vw : σ → TreeView Party Blk) (honest : Party → Prop)
    (T : BlockTree Blk) {P : List (TreeTrace Party Blk → Prop)} (hP : ∀ φ ∈ P, Stable φ)
    (Δ : ℕ) {supp : TreeTrace Party Blk → Prop} (hsupp : Stable supp)
    (s₀ : σ) (ex : O) {tr tr' : Trace σ E O} (hpre : tr <+: tr')
    (h : (finTree vw honest T P Δ supp s₀ ex).guard tr' = true) :
    (finTree vw honest T P Δ supp s₀ ex).guard tr = true :=
  treeFunc_guard_prefix vw honest
    ((stable_wellFormed T).and ((stable_all hP).and ((stable_chainForming T).and
      ((stable_agreement T).and ((stable_deltaPropagated T Δ).and hsupp))))) s₀ ex hpre h

end Func
/-! ## The ideal world and realization by the copy simulator -/

section Realize

variable {Party Blk σ ζ E O : Type}

/-- One step of the ideal world `ideal` before explosion: the simulator's transition is
appended to the trace, the flag records whether the guard fails on the extended trace,
and the output is the simulator's output if the guard holds and the exploded output
otherwise. -/
theorem ideal_step_live (F : TFunc σ E O) (S : Sys σ E O) (s : σ) (tr : Trace σ E O)
    (e : E) :
    (ideal F S).step (s, tr, false) e = SPComp.bind (S.step s e) fun p =>
      SPComp.pure ((p.1, tr ++ [(e, p.2, p.1)], !F.guard (tr ++ [(e, p.2, p.1)])),
        if F.guard (tr ++ [(e, p.2, p.1)]) then p.2 else F.exploded) := by
  simp only [ideal, Bool.false_or]
  congr 1; funext p
  cases F.guard (tr ++ [(e, p.2, p.1)]) <;> rfl

/-- One step of the ideal world `ideal` after explosion: the flag stays set and the output is
the exploded output. -/
theorem ideal_step_exploded (F : TFunc σ E O) (S : Sys σ E O) (s : σ) (tr : Trace σ E O)
    (e : E) :
    (ideal F S).step (s, tr, true) e = SPComp.bind (S.step s e) fun p =>
      SPComp.pure ((p.1, tr ++ [(e, p.2, p.1)], true), F.exploded) := by
  simp [ideal]

/-- Perfect realization: for a lossless protocol `π`, an environment under which the real
trace satisfies the guard of `treeFunc` with probability `1` has advantage `0` between `π`
and the ideal world with the copy simulator (`realizesBound_of_guardFail`). -/
theorem treeFunc_adv_eq_zero (π : Sys σ E O) (vw : σ → TreeView Party Blk)
    (honest : Party → Prop) (G : TreeTrace Party Blk → Prop) (ex : O)
    (hπ : ∀ s e, SPComp.NoFail (π.step s e)) (Z : Env (Strat ζ E O) ζ)
    (hZ : guardFail π (treeFunc vw honest G π.init ex).guard Z = 0) :
    adv π (ideal (treeFunc vw honest G π.init ex) π) Z = 0 :=
  haveI : Lossless π := ⟨hπ⟩
  le_antisymm (((inferInstance : RealizesBound π (ideal (treeFunc vw honest G π.init ex) π)
    (fun _ Z => guardFail π (treeFunc vw honest G π.init ex).guard Z)).realizes ζ Z).trans_eq
      hZ) zero_le

/-- Perfect realization of `F_Tree^P` under every environment for
which the real trace satisfies the guard with probability `1`. -/
theorem fTree_adv_eq_zero (π : Sys σ E O) (vw : σ → TreeView Party Blk)
    (honest : Party → Prop) (T : BlockTree Blk) (P : List (TreeTrace Party Blk → Prop))
    (ex : O) (hπ : ∀ s e, SPComp.NoFail (π.step s e)) (Z : Env (Strat ζ E O) ζ)
    (hZ : guardFail π (fTree vw honest T P π.init ex).guard Z = 0) :
    adv π (ideal (fTree vw honest T P π.init ex) π) Z = 0 :=
  treeFunc_adv_eq_zero π vw honest _ ex hπ Z hZ

/-- Perfect realization of `F_FinTree^P'` under every environment
for which the real trace satisfies the guard with probability `1`. -/
theorem finTree_adv_eq_zero (π : Sys σ E O) (vw : σ → TreeView Party Blk)
    (honest : Party → Prop) (T : BlockTree Blk) (P : List (TreeTrace Party Blk → Prop))
    (Δ : ℕ) (supp : TreeTrace Party Blk → Prop) (ex : O)
    (hπ : ∀ s e, SPComp.NoFail (π.step s e)) (Z : Env (Strat ζ E O) ζ)
    (hZ : guardFail π (finTree vw honest T P Δ supp π.init ex).guard Z = 0) :
    adv π (ideal (finTree vw honest T P Δ supp π.init ex) π) Z = 0 :=
  treeFunc_adv_eq_zero π vw honest _ ex hπ Z hZ

end Realize

/-! ## Bad-event probability zero from an invariant -/

section Invariant

variable {τ ζ E O : Type}

/-- A bind whose continuation accepts with probability `0` everywhere accepts with
probability `0`. -/
theorem prTrue_bind_eq_zero {α : Type} (X : SPComp α) (K : α → SPComp Bool) (h₀ : Heap)
    (hK : ∀ a h', prTrue (K a) h' = 0) : prTrue (SPComp.bind X K) h₀ = 0 := by
  refine le_antisymm ?_ zero_le
  calc prTrue (SPComp.bind X K) h₀
      ≤ prTrue (SPComp.bind X fun _ => (SPComp.fail : SPComp Bool)) h₀ :=
        prTrue_bind_le_of_le X _ _ h₀ fun a h' => by rw [hK, prTrue_fail]
    _ = 0 := by rw [bind_fail_right, prTrue_fail]

/-- **Invariant.** Let `Inv` hold initially, exclude the bad states, and be preserved by
every step in the sense that a step from an `Inv` state followed by a continuation that
accepts with probability `0` from every `Inv` state accepts with probability `0`. Then the
bad flag is set with probability `0` under every environment. -/
theorem prBad_eq_zero_of_invariant (S : Sys τ E O) (bad : τ → Bool) (Inv : τ → Prop)
    (hinit : Inv S.init) (hbad : ∀ t, Inv t → bad t = false)
    (hstep : ∀ t e (K : τ × O → SPComp Bool) h, Inv t →
      (∀ p h', Inv p.1 → prTrue (K p) h' = 0) → prTrue (SPComp.bind (S.step t e) K) h = 0)
    (Z : Env (Strat ζ E O) ζ) : prBad S bad Z = 0 := by
  have key : ∀ n z t h, Inv t →
      prTrue (SPComp.bind (loop S bad Z.input n (z, t, false)) fun c => SPComp.pure c.2.2)
        h = 0 := by
    intro n
    induction n with
    | zero => intro z t h _; simp [loop, prTrue_pure]
    | succ n ih =>
      intro z t h ht
      simp only [loop, SPComp.bind_assoc]
      refine prTrue_bind_eq_zero _ _ _ fun a h' => hstep _ _ _ _ ht fun p h'' hp => ?_
      refine prTrue_bind_eq_zero _ _ _ fun z' h''' => ?_
      rw [hbad _ hp, Bool.or_false]
      exact ih _ _ _ hp
  unfold prBad run
  rw [hbad _ hinit]
  exact key _ _ _ _ hinit

end Invariant

/-! ## Non-vacuity: one honest party on a growing chain -/

namespace Example

open Finality.Examples

/-- The view at round `n`: tree and position are the chain `[n, …, 0]`, and the final
blocks are the blocks at least two deep, `[n - 2, …, 0]`. -/
def lineView (n : ℕ) : TreeView Unit ℕ :=
  ⟨n, fun _ => line n, fun _ => line n, fun _ => (line n).drop 2⟩

/-- The tree trace whose view at time `t` is `lineView t`, with one honest party. -/
def lineTT : TreeTrace Unit ℕ := ⟨fun _ => True, lineView⟩

/-- Events: one honest input and one adversarial input, both without content. -/
abbrev Ev := Event Unit Unit

/-- The protocol: its state is the round `n`; every activation moves to round `n + 1` and
outputs the new position `[n + 1, …, 0]`. -/
noncomputable def lineProto : Sys ℕ Ev (List ℕ) where
  init := 0
  step n _ := SPComp.pure (n + 1, line (n + 1))

theorem lineProto_noFail : ∀ s e, SPComp.NoFail (lineProto.step s e) :=
  fun _ _ => SPComp.pure_noFail _

/-- The positions of `lineTT` are `Finality.Examples.lineTrace`. -/
theorem lineTT_chains : lineTT.chains = lineTrace := rfl

/-- The finalization of `lineTT` is the two-deep finality of `Finality.Examples` on
`lineTrace`. -/
theorem lineTT_finalized : lineTT.finalized = kDeep 2 lineTrace := rfl

theorem drop_two_line_suffix {t t' : ℕ} (h : t ≤ t') : (line t).drop 2 <:+ (line t').drop 2 := by
  rcases Nat.lt_or_ge t 2 with ht | ht
  · rw [List.drop_eq_nil_of_le (by rw [length_line]; omega)]
    exact List.nil_suffix
  · rw [drop_line ht, drop_line (by omega)]
    exact line_suffix (by omega)

/-- The tree properties: common prefix `2`, chain growth of one block per round, chain
quality `(evenBlock, 2, 1)`, and finality-respecting positions. -/
def lineP : List (TreeTrace Unit ℕ → Prop) :=
  [fun X => X.CommonPrefix 2, fun X => X.ChainGrowth 1 1, fun X => X.ChainQuality evenBlock 2 1,
    fun X => X.FinalityRespectingPos]

theorem lineP_stable : ∀ φ ∈ lineP, Stable φ := by
  simp only [lineP, List.mem_cons, List.not_mem_nil, or_false]
  rintro φ (rfl | rfl | rfl | rfl)
  exacts [stable_commonPrefix 2, stable_chainGrowth 1 1, stable_chainQuality _ 2 1,
    stable_finalityRespectingPos]

theorem lineTT_wellFormed : lineTT.WellFormed lineTree :=
  ⟨fun _ _ _ _ h => (line_suffix h).subset, fun _ _ _ => List.Subset.refl _,
    lineTrace_chainsInTree, fun _ _ h => h⟩

theorem lineTT_P : ∀ φ ∈ lineP, φ lineTT := by
  simp only [lineP, List.mem_cons, List.not_mem_nil, or_false]
  rintro φ (rfl | rfl | rfl | rfl)
  · exact lineTrace_commonPrefix 2
  · intro _ _ t t' _ _ h
    simp only [lineTT, lineView, length_line] at h ⊢
    omega
  · exact lineTrace_chainQuality
  · exact kDeep_finalityRespecting (lineTrace_commonPrefix 2)

theorem lineTT_agreement : lineTT.Agreement lineTree :=
  fun _ _ _ _ b b' _ _ _ _ _ _ => le_total b b'

theorem lineTT_chainForming : lineTT.ChainForming lineTree :=
  (kDeep_positionRespecting lineTrace_chainsInTree (lineTrace_commonPrefix 2)).chainForming

theorem lineTT_deltaPropagated (Δ : ℕ) : lineTT.DeltaPropagated lineTree Δ := by
  rintro _ _ t t' b i _ _ ⟨C, hC, hl⟩ hr
  simp only [lineTT, lineView] at hr
  exact ⟨b, i, ⟨C, hC.trans (drop_two_line_suffix (by omega)), hl⟩, lineTree.anc_refl b⟩

theorem lineTT_kSupport : lineTT.KSupport 2 :=
  fun _ t _ i _ hb => ⟨(), t, i, le_rfl, trivial, hb⟩

theorem lineTT_validity : lineTT.Validity 1 := by
  rintro _ t b _ _ ⟨C, hC, -⟩
  refine ⟨Finset.univ, by simp, fun _ _ => ⟨trivial, t, le_rfl, ?_⟩⟩
  exact (hC.trans ((List.drop_suffix _ _).trans (List.drop_suffix _ _))).subset
    List.mem_cons_self

/-- The guard of `F_Tree^P` holds on `lineTT`. -/
theorem lineTT_fTreeGuard : FTreeGuard lineTree lineP lineTT :=
  ⟨lineTT_wellFormed, lineTT_P, lineTT_agreement⟩

/-- The guard of `F_FinTree^P'` with `2`-support holds on `lineTT`, for every `Δ`. -/
theorem lineTT_finTreeGuardK (Δ : ℕ) :
    FinTreeGuard lineTree lineP Δ (fun X => X.KSupport 2) lineTT :=
  ⟨lineTT_wellFormed, lineTT_P, lineTT_chainForming, lineTT_agreement, lineTT_deltaPropagated Δ,
    lineTT_kSupport⟩

/-- The guard of `F_FinTree^P'` with `1`-validity holds on `lineTT`, for every `Δ`. -/
theorem lineTT_finTreeGuardV (Δ : ℕ) :
    FinTreeGuard lineTree lineP Δ (fun X => X.Validity 1) lineTT :=
  ⟨lineTT_wellFormed, lineTT_P, lineTT_chainForming, lineTT_agreement, lineTT_deltaPropagated Δ,
    lineTT_validity⟩

/-- The state after `t` entries of a trace with one more entry. -/
theorem stAt_snoc {σ E O : Type} (s₀ : σ) (tr : Trace σ E O) (x : E × O × σ) (t : ℕ) :
    stAt s₀ (tr ++ [x]) t = if t ≤ tr.length then stAt s₀ tr t else x.2.2 := by
  split_ifs with h
  · exact stAt_append_of_le s₀ tr [x] h
  · simp [stAt, List.take_of_length_le (show (tr ++ [x]).length ≤ t by simp; omega)]

/-- A trace whose state after `t` entries is `min t (length)` has the tree trace
`lineTT` truncated at its length. -/
theorem traceOf_line {tr : Trace ℕ Ev (List ℕ)} (h : ∀ t, stAt 0 tr t = min t tr.length) :
    traceOf lineView (fun _ => True) 0 tr = lineTT.clamp tr.length := by
  simp only [traceOf, TreeTrace.clamp, lineTT, h]

/-- The invariant of the monitored run of `lineProto`: the flag is unset, the state is the
number of entries, and the state after `t` entries is `min t (length)`. -/
def LineInv (m : ℕ × Trace ℕ Ev (List ℕ) × Bool) : Prop :=
  m.2.2 = false ∧ m.1 = m.2.1.length ∧ ∀ t, stAt 0 m.2.1 t = min t m.2.1.length

/-- For a stable guard `G` that holds on `lineTT`, the guard of `treeFunc` fails on the real
trace of `lineProto` with probability `0` under every environment. -/
theorem line_guardFail {ζ : Type} {G : TreeTrace Unit ℕ → Prop} (hG : Stable G)
    (hl : G lineTT) (ex : List ℕ) (Z : Env (Strat ζ Ev (List ℕ)) ζ) :
    guardFail lineProto (treeFunc lineView (fun _ => True) G lineProto.init ex).guard Z = 0 := by
  unfold guardFail
  refine prBad_eq_zero_of_invariant _ _ LineInv ⟨rfl, rfl, fun t => by simp [stAt, monitor]⟩
    (fun m hm => hm.1) ?_ Z
  rintro ⟨s, tr, b⟩ e K h ⟨hb, hs, htr⟩ hK
  simp only at hb hs htr
  subst hb hs
  simp only [monitor, lineProto, SPComp.pure_bind]
  have htr' : ∀ t, stAt 0 (tr ++ [(e, line (tr.length + 1), tr.length + 1)]) t =
      min t (tr ++ [(e, line (tr.length + 1), tr.length + 1)]).length := by
    intro t
    rw [stAt_snoc, htr]
    simp only [List.length_append, List.length_singleton]
    split_ifs <;> omega
  refine hK _ _ ⟨?_, by simp, htr'⟩
  have hg : (treeFunc lineView (fun _ => True) G lineProto.init ex).guard
      (tr ++ [(e, line (tr.length + 1), tr.length + 1)]) = true := by
    rw [treeFunc_guard_iff]
    exact (traceOf_line htr') ▸ hG _ _ hl
  have hg' : (treeFunc lineView (fun _ => True) G 0 ex).guard
      (tr ++ [(e, line (tr.length + 1), tr.length + 1)]) = true := hg
  simp [hg']

/-- **Non-vacuity of `F_Tree^P`.** `lineProto` satisfies the hypothesis of `fTree_adv_eq_zero`
(losslessness), block `3` is final at height `3` at time `5` of `lineTT`, the guard of
`F_Tree^P` with common prefix, chain growth, chain quality and finality-respecting
positions holds on `lineTT`, and the copy simulator realizes `F_Tree^P` perfectly: every
environment has advantage `0`. -/
theorem lineProto_fTree_adv :
    (∀ s e, SPComp.NoFail (lineProto.step s e)) ∧ lineTT.finalized 5 () 3 3 ∧
      FTreeGuard lineTree lineP lineTT ∧
      ∀ (ζ : Type) (Z : Env (Strat ζ Ev (List ℕ)) ζ),
        adv lineProto (ideal (fTree lineView (fun _ => True) lineTree lineP lineProto.init [])
          lineProto) Z = 0 :=
  ⟨lineProto_noFail, ⟨[2, 1, 0], by decide, rfl⟩, lineTT_fTreeGuard, fun _ Z =>
    fTree_adv_eq_zero lineProto _ _ _ _ _ lineProto_noFail Z
      (line_guardFail ((stable_wellFormed _).and ((stable_all lineP_stable).and
        (stable_agreement _))) lineTT_fTreeGuard [] Z)⟩

/-- **Non-vacuity of `F_FinTree^P'`.** For every `Δ`, the guards of `F_FinTree^P'` with
`2`-support and with `1`-validity hold on `lineTT`, and the copy simulator realizes both
perfectly: every environment has advantage `0`. -/
theorem lineProto_finTree_adv (Δ : ℕ) :
    FinTreeGuard lineTree lineP Δ (fun X => X.KSupport 2) lineTT ∧
      FinTreeGuard lineTree lineP Δ (fun X => X.Validity 1) lineTT ∧
      (∀ (ζ : Type) (Z : Env (Strat ζ Ev (List ℕ)) ζ),
        adv lineProto (ideal (finTreeK lineView (fun _ => True) lineTree lineP Δ 2
          lineProto.init []) lineProto) Z = 0) ∧
      ∀ (ζ : Type) (Z : Env (Strat ζ Ev (List ℕ)) ζ),
        adv lineProto (ideal (finTreeV lineView (fun _ => True) lineTree lineP Δ 1
          lineProto.init []) lineProto) Z = 0 := by
  have hst : ∀ {supp : TreeTrace Unit ℕ → Prop}, Stable supp →
      Stable (FinTreeGuard lineTree lineP Δ supp) := fun hs =>
    (stable_wellFormed _).and ((stable_all lineP_stable).and ((stable_chainForming _).and
      ((stable_agreement _).and ((stable_deltaPropagated _ Δ).and hs))))
  exact ⟨lineTT_finTreeGuardK Δ, lineTT_finTreeGuardV Δ,
    fun _ Z => finTree_adv_eq_zero lineProto _ _ _ _ _ _ _ lineProto_noFail Z
      (line_guardFail (hst (stable_kSupport 2)) (lineTT_finTreeGuardK Δ) [] Z),
    fun _ Z => finTree_adv_eq_zero lineProto _ _ _ _ _ _ _ lineProto_noFail Z
      (line_guardFail (hst (stable_validity 1)) (lineTT_finTreeGuardV Δ) [] Z)⟩

end Example

end CatCryptCore.Consensus.UC.FTree
