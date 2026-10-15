/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCTransparent
public import CatCryptCore.Consensus.Finality

@[expose] public section
set_option autoImplicit false

/-!
# The tree functionalities `F_Tree^P` and `F_FinTree^P'`

This file defines, as transparent functionalities in the sense of
`CatCrypt.Crypto.UCTransparent` (`TFunc`, `ideal`), the two functionalities of
Magri, Matt, Nielsen and Tschudi, *Enig* (ePrint 2022/201), §3:

* `F_Tree^P` (`fTree`): every party has a tree of blocks, a position (its selected
  chain) and a list of final blocks, whose head is its last final block. The adversary
  grows the trees, sets the positions and the final blocks; a change is accepted only if
  the extended trace satisfies every trace property in `P`, and final blocks of honest
  parties that are not on one chain (`TreeTrace.Agreement`) make the functionality
  explode.
* `F_FinTree^P'` (`finTree`): the same tree, where the adversary declares blocks final
  subject to the finality guards chain-forming, agreement, `Δ`-updated, and either
  `k`-support (`finTreeK`) or `v`-validity (`finTreeV`).

## Model

* `TreeView Party Blk` — the state of the functionality: round, tree, position and
  final blocks of every party. Lists of blocks are newest first, as in PoS-NSB and in
  `Consensus.Finality`; ancestry is an `FFG.BlockTree`.
* `TreeTrace` — an execution seen through the functionality: honest parties and the
  view at each time. `TreeTrace.chains` is the position trace and `TreeTrace.finalized`
  the finalization (block `b` final at position `i` when `b` is at height `i` in the
  final list), both in the vocabulary of `Consensus.Finality`.
* `traceOf vw honest s₀ tr` — the tree trace of a C1 trace `tr` whose states are mapped
  to views by `vw`; time `t` is the state after `t` activations, and times beyond the end
  of `tr` see the last state.
* `treeFunc vw honest G s₀ ex` — the transparent functionality with guard `G` on tree
  traces. Its state type `σ` is the state of the simulator; the functionality's own
  state is `vw s`. The guard depends on the trace only through the views.

## Trace properties

Reused from `Consensus.Finality` (row F1), applied to `chains` and `finalized`:
`CommonPrefix` (`ChainTrace.CommonPrefix`), `ChainQuality` (`ChainTrace.ChainQuality`),
positions in the block tree (`ChainTrace.ChainsInTree`, part of `WellFormed`),
finality-respecting positions (`Finality.FinalityRespecting`: a block final for an
honest party stays on its position), `ChainForming` (`Finality.ChainForming`),
`Agreement` (`Finality.Agreement`), and the depth predicate `Finality.kDeep` (for
`finalized` with depth `0` and for `KSupport`).

New here: `ChainGrowth` and `DeltaUpdated` measure time in rounds of the view (F1's
`ChainTrace.ChainGrowth` measures it in steps of the trace, and a finite trace extended
by its last state violates it), `KSupport` and `Validity` (the support guards of
`F_FinTree`), and the well-formedness conditions `TreesGrow`, `PositionsInTrees`,
`RoundsMonotone`.

Note on naming: F1's `PositionRespecting` (finality-respecting *positions* in the sense
of finalization indices) is a different property; Enig's finality-respecting positions
(a party's position extends its final blocks) is F1's `FinalityRespecting`.

## Main results

* `fTree_guard_iff`, `finTree_guard_iff` — the guards unfold to the stated properties.
* `fTree_guard_prefix`, `finTree_guard_prefix` — the guards are safety properties: a
  guard that holds on a trace holds on each of its prefixes, provided every property of
  `P` is stable under truncation (`Stable`); all properties defined here are
  (`stable_*`). Hence explosion in C1's `ideal` is permanent exactly as the trace
  property is violated permanently.
* `ideal_step_live`, `ideal_step_exploded` — one step of the ideal world: before
  explosion it outputs the simulator's output iff the extended trace satisfies the
  guard, and the designated exploded output otherwise.
* `fTree_realizes`, `finTree_realizes` — the copy simulator, which runs the protocol and
  copies its tree, position and final blocks into the functionality, realizes `F_Tree^P`
  and `F_FinTree^P'` with advantage at most the probability that the real trace violates
  the guard (instances of C1's `transparent_realizes_copy`, the up-to-bad lemma
  `adv_le_prBad` on the monitored run).
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
inconsistent `SetFinal` calls. C1's `ideal` has a single reaction to a guard failure:
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
(F1's `ChainsInTree`), and rounds do not decrease. -/
def WellFormed (T : BlockTree Blk) : Prop :=
  X.TreesGrow ∧ X.PositionsInTrees ∧ X.chains.ChainsInTree T ∧ X.RoundsMonotone

/-! ### Properties of the tree (the parameter `P` of `F_Tree^P`) -/

/-- Common prefix with parameter `k` of the positions (F1's `ChainTrace.CommonPrefix`). -/
def CommonPrefix (k : ℕ) : Prop := X.chains.CommonPrefix k

/-- Chain growth with `g` blocks per `s` rounds: if the round at `t'` is at least `s`
rounds after the round at `t`, the position of honest `q` at `t'` is at least `g` blocks
longer than the position of honest `p` at `t`. -/
def ChainGrowth (s g : ℕ) : Prop :=
  ∀ p q t t', X.honest p → X.honest q → (X.st t).round + s ≤ (X.st t').round →
    ((X.st t).pos p).length + g ≤ ((X.st t').pos q).length

/-- Chain quality of the positions (F1's `ChainTrace.ChainQuality`). -/
def ChainQuality (hb : Blk → Bool) (ℓ μ : ℕ) : Prop := X.chains.ChainQuality hb ℓ μ

/-- Finality-respecting positions: a block final for an honest party lies on its position
at every later time (F1's `FinalityRespecting`). -/
def FinalityRespectingPos : Prop := FinalityRespecting X.chains X.finalized

/-! ### Finality guards (the parameter `P'` of `F_FinTree^P'`) -/

/-- Chain-forming: the final blocks of an honest party at one time form a chain of `T`
(F1's `ChainForming`). -/
def ChainForming (T : BlockTree Blk) : Prop := Finality.ChainForming T X.chains X.finalized

/-- Agreement: all blocks final for honest parties lie on one chain of `T`
(F1's `Agreement`). -/
def Agreement (T : BlockTree Blk) : Prop := Finality.Agreement T X.chains X.finalized

/-- `Δ`-updated: if `b` is final for honest `p` at `t`, then at every time `t'` at least
`Δ` rounds later every honest `q` has a final block that `b` is an ancestor of. -/
def DeltaUpdated (T : BlockTree Blk) (Δ : ℕ) : Prop :=
  ∀ p q t t' b i, X.honest p → X.honest q → X.finalized t p b i →
    (X.st t).round + Δ ≤ (X.st t').round → ∃ b' j, X.finalized t' q b' j ∧ T.anc b b'

/-- `k`-support: a block final for an honest party at `t` was at least `k` deep in the
position of some honest party at some time `t₀ ≤ t` (via F1's `kDeep`). -/
def KSupport (k : ℕ) : Prop :=
  ∀ p t b i, X.honest p → X.finalized t p b i →
    ∃ q t₀ j, t₀ ≤ t ∧ X.honest q ∧ kDeep k X.chains t₀ q b j

/-- `v`-validity: a block final for an honest party at `t` was on the positions of at least
`v` honest parties, each at some time `t₀ ≤ t`. -/
def Validity (v : ℕ) : Prop :=
  ∀ p t b i, X.honest p → X.finalized t p b i →
    ∃ S : Finset Party, v ≤ S.card ∧ ∀ q ∈ S, X.honest q ∧ ∃ t₀ ≤ t, b ∈ (X.st t₀).pos q

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

theorem stable_deltaUpdated (T : BlockTree Blk) (Δ : ℕ) :
    Stable (fun X : TreeTrace Party Blk => X.DeltaUpdated T Δ) :=
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

/-- Conjunctions of stable properties are stable. -/
theorem Stable.and {φ ψ : TreeTrace Party Blk → Prop} (hφ : Stable φ) (hψ : Stable ψ) :
    Stable (fun X => φ X ∧ ψ X) :=
  fun X n h => ⟨hφ X n h.1, hψ X n h.2⟩

/-- The conjunction of a list of stable properties is stable. -/
theorem stable_all {P : List (TreeTrace Party Blk → Prop)} (hP : ∀ φ ∈ P, Stable φ) :
    Stable (fun X => ∀ φ ∈ P, φ X) :=
  fun X n h φ hφ => hP φ hφ X n (h φ hφ)

end Stable

/-! ## Tree traces of C1 traces and the functionalities -/

section Func

variable {Party Blk σ E O : Type}

/-- The state after the first `t` entries of the trace `tr`, from the initial state `s₀`;
for `t` beyond the length of `tr`, the last state. -/
def stAt (s₀ : σ) (tr : Trace σ E O) (t : ℕ) : σ :=
  ((tr.take t).getLast?.map fun x => x.2.2).getD s₀

/-- The tree trace of the C1 trace `tr`, with views `vw` and honest parties `honest`. -/
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
chain-forming, agreement, `Δ`-updated, and the support guard `supp`. -/
def FinTreeGuard (T : BlockTree Blk) (P : List (TreeTrace Party Blk → Prop)) (Δ : ℕ)
    (supp : TreeTrace Party Blk → Prop) (X : TreeTrace Party Blk) : Prop :=
  X.WellFormed T ∧ (∀ φ ∈ P, φ X) ∧ X.ChainForming T ∧ X.Agreement T ∧
    X.DeltaUpdated T Δ ∧ supp X

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
every property of `P`, and is chain-forming, in agreement, `Δ`-updated and supported. -/
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
      ((stable_agreement T).and ((stable_deltaUpdated T Δ).and hsupp))))) s₀ ex hpre h

end Func
end CatCryptCore.Consensus.UC.FTree
