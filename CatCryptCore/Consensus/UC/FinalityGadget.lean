/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.UC.FTree
public import CatCryptCore.Consensus.FinalityValidity

@[expose] public section
set_option autoImplicit false

/-!
# The FFG finality gadget over tree positions

The Casper FFG finality gadget as a transition on the positions of the tree functionality
`F_Tree` of `CatCryptCore.Consensus.UC.FTree`, and the trace
theorem behind its realization of `F_FinTree` (`CatCryptCore.Consensus.UC.Finality`). This
file contains no probability: it is the information-theoretic core of the realization.

## The gadget

The validators are the parties of the tree (`Party`, a `Fintype`), with stake `w`; the honest
validators are the set `H`, the others are adversarial. A gadget state (`GCore`) consists of
the current tree view (round, trees and positions of the parties), the cast votes together
with the round in which each was cast, and the votes each party has received. One gadget step
(`gstep`) takes the new tree view and one action (`GAct`):

* `hvote x`: the honest validator `x.validator` casts `x` if both checkpoints of `x` are
  epoch-boundary checkpoints (`IsCheckpointOf`) of its pruned position `cut v x.validator` and
  `x` does not make it slashable (slashing protection) (`HonestOK`);
* `avote x`: an adversarial validator casts an arbitrary vote;
* `deliver p x`: the adversary delivers a cast vote early to `p`;

and then delivers every vote cast at least `Δ` rounds ago to every party (synchrony).

Party `p` regards as final the blocks of the checkpoints that are finalized (`FFG.Finalized`)
by the votes it has received; its list of final blocks (`finList`) lists them by epoch, newest
first. `finView` is the view reported to `F_FinTree`: the tree view with these final lists.

## Main results

* `Run`: the hypotheses on a sequence of gadget states: empty start, gadget steps or
  stuttering between consecutive times, monotone rounds, and `Settled`: the pruned position
  of an honest party at `t` is a suffix of the position of every honest party at every later
  time (for `cut v p = (v.pos p).drop k` this is common prefix `k`).
* `FinalOnHonestPos`, `FinalOnHonestPos.agree`: a block final for an honest party lies on the
  position of every honest party at every later time; hence any two blocks final for honest
  parties lie on one honest position.
* `Run.honest_unslashable`, `Run.honest_onChain`, `Run.seen_subset`, `Run.overdue_seen`: the
  invariants of the gadget (slashing protection, voting on the pruned position, synchrony).
* `Run.anc_of_finalized`, `Run.finalized_unique`: accountable safety
  (`FFG.anc_of_kFinalized_of_justified`, `FFG.slashable_of_justified_same_epoch`) applied to the
  cast votes when `3 * stake w (univ \ H) < W`.
* `Run.validity`: v-validity (`Finality.finalized_validity`): a block final for an
  honest party at `t` lies on the pruned positions of honest validators `S` with
  `2 W ≤ 3 stake S + 3 stake (univ \ H)`, each at a time at most `t`.
* `finTreeGuard_of_run` (headline): when `1 ≤ Δ` and `3 * stake w (univ \ H) < W`, the tree
  trace reported by the gadget satisfies the guard of `F_FinTree^P'` with
  `P' = finality-respecting positions :: FinalOnHonestPos :: P` and the support guard
  `v`-validity with `v = 1`
  together with stake validity, provided the positions are well formed and satisfy `P`
  (`P` reading only rounds, trees and positions, `PosOnly`).

## Modelling choices

* Votes are authenticated: the adversary casts votes only for adversarial validators.
* The gadget has no fork choice of its own. Finality-respecting positions and
  `FinalOnHonestPos` follow from voting on pruned positions and `Settled`, as in Enig's
  composition of a finality layer with a tree whose common prefix holds.
* `FinalOnHonestPos` states agreement of final blocks through the honest positions; it does
  not refer to the block tree `T`, so it is informative also when `T` relates every two
  blocks.
* `Finality.finality_updated` is a liveness statement (a finalized checkpoint close
  to the tip after `GST`); `F_FinTree` enforces only safety guards, and its `Δ`-updatedness
  (`TreeTrace.DeltaUpdated`: a final block reaches every honest party within `Δ` rounds)
  follows here from the synchronous delivery of votes and the monotonicity of finalization.
-/

namespace CatCryptCore.Consensus.UC.FFGGadget

open CatCryptCore.Consensus.UC.FTree CatCryptCore.Consensus.Finality FFG

/-! ## Trace properties -/

section Props

variable {Party Blk : Type}

/-- The tree trace `X` with the final lists replaced by `f`. -/
def withFin (X : TreeTrace Party Blk) (f : ℕ → Party → List Blk) : TreeTrace Party Blk :=
  ⟨X.honest, fun t => { X.st t with fin := f t }⟩

/-- A trace property reads only rounds, trees and positions: it is preserved by replacing the
final lists. -/
def PosOnly (φ : TreeTrace Party Blk → Prop) : Prop :=
  ∀ X f, φ X → φ (withFin X f)

/-- The pruned positions are settled: for honest `p`, `q` and times `t ≤ t'`, the pruned
position `cut (X.st t) p` is a suffix of the position of `q` at `t'`. -/
def Settled (cut : TreeView Party Blk → Party → List Blk) (X : TreeTrace Party Blk) : Prop :=
  ∀ p q t t', X.honest p → X.honest q → t ≤ t' → cut (X.st t) p <:+ (X.st t').pos q

/-- Stake validity with adversarial stake `a`: a block final for an honest party at `t` lies
on the positions of honest parties `S`, each at some time at most `t`, with
`2 W ≤ 3 stake S + 3 a`. -/
def StakeValidity [Fintype Party] (w : Party → ℕ) (a : ℕ) (X : TreeTrace Party Blk) : Prop :=
  ∀ p t b i, X.honest p → X.finalized t p b i →
    ∃ S : Finset Party, 2 * totalStake w ≤ 3 * stake w S + 3 * a ∧
      ∀ q ∈ S, X.honest q ∧ ∃ t₀ ≤ t, b ∈ (X.st t₀).pos q

/-- Common prefix `k` is settledness of the positions without their newest `k` blocks. -/
theorem settled_drop_iff (k : ℕ) (X : TreeTrace Party Blk) :
    Settled (fun v p => (v.pos p).drop k) X ↔ X.CommonPrefix k := Iff.rfl

/-- Final blocks lie on the honest positions: a block final for an honest party at `t` lies
on the position of every honest party at every time `t' ≥ t`. -/
def FinalOnHonestPos (X : TreeTrace Party Blk) : Prop :=
  ∀ p q t t' b i, X.honest p → X.honest q → t ≤ t' → X.finalized t p b i → b ∈ (X.st t').pos q

theorem stable_finalOnHonestPos :
    Stable (fun X : TreeTrace Party Blk => FinalOnHonestPos X) :=
  fun _ n h p q _ _ b i hp hq htt hb => h p q _ _ b i hp hq (min_le_min_right n htt) hb

/-- Final blocks on the honest positions are finality-respecting positions. -/
theorem FinalOnHonestPos.finalityRespectingPos {X : TreeTrace Party Blk}
    (h : FinalOnHonestPos X) : X.FinalityRespectingPos :=
  fun p t t' b i hp htt hb => h p p t t' b i hp hp htt hb

/-- **Agreement on the honest positions.** If final blocks lie on the honest positions, then
any two blocks final for honest parties `p` at `t` and `q` at `t'` both lie on the position of
every honest party `r` at time `max t t'`: they are on one chain selected by an honest
party. -/
theorem FinalOnHonestPos.agree {X : TreeTrace Party Blk} (h : FinalOnHonestPos X)
    {p q r : Party} {t t' i j : ℕ} {b b' : Blk} (hp : X.honest p) (hq : X.honest q)
    (hr : X.honest r) (hb : X.finalized t p b i) (hb' : X.finalized t' q b' j) :
    b ∈ (X.st (max t t')).pos r ∧ b' ∈ (X.st (max t t')).pos r :=
  ⟨h p r t _ b i hp hr (le_max_left t t') hb, h q r t' _ b' j hq hr (le_max_right t t') hb'⟩

theorem stable_stakeValidity [Fintype Party] (w : Party → ℕ) (a : ℕ) :
    Stable (fun X : TreeTrace Party Blk => StakeValidity w a X) := by
  intro X n h p t b i hp hb
  obtain ⟨S, hS, hq⟩ := h p _ b i hp hb
  refine ⟨S, hS, fun q hqS => ⟨(hq q hqS).1, ?_⟩⟩
  obtain ⟨t₀, h₀, hm⟩ := (hq q hqS).2
  exact ⟨t₀, h₀.trans (min_le_left _ _), by simpa [TreeTrace.clamp, min_eq_of_le_min h₀] using hm⟩

end Props

/-! ## Gadget states and steps -/

/-- The actions of one gadget step: nothing, an honest vote, an adversarial vote, or the early
delivery of a vote to a party. -/
inductive GAct (Party Blk : Type) where
  | idle
  | hvote (x : Vote Party Blk)
  | avote (x : Vote Party Blk)
  | deliver (p : Party) (x : Vote Party Blk)

/-- A gadget state: the tree view, the cast votes with their rounds, and the votes received
by each party. -/
structure GCore (Party Blk : Type) where
  /-- The current tree view (the final lists of this view are not used). -/
  view : TreeView Party Blk
  /-- The cast votes, each with the round in which it was cast. -/
  cast : Finset (Vote Party Blk × ℕ)
  /-- The votes received by each party. -/
  seen : Party → Finset (Vote Party Blk)

/-- The parameters of the gadget: block tree, stake, honest validators, slots, epoch length,
pruning of positions and delivery bound. -/
structure Cfg (Party Blk : Type) where
  /-- The block tree. -/
  T : BlockTree Blk
  /-- The stake of each validator. -/
  w : Party → ℕ
  /-- The honest validators. -/
  H : Finset Party
  /-- The slot of each block. -/
  slot : Blk → ℕ
  /-- The number of slots per epoch. -/
  E : ℕ
  /-- The pruned position on which a party votes. -/
  cut : TreeView Party Blk → Party → List Blk
  /-- The delivery bound in rounds. -/
  Δ : ℕ

variable {Party Blk : Type} [Fintype Party] [DecidableEq Party] [DecidableEq Blk]

/-- The cast votes without rounds. -/
def GCore.votes (g : GCore Party Blk) : Finset (Vote Party Blk) := g.cast.image Prod.fst

/-- The initial gadget state with tree view `v₀`: no votes. -/
def ginit (v₀ : TreeView Party Blk) : GCore Party Blk := ⟨v₀, ∅, fun _ => ∅⟩

/-- The honest voting rule: `x.validator` is honest, both checkpoints of `x` are
epoch-boundary checkpoints of its pruned position in the view `v`, and casting `x` after `S`
does not make it slashable. -/
def HonestOK (c : Cfg Party Blk) (v : TreeView Party Blk) (S : Finset (Vote Party Blk))
    (x : Vote Party Blk) : Prop :=
  x.validator ∈ c.H ∧ IsCheckpointOf c.slot c.E (c.cut v x.validator) x.source ∧
    IsCheckpointOf c.slot c.E (c.cut v x.validator) x.target ∧
    x.validator ∉ slashable (insert x S)

open Classical in
/-- One action on the gadget state `g` (whose view is already the new one). -/
noncomputable def act (c : Cfg Party Blk) (g : GCore Party Blk) :
    GAct Party Blk → GCore Party Blk
  | .idle => g
  | .hvote x =>
    if HonestOK c g.view g.votes x then { g with cast := insert (x, g.view.round) g.cast } else g
  | .avote x => if x.validator ∉ c.H then { g with cast := insert (x, g.view.round) g.cast } else g
  | .deliver p x =>
    if x ∈ g.votes then { g with seen := fun q => if q = p then insert x (g.seen q) else g.seen q }
    else g

/-- The votes of `C` cast at least `Δ` rounds before round `r`. -/
def overdue (Δ r : ℕ) (C : Finset (Vote Party Blk × ℕ)) : Finset (Vote Party Blk) :=
  (C.filter fun y => y.2 + Δ ≤ r).image Prod.fst

/-- **The gadget step**: adopt the tree view `v`, perform the action `a`, and deliver every
vote cast at least `Δ` rounds ago to every party. -/
noncomputable def gstep (c : Cfg Party Blk) (g : GCore Party Blk) (a : GAct Party Blk)
    (v : TreeView Party Blk) : GCore Party Blk :=
  let g₁ := act c { g with view := v } a
  { g₁ with seen := fun q => g₁.seen q ∪ overdue c.Δ v.round g₁.cast }

theorem act_spec (c : Cfg Party Blk) (g : GCore Party Blk) (a : GAct Party Blk) :
    (act c g a).view = g.view ∧
      ((act c g a).cast = g.cast ∨ ∃ x, (act c g a).cast = insert (x, g.view.round) g.cast ∧
        (HonestOK c g.view g.votes x ∨ x.validator ∉ c.H)) ∧
      ∀ q, (act c g a).seen q ⊆ g.seen q ∪ g.votes := by
  cases a with
  | idle => exact ⟨rfl, Or.inl rfl, fun _ => Finset.subset_union_left⟩
  | hvote x =>
    dsimp only [act]
    split_ifs with hx
    · exact ⟨rfl, Or.inr ⟨x, rfl, Or.inl hx⟩, fun _ => Finset.subset_union_left⟩
    · exact ⟨rfl, Or.inl rfl, fun _ => Finset.subset_union_left⟩
  | avote x =>
    dsimp only [act]
    split_ifs with hx
    · exact ⟨rfl, Or.inl rfl, fun _ => Finset.subset_union_left⟩
    · exact ⟨rfl, Or.inr ⟨x, rfl, Or.inr hx⟩, fun _ => Finset.subset_union_left⟩
  | deliver p x =>
    dsimp only [act]
    split_ifs with hx
    · refine ⟨rfl, Or.inl rfl, fun q => ?_⟩
      dsimp only
      split_ifs
      · intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact Finset.mem_union_right _ hx
        · exact Finset.mem_union_left _ hy
      · exact Finset.subset_union_left
    · exact ⟨rfl, Or.inl rfl, fun _ => Finset.subset_union_left⟩

theorem gstep_view (c : Cfg Party Blk) (g : GCore Party Blk) (a : GAct Party Blk)
    (v : TreeView Party Blk) : (gstep c g a v).view = v :=
  (act_spec c { g with view := v } a).1

theorem gstep_cast (c : Cfg Party Blk) (g : GCore Party Blk) (a : GAct Party Blk)
    (v : TreeView Party Blk) : (gstep c g a v).cast = (act c { g with view := v } a).cast := rfl

theorem gstep_seen (c : Cfg Party Blk) (g : GCore Party Blk) (a : GAct Party Blk)
    (v : TreeView Party Blk) (q : Party) :
    (gstep c g a v).seen q = (act c { g with view := v } a).seen q ∪
      overdue c.Δ v.round (act c { g with view := v } a).cast := rfl

/-- A vote of another validator does not make `v` slashable. -/
theorem not_mem_slashable_insert {S : Finset (Vote Party Blk)} {x : Vote Party Blk} {v : Party}
    (hv : v ∉ slashable S) (hx : x.validator ≠ v) : v ∉ slashable (insert x S) := by
  rw [mem_slashable] at hv ⊢
  rintro (⟨y, hy, z, hz, hyv, hzv, hne, he⟩ | ⟨y, hy, z, hz, hyv, hzv, h₁, h₂, h₃⟩)
  · rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hx hyv
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hx hzv
    exact hv (Or.inl ⟨y, hy, z, hz, hyv, hzv, hne, he⟩)
  · rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hx hyv
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hx hzv
    exact hv (Or.inr ⟨y, hy, z, hz, hyv, hzv, h₁, h₂, h₃⟩)

/-! ## Final lists -/

/-- The largest target epoch of the votes `S`. -/
def maxEp (S : Finset (Vote Party Blk)) : ℕ := S.sup fun x => x.target.epoch

open Classical in
/-- The block finalized by `S` at epoch `e`, if any (chosen when there are several). -/
noncomputable def finAt (c : Cfg Party Blk) (S : Finset (Vote Party Blk)) (e : ℕ) : Option Blk :=
  if h : ∃ b, Finalized c.T c.w S ⟨b, e⟩ then some h.choose else none

/-- The final list of a party that has received the votes `S`: the blocks finalized by `S`,
by epoch, newest first. -/
noncomputable def finList (c : Cfg Party Blk) (S : Finset (Vote Party Blk)) : List Blk :=
  (List.range (maxEp S + 1)).reverse.filterMap (finAt c S)

/-- The view reported to `F_FinTree`: the tree view of `g` with the final lists of the gadget. -/
noncomputable def finView (c : Cfg Party Blk) (g : GCore Party Blk) : TreeView Party Blk :=
  { g.view with fin := fun p => finList c (g.seen p) }

theorem finAt_some {c : Cfg Party Blk} {S : Finset (Vote Party Blk)} {e : ℕ} {b : Blk}
    (h : finAt c S e = some b) : Finalized c.T c.w S ⟨b, e⟩ := by
  unfold finAt at h
  split_ifs at h with hb
  cases h
  exact hb.choose_spec

theorem finalized_of_mem_finList {c : Cfg Party Blk} {S : Finset (Vote Party Blk)} {b : Blk}
    (h : b ∈ finList c S) : ∃ e, Finalized c.T c.w S ⟨b, e⟩ := by
  obtain ⟨e, -, he⟩ := List.mem_filterMap.1 h
  exact ⟨e, finAt_some he⟩

/-- A checkpoint finalized by `S`, for positive total stake, lies below the largest target
epoch of `S`. -/
theorem epoch_lt_maxEp {c : Cfg Party Blk} {S : Finset (Vote Party Blk)} {cp : Checkpoint Blk}
    (hW : 0 < totalStake c.w) (h : Finalized c.T c.w S cp) : cp.epoch < maxEp S + 1 := by
  obtain ⟨-, c', he, hl⟩ := h
  rcases (voters S cp c').eq_empty_or_nonempty with h0 | ⟨v, hv⟩
  · have := hl.2.2
    rw [h0] at this
    simp [stake] at this
    omega
  · have := Finset.le_sup (f := fun x : Vote Party Blk => x.target.epoch) (mem_voters.1 hv)
    simp only at this
    unfold maxEp
    omega

/-- A block finalized by `S` at epoch `e`, the only one at that epoch, is in the final list. -/
theorem mem_finList {c : Cfg Party Blk} {S : Finset (Vote Party Blk)} {b : Blk} {e : ℕ}
    (hW : 0 < totalStake c.w) (h : Finalized c.T c.w S ⟨b, e⟩)
    (huniq : ∀ b', Finalized c.T c.w S ⟨b', e⟩ → b' = b) : b ∈ finList c S := by
  refine List.mem_filterMap.2 ⟨e, ?_, ?_⟩
  · rw [List.mem_reverse, List.mem_range]
    exact epoch_lt_maxEp hW h
  · have hex : ∃ b, Finalized c.T c.w S ⟨b, e⟩ := ⟨b, h⟩
    rw [finAt, dif_pos hex, huniq _ hex.choose_spec]

/-- If finalized blocks are ordered by ancestry as by epoch, the final list is a chain: every
block is an ancestor of the blocks before it. -/
theorem finList_pairwise {c : Cfg Party Blk} {S : Finset (Vote Party Blk)}
    (hanc : ∀ b b' e e', Finalized c.T c.w S ⟨b, e⟩ → Finalized c.T c.w S ⟨b', e'⟩ → e ≤ e' →
      c.T.anc b b') :
    (finList c S).Pairwise fun b b' => c.T.anc b' b := by
  unfold finList
  rw [List.pairwise_filterMap]
  refine (List.pairwise_reverse.2 (List.pairwise_lt_range (n := maxEp S + 1))).imp ?_
  intro e e' hlt b hb b' hb'
  exact hanc _ _ _ _ (finAt_some hb') (finAt_some hb) hlt.le

/-! ## Runs of the gadget -/

/-- The positions of the gadget states `G` as a tree trace (with the final lists of the tree
views). -/
def posTT (c : Cfg Party Blk) (G : ℕ → GCore Party Blk) : TreeTrace Party Blk :=
  ⟨fun p => p ∈ c.H, fun t => (G t).view⟩

/-- The tree trace reported by the gadget to `F_FinTree`. -/
noncomputable def finTT (c : Cfg Party Blk) (G : ℕ → GCore Party Blk) : TreeTrace Party Blk :=
  ⟨fun p => p ∈ c.H, fun t => finView c (G t)⟩

theorem finTT_eq (c : Cfg Party Blk) (G : ℕ → GCore Party Blk) :
    finTT c G = withFin (posTT c G) (fun t p => finList c ((G t).seen p)) := rfl

/-- A run of the gadget: no votes at time `0`; between consecutive times either nothing
changes or one gadget step is taken; the rounds of the views do not decrease; and the pruned
positions are settled. -/
structure Run (c : Cfg Party Blk) (G : ℕ → GCore Party Blk) : Prop where
  init_cast : (G 0).cast = ∅
  init_seen : ∀ p, (G 0).seen p = ∅
  step : ∀ t, G (t + 1) = G t ∨ ∃ a v, G (t + 1) = gstep c (G t) a v
  rounds : (posTT c G).RoundsMonotone
  settled : Settled c.cut (posTT c G)

namespace Run

variable {c : Cfg Party Blk} {G : ℕ → GCore Party Blk} (h : Run c G)
include h

theorem cast_succ (t : ℕ) : (G t).cast ⊆ (G (t + 1)).cast := by
  rcases h.step t with e | ⟨a, v, e⟩
  · rw [e]
  · rw [e, gstep_cast]
    rcases (act_spec c { G t with view := v } a).2.1 with hc | ⟨x, hc, -⟩
    · rw [hc]
    · rw [hc]; exact Finset.subset_insert _ _

/-- The cast votes only grow. -/
theorem cast_mono {t t' : ℕ} (htt : t ≤ t') : (G t).cast ⊆ (G t').cast := by
  induction t', htt using Nat.le_induction with
  | base => exact subset_rfl
  | succ t' _ ih => exact ih.trans (h.cast_succ t')

theorem votes_mono {t t' : ℕ} (htt : t ≤ t') : (G t).votes ⊆ (G t').votes :=
  Finset.image_subset_image (h.cast_mono htt)

theorem round_succ (t : ℕ) : (G t).view.round ≤ (G (t + 1)).view.round :=
  h.rounds t (t + 1) (Nat.le_succ t)

/-- Votes are cast at the current round or earlier. -/
theorem cast_round (t : ℕ) : ∀ y ∈ (G t).cast, y.2 ≤ (G t).view.round := by
  induction t with
  | zero => simp [h.init_cast]
  | succ t ih =>
    have hr := h.round_succ t
    rcases h.step t with e | ⟨a, v, e⟩
    · rw [e] at hr ⊢; exact ih
    · rw [e, gstep_view] at hr ⊢
      intro y hy
      rw [gstep_cast] at hy
      rcases (act_spec c { G t with view := v } a).2.1 with hc | ⟨x, hc, -⟩
      · rw [hc] at hy; exact (ih y hy).trans hr
      · rw [hc] at hy
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact le_rfl
        · exact (ih y hy).trans hr

/-- Every party has received only cast votes. -/
theorem seen_subset (t : ℕ) : ∀ p, (G t).seen p ⊆ (G t).votes := by
  induction t with
  | zero => intro p; simp [h.init_seen]
  | succ t ih =>
    have hv := h.votes_mono (Nat.le_succ t)
    rcases h.step t with e | ⟨a, v, e⟩
    · rw [e]; exact ih
    · rw [e] at hv ⊢
      intro p x hx
      rw [gstep_seen, Finset.mem_union] at hx
      rcases hx with hx | hx
      · rcases Finset.mem_union.1 ((act_spec c { G t with view := v } a).2.2 p hx) with hx | hx
        · exact hv (ih p hx)
        · exact hv hx
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
        exact Finset.mem_image_of_mem _ (Finset.mem_filter.1 hy).1

/-- Synchrony: a vote cast at least `Δ` rounds ago has been received by every party. -/
theorem overdue_seen (t : ℕ) :
    ∀ y ∈ (G t).cast, y.2 + c.Δ ≤ (G t).view.round → ∀ q, y.1 ∈ (G t).seen q := by
  induction t with
  | zero => simp [h.init_cast]
  | succ t ih =>
    rcases h.step t with e | ⟨a, v, e⟩
    · rw [e]; exact ih
    · rw [e, gstep_view]
      intro y hy hle q
      rw [gstep_seen]
      exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨y, Finset.mem_filter.2 ⟨hy, hle⟩, rfl⟩)

/-- Slashing protection: no honest validator is slashable. -/
theorem honest_unslashable (t : ℕ) : ∀ v ∈ c.H, v ∉ slashable (G t).votes := by
  induction t with
  | zero => intro v _; simp [GCore.votes, h.init_cast, mem_slashable, DoubleVote, SurroundVote]
  | succ t ih =>
    rcases h.step t with e | ⟨a, v', e⟩
    · rw [e]; exact ih
    · rw [e]
      intro v hv
      unfold GCore.votes
      rw [gstep_cast]
      rcases (act_spec c { G t with view := v' } a).2.1 with hc | ⟨x, hc, hx⟩
      · rw [hc]; exact ih v hv
      · rw [hc, Finset.image_insert]
        rcases hx with hx | hx
        · by_cases hxv : x.validator = v
          · subst hxv; exact hx.2.2.2
          · exact not_mem_slashable_insert (ih v hv) hxv
        · exact not_mem_slashable_insert (ih v hv) fun h' => hx (h' ▸ hv)

/-- Honest validators vote on their pruned positions: every honest vote cast by time `t` has
epoch-boundary checkpoints of the pruned position of its validator at some time `t₀ ≤ t`. -/
theorem honest_onChain (t : ℕ) : ∀ x ∈ (G t).votes, x.validator ∈ c.H → ∃ t₀ ≤ t,
    IsCheckpointOf c.slot c.E (c.cut (G t₀).view x.validator) x.source ∧
      IsCheckpointOf c.slot c.E (c.cut (G t₀).view x.validator) x.target := by
  induction t with
  | zero => simp [GCore.votes, h.init_cast]
  | succ t ih =>
    intro x hx hxH
    rcases h.step t with e | ⟨a, v, e⟩
    · rw [e] at hx
      obtain ⟨t₀, ht₀, h₁⟩ := ih x hx hxH
      exact ⟨t₀, ht₀.trans (Nat.le_succ t), h₁⟩
    · have hx' := hx
      rw [e] at hx'
      unfold GCore.votes at hx'
      rw [gstep_cast] at hx'
      rcases (act_spec c { G t with view := v } a).2.1 with hc | ⟨y, hc, hy⟩
      · rw [hc] at hx'
        obtain ⟨t₀, ht₀, h₁⟩ := ih x hx' hxH
        exact ⟨t₀, ht₀.trans (Nat.le_succ t), h₁⟩
      · rw [hc, Finset.image_insert] at hx'
        rcases Finset.mem_insert.1 hx' with rfl | hx'
        · rcases hy with hy | hy
          · refine ⟨t + 1, le_rfl, ?_⟩
            rw [e, gstep_view]
            exact ⟨hy.2.1, hy.2.2.1⟩
          · exact absurd hxH hy
        · obtain ⟨t₀, ht₀, h₁⟩ := ih x hx' hxH
          exact ⟨t₀, ht₀.trans (Nat.le_succ t), h₁⟩

/-- A block final for party `p` at time `t` is finalized by the cast votes at some epoch. -/
theorem finalized_of_final {t : ℕ} {p : Party} {b : Blk} {i : ℕ}
    (hb : (finTT c G).finalized t p b i) : ∃ e, Finalized c.T c.w (G t).votes ⟨b, e⟩ := by
  obtain ⟨C, hC, -⟩ := hb
  obtain ⟨e, he⟩ := finalized_of_mem_finList (hC.subset List.mem_cons_self)
  exact ⟨e, Finalized.mono (h.seen_subset t p) he⟩

/-- **v-validity** (`Finality.finalized_validity`): a block final for party `p` at time `t`
lies on the pruned positions of honest validators `S` with
`2 W ≤ 3 stake S + 3 stake (univ \ H)`, each at some time at most `t`. -/
theorem validity {t : ℕ} {p : Party} {b : Blk} {i : ℕ} (hb : (finTT c G).finalized t p b i) :
    ∃ S ⊆ c.H, 2 * totalStake c.w ≤ 3 * stake c.w S + 3 * stake c.w (Finset.univ \ c.H) ∧
      ∀ q ∈ S, ∃ t₀ ≤ t, b ∈ c.cut (G t₀).view q := by
  obtain ⟨e, he⟩ := h.finalized_of_final hb
  let X : ChainTrace Party Blk := ⟨fun q => q ∈ c.H, fun t₁ q => c.cut (G (min t₁ t)).view q⟩
  have hvotes : HonestVotesOnChain X c.slot c.E (G t).votes := by
    intro x hx hxH
    obtain ⟨t₀, ht₀, h₁, h₂⟩ := h.honest_onChain t x hx hxH
    refine ⟨t₀, ?_, ?_⟩ <;> simpa [X, min_eq_left ht₀]
  obtain ⟨S, hSH, hS, hW⟩ := finalized_validity (X := X) (H := c.H) (fun _ hv => hv) hvotes he
  refine ⟨S, hSH, hW, fun q hq => ?_⟩
  obtain ⟨-, t₁, ht₁⟩ := hS q hq
  exact ⟨min t₁ t, min_le_right _ _, ht₁.mem⟩

/-! ### Accountable safety and validity on the cast votes -/

variable (hA : 3 * stake c.w (Finset.univ \ c.H) < totalStake c.w)
include hA

/-- The slashable validators of the cast votes hold less than a third of the stake. -/
theorem slashable_lt (t : ℕ) : 3 * stake c.w (slashable (G t).votes) < totalStake c.w := by
  have hsub : slashable (G t).votes ⊆ Finset.univ \ c.H := fun v hv =>
    Finset.mem_sdiff.2 ⟨Finset.mem_univ v, fun hvH => h.honest_unslashable t v hvH hv⟩
  have := stake_mono c.w hsub
  omega

/-- Accountable safety on the cast votes (`FFG.anc_of_kFinalized_of_justified`). -/
theorem anc_of_finalized {t : ℕ} {b b' : Blk} {e e' : ℕ}
    (hb : Finalized c.T c.w (G t).votes ⟨b, e⟩) (hb' : Finalized c.T c.w (G t).votes ⟨b', e'⟩)
    (hle : e ≤ e') : c.T.anc b b' :=
  anc_of_kFinalized_of_justified hb.kFinalized hb'.1 hle (h.slashable_lt hA t)

/-- At most one block is finalized per epoch by the cast votes
(`FFG.slashable_of_justified_same_epoch`). -/
theorem finalized_unique {t : ℕ} {b b' : Blk} {e : ℕ}
    (hb : Finalized c.T c.w (G t).votes ⟨b, e⟩) (hb' : Finalized c.T c.w (G t).votes ⟨b', e⟩) :
    b' = b := by
  by_contra hne
  have := slashable_of_justified_same_epoch hb'.1 hb.1 rfl fun h' => hne (congrArg (·.block) h')
  have := h.slashable_lt hA t
  omega

/-- The final list of every party is a chain of the block tree. -/
theorem finList_chain (t : ℕ) (p : Party) :
    (finList c ((G t).seen p)).Pairwise fun b b' => c.T.anc b' b :=
  finList_pairwise fun _ _ _ _ hb hb' hle =>
    h.anc_of_finalized hA (Finalized.mono (h.seen_subset t p) hb) (Finalized.mono (h.seen_subset t p) hb') hle

/-- A block final for an honest party at `t` was on the pruned position of an honest validator
at some time at most `t`. -/
theorem exists_honest_support {t : ℕ} {p : Party} {b : Blk} {i : ℕ}
    (hb : (finTT c G).finalized t p b i) :
    ∃ S ⊆ c.H, S.Nonempty ∧
      2 * totalStake c.w ≤ 3 * stake c.w S + 3 * stake c.w (Finset.univ \ c.H) ∧
      ∀ q ∈ S, ∃ t₀ ≤ t, b ∈ c.cut (G t₀).view q := by
  obtain ⟨S, hSH, hW, hS⟩ := h.validity hb
  refine ⟨S, hSH, ?_, hW, hS⟩
  rcases S.eq_empty_or_nonempty with h0 | hne
  · have h0' : stake c.w S = 0 := by rw [h0]; exact Finset.sum_empty
    omega
  · exact hne

end Run

/-! ## The guard of `F_FinTree` on runs -/

/-- **Runs of the gadget satisfy the guard of `F_FinTree`.** Let `1 ≤ Δ` and let the
adversarial validators hold less than a third of the stake, `3 * stake w (univ \ H) < W`. For
every run `G` of the gadget whose positions are well formed and satisfy every property of `P`,
where each property of `P` reads only rounds, trees and positions, the tree trace reported by
the gadget satisfies the guard of `F_FinTree^P'` with
`P' = finality-respecting positions :: FinalOnHonestPos :: P`, `Δ`-updatedness, and the
support guard `1`-validity together with stake validity for the adversarial stake. -/
theorem finTreeGuard_of_run {c : Cfg Party Blk} {G : ℕ → GCore Party Blk} (h : Run c G)
    (hΔ : 1 ≤ c.Δ) (hA : 3 * stake c.w (Finset.univ \ c.H) < totalStake c.w)
    {P : List (TreeTrace Party Blk → Prop)} (hP : ∀ φ ∈ P, PosOnly φ)
    (hwf : (posTT c G).WellFormed c.T) (hPG : ∀ φ ∈ P, φ (posTT c G)) :
    FinTreeGuard c.T ((fun X => X.FinalityRespectingPos) :: FinalOnHonestPos :: P) c.Δ
      (fun X => X.Validity 1 ∧ StakeValidity c.w (stake c.w (Finset.univ \ c.H)) X)
      (finTT c G) := by
  have hW : 0 < totalStake c.w := by omega
  have hon : FinalOnHonestPos (finTT c G) := by
    intro p r t t' b i _ hr htt hb
    obtain ⟨S, hSH, ⟨q, hq⟩, -, hS⟩ := h.exists_honest_support hA hb
    obtain ⟨t₀, ht₀, hm⟩ := hS q hq
    exact (h.settled q r t₀ t' (hSH hq) hr (ht₀.trans htt)).subset hm
  refine ⟨hwf, ?_, ?_, ?_, ?_, ?_⟩
  · -- finality-respecting positions, final blocks on honest positions, the properties of `P`
    rw [List.forall_mem_cons, List.forall_mem_cons]
    exact ⟨hon.finalityRespectingPos, hon, fun φ hφ => hP φ hφ _ _ (hPG φ hφ)⟩
  · -- chain-forming
    rintro p t b b' i j - ⟨C, hC, rfl⟩ ⟨C', hC', rfl⟩ hij
    exact anc_of_suffix_cons (h.finList_chain hA t p) hC hC' hij
  · -- agreement
    rintro p q t t' b b' i j - - hb hb'
    obtain ⟨e, he⟩ := h.finalized_of_final hb
    obtain ⟨e', he'⟩ := h.finalized_of_final hb'
    have h₁ := Finalized.mono (h.votes_mono (le_max_left t t')) he
    have h₂ := Finalized.mono (h.votes_mono (le_max_right t t')) he'
    rcases le_total e e' with hle | hle
    · exact Or.inl (h.anc_of_finalized hA h₁ h₂ hle)
    · exact Or.inr (h.anc_of_finalized hA h₂ h₁ hle)
  · -- `Δ`-updatedness
    rintro p q t t' b i - - hb hr
    change (G t).view.round + c.Δ ≤ (G t').view.round at hr
    have htt : t ≤ t' := by
      by_contra hlt
      have := h.rounds t' t (by omega)
      change (G t').view.round ≤ (G t).view.round at this
      omega
    obtain ⟨C, hC, -⟩ := hb
    obtain ⟨e, he⟩ := finalized_of_mem_finList (hC.subset List.mem_cons_self)
    have hsub : (G t).seen p ⊆ (G t').seen q := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 (h.seen_subset t p hx)
      have := h.cast_round t y hy
      exact h.overdue_seen t' y (h.cast_mono htt hy) (by omega) q
    have hq := Finalized.mono hsub he
    have hmem : b ∈ finList c ((G t').seen q) :=
      mem_finList hW hq fun b' hb' =>
        h.finalized_unique hA (Finalized.mono (h.seen_subset t' q) hq)
          (Finalized.mono (h.seen_subset t' q) hb')
    obtain ⟨s, l, hsl⟩ := List.append_of_mem hmem
    refine ⟨b, l.length, ⟨l, ?_, rfl⟩, c.T.anc_refl b⟩
    show b :: l <:+ finList c ((G t').seen q)
    rw [hsl]
    exact List.suffix_append s _
  · -- `1`-validity and stake validity
    refine ⟨fun p t b i _ hb => ?_, fun p t b i _ hb => ?_⟩
    · obtain ⟨S, hSH, hne, -, hS⟩ := h.exists_honest_support hA hb
      refine ⟨S, Finset.card_pos.2 hne, fun q hq => ⟨hSH hq, ?_⟩⟩
      obtain ⟨t₀, ht₀, hm⟩ := hS q hq
      exact ⟨t₀, ht₀, (h.settled q q t₀ t₀ (hSH hq) (hSH hq) le_rfl).subset hm⟩
    · obtain ⟨S, hSH, -, hW', hS⟩ := h.exists_honest_support hA hb
      refine ⟨S, hW', fun q hq => ⟨hSH hq, ?_⟩⟩
      obtain ⟨t₀, ht₀, hm⟩ := hS q hq
      exact ⟨t₀, ht₀, (h.settled q q t₀ t₀ (hSH hq) (hSH hq) le_rfl).subset hm⟩

end CatCryptCore.Consensus.UC.FFGGadget
