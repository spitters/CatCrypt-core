/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.UC.FinalityGadget
public import CatCryptCore.Consensus.FinalityExamples
public import CatCryptCore.Crypto.UCTransparentHybrid

@[expose] public section
set_option autoImplicit false

/-!
# FFG in the `F_Tree`-hybrid world realizes `F_FinTree`

The Casper FFG finality gadget of `CatCryptCore.Consensus.UC.FinalityGadget`, run as a hybrid
protocol with one call per activation to the tree functionality `F_Tree^P` of
`CatCryptCore.Consensus.UC.FTree`, realizes the finality functionality `F_FinTree^P'` of the
same module perfectly (advantage `0` against every environment)
when the adversarial validators hold less than a third of the total stake `W`. The statement
is information-theoretic.

## The hybrid protocol

The subroutine is the ideal world `ideal (treeF …) ST` of `F_Tree^P` with an arbitrary lossless
tree simulator `ST` (for instance the PoS-NSB simulator `Chain.chainSim`). An outer
event is a pair of a tree event and a gadget action (`GAct`). The gadget (`ffgHybrid`) passes
the tree event to `F_Tree`, reads the tree view `ov o` from its output `o`, and takes one
gadget step (`gstep`) with that view and the action. If `F_Tree` answers with its exploded
output `exT`, the gadget stops for good (`GSt.dead`) and from then on outputs `exF`. Otherwise
it outputs `finView`: the tree view with the final lists of the gadget.

## The simulator and the functionality

`ffgSim` runs the gadget against `F_Tree` internally, with the tree simulator `ST`, and
proposes its states to `F_FinTree` (the copy simulator of `finTree_realizes` for the hybrid world).
`finF` is `F_FinTree^P'` over the states of the simulator, with the view `finView` of the
gadget component, `P' = finality-respecting positions :: FinalOnHonestPos :: P`, delivery
bound `Δ`, and the
support guard `1`-validity together with stake validity.

## Main results

* `inv_step`, `inv_init`: the invariant of the monitored run of the hybrid world: the guard of
  `F_FinTree` holds on the trace; while the gadget is live, `F_Tree` has not exploded, its
  trace satisfies the guard of `F_Tree`, the views of the gadget are the views of `F_Tree`,
  and the gadget states form a run (`FFGGadget.Run`).
* `guardFail_eq_zero`: the guard of `F_FinTree` never fails on the hybrid run.
* `ffg_realizes` (headline): under the hypotheses below, `ffgWorld` realizes
  `ideal (finF …) (ffgSim …)` with bound `0`.
* `ffg_UCEmulatesCSim`: the same as `UCConcrete.UCEmulatesCSim` with the zero bound.
* `Example.instance_hyps`, `Example.instance_realizes`, `Example.run_finalizes`: a one-validator
  instance satisfies every hypothesis (with `3 · 0 < W = 1`), and a run of its gadget
  finalizes the genesis block at time `2`.
* `ForkExample.instance_realizes`, `ForkExample.run_accountable`: an instance over `forkTree`
  with four validators of stake `1`, validator `3` adversarial, satisfies every hypothesis;
  in a run of its gadget the adversarial validator votes for the conflicting block `2` and
  double-votes, it is the only slashable validator, block `1` is final for an honest party,
  and no two finalized checkpoints conflict.

## Hypotheses of the headline theorem

* `hST`: the tree simulator is lossless; `hout`, `hov`: its output is a function `out` of its
  new state, and the gadget reads from it the view of that state (`ov (out s) = vwT s`).
* `hinit`: the guard of `F_Tree` holds on the empty trace (the initial view is admissible).
* `hP`: every property of `P` reads only rounds, trees and positions (`PosOnly`).
* `hset`: the guard of `F_Tree` implies that the pruned positions are settled
  (`Settled cut`); for `cut v p = (v.pos p).drop k` this is common prefix `k` in `P`.
* `hΔ`: `1 ≤ Δ`; `hA`: `3 * stake w (univ \ H) < W`.

## Modelling choices

* The honest validators are both the honest parties of `F_Tree` and of `F_FinTree`
  (`· ∈ H`). Corruption is static.
* The simulator is the copy simulator: since the trace of the hybrid world always satisfies
  the guard of `F_FinTree`, the functionality never explodes and copying is exact. The
  realization theorems carry the tag of composition plumbing.
-/

namespace CatCryptCore.Consensus.UC.FFGGadget

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent
open CatCryptCore.Consensus.UC.FTree CatCryptCore.Consensus.Finality FFG
open scoped ENNReal

/-! ## The hybrid protocol -/

/-- The state of the gadget protocol: the gadget state, whether `F_Tree` has exploded, and
the pending action of the current activation. -/
structure GSt (Party Blk : Type) where
  /-- The gadget state. -/
  core : GCore Party Blk
  /-- Set once `F_Tree` has answered with its exploded output. -/
  dead : Bool
  /-- The action of the current activation. -/
  pend : GAct Party Blk

section Hybrid

variable {Party Blk : Type} [Fintype Party] [DecidableEq Party] [DecidableEq Blk]
variable {σT ET OT : Type}

open Classical in
/-- The gadget after the answer `o` of `F_Tree`: stop on the exploded output `exT`, otherwise
one gadget step with the view `ov o` and the pending action. -/
noncomputable def gpost (c : Cfg Party Blk) (exT : OT) (ov : OT → TreeView Party Blk)
    (g : GSt Party Blk) (o : OT) : GSt Party Blk :=
  if g.dead = true ∨ o = exT then { g with dead := true }
  else { g with core := gstep c g.core g.pend (ov o) }

/-- The output of the gadget: `exF` once stopped, otherwise the view with the final lists. -/
noncomputable def gout (c : Cfg Party Blk) (exF : TreeView Party Blk) (g : GSt Party Blk) :
    TreeView Party Blk :=
  if g.dead = true then exF else finView c g.core

variable (c : Cfg Party Blk) (ST : Sys σT ET OT) (vwT : σT → TreeView Party Blk)
  (P : List (TreeTrace Party Blk → Prop)) (exT : OT) (ov : OT → TreeView Party Blk)
  (exF : TreeView Party Blk)

/-- **The FFG gadget as a hybrid protocol** over `F_Tree`, with initial view `v₀`: an outer
event `(eT, a)` passes `eT` to `F_Tree` and then performs `gpost` with the action `a`. -/
noncomputable def ffgHybrid (v₀ : TreeView Party Blk) :
    Hybrid (GSt Party Blk) (ET × GAct Party Blk) (TreeView Party Blk) ET OT where
  init := ⟨ginit v₀, false, .idle⟩
  pre g e := SPComp.pure ({ g with pend := e.2 }, e.1)
  post g o := SPComp.pure (gpost c exT ov g o, gout c exF (gpost c exT ov g o))
  pre_noFail _ _ := SPComp.pure_noFail _
  post_noFail _ _ := SPComp.pure_noFail _

/-- `F_Tree^P` over the states of the tree simulator `ST`, with honest parties `H`. -/
noncomputable def treeF : TFunc σT ET OT :=
  fTree vwT (· ∈ c.H) c.T P ST.init exT

/-- **The `F_Tree`-hybrid world**: the gadget running with the ideal world of `F_Tree` and the
tree simulator `ST`. -/
noncomputable def ffgWorld :=
  (ffgHybrid c exT ov exF (vwT ST.init)).withSub (ideal (treeF c ST vwT P exT) ST)

variable (Party Blk σT ET OT) in
/-- The states of the hybrid world. -/
abbrev WSt := GSt Party Blk × (σT × Trace σT ET OT × Bool)

/-- **The simulator** for `F_FinTree`: it runs the gadget against `F_Tree` with the tree
simulator `ST` internally and proposes the resulting states (the copy simulator). -/
noncomputable def ffgSim : Sys (WSt Party Blk σT ET OT) (ET × GAct Party Blk) (TreeView Party Blk) :=
  ffgWorld c ST vwT P exT ov exF

/-- The support guard of `F_FinTree`: `1`-validity and stake validity for the adversarial
stake. -/
def suppF (X : TreeTrace Party Blk) : Prop :=
  X.Validity 1 ∧ StakeValidity c.w (stake c.w (Finset.univ \ c.H)) X

/-- **The functionality** `F_FinTree^P'` over the states of the simulator: view `finView` of
the gadget component, honest parties `H`,
`P' = finality-respecting positions :: FinalOnHonestPos :: P`, delivery bound `Δ`, support
guard `suppF`, exploded output `exF`. -/
noncomputable def finF :
    TFunc (WSt Party Blk σT ET OT) (ET × GAct Party Blk) (TreeView Party Blk) :=
  finTree (fun s => finView c s.1.core) (· ∈ c.H) c.T
    ((fun X => X.FinalityRespectingPos) :: FinalOnHonestPos :: P)
    c.Δ (suppF c) (ffgSim c ST vwT P exT ov exF).init exF

end Hybrid

/-! ## The invariant of the monitored hybrid run -/

section Invariant

variable {Party Blk : Type} [Fintype Party] [DecidableEq Party] [DecidableEq Blk]
variable {σT ET OT : Type}
variable {c : Cfg Party Blk} {ST : Sys σT ET OT} {vwT : σT → TreeView Party Blk}
  {P : List (TreeTrace Party Blk → Prop)} {exT : OT} {ov : OT → TreeView Party Blk}
  {exF : TreeView Party Blk}

/-- The state after `t` entries of a trace that extends `tr` by one entry. -/
theorem stAt_snoc' {σ E O : Type} (s₀ : σ) (tr : Trace σ E O) (x : E × O × σ) (t : ℕ) :
    stAt s₀ (tr ++ [x]) t = if t ≤ tr.length then stAt s₀ tr t else x.2.2 :=
  Example.stAt_snoc s₀ tr x t

/-- Beyond the length of the trace, the state is the last state. -/
theorem stAt_of_length_le {σ E O : Type} (s₀ : σ) (tr : Trace σ E O) {t : ℕ}
    (ht : tr.length ≤ t) : stAt s₀ tr t = stAt s₀ tr tr.length := by
  rw [← stAt_min_length s₀ tr t, min_eq_right ht]

omit [Fintype Party] [DecidableEq Party] [DecidableEq Blk] in
/-- Appending an entry whose state has the view of the last state does not change the tree
trace. -/
theorem traceOf_snoc_same {σ E O : Type} (vw : σ → TreeView Party Blk) (honest : Party → Prop)
    (s₀ : σ) (tr : Trace σ E O) (x : E × O × σ) (hx : vw x.2.2 = vw (stAt s₀ tr tr.length)) :
    traceOf vw honest s₀ (tr ++ [x]) = traceOf vw honest s₀ tr := by
  simp only [traceOf, TreeTrace.mk.injEq, true_and]
  funext t
  rw [stAt_snoc']
  split_ifs with ht
  · rfl
  · exact hx.trans (congrArg vw (stAt_of_length_le s₀ tr (t := t) (by omega)).symm)

/-- The gadget states along a trace of the hybrid world. -/
def coreAt (s₀ : WSt Party Blk σT ET OT) (tr : Trace (WSt Party Blk σT ET OT) (ET × GAct Party Blk)
    (TreeView Party Blk)) (t : ℕ) : GCore Party Blk :=
  (stAt s₀ tr t).1.core

/-- The step part of a run: no votes at time `0`, gadget steps or stuttering. -/
def RunSteps (c : Cfg Party Blk) (G : ℕ → GCore Party Blk) : Prop :=
  (G 0).cast = ∅ ∧ (∀ p, (G 0).seen p = ∅) ∧
    ∀ t, G (t + 1) = G t ∨ ∃ a v, G (t + 1) = gstep c (G t) a v

/-- **The guard of `F_FinTree` while `F_Tree` is live.** If the guard of `F_Tree` holds on its
trace `trT`, the views of the gadget states `G` are the views of that trace, and `G` makes
gadget steps, then the tree trace reported by the gadget satisfies the guard of
`F_FinTree^P'` (`finTreeGuard_of_run`). -/
theorem guard_of_live (hP : ∀ φ ∈ P, PosOnly φ)
    (hset : ∀ X, FTreeGuard c.T P X → Settled c.cut X) (hΔ : 1 ≤ c.Δ)
    (hA : 3 * stake c.w (Finset.univ \ c.H) < totalStake c.w) {s₀T : σT}
    {trT : Trace σT ET OT} (hG : FTreeGuard c.T P (traceOf vwT (· ∈ c.H) s₀T trT))
    {G : ℕ → GCore Party Blk} (hv : ∀ t, (G t).view = vwT (stAt s₀T trT t))
    (hrun : RunSteps c G) :
    FinTreeGuard c.T ((fun X => X.FinalityRespectingPos) :: FinalOnHonestPos :: P) c.Δ (suppF c)
      (finTT c G) := by
  have e : posTT c G = traceOf vwT (· ∈ c.H) s₀T trT := by
    simp only [posTT, traceOf, TreeTrace.mk.injEq, true_and]
    funext t
    exact hv t
  rw [← e] at hG
  exact finTreeGuard_of_run ⟨hrun.1, hrun.2.1, hrun.2.2, hG.1.2.2.2, hset _ hG⟩ hΔ hA hP
    hG.1 hG.2.1

variable (c ST vwT P exT ov exF) in
/-- The invariant of the monitored hybrid world: the flag is unset; the guard of `F_FinTree`
holds on the trace; the state is the last state of the trace; and while the gadget is live,
`F_Tree` has not exploded, its guard holds on its trace, the two traces have the same length,
the views of the gadget are the views of `F_Tree`, and the gadget makes gadget steps. -/
def MInv (m : WSt Party Blk σT ET OT ×
    Trace (WSt Party Blk σT ET OT) (ET × GAct Party Blk) (TreeView Party Blk) × Bool) : Prop :=
  m.2.2 = false ∧
    FinTreeGuard c.T ((fun X => X.FinalityRespectingPos) :: FinalOnHonestPos :: P) c.Δ (suppF c)
      (traceOf (fun s => finView c s.1.core) (· ∈ c.H) (ffgSim c ST vwT P exT ov exF).init m.2.1) ∧
    stAt (ffgSim c ST vwT P exT ov exF).init m.2.1 m.2.1.length = m.1 ∧
    (m.1.1.dead = false →
      m.1.2.2.2 = false ∧ (treeF c ST vwT P exT).guard m.1.2.2.1 = true ∧
      m.2.1.length = m.1.2.2.1.length ∧
      (∀ t, (coreAt (ffgSim c ST vwT P exT ov exF).init m.2.1 t).view =
        vwT (stAt ST.init m.1.2.2.1 t)) ∧
      RunSteps c (coreAt (ffgSim c ST vwT P exT ov exF).init m.2.1))

theorem stAt_nil {σ E O : Type} (s₀ : σ) (t : ℕ) : stAt s₀ ([] : Trace σ E O) t = s₀ := by
  simp [stAt]

/-! ### One activation of the monitored hybrid world -/

variable (Party Blk σT ET OT) in
/-- The monitored states of the hybrid world. -/
abbrev MSt := WSt Party Blk σT ET OT ×
  Trace (WSt Party Blk σT ET OT) (ET × GAct Party Blk) (TreeView Party Blk) × Bool

variable (c ST vwT P exT) in
/-- The new state of the ideal world of `F_Tree` when the tree simulator moves to `s'`
with output `out s'`. -/
noncomputable def treeNext (out : σT → OT) (m : MSt Party Blk σT ET OT) (e : ET × GAct Party Blk)
    (s' : σT) : σT × Trace σT ET OT × Bool :=
  (s', m.1.2.2.1 ++ [(e.1, out s', s')],
    m.1.2.2.2 || !(treeF c ST vwT P exT).guard (m.1.2.2.1 ++ [(e.1, out s', s')]))

variable (c ST vwT P exT) in
/-- The answer of `F_Tree` in that case. -/
noncomputable def treeOut (out : σT → OT) (m : MSt Party Blk σT ET OT) (e : ET × GAct Party Blk)
    (s' : σT) : OT :=
  if (treeNext c ST vwT P exT out m e s').2.2 then exT else out s'

variable (c ST vwT P exT ov exF) in
/-- The new monitored state when the tree simulator moves to `s'` and the gadget to `g'`. -/
noncomputable def monNext (out : σT → OT) (m : MSt Party Blk σT ET OT) (e : ET × GAct Party Blk)
    (s' : σT) (g' : GSt Party Blk) : MSt Party Blk σT ET OT :=
  ((g', treeNext c ST vwT P exT out m e s'),
    m.2.1 ++ [(e, gout c exF g', (g', treeNext c ST vwT P exT out m e s'))],
    m.2.2 || !(finF c ST vwT P exT ov exF).guard
      (m.2.1 ++ [(e, gout c exF g', (g', treeNext c ST vwT P exT out m e s'))]))

/-- One activation of the monitored hybrid world, when the step of the tree simulator is a
computation `C` of its next state followed by the output `out`. -/
theorem monitor_step_eq (out : σT → OT) (C : SPComp σT) (m : MSt Party Blk σT ET OT)
    (e : ET × GAct Party Blk)
    (hC : ST.step m.1.2.1 e.1 = SPComp.bind C fun s' => SPComp.pure (s', out s')) :
    (monitor (ffgWorld c ST vwT P exT ov exF) (finF c ST vwT P exT ov exF).guard).step m e =
      SPComp.bind C fun s' =>
        SPComp.pure (monNext c ST vwT P exT ov exF out m e s'
            (gpost c exT ov { m.1.1 with pend := e.2 } (treeOut c ST vwT P exT out m e s')),
          gout c exF (gpost c exT ov { m.1.1 with pend := e.2 } (treeOut c ST vwT P exT out m e s'))) := by
  simp only [monitor, ffgWorld, Hybrid.withSub, ffgHybrid, ideal, hC, SPComp.bind_assoc,
    SPComp.pure_bind]
  rfl

/-- The two outcomes of `gpost`: the gadget stops, or it is live and takes a gadget step. -/
theorem gpost_cases (c : Cfg Party Blk) (exT : OT) (ov : OT → TreeView Party Blk)
    (g : GSt Party Blk) (o : OT) :
    gpost c exT ov g o = { g with dead := true } ∨
      (g.dead = false ∧ o ≠ exT ∧ gpost c exT ov g o = { g with core := gstep c g.core g.pend (ov o) }) := by
  unfold gpost
  split_ifs with h
  · exact Or.inl rfl
  · rw [not_or] at h
    exact Or.inr ⟨by simpa using h.1, h.2, rfl⟩

variable (hST : ∀ s e, SPComp.NoFail (ST.step s e)) (out : σT → OT)
  (hov : ∀ s, ov (out s) = vwT s)
  (hinit : FTreeGuard c.T P (traceOf vwT (· ∈ c.H) ST.init ([] : Trace σT ET OT)))
  (hP : ∀ φ ∈ P, PosOnly φ) (hset : ∀ X, FTreeGuard c.T P X → Settled c.cut X) (hΔ : 1 ≤ c.Δ)
  (hA : 3 * stake c.w (Finset.univ \ c.H) < totalStake c.w)

include hinit hP hset hΔ hA in
/-- The invariant holds initially. -/
theorem inv_init :
    MInv c ST vwT P exT ov exF ((ffgWorld c ST vwT P exT ov exF).init, [], false) := by
  have hv : ∀ t, (coreAt (ffgSim c ST vwT P exT ov exF).init
      ([] : Trace (WSt Party Blk σT ET OT) (ET × GAct Party Blk) (TreeView Party Blk)) t).view =
      vwT (stAt ST.init ([] : Trace σT ET OT) t) := fun t => by
    simp only [coreAt, stAt_nil]; rfl
  have hrun : RunSteps c (coreAt (ffgSim c ST vwT P exT ov exF).init
      ([] : Trace (WSt Party Blk σT ET OT) (ET × GAct Party Blk) (TreeView Party Blk))) :=
    ⟨by simp only [coreAt, stAt_nil]; rfl, fun _ => by simp only [coreAt, stAt_nil]; rfl,
      fun t => Or.inl (by simp only [coreAt, stAt_nil])⟩
  refine ⟨rfl, guard_of_live hP hset hΔ hA hinit hv hrun, stAt_nil _ _, fun _ =>
    ⟨rfl, (treeFunc_guard_iff _ _ _ _ _ _).2 hinit, rfl, hv, hrun⟩⟩

include hov hP hset hΔ hA in
/-- The invariant is preserved by every activation, for every next state `s'` of the tree
simulator and every new gadget state `g'` that `gpost` can produce. -/
theorem inv_step_gen (m : MSt Party Blk σT ET OT) (e : ET × GAct Party Blk) (s' : σT)
    (hm : MInv c ST vwT P exT ov exF m) (g' : GSt Party Blk)
    (hg : g' = ⟨m.1.1.core, true, e.2⟩ ∨
      (m.1.1.dead = false ∧ treeOut c ST vwT P exT out m e s' ≠ exT ∧
        g' = ⟨gstep c m.1.1.core e.2 (ov (treeOut c ST vwT P exT out m e s')), m.1.1.dead, e.2⟩)) :
    MInv c ST vwT P exT ov exF (monNext c ST vwT P exT ov exF out m e s' g') := by
  obtain ⟨⟨g, sT, trT, fT⟩, tr, fl⟩ := m
  obtain ⟨hfl, hguard, hlast, hlive⟩ := hm
  simp only at hfl hguard hlast hlive hg
  subst hfl
  set s₀ := (ffgSim c ST vwT P exT ov exF).init
  set x : (ET × GAct Party Blk) × TreeView Party Blk × WSt Party Blk σT ET OT :=
    (e, gout c exF g', (g', treeNext c ST vwT P exT out ((g, sT, trT, fT), tr, false) e s'))
    with hx
  have hlen : (tr ++ [x]).length = tr.length + 1 := by simp
  have hlast' : stAt s₀ (tr ++ [x]) (tr ++ [x]).length = x.2.2 := by
    rw [stAt_snoc', if_neg (by simp)]
  have hgold : (stAt s₀ tr tr.length).1.core = g.core := by rw [hlast]
  have hguardF : ∀ tr' : Trace (WSt Party Blk σT ET OT) (ET × GAct Party Blk) (TreeView Party Blk),
      FinTreeGuard c.T ((fun X => X.FinalityRespectingPos) :: FinalOnHonestPos :: P) c.Δ (suppF c)
        (traceOf (fun s => finView c s.1.core) (· ∈ c.H) s₀ tr') →
      (finF c ST vwT P exT ov exF).guard tr' = true := fun tr' h' => by
    rw [finF, finTree_guard_iff]; exact h'
  rcases hg with rfl | ⟨hd, ho, rfl⟩
  · -- the gadget stops: the reported trace does not change
    have hsame : traceOf (fun s => finView c s.1.core) (· ∈ c.H) s₀ (tr ++ [x]) =
        traceOf (fun s => finView c s.1.core) (· ∈ c.H) s₀ tr :=
      traceOf_snoc_same _ _ s₀ tr x (by rw [hgold])
    refine ⟨?_, ?_, hlast', fun h => absurd h (by simp [monNext])⟩
    · show (false || !(finF c ST vwT P exT ov exF).guard (tr ++ [x])) = false
      rw [hguardF _ (hsame ▸ hguard)]; rfl
    · exact hsame ▸ hguard
  · -- the gadget is live
    obtain ⟨hfT, hgT, hlenT, hv, hrun⟩ := hlive hd
    subst hfT
    have hnext : (treeNext c ST vwT P exT out ((g, sT, trT, false), tr, false) e s').2.2 = false := by
      by_contra hc
      exact ho (by rw [treeOut, if_pos (by simpa using hc)])
    have hout' : treeOut c ST vwT P exT out ((g, sT, trT, false), tr, false) e s' = out s' := by
      rw [treeOut, if_neg (by simp [hnext])]
    have hgT' : (treeF c ST vwT P exT).guard (trT ++ [(e.1, out s', s')]) = true := by
      simpa [treeNext] using hnext
    have hGT : FTreeGuard c.T P (traceOf vwT (· ∈ c.H) ST.init (trT ++ [(e.1, out s', s')])) :=
      (treeFunc_guard_iff _ _ _ _ _ _).1 hgT'
    have hcore : ∀ t, coreAt s₀ (tr ++ [x]) t =
        if t ≤ tr.length then coreAt s₀ tr t else gstep c g.core e.2 (vwT s') := by
      intro t
      simp only [coreAt, stAt_snoc']
      split_ifs
      · rfl
      · simp [hx, hout', hov]
    have hv' : ∀ t, (coreAt s₀ (tr ++ [x]) t).view =
        vwT (stAt ST.init (trT ++ [(e.1, out s', s')]) t) := by
      intro t
      rw [hcore, stAt_snoc', ← hlenT]
      split_ifs
      · exact hv t
      · exact gstep_view _ _ _ _
    have hrun' : RunSteps c (coreAt s₀ (tr ++ [x])) := by
      refine ⟨by rw [hcore, if_pos (Nat.zero_le _)]; exact hrun.1,
        fun p => by rw [hcore, if_pos (Nat.zero_le _)]; exact hrun.2.1 p, fun t => ?_⟩
      rw [hcore, hcore]
      by_cases h₁ : t + 1 ≤ tr.length
      · rw [if_pos h₁, if_pos (by omega)]; exact hrun.2.2 t
      · by_cases h₂ : t = tr.length
        · subst h₂
          rw [if_neg h₁, if_pos le_rfl]
          exact Or.inr ⟨e.2, vwT s', by simp [coreAt, hgold]⟩
        · rw [if_neg h₁, if_neg (by omega)]
          exact Or.inl rfl
    have hF := guard_of_live hP hset hΔ hA hGT hv' hrun'
    refine ⟨?_, hF, hlast', fun _ => ⟨hnext, hgT', ?_, hv', hrun'⟩⟩
    · show (false || !(finF c ST vwT P exT ov exF).guard (tr ++ [x])) = false
      rw [hguardF _ hF]; rfl
    · simp [monNext, treeNext, hlenT]

include hov hP hset hΔ hA in
/-- The invariant is preserved by every activation. -/
theorem inv_step (m : MSt Party Blk σT ET OT) (e : ET × GAct Party Blk) (s' : σT)
    (hm : MInv c ST vwT P exT ov exF m) :
    MInv c ST vwT P exT ov exF (monNext c ST vwT P exT ov exF out m e s'
      (gpost c exT ov { m.1.1 with pend := e.2 } (treeOut c ST vwT P exT out m e s'))) :=
  inv_step_gen out hov hP hset hΔ hA m e s' hm _ (gpost_cases c exT ov _ _)

include hov hinit hP hset hΔ hA in
/-- **The guard of `F_FinTree` never fails on the hybrid run**: under the hypotheses of
`ffg_realizes`, for every environment the probability that the guard of `F_FinTree` fails on
the trace of the `F_Tree`-hybrid world is `0`. -/
theorem guardFail_eq_zero
    (hout : ∀ s e, ∃ C : SPComp σT, ST.step s e = SPComp.bind C fun s' => SPComp.pure (s', out s'))
    {ζ : Type} (Z : Env (Strat ζ (ET × GAct Party Blk) (TreeView Party Blk)) ζ) :
    guardFail (ffgWorld c ST vwT P exT ov exF) (finF c ST vwT P exT ov exF).guard Z = 0 := by
  unfold guardFail
  refine prBad_eq_zero_of_invariant _ _ (MInv c ST vwT P exT ov exF)
    (inv_init hinit hP hset hΔ hA) (fun m hm => hm.1) ?_ Z
  intro m e K h hm hK
  obtain ⟨C, hC⟩ := hout m.1.2.1 e.1
  rw [monitor_step_eq out C m e hC, SPComp.bind_assoc]
  refine prTrue_bind_eq_zero _ _ _ fun s' h' => ?_
  rw [SPComp.pure_bind]
  exact hK _ _ (inv_step out hov hP hset hΔ hA m e s' hm)

include hST hov hinit hP hset hΔ hA in
/-- **FFG in the `F_Tree`-hybrid world realizes `F_FinTree` perfectly** (composition
plumbing).
Let the tree simulator `ST` be lossless and output a function `out` of its new state from
which the gadget reads the view of that state (`ov (out s) = vwT s`); let the guard of
`F_Tree^P` hold on the empty trace; let every property of `P` read only rounds, trees and
positions; let the guard of `F_Tree^P` imply that the pruned positions `cut` are settled; let
`1 ≤ Δ`; and let the adversarial validators hold less than a third of the total stake,
`3 * stake w (univ \ H) < W`. Then the FFG gadget running with the ideal world of `F_Tree^P`
(`ffgWorld`) realizes the ideal world of `F_FinTree^P'` (`finF`, with
`P' = finality-respecting positions :: FinalOnHonestPos :: P`, propagation within `Δ` rounds and the
support guard `suppF`)
with the simulator `ffgSim`: every environment has advantage `0`. -/
theorem ffg_realizes
    (hout : ∀ s e, ∃ C : SPComp σT, ST.step s e = SPComp.bind C fun s' => SPComp.pure (s', out s')) :
    Realizes (ffgWorld c ST vwT P exT ov exF)
      (ideal (finF c ST vwT P exT ov exF) (ffgSim c ST vwT P exT ov exF)) (fun _ _ => 0) := by
  intro ζ Z
  have hnf : ∀ s e, SPComp.NoFail ((ffgWorld c ST vwT P exT ov exF).step s e) :=
    Hybrid.withSub_noFail _ _ (Hybrid.ideal_noFail _ _ hST)
  exact (transparent_realizes_copy _ _ hnf ζ Z).trans_eq
    (guardFail_eq_zero out hov hinit hP hset hΔ hA hout Z)

include hST hov hinit hP hset hΔ hA in
/-- **The realization as concrete UC emulation** (`UCConcrete.UCEmulatesCSim`) with the zero
bound (composition plumbing): with the environment strategy as honest input, the
environment's final state as output, empty leakage and the identity simulator map, the view
maps of the `F_Tree`-hybrid world and of the ideal world of `F_FinTree` are at distance `0`
for every environment. -/
theorem ffg_UCEmulatesCSim
    (hout : ∀ s e, ∃ C : SPComp σT, ST.step s e = SPComp.bind C fun s' => SPComp.pure (s', out s'))
    (ζ V : Type) :
    UCEmulatesCSim ⟨Strat ζ (ET × GAct Party Blk) (TreeView Party Blk), ζ, Empty, Empty, V⟩
      (fun s => SPComp.bind (view (ffgWorld c ST vwT P exT ov exF) s) fun z =>
        SPComp.pure (Sum.inl z))
      (fun s => SPComp.bind (view (ideal (finF c ST vwT P exT ov exF)
        (ffgSim c ST vwT P exT ov exF)) s) fun z => SPComp.pure (Sum.inl z)) id
      (fun _ _ => 0) :=
  (ffg_realizes hST out hov hinit hP hset hΔ hA hout).toUCEmulatesCSim ζ V

end Invariant

/-! ## A concrete instance -/

namespace Example

open CatCryptCore.Consensus.Finality.Examples

/-- The tree view at round `n`: one party whose tree and position are `[n, …, 0]`, and no final
blocks of `F_Tree`. -/
def lv (n : ℕ) : TreeView (Fin 1) ℕ := ⟨n, fun _ => line n, fun _ => line n, fun _ => []⟩

/-- The tree simulator: its state is the round `n`; every activation moves to round `n + 1`
and outputs the view of the new round. -/
noncomputable def lineST : Sys ℕ Unit (TreeView (Fin 1) ℕ) where
  init := 0
  step n _ := SPComp.pure (n + 1, lv (n + 1))

/-- The gadget parameters: the chain `lineTree`, one honest validator of stake `1`, slots equal
to block numbers, epochs of one slot, voting on the full position, delivery bound `1`. -/
def cfg : Cfg (Fin 1) ℕ := ⟨lineTree, fun _ => 1, Finset.univ, id, 1, fun v p => v.pos p, 1⟩

/-- The tree property: common prefix `0`. -/
def lineP : List (TreeTrace (Fin 1) ℕ → Prop) := [fun X => X.CommonPrefix 0]

/-- **Non-vacuity of the hypotheses.** For the one-validator instance (`3 · 0 < W = 1`), every
hypothesis of `ffg_realizes` holds, with `out = lv`, `ov = id`, `exT = exF = lv 0`. -/
theorem instance_hyps :
    (∀ s e, SPComp.NoFail (lineST.step s e)) ∧
      (∀ s e, ∃ C : SPComp ℕ, lineST.step s e = SPComp.bind C fun s' => SPComp.pure (s', lv s')) ∧
      (∀ s, id (lv s) = lv s) ∧
      FTreeGuard cfg.T lineP
        (traceOf lv (· ∈ cfg.H) lineST.init ([] : Trace ℕ Unit (TreeView (Fin 1) ℕ))) ∧
      (∀ φ ∈ lineP, PosOnly φ) ∧ (∀ X, FTreeGuard cfg.T lineP X → Settled cfg.cut X) ∧
      1 ≤ cfg.Δ ∧ 3 * stake cfg.w (Finset.univ \ cfg.H) < totalStake cfg.w := by
  refine ⟨fun _ _ => SPComp.pure_noFail _, fun n _ => ⟨SPComp.pure (n + 1), by rw [SPComp.pure_bind]; rfl⟩,
    fun _ => rfl, ?_, ?_, ?_, le_rfl, by decide⟩
  · refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro p t t' _ _; simp [traceOf, stAt_nil]
    · intro p t _; simp [traceOf, stAt_nil, lv]
    · intro p t _; simp [TreeTrace.chains, traceOf, stAt_nil, lv, lineST, line]
    · intro t t' _; simp [traceOf, stAt_nil]
    · simp only [lineP, List.mem_singleton, forall_eq]
      intro p q t t' _ _ _
      simp only [TreeTrace.chains, traceOf, stAt_nil, List.drop_zero]
      exact List.suffix_refl _
    · rintro p q t t' b b' i j _ _ ⟨C, hC, -⟩
      simp [TreeTrace.finChains, traceOf, stAt_nil, lv] at hC
  · simp only [lineP, List.mem_singleton, forall_eq]
    exact fun X f h => h
  · intro X hX p q t t' hp hq h
    exact hX.2.1 _ List.mem_cons_self p q t t' hp hq h

/-- **The realization for the instance** (composition plumbing): the FFG gadget over the
one-party tree realizes `F_FinTree` with advantage `0` against every environment. -/
theorem instance_realizes :
    Realizes (ffgWorld cfg lineST lv lineP (lv 0) id (lv 0))
      (ideal (finF cfg lineST lv lineP (lv 0) id (lv 0)) (ffgSim cfg lineST lv lineP (lv 0) id (lv 0)))
      (fun _ _ => 0) := by
  obtain ⟨hST, hout, hov, hinit, hP, hset, hΔ, hA⟩ := instance_hyps
  exact ffg_realizes hST lv hov hinit hP hset hΔ hA hout

/-- The honest vote from the genesis checkpoint `(0, 0)` to the checkpoint `(1, 1)`. -/
def vx : Vote (Fin 1) ℕ := ⟨0, ⟨0, 0⟩, ⟨1, 1⟩⟩

/-- A run of the gadget: at time `1` the view `[1, 0]` and the honest vote `vx`; at time `2`
the view `[2, 1, 0]`, when `vx` is delivered; afterwards nothing changes. -/
noncomputable def runG : ℕ → GCore (Fin 1) ℕ
  | 0 => ginit (lv 0)
  | 1 => gstep cfg (ginit (lv 0)) (.hvote vx) (lv 1)
  | _ + 2 => gstep cfg (gstep cfg (ginit (lv 0)) (.hvote vx) (lv 1)) .idle (lv 2)

theorem runG_view (t : ℕ) : (runG t).view = lv (min t 2) := by
  rcases t with _ | _ | t
  · rfl
  · exact gstep_view _ _ _ _
  · rw [show min (t + 2) 2 = 2 by omega]; exact gstep_view _ _ _ _

theorem runG_run : Run cfg runG where
  init_cast := rfl
  init_seen _ := rfl
  step t := by
    rcases t with _ | _ | t
    · exact Or.inr ⟨.hvote vx, lv 1, rfl⟩
    · exact Or.inr ⟨.idle, lv 2, rfl⟩
    · exact Or.inl rfl
  rounds t t' h := by
    show (runG t).view.round ≤ (runG t').view.round
    rw [runG_view, runG_view]
    simp only [lv]
    omega
  settled p q t t' _ _ h := by
    show (runG t).view.pos p <:+ (runG t').view.pos q
    rw [runG_view, runG_view]
    exact line_suffix (min_le_min_right 2 h)

theorem honestOK_vx : HonestOK cfg (lv 1) ∅ vx := by
  refine ⟨Finset.mem_univ _, by decide, by decide, ?_⟩
  simp [mem_slashable, DoubleVote, SurroundVote, vx]

/-- The vote `vx` has been received at time `2`. -/
theorem vx_mem_seen : vx ∈ (runG 2).seen 0 := by
  have h1 : (vx, 1) ∈ (runG 1).cast := by
    show (vx, 1) ∈ (act cfg { ginit (lv 0) with view := lv 1 } (.hvote vx)).cast
    simp only [act]
    split_ifs with h
    · exact Finset.mem_insert_self _ _
    · exact absurd (by simpa [GCore.votes, ginit] using honestOK_vx) h
  show vx ∈ (gstep cfg (runG 1) .idle (lv 2)).seen 0
  rw [gstep_seen]
  exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨(vx, 1), Finset.mem_filter.2 ⟨h1, le_rfl⟩, rfl⟩)

/-- The genesis checkpoint is finalized by every vote set that contains `vx`. -/
theorem finalized_genesis {S : Finset (Vote (Fin 1) ℕ)} (hx : vx ∈ S) :
    Finalized cfg.T cfg.w S ⟨0, 0⟩ := by
  refine ⟨Justified.genesis, ⟨1, 1⟩, rfl, by decide, Nat.zero_le 1, ?_⟩
  have hv : voters S ⟨0, 0⟩ ⟨1, 1⟩ = Finset.univ :=
    Finset.eq_univ_of_forall fun v => by
      rw [Subsingleton.elim v 0]
      exact mem_voters.2 hx
  rw [hv]
  decide

/-- **Non-vacuity of the conclusion.** The run `runG` of the gadget of the instance satisfies
the hypotheses of `finTreeGuard_of_run`, its reported trace satisfies the guard of
`F_FinTree^P'`, and the genesis block is final for the honest party at time `2`. -/
theorem run_finalizes :
    Run cfg runG ∧ (posTT cfg runG).WellFormed cfg.T ∧ (∀ φ ∈ lineP, φ (posTT cfg runG)) ∧
      FinTreeGuard cfg.T ((fun X => X.FinalityRespectingPos) :: FinalOnHonestPos :: lineP) cfg.Δ
        (suppF cfg)
        (finTT cfg runG) ∧
      ∃ i, (finTT cfg runG).finalized 2 0 0 i := by
  obtain ⟨-, -, -, -, hP, -, hΔ, hA⟩ := instance_hyps
  have hwf : (posTT cfg runG).WellFormed cfg.T := by
    refine ⟨fun p t t' _ h => ?_, fun p t _ => ?_, fun p t _ => ?_, runG_run.rounds⟩
    · show (runG t).view.tree p ⊆ (runG t').view.tree p
      rw [runG_view, runG_view]
      exact (line_suffix (min_le_min_right 2 h)).subset
    · show (runG t).view.pos p ⊆ (runG t).view.tree p
      rw [runG_view]
      exact List.Subset.refl _
    · show ((runG t).view.pos p).Pairwise fun b b' => lineTree.anc b' b
      rw [runG_view]
      exact lineTrace_chainsInTree () (min t 2) trivial
  have hPG : ∀ φ ∈ lineP, φ (posTT cfg runG) := by
    simp only [lineP, List.mem_singleton, forall_eq]
    exact fun p q t t' hp hq h => runG_run.settled p q t t' hp hq h
  refine ⟨runG_run, hwf, hPG, finTreeGuard_of_run runG_run hΔ hA hP hwf hPG, ?_⟩
  have hfin := finalized_genesis vx_mem_seen
  have hmem : 0 ∈ finList cfg ((runG 2).seen 0) :=
    mem_finList (by decide) hfin fun b' hb' =>
      congrArg Checkpoint.block (justified_epoch_zero hb'.1 rfl)
  obtain ⟨s, l, hsl⟩ := List.append_of_mem hmem
  refine ⟨l.length, l, ?_, rfl⟩
  show 0 :: l <:+ finList cfg ((runG 2).seen 0)
  rw [hsl]
  exact List.suffix_append s _

end Example

/-! ## An instance with a fork and an adversarial validator -/

namespace ForkExample

open CatCryptCore.Consensus.Finality.Examples FFG.Examples

/-- The tree view at round `n`: every party has the tree `[2, 1, 0]` of `forkTree` (genesis `0`
with the two children `1` and `2`), the position `[1, 0]`, and no final blocks of `F_Tree`. -/
def fv (n : ℕ) : TreeView (Fin 4) (Fin 3) := ⟨n, fun _ => [2, 1, 0], fun _ => [1, 0], fun _ => []⟩

/-- The tree simulator: its state is the round `n`; every activation moves to round `n + 1`
and outputs the view of the new round. -/
noncomputable def forkST : Sys ℕ Unit (TreeView (Fin 4) (Fin 3)) where
  init := 0
  step n _ := SPComp.pure (n + 1, fv (n + 1))

/-- The gadget parameters: the block tree `forkTree`, four validators of stake `1`, the honest
validators `0, 1, 2`, slots equal to block numbers, epochs of one slot, voting on the full
position, delivery bound `1`. -/
def cfg : Cfg (Fin 4) (Fin 3) := ⟨forkTree, unitStake, {0, 1, 2}, blockSlot, 1, fun v p => v.pos p, 1⟩

/-- The tree property: common prefix `0`. -/
def forkP : List (TreeTrace (Fin 4) (Fin 3) → Prop) := [fun X => X.CommonPrefix 0]

theorem cfg_hA : 3 * stake cfg.w (Finset.univ \ cfg.H) < totalStake cfg.w := by decide

/-- **Non-vacuity of the hypotheses with an adversarial validator.** For the instance with four
validators of stake `1` of which validator `3` is adversarial (`3 · 1 < W = 4`), every
hypothesis of `ffg_realizes` holds, with `out = fv`, `ov = id`, `exT = exF = fv 0`. -/
theorem instance_hyps :
    (∀ s e, SPComp.NoFail (forkST.step s e)) ∧
      (∀ s e, ∃ C : SPComp ℕ, forkST.step s e = SPComp.bind C fun s' => SPComp.pure (s', fv s')) ∧
      (∀ s, id (fv s) = fv s) ∧
      FTreeGuard cfg.T forkP
        (traceOf fv (· ∈ cfg.H) forkST.init ([] : Trace ℕ Unit (TreeView (Fin 4) (Fin 3)))) ∧
      (∀ φ ∈ forkP, PosOnly φ) ∧ (∀ X, FTreeGuard cfg.T forkP X → Settled cfg.cut X) ∧
      1 ≤ cfg.Δ ∧ 3 * stake cfg.w (Finset.univ \ cfg.H) < totalStake cfg.w := by
  refine ⟨fun _ _ => SPComp.pure_noFail _,
    fun n _ => ⟨SPComp.pure (n + 1), by rw [SPComp.pure_bind]; rfl⟩,
    fun _ => rfl, ?_, ?_, ?_, le_rfl, cfg_hA⟩
  · refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro p t t' _ _; simp [traceOf, stAt_nil]
    · intro p t _; simp [traceOf, stAt_nil, fv]
    · intro p t _
      show List.Pairwise (fun b b' : Fin 3 => forkTree.anc b' b) [1, 0]
      decide
    · intro t t' _; simp [traceOf, stAt_nil]
    · simp only [forkP, List.mem_singleton, forall_eq]
      intro p q t t' _ _ _
      simp only [TreeTrace.chains, traceOf, stAt_nil, List.drop_zero]
      exact List.suffix_refl _
    · rintro p q t t' b b' i j _ _ ⟨C, hC, -⟩
      simp [TreeTrace.finChains, traceOf, stAt_nil, fv] at hC
  · simp only [forkP, List.mem_singleton, forall_eq]
    exact fun X f h => h
  · intro X hX p q t t' hp hq h
    exact hX.2.1 _ List.mem_cons_self p q t t' hp hq h

/-- **The realization for the instance** (composition plumbing): the FFG gadget over the fork
tree, with one adversarial validator of four, realizes `F_FinTree` with advantage `0` against
every environment. -/
theorem instance_realizes :
    Realizes (ffgWorld cfg forkST fv forkP (fv 0) id (fv 0))
      (ideal (finF cfg forkST fv forkP (fv 0) id (fv 0))
        (ffgSim cfg forkST fv forkP (fv 0) id (fv 0)))
      (fun _ _ => 0) := by
  obtain ⟨hST, hout, hov, hinit, hP, hset, hΔ, hA⟩ := instance_hyps
  exact ffg_realizes hST fv hov hinit hP hset hΔ hA hout

/-- The votes of the run, in the order cast: the honest validators `0, 1, 2` vote from genesis
to `(1, 1)`; the adversarial validator `3` votes from genesis to the conflicting checkpoint
`(2, 1)` and from genesis to `(1, 1)` (a double vote); the honest validators vote from `(1, 1)`
to `(1, 2)`. -/
def fVotes : List (Vote (Fin 4) (Fin 3)) :=
  [vote 0 0 0 1 1, vote 1 0 0 1 1, vote 2 0 0 1 1, vote 3 0 0 2 1, vote 3 0 0 1 1,
   vote 0 1 1 1 2, vote 1 1 1 1 2, vote 2 1 1 1 2]

/-- The `k`-th vote of the run. -/
def fVote (k : ℕ) : Vote (Fin 4) (Fin 3) := fVotes.getD k (vote 0 0 0 0 0)

/-- The action at step `k`: the adversarial votes at steps `3` and `4`, the honest votes at the
other steps below `8`, and nothing afterwards. -/
def fAct (k : ℕ) : GAct (Fin 4) (Fin 3) :=
  if k = 3 ∨ k = 4 then .avote (fVote k) else if k < 8 then .hvote (fVote k) else .idle

/-- The cast votes after `t` steps: the `k`-th vote cast in round `k + 1`. -/
def castF : ℕ → Finset (Vote (Fin 4) (Fin 3) × ℕ)
  | 0 => ∅
  | t + 1 => if t < 8 then insert (fVote t, t + 1) (castF t) else castF t

/-- A run of the gadget: at step `t < 9` the view of round `t + 1` and the action `fAct t`;
the step `8` delivers every vote; afterwards nothing changes. -/
noncomputable def runF : ℕ → GCore (Fin 4) (Fin 3)
  | 0 => ginit (fv 0)
  | t + 1 => if t < 9 then gstep cfg (runF t) (fAct t) (fv (t + 1)) else runF t

theorem gstep_cast_hvote {c : Cfg (Fin 4) (Fin 3)} {g : GCore (Fin 4) (Fin 3)}
    {x : Vote (Fin 4) (Fin 3)} {v : TreeView (Fin 4) (Fin 3)} (h : HonestOK c v g.votes x) :
    (gstep c g (.hvote x) v).cast = insert (x, v.round) g.cast := by
  rw [gstep_cast]
  exact congrArg GCore.cast (if_pos h)

theorem gstep_cast_avote {c : Cfg (Fin 4) (Fin 3)} {g : GCore (Fin 4) (Fin 3)}
    {x : Vote (Fin 4) (Fin 3)} {v : TreeView (Fin 4) (Fin 3)} (h : x.validator ∉ c.H) :
    (gstep c g (.avote x) v).cast = insert (x, v.round) g.cast := by
  rw [gstep_cast]
  exact congrArg GCore.cast (if_pos h)

theorem runF_view (t : ℕ) : (runF t).view = fv (min t 9) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases ht : t < 9
    · rw [runF, if_pos ht, gstep_view, Nat.min_eq_left (by omega)]
    · rw [runF, if_neg ht, ih, Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]

theorem cast_runF (t : ℕ) : (runF t).cast = castF t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases ht : t < 9
    · rw [runF, if_pos ht]
      interval_cases t <;>
      first
      | (rw [show fAct _ = .hvote (fVote _) from rfl,
            gstep_cast_hvote (by rw [GCore.votes, ih]; unfold HonestOK; decide), ih]; rfl)
      | (rw [show fAct _ = .avote (fVote _) from rfl, gstep_cast_avote (by decide), ih]; rfl)
      | (rw [show fAct _ = .idle from rfl, gstep_cast]; exact ih)
    · rw [runF, if_neg ht, ih, castF, if_neg (by omega)]

/-- All votes of the run. -/
def allV : Finset (Vote (Fin 4) (Fin 3)) := (castF 8).image Prod.fst

theorem votes_runF_nine : (runF 9).votes = allV := by
  rw [GCore.votes, cast_runF]; rfl

theorem allV_subset_seen (p : Fin 4) : allV ⊆ (runF 9).seen p := by
  intro x hx
  show x ∈ (gstep cfg (runF 8) (fAct 8) (fv 9)).seen p
  rw [gstep_seen]
  refine Finset.mem_union_right _ ?_
  show x ∈ overdue 1 9 (runF 8).cast
  rw [cast_runF]
  exact (show allV ⊆ overdue 1 9 (castF 8) by decide) hx

theorem runF_run : Run cfg runF where
  init_cast := rfl
  init_seen _ := rfl
  step t := by
    by_cases ht : t < 9
    · exact Or.inr ⟨fAct t, fv (t + 1), by rw [runF, if_pos ht]⟩
    · exact Or.inl (by rw [runF, if_neg ht])
  rounds t t' h := by
    show (runF t).view.round ≤ (runF t').view.round
    rw [runF_view, runF_view]
    simp only [fv]
    omega
  settled p q t t' _ _ _ := by
    show (runF t).view.pos p <:+ (runF t').view.pos q
    rw [runF_view, runF_view]
    exact List.suffix_refl _

theorem allV_finalized : Finalized cfg.T cfg.w allV ⟨1, 1⟩ :=
  finalized_of_links (c' := ⟨1, 2⟩) (by decide) rfl (by decide)

/-- **Accountable safety on a run with a fork and an adversarial validator.** The run `runF`
of the gadget over `forkTree` (blocks `1` and `2` conflict) satisfies the hypotheses of
`finTreeGuard_of_run`, and its reported trace satisfies the guard of `F_FinTree^P'`. The
adversarial validator `3` votes for the conflicting checkpoint `(2, 1)` and double-votes, and it
is the only slashable validator, of stake `1` with `3 · 1 < W = 4`. Block `1` is final for the
honest party `0` at time `9`, and at every time no two checkpoints finalized by the cast votes
lie on conflicting blocks (`Run.anc_of_finalized`, from `FFG.anc_of_kFinalized_of_justified`). -/
theorem run_accountable :
    Run cfg runF ∧
      FinTreeGuard cfg.T ((fun X => X.FinalityRespectingPos) :: FinalOnHonestPos :: forkP) cfg.Δ
        (suppF cfg) (finTT cfg runF) ∧
      cfg.T.Conflicting 1 2 ∧ vote 3 0 0 2 1 ∈ (runF 9).votes ∧
      slashable (runF 9).votes = {3} ∧
      3 * stake cfg.w (slashable (runF 9).votes) < totalStake cfg.w ∧
      (∃ i, (finTT cfg runF).finalized 9 0 1 i) ∧
      ∀ t b b' e e', Finalized cfg.T cfg.w (runF t).votes ⟨b, e⟩ →
        Finalized cfg.T cfg.w (runF t).votes ⟨b', e'⟩ → ¬ cfg.T.Conflicting b b' := by
  obtain ⟨-, -, -, -, hP, -, hΔ, hA⟩ := instance_hyps
  have hwf : (posTT cfg runF).WellFormed cfg.T := by
    refine ⟨fun p t t' _ h => ?_, fun p t _ => ?_, fun p t _ => ?_, runF_run.rounds⟩
    · show (runF t).view.tree p ⊆ (runF t').view.tree p
      rw [runF_view, runF_view]
      exact List.Subset.refl _
    · show (runF t).view.pos p ⊆ (runF t).view.tree p
      rw [runF_view]
      show ([1, 0] : List (Fin 3)) ⊆ [2, 1, 0]
      decide
    · show ((runF t).view.pos p).Pairwise fun b b' => forkTree.anc b' b
      rw [runF_view]
      show List.Pairwise (fun b b' : Fin 3 => forkTree.anc b' b) [1, 0]
      decide
  have hPG : ∀ φ ∈ forkP, φ (posTT cfg runF) := by
    simp only [forkP, List.mem_singleton, forall_eq]
    exact fun p q t t' hp hq h => runF_run.settled p q t t' hp hq h
  refine ⟨runF_run, finTreeGuard_of_run runF_run hΔ hA hP hwf hPG, forkTree_conflicting,
    by rw [votes_runF_nine]; decide, by rw [votes_runF_nine]; decide,
    by rw [votes_runF_nine]; decide, ?_, ?_⟩
  · have hfin : Finalized cfg.T cfg.w ((runF 9).seen 0) ⟨1, 1⟩ :=
      Finalized.mono (allV_subset_seen 0) allV_finalized
    have hmem : 1 ∈ finList cfg ((runF 9).seen 0) :=
      mem_finList (by decide) hfin fun b' hb' =>
        runF_run.finalized_unique hA (Finalized.mono (runF_run.seen_subset 9 0) hfin)
          (Finalized.mono (runF_run.seen_subset 9 0) hb')
    obtain ⟨s, l, hsl⟩ := List.append_of_mem hmem
    refine ⟨l.length, l, ?_, rfl⟩
    show 1 :: l <:+ finList cfg ((runF 9).seen 0)
    rw [hsl]
    exact List.suffix_append s _
  · intro t b b' e e' hb hb' hc
    rcases le_total e e' with hle | hle
    · exact hc.1 (runF_run.anc_of_finalized hA hb hb' hle)
    · exact hc.2 (runF_run.anc_of_finalized hA hb' hb hle)

end ForkExample

end CatCryptCore.Consensus.UC.FFGGadget
