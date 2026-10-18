/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.UC.FinalityLive
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
proposes its states to `F_FinTree` (the copy simulator of the hybrid world).
`finF` is `F_FinTree^P'` over the states of the simulator, with the view `finView` of the
gadget component, `P' = finP c P σ d`: finality liveness `TreeTrace.UpdatedWithin` from round
`2 E + σ + d + Δ` with lag `3 E + 2 σ + d + Δ - 1`, finality-respecting positions,
`FinalOnHonestPos` and `P`; delivery bound `Δ`; and the support guard `1`-validity together
with stake validity.

## Main results

* `inv_step`, `inv_init`: the invariant of the monitored run of the hybrid world: the guard of
  `F_FinTree` holds on the trace; while the gadget is live, `F_Tree` has not exploded, its
  trace satisfies the guard of `F_Tree`, the views of the gadget are the views of `F_Tree`,
  and the gadget states form a run (`FFGGadget.Run`).
* `guardFail_eq_zero`: the guard of `F_FinTree` never fails on the hybrid run.
* `ffg_realizes` (headline): under the hypotheses below, `ffgWorld` realizes
  `ideal (finF …) (ffgSim …)` with bound `0`.
  The statement is a `RealizesBound`, found by instance search from `Lossless`, `GuardSim`
  (`ffgSim` copies `ffgWorld`) and `GuardFailBound … 0` (`guardFail_eq_zero`); the form
  `UCConcrete.UCEmulatesCSim` with the zero bound follows through `UCFromRealizes`.
* `Example.instance_hyps`, `Example.instance_realizes`, `Example.run_finalizes`: a one-validator
  instance satisfies every hypothesis (with `3 · 0 < W = 1`, `σ = 1`, `d = 0`), and in a run
  of its gadget the honest party has a final block from time `4` on, at most `5` rounds behind.
* `ForkExample.run_accountable`: over `forkTree` with four validators of stake `1`, validator
  `3` adversarial, in a run of the gadget the adversarial validator votes for the conflicting
  block `2` and double-votes, it is the only slashable validator, block `1`, finalized by the
  first round of the honest schedule, is final for an honest party, and no two finalized
  checkpoints conflict.

## Hypotheses of the headline theorem

* `hST`: the tree simulator is lossless; `hout`, `hov`: its output is a function `out` of its
  new state, and the gadget reads from it the view of that state (`ov (out s) = vwT s`).
* `hinit`: the guard of `F_Tree` holds on the empty trace (the initial view is admissible).
* `hP`: every property of `P` reads only rounds, trees and positions (`PosOnly`).
* `hset`: the guard of `F_Tree` implies that the pruned positions are settled
  (`Settled cut`).
* `hLive`: the guard of `F_Tree` implies the liveness hypotheses `LiveHyp c σ` (chain growth
  with window `σ`, decreasing slots, genesis on every honest position, the clock).
* `hcut`: the gadget votes on the blocks of slot at most the round minus `d`.
* `hΔ`, `hE`: `1 ≤ Δ`, `1 ≤ E`; `hA`: `3 * stake w (univ \ H) < W`; `hv₀`: the validator
  `c.v₀` of the schedule is in `H`; `hstart`: the schedule starts at round `2 E + σ + d`.

## Modelling choices

* The honest validators are both the honest parties of `F_Tree` and of `F_FinTree`
  (`· ∈ H`). Corruption is static.
* The simulator is the copy simulator: since the trace of the hybrid world always satisfies
  the guard of `F_FinTree`, the functionality never explodes and copying is exact.
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
  (exF : TreeView Party Blk) (σ d : ℕ)

/-- **The FFG gadget as a hybrid protocol** over `F_Tree`, with initial view `v₀`: an outer
event `(eT, a)` passes `eT` to `F_Tree` and then performs `gpost` with the action `a`. -/
noncomputable def ffgHybrid (v₀ : TreeView Party Blk) :
    Hybrid (GSt Party Blk) (ET × GAct Party Blk) (TreeView Party Blk) ET OT where
  init := ⟨ginit c v₀, false, .idle⟩
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

/-- The properties `P'` of `F_FinTree`: finality liveness (`TreeTrace.UpdatedWithin`) from
round `2 E + σ + d + Δ` with lag `3 E + 2 σ + d + Δ - 1`, finality-respecting positions,
final blocks on the honest positions (`FinalOnHonestPos`), and the properties `P` of
`F_Tree`. -/
def finP : List (TreeTrace Party Blk → Prop) :=
  (fun X => X.UpdatedWithin c.slot (2 * c.E + σ + d + c.Δ) (3 * c.E + 2 * σ + d + c.Δ - 1)) ::
    (fun X => X.FinalityRespectingPos) :: FinalOnHonestPos :: P

/-- **The functionality** `F_FinTree^P'` over the states of the simulator: view `finView` of
the gadget component, honest parties `H`, `P' = finP c P σ d` (finality liveness,
finality-respecting positions, `FinalOnHonestPos`, `P`), delivery bound `Δ`, support guard
`suppF`, exploded output `exF`. -/
noncomputable def finF :
    TFunc (WSt Party Blk σT ET OT) (ET × GAct Party Blk) (TreeView Party Blk) :=
  finTree (fun s => finView c s.1.core) (· ∈ c.H) c.T (finP c P σ d)
    c.Δ (suppF c) (ffgSim c ST vwT P exT ov exF).init exF

instance [Lossless ST] : Lossless (ffgWorld c ST vwT P exT ov exF) :=
  Hybrid.lossless_withSub _ _

instance [Lossless ST] : Lossless (ffgSim c ST vwT P exT ov exF) :=
  Hybrid.lossless_withSub _ _

/-- `ffgSim` is the copy simulator of `ffgWorld`. -/
instance (F : TFunc (WSt Party Blk σT ET OT) (ET × GAct Party Blk) (TreeView Party Blk)) :
    GuardSim (ffgWorld c ST vwT P exT ov exF) (ffgSim c ST vwT P exT ov exF) F :=
  ⟨rfl, fun _ _ _ => rfl⟩

end Hybrid

/-! ## The invariant of the monitored hybrid run -/

section Invariant

variable {Party Blk : Type} [Fintype Party] [DecidableEq Party] [DecidableEq Blk]
variable {σT ET OT : Type}
variable {c : Cfg Party Blk} {ST : Sys σT ET OT} {vwT : σT → TreeView Party Blk}
  {P : List (TreeTrace Party Blk → Prop)} {exT : OT} {ov : OT → TreeView Party Blk}
  {exF : TreeView Party Blk} {σ d : ℕ}

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

/-- The step part of a run: no votes at time `0`, the schedule at round `0` from the genesis
checkpoint, gadget steps or stuttering. -/
def RunSteps (c : Cfg Party Blk) (G : ℕ → GCore Party Blk) : Prop :=
  (G 0).cast = ∅ ∧ (∀ p, (G 0).seen p = ∅) ∧ (G 0).nr = 0 ∧
    (G 0).sch = (∅, genesisCheckpoint c.T) ∧
    ∀ t, G (t + 1) = G t ∨ ∃ a v, G (t + 1) = gstep c (G t) a v

/-- **The guard of `F_FinTree` while `F_Tree` is live.** If the guard of `F_Tree` holds on its
trace `trT`, the views of the gadget states `G` are the views of that trace, and `G` makes
gadget steps, then the tree trace reported by the gadget satisfies the guard of
`F_FinTree^P'` with `P' = finP c P σ d` (`finTreeGuard_of_run`, `Run.updatedWithin`). -/
theorem guard_of_live (hP : ∀ φ ∈ P, PosOnly φ)
    (hset : ∀ X, FTreeGuard c.T P X → Settled c.cut X) (hΔ : 1 ≤ c.Δ)
    (hA : 3 * stake c.w (Finset.univ \ c.H) < totalStake c.w)
    (hlive : ∀ X, FTreeGuard c.T P X → LiveHyp c σ X)
    (hcut : ∀ v p, c.cut v p = (v.pos p).filter fun b => decide (c.slot b + d ≤ v.round))
    (hE : 1 ≤ c.E) (hv₀ : c.v₀ ∈ c.H) (hstart : c.start = 2 * c.E + σ + d) {s₀T : σT}
    {trT : Trace σT ET OT} (hG : FTreeGuard c.T P (traceOf vwT (· ∈ c.H) s₀T trT))
    {G : ℕ → GCore Party Blk} (hv : ∀ t, (G t).view = vwT (stAt s₀T trT t))
    (hrun : RunSteps c G) :
    FinTreeGuard c.T (finP c P σ d) c.Δ (suppF c) (finTT c G) := by
  have e : posTT c G = traceOf vwT (· ∈ c.H) s₀T trT := by
    simp only [posTT, traceOf, TreeTrace.mk.injEq, true_and]
    funext t
    exact hv t
  rw [← e] at hG
  have hR : Run c G :=
    ⟨hrun.1, hrun.2.1, hrun.2.2.1, hrun.2.2.2.1, hrun.2.2.2.2, hG.1.2.2.2, hset _ hG⟩
  obtain ⟨hwf, hPs, hrest⟩ := finTreeGuard_of_run hR hΔ hA hP hG.1 hG.2.1
  exact ⟨hwf, List.forall_mem_cons.2
    ⟨hR.updatedWithin hA hE hΔ (hlive _ hG) hcut hv₀ hstart, hPs⟩, hrest⟩

variable (c ST vwT P exT ov exF σ d) in
/-- The invariant of the monitored hybrid world: the flag is unset; the guard of `F_FinTree`
holds on the trace; the state is the last state of the trace; and while the gadget is live,
`F_Tree` has not exploded, its guard holds on its trace, the two traces have the same length,
the views of the gadget are the views of `F_Tree`, and the gadget makes gadget steps. -/
def MInv (m : WSt Party Blk σT ET OT ×
    Trace (WSt Party Blk σT ET OT) (ET × GAct Party Blk) (TreeView Party Blk) × Bool) : Prop :=
  m.2.2 = false ∧
    FinTreeGuard c.T (finP c P σ d) c.Δ (suppF c)
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

variable (c ST vwT P exT ov exF σ d) in
/-- The new monitored state when the tree simulator moves to `s'` and the gadget to `g'`. -/
noncomputable def monNext (out : σT → OT) (m : MSt Party Blk σT ET OT) (e : ET × GAct Party Blk)
    (s' : σT) (g' : GSt Party Blk) : MSt Party Blk σT ET OT :=
  ((g', treeNext c ST vwT P exT out m e s'),
    m.2.1 ++ [(e, gout c exF g', (g', treeNext c ST vwT P exT out m e s'))],
    m.2.2 || !(finF c ST vwT P exT ov exF σ d).guard
      (m.2.1 ++ [(e, gout c exF g', (g', treeNext c ST vwT P exT out m e s'))]))

/-- One activation of the monitored hybrid world, when the step of the tree simulator is a
computation `C` of its next state followed by the output `out`. -/
theorem monitor_step_eq (out : σT → OT) (C : SPComp σT) (m : MSt Party Blk σT ET OT)
    (e : ET × GAct Party Blk)
    (hC : ST.step m.1.2.1 e.1 = SPComp.bind C fun s' => SPComp.pure (s', out s')) :
    (monitor (ffgWorld c ST vwT P exT ov exF) (finF c ST vwT P exT ov exF σ d).guard).step m e =
      SPComp.bind C fun s' =>
        SPComp.pure (monNext c ST vwT P exT ov exF σ d out m e s'
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
  (hLive : ∀ X, FTreeGuard c.T P X → LiveHyp c σ X)
  (hcut : ∀ v p, c.cut v p = (v.pos p).filter fun b => decide (c.slot b + d ≤ v.round))
  (hE : 1 ≤ c.E) (hv₀ : c.v₀ ∈ c.H) (hstart : c.start = 2 * c.E + σ + d)

include hinit hP hset hΔ hA hLive hcut hE hv₀ hstart in
/-- The invariant holds initially. -/
theorem inv_init :
    MInv c ST vwT P exT ov exF σ d ((ffgWorld c ST vwT P exT ov exF).init, [], false) := by
  have hv : ∀ t, (coreAt (ffgSim c ST vwT P exT ov exF).init
      ([] : Trace (WSt Party Blk σT ET OT) (ET × GAct Party Blk) (TreeView Party Blk)) t).view =
      vwT (stAt ST.init ([] : Trace σT ET OT) t) := fun t => by
    simp only [coreAt, stAt_nil]; rfl
  have hrun : RunSteps c (coreAt (ffgSim c ST vwT P exT ov exF).init
      ([] : Trace (WSt Party Blk σT ET OT) (ET × GAct Party Blk) (TreeView Party Blk))) :=
    ⟨by simp only [coreAt, stAt_nil]; rfl, fun _ => by simp only [coreAt, stAt_nil]; rfl,
      by simp only [coreAt, stAt_nil]; rfl, by simp only [coreAt, stAt_nil]; rfl,
      fun t => Or.inl (by simp only [coreAt, stAt_nil])⟩
  refine ⟨rfl, guard_of_live hP hset hΔ hA hLive hcut hE hv₀ hstart hinit hv hrun, stAt_nil _ _,
    fun _ => ⟨rfl, (treeFunc_guard_iff _ _ _ _ _ _).2 hinit, rfl, hv, hrun⟩⟩

include hov hP hset hΔ hA hLive hcut hE hv₀ hstart in
/-- The invariant is preserved by every activation, for every next state `s'` of the tree
simulator and every new gadget state `g'` that `gpost` can produce. -/
theorem inv_step_gen (m : MSt Party Blk σT ET OT) (e : ET × GAct Party Blk) (s' : σT)
    (hm : MInv c ST vwT P exT ov exF σ d m) (g' : GSt Party Blk)
    (hg : g' = ⟨m.1.1.core, true, e.2⟩ ∨
      (m.1.1.dead = false ∧ treeOut c ST vwT P exT out m e s' ≠ exT ∧
        g' = ⟨gstep c m.1.1.core e.2 (ov (treeOut c ST vwT P exT out m e s')), m.1.1.dead, e.2⟩)) :
    MInv c ST vwT P exT ov exF σ d (monNext c ST vwT P exT ov exF σ d out m e s' g') := by
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
      FinTreeGuard c.T (finP c P σ d) c.Δ (suppF c)
        (traceOf (fun s => finView c s.1.core) (· ∈ c.H) s₀ tr') →
      (finF c ST vwT P exT ov exF σ d).guard tr' = true := fun tr' h' => by
    rw [finF, finTree_guard_iff]; exact h'
  rcases hg with rfl | ⟨hd, ho, rfl⟩
  · -- the gadget stops: the reported trace does not change
    have hsame : traceOf (fun s => finView c s.1.core) (· ∈ c.H) s₀ (tr ++ [x]) =
        traceOf (fun s => finView c s.1.core) (· ∈ c.H) s₀ tr :=
      traceOf_snoc_same _ _ s₀ tr x (by rw [hgold])
    refine ⟨?_, ?_, hlast', fun h => absurd h (by simp [monNext])⟩
    · show (false || !(finF c ST vwT P exT ov exF σ d).guard (tr ++ [x])) = false
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
        fun p => by rw [hcore, if_pos (Nat.zero_le _)]; exact hrun.2.1 p,
        by rw [hcore, if_pos (Nat.zero_le _)]; exact hrun.2.2.1,
        by rw [hcore, if_pos (Nat.zero_le _)]; exact hrun.2.2.2.1, fun t => ?_⟩
      rw [hcore, hcore]
      by_cases h₁ : t + 1 ≤ tr.length
      · rw [if_pos h₁, if_pos (by omega)]; exact hrun.2.2.2.2 t
      · by_cases h₂ : t = tr.length
        · subst h₂
          rw [if_neg h₁, if_pos le_rfl]
          exact Or.inr ⟨e.2, vwT s', by simp [coreAt, hgold]⟩
        · rw [if_neg h₁, if_neg (by omega)]
          exact Or.inl rfl
    have hF := guard_of_live hP hset hΔ hA hLive hcut hE hv₀ hstart hGT hv' hrun'
    refine ⟨?_, hF, hlast', fun _ => ⟨hnext, hgT', ?_, hv', hrun'⟩⟩
    · show (false || !(finF c ST vwT P exT ov exF σ d).guard (tr ++ [x])) = false
      rw [hguardF _ hF]; rfl
    · simp [monNext, treeNext, hlenT]

include hov hP hset hΔ hA hLive hcut hE hv₀ hstart in
/-- The invariant is preserved by every activation. -/
theorem inv_step (m : MSt Party Blk σT ET OT) (e : ET × GAct Party Blk) (s' : σT)
    (hm : MInv c ST vwT P exT ov exF σ d m) :
    MInv c ST vwT P exT ov exF σ d (monNext c ST vwT P exT ov exF σ d out m e s'
      (gpost c exT ov { m.1.1 with pend := e.2 } (treeOut c ST vwT P exT out m e s'))) :=
  inv_step_gen out hov hP hset hΔ hA hLive hcut hE hv₀ hstart m e s' hm _
    (gpost_cases c exT ov _ _)

include hov hinit hP hset hΔ hA hLive hcut hE hv₀ hstart in
/-- **The guard of `F_FinTree` never fails on the hybrid run**: under the hypotheses of
`ffg_realizes`, for every environment the probability that the guard of `F_FinTree` fails on
the trace of the `F_Tree`-hybrid world is `0`. -/
theorem guardFail_eq_zero
    (hout : ∀ s e, ∃ C : SPComp σT, ST.step s e = SPComp.bind C fun s' => SPComp.pure (s', out s'))
    {ζ : Type} (Z : Env (Strat ζ (ET × GAct Party Blk) (TreeView Party Blk)) ζ) :
    guardFail (ffgWorld c ST vwT P exT ov exF) (finF c ST vwT P exT ov exF σ d).guard Z = 0 := by
  unfold guardFail
  refine prBad_eq_zero_of_invariant _ _ (MInv c ST vwT P exT ov exF σ d)
    (inv_init hinit hP hset hΔ hA hLive hcut hE hv₀ hstart) (fun m hm => hm.1) ?_ Z
  intro m e K h hm hK
  obtain ⟨C, hC⟩ := hout m.1.2.1 e.1
  rw [monitor_step_eq out C m e hC, SPComp.bind_assoc]
  refine prTrue_bind_eq_zero _ _ _ fun s' h' => ?_
  rw [SPComp.pure_bind]
  exact hK _ _ (inv_step out hov hP hset hΔ hA hLive hcut hE hv₀ hstart m e s' hm)

include hST hov hinit hP hset hΔ hA hLive hcut hE hv₀ hstart in
/-- **FFG in the `F_Tree`-hybrid world realizes `F_FinTree` perfectly.** Let the tree simulator `ST` be lossless and output a function `out` of its new state from
which the gadget reads the view of that state (`ov (out s) = vwT s`); let the guard of
`F_Tree^P` hold on the empty trace; let every property of `P` read only rounds, trees and
positions; let the guard of `F_Tree^P` imply that the pruned positions `cut` are settled and
the liveness hypotheses `LiveHyp c σ` with chain-growth window `σ`; let the gadget vote on the
positions pruned by depth `d` (`hcut`); let `1 ≤ Δ` and `1 ≤ E`; let the adversarial
validators hold less than a third of the total stake, `3 * stake w (univ \ H) < W`; and let
the schedule be read off the position of `c.v₀ ∈ H` from round `c.start = 2 E + σ + d`. Then
the FFG gadget running with the ideal world of `F_Tree^P` (`ffgWorld`) realizes the ideal
world of `F_FinTree^P'` (`finF`, with `P' = finP c P σ d`: finality liveness from round
`2 E + σ + d + Δ` with lag `3 E + 2 σ + d + Δ - 1`, finality-respecting positions,
`FinalOnHonestPos` and `P`; propagation within `Δ` rounds; the support guard `suppF`) with
the simulator `ffgSim`: every environment has advantage `0`. -/
theorem ffg_realizes
    (hout : ∀ s e, ∃ C : SPComp σT, ST.step s e = SPComp.bind C fun s' => SPComp.pure (s', out s')) :
    RealizesBound (ffgWorld c ST vwT P exT ov exF)
      (ideal (finF c ST vwT P exT ov exF σ d) (ffgSim c ST vwT P exT ov exF)) (fun _ _ => 0) :=
  haveI : Lossless ST := ⟨hST⟩
  haveI : GuardFailBound (ffgWorld c ST vwT P exT ov exF) (finF c ST vwT P exT ov exF σ d).guard
      (fun _ _ => 0) :=
    ⟨fun _ Z => (guardFail_eq_zero out hov hinit hP hset hΔ hA hLive hcut hE hv₀ hstart hout Z).le⟩
  inferInstance

include hST hov hinit hP hset hΔ hA hLive hcut hE hv₀ hstart in
/-- The realization as concrete UC emulation (`UCConcrete.UCEmulatesCSim`) with the zero
bound, through `UCFromRealizes`: with the environment strategy as honest input, the
environment's final state as output, empty leakage and the identity simulator map, the view
maps of the `F_Tree`-hybrid world and of the ideal world of `F_FinTree` are at distance `0`
for every environment. -/
example
    (hout : ∀ s e, ∃ C : SPComp σT, ST.step s e = SPComp.bind C fun s' => SPComp.pure (s', out s'))
    (ζ V : Type) :
    UCEmulatesCSim ⟨Strat ζ (ET × GAct Party Blk) (TreeView Party Blk), ζ, Empty, Empty, V⟩
      (fun s => SPComp.bind (view (ffgWorld c ST vwT P exT ov exF) s) fun z =>
        SPComp.pure (Sum.inl z))
      (fun s => SPComp.bind (view (ideal (finF c ST vwT P exT ov exF σ d)
        (ffgSim c ST vwT P exT ov exF)) s) fun z => SPComp.pure (Sum.inl z)) id
      (fun _ _ => 0) :=
  haveI := ffg_realizes hST out hov hinit hP hset hΔ hA hLive hcut hE hv₀ hstart hout
    (exT := exT) (exF := exF)
  ucEmulatesCSim_of_UCFromRealizes _ _ ζ V fun _ _ => 0

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
to block numbers, epochs of one slot, voting on the blocks of slot at most the round (pruning
depth `0`), delivery bound `1`, and the schedule from round `3` read off the position of the
validator `0`. -/
def cfg : Cfg (Fin 1) ℕ :=
  ⟨lineTree, fun _ => 1, Finset.univ, id, 1, fun v p => (v.pos p).filter fun b => decide (b ≤ v.round),
    1, 3, 0⟩

/-- The tree properties: common prefix `0` and the liveness hypotheses with window `1`. -/
def lineP : List (TreeTrace (Fin 1) ℕ → Prop) := [fun X => X.CommonPrefix 0, LiveHyp cfg 1]

theorem lineP_posOnly : ∀ φ ∈ lineP, PosOnly φ := by
  simp only [lineP, List.mem_cons, List.not_mem_nil, or_false]
  rintro φ (rfl | rfl)
  · exact fun X f h => h
  · exact posOnly_liveHyp cfg 1

theorem lineP_settled : ∀ X, FTreeGuard cfg.T lineP X → Settled cfg.cut X := by
  intro X hX p q t t' hp hq h
  have hL : LiveHyp cfg 1 X := hX.2.1 _ (by simp [lineP])
  exact (filter_slot_suffix (slot := id) (hL.decreasing p t hp) _).trans
    (hX.2.1 _ List.mem_cons_self p q t t' hp hq h)

/-- **Non-vacuity of the hypotheses.** For the one-validator instance (`3 · 0 < W = 1`), every
hypothesis of `ffg_realizes` holds with window `σ = 1` and pruning depth `d = 0`, with
`out = lv`, `ov = id`, `exT = exF = lv 0`. -/
theorem instance_hyps :
    (∀ s e, SPComp.NoFail (lineST.step s e)) ∧
      (∀ s e, ∃ C : SPComp ℕ, lineST.step s e = SPComp.bind C fun s' => SPComp.pure (s', lv s')) ∧
      (∀ s, id (lv s) = lv s) ∧
      FTreeGuard cfg.T lineP
        (traceOf lv (· ∈ cfg.H) lineST.init ([] : Trace ℕ Unit (TreeView (Fin 1) ℕ))) ∧
      (∀ φ ∈ lineP, PosOnly φ) ∧ (∀ X, FTreeGuard cfg.T lineP X → Settled cfg.cut X) ∧
      1 ≤ cfg.Δ ∧ 3 * stake cfg.w (Finset.univ \ cfg.H) < totalStake cfg.w ∧
      (∀ X, FTreeGuard cfg.T lineP X → LiveHyp cfg 1 X) ∧
      (∀ v p, cfg.cut v p = (v.pos p).filter fun b => decide (cfg.slot b + 0 ≤ v.round)) ∧
      1 ≤ cfg.E ∧ cfg.v₀ ∈ cfg.H ∧ cfg.start = 2 * cfg.E + 1 + 0 := by
  refine ⟨fun _ _ => SPComp.pure_noFail _, fun n _ => ⟨SPComp.pure (n + 1), by rw [SPComp.pure_bind]; rfl⟩,
    fun _ => rfl, ?_, lineP_posOnly, lineP_settled, le_rfl, by decide,
    fun X hX => hX.2.1 _ (by simp [lineP]), fun _ _ => rfl, le_rfl, Finset.mem_univ _, rfl⟩
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro p t t' _ _; simp [traceOf, stAt_nil]
  · intro p t _; simp [traceOf, stAt_nil, lv]
  · intro p t _; simp [TreeTrace.chains, traceOf, stAt_nil, lv, lineST, line]
  · intro t t' _; simp [traceOf, stAt_nil]
  · simp only [lineP, List.mem_cons, List.not_mem_nil, or_false]
    rintro φ (rfl | rfl)
    · intro p q t t' _ _ _
      simp only [TreeTrace.chains, traceOf, stAt_nil, List.drop_zero]
      exact List.suffix_refl _
    · exact
        { growth := fun p t a _ ha => by simp [traceOf, stAt_nil, lineST, lv] at ha
          decreasing := fun p t _ => by simp [traceOf, stAt_nil, lineST, lv, line]
          genesis_mem := fun p t _ => by simp [traceOf, stAt_nil, lineST, lv, line, cfg, lineTree]
          genesis_slot := rfl
          inTree := fun p t _ => by simp [TreeTrace.chains, traceOf, stAt_nil, lv, lineST, line]
          round_zero := by simp [traceOf, stAt_nil, lineST, lv]
          round_step := fun t => by simp [traceOf, stAt_nil, lineST, lv] }
  · rintro p q t t' b b' i j _ _ ⟨C, hC, -⟩
    simp [TreeTrace.finChains, traceOf, stAt_nil, lv] at hC

/-- **The realization for the instance**: the FFG gadget over the
one-party tree realizes `F_FinTree`, whose properties include finality liveness, with
advantage `0` against every environment. -/
theorem instance_realizes :
    Realizes (ffgWorld cfg lineST lv lineP (lv 0) id (lv 0))
      (ideal (finF cfg lineST lv lineP (lv 0) id (lv 0) 1 0)
        (ffgSim cfg lineST lv lineP (lv 0) id (lv 0)))
      (fun _ _ => 0) := by
  obtain ⟨hST, hout, hov, hinit, hP, hset, hΔ, hA, hL, hcut, hE, hv₀, hstart⟩ := instance_hyps
  exact (ffg_realizes hST lv hov hinit hP hset hΔ hA hL hcut hE hv₀ hstart hout).realizes

/-- A run of the gadget without adversarial actions: at time `t` the view `[t, …, 0]`. -/
noncomputable def runG : ℕ → GCore (Fin 1) ℕ
  | 0 => ginit cfg (lv 0)
  | t + 1 => gstep cfg (runG t) .idle (lv (t + 1))

theorem runG_view (t : ℕ) : (runG t).view = lv t := by
  cases t with
  | zero => rfl
  | succ t => exact gstep_view _ _ _ _

theorem runG_run : Run cfg runG where
  init_cast := rfl
  init_seen _ := rfl
  init_nr := rfl
  init_sch := rfl
  step t := Or.inr ⟨.idle, lv (t + 1), rfl⟩
  rounds t t' h := by
    show (runG t).view.round ≤ (runG t').view.round
    rw [runG_view, runG_view]
    exact h
  settled p q t t' _ _ h := by
    show cfg.cut (runG t).view p <:+ (runG t').view.pos q
    rw [runG_view, runG_view]
    show (line t).filter (fun b => decide (b ≤ t)) <:+ line t'
    rw [filter_line, min_self]
    exact line_suffix h

theorem runG_live : LiveHyp cfg 1 (posTT cfg runG) where
  growth p t a _ ha := by
    change a + 1 ≤ (runG t).view.round at ha
    rw [runG_view] at ha
    refine ⟨a + 1, ?_, Nat.lt_succ_self a, le_rfl⟩
    show a + 1 ∈ (runG t).view.pos p
    rw [runG_view]
    exact mem_line.2 ha
  decreasing p t _ := by
    show ((runG t).view.pos p).Pairwise fun b b' => b' < b
    rw [runG_view]
    exact line_pairwise_lt t
  genesis_mem p t _ := by
    show 0 ∈ (runG t).view.pos p
    rw [runG_view]
    exact mem_line.2 (Nat.zero_le _)
  genesis_slot := rfl
  inTree p t _ := by
    show ((runG t).view.pos p).Pairwise fun b b' => lineTree.anc b' b
    rw [runG_view]
    exact lineTrace_chainsInTree () t trivial
  round_zero := rfl
  round_step t := by
    show (runG (t + 1)).view.round ≤ (runG t).view.round + 1
    rw [runG_view, runG_view]
    exact le_rfl

/-- **Non-vacuity of the conclusion.** The run `runG` of the gadget of the instance, in which
the gadget casts the honest votes itself, satisfies the hypotheses of `finTreeGuard_of_run` and
`Run.updatedWithin`, its reported trace satisfies the guard of `F_FinTree^P'`, and from time
`4` on the honest party has a final block at most `5` rounds behind the current round. -/
theorem run_finalizes :
    Run cfg runG ∧ (posTT cfg runG).WellFormed cfg.T ∧ (∀ φ ∈ lineP, φ (posTT cfg runG)) ∧
      FinTreeGuard cfg.T (finP cfg lineP 1 0) cfg.Δ (suppF cfg) (finTT cfg runG) ∧
      ∀ t, 4 ≤ t → ∃ b ∈ ((finTT cfg runG).st t).fin 0, t ≤ b + 5 := by
  obtain ⟨-, -, -, -, hP, -, hΔ, hA, -, hcut, hE, hv₀, hstart⟩ := instance_hyps
  have hwf : (posTT cfg runG).WellFormed cfg.T := by
    refine ⟨fun p t t' _ h => ?_, fun p t _ => ?_, fun p t _ => ?_, runG_run.rounds⟩
    · show (runG t).view.tree p ⊆ (runG t').view.tree p
      rw [runG_view, runG_view]
      exact (line_suffix h).subset
    · show (runG t).view.pos p ⊆ (runG t).view.tree p
      rw [runG_view]
      exact List.Subset.refl _
    · exact runG_live.inTree p t ‹_›
  have hPG : ∀ φ ∈ lineP, φ (posTT cfg runG) := by
    simp only [lineP, List.mem_cons, List.not_mem_nil, or_false]
    rintro φ (rfl | rfl)
    · intro p q t t' _ _ h
      show (runG t).view.pos p <:+ (runG t').view.pos q
      rw [runG_view, runG_view]
      exact line_suffix h
    · exact runG_live
  have hU := runG_run.updatedWithin hA hE hΔ runG_live hcut hv₀ hstart
  obtain ⟨hwf', hPs, hrest⟩ := finTreeGuard_of_run runG_run hΔ hA hP hwf hPG
  refine ⟨runG_run, hwf, hPG, ⟨hwf', List.forall_mem_cons.2 ⟨hU, hPs⟩, hrest⟩, fun t ht => ?_⟩
  obtain ⟨b, hb, hle⟩ := hU 0 t (Finset.mem_univ _) (by
    change _ ≤ (runG t).view.round
    rw [runG_view]
    exact ht)
  refine ⟨b, hb, ?_⟩
  change (runG t).view.round ≤ b + (3 * 1 + 2 * 1 + 0 + 1 - 1) at hle
  rw [runG_view] at hle
  exact hle

end Example

/-! ## An instance with a fork and an adversarial validator -/

namespace ForkExample

open CatCryptCore.Consensus.Finality.Examples FFG.Examples

/-- The tree view at round `n`: every party has the tree `[2, 1, 0]` of `forkTree` (genesis `0`
with the two children `1` and `2`), the position `[1, 0]`, and no final blocks of `F_Tree`. -/
def fv (n : ℕ) : TreeView (Fin 4) (Fin 3) := ⟨n, fun _ => [2, 1, 0], fun _ => [1, 0], fun _ => []⟩

/-- The gadget parameters: the block tree `forkTree`, four validators of stake `1`, the honest
validators `0, 1, 2`, slots equal to block numbers, epochs of one slot, voting on the full
position, delivery bound `1`, and the schedule from round `1` read off the position of the
validator `0`. -/
def cfg : Cfg (Fin 4) (Fin 3) :=
  ⟨forkTree, unitStake, {0, 1, 2}, blockSlot, 1, fun v p => v.pos p, 1, 1, 0⟩

/-- The tree property: common prefix `0`. -/
def forkP : List (TreeTrace (Fin 4) (Fin 3) → Prop) := [fun X => X.CommonPrefix 0]

theorem cfg_hA : 3 * stake cfg.w (Finset.univ \ cfg.H) < totalStake cfg.w := by decide

theorem forkP_posOnly : ∀ φ ∈ forkP, PosOnly φ := by
  simp only [forkP, List.mem_singleton, forall_eq]
  exact fun X f h => h

/-- The votes of the first round of the honest schedule: the honest validators `0, 1, 2` vote
from genesis to `(1, 1)` and from `(1, 1)` to `(1, 2)`. -/
def hV : Finset (Vote (Fin 4) (Fin 3)) :=
  {vote 0 0 0 1 1, vote 1 0 0 1 1, vote 2 0 0 1 1, vote 0 1 1 1 2, vote 1 1 1 1 2, vote 2 1 1 1 2}

/-- The adversarial votes: validator `3` votes from genesis to the conflicting checkpoint
`(2, 1)`, and then from genesis to `(1, 1)` (a double vote). -/
def a₁ : Vote (Fin 4) (Fin 3) := vote 3 0 0 2 1

@[inherit_doc a₁]
def a₂ : Vote (Fin 4) (Fin 3) := vote 3 0 0 1 1

/-- The gadget after one step: the view of round `1`, the honest round `0` of the schedule
(`hV`) and the adversarial vote `a₁`. -/
noncomputable def g₁ : GCore (Fin 4) (Fin 3) := gstep cfg (ginit cfg (fv 0)) (.avote a₁) (fv 1)

/-- The gadget after two steps: the view of round `2` and the adversarial vote `a₂`; the next
honest round is due at round `3`. -/
noncomputable def g₂ : GCore (Fin 4) (Fin 3) := gstep cfg g₁ (.avote a₂) (fv 2)

/-- A run of the gadget: two steps, after which nothing changes. -/
noncomputable def runF : ℕ → GCore (Fin 4) (Fin 3)
  | 0 => ginit cfg (fv 0)
  | 1 => g₁
  | _ + 2 => g₂

theorem gstep_cast_avote {c : Cfg (Fin 4) (Fin 3)} {g : GCore (Fin 4) (Fin 3)}
    {x : Vote (Fin 4) (Fin 3)} {v : TreeView (Fin 4) (Fin 3)} (h : x.validator ∉ c.H) :
    (gstep c g (.avote x) v).cast = insert (x, v.round) (hround c { g with view := v }).cast := by
  rw [gstep_cast]
  have hv := (hround_spec c { g with view := v }).1
  dsimp only [act]
  rw [if_pos h]
  dsimp only
  rw [hv]

/-- The votes of the first round of the schedule of the instance are `hV`. -/
theorem schedVotes_first : schedVotes cfg { ginit cfg (fv 0) with view := fv 1 } = hV := by
  have hE : livenessEpoch (∅ : Finset (Vote (Fin 4) (Fin 3))) (genesisCheckpoint forkTree) = 1 := by
    simp [livenessEpoch, genesisCheckpoint]
  have h1 : schedExt cfg (fv 1) 0 1 = 1 := by
    unfold schedExt
    rw [extendTo_of_anc (by show forkTree.anc 0 (boundaryBlock blockSlot 1 0 [1, 0] 1); decide)]
    rfl
  have h2 : schedExt cfg (fv 1) 1 2 = 1 := by
    unfold schedExt
    rw [extendTo_of_anc (by show forkTree.anc 1 (boundaryBlock blockSlot 1 0 [1, 0] 2); decide)]
    rfl
  show livenessVotes cfg.H (schedExt cfg (fv 1)) ∅ (genesisCheckpoint forkTree) = hV
  unfold livenessVotes livenessNext livenessTarget
  rw [hE]
  have h0 : (genesisCheckpoint forkTree).block = 0 := rfl
  rw [h0, h1, h2]
  decide

/-- Every vote of `hV` satisfies the honest voting rule at round `1`. -/
theorem honestCast_first : honestCast cfg { ginit cfg (fv 0) with view := fv 1 } = hV := by
  classical
  unfold honestCast
  rw [schedVotes_first]
  refine Finset.filter_true_of_mem ?_
  have h : ∀ x ∈ hV, HonestOK cfg (fv 1) (∅ ∪ hV) x := by unfold HonestOK; decide
  exact h

theorem cast_g₁ : g₁.cast = insert (a₁, 1) (hV.image fun x => (x, 1)) := by
  unfold g₁
  rw [gstep_cast_avote (by decide)]
  rcases (hround_spec cfg { ginit cfg (fv 0) with view := fv 1 }).2.2 with
    ⟨-, -, -, hlt⟩ | ⟨-, hc, -, -⟩
  · exact absurd hlt (by decide)
  · rw [hc, honestCast_first]
    rfl

theorem cast_g₂ : g₂.cast = insert (a₂, 2) (insert (a₁, 1) (hV.image fun x => (x, 1))) := by
  unfold g₂
  rw [gstep_cast_avote (by decide)]
  have hnr : g₁.nr = 1 := by
    unfold g₁
    rw [gstep_nr]
    rcases (hround_spec cfg { ginit cfg (fv 0) with view := fv 1 }).2.2 with
      ⟨-, -, -, hlt⟩ | ⟨-, -, hn, -⟩
    · exact absurd hlt (by decide)
    · exact hn
  rcases (hround_spec cfg { g₁ with view := fv 2 }).2.2 with ⟨hc, -, -, -⟩ | ⟨hle, -, -, -⟩
  · rw [hc, cast_g₁]
    rfl
  · change 1 + g₁.nr * (2 * 1) ≤ 2 at hle
    rw [hnr] at hle
    omega

theorem runF_view (t : ℕ) : (runF t).view = fv (min t 2) := by
  rcases t with _ | _ | t
  · rfl
  · exact gstep_view _ _ _ _
  · rw [show min (t + 2) 2 = 2 by omega]; exact gstep_view _ _ _ _

/-- All votes of the run. -/
def allV : Finset (Vote (Fin 4) (Fin 3)) := insert a₂ (insert a₁ hV)

theorem votes_runF_two : (runF 2).votes = allV := by
  show g₂.votes = allV
  rw [GCore.votes, cast_g₂]
  decide

theorem hV_subset_seen (p : Fin 4) : hV ⊆ (runF 2).seen p := by
  intro x hx
  show x ∈ (gstep cfg g₁ (.avote a₂) (fv 2)).seen p
  rw [gstep_seen]
  refine Finset.mem_union_right _ ?_
  rw [← gstep_cast]
  show x ∈ overdue 1 2 g₂.cast
  rw [cast_g₂]
  exact (show hV ⊆ overdue 1 2 (insert (a₂, 2) (insert (a₁, 1) (hV.image fun x => (x, 1)))) by
    decide) hx

theorem runF_run : Run cfg runF where
  init_cast := rfl
  init_seen _ := rfl
  init_nr := rfl
  init_sch := rfl
  step t := by
    rcases t with _ | _ | t
    · exact Or.inr ⟨.avote a₁, fv 1, rfl⟩
    · exact Or.inr ⟨.avote a₂, fv 2, rfl⟩
    · exact Or.inl rfl
  rounds t t' h := by
    show (runF t).view.round ≤ (runF t').view.round
    rw [runF_view, runF_view]
    simp only [fv]
    omega
  settled p q t t' _ _ _ := by
    show (runF t).view.pos p <:+ (runF t').view.pos q
    rw [runF_view, runF_view]
    exact List.suffix_refl _

theorem hV_finalized : Finalized cfg.T cfg.w hV ⟨1, 1⟩ :=
  finalized_of_links (c' := ⟨1, 2⟩) (by decide) rfl (by decide)

/-- **Accountable safety on a run with a fork and an adversarial validator.** The run `runF`
of the gadget over `forkTree` (blocks `1` and `2` conflict) satisfies the hypotheses of
`finTreeGuard_of_run`, and its reported trace satisfies the guard of `F_FinTree^P'`. The
adversarial validator `3` votes for the conflicting checkpoint `(2, 1)` and double-votes, and it
is the only slashable validator, of stake `1` with `3 · 1 < W = 4`. The honest votes are those
of the first round of the schedule, cast by the gadget at round `1`. Block `1` is final for the
honest party `0` at time `2`, and at every time no two checkpoints finalized by the cast votes
lie on conflicting blocks (`Run.anc_of_finalized`, from `FFG.anc_of_kFinalized_of_justified`). -/
theorem run_accountable :
    Run cfg runF ∧
      FinTreeGuard cfg.T ((fun X => X.FinalityRespectingPos) :: FinalOnHonestPos :: forkP) cfg.Δ
        (suppF cfg) (finTT cfg runF) ∧
      cfg.T.Conflicting 1 2 ∧ vote 3 0 0 2 1 ∈ (runF 2).votes ∧
      slashable (runF 2).votes = {3} ∧
      3 * stake cfg.w (slashable (runF 2).votes) < totalStake cfg.w ∧
      (∃ i, (finTT cfg runF).finalized 2 0 1 i) ∧
      ∀ t b b' e e', Finalized cfg.T cfg.w (runF t).votes ⟨b, e⟩ →
        Finalized cfg.T cfg.w (runF t).votes ⟨b', e'⟩ → ¬ cfg.T.Conflicting b b' := by
  have hA := cfg_hA
  have hΔ : 1 ≤ cfg.Δ := le_rfl
  have hP := forkP_posOnly
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
    by rw [votes_runF_two]; decide, by rw [votes_runF_two]; decide,
    by rw [votes_runF_two]; decide, ?_, ?_⟩
  · have hfin : Finalized cfg.T cfg.w ((runF 2).seen 0) ⟨1, 1⟩ :=
      Finalized.mono (hV_subset_seen 0) hV_finalized
    have hmem : 1 ∈ finList cfg ((runF 2).seen 0) :=
      mem_finList (by decide) hfin fun b' hb' =>
        runF_run.finalized_unique hA (Finalized.mono (runF_run.seen_subset 2 0) hfin)
          (Finalized.mono (runF_run.seen_subset 2 0) hb')
    obtain ⟨s, l, hsl⟩ := List.append_of_mem hmem
    refine ⟨l.length, l, ?_, rfl⟩
    show 1 :: l <:+ finList cfg ((runF 2).seen 0)
    rw [hsl]
    exact List.suffix_append s _
  · intro t b b' e e' hb hb' hc
    rcases le_total e e' with hle | hle
    · exact hc.1 (runF_run.anc_of_finalized hA hb hb' hle)
    · exact hc.2 (runF_run.anc_of_finalized hA hb' hb hle)

end ForkExample

end CatCryptCore.Consensus.UC.FFGGadget
