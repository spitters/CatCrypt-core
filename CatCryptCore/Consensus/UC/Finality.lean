/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.UC.FinalityGadget
public import CatCryptCore.Crypto.UCTransparentHybrid

@[expose] public section
set_option autoImplicit false

/-!
# FFG in the `F_Tree`-hybrid world realizes `F_FinTree`

Row C4b (FIN-REALIZE) of the Ethereum consensus plan. The Casper FFG finality gadget of
`CatCryptCore.Consensus.UC.FinalityGadget`, run as a hybrid protocol with one call per
activation to the tree functionality `F_Tree^P` of row C3, realizes the finality
functionality `F_FinTree^P'` of row C3 perfectly (advantage `0` against every environment)
when the adversarial validators hold less than a third of the total stake `W`. The statement
is information-theoretic.

## The hybrid protocol

The subroutine is the ideal world `ideal (treeF …) ST` of `F_Tree^P` with an arbitrary lossless
tree simulator `ST` (for instance the PoS-NSB simulator `Chain.chainSim` of row C4a). An outer
event is a pair of a tree event and a gadget action (`GAct`). The gadget (`ffgHybrid`) passes
the tree event to `F_Tree`, reads the tree view `ov o` from its output `o`, and takes one
gadget step (`gstep`) with that view and the action. If `F_Tree` answers with its exploded
output `exT`, the gadget stops for good (`GSt.dead`) and from then on outputs `exF`. Otherwise
it outputs `finView`: the tree view with the final lists of the gadget.

## The simulator and the functionality

`ffgSim` runs the gadget against `F_Tree` internally, with the tree simulator `ST`, and
proposes its states to `F_FinTree` (the copy simulator of C3 for the hybrid world).
`finF` is `F_FinTree^P'` over the states of the simulator, with the view `finView` of the
gadget component, `P' = finality-respecting positions :: P`, delivery bound `Δ`, and the
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
  the guard of `F_FinTree`, the functionality never explodes and copying is exact. The theorem
  is therefore not tagged as a UC statement with a non-trivial simulator.
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
the gadget component, honest parties `H`, `P' = finality-respecting positions :: P`, delivery
bound `Δ`, support guard `suppF`, exploded output `exF`. -/
noncomputable def finF :
    TFunc (WSt Party Blk σT ET OT) (ET × GAct Party Blk) (TreeView Party Blk) :=
  finTree (fun s => finView c s.1.core) (· ∈ c.H) c.T ((fun X => X.FinalityRespectingPos) :: P)
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
    FinTreeGuard c.T ((fun X => X.FinalityRespectingPos) :: P) c.Δ (suppF c) (finTT c G) := by
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
    FinTreeGuard c.T ((fun X => X.FinalityRespectingPos) :: P) c.Δ (suppF c)
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
      FinTreeGuard c.T ((fun X => X.FinalityRespectingPos) :: P) c.Δ (suppF c)
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
/-- **FFG in the `F_Tree`-hybrid world realizes `F_FinTree` perfectly (row C4b).**
Let the tree simulator `ST` be lossless and output a function `out` of its new state from
which the gadget reads the view of that state (`ov (out s) = vwT s`); let the guard of
`F_Tree^P` hold on the empty trace; let every property of `P` read only rounds, trees and
positions; let the guard of `F_Tree^P` imply that the pruned positions `cut` are settled; let
`1 ≤ Δ`; and let the adversarial validators hold less than a third of the total stake,
`3 * stake w (univ \ H) < W`. Then the FFG gadget running with the ideal world of `F_Tree^P`
(`ffgWorld`) realizes the ideal world of `F_FinTree^P'` (`finF`, with
`P' = finality-respecting positions :: P`, `Δ`-updatedness and the support guard `suppF`)
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
bound: with the environment strategy as honest input, the environment's final state as output,
empty leakage and the identity simulator map, the view maps of the `F_Tree`-hybrid world and of
the ideal world of `F_FinTree` are at distance `0` for every environment. -/
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

end CatCryptCore.Consensus.UC.FFGGadget
