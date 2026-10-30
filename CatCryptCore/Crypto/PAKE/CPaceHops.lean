/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PAKE.CPaceSquare
public import CatCryptCore.Crypto.PAKE.CPaceH1
public import CatCryptCore.Crypto.PAKE.DHExtractKit
public import CatCryptCore.Crypto.OracleLazyMulti

/-!
# The hops of the CPace square

`cpace_realizesSim_oracleGame` (`CatCryptCore.Crypto.PAKE.CPaceSquare`) bounds the CPace square
by the advantage of an oracle adversary between the real game `realGame G` and the simulated game
`simGame G`. This file bounds that advantage by the probability of one bad event: the outputs of
the real and of the simulated world differ in a joint run.

## The simulated world as a keyed game

The oracle of `simGame G` is the distribution of a step of the simulator running with
`F_lePAKE`. Every component of that step is the lift of an explicit probability mass function:
`simStartP`, `simResumeP`, `simFinishP` for the simulator and `fStepP` for `F_lePAKE`, composed
by `driveP`. The step is `simWorldP` (`simWorld_step_eq`), and the oracle of `simGame G` is its
distribution (`simGame_oracle_eq`).

The simulator samples the table of `H1` at its first activation. `idealGame G` samples the table
as the key of the game and runs `simWorldP` with the table in place; it accepts with the
probability of `simGame G` (`simGame_accept_eq`).

## Steps as functions of one draw

A step of the real world draws at most one scalar and one value of `H2`; it is the image of a
uniform pair under `realDet` (`realGame_oracle_eq`). A step of the simulated world draws at most a
scalar or a value of `H2` at its start and one key at each of its two calls to `F_lePAKE`; it is
the image of a uniform draw `((z, k₀), k₁, k₂)` under `simWorldD` (`idealGame_oracle_eq`).

## The joint world

`jointD` runs both worlds on one draw: a new party with password `pw` takes the secret `z` in the
simulated world and `z / td pw` in the real world, and a fresh value of `H2` in the real world is
read from the slot of the draw that the simulated world reads at the same place (`cpl`). Its
state records whether the two outputs differed. Answering with the real outputs (`jointReal`), its
real part is the real game; answering with the simulated outputs (`jointSim`), its simulated part
is `idealGame G`. The two answers agree on every transition whose outputs agree, so the advantage
is at most the probability `badGame G B` that the outputs differ at some step of the run against
`jointSim` (`advantage_le_badGame`).

## Main definitions

* `driveP`: an activation of a multi-call simulator over probability mass functions.
* `simWorldP`: the step of the simulated world.
* `idealGame`: the simulated world with the table of `H1` as the key.
* `realDet`, `simWorldD`: the steps of the two worlds as functions of a draw.
* `jointD`, `jointReal`, `jointSim`: the joint world.
* `badGame`: the bad-event experiment.

## Main results

* `simGame_oracle_eq`: the oracle of `simGame G` is the distribution `simWorldP`.
* `simGame_accept_eq`: `simGame G` and `idealGame G` accept with the same probability.
* `realGame_oracle_eq`, `idealGame_oracle_eq`: the oracles as images of uniform draws.
* `advantage_le_badGame`: the advantage between `realGame G` and `simGame G` is at most the
  probability of the bad event.
* `run_flagWhen_le_of_inv`: a bad flag implied by another along an invariant.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.PAKE.CPaceHops

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FPAKE
open CatCrypt.Crypto.PAKE.DHExtract CatCrypt.Crypto.PAKE.CPaceSquare CatCrypt.NonUniform
open scoped ENNReal

/-! ## Computations given by probability mass functions

This section belongs upstream, in `CatCryptCore.Crypto.PAKE.CPaceSquare` beside `PureNF.pmf`. -/

/-- Lifting a probability mass function to a computation is injective. -/
theorem liftPMF_injective {α : Type} : Function.Injective (liftPMF (α := α)) := by
  intro p q h
  have h' := congrFun h Heap.empty
  simp only [liftPMF] at h'
  ext a
  have := congrArg (fun r : PMF (Option (α × Heap)) => r (some (a, Heap.empty))) h'
  rw [PMF.map_apply, PMF.map_apply, tsum_eq_single a, tsum_eq_single a, ite_eq_left rfl,
    ite_eq_left rfl] at this
  · exact this
  all_goals
    intro b hb
    rw [ite_eq_right]
    intro hc
    exact hb (congrArg Prod.fst (Option.some_injective _ hc)).symm

/-- The distribution of a computation that is the lift of `p` is `p`. -/
theorem PureNF.pmf_eq {α : Type} {c : SPComp α} (hc : PureNF c) {p : PMF α}
    (h : c = liftPMF p) : hc.pmf = p :=
  liftPMF_injective (hc.eq_liftPMF.symm.trans h)

/-- `SPComp.map` of a lift is the lift of the image. -/
theorem map_liftPMF {α β : Type} (f : α → β) (p : PMF α) :
    SPComp.map f (liftPMF p) = liftPMF (p.map f) :=
  liftPMF_bind_pure p f

/-- **An activation of a multi-call simulator over probability mass functions**: the steps of
the subroutine, the resumption and the finish of the simulator are distributions. -/
noncomputable def driveP {σ τ O EG OG : Type} (step : τ → EG → PMF (τ × OG))
    (res : σ → OG → PMF (σ × (EG ⊕ O))) (fin : σ → OG → PMF (σ × O)) :
    ℕ → σ → EG ⊕ O → τ → PMF (σ × τ × O)
  | _, s, .inr o, t => PMF.pure (s, t, o)
  | 0, s, .inl g, t =>
    (step t g).bind fun q => (fin s q.2).map fun r => (r.1, q.1, r.2)
  | n + 1, s, .inl g, t =>
    (step t g).bind fun q => (res s q.2).bind fun r => driveP step res fin n r.1 r.2 q.1

/-- An activation of a multi-call simulator whose components are lifts is the lift of `driveP`. -/
theorem drive_eq_liftPMF {σ τ E O EG OG : Type} (π : MultiHybrid σ E O EG OG) (X : Sys τ EG OG)
    (step : τ → EG → PMF (τ × OG)) (res : σ → OG → PMF (σ × (EG ⊕ O)))
    (fin : σ → OG → PMF (σ × O)) (hX : ∀ t g, X.step t g = liftPMF (step t g))
    (hr : ∀ s o, π.resume s o = liftPMF (res s o)) (hf : ∀ s o, π.finish s o = liftPMF (fin s o)) :
    ∀ n s d t, π.drive X n s d t = liftPMF (driveP step res fin n s d t) := by
  intro n
  induction n with
  | zero =>
    rintro s (g | o) t
    · simp only [MultiHybrid.drive, driveP, hX, hf, liftPMF_bind_pure, liftPMF_bind_liftPMF]
    · simp only [MultiHybrid.drive, driveP, liftPMF_pure]
  | succ n ih =>
    rintro s (g | o) t
    · simp only [MultiHybrid.drive, driveP, hX, hr, ih, liftPMF_bind_liftPMF]
    · simp only [MultiHybrid.drive, driveP, liftPMF_pure]

/-- The step of a multi-call simulator over a subroutine, both given by distributions. -/
noncomputable def withSubP {σ τ E O EG OG : Type} (start : σ → E → PMF (σ × (EG ⊕ O)))
    (step : τ → EG → PMF (τ × OG)) (res : σ → OG → PMF (σ × (EG ⊕ O)))
    (fin : σ → OG → PMF (σ × O)) (fuel : ℕ) (t : σ × τ) (e : E) : PMF ((σ × τ) × O) :=
  (start t.1 e).bind fun r =>
    (driveP step res fin fuel r.1 r.2 t.2).map fun p => ((p.1, p.2.1), p.2.2)

/-- A step of a multi-call simulator over a subroutine, whose components are lifts, is the lift of
`withSubP`. -/
theorem withSub_step_eq_liftPMF {σ τ E O EG OG : Type} (π : MultiHybrid σ E O EG OG)
    (X : Sys τ EG OG) (start : σ → E → PMF (σ × (EG ⊕ O))) (step : τ → EG → PMF (τ × OG))
    (res : σ → OG → PMF (σ × (EG ⊕ O))) (fin : σ → OG → PMF (σ × O))
    (hs : ∀ s e, π.start s e = liftPMF (start s e)) (hX : ∀ t g, X.step t g = liftPMF (step t g))
    (hr : ∀ s o, π.resume s o = liftPMF (res s o)) (hf : ∀ s o, π.finish s o = liftPMF (fin s o))
    (t : σ × τ) (e : E) :
    (π.withSub X).step t e = liftPMF (withSubP start step res fin π.fuel t e) := by
  simp only [MultiHybrid.withSub, withSubP, hs, drive_eq_liftPMF π X step res fin hX hr hf,
    liftPMF_bind_pure, liftPMF_bind_liftPMF]

/-- `driveP` preserves a property of the simulator state that its resumption and finish
preserve. -/
theorem driveP_support {σ τ O EG OG : Type} (step : τ → EG → PMF (τ × OG))
    (res : σ → OG → PMF (σ × (EG ⊕ O))) (fin : σ → OG → PMF (σ × O)) (P : σ → Prop)
    (hr : ∀ s o, P s → ∀ y ∈ (res s o).support, P y.1)
    (hf : ∀ s o, P s → ∀ y ∈ (fin s o).support, P y.1) :
    ∀ n s d t, P s → ∀ y ∈ (driveP step res fin n s d t).support, P y.1 := by
  intro n
  induction n with
  | zero =>
    rintro s (g | o) t hs y hy
    · simp only [driveP, PMF.support_bind, PMF.support_map, Set.mem_iUnion, Set.mem_image] at hy
      obtain ⟨q, -, r, hr', rfl⟩ := hy
      exact hf s q.2 hs r hr'
    · simp only [driveP, PMF.support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact hs
  | succ n ih =>
    rintro s (g | o) t hs y hy
    · simp only [driveP, PMF.support_bind, Set.mem_iUnion] at hy
      obtain ⟨q, -, r, hr', hy⟩ := hy
      exact ih r.1 r.2 q.1 (hr s q.2 hs r hr') y hy
    · simp only [driveP, PMF.support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact hs

/-! ## Keys sampled at the first query

This section belongs upstream, in `CatCryptCore.Crypto.OracleAdversary`. -/

section LazyKey

variable {K σ D R α : Type}

/-- From a state with the key `k` in place, a run against `O` is the run against `O` with the
key `k` put in place before every call, when every call from a state with `k` in place leaves
`k` in place. -/
theorem run_eq_run_set (O : σ → D → PMF (R × σ)) (set : K → σ → σ) (k : K)
    (hpres : ∀ s d, ∀ x ∈ (O (set k s) d).support, set k x.2 = x.2) (A : OracleAdv D R α)
    (t : σ) (ht : set k t = t) :
    OracleAdv.run O A t = OracleAdv.run (fun s d => O (set k s) d) A t := by
  induction A generalizing t with
  | ret a => rfl
  | rand p f ih => simp only [OracleAdv.run_rand, fun b => ih b t ht]
  | query d f ih =>
    simp only [OracleAdv.run_query]
    rw [ht]
    refine PMF.bind_congr_support _ _ _ fun x hx => ih x.1 x.2 ?_
    exact hpres t d x (by rwa [ht])

/-- **A key sampled at the first query.** Let `O` sample the key `k` from `μ` at its first call
from `s₀` and put it in place (`set k`), and let every call from a state with `k` in place leave
`k` in place. The output of a run against `O` from `s₀` is the output of a run against `O` with
the key put in place, averaged over `k` sampled from `μ` up front. -/
theorem run_map_fst_lazyKey (μ : PMF K) (O : σ → D → PMF (R × σ)) (set : K → σ → σ) (s₀ : σ)
    (h₀ : ∀ d, O s₀ d = μ.bind fun k => O (set k s₀) d)
    (hpres : ∀ k s d, ∀ x ∈ (O (set k s) d).support, set k x.2 = x.2) (A : OracleAdv D R α) :
    (OracleAdv.run O A s₀).map Prod.fst =
      μ.bind fun k => (OracleAdv.run (fun s d => O (set k s) d) A s₀).map Prod.fst := by
  induction A with
  | ret a => simp only [OracleAdv.run_ret, PMF.pure_map, PMF.bind_const]
  | rand p f ih =>
    simp only [OracleAdv.run_rand, PMF.map_bind, ih]
    exact PMF.bind_comm _ _ _
  | query d f ih =>
    simp only [OracleAdv.run_query, h₀, PMF.bind_bind, PMF.map_bind]
    refine congrArg _ (funext fun k => PMF.bind_congr_support _ _ _ fun x hx => ?_)
    rw [run_eq_run_set O set k (hpres k) (f x.1) x.2 (hpres k s₀ d x hx)]

end LazyKey

/-! ## Comparing bad flags along an invariant

This section belongs upstream, in `CatCryptCore.Crypto.OracleLazyMulti` beside `flagWhen`. -/

section FlagMono

variable {D R α σ : Type}

/-- **A bad flag implied by another along an invariant.** Let every call from a state satisfying
`I` either make a transition that is bad for `bad₂`, or make a transition that is not bad for
`bad₁` and reaches a state satisfying `I`. From a state satisfying `I`, the run of `O` flagged by
`bad₁` sets its flag with at most the probability with which the run flagged by `bad₂` sets
its flag. -/
theorem run_flagWhen_le_of_inv (O : σ → D → PMF (R × σ)) (bad₁ bad₂ : σ → D → R × σ → Prop)
    [∀ s d x, Decidable (bad₁ s d x)] [∀ s d x, Decidable (bad₂ s d x)] (I : σ → Prop)
    (hstep : ∀ s d, I s → ∀ x ∈ (O s d).support, bad₂ s d x ∨ (¬ bad₁ s d x ∧ I x.2))
    (A : OracleAdv D R α) (s : σ) (hs : I s) :
    (OracleAdv.run (OracleAdv.flagWhen bad₁ O) A (s, false)).toOuterMeasure
        {y | y.2.2 = true} ≤
      (OracleAdv.run (OracleAdv.flagWhen bad₂ O) A (s, false)).toOuterMeasure
        {y | y.2.2 = true} := by
  let bad₁' : σ × Bool → D → R × (σ × Bool) → Prop := fun st d x => bad₁ st.1 d (x.1, x.2.1)
  let O₂₁ := OracleAdv.flagWhen bad₁' (OracleAdv.flagWhen bad₂ O)
  have h₁ : (OracleAdv.run O₂₁ A ((s, false), false)).map
      (Prod.map id fun st => (st.1.1, st.2)) =
        OracleAdv.run (OracleAdv.flagWhen bad₁ O) A (s, false) :=
    OracleAdv.run_map_state _ _ _ (fun st d => by
      simp only [O₂₁, bad₁', OracleAdv.flagWhen, PMF.map_comp]
      rfl) A _
  have h₂ : (OracleAdv.run O₂₁ A ((s, false), false)).map (Prod.map id Prod.fst) =
      OracleAdv.run (OracleAdv.flagWhen bad₂ O) A (s, false) :=
    OracleAdv.run_flagWhen_map bad₁' _ A _ false
  have hsupp : ∀ y ∈ (OracleAdv.run O₂₁ A ((s, false), false)).support,
      y.2.2 = true → y.2.1.2 = true := by
    intro y hy
    have h := OracleForking.run_support_rel O₂₁
      (fun st st' => ((st.2 = true → st.1.2 = true) ∧ (st.1.2 = false → I st.1.1)) →
        ((st'.2 = true → st'.1.2 = true) ∧ (st'.1.2 = false → I st'.1.1)))
      (fun _ h => h) (fun _ _ _ h₁ h₂ h => h₂ (h₁ h)) ?_ A _ y hy
      ⟨fun h => absurd h Bool.false_ne_true, fun _ => hs⟩
    · exact h.1
    · rintro ⟨⟨t, f₂⟩, f₁⟩ d x hx ⟨hf, hI⟩
      simp only [O₂₁, OracleAdv.flagWhen, PMF.support_map, Set.mem_image] at hx
      obtain ⟨y, ⟨x₀, h₀, rfl⟩, rfl⟩ := hx
      cases f₂ with
      | true => simp
      | false =>
        have hf₁ : f₁ = false := by
          cases f₁
          · rfl
          · exact absurd (hf rfl) Bool.false_ne_true
        subst hf₁
        rcases hstep t d (hI rfl) x₀ h₀ with hb | ⟨hb, hI'⟩
        · simp [hb]
        · simp [bad₁', hb, hI']
  rw [← h₁, ← h₂, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  refine PMF.toOuterMeasure_mono _ fun y hy => ?_
  exact hsupp y hy.2 hy.1

end FlagMono

/-! ## The simulated world as distributions -/

section SimWorld

variable {S W Pw K : Type} [Field S] [Fintype S] [DecidableEq S] [DecidableEq W]
  [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K] [Inhabited K] (G : DHGroup S W)

/-- The distribution of `tdStep`. -/
noncomputable def tdStepP (c : SimCore S W Pw K) : PMF ((Pw → Sˣ) × SimCore S W Pw K) :=
  match c.td with
  | some td => PMF.pure (td, c)
  | none => (PMF.uniformFintype (Pw → Sˣ)).map fun td => (td, { c with td := some td })

/-- The distribution of `honCore`. -/
noncomputable def honCoreP (c : SimCore S W Pw K) (sid pid peer : PartyId) (role : Role) :
    PMF (SimCore S W Pw K) :=
  if sid = 0 ∧ pid ≤ 1 ∧ c.info pid = none then
    if Active sid pid peer = true then
      (PMF.uniformFintype S).map fun z =>
        { c with info := Function.update c.info pid (some (peer, role)),
                 zs := Function.update c.zs pid (some z) }
    else PMF.pure { c with info := Function.update c.info pid (some (peer, role)) }
  else PMF.pure c

/-- The distribution of `honStep`. -/
noncomputable def honStepP (c : SimCore S W Pw K) :
    Option (PartyId × PartyId × PartyId × Role) → PMF (SimCore S W Pw K)
  | some (sid, pid, peer, role) =>
    (honCoreP c sid pid peer role).map fun c' => { c' with phase := .fwd }
  | none => PMF.pure { c with phase := .fwd }

/-- The distribution of `h2Core`. -/
noncomputable def h2CoreP (td : Pw → Sˣ) (c : SimCore S W Pw K) (x : Inp W) :
    PMF (SimCore S W Pw K × Dec Pw W K) :=
  match lateTarget G td c x with
  | some (pid, pw) =>
    PMF.pure ({ c with pend := Function.update c.pend pid none, phase := .late x },
      sCall (.lateTestPwd 0 pid pw))
  | none =>
    (PMF.uniformFintype K).map fun k =>
      ({ c with h2 := (x, k) :: c.h2, phase := .rest }, sOut (.hash k))

/-- The distribution of `advCore`. -/
noncomputable def advCoreP (td : Pw → Sˣ) (c : SimCore S W Pw K) :
    RAEv Pw W → PMF (SimCore S W Pw K × Dec Pw W K)
  | .idle => PMF.pure ({ c with phase := .rest }, sOut .ack)
  | .poll => PMF.pure ({ c with phase := .fwd }, sCall .poll)
  | .msg pid => PMF.pure ({ c with phase := .rest }, sOut (.msg ((c.zs pid).map G.pub)))
  | .h1 pw => PMF.pure ({ c with cands := if pw ∈ c.cands then c.cands else c.cands ++ [pw],
                                  phase := .rest }, sOut (.gen (G.pub (td pw))))
  | .h2 x =>
    match c.h2.lookup x with
    | some k => PMF.pure ({ c with phase := .rest }, sOut (.hash k))
    | none => h2CoreP G td c x
  | .send pid m => PMF.pure (sendCore G td c pid m)

/-- The distribution of `simCore`. -/
noncomputable def simCoreP (c : SimCore S W Pw K) (e : OEv Pw W) :
    PMF (SimCore S W Pw K × Dec Pw W K) :=
  (tdStepP c).bind fun p => match e with
    | .inl h => (honStepP p.2 (honPub h)).map fun c' => (c', .inl (.inl h))
    | .inr a => advCoreP G p.1 p.2 a

/-- The distribution of `simStart`. -/
noncomputable def simStartP (s : SimSt S W Pw K) (e : OEv Pw W) :
    PMF (SimSt S W Pw K × Dec Pw W K) :=
  match e with
  | .inr (.h2 x) =>
    match s.2.lookup x with
    | some k => PMF.pure (({ s.1 with phase := .rest }, s.2), sOut (.hash k))
    | none => (simCoreP G s.1 e).map fun r => ((r.1, s.2), r.2)
  | _ => (simCoreP G s.1 e).map fun r => ((r.1, s.2), r.2)

/-- The distribution of `simResume`. -/
noncomputable def simResumeP (s : SimSt S W Pw K) (o : FOut K) :
    PMF (SimSt S W Pw K × Dec Pw W K) :=
  match s.1.phase with
  | .key pid k => PMF.pure (({ s.1 with phase := .done }, s.2), sCall (.newKey 0 pid k))
  | _ => PMF.pure ((simAnswer s o).1, .inr (simAnswer s o).2)

/-- The distribution of a step of the adversary port of `F_lePAKE` with uniform keys. -/
noncomputable def leAdvP (t : St Pw K) : LeAEv Pw K → PMF (St Pw K × AOut K)
  | .idle => PMF.pure (t, .ack)
  | .poll => PMF.pure ((pollStep t).1, .notice (pollStep t).2)
  | .testPwd sid pid g => PMF.pure (testStep t (sid, pid) g, .answer (testAns t (sid, pid) g))
  | .registerTest sid pid => PMF.pure (registerStep t (sid, pid), .ack)
  | .newKey sid pid k =>
    (PMF.uniformFintype K).map fun kf => (newKeyStep t (sid, pid) k kf, .ack)
  | .lateTestPwd sid pid g =>
    (PMF.uniformFintype K).map fun kf =>
      (lateStep t (sid, pid), .reveal (lateReveal t (sid, pid) g kf))

/-- The distribution of a step of `F_lePAKE` with uniform keys. -/
noncomputable def fStepP (t : St Pw K) : FEv Pw K → PMF (St Pw K × FOut K)
  | .inl h => PMF.pure ((leHonStep t h).1, .inl (leHonStep t h).2)
  | .inr a => (leAdvP t a).map fun q => (q.1, .inr q.2)

/-- **The step of the simulated world** as a distribution: the simulator running with
`F_lePAKE`. -/
noncomputable def simWorldP (t : SimSt S W Pw K × St Pw K) (e : OEv Pw W) :
    PMF ((SimSt S W Pw K × St Pw K) × OOut W K) :=
  withSubP (simStartP G) fStepP simResumeP (fun s o => PMF.pure (simAnswer s o)) 1 t e

omit [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- `tdStep` is the lift of `tdStepP`. -/
theorem tdStep_eq (c : SimCore S W Pw K) : tdStep c = liftPMF (tdStepP c) := by
  cases h : c.td <;> simp only [tdStep, tdStepP, h, liftPMF_pure, sample_eq_liftPMF, map_liftPMF]

omit [DecidableEq S] [DecidableEq W] [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K]
  [Inhabited K] in
/-- `honStep` is the lift of `honStepP`. -/
theorem honStep_eq (c : SimCore S W Pw K) (o : Option (PartyId × PartyId × PartyId × Role)) :
    honStep c o = liftPMF (honStepP c o) := by
  rcases o with _ | ⟨sid, pid, peer, role⟩
  · exact liftPMF_pure _
  · simp only [honStep, honStepP, honCore, honCoreP]
    split_ifs <;> simp only [liftPMF_pure, sample_eq_liftPMF, map_liftPMF, PMF.pure_map,
      PMF.map_comp]

omit [Fintype S] [DecidableEq S] [Fintype Pw] in
/-- `advCore` is the lift of `advCoreP`. -/
theorem advCore_eq (td : Pw → Sˣ) (c : SimCore S W Pw K) (a : RAEv Pw W) :
    advCore G td c a = liftPMF (advCoreP G td c a) := by
  cases a with
  | h2 x =>
    cases hl : c.h2.lookup x with
    | some k => simp only [advCore, advCoreP, hl, liftPMF_pure]
    | none =>
      rcases ht : lateTarget G td c x with _ | ⟨pid, pw⟩ <;>
        simp only [advCore, advCoreP, hl, h2Core, h2CoreP, ht, liftPMF_pure, sample_eq_liftPMF,
          map_liftPMF]
  | _ => exact liftPMF_pure _

/-- `simCore` is the lift of `simCoreP`. -/
theorem simCore_eq (c : SimCore S W Pw K) (e : OEv Pw W) :
    simCore G c e = liftPMF (simCoreP G c e) := by
  unfold simCore simCoreP
  rw [tdStep_eq, ← liftPMF_bind_liftPMF]
  congr 1
  funext p
  rcases e with h | a
  · simp only [honStep_eq, map_liftPMF]
  · exact advCore_eq G p.1 p.2 a

/-- `simStart` is the lift of `simStartP`. -/
theorem simStart_eq (s : SimSt S W Pw K) (e : OEv Pw W) :
    simStart G s e = liftPMF (simStartP G s e) := by
  rcases e with h | (_ | _ | _ | _ | x | _)
  case inr.h2 =>
    cases hl : s.2.lookup x <;>
      simp only [simStart, simStartP, hl, liftPMF_pure, simCore_eq, map_liftPMF]
  all_goals simp only [simStart, simStartP, simCore_eq, map_liftPMF]

omit [Fintype S] [DecidableEq S] [DecidableEq W] [Fintype Pw] [DecidableEq Pw] [Fintype K]
  [Nonempty K] in
/-- `simResume` is the lift of `simResumeP`. -/
theorem simResume_eq (s : SimSt S W Pw K) (o : FOut K) :
    simResume s o = liftPMF (simResumeP s o) := by
  rcases s with ⟨c, p⟩
  cases hph : c.phase <;> simp only [simResume, simResumeP, hph, liftPMF_pure]

omit [Fintype Pw] [Inhabited K] in
/-- A step of `F_lePAKE` with uniform keys is the lift of `fStepP`. -/
theorem fStep_eq (t : St Pw K) (e : FEv Pw K) :
    (F_lePAKE (Pw := Pw) (SPComp.sample K)).step t e = liftPMF (fStepP t e) := by
  rcases e with h | a
  · simp only [F_lePAKE, Sys.ofPorts_step_inl, leHonSys, fStepP, liftPMF_pure, map_liftPMF,
      PMF.pure_map]
  · simp only [F_lePAKE, Sys.ofPorts_step_inr, leAdvSys, fStepP]
    cases a <;> simp only [leAdvP, liftPMF_pure, sample_eq_liftPMF, map_liftPMF, PMF.pure_map,
      PMF.map_comp]

/-- The step of the simulated world is the lift of `simWorldP`. -/
theorem simWorld_step_eq (t : SimSt S W Pw K × St Pw K) (e : OEv Pw W) :
    ((simProt G).withSub (F_lePAKE (Pw := Pw) (SPComp.sample K))).step t e =
      liftPMF (simWorldP G t e) :=
  withSub_step_eq_liftPMF _ _ _ _ _ _ (simStart_eq G) fStep_eq simResume_eq
    (fun _ _ => liftPMF_pure _) t e

/-- **The oracle of the simulated game** is the distribution `simWorldP`. -/
theorem simGame_oracle_eq (t : SimSt S W Pw K × St Pw K) (e : OEv Pw W) :
    (simGame G).oracle () t e = (simWorldP G t e).map Prod.swap :=
  congrArg (PMF.map Prod.swap) (PureNF.pmf_eq (simWorld_pureNF G t e) (simWorld_step_eq G t e))

/-! ### The table of `H1` as the key -/

/-- The state of the simulated world with the table `td` of `H1` in place. -/
def setTd (td : Pw → Sˣ) (t : SimSt S W Pw K × St Pw K) : SimSt S W Pw K × St Pw K :=
  (({ t.1.1 with td := some td }, t.1.2), t.2)

/-- **The simulated world with the table of `H1` as the key**: the table is sampled up front, and
each step runs `simWorldP` with the table in place. -/
noncomputable def idealGame : KeyedGame (OEv Pw W) (OOut W K) where
  Key := Pw → Sˣ
  State := SimSt S W Pw K × St Pw K
  keyDist := PMF.uniformFintype (Pw → Sˣ)
  oracle td t e := (simWorldP G (setTd td t) e).map Prod.swap
  init := ((simProt G).init, initSt)

/-- Without a table, `simCoreP` samples the table first. -/
theorem simCoreP_of_td_none (c : SimCore S W Pw K) (hc : c.td = none) (e : OEv Pw W) :
    simCoreP G c e =
      (PMF.uniformFintype (Pw → Sˣ)).bind fun td => simCoreP G { c with td := some td } e := by
  simp only [simCoreP, tdStepP, hc, PMF.bind_map, PMF.pure_bind]
  rfl

/-- Without a table and without programmed inputs, a step of the simulated world samples the
table first. -/
theorem simWorldP_of_td_none (t : SimSt S W Pw K × St Pw K) (hc : t.1.1.td = none)
    (hp : t.1.2 = []) (e : OEv Pw W) :
    simWorldP G t e = (PMF.uniformFintype (Pw → Sˣ)).bind fun td => simWorldP G (setTd td t) e := by
  have hs : simStartP G t.1 e = (PMF.uniformFintype (Pw → Sˣ)).bind fun td =>
      simStartP G ({ t.1.1 with td := some td }, t.1.2) e := by
    rcases e with h | (_ | _ | _ | _ | x | _)
    all_goals simp only [simStartP, hp, List.lookup_nil, simCoreP_of_td_none G _ hc,
      PMF.map_bind]
  simp only [simWorldP, withSubP, hs, PMF.bind_bind]
  rfl

omit [Fintype S] [DecidableEq S] [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K] in
/-- `sendCore` keeps the table of `H1`. -/
theorem sendCore_td (td : Pw → Sˣ) (c : SimCore S W Pw K) (pid : PartyId) (m : W) :
    (sendCore G td c pid m).1.td = c.td := by
  unfold sendCore
  grind [sendCore]

omit [DecidableEq S] [DecidableEq W] [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K]
  [Inhabited K] in
/-- `honStepP` keeps the table of `H1`. -/
theorem honStepP_td (c : SimCore S W Pw K) (o : Option (PartyId × PartyId × PartyId × Role)) :
    ∀ y ∈ (honStepP c o).support, y.td = c.td := by
  rcases o with _ | ⟨sid, pid, peer, role⟩
  · simp [honStepP]
  · simp only [honStepP, honCoreP]
    split_ifs <;> simp

omit [Fintype S] [DecidableEq S] [Fintype Pw] in
/-- `advCoreP` keeps the table of `H1`. -/
theorem advCoreP_td (td : Pw → Sˣ) (c : SimCore S W Pw K) (a : RAEv Pw W) :
    ∀ y ∈ (advCoreP G td c a).support, y.1.td = c.td := by
  cases a with
  | h2 x =>
    cases hl : c.h2.lookup x with
    | some k => simp [advCoreP, hl]
    | none =>
      rcases ht : lateTarget G td c x with _ | ⟨pid, pw⟩ <;> simp [advCoreP, hl, h2CoreP, ht]
  | send pid m => simp [advCoreP, sendCore_td]
  | _ => simp [advCoreP]

/-- From a state with the table `td` in place, `simCoreP` keeps it. -/
theorem simCoreP_td {td : Pw → Sˣ} (c : SimCore S W Pw K) (hc : c.td = some td) (e : OEv Pw W) :
    ∀ y ∈ (simCoreP G c e).support, y.1.td = some td := by
  rcases e with h | a <;>
    simp only [simCoreP, tdStepP, hc, PMF.pure_bind, PMF.support_map, Set.mem_image]
  · rintro _ ⟨c', hc', rfl⟩
    rw [honStepP_td c _ c' hc', hc]
  · intro y hy
    rw [advCoreP_td G _ c a y hy, hc]

/-- From a state with the table `td` in place, `simStartP` keeps it. -/
theorem simStartP_td {td : Pw → Sˣ} (s : SimSt S W Pw K) (hs : s.1.td = some td)
    (e : OEv Pw W) : ∀ y ∈ (simStartP G s e).support, y.1.1.td = some td := by
  rcases e with h | (_ | _ | _ | _ | x | _)
  case inr.h2 =>
    cases hl : s.2.lookup x with
    | some k => simp [simStartP, hl, hs]
    | none =>
      simp only [simStartP, hl, PMF.support_map, Set.mem_image]
      rintro _ ⟨r, hr, rfl⟩
      exact simCoreP_td G _ hs _ r hr
  all_goals
    simp only [simStartP, PMF.support_map, Set.mem_image]
    rintro _ ⟨r, hr, rfl⟩
    exact simCoreP_td G _ hs _ r hr

omit [Fintype S] [DecidableEq S] [DecidableEq W] [Fintype Pw] [DecidableEq Pw] [Fintype K]
  [Nonempty K] in
/-- `simAnswer` keeps the table of `H1`. -/
theorem simAnswer_td (s : SimSt S W Pw K) (o : FOut K) : (simAnswer s o).1.1.td = s.1.td := by
  unfold simAnswer
  split <;> rfl

omit [Fintype S] [DecidableEq S] [DecidableEq W] [Fintype Pw] [DecidableEq Pw] [Fintype K]
  [Nonempty K] in
/-- `simResumeP` keeps the table of `H1`. -/
theorem simResumeP_td (s : SimSt S W Pw K) (o : FOut K) :
    ∀ y ∈ (simResumeP s o).support, y.1.1.td = s.1.td := by
  unfold simResumeP
  split <;> simp [simAnswer_td]

/-- From a state with the table `td` in place, a step of the simulated world keeps it. -/
theorem simWorldP_td {td : Pw → Sˣ} (t : SimSt S W Pw K × St Pw K) (ht : t.1.1.td = some td)
    (e : OEv Pw W) : ∀ y ∈ (simWorldP G t e).support, y.1.1.1.td = some td := by
  simp only [simWorldP, withSubP, PMF.support_bind, PMF.support_map, Set.mem_iUnion,
    Set.mem_image]
  rintro _ ⟨r, hr, p, hp, rfl⟩
  exact driveP_support fStepP simResumeP (fun s o => PMF.pure (simAnswer s o))
    (fun s => s.1.td = some td)
    (fun s o hs y hy => (simResumeP_td s o y hy).trans hs)
    (fun s o hs y hy => by simp only [PMF.support_pure, Set.mem_singleton_iff] at hy; subst hy
                           exact (simAnswer_td s o).trans hs)
    1 r.1 r.2 t.2 (simStartP_td G t.1 ht e r hr) p hp

/-- **The simulated game is the simulated world with the table of `H1` as the key**: for every
oracle adversary `B`, `simGame G` and `idealGame G` accept with the same probability. -/
theorem simGame_accept_eq (B : OracleAdv (OEv Pw W) (OOut W K) Bool) :
    (simGame G).accept B = (idealGame G).accept B := by
  have h0 : ∀ e : OEv Pw W, (simWorldP (K := K) G ((simProt G).init, initSt) e).map Prod.swap =
      (PMF.uniformFintype (Pw → Sˣ)).bind fun td =>
        (simWorldP G (setTd td ((simProt G).init, initSt)) e).map Prod.swap := fun e => by
    rw [simWorldP_of_td_none G ((simProt G).init, initSt) rfl rfl e, PMF.map_bind]
  have hpres : ∀ (td : Pw → Sˣ) (t : SimSt S W Pw K × St Pw K) e,
      ∀ x ∈ ((simWorldP G (setTd td t) e).map Prod.swap).support, setTd td x.2 = x.2 := by
    intro td t e x hx
    simp only [PMF.support_map, Set.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h := simWorldP_td G (setTd td t) rfl e y hy
    obtain ⟨⟨⟨c, p⟩, st⟩, o⟩ := y
    cases c
    simp_all [setTd]
  have h := run_map_fst_lazyKey (PMF.uniformFintype (Pw → Sˣ))
    (fun t e => (simWorldP G t e).map Prod.swap) setTd ((simProt G).init, initSt) h0 hpres B
  have hO : (simGame (Pw := Pw) (K := K) G).oracle () =
      fun t e => (simWorldP G t e).map Prod.swap :=
    funext₂ (simGame_oracle_eq G)
  unfold KeyedGame.accept
  erw [PMF.pure_bind]
  rw [hO]
  exact congrArg (fun q : PMF Bool => q true) h

end SimWorld

/-! ## Oracles as functions of one uniform draw

Every step of the real and of the simulated world draws at most one scalar and at most one value
of `H2`. Each step is the image of one uniform draw `(z, k) ∈ S × K` under a deterministic
function. -/

section Draw

variable {A B γ : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]

/-- A point mass is the image of a uniform pair under a constant map. -/
theorem pure_eq_map_uniform_prod (b : γ) :
    PMF.pure b = (PMF.uniformFintype (A × B)).map fun _ => b :=
  (PMF.map_const _ _).symm

/-- The image of a uniform value is the image of a uniform pair under the first component. -/
theorem map_uniform_eq_map_prod_fst (f : A → γ) :
    (PMF.uniformFintype A).map f = (PMF.uniformFintype (A × B)).map fun r => f r.1 := by
  rw [← PMF.map_uniform_fst (B := B), PMF.map_comp]
  rfl

/-- The image of a uniform value is the image of a uniform pair under the second component. -/
theorem map_uniform_eq_map_prod_snd (f : B → γ) :
    (PMF.uniformFintype B).map f = (PMF.uniformFintype (A × B)).map fun r => f r.2 := by
  rw [PMF.uniform_prod_eq_bind, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def, PMF.bind_const]

end Draw

/-- The answer of a random function with the table `tb` at `x` when the fresh value is `k`. -/
def roDet {D K : Type} [DecidableEq D] (tb : List (D × K)) (x : D) (k : K) : K × List (D × K) :=
  match tb.lookup x with
  | some v => (v, tb)
  | none => (k, (x, k) :: tb)

/-- The lazily sampled random function is the image of a uniform value under `roDet`. -/
theorem roAt_eq_map {D K : Type} [DecidableEq D] [Fintype K] [Nonempty K] (tb : List (D × K))
    (x : D) : roAt tb x = (PMF.uniformFintype K).map (roDet tb x) := by
  cases h : tb.lookup x with
  | some v =>
    have hf : roDet tb x = fun _ => (v, tb) := funext fun _ => by simp only [roDet, h]
    rw [hf]
    simp only [roAt, h]
    exact (PMF.map_const _ _).symm
  | none =>
    simp only [roAt, h]
    congr 1
    funext v
    simp only [roDet, h]

section RealDraw

variable {S W Pw K : Type} [Field S] [Fintype S] [DecidableEq S] [DecidableEq W]
  [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K] (G : DHGroup S W)

/-- **A step of the real protocol** with the table `td` of `H1` and the draw `r`: a new protocol
party takes the secret `r.1`, and a fresh value of `H2` is `r.2`. -/
def realDet (td : Pw → Sˣ) (s : RSt S W Pw K) (e : OEv Pw W) (r : S × K) :
    OOut W K × RSt S W Pw K :=
  match e with
  | .inl (.newSession sid pid peer role pw) =>
    if (s.st.recs (sid, pid)).isNone ∧ Active sid pid peer = true then
      (.inl .ok, { s with st := addSession s.st (sid, pid) peer role pw,
                          ys := Function.update s.ys pid (some r.1) })
    else (.inl .ok, { s with st := addSession s.st (sid, pid) peer role pw })
  | .inl (.getKey sid pid) => (.inl (.key (keyOf s.st (sid, pid))), s)
  | .inr .idle => (.inr .ack, s)
  | .inr .poll => (.inr (.notice (pollStep s.st).2), { s with st := (pollStep s.st).1 })
  | .inr (.msg pid) => (.inr (.msg (realMsg G td s pid)), s)
  | .inr (.h1 pw) => (.inr (.gen (G.pub (td pw))), s)
  | .inr (.h2 x) => (.inr (.hash (roDet s.h2 x r.2).1), { s with h2 := (roDet s.h2 x r.2).2 })
  | .inr (.send pid m) =>
    match s.ys pid, s.st.recs (0, pid) with
    | some y, some rc =>
      if rc.key = none ∧ m ≠ G.pub 0 then
        (.inr .ack,
          { s with st := setRec s.st (0, pid) { rc with key := some (roDet s.h2
                (h2Inp pid rc.role (G.exp (G.pub (td rc.pw)) y) m (G.exp m y)) r.2).1 },
                   h2 := (roDet s.h2
                (h2Inp pid rc.role (G.exp (G.pub (td rc.pw)) y) m (G.exp m y)) r.2).2 })
      else (.inr .ack, s)
    | _, _ => (.inr .ack, s)

/-- **The oracle of the real game** is the image of a uniform draw under `realDet`. -/
theorem realGame_oracle_eq (td : Pw → Sˣ) (s : RSt S W Pw K) (e : OEv Pw W) :
    (realGame G).oracle td s e = (PMF.uniformFintype (S × K)).map (realDet G td s e) := by
  have hP : ∀ {γ : Type} (b : γ), PMF.pure b = (PMF.uniformFintype (S × K)).map fun _ => b :=
    fun b => pure_eq_map_uniform_prod b
  change _ = (PMF.uniformFintype (S × K)).map fun r => realDet G td s e r
  rcases e with (⟨sid, pid, peer, role, pw⟩ | ⟨sid, pid⟩) | (_ | _ | pid | pw | x | ⟨pid, m⟩)
  · simp only [realGame, realHon]
    split_ifs with h
    · rw [PMF.map_comp, map_uniform_eq_map_prod_fst (B := K)]
      congr 1
      funext r
      simp only [realDet, h, and_self, ite_true, Function.comp_apply]
    · rw [PMF.pure_map, hP]
      congr 1
      funext r
      simp only [realDet, h, ite_false]
  all_goals try
    simp only [realGame, realHon, realAdv]
    rw [PMF.pure_map, hP]
    rfl
  · simp only [realGame, realAdv, roAt_eq_map, PMF.map_comp]
    rw [map_uniform_eq_map_prod_snd (A := S)]
    congr 1
  · simp only [realGame, realAdv]
    cases hy : s.ys pid with
    | none =>
      rw [PMF.pure_map, hP]
      congr 1
      funext r
      simp only [realDet, hy]
    | some y =>
      cases hr : s.st.recs (0, pid) with
      | none =>
        rw [PMF.pure_map, hP]
        congr 1
        funext r
        simp only [realDet, hy, hr]
      | some rc =>
        dsimp only
        split_ifs with hk
        · rw [roAt_eq_map, PMF.map_comp, PMF.map_comp, map_uniform_eq_map_prod_snd (A := S)]
          congr 1
          funext r
          simp [realDet, hy, hr, hk]
        · rw [PMF.pure_map, hP]
          congr 1
          funext r
          simp only [realDet, hy, hr, hk, ite_false]

end RealDraw

/-! ### Activations with two calls as functions of draws -/

section Drive1

variable {σ τ E O EG OG Rs Rf : Type} [Fintype Rs] [Nonempty Rs] [Fintype Rf] [Nonempty Rf]

/-- An activation with at most two calls over deterministic components: the subroutine step
`stepD` reads the draw `k.1` at the first call and `k.2` at the second. -/
def drive1D (stepD : τ → EG → Rf → τ × OG) (resV : σ → OG → σ × (EG ⊕ O))
    (finV : σ → OG → σ × O) (s : σ) (d : EG ⊕ O) (t : τ) (k : Rf × Rf) : σ × τ × O :=
  match d with
  | .inr o => (s, t, o)
  | .inl g =>
    match resV s (stepD t g k.1).2 with
    | (s', .inr o) => (s', (stepD t g k.1).1, o)
    | (s', .inl g') =>
      ((finV s' (stepD (stepD t g k.1).1 g' k.2).2).1, (stepD (stepD t g k.1).1 g' k.2).1,
        (finV s' (stepD (stepD t g k.1).1 g' k.2).2).2)

/-- `driveP` with one resumption, over a subroutine step that is the image of a uniform draw and
a deterministic resumption and finish, is the image of two independent draws under `drive1D`. -/
theorem driveP_one_eq (step : τ → EG → PMF (τ × OG)) (res : σ → OG → PMF (σ × (EG ⊕ O)))
    (fin : σ → OG → PMF (σ × O)) (stepD : τ → EG → Rf → τ × OG)
    (resV : σ → OG → σ × (EG ⊕ O)) (finV : σ → OG → σ × O)
    (hstep : ∀ t g, step t g = (PMF.uniformFintype Rf).map (stepD t g))
    (hres : ∀ s o, res s o = PMF.pure (resV s o)) (hfin : ∀ s o, fin s o = PMF.pure (finV s o))
    (s : σ) (d : EG ⊕ O) (t : τ) :
    driveP step res fin 1 s d t =
      (PMF.uniformFintype (Rf × Rf)).map (drive1D stepD resV finV s d t) := by
  rcases d with g | o
  · simp only [driveP, hstep, hres, PMF.bind_map, PMF.pure_bind, Function.comp_def]
    rw [PMF.uniform_prod_eq_bind, PMF.map_bind]
    refine congrArg _ (funext fun k₁ => ?_)
    rw [PMF.map_comp]
    rcases h : resV s (stepD t g k₁).2 with ⟨s', g' | o⟩
    · simp only [driveP, hstep, hfin, PMF.bind_map, Function.comp_def]
      congr 1
      funext k₂
      simp only [PMF.pure_map, Function.comp_apply, drive1D, h]
    · simp only [driveP]
      rw [← PMF.map_const (PMF.uniformFintype Rf)]
      congr 1
      funext k₂
      simp only [drive1D, h, Function.const_apply, Function.comp_apply]
  · simp only [driveP]
    rw [← PMF.map_const (PMF.uniformFintype (Rf × Rf))]
    rfl

/-- `withSubP` with one resumption, over components that are images of uniform draws, is the
image of independent draws for the start and the two calls. -/
theorem withSubP_one_eq (start : σ → E → PMF (σ × (EG ⊕ O))) (step : τ → EG → PMF (τ × OG))
    (res : σ → OG → PMF (σ × (EG ⊕ O))) (fin : σ → OG → PMF (σ × O))
    (startD : σ → E → Rs → σ × (EG ⊕ O)) (stepD : τ → EG → Rf → τ × OG)
    (resV : σ → OG → σ × (EG ⊕ O)) (finV : σ → OG → σ × O) (t : σ × τ) (e : E)
    (hstart : start t.1 e = (PMF.uniformFintype Rs).map (startD t.1 e))
    (hstep : ∀ t g, step t g = (PMF.uniformFintype Rf).map (stepD t g))
    (hres : ∀ s o, res s o = PMF.pure (resV s o)) (hfin : ∀ s o, fin s o = PMF.pure (finV s o)) :
    withSubP start step res fin 1 t e =
      (PMF.uniformFintype (Rs × (Rf × Rf))).map fun r =>
        (((drive1D stepD resV finV (startD t.1 e r.1).1 (startD t.1 e r.1).2 t.2 r.2).1,
          (drive1D stepD resV finV (startD t.1 e r.1).1 (startD t.1 e r.1).2 t.2 r.2).2.1),
        (drive1D stepD resV finV (startD t.1 e r.1).1 (startD t.1 e r.1).2 t.2 r.2).2.2) := by
  simp only [withSubP, hstart, PMF.bind_map, Function.comp_def,
    driveP_one_eq step res fin stepD resV finV hstep hres hfin, PMF.map_comp]
  rw [PMF.uniform_prod_eq_bind (A := Rs) (B := Rf × Rf), PMF.map_bind]
  refine congrArg _ (funext fun a => ?_)
  rw [PMF.map_comp]
  rfl

end Drive1

/-! ### The simulated world as a function of draws -/

section SimDraw

variable {S W Pw K : Type} [Field S] [Fintype S] [DecidableEq S] [DecidableEq W]
  [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K] [Inhabited K] (G : DHGroup S W)

/-- `honCore` with the secret `z` of a new protocol party. -/
def honCoreD (c : SimCore S W Pw K) (sid pid peer : PartyId) (role : Role) (z : S) :
    SimCore S W Pw K :=
  if sid = 0 ∧ pid ≤ 1 ∧ c.info pid = none then
    if Active sid pid peer = true then
      { c with info := Function.update c.info pid (some (peer, role)),
               zs := Function.update c.zs pid (some z) }
    else { c with info := Function.update c.info pid (some (peer, role)) }
  else c

/-- `honStep` with the secret `z` of a new protocol party. -/
def honStepD (c : SimCore S W Pw K) :
    Option (PartyId × PartyId × PartyId × Role) → S → SimCore S W Pw K
  | some (sid, pid, peer, role), z => { honCoreD c sid pid peer role z with phase := .fwd }
  | none, _ => { c with phase := .fwd }

/-- `h2Core` with the fresh value `k`. -/
def h2CoreD (td : Pw → Sˣ) (c : SimCore S W Pw K) (x : Inp W) (k : K) :
    SimCore S W Pw K × Dec Pw W K :=
  match lateTarget G td c x with
  | some (pid, pw) =>
    ({ c with pend := Function.update c.pend pid none, phase := .late x },
      sCall (.lateTestPwd 0 pid pw))
  | none => ({ c with h2 := (x, k) :: c.h2, phase := .rest }, sOut (.hash k))

/-- `advCore` with the fresh value `k`. -/
def advCoreD (td : Pw → Sˣ) (c : SimCore S W Pw K) (a : RAEv Pw W) (k : K) :
    SimCore S W Pw K × Dec Pw W K :=
  match a with
  | .idle => ({ c with phase := .rest }, sOut .ack)
  | .poll => ({ c with phase := .fwd }, sCall .poll)
  | .msg pid => ({ c with phase := .rest }, sOut (.msg ((c.zs pid).map G.pub)))
  | .h1 pw => ({ c with cands := if pw ∈ c.cands then c.cands else c.cands ++ [pw],
                        phase := .rest }, sOut (.gen (G.pub (td pw))))
  | .h2 x =>
    match c.h2.lookup x with
    | some k' => ({ c with phase := .rest }, sOut (.hash k'))
    | none => h2CoreD G td c x k
  | .send pid m => sendCore G td c pid m

/-- `simCore` with the table `td` of `H1` in place and the draw `r`. -/
def simCoreD (td : Pw → Sˣ) (c : SimCore S W Pw K) (e : OEv Pw W) (r : S × K) :
    SimCore S W Pw K × Dec Pw W K :=
  match e with
  | .inl h => (honStepD c (honPub h) r.1, .inl (.inl h))
  | .inr a => advCoreD G td c a r.2

/-- `simStart` with the table `td` of `H1` in place and the draw `r`. -/
def simStartD (td : Pw → Sˣ) (s : SimSt S W Pw K) (e : OEv Pw W) (r : S × K) :
    SimSt S W Pw K × Dec Pw W K :=
  match e with
  | .inr (.h2 x) =>
    match s.2.lookup x with
    | some k => (({ s.1 with phase := .rest }, s.2), sOut (.hash k))
    | none => (((simCoreD G td s.1 e r).1, s.2), (simCoreD G td s.1 e r).2)
  | _ => (((simCoreD G td s.1 e r).1, s.2), (simCoreD G td s.1 e r).2)

/-- A step of the adversary port of `F_lePAKE` with the fresh key `kf`. -/
def leAdvD (t : St Pw K) (a : LeAEv Pw K) (kf : K) : St Pw K × AOut K :=
  match a with
  | .idle => (t, .ack)
  | .poll => ((pollStep t).1, .notice (pollStep t).2)
  | .testPwd sid pid g => (testStep t (sid, pid) g, .answer (testAns t (sid, pid) g))
  | .registerTest sid pid => (registerStep t (sid, pid), .ack)
  | .newKey sid pid k => (newKeyStep t (sid, pid) k kf, .ack)
  | .lateTestPwd sid pid g => (lateStep t (sid, pid), .reveal (lateReveal t (sid, pid) g kf))

/-- A step of `F_lePAKE` with the fresh key `kf`. -/
def fStepD (t : St Pw K) (e : FEv Pw K) (kf : K) : St Pw K × FOut K :=
  match e with
  | .inl h => ((leHonStep t h).1, .inl (leHonStep t h).2)
  | .inr a => ((leAdvD t a kf).1, .inr (leAdvD t a kf).2)

/-- The value of `simResume`. -/
def simResumeV (s : SimSt S W Pw K) (o : FOut K) : SimSt S W Pw K × Dec Pw W K :=
  match s.1.phase with
  | .key pid k => (({ s.1 with phase := .done }, s.2), sCall (.newKey 0 pid k))
  | _ => ((simAnswer s o).1, .inr (simAnswer s o).2)

/-- **A step of the simulated world** with the table `td` of `H1` in place and the draw
`r = (r₀, k₁, k₂)`: the start reads `r₀`, and the calls to `F_lePAKE` read `k₁` and `k₂`. -/
def simWorldD (td : Pw → Sˣ) (t : SimSt S W Pw K × St Pw K) (e : OEv Pw W)
    (r : (S × K) × K × K) : (SimSt S W Pw K × St Pw K) × OOut W K :=
  (((drive1D fStepD simResumeV simAnswer (simStartD G td t.1 e r.1).1
      (simStartD G td t.1 e r.1).2 t.2 r.2).1,
    (drive1D fStepD simResumeV simAnswer (simStartD G td t.1 e r.1).1
      (simStartD G td t.1 e r.1).2 t.2 r.2).2.1),
    (drive1D fStepD simResumeV simAnswer (simStartD G td t.1 e r.1).1
      (simStartD G td t.1 e r.1).2 t.2 r.2).2.2)

omit [DecidableEq S] [DecidableEq W] [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K]
  [Inhabited K] in
/-- `honStepP` is the image of a uniform secret under `honStepD`. -/
theorem honStepP_eq_map (c : SimCore S W Pw K) (o : Option (PartyId × PartyId × PartyId × Role)) :
    honStepP c o = (PMF.uniformFintype S).map (honStepD c o) := by
  rcases o with _ | ⟨sid, pid, peer, role⟩
  · exact (PMF.map_const _ _).symm
  · simp only [honStepP, honCoreP]
    split_ifs with h₁ h₂
    · rw [PMF.map_comp]
      congr 1
      funext z
      rw [Function.comp_apply, honStepD, honCoreD, ite_eq_left h₁, ite_eq_left h₂]
    · rw [PMF.pure_map, ← PMF.map_const (PMF.uniformFintype S)]
      congr 1
      funext z
      rw [Function.const_apply, honStepD, honCoreD, ite_eq_left h₁, ite_eq_right h₂]
    · rw [PMF.pure_map, ← PMF.map_const (PMF.uniformFintype S)]
      congr 1
      funext z
      simp only [honStepD, honCoreD, h₁, ite_false, Function.const_apply]

omit [Fintype S] [DecidableEq S] [Fintype Pw] in
/-- `advCoreP` is the image of a uniform value under `advCoreD`. -/
theorem advCoreP_eq_map (td : Pw → Sˣ) (c : SimCore S W Pw K) (a : RAEv Pw W) :
    advCoreP G td c a = (PMF.uniformFintype K).map (advCoreD G td c a) := by
  cases a with
  | h2 x =>
    cases hl : c.h2.lookup x with
    | some k =>
      simp only [advCoreP, hl]
      rw [← PMF.map_const (PMF.uniformFintype K)]
      congr 1
      funext k'
      simp only [advCoreD, hl, Function.const_apply]
    | none =>
      rcases ht : lateTarget G td c x with _ | ⟨pid, pw⟩
      · simp only [advCoreP, hl, h2CoreP, ht]
        congr 1
        funext k'
        simp only [advCoreD, hl, h2CoreD, ht]
      · simp only [advCoreP, hl, h2CoreP, ht]
        rw [← PMF.map_const (PMF.uniformFintype K)]
        congr 1
        funext k'
        simp only [advCoreD, hl, h2CoreD, ht, Function.const_apply]
  | _ => exact (PMF.map_const _ _).symm

/-- With the table `td` of `H1` in place, `simCoreP` is the image of a uniform draw under
`simCoreD`. -/
theorem simCoreP_eq_map {td : Pw → Sˣ} (c : SimCore S W Pw K) (hc : c.td = some td)
    (e : OEv Pw W) : simCoreP G c e = (PMF.uniformFintype (S × K)).map (simCoreD G td c e) := by
  change _ = (PMF.uniformFintype (S × K)).map fun r => simCoreD G td c e r
  rcases e with h | a
  · simp only [simCoreP, tdStepP, hc, PMF.pure_bind, honStepP_eq_map, PMF.map_comp]
    rw [map_uniform_eq_map_prod_fst (B := K)]
    rfl
  · simp only [simCoreP, tdStepP, hc, PMF.pure_bind, advCoreP_eq_map]
    rw [map_uniform_eq_map_prod_snd (A := S)]
    rfl

/-- With the table `td` of `H1` in place, `simStartP` is the image of a uniform draw under
`simStartD`. -/
theorem simStartP_eq_map {td : Pw → Sˣ} (s : SimSt S W Pw K) (hs : s.1.td = some td)
    (e : OEv Pw W) :
    simStartP G s e = (PMF.uniformFintype (S × K)).map (simStartD G td s e) := by
  change _ = (PMF.uniformFintype (S × K)).map fun r => simStartD G td s e r
  rcases e with h | (_ | _ | _ | _ | x | _)
  case inr.h2 =>
    cases hl : s.2.lookup x with
    | some k =>
      simp only [simStartP, hl]
      rw [← PMF.map_const (PMF.uniformFintype (S × K))]
      congr 1
      funext r
      simp only [simStartD, hl, Function.const_apply]
    | none =>
      simp only [simStartP, hl, simCoreP_eq_map G s.1 hs, PMF.map_comp]
      congr 1
      funext r
      simp only [simStartD, hl, Function.comp_apply]
  all_goals
    simp only [simStartP, simCoreP_eq_map G s.1 hs, PMF.map_comp]
    rfl

omit [Fintype Pw] [Inhabited K] in
/-- A step of `F_lePAKE` is the image of a uniform key under `fStepD`. -/
theorem fStepP_eq_map (t : St Pw K) (g : FEv Pw K) :
    fStepP t g = (PMF.uniformFintype K).map (fStepD t g) := by
  change _ = (PMF.uniformFintype K).map fun kf => fStepD t g kf
  rcases g with h | a
  · exact (PMF.map_const _ _).symm
  · cases a <;> simp only [fStepP, leAdvP, PMF.pure_map, PMF.map_comp] <;>
      first
      | exact (PMF.map_const _ _).symm
      | rfl

omit [Fintype S] [DecidableEq S] [DecidableEq W] [Fintype Pw] [DecidableEq Pw] [Fintype K]
  [Nonempty K] in
/-- `simResumeP` is the point mass at `simResumeV`. -/
theorem simResumeP_eq_pure (s : SimSt S W Pw K) (o : FOut K) :
    simResumeP s o = PMF.pure (simResumeV s o) := by
  unfold simResumeP simResumeV
  split <;> rfl

/-- **The step of the simulated world as a function of draws**: with the table `td` of `H1` in
place, `simWorldP` is the image of a uniform draw under `simWorldD`. -/
theorem simWorldP_eq_map {td : Pw → Sˣ} (t : SimSt S W Pw K × St Pw K) (ht : t.1.1.td = some td)
    (e : OEv Pw W) :
    simWorldP G t e = (PMF.uniformFintype ((S × K) × K × K)).map (simWorldD G td t e) :=
  withSubP_one_eq _ _ _ _ (simStartD G td) fStepD simResumeV simAnswer t e
    (simStartP_eq_map G t.1 ht e) fStepP_eq_map simResumeP_eq_pure (fun _ _ => rfl)

/-- **The oracle of the simulated world with the table of `H1` as the key** is the image of a
uniform draw under `simWorldD`. -/
theorem idealGame_oracle_eq (td : Pw → Sˣ) (t : SimSt S W Pw K × St Pw K) (e : OEv Pw W) :
    (idealGame G).oracle td t e =
      (PMF.uniformFintype ((S × K) × K × K)).map fun r =>
        (simWorldD G td (setTd td t) e r).swap := by
  change (simWorldP G (setTd td t) e).map Prod.swap = _
  rw [simWorldP_eq_map G (setTd td t) rfl e, PMF.map_comp]
  rfl

end SimDraw

/-! ## The joint world

The joint world runs the simulated world and the real world on one draw per step. A new protocol
party with password `pw` takes the secret `z` in the simulated world and `z / td pw` in the real
world, so that both send `g^z`. A fresh value of `H2` in the real world is the value of the
slot of the draw that the simulated world reads at the same place: the start for a fresh `H2`
query, the first call for a late test or a key without a test, the second call for a key after a
test. The state records whether the outputs of the two worlds differed at the last step. -/

/-- A slot of the draw `((z, k₀), k₁, k₂)` that holds a value of `H2`. -/
inductive Slot where
  /-- The value `k₀` read by the start of the simulator. -/
  | start
  /-- The value `k₁` read by the first call to `F_lePAKE`. -/
  | call₁
  /-- The value `k₂` read by the second call to `F_lePAKE`. -/
  | call₂

/-- The value at a slot of a draw. -/
def Slot.get {S K : Type} : Slot → (S × K) × K × K → K
  | .start, r => r.1.2
  | .call₁, r => r.2.1
  | .call₂, r => r.2.2

/-- A rearrangement of a draw that puts the scalar and the value at the slot `j` first. -/
def Slot.equiv (S K : Type) : Slot → ((S × K) × K × K) ≃ ((S × K) × K × K)
  | .start => Equiv.refl _
  | .call₁ =>
    { toFun := fun r => ((r.1.1, r.2.1), r.1.2, r.2.2)
      invFun := fun r => ((r.1.1, r.2.1), r.1.2, r.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  | .call₂ =>
    { toFun := fun r => ((r.1.1, r.2.2), r.2.1, r.1.2)
      invFun := fun r => ((r.1.1, r.2.2), r.2.1, r.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The scalar of a uniform draw scaled by a unit, with the value at any slot, is a uniform
pair. -/
theorem map_uniform_slot {S K : Type} [Field S] [Fintype S] [Fintype K]
    [Nonempty K] (a : Sˣ) (j : Slot) :
    (PMF.uniformFintype ((S × K) × K × K)).map (fun r => ((a : S) * r.1.1, j.get r)) =
      PMF.uniformFintype (S × K) := by
  have hj : (fun r : (S × K) × K × K => ((a : S) * r.1.1, j.get r)) =
      Prod.map (Units.mulLeft a) id ∘ Prod.fst ∘ Slot.equiv S K j := by
    funext r
    cases j <;> rfl
  rw [hj, ← PMF.map_comp, ← PMF.map_comp, PMF.uniformFintype_map_equiv, PMF.map_uniform_fst]
  exact PMF.uniformFintype_map_equiv ((Units.mulLeft a).prodCongr (Equiv.refl K))

section Joint

variable {S W Pw K : Type} [Field S] [Fintype S] [DecidableEq S] [DecidableEq W]
  [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K] [Inhabited K] (G : DHGroup S W)

/-- The factor from the secret of the simulated world to the secret of the real world. -/
def cplScale (td : Pw → Sˣ) : OEv Pw W → Sˣ
  | .inl (.newSession _ _ _ _ pw) => (td pw)⁻¹
  | _ => 1

/-- The slot of the draw that the real world reads for a fresh value of `H2`. -/
def cplSlot (td : Pw → Sˣ) (t : SimSt S W Pw K × St Pw K) : OEv Pw W → Slot
  | .inr (.h2 x) =>
    if t.1.2.lookup x = none ∧ t.1.1.h2.lookup x = none ∧
        (lateTarget G td t.1.1 x).isSome = true then .call₁ else .start
  | .inr (.send pid m) =>
    match (sendCore G td t.1.1 pid m).2 with
    | .inl (.inr (.newKey _ _ _)) => .call₁
    | _ => .call₂
  | _ => .start

/-- The draw of the real world from the draw of the simulated world. -/
def cpl (td : Pw → Sˣ) (t : SimSt S W Pw K × St Pw K) (e : OEv Pw W) (r : (S × K) × K × K) :
    S × K :=
  ((cplScale td e : S) * r.1.1, (cplSlot G td t e).get r)

/-- The state of the joint world: the simulated world, the real world, and whether the outputs
differed at the last step. -/
abbrev JSt (S W Pw K : Type) [Field S] :=
  ((SimSt S W Pw K × St Pw K) × RSt S W Pw K) × Bool

/-- **A step of the joint world** with the draw `r`: the outputs of the real and of the
simulated world, and the next states. -/
def jointD (td : Pw → Sˣ) (s : (SimSt S W Pw K × St Pw K) × RSt S W Pw K) (e : OEv Pw W)
    (r : (S × K) × K × K) :
    (OOut W K × OOut W K) × ((SimSt S W Pw K × St Pw K) × RSt S W Pw K) :=
  (((realDet G td s.2 e (cpl G td s.1 e r)).1, (simWorldD G td (setTd td s.1) e r).2),
    ((simWorldD G td (setTd td s.1) e r).1, (realDet G td s.2 e (cpl G td s.1 e r)).2))

open Classical in
/-- The joint world answering with the output of the real world. -/
noncomputable def jointReal (td : Pw → Sˣ) (s : JSt S W Pw K) (e : OEv Pw W) :
    PMF (OOut W K × JSt S W Pw K) :=
  (PMF.uniformFintype ((S × K) × K × K)).map fun r =>
    ((jointD G td s.1 e r).1.1,
      ((jointD G td s.1 e r).2, decide ((jointD G td s.1 e r).1.1 ≠ (jointD G td s.1 e r).1.2)))

open Classical in
/-- The joint world answering with the output of the simulated world. -/
noncomputable def jointSim (td : Pw → Sˣ) (s : JSt S W Pw K) (e : OEv Pw W) :
    PMF (OOut W K × JSt S W Pw K) :=
  (PMF.uniformFintype ((S × K) × K × K)).map fun r =>
    ((jointD G td s.1 e r).1.2,
      ((jointD G td s.1 e r).2, decide ((jointD G td s.1 e r).1.1 ≠ (jointD G td s.1 e r).1.2)))

omit [DecidableEq S] [Fintype Pw] in
/-- The two answers of the joint world agree on every outcome whose outputs did not differ. -/
theorem jointReal_apply_eq (td : Pw → Sˣ) (s : JSt S W Pw K) (e : OEv Pw W)
    (x : OOut W K × JSt S W Pw K) (hx : x.2.2 = false) :
    jointReal G td s e x = jointSim G td s e x := by
  simp only [jointReal, jointSim, PMF.map_apply]
  refine tsum_congr fun r => ?_
  by_cases h : (jointD G td s.1 e r).1.1 = (jointD G td s.1 e r).1.2
  · rw [h]
  · have h₁ : x ≠ ((jointD G td s.1 e r).1.1, ((jointD G td s.1 e r).2, true)) :=
      fun hc => by simp [hc] at hx
    have h₂ : x ≠ ((jointD G td s.1 e r).1.2, ((jointD G td s.1 e r).2, true)) :=
      fun hc => by simp [hc] at hx
    simp only [h, ne_eq, not_false_eq_true, decide_true, h₁, h₂, ite_false]

/-- The real part of `jointReal` is the real game. -/
theorem jointReal_map (td : Pw → Sˣ) (s : JSt S W Pw K) (e : OEv Pw W) :
    (jointReal G td s e).map (Prod.map id fun s' => s'.1.2) = (realGame G).oracle td s.1.2 e := by
  rw [realGame_oracle_eq, jointReal, PMF.map_comp, ← map_uniform_slot (cplScale td e)
    (cplSlot G td s.1.1 e), PMF.map_comp]
  rfl

/-- The simulated part of `jointSim` is the simulated world with the table of `H1` as the
key. -/
theorem jointSim_map (td : Pw → Sˣ) (s : JSt S W Pw K) (e : OEv Pw W) :
    (jointSim G td s e).map (Prod.map id fun s' => s'.1.1) = (idealGame G).oracle td s.1.1 e := by
  rw [idealGame_oracle_eq, jointSim, PMF.map_comp]
  rfl

/-- The bad transitions of the joint world: the outputs of the two worlds differed. -/
def JointBad (_ : JSt S W Pw K) (_ : OEv Pw W) (x : OOut W K × JSt S W Pw K) : Prop :=
  x.2.2 = true

instance (s : JSt S W Pw K) (e : OEv Pw W) (x : OOut W K × JSt S W Pw K) :
    Decidable (JointBad s e x) :=
  inferInstanceAs (Decidable (x.2.2 = true))

/-- The initial state of the joint world. -/
noncomputable def jointInit : JSt S W Pw K :=
  ((((simProt G).init, initSt), ⟨initSt, fun _ => none, []⟩), false)

/-- **The bad-event experiment**: the table of `H1` is sampled, the adversary runs against the
joint world answering with the outputs of the simulated world, and the experiment outputs whether
the outputs of the real and of the simulated world differed at some step. -/
noncomputable def badGame (B : OracleAdv (OEv Pw W) (OOut W K) Bool) : PMF Bool :=
  (PMF.uniformFintype (Pw → Sˣ)).bind fun td =>
    (OracleAdv.run (OracleAdv.flagWhen JointBad (jointSim G td)) B (jointInit G, false)).map
      fun y => y.2.2

/-- The output distribution of a run, at `true`, as an outer measure. -/
theorem map_fst_apply_true {σ : Type} (p : PMF (Bool × σ)) :
    (p.map Prod.fst) true = p.toOuterMeasure {x | x.1 ∈ ({true} : Set Bool)} := by
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  rfl

/-- **Real versus simulated, up to the bad event.** For every oracle adversary `B`, the advantage
of `B` between the real game and the simulated game is at most the probability of the bad event
of the joint world. -/
theorem advantage_le_badGame (B : OracleAdv (OEv Pw W) (OOut W K) Bool) :
    KeyedGame.advantage (realGame G) (simGame G) B ≤ badGame G B true := by
  have hagree : ∀ (td : Pw → Sˣ) (s : JSt S W Pw K) (e : OEv Pw W)
      (x : OOut W K × JSt S W Pw K), ¬ JointBad s e x →
        jointReal G td s e x = jointSim G td s e x :=
    fun td s e x hx => jointReal_apply_eq G td s e x (by simpa [JointBad] using hx)
  have hR : ∀ td : Pw → Sˣ,
      (OracleAdv.run ((realGame G).oracle td) B (realGame G).init).map Prod.fst =
        (OracleAdv.run (jointReal G td) B (jointInit G)).map Prod.fst := fun td => by
    have h := OracleAdv.run_map_state (jointReal G td) ((realGame G).oracle td)
      (fun s' => s'.1.2) (fun s e => jointReal_map G td s e) B (jointInit G)
    calc _ = ((OracleAdv.run (jointReal G td) B (jointInit G)).map
          (Prod.map id fun s' => s'.1.2)).map Prod.fst := (congrArg (PMF.map Prod.fst) h).symm
      _ = _ := by rw [PMF.map_comp]; rfl
  have hI : ∀ td : Pw → Sˣ,
      (OracleAdv.run ((idealGame G).oracle td) B (idealGame G).init).map Prod.fst =
        (OracleAdv.run (jointSim G td) B (jointInit G)).map Prod.fst := fun td => by
    have h := OracleAdv.run_map_state (jointSim G td) ((idealGame G).oracle td)
      (fun s' => s'.1.1) (fun s e => jointSim_map G td s e) B (jointInit G)
    calc _ = ((OracleAdv.run (jointSim G td) B (jointInit G)).map
          (Prod.map id fun s' => s'.1.1)).map Prod.fst := (congrArg (PMF.map Prod.fst) h).symm
      _ = _ := by rw [PMF.map_comp]; rfl
  have hF : ∀ td, ((OracleAdv.run (OracleAdv.flagWhen JointBad (jointSim G td)) B
      (jointInit G, false)).map fun y => y.2.2) true =
      (OracleAdv.run (OracleAdv.flagWhen JointBad (jointSim G td)) B
        (jointInit G, false)).toOuterMeasure {y | y.2.2 = true} := fun td => by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    rfl
  have h₁ : ∀ td, ((OracleAdv.run (jointReal G td) B (jointInit G)).map Prod.fst) true ≤
      ((OracleAdv.run (jointSim G td) B (jointInit G)).map Prod.fst) true +
        ((OracleAdv.run (OracleAdv.flagWhen JointBad (jointSim G td)) B
          (jointInit G, false)).map fun y => y.2.2) true := fun td => by
    rw [map_fst_apply_true, map_fst_apply_true, hF]
    exact OracleAdv.run_toOuterMeasure_le_add_flagWhen JointBad _ _ (hagree td) B _ _
  have h₂ : ∀ td, ((OracleAdv.run (jointSim G td) B (jointInit G)).map Prod.fst) true ≤
      ((OracleAdv.run (jointReal G td) B (jointInit G)).map Prod.fst) true +
        ((OracleAdv.run (OracleAdv.flagWhen JointBad (jointSim G td)) B
          (jointInit G, false)).map fun y => y.2.2) true := fun td => by
    rw [map_fst_apply_true, map_fst_apply_true, hF,
      ← OracleAdv.run_flagWhen_prob_eq JointBad _ _ (hagree td) B]
    exact OracleAdv.run_toOuterMeasure_le_add_flagWhen JointBad _ _
      (fun s e x hx => (hagree td s e x hx).symm) B _ _
  have hacc₁ : (realGame G).accept B = ∑' td : Pw → Sˣ, PMF.uniformFintype (Pw → Sˣ) td *
      ((OracleAdv.run (jointReal G td) B (jointInit G)).map Prod.fst) true := by
    unfold KeyedGame.accept
    rw [PMF.bind_apply]
    exact tsum_congr fun td => by rw [hR td]; rfl
  have hacc₂ : (idealGame G).accept B = ∑' td : Pw → Sˣ, PMF.uniformFintype (Pw → Sˣ) td *
      ((OracleAdv.run (jointSim G td) B (jointInit G)).map Prod.fst) true := by
    unfold KeyedGame.accept
    rw [PMF.bind_apply]
    exact tsum_congr fun td => by rw [hI td]; rfl
  rw [KeyedGame.advantage, simGame_accept_eq, hacc₁, hacc₂, badGame, PMF.bind_apply]
  refine max_le (tsub_le_iff_left.mpr ?_) (tsub_le_iff_left.mpr ?_)
  all_goals
    rw [← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun td => ?_
    rw [← mul_add]
    gcongr
  · exact h₁ td
  · exact h₂ td

end Joint

end CatCrypt.Crypto.PAKE.CPaceHops
