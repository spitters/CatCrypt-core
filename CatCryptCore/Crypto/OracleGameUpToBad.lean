/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.SPCompPMF
public import CatCryptCore.Crypto.UCTransparentMulti
public import CatCryptCore.Crypto.OracleLazyMulti

/-!
# Oracle games up to a bad event

Tools for bounding the advantage of an oracle adversary between a keyed game and the oracle game
of a simulator running with a functionality, by the probability of a bad event of a joint run.

## Simulators over probability mass functions

`driveP` and `withSubP` are an activation and a step of a multi-call simulator
(`UCTransparent.MultiHybrid`) over a subroutine, all of whose components are probability mass
functions. When the components of the simulator and of the subroutine are lifts of such
functions, the step of `π.withSub X` is the lift of `withSubP` (`withSub_step_eq_liftPMF`).
`drive1D` is an activation with at most two calls over deterministic components, and an activation
with one resumption over components that are images of uniform draws is the image of independent
draws under `drive1D` (`driveP_one_eq`, `withSubP_one_eq`).

## Steps as images of uniform draws

A point mass and the image of a uniform value are images of a uniform pair
(`pure_eq_map_uniform_prod`, `map_uniform_eq_map_prod_fst`, `map_uniform_eq_map_prod_snd`). A
lazily sampled random function with a table is the image of one uniform value under `roDet`
(`map_uniform_roDet`).

## Runs of oracle adversaries

* `OracleAdv.run_eq_bind_run_of_trigger`: a key drawn by the oracle at its first call satisfying
  a trigger may be drawn up front, for the full run; `OracleAdv.run_eq_run_of_inv` is the step
  after the draw, oracles agreeing on an invariant.
* `OracleAdv.run_map_fst_eq_bind_run_set_of_trigger`: the same with the key placed in the start
  state, for the output.
* `OracleAdv.run_map_fst_lazyKey`: a key sampled by the oracle at its first query may be sampled
  up front.
* `OracleAdv.run_flagWhen_le_of_inv`: a bad flag implied by another along an invariant.
* `OracleAdv.run_flagWhen_mono`, `OracleAdv.run_flagWhen_or_le`: monotonicity and the union bound
  for bad flags.

The system-level up-to-bad rule for systems lossless on an invariant is
`UCCoupling.realizes_upto_bad_rel_inv` (`CatCryptCore.Crypto.Party.Relator`); the results here
are stated for oracle adversaries and `OracleAdv.flagWhen`.

## Main definitions

* `driveP`, `withSubP`: an activation and a step of a multi-call simulator over distributions.
* `drive1D`: an activation with at most two calls as a function of two draws.
* `roDet`: a lazily sampled random function as a function of its fresh value.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto.UCTransparent
open scoped ENNReal

namespace CatCrypt.Crypto

/-! ## Computations given by probability mass functions -/

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

/-- `SPComp.map` of a lift is the lift of the image. -/
theorem map_liftPMF {α β : Type} (f : α → β) (p : PMF α) :
    SPComp.map f (liftPMF p) = liftPMF (p.map f) :=
  liftPMF_bind_pure p f

end CatCrypt.Crypto

namespace CatCrypt.Crypto.OracleGameUpToBad

/-! ## Multi-call simulators over probability mass functions -/

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

/-! ## Distributions as images of one uniform draw -/

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

/-- **A lazily sampled random function as the image of one uniform value**: the recorded value
at `x`, or a fresh uniform value that is recorded, is the image of a uniform value under
`roDet tb x`. -/
theorem map_uniform_roDet {D K : Type} [DecidableEq D] [Fintype K] [Nonempty K]
    (tb : List (D × K)) (x : D) :
    (PMF.uniformFintype K).map (roDet tb x) =
      match tb.lookup x with
      | some v => PMF.pure (v, tb)
      | none => (PMF.uniformFintype K).map fun v => (v, (x, v) :: tb) := by
  cases h : tb.lookup x with
  | some v =>
    have hf : roDet tb x = fun _ => (v, tb) := funext fun _ => by simp only [roDet, h]
    rw [hf]
    exact PMF.map_const _ _
  | none =>
    congr 1
    funext v
    simp only [roDet, h]

/-! ## Activations with two calls as functions of draws -/

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

/-! ## Output probabilities as outer measures -/

/-- The output distribution of a run, at `true`, as an outer measure. -/
theorem map_fst_apply_true {σ : Type} (p : PMF (Bool × σ)) :
    (p.map Prod.fst) true = p.toOuterMeasure {x | x.1 ∈ ({true} : Set Bool)} := by
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  rfl

/-- The output flag of a flagged run, at `true`, as an outer measure. -/
theorem map_flag_apply {σ β : Type} (p : PMF (β × (σ × Bool))) :
    (p.map fun y => y.2.2) true = p.toOuterMeasure {y | y.2.2 = true} := by
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  rfl

end CatCrypt.Crypto.OracleGameUpToBad

namespace CatCrypt.Crypto.OracleAdv

/-! ## Keys sampled at the first query -/

section LazyKey

variable {K σ D R α : Type}

/-- **Runs of oracles agreeing on an invariant.** From a state of an invariant `N` kept by every
call of `O`, a run against an oracle `O'` agreeing with `O` on `N` is the run against `O`. -/
theorem run_eq_run_of_inv (O O' : σ → D → PMF (R × σ)) (N : σ → Prop)
    (hN : ∀ s d, N s → ∀ x ∈ (O s d).support, N x.2) (hO : ∀ s d, N s → O' s d = O s d)
    (A : OracleAdv D R α) (s : σ) (hs : N s) :
    OracleAdv.run O' A s = OracleAdv.run O A s := by
  induction A generalizing s with
  | ret a => rfl
  | rand p f ih => simp only [OracleAdv.run_rand, fun b => ih b s hs]
  | query d f ih =>
    simp only [OracleAdv.run_query, hO s d hs]
    exact PMF.bind_congr_support _ _ _ fun x hx => ih x.1 x.2 (hN s d hs x hx)

/-- From a state with the key `k` in place, a run against `O` is the run against `O` with the
key `k` put in place before every call, when every call from a state with `k` in place leaves
`k` in place. -/
theorem run_eq_run_set (O : σ → D → PMF (R × σ)) (set : K → σ → σ) (k : K)
    (hpres : ∀ s d, ∀ x ∈ (O (set k s) d).support, set k x.2 = x.2) (A : OracleAdv D R α)
    (t : σ) (ht : set k t = t) :
    OracleAdv.run O A t = OracleAdv.run (fun s d => O (set k s) d) A t := by
  refine (run_eq_run_of_inv O _ (fun s => set k s = s) (fun s d hs x hx => ?_)
    (fun s d hs => by rw [hs]) A t ht).symm
  exact hpres s d x (by rwa [hs])

/-- **A key drawn at its first triggering call.** Let the oracle `O`, from the states `P` before
the draw, draw the key `k` from `μ` at the calls satisfying the trigger `c` and continue as the
oracle `Ok k`, and let `Ok k` agree with `O` on the other calls from `P`, which lead to `P` or to
states that satisfy `N k` for every key. Let a triggering call of `Ok k` lead to the states
`N k`, kept by every call of `O`, on which `Ok k` agrees with `O`. Then from a state of `P` the
run against `O` is the run against `Ok k` with `k` drawn from `μ` before the run, as a statement
about the output and the final state. -/
theorem run_eq_bind_run_of_trigger (μ : PMF K) (O : σ → D → PMF (R × σ))
    (Ok : K → σ → D → PMF (R × σ)) (P : σ → Prop) (c : σ → D → Prop) (N : K → σ → Prop)
    (hc : ∀ s d, P s → c s d → O s d = μ.bind fun k => Ok k s d)
    (hnc : ∀ k s d, P s → ¬ c s d → Ok k s d = O s d)
    (hP : ∀ s d, P s → ¬ c s d → ∀ x ∈ (O s d).support, P x.2 ∨ ∀ k, N k x.2)
    (hN₀ : ∀ k s d, P s → c s d → ∀ x ∈ (Ok k s d).support, N k x.2)
    (hN : ∀ k s d, N k s → ∀ x ∈ (O s d).support, N k x.2)
    (hdone : ∀ k s d, N k s → Ok k s d = O s d) (A : OracleAdv D R α) (s : σ) (hs : P s) :
    OracleAdv.run O A s = μ.bind fun k => OracleAdv.run (Ok k) A s := by
  induction A generalizing s with
  | ret a => simp only [OracleAdv.run_ret, PMF.bind_const]
  | rand p f ih =>
    simp only [OracleAdv.run_rand, fun b => ih b s hs]
    exact PMF.bind_comm _ _ _
  | query d f ih =>
    simp only [OracleAdv.run_query]
    by_cases hcs : c s d
    · rw [hc s d hs hcs, PMF.bind_bind]
      refine congrArg _ (funext fun k => PMF.bind_congr_support _ _ _ fun x hx => ?_)
      exact (run_eq_run_of_inv O (Ok k) (N k) (hN k) (hdone k) _ _ (hN₀ k s d hs hcs x hx)).symm
    · simp only [hnc _ s d hs hcs]
      rw [PMF.bind_comm]
      refine PMF.bind_congr_support _ _ _ fun x hx => ?_
      rcases hP s d hs hcs x hx with h | h
      · exact ih x.1 x.2 h
      · simp only [run_eq_run_of_inv O _ _ (hN _) (hdone _) _ _ (h _), PMF.bind_const]

/-- **A key drawn at its first triggering call, placed in the state.** Let the oracle `O`, from
the states `P` before the draw, draw the key `k` from `μ` at the calls satisfying the trigger `c`
and continue as from the state `set k s`, and let the other calls from `P` lead to `P` and
commute with `set k`. Then from a state `s` of `P` the output of a run against `O` is the output
of the run against `O` from `set k s` with `k` drawn from `μ` before the run. -/
theorem run_map_fst_eq_bind_run_set_of_trigger (μ : PMF K) (O : σ → D → PMF (R × σ))
    (set : K → σ → σ) (P : σ → Prop) (c : σ → D → Prop)
    (hc : ∀ s d, P s → c s d → O s d = μ.bind fun k => O (set k s) d)
    (hnc : ∀ k s d, P s → ¬ c s d → O (set k s) d = (O s d).map (Prod.map id (set k)))
    (hP : ∀ s d, P s → ¬ c s d → ∀ x ∈ (O s d).support, P x.2) (A : OracleAdv D R α) (s : σ)
    (hs : P s) :
    (OracleAdv.run O A s).map Prod.fst =
      μ.bind fun k => (OracleAdv.run O A (set k s)).map Prod.fst := by
  induction A generalizing s with
  | ret a => simp only [OracleAdv.run_ret, PMF.pure_map, PMF.bind_const]
  | rand p f ih =>
    simp only [OracleAdv.run_rand, PMF.map_bind, fun b => ih b s hs]
    exact PMF.bind_comm _ _ _
  | query d f ih =>
    simp only [OracleAdv.run_query, PMF.map_bind]
    by_cases hcs : c s d
    · rw [hc s d hs hcs, PMF.bind_bind]
    · simp only [hnc _ s d hs hcs, PMF.bind_map, Function.comp_def, Prod.map_fst, Prod.map_snd,
        id_eq]
      rw [PMF.bind_comm]
      exact PMF.bind_congr_support _ _ _ fun x hx => ih x.1 x.2 (hP s d hs hcs x hx)

/-- **A key sampled at the first query.** Let `O` sample the key `k` from `μ` at its first call
from `s₀` and put it in place (`set k`), and let every call from a state with `k` in place leave
`k` in place. The output of a run against `O` from `s₀` is the output of a run against `O` with
the key put in place, averaged over `k` sampled from `μ` up front. -/
theorem run_map_fst_lazyKey (μ : PMF K) (O : σ → D → PMF (R × σ)) (set : K → σ → σ) (s₀ : σ)
    (h₀ : ∀ d, O s₀ d = μ.bind fun k => O (set k s₀) d)
    (hpres : ∀ k s d, ∀ x ∈ (O (set k s) d).support, set k x.2 = x.2) (A : OracleAdv D R α) :
    (OracleAdv.run O A s₀).map Prod.fst =
      μ.bind fun k => (OracleAdv.run (fun s d => O (set k s) d) A s₀).map Prod.fst := by
  rw [run_eq_bind_run_of_trigger μ O (fun k s d => O (set k s) d) (· = s₀) (fun _ _ => True)
    (fun k s => set k s = s) (fun s d hs _ => hs ▸ h₀ d) (fun _ _ _ _ h => absurd trivial h)
    (fun _ _ _ h => absurd trivial h) (fun k _ d _ _ x hx => hpres k _ d x hx)
    (fun k s d hs x hx => hpres k s d x (by rwa [hs])) (fun k s d hs => by rw [hs]) A s₀ rfl,
    PMF.map_bind]

end LazyKey

/-! ## Comparing bad flags -/

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

/-- **A weaker bad event sets its flag at most as often.** -/
theorem run_flagWhen_mono (O : σ → D → PMF (R × σ)) (bad₁ bad₂ : σ → D → R × σ → Prop)
    [∀ s d x, Decidable (bad₁ s d x)] [∀ s d x, Decidable (bad₂ s d x)]
    (h : ∀ s d x, bad₁ s d x → bad₂ s d x) (A : OracleAdv D R α) (s : σ) :
    (OracleAdv.run (OracleAdv.flagWhen bad₁ O) A (s, false)).toOuterMeasure
        {y | y.2.2 = true} ≤
      (OracleAdv.run (OracleAdv.flagWhen bad₂ O) A (s, false)).toOuterMeasure
        {y | y.2.2 = true} :=
  run_flagWhen_le_of_inv O bad₁ bad₂ (fun _ => True)
    (fun s d _ x _ => (em (bad₁ s d x)).elim (fun hb => Or.inl (h s d x hb))
      (fun hb => Or.inr ⟨hb, trivial⟩)) A s trivial

/-- **The union bound for bad flags**: the flag of `bad₁ ∨ bad₂` is set with at most the sum
of the probabilities that the flags of `bad₁` and of `bad₂` are set. -/
theorem run_flagWhen_or_le (O : σ → D → PMF (R × σ)) (bad₁ bad₂ : σ → D → R × σ → Prop)
    [∀ s d x, Decidable (bad₁ s d x)] [∀ s d x, Decidable (bad₂ s d x)]
    (A : OracleAdv D R α) (s : σ) :
    (OracleAdv.run (OracleAdv.flagWhen (fun s d x => bad₁ s d x ∨ bad₂ s d x) O) A
        (s, false)).toOuterMeasure {y | y.2.2 = true} ≤
      (OracleAdv.run (OracleAdv.flagWhen bad₁ O) A (s, false)).toOuterMeasure
          {y | y.2.2 = true} +
        (OracleAdv.run (OracleAdv.flagWhen bad₂ O) A (s, false)).toOuterMeasure
          {y | y.2.2 = true} := by
  let bad₂' : σ × Bool → D → R × (σ × Bool) → Prop := fun st d x => bad₂ st.1 d (x.1, x.2.1)
  let O₂ := OracleAdv.flagWhen bad₂' (OracleAdv.flagWhen bad₁ O)
  have h₁ : (OracleAdv.run O₂ A ((s, false), false)).map (Prod.map id Prod.fst) =
      OracleAdv.run (OracleAdv.flagWhen bad₁ O) A (s, false) :=
    OracleAdv.run_flagWhen_map bad₂' _ A _ false
  have h₂ : (OracleAdv.run O₂ A ((s, false), false)).map
      (Prod.map id fun st => (st.1.1, st.2)) =
        OracleAdv.run (OracleAdv.flagWhen bad₂ O) A (s, false) :=
    OracleAdv.run_map_state _ _ _ (fun st d => by
      simp only [O₂, bad₂', OracleAdv.flagWhen, PMF.map_comp]
      rfl) A _
  have h₃ : (OracleAdv.run O₂ A ((s, false), false)).map
      (Prod.map id fun st => (st.1.1, st.1.2 || st.2)) =
        OracleAdv.run (OracleAdv.flagWhen (fun s d x => bad₁ s d x ∨ bad₂ s d x) O) A
          (s, false) :=
    OracleAdv.run_map_state _ _ _ (fun st d => by
      simp only [O₂, bad₂', OracleAdv.flagWhen, PMF.map_comp]
      congr 1
      funext x
      simp only [Function.comp_apply, Prod.map_apply, id_eq, Bool.decide_or]
      cases st.1.2 <;> cases st.2 <;> simp) A _
  rw [← h₁, ← h₂, ← h₃, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_map_apply]
  refine (MeasureTheory.measure_mono ?_).trans (MeasureTheory.measure_union_le _ _)
  intro y hy
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hy ⊢
  simp only [Set.mem_union, Set.mem_preimage, Set.mem_ofPred_eq]
  grind

/-- A flagged run does not depend on the decision procedure of the bad event. -/
theorem run_flagWhen_inst (O : σ → D → PMF (R × σ)) (bad : σ → D → R × σ → Prop)
    (i j : ∀ s d x, Decidable (bad s d x)) (A : OracleAdv D R α) (s : σ × Bool) :
    OracleAdv.run (@OracleAdv.flagWhen D R σ bad i O) A s =
      OracleAdv.run (@OracleAdv.flagWhen D R σ bad j O) A s := by
  rw [Subsingleton.elim i j]

end FlagMono

end CatCrypt.Crypto.OracleAdv
