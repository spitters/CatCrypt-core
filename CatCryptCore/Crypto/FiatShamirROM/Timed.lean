/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleAdversaryTimed
public import CatCryptCore.Crypto.FiatShamirROM.StraightLineMk
public import CatCryptCore.Crypto.FiatShamirROM.KeyRecoveryFlag
public import CatCryptCore.Crypto.FiatShamirROM.ProgFlag
public import CatCryptCore.Crypto.FiatShamirROM.Reduction
public import CatCryptCore.Crypto.Signatures.EUFCMAPMF

/-!
# Running time of the Fiat–Shamir ROM reductions

The extraction reductions of the Fiat–Shamir ROM development (`slReductionMk`,
`slReductionCls`, `slReduction`, `recReduction`) run the adversary followed by the
verifier's queries against a stateful oracle from initial tables and apply an output map
to the forgery and the final state: they have the form
`(OracleAdv.run O (withVerify x (A.run x)) s₀).map out`. The hybrid distinguisher
`hybDistByP` runs the adversary against the real hash oracle and a hybrid signing oracle
and forwards one signing query to its challenge oracle.

Each reduction has a costed form built from a costed witness `A'` of the adversary, with
`(A' x).erase = A.run x` and `(A' x).TimeBound T`. A reduction returning a probability
mass function has as costed form an `OracleAdv.Timed` tree over the empty oracle
interface (`timedRun`): every oracle call becomes one `rand` node over the distribution
of the call, and the run of the erased tree under any oracle has the output distribution
of the reduction (`*.run_erase_timed`). The costed hybrid distinguisher is an
`OracleAdv.Timed` tree whose erasure is the distinguisher (`hybDistByP.erase_timed`).

With `A'` of time `T`, at most `qH` hash and `qS` signing queries, and `V = G.V`
verifier points, every extraction reduction has time at most
`T + (tV + V * (tV + 1)) + ((tH + 1) * (qH + V) + (tS + 1) * qS) + tOut`, and so does
the hybrid distinguisher.

The rewinding reduction `extractReduction` runs the simulated game as a forking run
(`OracleForking.forkRun`). Its costed form is built from the costed forking run
`OracleForking.forkRun.timedK`, stated for any stateful oracle with fresh draws and any
costed adversary: the first run, at every fresh draw the fork decision, and on a result
without a second run whose output refers to that draw, the second run of the continuation
from the fork point with a fresh draw. A second run is started only on a result without
one, so every path holds at most one; on the support of the forking run the decision
agrees with that of `forkRun` when the counter is preserved by plain and incremented by
fresh transitions and every output refers to at most one draw. The rewinding reduction
has time at most
`2 * (T + (tV + V * (tV + 1)) + ((tH + tF + 1) * (qH + V) + (tS + 1) * qS)) + tExt`.

## Cost model

The registered costs of `CatCryptCore.Crypto.OracleAdversaryTimed`: one unit per `rand`
and per `query` node. The following costs are parameters:

* `tV` — computing one verifier point `G.vkey x m σ vs` and appending a value to `vs`;
  it is charged once before the first verifier query and once after each;
* `tH` — the local computation of one hash step of the oracle (a table lookup and an
  update), charged after the `rand` node that samples the step; at a designated point of
  the marker game `tMk` more is charged, the evaluation of the markers;
* `tS` — the local computation of one signing step (the attempt, its trace and the
  table updates);
* `tOut` — the output map: the extractor `E.ext` on the final tables, the recovery
  `ρ.recover` on the visible entries, or the predicate of the hybrid distinguisher;
* `tF` — the fork decision after a fresh draw: the counter `ctr s` and the predicate
  `hit` on the result of the rest of the run (for `extractReduction`, `hashCount` and
  `hitAt`); it is charged once per fresh draw, and the time theorems charge it to every
  hash query;
* `tExt` — the extractor `P.extract` on a forked pair, or the default witness.

The sampling inside one oracle step (a fresh answer, the values of an attempt, the
fresh values at the markers) is one distribution, sampled at one `rand` node.

## Main definitions

* `OracleAdv.Timed.oracleStep`, `OracleAdv.Timed.runOracle` — a stateful oracle call as
  one `rand` node, and the run of a costed adversary against a stateful oracle
* `OracleAdv.Timed.stepBind` — sequencing of a step-prefixed tree
* `verifyQueries.timed`, `withVerify.timed` — the verifier's queries with step costs
* `timedRun` — the costed form of `(OracleAdv.run O (withVerify x A) s₀).map out`
* `slReductionMk.timed`, `slReductionCls.timed`, `slReduction.timed`,
  `recReduction.timed`, `hybRunOf.timed`, `hybDistByOf.timed`, `hybDistByP.timed`
* `OracleForking.forkRun.timedK`, `OracleForking.forkRun.timed` — the costed forking run
  followed by a continuation, and with the result as output; its parts
  `forkRun.timedDecide` (the fork decision) and `forkRun.timedSecond` (the second run)
* `extractReduction.timed` — the costed rewinding reduction

## Main results

* `OracleAdv.Timed.timeBound_simulate_of_isQueryBoundBy` — simulation time with a cost
  per query: time at most `T + n` when the query costs of `A` sum to at most `n`
* `OracleAdv.Timed.run_erase_runOracle`, `OracleAdv.Timed.timeBound_runOracle`
* `withVerify_eq_bind` — the verifier's queries are a sequencing after the adversary
* `slReductionMk.run_erase_timed`, `slReductionMk.timeBound_timed` and the same pair for
  `slReductionCls`, `slReduction`, `recReduction`
* `hybDistByP.erase_timed`, `hybDistByP.timeBound_timed`
* `OracleAdv.run_bind_map_fst_empty` — over the empty interface, the output distribution
  of a sequencing is the sequencing of the output distributions
* `OracleForking.exists_hit_of_mem_support_forkRun` — a forked result refers to a draw
  numbered at or above the start counter
* `OracleForking.forkRun.run_erase_timedK`, `OracleForking.forkRun.run_erase_timed` — the
  erased costed forking run has the distribution of `forkRun`
* `OracleForking.forkRun.timeBound_timedK` — with `A` of time `T`, query costs at most `n`
  and a second-run budget `B ≥ T + n`, time at most `T + n + B + M` for a continuation of
  time `M` on forked and `M + B` on unforked results;
  `OracleForking.forkRun.timeBound_timed` — time at most `2 * (T + n)`
* `extractReduction.run_erase_timed`, `extractReduction.timeBound_timed`
* `OracleAdv.run_map_fst_empty_eq` — over the empty interface, the output distribution of
  a run is independent of the oracle and its state
* `TimedInverter`, `TimedTwoStage` — a costed inverter and a costed two-stage reduction
  over the empty interface; `TimedInverter.of_erase`, `TimedTwoStage.of_erase` derive them
  from an erasure equation of the costed tree and its time bound
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto

namespace OracleAdv.Timed

variable {D R D' R' α β : Type}

/-! ## Sequencing a step-prefixed tree -/

/-- The step-prefixed tree `p` followed by `f` on its output. -/
def stepBind (p : ℕ × Timed D R α) (f : α → ℕ × Timed D R β) : ℕ × Timed D R β :=
  delay p.1 (p.2.bind f)

theorem erase_stepBind (p : ℕ × Timed D R α) (f : α → ℕ × Timed D R β) :
    (stepBind p f).2.erase = p.2.erase.bind fun a => (f a).2.erase :=
  erase_bind p.2 f

/-- Times add under sequencing of a step-prefixed tree. -/
theorem timeBound_stepBind {p : ℕ × Timed D R α} {f : α → ℕ × Timed D R β} {m n : ℕ}
    (hp : StepTimeBound p m) (hf : ∀ a, StepTimeBound (f a) n) :
    StepTimeBound (stepBind p f) (m + n) :=
  (stepTimeBound_delay (c := p.1) (timeBound_bind hp.2 hf)).mono (by have := hp.1; omega)

/-! ## Simulation with a cost per query -/

/-- **Simulation time with a cost per query.** If `A` has time `T`, every program of
`impl` answering `d` has time at most `t d`, and the costs `t d` of the queries of `A`
sum to at most `n` on every path, then the simulated adversary has time at most
`T + n`. -/
theorem timeBound_simulate_of_isQueryBoundBy {S : Type}
    (impl : S → D → ℕ × Timed D' R' (R × S)) (t : D → ℕ)
    (himpl : ∀ s d, StepTimeBound (impl s d) (t d)) {A : Timed D R α} {T n : ℕ}
    (hA : A.TimeBound T) (hq : A.erase.IsQueryBoundBy t n) (s : S) :
    StepTimeBound (simulate impl A s) (T + n) := by
  induction A generalizing T n s with
  | ret a => exact ⟨Nat.zero_le _, trivial⟩
  | rand p c k ih =>
    have h1 := hA.1
    simp only [simulate, stepTimeBound_zero, timeBound_rand_iff]
    refine ⟨by omega, fun b => ?_⟩
    have h2 := (hA.2 b).1
    exact (stepTimeBound_delay (c := c b) (ih b (hA.2 b).2 (hq b) s)).mono (by omega)
  | query d c k ih =>
    obtain ⟨hd, hk⟩ := hq
    have hk' : ∀ x : R × S, StepTimeBound (delay (c x.1) (simulate impl (k x.1) x.2))
        (T - 1 + (n - t d)) := fun x =>
      (stepTimeBound_delay (ih x.1 (hA.2 x.1).2 (hk x.1) x.2)).mono
        (by have := (hA.2 x.1).1; omega)
    have hi := himpl s d
    have h := stepTimeBound_delay (c := (impl s d).1) (timeBound_bind hi.2 hk')
    exact h.mono (by have := hi.1; have := hA.1; omega)

/-! ## Runs against a stateful oracle -/

/-- The call of the stateful oracle `O` at `d` from the state `s` as one `rand` node
over its distribution, at step cost `t d`. -/
def oracleStep {S : Type} (O : S → D → PMF (R × S)) (t : D → ℕ) (s : S) (d : D) :
    ℕ × Timed D' R' (R × S) :=
  (t d, rand (O s d) (fun _ => 0) ret)

/-- The run of the costed adversary `A` against the stateful oracle `O` from the state
`s`, each call at `d` charged `t d` and one `rand` node. -/
def runOracle {S : Type} (O : S → D → PMF (R × S)) (t : D → ℕ) (A : Timed D R α) (s : S) :
    ℕ × Timed D' R' (α × S) :=
  simulate (oracleStep O t) A s

/-- Under any oracle `O'`, the run of the erased `runOracle O t A s` has the output
distribution of the run of the erased `A` against `O`. -/
theorem run_erase_runOracle {S U : Type} (O : S → D → PMF (R × S)) (t : D → ℕ)
    (O' : U → D' → PMF (R' × U)) (A : Timed D R α) (s : S) (u : U) :
    (OracleAdv.run O' (runOracle (D' := D') (R' := R') O t A s).2.erase u).map Prod.fst =
      OracleAdv.run O A.erase s := by
  rw [runOracle, erase_simulate, OracleAdv.run_simulate, PMF.map_comp]
  rw [← OracleAdv.run_map_state (OracleAdv.simOracle _ O') O Prod.fst ?_ A.erase (s, u)]
  · rfl
  · intro s d
    simp [OracleAdv.simOracle, oracleStep, erase, PMF.map_bind, PMF.pure_map, PMF.bind_pure]

/-- One oracle call costs its step cost and one node. -/
theorem stepTimeBound_oracleStep {S : Type} (O : S → D → PMF (R × S)) (t : D → ℕ) (s : S)
    (d : D) : StepTimeBound (oracleStep (D' := D') (R' := R') O t s d) (t d + 1) := by
  refine ⟨Nat.le_succ _, ?_⟩
  show (rand (O s d) (fun _ => 0) ret).TimeBound (t d + 1 - t d)
  exact ⟨by omega, fun _ => ⟨Nat.zero_le _, trivial⟩⟩

/-- **Time of a run against a stateful oracle.** With `A` of time `T` whose query costs
`t d + 1` sum to at most `n`, the run has time at most `T + n`. -/
theorem timeBound_runOracle {S : Type} (O : S → D → PMF (R × S)) (t : D → ℕ)
    {A : Timed D R α} {T n : ℕ} (hA : A.TimeBound T)
    (hq : A.erase.IsQueryBoundBy (fun d => t d + 1) n) (s : S) :
    StepTimeBound (runOracle (D' := D') (R' := R') O t A s) (T + n) :=
  timeBound_simulate_of_isQueryBoundBy _ _ (fun s d => stepTimeBound_oracleStep O t s d) hA hq s

end OracleAdv.Timed

/-- Over the empty interface, the output distribution of a sequencing is the sequencing of
the output distributions. -/
theorem OracleAdv.run_bind_map_fst_empty {U β γ : Type} (O' : U → Empty → PMF (Empty × U))
    (A : OracleAdv Empty Empty β) (f : β → OracleAdv Empty Empty γ) (u : U) :
    (OracleAdv.run O' (A.bind f) u).map Prod.fst =
      ((OracleAdv.run O' A u).map Prod.fst).bind
        fun b => (OracleAdv.run O' (f b) u).map Prod.fst := by
  induction A with
  | ret b => simp [OracleAdv.bind, PMF.pure_map]
  | rand p k ih => simp only [OracleAdv.bind, OracleAdv.run_rand, PMF.map_bind, PMF.bind_bind, ih]
  | query d k _ => exact d.elim

/-- Over the empty interface, the output distribution of a run depends neither on the oracle
nor on its initial state. -/
theorem OracleAdv.run_map_fst_empty_eq {U V β : Type} (O' : U → Empty → PMF (Empty × U))
    (O'' : V → Empty → PMF (Empty × V)) (A : OracleAdv Empty Empty β) (u : U) (v : V) :
    (OracleAdv.run O' A u).map Prod.fst = (OracleAdv.run O'' A v).map Prod.fst := by
  induction A with
  | ret b => simp [PMF.pure_map]
  | rand p k ih => simp only [OracleAdv.run_rand, PMF.map_bind, ih]
  | query d k _ => exact d.elim

/-! ## The costed forking run -/

namespace OracleForking

section ForkTimed

variable {D R S Ch α : Type} [Fintype Ch] [Nonempty Ch]
  (O : S → D → Step R S Ch) (ctr : S → ℕ) (hit : ℕ → α × S → Bool) (t : D → ℕ) (tF : ℕ)

/-- The costed second run of a fork: from the answer `f e₂` of the fresh draw `e₂`, the
oracle step cost `td`, the step cost of the adversary's continuation `c`, `k`, the run of
the continuation against the oracle, and `g'` on its output. -/
noncomputable def forkRun.timedSecond {γ : Type} (td : ℕ) (f : Ch → R × S) (c : R → ℕ)
    (k : R → OracleAdv.Timed D R α) (g' : α × S → ℕ × OracleAdv.Timed Empty Empty γ)
    (e₂ : Ch) : ℕ × OracleAdv.Timed Empty Empty γ :=
  OracleAdv.Timed.stepBind (OracleAdv.Timed.delay (td + c (f e₂).1)
    (OracleAdv.Timed.runOracle (toOracle O) t (k (f e₂).1) (f e₂).2)) g'

/-- The costed fork decision after the fresh draw `e₁` at the state `s` on the result `r`
of the rest of the run, at cost `tF`: when `r` has no second run and its output refers to
the draw numbered `ctr s`, a fresh draw `e₂` and the costed second run followed by `g` on
the forked pair; otherwise `g r`. -/
noncomputable def forkRun.timedDecide {γ : Type} (s : S) (td : ℕ) (f : Ch → R × S)
    (c : R → ℕ) (k : R → OracleAdv.Timed D R α)
    (g : (α × S) × Option ((α × S) × Ch × Ch) → ℕ × OracleAdv.Timed Empty Empty γ) (e₁ : Ch)
    (r : (α × S) × Option ((α × S) × Ch × Ch)) : ℕ × OracleAdv.Timed Empty Empty γ :=
  if r.2.isNone && hit (ctr s) r.1 then
    (tF, .rand (PMF.uniformOfFintype Ch)
      (fun e₂ => (forkRun.timedSecond O t td f c k (fun y₂ => g (r.1, some (y₂, e₁, e₂))) e₂).1)
      fun e₂ => (forkRun.timedSecond O t td f c k (fun y₂ => g (r.1, some (y₂, e₁, e₂))) e₂).2)
  else OracleAdv.Timed.delay tF (g r)

/-- **The costed forking run**, followed by the continuation `g` on its result. An oracle
call at `d` is one `rand` node over its transition at step cost `t d`; after a fresh draw
the rest of the run is followed by the costed fork decision `forkRun.timedDecide`. A
second run is started only on a result without one, so every path holds at most one. -/
noncomputable def forkRun.timedK {γ : Type} :
    OracleAdv.Timed D R α → S →
      ((α × S) × Option ((α × S) × Ch × Ch) → ℕ × OracleAdv.Timed Empty Empty γ) →
      ℕ × OracleAdv.Timed Empty Empty γ
  | .ret a, s, g => g ((a, s), none)
  | .rand p c k, s, g => (0, .rand p (fun b => c b + (forkRun.timedK (k b) s g).1)
      fun b => (forkRun.timedK (k b) s g).2)
  | .query d c k, s, g =>
    match O s d with
    | .plain p => (t d, .rand p (fun x => c x.1 + (forkRun.timedK (k x.1) x.2 g).1)
        fun x => (forkRun.timedK (k x.1) x.2 g).2)
    | .fresh f => (t d, .rand (PMF.uniformOfFintype Ch)
        (fun e₁ => c (f e₁).1 + (forkRun.timedK (k (f e₁).1) (f e₁).2
          (forkRun.timedDecide O ctr hit t tF s (t d) f c k g e₁)).1)
        fun e₁ => (forkRun.timedK (k (f e₁).1) (f e₁).2
          (forkRun.timedDecide O ctr hit t tF s (t d) f c k g e₁)).2)

/-- The costed forking run: `forkRun.timedK` with the result as output. -/
noncomputable def forkRun.timed (A : OracleAdv.Timed D R α) (s : S) :
    ℕ × OracleAdv.Timed Empty Empty ((α × S) × Option ((α × S) × Ch × Ch)) :=
  forkRun.timedK O ctr hit t tF A s fun r => (0, .ret r)

/-- A result of the forking run with a second run has an output referring to a draw
numbered at or above the counter of the start state. -/
theorem exists_hit_of_mem_support_forkRun
    (hplain : ∀ s d p, O s d = .plain p → ∀ x ∈ p.support, ctr x.2 = ctr s)
    (hfresh : ∀ s d f, O s d = .fresh f → ∀ e, ctr (f e).2 = ctr s + 1)
    (A : OracleAdv D R α) (s : S) (r : (α × S) × Option ((α × S) × Ch × Ch))
    (hr : r ∈ (forkRun O ctr hit A s).support) (h2 : r.2.isSome = true) :
    ∃ c, ctr s ≤ c ∧ hit c r.1 = true := by
  induction A generalizing s r with
  | ret a =>
    simp only [forkRun, PMF.support_pure, Set.mem_singleton_iff] at hr
    subst hr
    simp at h2
  | rand p k ih =>
    simp only [forkRun, PMF.mem_support_bind_iff] at hr
    obtain ⟨b, _, hb⟩ := hr
    exact ih b s r hb h2
  | query d k ih =>
    cases h : O s d with
    | plain p =>
      simp only [forkRun, h, PMF.mem_support_bind_iff] at hr
      obtain ⟨x, hx, hr⟩ := hr
      obtain ⟨c, hc, hh⟩ := ih _ _ r hr h2
      exact ⟨c, by rw [hplain s d p h x hx] at hc; exact hc, hh⟩
    | fresh f =>
      simp only [forkRun, h, PMF.mem_support_bind_iff] at hr
      obtain ⟨e, _, r', hr', hr⟩ := hr
      split_ifs at hr with hh
      · rw [PMF.mem_support_bind_iff] at hr
        obtain ⟨e', _, hr⟩ := hr
        rw [PMF.mem_support_map_iff] at hr
        obtain ⟨y, _, rfl⟩ := hr
        exact ⟨ctr s, le_rfl, hh⟩
      · rw [PMF.support_pure, Set.mem_singleton_iff] at hr
        rw [hr] at h2 ⊢
        obtain ⟨c, hc, hh'⟩ := ih _ _ r' hr' h2
        exact ⟨c, by rw [hfresh s d f h e] at hc; omega, hh'⟩

/-- **Erasure of the costed forking run.** When plain transitions keep the counter, fresh
transitions increment it and every output refers to at most one draw, then under any
oracle the erased `forkRun.timedK A s g` has the output distribution of the forking run of
the erased `A` followed by the erased `g`. -/
theorem forkRun.run_erase_timedK
    (hplain : ∀ s d p, O s d = .plain p → ∀ x ∈ p.support, ctr x.2 = ctr s)
    (hfresh : ∀ s d f, O s d = .fresh f → ∀ e, ctr (f e).2 = ctr s + 1)
    (hdisj : ∀ c c' y, hit c y = true → hit c' y = true → c = c')
    {U : Type} (O' : U → Empty → PMF (Empty × U)) (u : U) {γ : Type}
    (A : OracleAdv.Timed D R α) (s : S)
    (g : (α × S) × Option ((α × S) × Ch × Ch) → ℕ × OracleAdv.Timed Empty Empty γ) :
    (OracleAdv.run O' (forkRun.timedK O ctr hit t tF A s g).2.erase u).map Prod.fst =
      (forkRun O ctr hit A.erase s).bind
        fun r => (OracleAdv.run O' (g r).2.erase u).map Prod.fst := by
  induction A generalizing s g with
  | ret a => simp [forkRun.timedK, OracleAdv.Timed.erase, forkRun]
  | rand p c k ih =>
    simp only [forkRun.timedK, OracleAdv.Timed.erase, forkRun, OracleAdv.run_rand,
      PMF.map_bind, PMF.bind_bind, ih]
  | query d c k ih =>
    cases h : O s d with
    | plain p =>
      simp only [forkRun.timedK, h, OracleAdv.Timed.erase, forkRun, OracleAdv.run_rand,
        PMF.map_bind, PMF.bind_bind, ih]
    | fresh f =>
      simp only [forkRun.timedK, h, OracleAdv.Timed.erase, forkRun, OracleAdv.run_rand,
        PMF.map_bind, PMF.bind_bind, ih]
      congr 1
      funext e₁
      apply PMF.bind_congr_support
      intro r hr
      by_cases hh : hit (ctr s) r.1 = true
      · have hn : r.2.isNone = true := by
          cases h2 : r.2 with
          | none => rfl
          | some _ =>
            obtain ⟨c', hc', hh'⟩ := exists_hit_of_mem_support_forkRun O ctr hit hplain hfresh
              _ _ r hr (by rw [h2]; rfl)
            rw [hfresh s d f h e₁] at hc'
            have := hdisj _ _ _ hh hh'
            omega
        simp only [forkRun.timedDecide, hn, hh, Bool.and_self, if_true, OracleAdv.Timed.erase,
          OracleAdv.run_rand, PMF.map_bind, PMF.bind_bind, PMF.bind_map]
        congr 1
        funext e₂
        rw [forkRun.timedSecond, OracleAdv.Timed.erase_stepBind,
          OracleAdv.run_bind_map_fst_empty]
        simp only [OracleAdv.Timed.delay]
        rw [OracleAdv.Timed.run_erase_runOracle]
        rfl
      · simp only [forkRun.timedDecide, hh, Bool.and_false, Bool.false_eq_true, if_false,
          OracleAdv.Timed.delay, PMF.pure_bind]

/-- Under the hypotheses of `forkRun.run_erase_timedK`, the erased costed forking run has
the output distribution of the forking run of the erased adversary. -/
theorem forkRun.run_erase_timed
    (hplain : ∀ s d p, O s d = .plain p → ∀ x ∈ p.support, ctr x.2 = ctr s)
    (hfresh : ∀ s d f, O s d = .fresh f → ∀ e, ctr (f e).2 = ctr s + 1)
    (hdisj : ∀ c c' y, hit c y = true → hit c' y = true → c = c')
    {U : Type} (O' : U → Empty → PMF (Empty × U)) (u : U) (A : OracleAdv.Timed D R α)
    (s : S) :
    (OracleAdv.run O' (forkRun.timed O ctr hit t tF A s).2.erase u).map Prod.fst =
      forkRun O ctr hit A.erase s := by
  rw [forkRun.timed, forkRun.run_erase_timedK O ctr hit t tF hplain hfresh hdisj]
  simp only [OracleAdv.Timed.erase, OracleAdv.run_ret, PMF.pure_map, PMF.bind_pure]

/-- **Time of the costed forking run.** Let `A` have time `T` with query costs `u d` summing
to at most `n`, where `u d` covers the oracle step `t d`, its node, and at a fresh draw the
fork decision `tF`. For a budget `B ≥ T + n` of a second run, and a continuation `g` of
time `M` on a forked result and `M + B` on a result without a second run, the costed
forking run followed by `g` has time at most `T + n + B + M`. -/
theorem forkRun.timeBound_timedK (u : D → ℕ) (ht : ∀ d, t d + 1 ≤ u d)
    (htF : ∀ s d f, O s d = .fresh f → t d + tF + 1 ≤ u d) (B : ℕ) {γ : Type}
    (A : OracleAdv.Timed D R α) {T n : ℕ} (hA : A.TimeBound T)
    (hq : A.erase.IsQueryBoundBy u n) (hB : T + n ≤ B) (s : S)
    (g : (α × S) × Option ((α × S) × Ch × Ch) → ℕ × OracleAdv.Timed Empty Empty γ) (M : ℕ)
    (hg : ∀ r, OracleAdv.Timed.StepTimeBound (g r) (M + bif r.2.isNone then B else 0)) :
    OracleAdv.Timed.StepTimeBound (forkRun.timedK O ctr hit t tF A s g) (T + n + B + M) := by
  induction A generalizing T n s g M with
  | ret a =>
    refine (hg _).mono ?_
    simp only [Option.isNone_none, cond_true]
    omega
  | rand p c k ih =>
    have h1 := hA.1
    simp only [forkRun.timedK, OracleAdv.Timed.stepTimeBound_zero,
      OracleAdv.Timed.timeBound_rand_iff]
    refine ⟨by omega, fun b => ?_⟩
    have h2 := (hA.2 b).1
    exact (OracleAdv.Timed.stepTimeBound_delay (c := c b)
      (ih b (hA.2 b).2 (hq b) (by omega) s g M hg)).mono (by omega)
  | query d c k ih =>
    obtain ⟨hd, hk⟩ := hq
    have h1 := hA.1
    have htd := ht d
    cases h : O s d with
    | plain p =>
      simp only [forkRun.timedK, h]
      refine ⟨by omega, (OracleAdv.Timed.timeBound_rand_iff _ _ _ _).2 ⟨by omega, fun x => ?_⟩⟩
      have h2 := (hA.2 x.1).1
      exact (OracleAdv.Timed.stepTimeBound_delay (c := c x.1)
        (ih x.1 (hA.2 x.1).2 (hk x.1) (by omega) x.2 g M hg)).mono (by omega)
    | fresh f =>
      have htf := htF s d f h
      simp only [forkRun.timedK, h]
      refine ⟨by omega, (OracleAdv.Timed.timeBound_rand_iff _ _ _ _).2 ⟨by omega, fun e₁ => ?_⟩⟩
      have h2 := (hA.2 (f e₁).1).1
      refine (OracleAdv.Timed.stepTimeBound_delay (c := c (f e₁).1)
        (ih (f e₁).1 (hA.2 (f e₁).1).2 (hk (f e₁).1) (by omega) (f e₁).2 _ (M + tF) ?_)).mono
        (by omega)
      intro r
      unfold forkRun.timedDecide
      split_ifs with hr
      · rw [Bool.and_eq_true] at hr
        have hn := hr.1
        simp only [hn, cond_true]
        refine ⟨by omega, (OracleAdv.Timed.timeBound_rand_iff _ _ _ _).2
          ⟨by omega, fun e₂ => ?_⟩⟩
        have h3 := (hA.2 (f e₂).1).1
        have hr2 := OracleAdv.Timed.timeBound_runOracle (D' := Empty) (R' := Empty)
          (toOracle O) t (hA.2 (f e₂).1).2 ((hk (f e₂).1).of_cost_le ht) (f e₂).2
        have hY := OracleAdv.Timed.timeBound_stepBind (n := M)
          (OracleAdv.Timed.stepTimeBound_delay (c := t d + c (f e₂).1) hr2)
          (f := fun y₂ => g (r.1, some (y₂, e₁, e₂))) fun y₂ => by
            simpa using hg (r.1, some (y₂, e₁, e₂))
        exact hY.mono (by omega)
      · exact (OracleAdv.Timed.stepTimeBound_delay (c := tF) (hg r)).mono (by omega)

/-- **Time of the costed forking run.** With `A` of time `T` and query costs `u d` (the
oracle step `t d`, its node, and the fork decision `tF` at a fresh draw) summing to at most
`n`, the costed forking run has time at most `2 * (T + n)`: the first run and at most one
second run from the fork point. -/
theorem forkRun.timeBound_timed (u : D → ℕ) (ht : ∀ d, t d + 1 ≤ u d)
    (htF : ∀ s d f, O s d = .fresh f → t d + tF + 1 ≤ u d) {A : OracleAdv.Timed D R α}
    {T n : ℕ} (hA : A.TimeBound T) (hq : A.erase.IsQueryBoundBy u n) (s : S) :
    OracleAdv.Timed.StepTimeBound (forkRun.timed O ctr hit t tF A s) (2 * (T + n)) :=
  (forkRun.timeBound_timedK O ctr hit t tF u ht htF (T + n) A hA hq le_rfl s
    (fun r => (0, .ret r)) 0 fun _ => ⟨Nat.zero_le _, trivial⟩).mono (by omega)

end ForkTimed

end OracleForking

namespace FiatShamirROM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.OracleForking
open scoped ENNReal

open Protocol

/-! ## The verifier's queries -/

section Verify

variable {G : Protocol}

/-- The verifier's queries after the adversary are a sequencing. -/
theorem withVerify_eq_bind (x : G.Stmt) (A : OracleAdv G.Query G.Answer G.Forgery) :
    withVerify x A = A.bind fun f => verifyQueries x f.1 f.2 G.V [] := by
  induction A with
  | ret f => rfl
  | rand p k ih => simp only [withVerify, OracleAdv.bind, ih]
  | query d k ih => simp only [withVerify, OracleAdv.bind, ih]

/-- The costed verifier's queries: after each answer, the next verifier point is
computed at cost `tV`. -/
def verifyQueries.timed (tV : ℕ) (x : G.Stmt) (m : G.Msg) (σ : G.Sig) :
    ℕ → List G.Ch → OracleAdv.Timed G.Query G.Answer G.Forgery
  | 0, _ => .ret (m, σ)
  | n + 1, acc => .query (.inl (G.vkey x m σ acc)) (fun _ => tV) fun a => match a with
    | .inl e => verifyQueries.timed tV x m σ n (acc ++ [e])
    | .inr _ => .ret (m, σ)

theorem verifyQueries.erase_timed (tV : ℕ) (x : G.Stmt) (m : G.Msg) (σ : G.Sig) (n : ℕ)
    (acc : List G.Ch) :
    (verifyQueries.timed tV x m σ n acc).erase = verifyQueries x m σ n acc := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
    simp only [verifyQueries.timed, verifyQueries, OracleAdv.Timed.erase]
    congr 1
    funext a
    cases a with
    | inl e => exact ih _
    | inr _ => rfl

theorem verifyQueries.timeBound_timed (tV : ℕ) (x : G.Stmt) (m : G.Msg) (σ : G.Sig)
    (n : ℕ) (acc : List G.Ch) :
    (verifyQueries.timed tV x m σ n acc).TimeBound (n * (tV + 1)) := by
  induction n generalizing acc with
  | zero => trivial
  | succ n ih =>
    rw [Nat.succ_mul]
    refine ⟨by omega, fun a => ⟨show tV ≤ _ by omega, ?_⟩⟩
    cases a with
    | inl e => exact (ih _).mono (by dsimp only; omega)
    | inr _ => trivial

/-- The costed form of `withVerify x`: the adversary `A'`, then `tV` for the first
verifier point and the verifier's queries. -/
def withVerify.timed (tV : ℕ) (x : G.Stmt) (A' : OracleAdv.Timed G.Query G.Answer G.Forgery) :
    ℕ × OracleAdv.Timed G.Query G.Answer G.Forgery :=
  A'.bind fun f => (tV, verifyQueries.timed tV x f.1 f.2 G.V [])

theorem withVerify.erase_timed (tV : ℕ) (x : G.Stmt)
    (A' : OracleAdv.Timed G.Query G.Answer G.Forgery) :
    (withVerify.timed tV x A').2.erase = withVerify x A'.erase := by
  rw [withVerify.timed, OracleAdv.Timed.erase_bind, withVerify_eq_bind]
  simp only [verifyQueries.erase_timed]

theorem withVerify.timeBound_timed (tV : ℕ) (x : G.Stmt)
    {A' : OracleAdv.Timed G.Query G.Answer G.Forgery} {T : ℕ} (hT : A'.TimeBound T) :
    OracleAdv.Timed.StepTimeBound (withVerify.timed tV x A') (T + (tV + G.V * (tV + 1))) :=
  OracleAdv.Timed.timeBound_bind hT fun f =>
    ⟨by omega, (verifyQueries.timeBound_timed tV x f.1 f.2 G.V []).mono (by omega)⟩

/-- The verified run of an adversary with at most `qH` hash and `qS` signing queries
has query costs at most `(tH + 1) * (qH + V) + (tS + 1) * qS` for a cost `t` of at most
`tH` per hash and `tS` per signing query, plus one per query. -/
theorem isQueryBoundBy_withVerify_succ (x : G.Stmt) (t : G.Query → ℕ) {tH tS : ℕ}
    (ht : ∀ d, t d ≤ Sum.elim (fun _ => tH) (fun _ => tS) d)
    {A : OracleAdv G.Query G.Answer G.Forgery} {qH qS : ℕ} (hq : IsQueryBound₂ A qH qS) :
    (withVerify x A).IsQueryBoundBy (fun d => t d + 1)
      ((tH + 1) * (qH + G.V) + (tS + 1) * qS) :=
  ((isQueryBound₂_withVerify x A qH qS hq).isQueryBoundBy (tH + 1) (tS + 1)).of_cost_le
    fun d => by
      have := ht d
      cases d <;> simpa using this

end Verify

/-! ## The costed form of a verified run against a stateful oracle -/

section Run

variable {G : Protocol}

/-- **The costed verified run.** The costed adversary `A'` with the verifier's queries,
run against the stateful oracle `O` from `s₀` with step cost `t d` per call at `d`,
followed by the output map `out` at cost `tOut`; a tree over the empty interface. -/
def timedRun {S β : Type} (tV tOut : ℕ) (O : S → G.Query → PMF (G.Answer × S))
    (t : G.Query → ℕ) (s₀ : S) (out : G.Forgery × S → β) (x : G.Stmt)
    (A' : OracleAdv.Timed G.Query G.Answer G.Forgery) : ℕ × OracleAdv.Timed Empty Empty β :=
  OracleAdv.Timed.stepBind
    (OracleAdv.Timed.delay (withVerify.timed tV x A').1
      (OracleAdv.Timed.runOracle O t (withVerify.timed tV x A').2 s₀))
    fun y => (tOut, .ret (out y))

/-- Under any oracle, the costed verified run has the output distribution of
`(OracleAdv.run O (withVerify x A'.erase) s₀).map out`. -/
theorem timedRun.run_erase {S U β : Type} (tV tOut : ℕ) (O : S → G.Query → PMF (G.Answer × S))
    (t : G.Query → ℕ) (s₀ : S) (out : G.Forgery × S → β) (x : G.Stmt)
    (A' : OracleAdv.Timed G.Query G.Answer G.Forgery) (O' : U → Empty → PMF (Empty × U))
    (u : U) :
    (OracleAdv.run O' (timedRun tV tOut O t s₀ out x A').2.erase u).map Prod.fst =
      (OracleAdv.run O (withVerify x A'.erase) s₀).map out := by
  rw [← withVerify.erase_timed tV, ← OracleAdv.Timed.run_erase_runOracle O t O' _ s₀ u,
    timedRun, OracleAdv.Timed.erase_stepBind, OracleAdv.run_bind, PMF.map_bind, PMF.map_comp]
  simp only [OracleAdv.Timed.delay, OracleAdv.Timed.erase, OracleAdv.run_ret, PMF.pure_map]
  rw [PMF.map]
  rfl

/-- **Time of the costed verified run.** With `A'` of time `T` and at most `qH` hash and
`qS` signing queries, and a step cost of at most `tH` per hash and `tS` per signing call,
the costed run has time at most
`T + (tV + V * (tV + 1)) + ((tH + 1) * (qH + V) + (tS + 1) * qS) + tOut`. -/
theorem timedRun.timeBound {S β : Type} (tV tOut : ℕ) (O : S → G.Query → PMF (G.Answer × S))
    (t : G.Query → ℕ) (s₀ : S) (out : G.Forgery × S → β) (x : G.Stmt) {tH tS : ℕ}
    (ht : ∀ d, t d ≤ Sum.elim (fun _ => tH) (fun _ => tS) d)
    {A' : OracleAdv.Timed G.Query G.Answer G.Forgery} {T qH qS : ℕ} (hT : A'.TimeBound T)
    (hq : IsQueryBound₂ A'.erase qH qS) :
    OracleAdv.Timed.StepTimeBound (timedRun tV tOut O t s₀ out x A')
      (T + (tV + G.V * (tV + 1)) + ((tH + 1) * (qH + G.V) + (tS + 1) * qS) + tOut) := by
  have hw := withVerify.timeBound_timed tV x hT
  have hqw := isQueryBoundBy_withVerify_succ x t ht hq
  rw [← withVerify.erase_timed tV] at hqw
  have hr := OracleAdv.Timed.timeBound_runOracle (D' := Empty) (R' := Empty) O t hw.2 hqw s₀
  have hd := OracleAdv.Timed.stepTimeBound_delay (c := (withVerify.timed tV x A').1) hr
  have hb := OracleAdv.Timed.timeBound_stepBind (n := tOut) hd
    (f := fun y => (tOut, (OracleAdv.Timed.ret (out y) : OracleAdv.Timed Empty Empty β)))
    fun _ => ⟨le_rfl, trivial⟩
  exact hb.mono (by have := hw.1; omega)

end Run

/-! ## The straight-line reductions -/

section StraightLine

variable {G : Protocol} {rel : G.Stmt → G.Wit → Prop} {N : ℕ} {κ : G.Classes}
  {M : Markers κ} {ε : κ.ι → ℝ≥0∞} {εS : ℝ≥0∞}

/-- The step cost of the instrumented marker game: `tH` per hash query and `tMk` more at
a designated point, `tS` per signing query. -/
def slCostTimedMk (M : Markers κ) (tH tMk tS : ℕ) : G.Query → ℕ :=
  Sum.elim (fun k => tH + bif M.des k then tMk else 0) fun _ => tS

/-- The costed marker straight-line reduction on the statement `x`. -/
noncomputable def slReductionMk.timed (E : G.LogExtractorMk rel N κ M ε εS)
    (tV tH tMk tS tOut : ℕ) (A' : G.Stmt → OracleAdv.Timed G.Query G.Answer G.Forgery)
    (x : G.Stmt) : ℕ × OracleAdv.Timed Empty Empty G.Wit :=
  timedRun tV tOut (toOracle (slStepMk N M E.Bad x)) (slCostTimedMk M tH tMk tS)
    ((Protocol.Tables.empty, false), false) (fun y => E.ext x y.2.1.1 y.1) x (A' x)

/-- Under any oracle, the costed marker reduction has the output distribution of
`slReductionMk E A`. -/
theorem slReductionMk.run_erase_timed (E : G.LogExtractorMk rel N κ M ε εS) {qH qS : ℕ}
    (A : G.Adversary qH qS) (A' : G.Stmt → OracleAdv.Timed G.Query G.Answer G.Forgery)
    (hA : ∀ x, (A' x).erase = A.run x) (tV tH tMk tS tOut : ℕ) {U : Type}
    (O' : U → Empty → PMF (Empty × U)) (u : U) (x : G.Stmt) :
    (OracleAdv.run O' (slReductionMk.timed E tV tH tMk tS tOut A' x).2.erase u).map
      Prod.fst = slReductionMk E A x := by
  rw [slReductionMk.timed, timedRun.run_erase, hA]
  rfl

/-- **Time of the marker straight-line reduction.** With `A'` of time `T`, the costed
reduction has time at most
`T + (tV + V * (tV + 1)) + ((tH + tMk + 1) * (qH + V) + (tS + 1) * qS) + tOut`. -/
theorem slReductionMk.timeBound_timed (E : G.LogExtractorMk rel N κ M ε εS) {qH qS : ℕ}
    (A : G.Adversary qH qS) {A' : G.Stmt → OracleAdv.Timed G.Query G.Answer G.Forgery}
    (hA : ∀ x, (A' x).erase = A.run x) (tV tH tMk tS tOut : ℕ) {T : ℕ}
    (hT : ∀ x, (A' x).TimeBound T) (x : G.Stmt) :
    OracleAdv.Timed.StepTimeBound (slReductionMk.timed E tV tH tMk tS tOut A' x)
      (T + (tV + G.V * (tV + 1)) + ((tH + tMk + 1) * (qH + G.V) + (tS + 1) * qS) + tOut) :=
  timedRun.timeBound tV tOut _ _ _ _ x
    (fun d => by
      cases d with
      | inl k => cases h : M.des k <;> simp [slCostTimedMk, h]
      | inr m => exact le_rfl)
    (hT x) (by rw [hA]; exact A.isQueryBound x)

/-- The costed class-wise straight-line reduction on the statement `x`. -/
noncomputable def slReductionCls.timed (E : G.LogExtractorCls rel N κ ε εS)
    (tV tH tS tOut : ℕ) (A' : G.Stmt → OracleAdv.Timed G.Query G.Answer G.Forgery)
    (x : G.Stmt) : ℕ × OracleAdv.Timed Empty Empty G.Wit :=
  timedRun tV tOut (toOracle (slStep N E.Bad x)) (Sum.elim (fun _ => tH) fun _ => tS)
    ((Protocol.Tables.empty, false), false) (fun y => E.ext x y.2.1.1 y.1) x (A' x)

/-- Under any oracle, the costed class-wise reduction has the output distribution of
`slReductionCls E A`. -/
theorem slReductionCls.run_erase_timed (E : G.LogExtractorCls rel N κ ε εS) {qH qS : ℕ}
    (A : G.Adversary qH qS) (A' : G.Stmt → OracleAdv.Timed G.Query G.Answer G.Forgery)
    (hA : ∀ x, (A' x).erase = A.run x) (tV tH tS tOut : ℕ) {U : Type}
    (O' : U → Empty → PMF (Empty × U)) (u : U) (x : G.Stmt) :
    (OracleAdv.run O' (slReductionCls.timed E tV tH tS tOut A' x).2.erase u).map
      Prod.fst = slReductionCls E A x := by
  rw [slReductionCls.timed, timedRun.run_erase, hA]
  rfl

/-- **Time of the class-wise straight-line reduction.** With `A'` of time `T`, the
costed reduction has time at most
`T + (tV + V * (tV + 1)) + ((tH + 1) * (qH + V) + (tS + 1) * qS) + tOut`. -/
theorem slReductionCls.timeBound_timed (E : G.LogExtractorCls rel N κ ε εS) {qH qS : ℕ}
    (A : G.Adversary qH qS) {A' : G.Stmt → OracleAdv.Timed G.Query G.Answer G.Forgery}
    (hA : ∀ x, (A' x).erase = A.run x) (tV tH tS tOut : ℕ) {T : ℕ}
    (hT : ∀ x, (A' x).TimeBound T) (x : G.Stmt) :
    OracleAdv.Timed.StepTimeBound (slReductionCls.timed E tV tH tS tOut A' x)
      (T + (tV + G.V * (tV + 1)) + ((tH + 1) * (qH + G.V) + (tS + 1) * qS) + tOut) :=
  timedRun.timeBound tV tOut _ _ _ _ x (fun _ => le_rfl) (hT x)
    (by rw [hA]; exact A.isQueryBound x)

/-- The costed straight-line reduction on the statement `x`. -/
noncomputable def slReduction.timed {ε : ℝ≥0∞} (E : G.LogExtractor rel N ε)
    (tV tH tS tOut : ℕ) (A' : G.Stmt → OracleAdv.Timed G.Query G.Answer G.Forgery)
    (x : G.Stmt) : ℕ × OracleAdv.Timed Empty Empty G.Wit :=
  timedRun tV tOut (toOracle (slStep N E.Bad x)) (Sum.elim (fun _ => tH) fun _ => tS)
    ((Protocol.Tables.empty, false), false) (fun y => E.ext x y.2.1.1 y.1) x (A' x)

/-- Under any oracle, the costed straight-line reduction has the output distribution of
`slReduction E A`. -/
theorem slReduction.run_erase_timed {ε : ℝ≥0∞} (E : G.LogExtractor rel N ε) {qH qS : ℕ}
    (A : G.Adversary qH qS) (A' : G.Stmt → OracleAdv.Timed G.Query G.Answer G.Forgery)
    (hA : ∀ x, (A' x).erase = A.run x) (tV tH tS tOut : ℕ) {U : Type}
    (O' : U → Empty → PMF (Empty × U)) (u : U) (x : G.Stmt) :
    (OracleAdv.run O' (slReduction.timed E tV tH tS tOut A' x).2.erase u).map
      Prod.fst = slReduction E A x := by
  rw [slReduction.timed, timedRun.run_erase, hA]
  rfl

/-- **Time of the straight-line reduction.** With `A'` of time `T`, the costed reduction
has time at most
`T + (tV + V * (tV + 1)) + ((tH + 1) * (qH + V) + (tS + 1) * qS) + tOut`. -/
theorem slReduction.timeBound_timed {ε : ℝ≥0∞} (E : G.LogExtractor rel N ε) {qH qS : ℕ}
    (A : G.Adversary qH qS) {A' : G.Stmt → OracleAdv.Timed G.Query G.Answer G.Forgery}
    (hA : ∀ x, (A' x).erase = A.run x) (tV tH tS tOut : ℕ) {T : ℕ}
    (hT : ∀ x, (A' x).TimeBound T) (x : G.Stmt) :
    OracleAdv.Timed.StepTimeBound (slReduction.timed E tV tH tS tOut A' x)
      (T + (tV + G.V * (tV + 1)) + ((tH + 1) * (qH + G.V) + (tS + 1) * qS) + tOut) :=
  timedRun.timeBound tV tOut _ _ _ _ x (fun _ => le_rfl) (hT x)
    (by rw [hA]; exact A.isQueryBound x)

end StraightLine

/-! ## The key-recovery reduction -/

section Recovery

variable {G : Protocol} {κ : G.Classes} {rel : G.Stmt → G.Wit → Prop}

/-- The costed key-recovery reduction on the statement `x`. -/
noncomputable def recReduction.timed (ρ : G.Recovery κ rel) (dflt : G.Stmt → G.Wit)
    (tV tH tS tOut : ℕ) (A' : G.Stmt → OracleAdv.Timed G.Query G.Answer G.Forgery)
    (x : G.Stmt) : ℕ × OracleAdv.Timed Empty Empty G.Wit :=
  timedRun tV tOut (toOracle (simStep x)) (Sum.elim (fun _ => tH) fun _ => tS)
    (Protocol.Tables.empty, false)
    (fun y => (ρ.recover x (y.2.1.prog ++ y.2.1.hash)).getD (dflt x)) x (A' x)

/-- Under any oracle, the costed key-recovery reduction has the output distribution of
`recReduction ρ dflt A`. -/
theorem recReduction.run_erase_timed (ρ : G.Recovery κ rel) (dflt : G.Stmt → G.Wit)
    {qH qS : ℕ} (A : G.Adversary qH qS)
    (A' : G.Stmt → OracleAdv.Timed G.Query G.Answer G.Forgery)
    (hA : ∀ x, (A' x).erase = A.run x) (tV tH tS tOut : ℕ) {U : Type}
    (O' : U → Empty → PMF (Empty × U)) (u : U) (x : G.Stmt) :
    (OracleAdv.run O' (recReduction.timed ρ dflt tV tH tS tOut A' x).2.erase u).map
      Prod.fst = recReduction ρ dflt A x := by
  rw [recReduction.timed, timedRun.run_erase, hA]
  rfl

/-- **Time of the key-recovery reduction.** With `A'` of time `T`, the costed reduction
has time at most
`T + (tV + V * (tV + 1)) + ((tH + 1) * (qH + V) + (tS + 1) * qS) + tOut`. -/
theorem recReduction.timeBound_timed (ρ : G.Recovery κ rel) (dflt : G.Stmt → G.Wit)
    {qH qS : ℕ} (A : G.Adversary qH qS)
    {A' : G.Stmt → OracleAdv.Timed G.Query G.Answer G.Forgery}
    (hA : ∀ x, (A' x).erase = A.run x) (tV tH tS tOut : ℕ) {T : ℕ}
    (hT : ∀ x, (A' x).TimeBound T) (x : G.Stmt) :
    OracleAdv.Timed.StepTimeBound (recReduction.timed ρ dflt tV tH tS tOut A' x)
      (T + (tV + G.V * (tV + 1)) + ((tH + 1) * (qH + G.V) + (tS + 1) * qS) + tOut) :=
  timedRun.timeBound tV tOut _ _ _ _ x (fun _ => le_rfl) (hT x)
    (by rw [hA]; exact A.isQueryBound x)

end Recovery

/-! ## The hybrid distinguisher -/

section Hybrid

variable {G : Protocol}

/-- The costed form of `hybRunOf sgn D D' k xw f`: a hash query is one `rand` node over
the real hash step at step cost `tH`, a signing query other than the `k`-th one is one
`rand` node over the signing step at step cost `tS`, the `k`-th signing query is
forwarded to the challenge oracle, and the output map `f` costs `tOut`. -/
noncomputable def hybRunOf.timed (sgn : G.SignStep) (D D' : G.Sampler) (k : ℕ)
    (xw : G.Stmt × G.Wit) {α β : Type} (f : α × (G.Tables × Bool) → β) (tH tS tOut : ℕ) :
    ℕ → OracleAdv.Timed G.Query G.Answer α → G.Tables × Bool →
      ℕ × OracleAdv.Timed (G.Msg × (G.Tables × Bool)) (G.Answer × (G.Tables × Bool)) β
  | _, .ret a, s => (tOut, .ret (f (a, s)))
  | j, .rand p c κ, s =>
    (0, .rand p (fun b => c b + (hybRunOf.timed sgn D D' k xw f tH tS tOut j (κ b) s).1)
      fun b => (hybRunOf.timed sgn D D' k xw f tH tS tOut j (κ b) s).2)
  | j, .query (.inl key) c κ, s =>
    (0, .rand (toOracle (realStep xw) s (.inl key))
      (fun o => tH + c o.1 + (hybRunOf.timed sgn D D' k xw f tH tS tOut j (κ o.1) o.2).1)
      fun o => (hybRunOf.timed sgn D D' k xw f tH tS tOut j (κ o.1) o.2).2)
  | j, .query (.inr m) c κ, s =>
    if j = k then
      (0, .query (m, s)
        (fun o => c o.1 + (hybRunOf.timed sgn D D' k xw f tH tS tOut (j + 1) (κ o.1) o.2).1)
        fun o => (hybRunOf.timed sgn D D' k xw f tH tS tOut (j + 1) (κ o.1) o.2).2)
    else
      (0, .rand (sgn (if j < k then D' else D) xw s m)
        (fun o => tS + c o.1 + (hybRunOf.timed sgn D D' k xw f tH tS tOut (j + 1) (κ o.1) o.2).1)
        fun o => (hybRunOf.timed sgn D D' k xw f tH tS tOut (j + 1) (κ o.1) o.2).2)

theorem hybRunOf.erase_timed (sgn : G.SignStep) (D D' : G.Sampler) (k : ℕ)
    (xw : G.Stmt × G.Wit) {α β : Type} (f : α × (G.Tables × Bool) → β) (tH tS tOut : ℕ)
    (j : ℕ) (A : OracleAdv.Timed G.Query G.Answer α) (s : G.Tables × Bool) :
    (hybRunOf.timed sgn D D' k xw f tH tS tOut j A s).2.erase =
      hybRunOf sgn D D' k xw f j A.erase s := by
  induction A generalizing j s with
  | ret a => rfl
  | rand p c κ ih => simp only [hybRunOf.timed, hybRunOf, OracleAdv.Timed.erase, ih]
  | query d c κ ih =>
    cases d with
    | inl key => simp only [hybRunOf.timed, hybRunOf, OracleAdv.Timed.erase, ih]
    | inr m =>
      by_cases hj : j = k
      · simp only [hybRunOf.timed, hybRunOf, hj, if_true, OracleAdv.Timed.erase, ih]
      · simp only [hybRunOf.timed, hybRunOf, hj, if_false, OracleAdv.Timed.erase, ih]

/-- **Time of the costed hybrid run.** With `A` of time `T` whose query costs, `tH + 1`
per hash and `tS + 1` per signing query, sum to at most `n`, the costed run has time at
most `T + n + tOut`. -/
theorem hybRunOf.timeBound_timed (sgn : G.SignStep) (D D' : G.Sampler) (k : ℕ)
    (xw : G.Stmt × G.Wit) {α β : Type} (f : α × (G.Tables × Bool) → β) (tH tS tOut : ℕ)
    {A : OracleAdv.Timed G.Query G.Answer α} {T n : ℕ} (hA : A.TimeBound T)
    (hq : A.erase.IsQueryBoundBy (Sum.elim (fun _ => tH + 1) fun _ => tS + 1) n)
    (j : ℕ) (s : G.Tables × Bool) :
    OracleAdv.Timed.StepTimeBound (hybRunOf.timed sgn D D' k xw f tH tS tOut j A s)
      (T + n + tOut) := by
  induction A generalizing T n j s with
  | ret a =>
    simp only [hybRunOf.timed]
    exact ⟨by omega, trivial⟩
  | rand p c κ ih =>
    have h1 := hA.1
    simp only [hybRunOf.timed, OracleAdv.Timed.stepTimeBound_zero,
      OracleAdv.Timed.timeBound_rand_iff]
    refine ⟨by omega, fun b => ?_⟩
    have h2 := (hA.2 b).1
    exact (OracleAdv.Timed.stepTimeBound_delay (c := c b) (ih b (hA.2 b).2 (hq b) j s)).mono
      (by omega)
  | query d c κ ih =>
    obtain ⟨hd, hk⟩ := hq
    have h1 := hA.1
    cases d with
    | inl key =>
      simp only [Sum.elim_inl] at hd hk
      simp only [hybRunOf.timed, OracleAdv.Timed.stepTimeBound_zero,
        OracleAdv.Timed.timeBound_rand_iff]
      refine ⟨by omega, fun o => ?_⟩
      have h2 := (hA.2 o.1).1
      exact (OracleAdv.Timed.stepTimeBound_delay (c := tH + c o.1)
        (ih o.1 (hA.2 o.1).2 (hk o.1) j o.2)).mono (by omega)
    | inr m =>
      simp only [Sum.elim_inr] at hd hk
      by_cases hj : j = k
      · simp only [hybRunOf.timed, hj, if_true, OracleAdv.Timed.stepTimeBound_zero,
          OracleAdv.Timed.timeBound_query_iff]
        refine ⟨by omega, fun o => ?_⟩
        have h2 := (hA.2 o.1).1
        exact (OracleAdv.Timed.stepTimeBound_delay (c := c o.1)
          (ih o.1 (hA.2 o.1).2 (hk o.1) (k + 1) o.2)).mono (by omega)
      · simp only [hybRunOf.timed, hj, if_false, OracleAdv.Timed.stepTimeBound_zero,
          OracleAdv.Timed.timeBound_rand_iff]
        refine ⟨by omega, fun o => ?_⟩
        have h2 := (hA.2 o.1).1
        exact (OracleAdv.Timed.stepTimeBound_delay (c := tS + c o.1)
          (ih o.1 (hA.2 o.1).2 (hk o.1) (j + 1) o.2)).mono (by omega)

/-- The costed `k`-th hybrid distinguisher of the signing step `sgn`: the costed
adversary `A' xw.1` with the verifier's queries, run by `hybRunOf.timed`. -/
noncomputable def hybDistByOf.timed (sgn : G.SignStep)
    (P : G.Stmt → G.Forgery × (G.Tables × Bool) → Bool) (D D' : G.Sampler) (k : ℕ)
    (tV tH tS tOut : ℕ) (A' : G.Stmt → OracleAdv.Timed G.Query G.Answer G.Forgery)
    (xw : G.Stmt × G.Wit) :
    ℕ × OracleAdv.Timed (G.Msg × (G.Tables × Bool)) (G.Answer × (G.Tables × Bool)) Bool :=
  OracleAdv.Timed.delay (withVerify.timed tV xw.1 (A' xw.1)).1
    (hybRunOf.timed sgn D D' k xw (P xw.1) tH tS tOut 0 (withVerify.timed tV xw.1 (A' xw.1)).2
      (Protocol.Tables.empty, false))

theorem hybDistByOf.erase_timed (sgn : G.SignStep)
    (P : G.Stmt → G.Forgery × (G.Tables × Bool) → Bool) (D D' : G.Sampler) (k : ℕ)
    {qH qS : ℕ} (A : G.Adversary qH qS)
    (A' : G.Stmt → OracleAdv.Timed G.Query G.Answer G.Forgery)
    (hA : ∀ x, (A' x).erase = A.run x) (tV tH tS tOut : ℕ) (xw : G.Stmt × G.Wit) :
    (hybDistByOf.timed sgn P D D' k tV tH tS tOut A' xw).2.erase =
      hybDistByOf sgn P D D' k A xw := by
  rw [hybDistByOf.timed, OracleAdv.Timed.delay, hybRunOf.erase_timed, withVerify.erase_timed,
    hA]
  rfl

theorem hybDistByOf.timeBound_timed (sgn : G.SignStep)
    (P : G.Stmt → G.Forgery × (G.Tables × Bool) → Bool) (D D' : G.Sampler) (k : ℕ)
    {qH qS : ℕ} (A : G.Adversary qH qS)
    {A' : G.Stmt → OracleAdv.Timed G.Query G.Answer G.Forgery}
    (hA : ∀ x, (A' x).erase = A.run x) (tV tH tS tOut : ℕ) {T : ℕ}
    (hT : ∀ x, (A' x).TimeBound T) (xw : G.Stmt × G.Wit) :
    OracleAdv.Timed.StepTimeBound (hybDistByOf.timed sgn P D D' k tV tH tS tOut A' xw)
      (T + (tV + G.V * (tV + 1)) + ((tH + 1) * (qH + G.V) + (tS + 1) * qS) + tOut) := by
  have hw := withVerify.timeBound_timed tV xw.1 (hT xw.1)
  have hq := isQueryBoundBy_withVerify_succ xw.1 (Sum.elim (fun _ => tH) fun _ => tS)
    (fun _ => le_rfl) (A := (A' xw.1).erase) (by rw [hA]; exact A.isQueryBound xw.1)
  rw [← withVerify.erase_timed tV] at hq
  have hr := hybRunOf.timeBound_timed sgn D D' k xw (P xw.1) tH tS tOut hw.2
    (hq.of_cost_le fun d => by cases d <;> rfl) 0 (Protocol.Tables.empty, false)
  have hd := OracleAdv.Timed.stepTimeBound_delay
    (c := (withVerify.timed tV xw.1 (A' xw.1)).1) hr
  exact hd.mono (by have := hw.1; omega)

/-- The costed `k`-th hybrid distinguisher with the programmed flag. -/
noncomputable def hybDistByP.timed (P : G.Stmt → G.Forgery × (G.Tables × Bool) → Bool)
    (D D' : G.Sampler) (k : ℕ) (tV tH tS tOut : ℕ)
    (A' : G.Stmt → OracleAdv.Timed G.Query G.Answer G.Forgery) (xw : G.Stmt × G.Wit) :
    ℕ × OracleAdv.Timed (G.Msg × (G.Tables × Bool)) (G.Answer × (G.Tables × Bool)) Bool :=
  hybDistByOf.timed attSignP P D D' k tV tH tS tOut A' xw

/-- Erasing the step costs of the costed hybrid distinguisher with the programmed flag
gives `hybDistByP P D D' k A`. -/
theorem hybDistByP.erase_timed (P : G.Stmt → G.Forgery × (G.Tables × Bool) → Bool)
    (D D' : G.Sampler) (k : ℕ) {qH qS : ℕ} (A : G.Adversary qH qS)
    (A' : G.Stmt → OracleAdv.Timed G.Query G.Answer G.Forgery)
    (hA : ∀ x, (A' x).erase = A.run x) (tV tH tS tOut : ℕ) (xw : G.Stmt × G.Wit) :
    (hybDistByP.timed P D D' k tV tH tS tOut A' xw).2.erase = hybDistByP P D D' k A xw :=
  hybDistByOf.erase_timed attSignP P D D' k A A' hA tV tH tS tOut xw

/-- **Time of the hybrid distinguisher with the programmed flag.** With `A'` of time
`T`, the costed distinguisher has time at most
`T + (tV + V * (tV + 1)) + ((tH + 1) * (qH + V) + (tS + 1) * qS) + tOut`. -/
theorem hybDistByP.timeBound_timed (P : G.Stmt → G.Forgery × (G.Tables × Bool) → Bool)
    (D D' : G.Sampler) (k : ℕ) {qH qS : ℕ} (A : G.Adversary qH qS)
    {A' : G.Stmt → OracleAdv.Timed G.Query G.Answer G.Forgery}
    (hA : ∀ x, (A' x).erase = A.run x) (tV tH tS tOut : ℕ) {T : ℕ}
    (hT : ∀ x, (A' x).TimeBound T) (xw : G.Stmt × G.Wit) :
    OracleAdv.Timed.StepTimeBound (hybDistByP.timed P D D' k tV tH tS tOut A' xw)
      (T + (tV + G.V * (tV + 1)) + ((tH + 1) * (qH + G.V) + (tS + 1) * qS) + tOut) :=
  hybDistByOf.timeBound_timed attSignP P D D' k A hA tV tH tS tOut hT xw

end Hybrid

/-! ## The rewinding reduction -/

section Rewinding

variable {P : Sigma} {M : Type} [DecidableEq M]

/-- The costed relation reduction on the statement `x`: the costed adversary `A' x` with
the verifier's queries, run as the costed forking run (`OracleForking.forkRun.timedK`)
against the simulated oracle with step cost `tH` per hash and `tS` per signing call and
fork decision cost `tF`, followed by the extractor at cost `tExt`. -/
noncomputable def extractReduction.timed (tV tH tS tF tExt : ℕ)
    (A' : P.Stmt → OracleAdv.Timed (Query P M) (Answer P) (Forgery P M)) (x : P.Stmt) :
    ℕ × OracleAdv.Timed Empty Empty P.Wit :=
  OracleAdv.Timed.delay (withVerify.timed tV x (A' x)).1
    (forkRun.timedK (simStep (G := P.toProtocol M) x) hashCount (hitAt x)
      (Sum.elim (fun _ => tH) fun _ => tS) tF (withVerify.timed tV x (A' x)).2
      (Protocol.Tables.empty, false) fun r => (tExt, .ret (extractW x r)))

/-- Under any oracle, the costed relation reduction has the output distribution of
`extractReduction A`. -/
theorem extractReduction.run_erase_timed {qH qS : ℕ} (A : Adversary P M qH qS)
    (A' : P.Stmt → OracleAdv.Timed (Query P M) (Answer P) (Forgery P M))
    (hA : ∀ x, (A' x).erase = A.run x) (tV tH tS tF tExt : ℕ) {U : Type}
    (O' : U → Empty → PMF (Empty × U)) (u : U) (x : P.Stmt) :
    (OracleAdv.run O' (extractReduction.timed tV tH tS tF tExt A' x).2.erase u).map
      Prod.fst = extractReduction A x := by
  rw [extractReduction.timed, OracleAdv.Timed.delay,
    forkRun.run_erase_timedK _ _ _ _ _ (simStep_plain x) (simStep_hashCount_fresh x)
      (hitAt_disj x), withVerify.erase_timed, hA]
  simp only [OracleAdv.Timed.erase, OracleAdv.run_ret, PMF.pure_map]
  rfl

/-- **Time of the rewinding reduction.** With `A'` of time `T`, at most `qH` hash and
`qS` signing queries and `V` verifier points, the costed relation reduction has time at
most `2 * (T + (tV + V * (tV + 1)) + ((tH + tF + 1) * (qH + V) + (tS + 1) * qS)) + tExt`:
the adversary with the verifier's queries is run at most twice, each hash query is charged
its step, its node and the fork decision, each signing query its step and its node, and
the extractor is called once. -/
theorem extractReduction.timeBound_timed {qH qS : ℕ} (A : Adversary P M qH qS)
    {A' : P.Stmt → OracleAdv.Timed (Query P M) (Answer P) (Forgery P M)}
    (hA : ∀ x, (A' x).erase = A.run x) (tV tH tS tF tExt : ℕ) {T : ℕ}
    (hT : ∀ x, (A' x).TimeBound T) (x : P.Stmt) :
    OracleAdv.Timed.StepTimeBound (extractReduction.timed tV tH tS tF tExt A' x)
      (2 * (T + (tV + (P.toProtocol M).V * (tV + 1)) +
        ((tH + tF + 1) * (qH + (P.toProtocol M).V) + (tS + 1) * qS)) + tExt) := by
  have hw := withVerify.timeBound_timed tV x (hT x)
  have hq := isQueryBoundBy_withVerify_succ x (Sum.elim (fun _ => tH + tF) fun _ => tS)
    (fun _ => le_rfl) (A := (A' x).erase) (by rw [hA]; exact A.isQueryBound x)
  rw [← withVerify.erase_timed tV] at hq
  have hr := forkRun.timeBound_timedK (simStep (G := P.toProtocol M) x) hashCount (hitAt x)
    (Sum.elim (fun _ => tH) fun _ => tS) tF _
    (fun d => by cases d <;> simp)
    (fun s d f h => by
      cases d with
      | inl k => simp
      | inr m => simp [simStep] at h)
    _ _ hw.2 hq le_rfl (Protocol.Tables.empty, false)
    (fun r => (tExt, .ret (extractW x r))) tExt fun _ => ⟨by omega, trivial⟩
  exact (OracleAdv.Timed.stepTimeBound_delay (c := (withVerify.timed tV x (A' x)).1) hr).mono
    (by have := hw.1; omega)

end Rewinding

/-! ## Costed reductions over the empty interface -/

section Costed

/-- **A costed inverter.** `B'` is a costed form of the inverter `B` of time `n`: under any
oracle, the erased costed tree on `x` has the output distribution `B x`, and the step cost
followed by the tree has time at most `n` on every `x`. -/
def TimedInverter {X W : Type} (B' : X → ℕ × OracleAdv.Timed Empty Empty W) (B : X → PMF W)
    (n : ℕ) : Prop :=
  (∀ x {U : Type} (O' : U → Empty → PMF (Empty × U)) (u : U),
      (OracleAdv.run O' (B' x).2.erase u).map Prod.fst = B x) ∧
    ∀ x, OracleAdv.Timed.StepTimeBound (B' x) n

/-- A costed form whose erasure is the oracle tree `A x`, where the run of `A x` has the
output distribution `B x`, is a costed inverter for `B`. -/
theorem TimedInverter.of_erase {X W : Type} {B' : X → ℕ × OracleAdv.Timed Empty Empty W}
    {A : X → OracleAdv Empty Empty W} {B : X → PMF W} {n : ℕ}
    (he : ∀ x, (B' x).2.erase = A x)
    (hA : ∀ x, (OracleAdv.run (fun (_ : Unit) (d : Empty) => d.elim) (A x) ()).map Prod.fst =
      B x)
    (ht : ∀ x, OracleAdv.Timed.StepTimeBound (B' x) n) : TimedInverter B' B n :=
  ⟨fun x _ O' u => by rw [he, OracleAdv.run_map_fst_empty_eq O' _ (A x) u (), hA], ht⟩

/-- **A costed two-stage reduction.** The costed first stage `choose'` and second stage
`guess'` are costed forms of the two stages `choose` and `guess` of a tweak-adaptive
reduction, of time `n`: the erased first stage, with the time budget dropped from its
state and lifted by `Signatures.liftPMF`, is `choose`; the erased second stage on a state
and a challenge, lifted, is `guess` on the state without the budget and the challenge; the
first stage followed by the second on any challenge `f z` has time at most `n`. -/
def TimedTwoStage {Tw St Ch : Type} (choose' : ℕ × OracleAdv.Timed Empty Empty (Tw × (St × ℕ)))
    (guess' : St × ℕ → Ch → ℕ × OracleAdv.Timed Empty Empty Bool)
    (choose : SPComp (Tw × St)) (guess : St → Ch → SPComp Bool) (n : ℕ) : Prop :=
  (∀ {U : Type} (O' : U → Empty → PMF (Empty × U)) (u : U),
      Signatures.liftPMF ((OracleAdv.run O' choose'.2.erase u).map
        fun z => (z.1.1, z.1.2.1)) = choose) ∧
    (∀ s c {U : Type} (O' : U → Empty → PMF (Empty × U)) (u : U),
      Signatures.liftPMF ((OracleAdv.run O' (guess' s c).2.erase u).map Prod.fst) =
        guess s.1 c) ∧
    ∀ f : Tw × (St × ℕ) → Ch,
      OracleAdv.Timed.StepTimeBound (OracleAdv.Timed.stepBind choose' fun z => guess' z.2 (f z))
        n

/-- Costed stages whose erasures are the oracle trees `C` and `G s c`, where the lifted
runs of `C` (budget dropped) and of `G s c` are `choose` and `guess s.1 c`, form a costed
two-stage reduction for `choose` and `guess`. -/
theorem TimedTwoStage.of_erase {Tw St Ch : Type}
    {choose' : ℕ × OracleAdv.Timed Empty Empty (Tw × (St × ℕ))}
    {guess' : St × ℕ → Ch → ℕ × OracleAdv.Timed Empty Empty Bool}
    {C : OracleAdv Empty Empty (Tw × (St × ℕ))} {G : St × ℕ → Ch → OracleAdv Empty Empty Bool}
    {choose : SPComp (Tw × St)} {guess : St → Ch → SPComp Bool} {n : ℕ}
    (hCe : choose'.2.erase = C) (hGe : ∀ s c, (guess' s c).2.erase = G s c)
    (hC : Signatures.liftPMF
      (((OracleAdv.run (fun (_ : Unit) (d : Empty) => d.elim) C ()).map Prod.fst).map
        fun z => (z.1, z.2.1)) = choose)
    (hG : ∀ s c, Signatures.liftPMF
      ((OracleAdv.run (fun (_ : Unit) (d : Empty) => d.elim) (G s c) ()).map Prod.fst) =
        guess s.1 c)
    (ht : ∀ f : Tw × (St × ℕ) → Ch,
      OracleAdv.Timed.StepTimeBound (OracleAdv.Timed.stepBind choose' fun z => guess' z.2 (f z))
        n) :
    TimedTwoStage choose' guess' choose guess n := by
  refine ⟨fun O' u => ?_, fun s c _ O' u => ?_, ht⟩
  · rw [← hC, hCe, ← OracleAdv.run_map_fst_empty_eq O' _ C u (), PMF.map_comp]
    rfl
  · rw [← hG, hGe, OracleAdv.run_map_fst_empty_eq O' _ (G s c) u ()]

end Costed

end FiatShamirROM

end CatCrypt.Crypto
