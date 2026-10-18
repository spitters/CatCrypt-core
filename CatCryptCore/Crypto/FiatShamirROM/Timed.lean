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
  `ρ.recover` on the visible entries, or the predicate of the hybrid distinguisher.

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

## Main results

* `OracleAdv.Timed.timeBound_simulate_of_isQueryBoundBy` — simulation time with a cost
  per query: time at most `T + n` when the query costs of `A` sum to at most `n`
* `OracleAdv.Timed.run_erase_runOracle`, `OracleAdv.Timed.timeBound_runOracle`
* `withVerify_eq_bind` — the verifier's queries are a sequencing after the adversary
* `slReductionMk.run_erase_timed`, `slReductionMk.timeBound_timed` and the same pair for
  `slReductionCls`, `slReduction`, `recReduction`
* `hybDistByP.erase_timed`, `hybDistByP.timeBound_timed`
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

end FiatShamirROM

end CatCrypt.Crypto
