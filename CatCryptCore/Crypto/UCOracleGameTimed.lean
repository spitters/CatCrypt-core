/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCOracleGame
import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
public import CatCryptCore.Tactics.DeriveTimeBound.Basic
public import CatCryptCore.Tactics.AutoTime.Basic
public import CatCryptCore.Crypto.OracleAdversaryFree
public import CatCryptCore.Core.SPTreeTimedFree
public import CatCryptCore.Crypto.OracleAdversaryPotential
public import CatCryptCore.ForMathlib.ListLength
public import CatCryptCore.Tactics.StdCosts

/-!
# Running time of the environment reduction of an oracle protocol

`derive_reduction` builds the costed forms of `OProt.reduce`, the environment `Z` with its
distinguisher run against the program of an oracle protocol `P` as an oracle adversary, and of
`OProt.reduction`, `reduce` from the initial states of `Z` and `P`.

`Z.next z h` is a distribution over states and events, and a sample node of a costed adversary
branches on its whole type, so `OracleAdv.Timed.TimeBound` of `reduce.timed` needs a bound on the
costs at every state, reachable or not. An environment whose state grows and whose step reads the
state has no such bound. Its time is stated by `TimeBoundOn supportOutcome`, the time on the paths
through outcomes of positive probability, on which an invariant indexed by the round holds.

Search words: time certificate, graded time bound, reachable states, support of a sample,
activation count, environment reduction.

## Main definitions

* `OProt.reduce.timed`, `OProt.reduction.timed` — the costed reductions
* `OracleAdv.Timed.OutcomeFilter`, `anyOutcome`, `supportOutcome` — selections of the outcomes
  of the sample nodes
* `OracleAdv.Timed.TimeBoundOn`, `StepTimeBoundOn`, `AllRetOn` — time and leaves on the selected
  paths
* `OProt.EnvCostBound`, `OProt.ProtCostBound` — graded costs of an environment and of a protocol

## Main results

* `OProt.reduce.erase_timed`, `OProt.reduction.erase_timed` — their erasure theorems
* `OProt.reduce.timeBoundGraded_timed`, `OProt.reduction.timeBoundGraded_timed` — the time is a
  sum over the rounds of the graded bounds, on states of invariants of the environment and the
  protocol
* `OProt.reduce.timeBound_timed`, `OProt.reduction.timeBound_timed` — the graded time over every
  outcome at the constant invariant: time on every path, linear in the number of activations,
  over uniform bounds on the costs of the steps of the environment, the distinguisher, the
  protocol's steps and the time of its oracle programs
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OracleAdv.Timed

variable {D R α : Type}

/-- A selection of the outcomes of each probabilistic node of a costed adversary. -/
abbrev OutcomeFilter : Type 1 := ∀ β : Type, PMF β → β → Prop

/-- Every outcome of a sample. -/
def anyOutcome : OutcomeFilter := fun _ _ _ => True

/-- The outcomes of a sample of positive probability. -/
def supportOutcome : OutcomeFilter := fun _ p b => b ∈ p.support

/-- `A.TimeBoundOn F n`: `A` takes time at most `n` on every path through outcomes of `F` and
arbitrary oracle answers. -/
def TimeBoundOn (F : OutcomeFilter) : Timed D R α → ℕ → Prop
  | ret _, _ => True
  | rand p c k, n =>
    1 ≤ n ∧ ∀ b, F _ p b → c b ≤ n - 1 ∧ TimeBoundOn F (k b) (n - 1 - c b)
  | query _ c k, n => 1 ≤ n ∧ ∀ r, c r ≤ n - 1 ∧ TimeBoundOn F (k r) (n - 1 - c r)

/-- `StepTimeBoundOn F (c, A) T`: the step cost `c` followed by `A` takes time at most `T` on
every path through outcomes of `F`. -/
def StepTimeBoundOn (F : OutcomeFilter) (x : ℕ × Timed D R α) (n : ℕ) : Prop :=
  x.1 ≤ n ∧ x.2.TimeBoundOn F (n - x.1)

/-- `A.AllRetOn F P`: every leaf of `A` on a path through outcomes of `F` satisfies `P`. -/
def AllRetOn (F : OutcomeFilter) : Timed D R α → (α → Prop) → Prop
  | ret a, P => P a
  | rand p _ k, P => ∀ b, F _ p b → AllRetOn F (k b) P
  | query _ _ k, P => ∀ r, AllRetOn F (k r) P

/-- Unfolding of `TimeBoundOn` at a sample. -/
theorem timeBoundOn_rand_iff {F : OutcomeFilter} {γ : Type} (p : PMF γ) (c : γ → ℕ)
    (k : γ → Timed D R α) (n : ℕ) :
    (rand p c k).TimeBoundOn F n ↔ 1 ≤ n ∧ ∀ b, F _ p b → StepTimeBoundOn F (c b, k b) (n - 1) :=
  Iff.rfl

/-- Unfolding of `TimeBoundOn` at a query. -/
theorem timeBoundOn_query_iff {F : OutcomeFilter} (d : D) (c : R → ℕ) (k : R → Timed D R α)
    (n : ℕ) : (query d c k).TimeBoundOn F n ↔ 1 ≤ n ∧ ∀ r, StepTimeBoundOn F (c r, k r) (n - 1) :=
  Iff.rfl

/-- A zero step cost adds nothing to the time. -/
theorem stepTimeBoundOn_zero {F : OutcomeFilter} {A : Timed D R α} {n : ℕ} :
    StepTimeBoundOn F (0, A) n ↔ A.TimeBoundOn F n := by
  simp [StepTimeBoundOn]

/-- A time bound holds at every larger time. -/
theorem TimeBoundOn.mono {F : OutcomeFilter} {A : Timed D R α} {m n : ℕ}
    (h : A.TimeBoundOn F m) (hmn : m ≤ n) : A.TimeBoundOn F n := by
  induction A generalizing m n with
  | ret a => trivial
  | rand p c k ih =>
    exact ⟨h.1.trans hmn, fun b hb =>
      ⟨(h.2 b hb).1.trans (by omega), ih b (h.2 b hb).2 (by omega)⟩⟩
  | query d c k ih =>
    exact ⟨h.1.trans hmn, fun r => ⟨(h.2 r).1.trans (by omega), ih r (h.2 r).2 (by omega)⟩⟩

/-- A step time bound holds at every larger time. -/
theorem StepTimeBoundOn.mono {F : OutcomeFilter} {x : ℕ × Timed D R α} {m n : ℕ}
    (h : StepTimeBoundOn F x m) (hmn : m ≤ n) : StepTimeBoundOn F x n :=
  ⟨h.1.trans hmn, h.2.mono (Nat.sub_le_sub_right hmn _)⟩

/-- A delay by `c` adds `c` to a step time bound. -/
theorem stepTimeBoundOn_delay {F : OutcomeFilter} {c : ℕ} {x : ℕ × Timed D R α} {n : ℕ}
    (h : StepTimeBoundOn F x n) : StepTimeBoundOn F (delay c x) (c + n) := by
  refine ⟨Nat.add_le_add_left h.1 c, ?_⟩
  have e : c + n - (c + x.1) = n - x.1 := by omega
  simpa only [delay, e] using h.2

/-- A time bound on every path is a time bound on the paths through outcomes of `F`. -/
theorem TimeBound.timeBoundOn (F : OutcomeFilter) {A : Timed D R α} {n : ℕ}
    (h : A.TimeBound n) : A.TimeBoundOn F n := by
  induction A generalizing n with
  | ret a => trivial
  | rand p c k ih => exact ⟨h.1, fun b _ => ⟨(h.2 b).1, ih b (h.2 b).2⟩⟩
  | query d c k ih => exact ⟨h.1, fun r => ⟨(h.2 r).1, ih r (h.2 r).2⟩⟩

/-- A time bound over every outcome is a time bound. -/
theorem TimeBoundOn.timeBound_of_anyOutcome {A : Timed D R α} {n : ℕ}
    (h : A.TimeBoundOn anyOutcome n) : A.TimeBound n := by
  induction A generalizing n with
  | ret a => trivial
  | rand p c k ih =>
    exact ⟨h.1, fun b => ⟨(h.2 b trivial).1, ih b (h.2 b trivial).2⟩⟩
  | query d c k ih => exact ⟨h.1, fun r => ⟨(h.2 r).1, ih r (h.2 r).2⟩⟩

/-- A step time bound over every outcome is a step time bound. -/
theorem stepTimeBoundOn_anyOutcome {x : ℕ × Timed D R α} {n : ℕ} :
    StepTimeBoundOn anyOutcome x n ↔ StepTimeBound x n :=
  ⟨fun h => ⟨h.1, h.2.timeBound_of_anyOutcome⟩, fun h => ⟨h.1, h.2.timeBoundOn _⟩⟩

/-- A predicate holding of all values holds of the leaves of `A`. -/
theorem allRetOn_of_forall (F : OutcomeFilter) {P : α → Prop} (hP : ∀ a, P a)
    (A : Timed D R α) : A.AllRetOn F P := by
  induction A with
  | ret a => exact hP a
  | rand p c k ih => exact fun b _ => ih b
  | query d c k ih => exact fun r => ih r

/-- Times add under sequencing on the paths through outcomes of `F`, with the continuation bounded
on the leaves of those paths. -/
theorem timeBoundOn_bind {β : Type} {F : OutcomeFilter} {P : α → Prop} {A : Timed D R α}
    {f : α → ℕ × Timed D R β} {m n : ℕ} (hA : A.TimeBoundOn F m) (hP : A.AllRetOn F P)
    (hf : ∀ a, P a → StepTimeBoundOn F (f a) n) : StepTimeBoundOn F (A.bind f) (m + n) := by
  induction A generalizing m with
  | ret a => exact (hf a hP).mono (Nat.le_add_left n m)
  | rand p c k ih =>
    have h1 := hA.1
    simp only [bind, stepTimeBoundOn_zero, timeBoundOn_rand_iff]
    refine ⟨by omega, fun b hb => ?_⟩
    have h2 := (hA.2 b hb).1
    exact (stepTimeBoundOn_delay (c := c b) (ih b (hA.2 b hb).2 (hP b hb))).mono (by omega)
  | query d c k ih =>
    have h1 := hA.1
    simp only [bind, stepTimeBoundOn_zero, timeBoundOn_query_iff]
    refine ⟨by omega, fun r => ?_⟩
    have h2 := (hA.2 r).1
    exact (stepTimeBoundOn_delay (c := c r) (ih r (hA.2 r).2 (hP r))).mono (by omega)

end CatCrypt.Crypto.OracleAdv.Timed

namespace CatCrypt.Crypto.UCTransparent.OProt

open CatCrypt.Core OracleAdv.Timed

derive_reduction reduce
derive_reduction reduction

/-! ## Graded time on the reachable states -/

/-- The graded costs of an environment `Z` over the outcome filter `F` and the interface
predicates `Ev` and `Out`. From a state of `Inv i`, `next` costs at most `tN i` and its outcomes in
`F` have a state of `Mid i` and an event of `Ev i`; from a state of `Mid i` on an output of
`Out i`, `obs` costs at most `tO i` and its outcomes in `F` have a state of `Inv (i + 1)`; the
distinguisher on a state of `Inv i` costs at most `tD i`. The round `i` is the number of activations
made so far, and the predicates may bound the sizes of states, events and outputs in terms of it. -/
structure EnvCostBound {ζ E O : Type} (F : OutcomeFilter) (Z : Strat ζ E O)
    (distCost nextCost : ζ → ℕ) (obsCost : ζ → O → ℕ) (Inv Mid : ℕ → ζ → Prop)
    (Ev : ℕ → E → Prop) (Out : ℕ → O → Prop) (tD tN tO : ℕ → ℕ) : Prop where
  /-- The cost of the distinguisher at round `i`. -/
  dist_time : ∀ i z, Inv i z → distCost z ≤ tD i
  /-- The cost of `next` at round `i`. -/
  next_time : ∀ i z, Inv i z → nextCost z ≤ tN i
  /-- The outcomes of `next` at round `i`. -/
  next_ret : ∀ i z h z₁ e h₁, Inv i z → F _ (Z.next z h) (some ((z₁, e), h₁)) → Mid i z₁ ∧ Ev i e
  /-- The cost of `obs` at round `i`. -/
  obs_time : ∀ i z o, Mid i z → Out i o → obsCost z o ≤ tO i
  /-- The outcomes of `obs` at round `i`. -/
  obs_ret : ∀ i z o h z₂ h₂, Mid i z → Out i o → F _ (Z.obs z o h) (some (z₂, h₂)) → Inv (i + 1) z₂

/-- The graded costs of an oracle protocol `P` over the outcome filter `F` and the interface
predicates `Ev` and `Out`. From a state of `Inv i` on an event of `Ev i`, the step costs at most
`tC i`, its oracle program runs in time `tP i`, and that program returns states of `Inv (i + 1)`
and outputs of `Out i`. -/
structure ProtCostBound {τ E O Q A : Type} (F : OutcomeFilter) (P : OProt τ E O Q A)
    (stepCost : τ → E → ℕ) (Inv : ℕ → τ → Prop) (Ev : ℕ → E → Prop) (Out : ℕ → O → Prop)
    (tC tP : ℕ → ℕ) : Prop where
  /-- The cost of computing the step at round `i`. -/
  step_cost : ∀ i t e, Inv i t → Ev i e → stepCost t e ≤ tC i
  /-- The time of the oracle program at round `i`. -/
  step_time : ∀ i t e, Inv i t → Ev i e → (ofAdv (P.step t e)).TimeBoundOn F (tP i)
  /-- The results of the oracle program at round `i`. -/
  step_ret : ∀ i t e, Inv i t → Ev i e →
    (ofAdv (P.step t e)).AllRetOn F fun p => Inv (i + 1) p.1 ∧ Out i p.2

/-- **Graded time of `reduce`.** From round `i`, on states of the invariants of `Z` and `P`, `n`
activations of the costed `reduce` take the sum over the rounds `i + j`, `j < n`, of the bounds of
the steps of the environment and the protocol and `12`, and the bound `tD (i + n)` of the
distinguisher and `6`. An environment whose state grows has no uniform step bound; this bound holds
on the states it reaches. -/
theorem reduce.timeBoundGraded_timed {τ E O Q A ζ : Type} {F : OutcomeFilter}
    (P : OProt τ E O Q A) (Z : Strat ζ E O) (dist : ζ → SPComp Bool) (distCost nextCost : ζ → ℕ)
    (stepCost : τ → E → ℕ) (obsCost : ζ → O → ℕ) {InvZ MidZ : ℕ → ζ → Prop} {InvS : ℕ → τ → Prop}
    {Ev : ℕ → E → Prop} {Out : ℕ → O → Prop} {tD tN tC tP tO : ℕ → ℕ}
    (hZ : EnvCostBound F Z distCost nextCost obsCost InvZ MidZ Ev Out tD tN tO)
    (hS : ProtCostBound F P stepCost InvS Ev Out tC tP) (n : ℕ) :
    ∀ i z t h, InvZ i z → InvS i t →
      StepTimeBoundOn F (reduce.timed P Z dist distCost n z t h nextCost stepCost obsCost)
        (∑ j ∈ Finset.range n, (tN (i + j) + tC (i + j) + tP (i + j) + tO (i + j) + 12) +
          (tD (i + n) + 6)) := by
  induction n with
  | zero =>
    intro i z t h hz ht
    have hd := hZ.dist_time i z hz
    simp only [reduce.timed, Finset.range_zero, Finset.sum_empty, Nat.add_zero, Nat.zero_add]
    refine (stepTimeBoundOn_delay (c := 1) (n := tD i + 5)
      ⟨by omega, (timeBoundOn_rand_iff _ _ _ _).2 ⟨by omega, fun o _ => ?_⟩⟩).mono (by omega)
    rcases o with _ | ⟨b, _⟩ <;> exact ⟨by grind, trivial⟩
  | succ n ih =>
    intro i z t h hz ht
    have hsum :
        ∑ j ∈ Finset.range (n + 1), (tN (i + j) + tC (i + j) + tP (i + j) + tO (i + j) + 12) =
        ∑ j ∈ Finset.range n,
            (tN (i + 1 + j) + tC (i + 1 + j) + tP (i + 1 + j) + tO (i + 1 + j) + 12) +
          (tN i + tC i + tP i + tO i + 12) := by
      rw [Finset.sum_range_succ']
      congr 1
      exact Finset.sum_congr rfl fun j _ => by rw [show i + (j + 1) = i + 1 + j by omega]
    rw [hsum, show i + (n + 1) = i + 1 + n by omega]
    have ih' := ih (i + 1)
    generalize (∑ j ∈ Finset.range n,
      (tN (i + 1 + j) + tC (i + 1 + j) + tP (i + 1 + j) + tO (i + 1 + j) + 12)) = a at ih' ⊢
    generalize tD (i + 1 + n) = d at ih' ⊢
    simp only [reduce.timed]
    have hN := hZ.next_time i z hz
    refine (stepTimeBoundOn_delay (c := 1)
      (n := tN i + tC i + tP i + tO i + (a + (d + 6)) + 11)
      ⟨by omega, (timeBoundOn_rand_iff _ _ _ _).2 ⟨by omega, fun o ho => ?_⟩⟩).mono (by omega)
    rcases o with _ | ⟨⟨z₁, e⟩, h₁⟩
    · exact ⟨by grind, trivial⟩
    obtain ⟨hm, he⟩ := hZ.next_ret i z h z₁ e h₁ hz ho
    have hc := hS.step_cost i t e ht he
    refine (stepTimeBoundOn_delay (c := 1) (stepTimeBoundOn_delay (c := 1 + stepCost t e)
      (timeBoundOn_bind (hS.step_time i t e ht he) (hS.step_ret i t e ht he)
        (n := tO i + (a + (d + 6)) + 5) fun p hp => ?_))).mono (by omega)
    have hp₂ := hZ.obs_time i z₁ p.2 hm hp.2
    refine ⟨by omega, (timeBoundOn_rand_iff _ _ _ _).2 ⟨by omega, fun o' ho' => ?_⟩⟩
    rcases o' with _ | ⟨z₂, h₂⟩
    · exact ⟨by grind, trivial⟩
    exact (stepTimeBoundOn_delay (c := 1) (stepTimeBoundOn_delay (c := 1)
      (ih' z₂ p.1 h₂ (hZ.obs_ret i z₁ p.2 h₁ z₂ h₂ hm hp.2 ho') hp.1))).mono (by omega)

/-- **Graded time of the environment reduction.** From initial states of the invariants, the
costed reduction of `Z` against `P` takes the sum over the `Z.input.rounds` activations of the
bounds of the steps of the environment and the protocol and `12`, and the bound of the distinguisher
at the last round and `8`. -/
theorem reduction.timeBoundGraded_timed {τ E O Q A ζ : Type} {F : OutcomeFilter}
    (P : OProt τ E O Q A) (Z : UCConcrete.Env (Strat ζ E O) ζ) (distCost nextCost : ζ → ℕ)
    (stepCost : τ → E → ℕ) (obsCost : ζ → O → ℕ) {InvZ MidZ : ℕ → ζ → Prop} {InvS : ℕ → τ → Prop}
    {Ev : ℕ → E → Prop} {Out : ℕ → O → Prop} {tD tN tC tP tO : ℕ → ℕ}
    (hZ : EnvCostBound F Z.input distCost nextCost obsCost InvZ MidZ Ev Out tD tN tO)
    (hS : ProtCostBound F P stepCost InvS Ev Out tC tP) (hz : InvZ 0 Z.input.init)
    (ht : InvS 0 P.init) :
    StepTimeBoundOn F (reduction.timed P Z distCost nextCost stepCost obsCost)
      (1 + (∑ j ∈ Finset.range Z.input.rounds, (tN j + tC j + tP j + tO j + 12) +
        (tD Z.input.rounds + 1 + 6))) := by
  have H := reduce.timeBoundGraded_timed P Z.input Z.dist (fun a => 1 + distCost a) nextCost
    stepCost obsCost (tD := fun i => tD i + 1)
    ⟨fun i z hi => by have := hZ.dist_time i z hi; omega, hZ.next_time, hZ.next_ret, hZ.obs_time,
      hZ.obs_ret⟩ hS Z.input.rounds 0 Z.input.init P.init Z.heap hz ht
  simp only [Nat.zero_add] at H
  exact stepTimeBoundOn_delay H

/-! ## Uniform bounds -/

/-- **Time of `reduce`.** When the distinguisher costs at most `cd`, the steps of the environment
at most `cn` and `co`, the protocol's step at most `cs` on all states and its oracle program runs
in time `s`, `n` activations of the costed `reduce` take `n * (cn + cs + s + co + 12) + (cd + 6)`
on every path. This is `reduce.timeBoundGraded_timed` over every outcome and the constant
invariant, for environments whose steps do not read a state of unbounded size. -/
theorem reduce.timeBound_timed {τ E O Q A ζ : Type} (P : OProt τ E O Q A) (Z : Strat ζ E O)
    (dist : ζ → SPComp Bool) (distCost : ζ → ℕ) (nextCost : ζ → ℕ) (stepCost : τ → E → ℕ)
    (obsCost : ζ → O → ℕ) {cd cn cs co s : ℕ} (hd : ∀ z, distCost z ≤ cd)
    (hn : ∀ z, nextCost z ≤ cn) (hs : ∀ t e, stepCost t e ≤ cs) (ho : ∀ z o, obsCost z o ≤ co)
    (hP : ∀ t e, (ofAdv (P.step t e)).TimeBound s) (n : ℕ) :
    ∀ z t h, StepTimeBound (reduce.timed P Z dist distCost n z t h nextCost stepCost obsCost)
      (n * (cn + cs + s + co + 12) + (cd + 6)) := by
  intro z t h
  have H := reduce.timeBoundGraded_timed (F := anyOutcome) P Z dist distCost nextCost stepCost
    obsCost (InvZ := fun _ _ => True) (MidZ := fun _ _ => True) (InvS := fun _ _ => True)
    (Ev := fun _ _ => True) (Out := fun _ _ => True) (tD := fun _ => cd) (tN := fun _ => cn)
    (tC := fun _ => cs) (tP := fun _ => s) (tO := fun _ => co)
    ⟨fun _ z _ => hd z, fun _ z _ => hn z, fun _ _ _ _ _ _ _ _ => ⟨trivial, trivial⟩,
      fun _ z o _ _ => ho z o, fun _ _ _ _ _ _ _ _ _ => trivial⟩
    ⟨fun _ t e _ _ => hs t e, fun _ t e _ _ => (hP t e).timeBoundOn _,
      fun _ _ _ _ _ => allRetOn_of_forall _ (fun _ => ⟨trivial, trivial⟩) _⟩
    n 0 z t h trivial trivial
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at H
  exact stepTimeBoundOn_anyOutcome.1 H

/-- **Time of the environment reduction.** Under the cost bounds of `reduce.timeBound_timed`,
the costed reduction of `Z` against `P` takes
`1 + (Z.input.rounds * (cn + cs + s + co + 12) + (cd + 1 + 6))`. -/
theorem reduction.timeBound_timed {τ E O Q A ζ : Type} (P : OProt τ E O Q A)
    (Z : UCConcrete.Env (Strat ζ E O) ζ) (distCost : ζ → ℕ) (nextCost : ζ → ℕ)
    (stepCost : τ → E → ℕ) (obsCost : ζ → O → ℕ) {cd cn cs co s : ℕ} (hd : ∀ z, distCost z ≤ cd)
    (hn : ∀ z, nextCost z ≤ cn) (hs : ∀ t e, stepCost t e ≤ cs) (ho : ∀ z o, obsCost z o ≤ co)
    (hP : ∀ t e, (ofAdv (P.step t e)).TimeBound s) :
    StepTimeBound (reduction.timed P Z distCost nextCost stepCost obsCost)
      (1 + (Z.input.rounds * (cn + cs + s + co + 12) + (cd + 1 + 6))) :=
  stepTimeBound_delay (reduce.timeBound_timed P Z.input Z.dist (fun a => 1 + distCost a)
    nextCost stepCost obsCost (cd := cd + 1) (fun z => by grind) hn hs ho hP _ _ _ _)

end CatCrypt.Crypto.UCTransparent.OProt
