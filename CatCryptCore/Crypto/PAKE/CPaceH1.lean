/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PAKE.DHExtractKit
public import CatCryptCore.Crypto.EagerLazyRF
public import CatCryptCore.Crypto.OracleForkingLemma

/-!
# The CPace password generator: lazy and eager, and double matches

In CPace the generator of a password is `H1(pw)`. A simulator programs `H1` lazily: at the
first query of `pw` it draws a nonzero exponent `t` and answers `g^t`, recording `t`. This
file relates the lazy programming to the eager table of the double-match game `dmGame`
(`CatCryptCore.Crypto.PAKE.DHExtractKit`), and reduces the double-match bad event of a
CPace-style experiment to that game.

## Oracles that read one point of a function

A query `q` of a point oracle reads a function `f : D → R` at the point `pt q` and answers by
the deterministic step `step q (f (pt q))` on a state `σ`. The eager oracle `eagerOracle`
reads a function sampled before the run; the lazy oracle `lazyOracle` draws `f (pt q)` at the
first query of the point and records it in a table.

* `uniform_bind_run_eagerOracle`: averaged over a uniform function, a run against the eager
  oracle has the output and final state of a run against the lazy oracle.

## The CPace experiment

The adversary receives the simulated message `X = g^z` and queries `H1` (`Sum.inl pw`,
answered by the generator of `pw`) and the match oracle (`Sum.inr (pw, peer, k)`, answered by
the CPace match test of `k` for the transcript `(X, peer)` over the generator of `pw`). The
experiment records the queries that match; the bad event `DoubleMatch` is that two recorded
queries for distinct passwords match the same transcript.

* `lazyGame`: the experiment with `H1` programmed lazily; `eagerGame` with the table sampled
  up front.
* `lazyGame_eq_eagerGame`: the two experiments are equal.
* `matchWrap`: the match-recording reduction to the double-match game; it answers `H1` from
  the table it is given, forwards match queries and outputs a recorded double match.
* `eagerGame_le_dmGame`, `lazyGame_le_ssdhGame`: the bad event has probability at most
  `dmGame (matchWrap A)`, and at most `2 · ssdhGame (ssdhReduction (matchWrap A))`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.PAKE.CPaceH1

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.PRPPRF
open CatCrypt.Crypto.PAKE.DHExtract
open scoped ENNReal

/-! ## Monotonicity of decided events

This section belongs upstream, beside `DHExtract.map_decide_apply_true`. -/

/-- An event implied by another on the support of `p` has at least its probability. -/
theorem map_decide_le {β : Type} (p : PMF β) (P P' : β → Prop) [DecidablePred P]
    [DecidablePred P'] (h : ∀ y ∈ p.support, P y → P' y) :
    (p.map fun y => decide (P y)) true ≤ (p.map fun y => decide (P' y)) true := by
  rw [map_decide_apply_true, map_decide_apply_true]
  refine ENNReal.tsum_le_tsum fun y => ?_
  by_cases hy : y ∈ p.support
  · by_cases hP : P y
    · simp [hP, h y hy hP]
    · simp [hP]
  · simp [(PMF.apply_eq_zero_iff p y).2 hy]

/-! ## Oracles that read one point of a function -/

section PointOracle

variable {Q Ans D R σ : Type} [DecidableEq D]

/-- **The eager point oracle.** The query `q` reads the function `f` at the point `pt q` and
    answers by `step q (f (pt q))` from the state. -/
noncomputable def eagerOracle (pt : Q → D) (step : Q → R → σ → Ans × σ) (f : D → R) (s : σ)
    (q : Q) : PMF (Ans × σ) :=
  PMF.pure (step q (f (pt q)) s)

/-- **The lazy point oracle.** The query `q` reads the lazily sampled random function at the
    point `pt q` (a recorded value, or a fresh uniform value that is recorded) and answers by
    `step` from the first component of the state; the second component is the table. -/
noncomputable def lazyOracle [Fintype R] [Nonempty R] (pt : Q → D) (step : Q → R → σ → Ans × σ)
    (s : σ × List (D × R)) (q : Q) : PMF (Ans × (σ × List (D × R))) :=
  (rfOracle s.2 (pt q)).map fun x => ((step q x.1 s.1).1, ((step q x.1 s.1).2, x.2))

/-- The simulator program of a point oracle: one query at `pt q`, then the step. -/
def pointImpl (pt : Q → D) (step : Q → R → σ → Ans × σ) (s : σ) (q : Q) :
    OracleAdv D R (Ans × σ) :=
  .query (pt q) fun v => .ret (step q v s)

omit [DecidableEq D] in
/-- The point program against the keyed oracle of `f` is the eager oracle. -/
theorem simOracle_pointImpl_keyed (pt : Q → D) (step : Q → R → σ → Ans × σ) (f : D → R)
    (s : σ × Unit) (q : Q) :
    OracleAdv.simOracle (pointImpl pt step) (keyedOracle (fun f d => f d) f) s q =
      (eagerOracle pt step f s.1 q).map (Prod.map id fun s' => (s', ())) := by
  simp [OracleAdv.simOracle, pointImpl, keyedOracle, eagerOracle, PMF.pure_map]
  rfl

/-- The point program against the lazily sampled random function is the lazy oracle. -/
theorem simOracle_pointImpl_rf [Fintype R] [Nonempty R] (pt : Q → D)
    (step : Q → R → σ → Ans × σ) :
    OracleAdv.simOracle (pointImpl pt step) rfOracle = lazyOracle pt step := by
  funext s q
  simp only [OracleAdv.simOracle, pointImpl, lazyOracle, OracleAdv.run_query,
    OracleAdv.run_ret, PMF.map_bind, PMF.pure_map]
  rfl

/-- **Eager and lazy point oracles.** Averaged over a uniform function `D → R`, the output and
    final state of a run against the eager point oracle are those of a run against the lazy
    point oracle from the empty table. -/
theorem uniform_bind_run_eagerOracle [Fintype D] [Fintype R] [Nonempty R]
    {α : Type} (pt : Q → D) (step : Q → R → σ → Ans × σ) (A : OracleAdv Q Ans α) (s : σ) :
    (PMF.uniformFintype (D → R)).bind (fun f => OracleAdv.run (eagerOracle pt step f) A s) =
      (OracleAdv.run (lazyOracle pt step) A (s, [])).map fun x => (x.1, x.2.1) := by
  classical
  have h := Constructions.ECBCPRF.uniform_bind_run_keyed_map_fst
    (OracleAdv.simulate (pointImpl pt step) A s)
  simp only [OracleAdv.run_simulate, simOracle_pointImpl_rf, PMF.map_comp] at h
  have hk : ∀ f : D → R, OracleAdv.run (OracleAdv.simOracle (pointImpl pt step)
      (keyedOracle (fun f d => f d) f)) A (s, ()) =
      (OracleAdv.run (eagerOracle pt step f) A s).map (Prod.map id fun s' => (s', ())) :=
    fun f => (OracleAdv.run_map_state _ _ _
      (fun s q => (simOracle_pointImpl_keyed pt step f (s, ()) q).symm) A s).symm
  simp only [hk, PMF.map_comp] at h
  have hid : ((Prod.fst ∘ fun x : α × σ × Unit => ((x.1, x.2.1), x.2.2)) ∘
      Prod.map id fun s' => (s', ())) = (id : α × σ → α × σ) := by
    funext x; rfl
  simp only [hid, PMF.map_id] at h
  exact h

end PointOracle

/-! ## The CPace experiment -/

section CPace

variable {S W Pw : Type} [Field S] [DecidableEq W] (G : DHGroup S W)

/-- A query of the CPace experiment: `H1` at a password, or the match test `(pw, peer, k)`. -/
abbrev Query (W Pw : Type) := Pw ⊕ (Pw × W × W)

/-- An answer of the CPace experiment: a generator, or the bit of a match test. -/
abbrev Answer (W : Type) := W ⊕ Bool

/-- The recorded match queries. -/
abbrev MatchLog (W Pw : Type) := List (Pw × W × W)

/-- The password a query reads the generator of. -/
def Query.pw {W Pw : Type} : Query W Pw → Pw
  | .inl pw => pw
  | .inr m => m.1

/-- **The CPace match test** of the query `(pw, peer, k)` for the simulated message `X` over
    the generator `gen`: `peer` is not the identity and `k` is the Diffie–Hellman value of `X`
    and `peer` over `gen`. -/
def matchTest (X gen : W) (m : Pw × W × W) : Bool :=
  decide (m.2.1 ≠ G.pub 0 ∧ m.2.2 = G.cdhIn gen X m.2.1)

/-- **One step of the CPace experiment** with the exponent `t` of the password read: `H1`
    answers `g^t`; a match query answers its match test over `g^t` and is recorded if it
    matches. -/
def cpaceStep (X : W) (q : Query W Pw) (t : Sˣ) (log : MatchLog W Pw) :
    Answer W × MatchLog W Pw :=
  match q with
  | .inl _ => (.inl (G.pub t), log)
  | .inr m => (.inr (matchTest G X (G.pub t) m),
      if matchTest G X (G.pub t) m then m :: log else log)

/-- An adversary of the CPace experiment: on the simulated message it queries `H1` and the
    match oracle. -/
abbrev CPaceAdversary (W Pw α : Type) := W → OracleAdv (Query W Pw) (Answer W) α

/-- **The double-match bad event**: two recorded queries for distinct passwords match the same
    transcript. -/
def DoubleMatch (log : MatchLog W Pw) : Prop :=
  ∃ a ∈ log, ∃ b ∈ log, a.2.1 = b.2.1 ∧ a.1 ≠ b.1

instance [DecidableEq Pw] (log : MatchLog W Pw) : Decidable (DoubleMatch log) := by
  unfold DoubleMatch; infer_instance

variable [Fintype S] [DecidableEq S] [Fintype Pw] [DecidableEq Pw]

/-- **The CPace experiment with lazy `H1`.** The simulated message is `g^z`; `H1` draws a
    uniform nonzero exponent at the first query of a password. The output is the bad event. -/
noncomputable def lazyGame {α : Type} (A : CPaceAdversary W Pw α) : PMF Bool :=
  (PMF.uniformFintype S).bind fun z =>
    (OracleAdv.run (lazyOracle Query.pw (cpaceStep G (G.pub z))) (A (G.pub z)) ([], [])).map
      fun y => decide (DoubleMatch y.2.1)

/-- **The CPace experiment with eager `H1`.** The table `td : Pw → Sˣ` is sampled up front and
    `H1 pw = g^{td pw}`. -/
noncomputable def eagerGame {α : Type} (A : CPaceAdversary W Pw α) : PMF Bool :=
  (PMF.uniformFintype S).bind fun z => (PMF.uniformFintype (Pw → Sˣ)).bind fun td =>
    (OracleAdv.run (eagerOracle Query.pw (cpaceStep G (G.pub z)) td) (A (G.pub z)) []).map
      fun y => decide (DoubleMatch y.2)

/-- **Lazy and eager `H1`.** The CPace experiment with `H1` programmed lazily equals the
    experiment with the table sampled up front. -/
theorem lazyGame_eq_eagerGame {α : Type} (A : CPaceAdversary W Pw α) :
    lazyGame G A = eagerGame G A := by
  unfold lazyGame eagerGame
  refine congrArg _ (funext fun z => ?_)
  rw [← PMF.map_bind, uniform_bind_run_eagerOracle, PMF.map_comp]
  rfl

/-! ### The match-recording reduction -/

/-- The pairs of entries of a log. -/
def logPairs (log : MatchLog W Pw) : List ((Pw × W × W) × (Pw × W × W)) :=
  log.flatMap fun a => log.map fun b => (a, b)

/-- The output of the match-recording reduction on its log: the first recorded pair for
    distinct passwords and the same peer, as `(peer, k₁, k₂, pw₁, pw₂)`, and a losing output
    with equal passwords if there is none. -/
def findDM [Inhabited Pw] (X : W) (log : MatchLog W Pw) : W × W × W × Pw × Pw :=
  match (logPairs log).find? (fun p => decide (p.1.2.1 = p.2.2.1 ∧ p.1.1 ≠ p.2.1)) with
  | some p => (p.1.2.1, p.1.2.2, p.2.2.2, p.1.1, p.2.1)
  | none => (X, X, X, default, default)

/-- The simulator program of the match-recording reduction with the generator table `H`:
    `H1` is answered from `H`; a match query is forwarded and recorded if it matches. -/
def wrapImpl (H : Pw → W) (log : MatchLog W Pw) (q : Query W Pw) :
    OracleAdv (Pw × W × W) Bool (Answer W × MatchLog W Pw) :=
  match q with
  | .inl pw => .ret (.inl (H pw), log)
  | .inr m => .query m fun b => .ret (.inr b, if b then m :: log else log)

/-- **The match-recording reduction.** On the simulated message `X` and the generator table
    `H` it runs the CPace adversary, answering `H1` from `H` and forwarding match queries to
    the match oracle while recording those that match, and outputs a recorded double match
    (`findDM`). -/
def matchWrap [Inhabited Pw] {α : Type} (A : CPaceAdversary W Pw α) : DMAdversary W Pw :=
  fun X H => (OracleAdv.simulate (wrapImpl H) (A X) []).bind fun x => .ret (findDM X x.2)

omit [Fintype S] [DecidableEq S] [Fintype Pw] [DecidableEq Pw] in
/-- The reduction's program against the match oracle of the table `g^{td}` is the eager
    CPace oracle. -/
theorem simOracle_wrapImpl (X : W) (td : Pw → Sˣ) (s : MatchLog W Pw × Unit)
    (q : Query W Pw) :
    OracleAdv.simOracle (wrapImpl fun pw => G.pub (td pw))
        (dmOracle G X fun pw => G.pub (td pw)) s q =
      (eagerOracle Query.pw (cpaceStep G X) td s.1 q).map
        (Prod.map id fun s' => (s', ())) := by
  obtain ⟨log, ⟨⟩⟩ := s
  rcases q with pw | m
  · simp [OracleAdv.simOracle, wrapImpl, eagerOracle, cpaceStep, Query.pw, PMF.pure_map]
  · simp [OracleAdv.simOracle, wrapImpl, eagerOracle, cpaceStep, Query.pw, dmOracle,
      matchTest, PMF.pure_map]
    grind

omit [Fintype S] [DecidableEq S] [Fintype Pw] in
/-- The run of the match-recording reduction against the match oracle of the table `g^{td}`
    is the run of the adversary against the eager CPace oracle, with `findDM` applied to the
    final log. -/
theorem run_matchWrap [Inhabited Pw] {α : Type} (A : CPaceAdversary W Pw α) (X : W)
    (td : Pw → Sˣ) :
    OracleAdv.run (dmOracle G X fun pw => G.pub (td pw))
        (matchWrap A X fun pw => G.pub (td pw)) () =
      (OracleAdv.run (eagerOracle Query.pw (cpaceStep G X) td) (A X) []).map
        fun y => (findDM X y.2, ()) := by
  have hs := OracleAdv.run_map_state _ _ (fun s : MatchLog W Pw => (s, ()))
    (fun s q => (simOracle_wrapImpl G X td (s, ()) q).symm) (A X) []
  simp only [matchWrap, OracleAdv.run_bind, OracleAdv.run_simulate, ← hs, OracleAdv.run_ret,
    PMF.bind_map, PMF.map_comp]
  rfl

omit [Fintype S] [DecidableEq S] [Fintype Pw] [DecidableEq Pw] in
/-- Every recorded query of a run against the eager CPace oracle matches. -/
theorem run_eagerOracle_log_match {α : Type} (X : W) (td : Pw → Sˣ)
    (A : OracleAdv (Query W Pw) (Answer W) α) (y : α × MatchLog W Pw)
    (hy : y ∈ (OracleAdv.run (eagerOracle Query.pw (cpaceStep G X) td) A []).support) :
    ∀ m ∈ y.2, matchTest G X (G.pub (td m.1)) m = true := by
  refine OracleForking.run_support_rel _
    (fun s s' => (∀ m ∈ s, matchTest G X (G.pub (td m.1)) m = true) →
      ∀ m ∈ s', matchTest G X (G.pub (td m.1)) m = true)
    (fun _ h => h) (fun _ _ _ h₁ h₂ h => h₂ (h₁ h)) ?_ A [] y hy (by simp)
  intro s q x hx h
  simp only [eagerOracle, PMF.support_pure, Set.mem_singleton_iff] at hx
  subst hx
  rcases q with pw | m
  · simpa [cpaceStep] using h
  · intro m' hm'
    simp only [cpaceStep] at hm'
    split_ifs at hm' with ht
    · grind [Query.pw]
    · exact h m' hm'

omit [Fintype S] [DecidableEq S] [Fintype Pw] in
/-- **A recorded double match wins the double-match game.** -/
theorem dmWins_findDM [Inhabited Pw] (X : W) (td : Pw → Sˣ) (log : MatchLog W Pw)
    (hlog : ∀ m ∈ log, matchTest G X (G.pub (td m.1)) m = true) (hdm : DoubleMatch log) :
    DMWins G X (fun pw => G.pub (td pw)) (findDM X log) := by
  obtain ⟨a, ha, b, hb, hpeer, hne⟩ := hdm
  have hab : (a, b) ∈ logPairs log :=
    List.mem_flatMap.2 ⟨a, ha, List.mem_map.2 ⟨b, hb, rfl⟩⟩
  unfold findDM
  split
  · next p hf =>
    have hp := List.find?_some hf
    have hmem := List.mem_of_find?_eq_some hf
    simp only [logPairs, List.mem_flatMap, List.mem_map] at hmem
    obtain ⟨a', ha', b', hb', rfl⟩ := hmem
    have h₁ := hlog a' ha'
    have h₂ := hlog b' hb'
    simp only [matchTest, decide_eq_true_eq] at h₁ h₂ hp
    simp only [DMWins, SDHWins]
    grind
  · next hf =>
    rw [List.find?_eq_none] at hf
    exact absurd (by simp [hpeer, hne]) (hf _ hab)

/-- **The bad event reduces to the double-match game.** For every CPace adversary `A`, the
    probability of a double match in the eager experiment is at most the success probability
    of the match-recording reduction in `dmGame`. -/
theorem eagerGame_le_dmGame [Inhabited Pw] {α : Type} (A : CPaceAdversary W Pw α) :
    eagerGame G A true ≤ dmGame G (matchWrap A) true := by
  unfold eagerGame dmGame
  refine (bind_apply_le_mul _ _ _ _ 1 fun z => bind_apply_le_mul _ _ _ _ 1 fun td => ?_).trans_eq
    (one_mul _)
  rw [one_mul, run_matchWrap, PMF.map_comp]
  exact map_decide_le _ _ _ fun y hy =>
    dmWins_findDM G _ td _ (run_eagerOracle_log_match G _ td _ y hy)

/-- **The CPace double match reduces to strong SDH.** For every CPace adversary `A`, the
    probability of a double match with `H1` programmed lazily is at most
    `2 · Pr[ssdhGame (ssdhReduction (matchWrap A))]`. -/
theorem lazyGame_le_ssdhGame [Nonempty S] [Inhabited Pw] {α : Type}
    (A : CPaceAdversary W Pw α) :
    lazyGame G A true ≤ 2 * ssdhGame G (ssdhReduction G (matchWrap A)) true := by
  rw [lazyGame_eq_eagerGame]
  exact (eagerGame_le_dmGame G A).trans (dmGame_le_ssdhGame G _)

end CPace

end CatCrypt.Crypto.PAKE.CPaceH1
