/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveSimulator

/-!
# Tests of `derive_hybrid_time (graded)`

Fresh multi-call simulators whose steps scan list-valued state, each certified by the graded
time bound at the length potential of its state:

* `logSim`: a log of the outer events, each answered by a membership test in the log; the
  invariant `s.length ≤ 0 + 1 * i`; lifted to the bundled simulator `logSimS` by
  `derive_simulator`;
* `keySim`: a key fixed by the first event, a `match` on the state, a scan of the log by `any`;
* `coinSim`: a coin drawn at the first event (a bind of the step), then events logged;
* `primSim`: a primitive `f` with a cost parameter, whose bound is a binder of the theorem;
* `cntSim`: a counter state without lists, whose potential has no atom;
* `nestSim`: records of positions scanned at every event, a step quadratic in the potential,
  refused with its bound.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveSimulatorGradedTest

open CatCrypt.Core CatCrypt.Crypto.UCTransparent CatCrypt.Crypto

/-- A log of the outer events, each answered by whether it was logged before. -/
noncomputable def logSim : MultiHybrid (List ℕ) ℕ Bool Unit Unit where
  init := []
  fuel := 0
  start s e := SPComp.pure (e :: s, .inr (List.elem e s))
  resume s o := SPComp.pure (s, .inl o)
  finish s _ := SPComp.pure (s, true)
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

derive_reduction logSim
derive_time_bound logSim.start.tree
derive_time_bound logSim.resume.tree
derive_time_bound logSim.finish.tree
derive_hybrid_time (graded) logSim

/-- The graded bound of the log: after `i` activations the log has at most `i` entries and a
step costs at most `2 + 4 * i`. -/
example : logSim.timed.TimeBoundGraded (fun i s => s.length ≤ 0 + 1 * i) 2 4 :=
  logSim.timeBoundGraded_timed

/-- The simulator of the log. -/
noncomputable def logSimS (V : PubView ℕ Bool) (W : PubView Unit Unit)
    (h : logSim.Opaque V W) : Simulator ℕ Bool Unit Unit V W :=
  Simulator.ofMultiHybrid logSim h

derive_simulator logSimS

/-- `derive_simulator` lifts the graded bound of the log to the bundled simulator. -/
example (V : PubView ℕ Bool) (W : PubView Unit Unit) : (logSimS.timed V W).TimeBoundGraded 2 4 :=
  logSimS.timeBoundGraded_timed V W

/-- A key fixed by the first event, then events logged and matched against the key. -/
noncomputable def keySim : MultiHybrid (Option ℕ × List ℕ) ℕ Bool Unit Unit where
  init := (none, [])
  fuel := 0
  start s e := match s.1 with
    | none => SPComp.pure ((some e, s.2), .inr false)
    | some v => SPComp.pure ((s.1, e :: s.2), .inr (s.2.any (fun c => c == v)))
  resume s o := SPComp.pure (s, .inl o)
  finish s _ := SPComp.pure (s, s.2.elem 0)
  start_noFail s _ := by
    cases s.1 <;> exact SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

derive_reduction keySim
derive_time_bound keySim.start.tree
derive_time_bound keySim.resume.tree
derive_time_bound keySim.finish.tree
derive_hybrid_time (graded) keySim

/-- The graded bound of the keyed log: the potential is the length of the log. -/
example : keySim.timed.TimeBoundGraded (fun i s => s.2.length ≤ 0 + 1 * i) 4 6 :=
  keySim.timeBoundGraded_timed

/-- A coin drawn at the first event, then events logged. -/
noncomputable def coinSim : MultiHybrid (Option Bool × List ℕ) ℕ Bool Unit Unit where
  init := (none, [])
  fuel := 0
  start s e := match s.1 with
    | none => SPComp.bind (SPComp.sample Bool) fun b => SPComp.pure ((some b, s.2), .inr b)
    | some v => SPComp.pure ((some v, e :: s.2), .inr (s.2.elem e))
  resume s o := SPComp.pure (s, .inl o)
  finish s _ := SPComp.pure (s, true)
  start_noFail s _ := by
    rcases s with ⟨_ | v, h⟩
    · exact CatCrypt.Crypto.Assumptions.SPComp.bind_noFail
        (fun h => CatCrypt.Crypto.Assumptions.SPComp.sample_noFail h)
        fun _ => SPComp.pure_noFail _
    · exact SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

derive_reduction coinSim
derive_time_bound coinSim.start.tree
derive_time_bound coinSim.resume.tree
derive_time_bound coinSim.finish.tree
derive_hybrid_time (graded) coinSim

/-- The graded bound of the coin and the log: the drawn coin leaves the log unchanged. -/
example : coinSim.timed.TimeBoundGraded (fun i s => s.2.length ≤ 0 + 1 * i) 4 4 :=
  coinSim.timeBoundGraded_timed

/-- A log of the events with a primitive `f` applied to each event. -/
noncomputable def primSim (f : ℕ → Bool) : MultiHybrid (List ℕ) ℕ Bool Unit Unit where
  init := []
  fuel := 0
  start s e := SPComp.pure (e :: s, .inr (f e && s.elem e))
  resume s o := SPComp.pure (s, .inl o)
  finish s _ := SPComp.pure (s, true)
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

derive_reduction primSim
derive_time_bound primSim.start.tree
derive_time_bound primSim.resume.tree
derive_time_bound primSim.finish.tree
derive_hybrid_time (graded) primSim

/-- The graded bound with the cost `t` of the primitive in the constant. -/
example (f : ℕ → Bool) (fCost : ℕ → ℕ) {t : ℕ} (ht : ∀ a, fCost a ≤ t) :
    (primSim.timed f fCost).TimeBoundGraded (fun i s => s.length ≤ 0 + 1 * i) (t + 5) 4 :=
  primSim.timeBoundGraded_timed f fCost ht

/-- A counter state without lists. -/
noncomputable def cntSim : MultiHybrid ℕ ℕ Bool Unit Unit where
  init := 0
  fuel := 0
  start s e := SPComp.pure (s + 1, .inr (e == s))
  resume s o := SPComp.pure (s, .inl o)
  finish s _ := SPComp.pure (s, true)
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

derive_reduction cntSim
derive_time_bound cntSim.start.tree
derive_time_bound cntSim.resume.tree
derive_time_bound cntSim.finish.tree
derive_hybrid_time (graded) cntSim

/-- A state without atoms: the potential is trivial and the steps have a uniform cost. -/
example : cntSim.timed.TimeBoundGraded (fun i _ => ∀ _ : Unit, 0 ≤ 0 + 0 * i) 2 0 :=
  cntSim.timeBoundGraded_timed

/-- Records of positions, each scanned at every event: a step quadratic in the potential. -/
noncomputable def nestSim : MultiHybrid (List (ℕ × List ℕ)) ℕ Bool Unit Unit where
  init := []
  fuel := 0
  start s e := SPComp.pure ((e, s.map Prod.fst) :: s, .inr (s.any (fun c => c.2.elem e)))
  resume s o := SPComp.pure (s, .inl o)
  finish s _ := SPComp.pure (s, true)
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

derive_reduction nestSim
derive_time_bound nestSim.start.tree
derive_time_bound nestSim.resume.tree
derive_time_bound nestSim.finish.tree

/--
error: derive_hybrid_time (graded): the bound of the step `start` of `CatCrypt.Tactics.DeriveSimulatorGradedTest.nestSim`
  (0 + 3) * M + 1 + ((1 + (4 * M + 1) + 5) * M + 1) + 2
is not affine in the bound `M` of the potential of the state:
  the term
    (1 + (4 * M + 1) + 5) * M
  reads the state other than through
    M
-/
#guard_msgs in
derive_hybrid_time (graded) nestSim

end CatCrypt.Tactics.DeriveSimulatorGradedTest
