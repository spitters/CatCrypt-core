/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveSimulator

/-!
# Tests of `derive_hybrid_time (potential)` and of the potential branch of `derive_simulator`

Fresh multi-call simulators, one per shape of the class of `StatePotential.lean`:

* `lazyTab`: a lazily filled table on a structure state, costed on costed states (the table and
  its cost companion); a miss fills the entry with `Function.update`. The potential is the
  supremum of the companion, the import of a query `3 + k` (the companion grows by `3`).
* `accBuf`: a buffer that accumulates the input lists and answers with the length read before the
  append; the potential is the length plus the elements of the buffer, the import of an event its
  own potential, and the answer, which copies the length, passes on no import.
* `declPrice`: a price declared by an event `some p` and read by an event `none`, whose step
  builds a list of the price's length; the potential is the price.
* `fwdOuter`: a forwarding outer factor over `accBuf`, composed in `fwdBufSim`: the middle
  interface conserves import with `κ = 0`.
* `selfAppend`: a step that appends the state to itself, refused at its potential clause.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveSimulatorPotTest

open CatCrypt.Core CatCrypt.Crypto.UCTransparent CatCrypt.Crypto

/-- The state of `lazyTab`: a table of answers and a counter. -/
structure TabSt where
  /-- The table. -/
  tab : ℕ → Option Bool
  /-- A counter that the steps keep. -/
  n : ℕ

/-- A lazily filled table: a query `k` answers the entry at `k`, filling it on a miss. -/
noncomputable def lazyTab : MultiHybrid TabSt ℕ Bool Unit Unit where
  init := ⟨fun _ => none, 0⟩
  fuel := 0
  start s k := match s.tab k with
    | some v => SPComp.pure (s, .inr v)
    | none => SPComp.pure (⟨Function.update s.tab k (some (k % 2 == 0)), s.n⟩, .inr true)
  resume s o := SPComp.pure (s, .inl o)
  finish s _ := SPComp.pure (s, true)
  start_noFail s k := by
    cases s.tab k <;> exact SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

derive_reduction lazyTab
derive_time_bound lazyTab.start.treeHat
derive_time_bound lazyTab.resume.treeHat
derive_time_bound lazyTab.finish.treeHat
derive_hybrid_time (potential) lazyTab

/-- The potential bound of the lazily filled table: a query `k` receives the import `3 + k`. -/
example : Nonempty <| lazyTab.timed.PotentialBound (fun k => 3 + StatePotential.pot k)
    (fun o => 0 + StatePotential.pot o) (fun g => StatePotential.pot g)
    (fun o => StatePotential.pot o) 5 1 :=
  ⟨lazyTab.potentialBound_timed⟩

/-- A buffer accumulating the input lists. -/
noncomputable def accBuf : MultiHybrid (List ℕ) (List ℕ) ℕ Unit Unit where
  init := []
  fuel := 0
  start s x := SPComp.pure (s ++ x, .inr s.length)
  resume s _ := SPComp.pure (s, .inr 0)
  finish s _ := SPComp.pure (s, 0)
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

derive_reduction accBuf
derive_time_bound accBuf.start.tree
derive_time_bound accBuf.resume.tree
derive_time_bound accBuf.finish.tree
derive_hybrid_time (potential) accBuf

/-- The potential bound of the buffer: a step costs at most `4 + 5 * (Φ s + g x)`; the answer
copies the length of the buffer, so the outputs pass on no import. -/
example : Nonempty <| accBuf.timed.PotentialBound (fun x => 0 + StatePotential.pot x)
    (fun o => 0 + StatePotential.pot o) (fun g => StatePotential.pot g) (fun _ => 0) 4 5 :=
  ⟨accBuf.potentialBound_timed⟩

/-- A price declared by `some p` and read by `none`. -/
noncomputable def declPrice : MultiHybrid ℕ (Option ℕ) ℕ Unit Unit where
  init := 0
  fuel := 0
  start s e := match e with
    | some p => SPComp.pure (p, .inr 0)
    | none => SPComp.pure (s, .inr (List.replicate s 0).length)
  resume s _ := SPComp.pure (s, .inr 0)
  finish s _ := SPComp.pure (s, 0)
  start_noFail _ e := by
    cases e <;> exact SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

derive_reduction declPrice
derive_time_bound declPrice.start.tree
derive_time_bound declPrice.resume.tree
derive_time_bound declPrice.finish.tree
derive_hybrid_time (potential) declPrice

/-- The potential bound of the declared price. -/
example : Nonempty <| declPrice.timed.PotentialBound (fun x => 0 + StatePotential.pot x)
    (fun o => 0 + StatePotential.pot o) (fun g => StatePotential.pot g) (fun _ => 0) 6 6 :=
  ⟨declPrice.potentialBound_timed⟩

/-- The simulator of the lazily filled table. -/
noncomputable def lazySim (V : PubView ℕ Bool) (W : PubView Unit Unit)
    (h : lazyTab.Opaque V W) : Simulator ℕ Bool Unit Unit V W :=
  Simulator.ofMultiHybrid lazyTab h

derive_simulator lazySim

example (V : PubView ℕ Bool) (W : PubView Unit Unit) :
    (lazySim.timed V W).TimeBoundPot (fun k => 3 + StatePotential.pot k)
      (fun o => 0 + StatePotential.pot o) (fun g => StatePotential.pot g)
      (fun o => StatePotential.pot o) 5 1 0 :=
  lazySim.timeBoundPot_timed V W

example (V : PubView ℕ Bool) (W : PubView Unit Unit) : (lazySim.timed V W).PotCert 5 1 4 0 :=
  lazySim.potCert_timed V W

/-- A forwarding outer factor: an event is passed to the inner factor, its answer returned. -/
noncomputable def fwdOuter : MultiHybrid Unit (List ℕ) ℕ (List ℕ) ℕ where
  init := ()
  fuel := 0
  start s x := SPComp.pure (s, .inl x)
  resume s o := SPComp.pure (s, .inr o)
  finish s o := SPComp.pure (s, o)
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

derive_reduction fwdOuter
derive_time_bound fwdOuter.start.tree
derive_time_bound fwdOuter.resume.tree
derive_time_bound fwdOuter.finish.tree
derive_hybrid_time (potential) fwdOuter

/-- A buffer that accumulates the input lists and answers `0`: its answers pass on their
potential. -/
noncomputable def accSink : MultiHybrid (List ℕ) (List ℕ) ℕ Unit Unit where
  init := []
  fuel := 0
  start s x := SPComp.pure (x ++ s, .inr 0)
  resume s _ := SPComp.pure (s, .inr 0)
  finish s _ := SPComp.pure (s, 0)
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

derive_reduction accSink
derive_time_bound accSink.start.tree
derive_time_bound accSink.resume.tree
derive_time_bound accSink.finish.tree
derive_hybrid_time (potential) accSink

/-- The composite of the forwarding factor over the sink. -/
noncomputable def fwdSinkSim (V : PubView (List ℕ) ℕ) (U : PubView (List ℕ) ℕ)
    (W : PubView Unit Unit) (h₁ : fwdOuter.Opaque V U) (h₂ : accSink.Opaque U W) :
    Simulator (List ℕ) ℕ Unit Unit V W :=
  (Simulator.ofMultiHybrid fwdOuter h₁).comp (Simulator.ofMultiHybrid accSink h₂)

derive_simulator fwdSinkSim

/-- The certificate of the composite: the potentials of the factors add, the middle interface
conserves import with `κ = 0`. -/
example (V U : PubView (List ℕ) ℕ) (W : PubView Unit Unit) :
    ∃ a b c d, (fwdSinkSim.timed V U W).PotCert a b c d :=
  ⟨_, _, _, _, fwdSinkSim.potCert_timed V U W⟩

/-- The forwarding factor over `accBuf`, whose answer copies the length of the buffer: the outer
factor receives answers of import `pot o` that the inner factor does not pass on, and the
composite is refused at its middle interface. -/
noncomputable def fwdBufSim (V : PubView (List ℕ) ℕ) (U : PubView (List ℕ) ℕ)
    (W : PubView Unit Unit) (h₁ : fwdOuter.Opaque V U) (h₂ : accBuf.Opaque U W) :
    Simulator (List ℕ) ℕ Unit Unit V W :=
  (Simulator.ofMultiHybrid fwdOuter h₁).comp (Simulator.ofMultiHybrid accBuf h₂)

/--
error: derive_simulator: the middle interface of the composite
  (Simulator.Timed.ofMultiHybrid fwdOuter.timed).comp (Simulator.Timed.ofMultiHybrid accBuf.timed)
does not conserve import up to `κ ≤ 16` per message: the inner factor receives events of import
  fun x ↦ 0 + StatePotential.pot x
where the outer factor passes on
  fun x ↦ StatePotential.pot x
and the outer factor receives answers of import
  fun x ↦ 0 + StatePotential.pot x
where the inner factor passes on
  fun x ↦ 0
-/
#guard_msgs (whitespace := lax) in
derive_simulator fwdBufSim

/-- A buffer whose step appends the buffer to itself: its potential doubles. -/
noncomputable def selfAppend : MultiHybrid (List ℕ) Unit ℕ Unit Unit where
  init := []
  fuel := 0
  start s _ := SPComp.pure (s ++ s, .inr 0)
  resume s _ := SPComp.pure (s, .inr 0)
  finish s _ := SPComp.pure (s, 0)
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

derive_reduction selfAppend
derive_time_bound selfAppend.start.tree
derive_time_bound selfAppend.resume.tree
derive_time_bound selfAppend.finish.tree

/--
error: derive_hybrid_time (potential): the potential clause of the step `start` of
`CatCrypt.Tactics.DeriveSimulatorPotTest.selfAppend`, `Φ s' + h y ≤ Φ s + (κ + pot x)`, does not
close for `κ = 16` and the measures `0` passed on:
  `omega` does not prove
    s✝.length + s✝.length + (s✝.sum + s✝.sum) ≤ s✝.length + s✝.sum + 16
-/
#guard_msgs (whitespace := lax) in
derive_hybrid_time (potential) selfAppend

end CatCrypt.Tactics.DeriveSimulatorPotTest
