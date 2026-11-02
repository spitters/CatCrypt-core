/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveSimulator
public import CatCryptCore.Crypto.UCSimulatorTimed

/-!
# Tests of `derive_simulator`: graded leaves and refused bounds

* `logSim`: a leaf on plain states with a graded time theorem and no step theorem of `start`.
* `hatSimRefused`: a leaf on costed states with no bound on them, refused with an error that names
  the missing theorems.
* `hatSim`: the same leaf with its graded time theorem; the hypothesis of the time theorem bounds
  the cost companion of a parameter.
* `selfSim`: a leaf whose time theorem assumes its own bound, refused.
* `funSim`: a leaf on plain states whose step theorem has a hypothesis on the state, refused.
* `logMono`, `hatMono`: graded leaves under `Simulator.mono`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveSimulatorBoundTest

open CatCrypt.Core CatCrypt.Crypto.UCTransparent CatCrypt.Crypto

/-- A multi-call simulator on the plain state `List ℕ`: `start` reads the length of the list and
records the event. -/
noncomputable def logProt : MultiHybrid (List ℕ) ℕ ℕ ℕ ℕ where
  init := []
  fuel := 0
  start s e := SPComp.pure (e :: s, .inr s.length)
  resume s o := SPComp.pure (s, .inr o)
  finish s o := SPComp.pure (s, o)
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

derive_reduction logProt

/-- The state of `hatProt`: a table and a phase. -/
structure HatSt where
  /-- The table. -/
  t : ℕ → ℕ
  /-- The phase. -/
  n : ℕ

/-- A multi-call simulator on a state holding a table: `start` reads the entry at the event and
raises it by `g`, so the cost of a read depends on the cost companion of the state. -/
noncomputable def hatProt (g : ℕ → ℕ) : MultiHybrid HatSt ℕ ℕ ℕ ℕ where
  init := ⟨fun _ => 0, 0⟩
  fuel := 0
  start s e := SPComp.pure (⟨fun x => if x = e then s.t e + g e else s.t x, s.n⟩, .inr (s.t e))
  resume s o := SPComp.pure (s, .inr o)
  finish s o := SPComp.pure (s, o)
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

derive_reduction hatProt
derive_time_bound hatProt.start.treeHat
derive_time_bound hatProt.resume.treeHat
derive_time_bound hatProt.finish.treeHat

/-- A step of `logProt` after `i` activations costs at most `2 + 3 * i`. -/
theorem logProt.timeBoundGraded_timed :
    logProt.timed.TimeBoundGraded (fun i s => s.length ≤ i) 2 3 := by
  refine ⟨by simp [logProt.timed], fun i s e hs => ⟨?_, ?_⟩, fun i s o hs => ⟨?_, ?_⟩,
    fun i s o hs => ⟨?_, ?_⟩⟩
  · have hs' : s.length ≤ i := hs
    simp only [logProt.timed, logProt.start.tree.timed, SPTree.Timed.stepTime,
      SPTree.Timed.time_ret, List.length.timedCost_eq]
    omega
  · have hs' : s.length ≤ i := hs
    simp [logProt.timed, logProt.start.tree.timed, SPTree.Timed.AllRet, hs']
  · simp [logProt.timed, logProt.resume.tree.timed, SPTree.Timed.stepTime, SPTree.Timed.time_ret]
  · have hs' : s.length ≤ i := hs
    simp [logProt.timed, logProt.resume.tree.timed, SPTree.Timed.AllRet]
    omega
  · simp [logProt.timed, logProt.finish.tree.timed, SPTree.Timed.stepTime, SPTree.Timed.time_ret]
  · have hs' : s.length ≤ i := hs
    simp [logProt.timed, logProt.finish.tree.timed, SPTree.Timed.AllRet]
    omega

/-- The simulator of `logProt`. -/
noncomputable def logSim (V W : PubView ℕ ℕ) (h : logProt.Opaque V W) :
    Simulator ℕ ℕ ℕ ℕ V W :=
  Simulator.ofMultiHybrid logProt h

derive_simulator logSim

/-- The leaf has a graded time theorem and no step theorem of `start`. -/
example (V W : PubView ℕ ℕ) (h : logProt.Opaque V W) :
    (logSim.timed V W).Erases (logSim V W h) ∧ (logSim.timed V W).TimeBoundGraded 2 3 :=
  ⟨logSim.erase_timed V W h, logSim.timeBoundGraded_timed V W⟩

/-- The simulator of `hatProt`, refused while `hatProt` has no time bound on its costed states. -/
noncomputable def hatSimRefused (V W : PubView ℕ ℕ) (g : ℕ → ℕ) (h : (hatProt g).Opaque V W) :
    Simulator ℕ ℕ ℕ ℕ V W :=
  Simulator.ofMultiHybrid (hatProt g) h

/--
error: derive_simulator: the costed form of `CatCrypt.Tactics.DeriveSimulatorBoundTest.hatProt`
runs on costed states and has no time bound on them. Prove
`CatCrypt.Tactics.DeriveSimulatorBoundTest.hatProt.timeBoundGraded_timed` (a step after `i`
activations costs at most `a + b * i`) or
`CatCrypt.Tactics.DeriveSimulatorBoundTest.hatProt.timeBoundInv_timed` (a bound on the states of
an invariant) before this command:
  derive_simulator: the bound of `hatProt.start.treeHat.timeBound_timed` or a hypothesis of it
  depends on the state or the input of the step
-/
#guard_msgs (whitespace := lax) in
derive_simulator hatSimRefused

/-- A step of `hatProt` after `i` activations costs at most `1 + (t + 5) * i`, for a cost at most
`t` of `g`: a step adds at most `t + 5` to the cost companion of an entry of the table. -/
theorem hatProt.timeBoundGraded_timed (g gCost : ℕ → ℕ) {t : ℕ} (hG : ∀ a, gCost a ≤ t) :
    (hatProt.timed g gCost).TimeBoundGraded (fun i s => ∀ x, s.1.2 x ≤ (t + 5) * i) 1 (t + 5) := by
  refine ⟨by simp [hatProt.timed], fun i s e hs => ⟨?_, ?_⟩, fun i s o hs => ⟨?_, ?_⟩,
    fun i s o hs => ⟨?_, ?_⟩⟩
  · have := hs e
    simp only [hatProt.timed, hatProt.start.treeHat.timed, SPTree.Timed.stepTime,
      SPTree.Timed.time_ret]
    omega
  · intro x
    have h₁ := hs x
    have h₂ := hs e
    have h₃ := hG e
    simp only [Nat.mul_succ]
    split <;> omega
  · simp [hatProt.timed, hatProt.resume.treeHat.timed, SPTree.Timed.stepTime,
      SPTree.Timed.time_ret]
  · intro x
    have h₁ := hs x
    simp only [Nat.mul_succ]
    omega
  · simp [hatProt.timed, hatProt.finish.treeHat.timed, SPTree.Timed.stepTime,
      SPTree.Timed.time_ret]
  · intro x
    have h₁ := hs x
    simp only [Nat.mul_succ]
    omega

/-- The simulator of `hatProt`, certified by its graded time theorem. -/
noncomputable def hatSim (V W : PubView ℕ ℕ) (g : ℕ → ℕ) (h : (hatProt g).Opaque V W) :
    Simulator ℕ ℕ ℕ ℕ V W :=
  Simulator.ofMultiHybrid (hatProt g) h

derive_simulator hatSim

/-- The hypothesis of the time theorem bounds the cost companion of the parameter `g`. -/
example (V W : PubView ℕ ℕ) (g gCost : ℕ → ℕ) {t : ℕ} (hG : ∀ a, gCost a ≤ t)
    (h : (hatProt g).Opaque V W) :
    (hatSim.timed V W g gCost).Erases (hatSim V W g h) ∧
      (hatSim.timed V W g gCost).TimeBoundGraded 1 (t + 5) :=
  ⟨hatSim.erase_timed V W g h gCost, hatSim.timeBoundGraded_timed V W g gCost hG⟩

/-- A second multi-call simulator on a state holding a table, for a leaf theorem that assumes the
bound of its own costed form. -/
noncomputable def selfProt : MultiHybrid HatSt ℕ ℕ ℕ ℕ where
  init := ⟨fun _ => 0, 0⟩
  fuel := 0
  start s e := SPComp.pure (⟨fun x => if x = e then s.t e + 1 else s.t x, s.n⟩, .inr (s.t e))
  resume s o := SPComp.pure (s, .inr o)
  finish s o := SPComp.pure (s, o)
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

derive_reduction selfProt

/-- A theorem that assumes the bound it states. -/
theorem selfProt.timeBoundInv_timed {Inv : ((ℕ → ℕ) × (ℕ → ℕ)) × ℕ → Prop} {a b c : ℕ}
    (h : selfProt.timed.TimeBoundInv Inv a b c) : selfProt.timed.TimeBoundInv Inv a b c := h

/-- The simulator of `selfProt`, refused for the hypothesis of `selfProt.timeBoundInv_timed`. -/
noncomputable def selfSim (V W : PubView ℕ ℕ) (h : selfProt.Opaque V W) :
    Simulator ℕ ℕ ℕ ℕ V W :=
  Simulator.ofMultiHybrid selfProt h

/--
error: derive_simulator: the time theorem of `CatCrypt.Tactics.DeriveSimulatorBoundTest.selfSim`
would assume the time bound of its own costed form:
  selfProt.timed.TimeBoundInv ?Inv✝ ?a✝ ?b✝ ?c✝
Prove `CatCrypt.Tactics.DeriveSimulatorBoundTest.selfProt.timeBoundGraded_timed` or
`CatCrypt.Tactics.DeriveSimulatorBoundTest.selfProt.timeBoundInv_timed` before this command, or
the bound of the simulator that contains it.
-/
#guard_msgs (whitespace := lax) in
derive_simulator selfSim

/-- A multi-call simulator on a function state whose step theorem has a hypothesis on the state:
on a plain state, the hypothesis of the step theorem is not shared with a hypothesis on a
parameter. -/
noncomputable def funProt (g : ℕ → ℕ) : MultiHybrid (ℕ → ℕ) ℕ ℕ ℕ ℕ where
  init := fun _ => 0
  fuel := 0
  start s e := SPComp.pure (fun x => if x = e then s e + g e else s x, .inr (s e))
  resume s o := SPComp.pure (s, .inr o)
  finish s o := SPComp.pure (s, o)
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

/-- The simulator of `funProt`, refused: the hypotheses of its step theorem bound the state. -/
noncomputable def funSim (V W : PubView ℕ ℕ) (g : ℕ → ℕ) (h : (funProt g).Opaque V W) :
    Simulator ℕ ℕ ℕ ℕ V W :=
  Simulator.ofMultiHybrid (funProt g) h

/--
error: derive_simulator: the costed form of `CatCrypt.Tactics.DeriveSimulatorBoundTest.funProt`
has no time bound independent of the state. Prove
`CatCrypt.Tactics.DeriveSimulatorBoundTest.funProt.timeBoundGraded_timed` (a step after `i`
activations costs at most `a + b * i`) before this command:
  derive_simulator: the bound of `funProt.start.tree.timeBound_timed` or a hypothesis of it
  depends on the state or the input of the step
-/
#guard_msgs (whitespace := lax) in
derive_simulator funSim

/-- The size-graded form of the bound of `logProt`, with the constant `0` of the size. -/
theorem logProt.timeBoundSized_timed {sE sO : ℕ → ℕ} :
    logProt.timed.TimeBoundSized (fun i s => s.length ≤ i) sE sO 2 3 0 :=
  logProt.timeBoundGraded_timed.timeBoundSized sE sO 0

/-- `logSim` at other views: a graded leaf under a change of views. -/
noncomputable def logMono (V V' W W' : PubView ℕ ℕ) (h : logProt.Opaque V W)
    (hVev : ∀ e e', V'.ev e e' → V.ev e e') (hVout : ∀ o o', V.out o o' → V'.out o o')
    (hWev : ∀ g g', W.ev g g' → W'.ev g g') (hWout : ∀ o o', W'.out o o' → W.out o o') :
    Simulator ℕ ℕ ℕ ℕ V' W' :=
  (Simulator.ofMultiHybrid logProt h).mono hVev hVout hWev hWout

derive_simulator logMono

/-- The graded and size-graded bounds of the leaf are kept by the change of views. -/
example (V V' W W' : PubView ℕ ℕ) {sE sO : ℕ → ℕ} :
    (logMono.timed V V' W W').TimeBoundGraded 2 3 ∧
      (logMono.timed V V' W W').TimeBoundSized sE sO 2 3 0 :=
  ⟨logMono.timeBoundGraded_timed V V' W W', logMono.timeBoundSized_timed V V' W W'⟩

/-- `hatSim` at other views: a graded leaf on costed states under a change of views. -/
noncomputable def hatMono (V V' W W' : PubView ℕ ℕ) (g : ℕ → ℕ) (h : (hatProt g).Opaque V W)
    (hVev : ∀ e e', V'.ev e e' → V.ev e e') (hVout : ∀ o o', V.out o o' → V'.out o o')
    (hWev : ∀ g g', W.ev g g' → W'.ev g g') (hWout : ∀ o o', W'.out o o' → W.out o o') :
    Simulator ℕ ℕ ℕ ℕ V' W' :=
  (Simulator.ofMultiHybrid (hatProt g) h).mono hVev hVout hWev hWout

derive_simulator hatMono

/-- The costed form at other views erases to `hatMono`, with the graded bound of the leaf. -/
example (V V' W W' : PubView ℕ ℕ) (g gCost : ℕ → ℕ) {t : ℕ} (hG : ∀ a, gCost a ≤ t)
    (h : (hatProt g).Opaque V W) (hVev : ∀ e e', V'.ev e e' → V.ev e e')
    (hVout : ∀ o o', V.out o o' → V'.out o o') (hWev : ∀ g g', W.ev g g' → W'.ev g g')
    (hWout : ∀ o o', W'.out o o' → W.out o o') :
    (hatMono.timed V V' W W' g gCost).Erases (hatMono V V' W W' g h hVev hVout hWev hWout) ∧
      (hatMono.timed V V' W W' g gCost).TimeBoundGraded 1 (t + 5) :=
  ⟨hatMono.erase_timed V V' W W' g h hVev hVout hWev hWout gCost,
    hatMono.timeBoundGraded_timed V V' W W' g gCost hG⟩

end CatCrypt.Tactics.DeriveSimulatorBoundTest
