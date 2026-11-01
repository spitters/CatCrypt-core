/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Party.Timed
public import CatCryptCore.Crypto.UCSimulatorCostGraded

/-!
# Costed loops of party programs

The costed form of the loop of a party program with calls (`Prog.loopMulti`). A costed body is
a program over the effect `Costed Op`, whose effect operations `q : Op` are interpreted by
step-prefixed costed trees `ι q : ℕ × SPTree.Timed ℕ`. The tree phases `ProgE.emitT`,
`ProgE.awaitT` run a costed program in step-prefixed costed trees: an operation `q` is the tree
`ι q`, a tick of `c` units the step cost `c` (`ProgE.runT`). The erasure `ProgE.eraseT ι` of a
costed program is the program of the classical language whose operations are the compiled trees
of `ι`, without the ticks; an activation in trees, compiled and its residual erased, is the
activation of the erased program (`ProgE.stepWithT_erase`).

The costed step `Prog.loopSys.timed ι bodyT` of the loop of `bodyT` is an activation in trees
that restarts with `bodyT s` when the residual returns `s`. The costed multi-call simulator
`Prog.loopMulti.timed ι bodyT s₀ n` runs on costed residual programs and wraps its steps as
`MultiHybrid.ofSys` does (`MultiHybrid.guardNF`); it erases through `ProgE.eraseT ι` to
`Prog.loopMulti body s₀ n` when `bodyT` erases to `body` (`Prog.loopMulti.erase_timed`).

The cost model is that of `ProgE.Bound` at the weight `ProgE.weightT ι`: an operation `q` costs
the step time of `ι q`, a tick of `c` units costs `c`. Under the graded bound
`ProgE.LoopBoundGraded (weightT ι) bodyT s₀ Inv a b`, the residual after `j` activations is a
suffix of the `k`-th iteration for some `k ≤ j`, whose remaining cost is at most `a + b * k`
(`Prog.loopMulti.ActInv`). An activation finishes at most the current iteration and runs the
next one up to its first output, so each step from a state of `ActInv j` costs at most
`(2 * a + b) + 2 * b * j` and returns states of `ActInv (j + 1)`
(`Prog.loopMulti.start_time`, `resume_time`, `finish_time`). For a constant bound (`b = 0`)
this is the invariant time bound `MultiHybrid.Timed.TimeBoundInv` with the bound `2 * a` of
each step (`Prog.loopMulti.timeBoundInv_timed`).

Search words: party language, costed loop, simulator cost, loop simulator, time certificate,
graded bound, lazily sampled table.

## Main definitions

* `Party.ProgE.runT`, `Party.ProgE.emitT`, `Party.ProgE.awaitT`, `Party.ProgE.stepWithT`,
  `Party.ProgE.actT`: activations of costed programs in step-prefixed costed trees.
* `Party.ProgE.weightT`, `Party.ProgE.eraseT`: the weight of the operations of a costed
  program, and its erasure.
* `Party.Prog.loopSys.timed`: the costed step of a loop.
* `Party.Prog.loopMulti.timed`: the costed multi-call simulator of a loop.
* `Party.Prog.loopMulti.IterInv`, `Party.Prog.loopMulti.ActInv`: the invariants of the
  residual programs, by iteration and by activation.

## Main results

* `Party.ProgE.stepWithT_erase`, `Party.Prog.loopSys.step_erase_timed`: erasure of an
  activation and of a loop step.
* `Party.Prog.loopMulti.erase_timed`: the costed loop erases to the loop.
* `Party.ProgE.emitT_time`, `Party.ProgE.awaitT_time`: the time of an activation is at most the
  cost of the path it runs.
* `Party.Prog.loopSys.timed_time`: the time of a loop step.
* `Party.Prog.loopMulti.start_time`, `Party.Prog.loopMulti.resume_time`,
  `Party.Prog.loopMulti.finish_time`: the graded bounds of the steps.
* `Party.Prog.loopMulti.timeBoundInv_timed`: the invariant time bound under a constant bound.
* `Party.Prog.loopMulti.timeBoundGraded_timed`: the graded time bound `2 * a + b`, `2 * b`.
* `Party.ProgE.eraseT_sampleTree_priced`, `Party.ProgE.LoopBoundGraded.sampleTree`: a priced
  body whose operations are distribution samples (`ProgE.AllOps ProgE.IsSample`) is a costed
  body under the tree interpretation `ProgE.sampleTree`, with the graded bound it has at the
  weight `Costed.weight`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Party

open CatCrypt.Core CatCrypt.Crypto.UCTransparent

namespace ProgE

variable {Op E O α γ δ : Type}

/-! ## Activations in costed trees and erasure -/

/-- The costed tree of a costed operation: `ι q` for an operation `q`, the step cost `c` for a
tick of `c` units. -/
noncomputable def runT (ι : Op → ℕ × SPTree.Timed ℕ) : Costed Op → ℕ × SPTree.Timed ℕ
  | .op q => ι q
  | .tick c => (c, .ret 0)

/-- The emit phase in costed trees: the operations up to the next `send o` run as their trees,
followed by `s o` at the rest; a return continues with `r`; a `recv` or a failure fails. -/
noncomputable def emitT (ι : Op → ℕ × SPTree.Timed ℕ)
    (s : O → ProgE (Costed Op) E O α → ℕ × SPTree.Timed γ) (r : α → ℕ × SPTree.Timed γ) :
    ProgE (Costed Op) E O α → ℕ × SPTree.Timed γ
  | .ret a => r a
  | .recv _ => (0, .fail)
  | .send o p => s o p
  | .opN q k => SPTree.Timed.delay (runT ι q).1 ((runT ι q).2.bind fun n => emitT ι s r (k n))
  | .fail => (0, .fail)

/-- The await phase in costed trees on the event `e`: the operations up to the next `recv` run
as their trees, the `recv` takes `e` and the emit phase follows with `s` and `rE`; a return
continues with `rA`; a `send` or a failure fails. -/
noncomputable def awaitT (ι : Op → ℕ × SPTree.Timed ℕ) (e : E)
    (s : O → ProgE (Costed Op) E O α → ℕ × SPTree.Timed γ) (rA rE : α → ℕ × SPTree.Timed γ) :
    ProgE (Costed Op) E O α → ℕ × SPTree.Timed γ
  | .ret a => rA a
  | .recv k => emitT ι s rE (k e)
  | .send _ _ => (0, .fail)
  | .opN q k =>
    SPTree.Timed.delay (runT ι q).1 ((runT ι q).2.bind fun n => awaitT ι e s rA rE (k n))
  | .fail => (0, .fail)

/-- One activation in costed trees of the costed program `p` on the event `e`, continuing with
`restart a e` when `p` returns `a` in the await phase: the residual and the output. -/
noncomputable def stepWithT (ι : Op → ℕ × SPTree.Timed ℕ)
    (restart : α → E → ℕ × SPTree.Timed (ProgE (Costed Op) E O α × O))
    (p : ProgE (Costed Op) E O α) (e : E) : ℕ × SPTree.Timed (ProgE (Costed Op) E O α × O) :=
  awaitT ι e (fun o q => (0, .ret (q, o))) (fun a => restart a e) (fun _ => (0, .fail)) p

/-- One activation in costed trees of a program that halts on return. -/
noncomputable def actT (ι : Op → ℕ × SPTree.Timed ℕ) (p : ProgE (Costed Op) E O α) (e : E) :
    ℕ × SPTree.Timed (ProgE (Costed Op) E O α × O) :=
  stepWithT ι (fun _ _ => (0, .fail)) p e

/-- The weight of a costed operation under `ι`: the step time of its tree. -/
noncomputable def weightT (ι : Op → ℕ × SPTree.Timed ℕ) (q : Costed Op) : ℕ :=
  SPTree.Timed.stepTime (runT ι q)

/-- The classical operation of `q`: the compiled tree of `ι q`. -/
noncomputable def opComp (ι : Op → ℕ × SPTree.Timed ℕ) (q : Op) : SPComp ℕ :=
  (ι q).2.erase.compile

/-- The erasure of a costed program under `ι`: the ticks removed and each operation `q`
replaced by its classical operation `opComp ι q`. -/
noncomputable def eraseT (ι : Op → ℕ × SPTree.Timed ℕ) (p : ProgE (Costed Op) E O α) :
    Prog E O α :=
  mapOp (opComp ι) (erase p)

/-- The compiled tree of a costed bind is the bind of the compiled trees. -/
theorem compile_delay_bind {β : Type} (c : ℕ) (t : SPTree.Timed β)
    (f : β → ℕ × SPTree.Timed γ) :
    (SPTree.Timed.delay c (t.bind f)).2.erase.compile =
      SPComp.bind t.erase.compile fun b => (f b).2.erase.compile := by
  simp only [SPTree.Timed.delay, SPTree.Timed.erase_bind, SPTree.compile_bind]

/-- A failing tree, compiled and followed by `g`, fails. -/
theorem compile_fail_bind {β : Type} (g : β → SPComp γ) :
    SPComp.bind (SPTree.Timed.fail : SPTree.Timed β).erase.compile g = SPComp.fail := by
  rw [SPTree.Timed.erase_fail, SPTree.compile_fail, SPComp.fail_bind]

/-- A returning tree, compiled and followed by `g`, is `g` at the returned value. -/
theorem compile_ret_bind {β : Type} (b : β) (g : β → SPComp γ) :
    SPComp.bind (SPTree.Timed.ret b).erase.compile g = g b := by
  rw [SPTree.Timed.erase_ret, SPTree.compile_ret, SPComp.pure_bind]

/-- A step-prefixed failing tree takes no time. -/
theorem stepTime_fail {β : Type} (c : ℕ) :
    SPTree.Timed.stepTime ((c, .fail) : ℕ × SPTree.Timed β) = c := by
  simp only [SPTree.Timed.stepTime, SPTree.Timed.time_fail, Nat.add_zero]

/-- **Erasure of the emit phase.** The emit phase in costed trees, compiled and followed by
`g`, is the emit phase of the erased program, when the continuations are related by
erasure. -/
theorem emitT_erase (ι : Op → ℕ × SPTree.Timed ℕ)
    (s : O → ProgE (Costed Op) E O α → ℕ × SPTree.Timed γ) (r : α → ℕ × SPTree.Timed γ)
    (s' : O → Prog E O α → SPComp δ) (r' : α → SPComp δ) (g : γ → SPComp δ)
    (hs : ∀ o q, SPComp.bind (s o q).2.erase.compile g = s' o (eraseT ι q))
    (hr : ∀ a, SPComp.bind (r a).2.erase.compile g = r' a) (p : ProgE (Costed Op) E O α) :
    SPComp.bind (emitT ι s r p).2.erase.compile g = emitK Prog.handler s' r' (eraseT ι p) := by
  induction p with
  | ret a => exact hr a
  | recv k ih => exact compile_fail_bind g
  | send o p ih => exact hs o p
  | opN q k ih =>
    cases q with
    | op q =>
      simp only [emitT, runT, compile_delay_bind, SPComp.bind_assoc, ih]
      rfl
    | tick c => exact ih 0
  | fail => exact compile_fail_bind g

/-- **Erasure of the await phase.** The await phase in costed trees, compiled and followed by
`g`, is the await phase of the erased program, when the continuations are related by
erasure. -/
theorem awaitT_erase (ι : Op → ℕ × SPTree.Timed ℕ) (e : E)
    (s : O → ProgE (Costed Op) E O α → ℕ × SPTree.Timed γ) (rA rE : α → ℕ × SPTree.Timed γ)
    (s' : O → Prog E O α → SPComp δ) (rA' rE' : α → SPComp δ) (g : γ → SPComp δ)
    (hs : ∀ o q, SPComp.bind (s o q).2.erase.compile g = s' o (eraseT ι q))
    (hA : ∀ a, SPComp.bind (rA a).2.erase.compile g = rA' a)
    (hE : ∀ a, SPComp.bind (rE a).2.erase.compile g = rE' a) (p : ProgE (Costed Op) E O α) :
    SPComp.bind (awaitT ι e s rA rE p).2.erase.compile g =
      awaitK Prog.handler e s' rA' rE' (eraseT ι p) := by
  induction p with
  | ret a => exact hA a
  | recv k ih => exact emitT_erase ι s rE s' rE' g hs hE (k e)
  | send o p ih => exact compile_fail_bind g
  | opN q k ih =>
    cases q with
    | op q =>
      simp only [awaitT, runT, compile_delay_bind, SPComp.bind_assoc, ih]
      rfl
    | tick c => exact ih 0
  | fail => exact compile_fail_bind g

/-- **Erasure of an activation with restart.** An activation in costed trees, compiled and its
residual erased, is the activation of the erased program, when the restarts are related by
erasure. -/
theorem stepWithT_erase (ι : Op → ℕ × SPTree.Timed ℕ)
    (restart : α → E → ℕ × SPTree.Timed (ProgE (Costed Op) E O α × O))
    (restart' : α → E → SPComp (Prog E O α × O))
    (hr : ∀ a e, SPComp.bind (restart a e).2.erase.compile
      (fun x => SPComp.pure (eraseT ι x.1, x.2)) = restart' a e)
    (p : ProgE (Costed Op) E O α) (e : E) :
    SPComp.bind (stepWithT ι restart p e).2.erase.compile
        (fun x => SPComp.pure (eraseT ι x.1, x.2)) =
      Prog.stepWith restart' (eraseT ι p) e :=
  awaitT_erase ι e _ _ _ (fun o q => SPComp.pure (q, o)) _ (fun _ => SPComp.fail) _
    (fun _ _ => compile_ret_bind _ _) (fun a => hr a e) (fun _ => compile_fail_bind _) p

/-- **Erasure of an activation.** An activation in costed trees of a program that halts on
return, compiled and its residual erased, is the activation of the erased program. -/
theorem actT_erase (ι : Op → ℕ × SPTree.Timed ℕ) (p : ProgE (Costed Op) E O α) (e : E) :
    SPComp.bind (actT ι p e).2.erase.compile (fun x => SPComp.pure (eraseT ι x.1, x.2)) =
      Prog.act (eraseT ι p) e :=
  stepWithT_erase ι _ _ (fun _ _ => compile_fail_bind _) p e

/-! ## The time of an activation -/

/-- **Time of the emit phase.** When `p` costs at most `t ≤ T` and returns values of `P`, and
the continuations at outputs (with residuals of cost at most `T`) and at returns of `P` cost at
most `D` and return values of `R`, the emit phase in costed trees costs at most `t + D` and
returns values of `R`. -/
theorem emitT_time (ι : Op → ℕ × SPTree.Timed ℕ) {P : α → Prop} {R : γ → Prop} {T D : ℕ}
    (s : O → ProgE (Costed Op) E O α → ℕ × SPTree.Timed γ) (r : α → ℕ × SPTree.Timed γ)
    (hs : ∀ o q u, u ≤ T → Bound (weightT ι) q u P →
      SPTree.Timed.stepTime (s o q) ≤ D ∧ SPTree.Timed.AllRet R (s o q).2)
    (hr : ∀ a, P a → SPTree.Timed.stepTime (r a) ≤ D ∧ SPTree.Timed.AllRet R (r a).2)
    (p : ProgE (Costed Op) E O α) (t : ℕ) (ht : t ≤ T) (hp : Bound (weightT ι) p t P) :
    SPTree.Timed.stepTime (emitT ι s r p) ≤ t + D ∧
      SPTree.Timed.AllRet R (emitT ι s r p).2 := by
  induction p generalizing t with
  | ret a =>
    have := hr a hp
    exact ⟨by simp only [emitT]; omega, this.2⟩
  | recv k ih => exact ⟨by simp only [emitT, stepTime_fail]; omega, trivial⟩
  | send o p ih =>
    have := hs o p (t - 1) (by omega) hp.2
    exact ⟨by simp only [emitT]; omega, this.2⟩
  | opN q k ih =>
    have hk : ∀ n, SPTree.Timed.stepTime (emitT ι s r (k n)) ≤ t - weightT ι q + D ∧
        SPTree.Timed.AllRet R (emitT ι s r (k n)).2 :=
      fun n => ih n (t - weightT ι q) (by have := hp.1; omega) (hp.2 n)
    have hb := SPTree.Timed.stepTime_bind_le (runT ι q).2 (fun n => emitT ι s r (k n))
      (t - weightT ι q + D) fun n => (hk n).1
    have hw : weightT ι q ≤ t := hp.1
    simp only [weightT, SPTree.Timed.stepTime] at hw hb
    refine ⟨?_, SPTree.Timed.allRet_bind_of
      (SPTree.Timed.allRet_of_forall (fun n => (hk n).2) _)⟩
    simp only [emitT, SPTree.Timed.stepTime, SPTree.Timed.delay] at hb ⊢
    omega
  | fail => exact ⟨by simp only [emitT, stepTime_fail]; omega, trivial⟩

/-- **Time of the await phase.** When `p` costs at most `t ≤ T` and returns values of `P`, and
the continuations cost at most `D` and return values of `R`, the await phase in costed trees
costs at most `t + D` and returns values of `R`. -/
theorem awaitT_time (ι : Op → ℕ × SPTree.Timed ℕ) {P : α → Prop} {R : γ → Prop} {T D : ℕ}
    (e : E) (s : O → ProgE (Costed Op) E O α → ℕ × SPTree.Timed γ)
    (rA rE : α → ℕ × SPTree.Timed γ)
    (hs : ∀ o q u, u ≤ T → Bound (weightT ι) q u P →
      SPTree.Timed.stepTime (s o q) ≤ D ∧ SPTree.Timed.AllRet R (s o q).2)
    (hA : ∀ a, P a → SPTree.Timed.stepTime (rA a) ≤ D ∧ SPTree.Timed.AllRet R (rA a).2)
    (hE : ∀ a, P a → SPTree.Timed.stepTime (rE a) ≤ D ∧ SPTree.Timed.AllRet R (rE a).2)
    (p : ProgE (Costed Op) E O α) (t : ℕ) (ht : t ≤ T) (hp : Bound (weightT ι) p t P) :
    SPTree.Timed.stepTime (awaitT ι e s rA rE p) ≤ t + D ∧
      SPTree.Timed.AllRet R (awaitT ι e s rA rE p).2 := by
  induction p generalizing t with
  | ret a =>
    have := hA a hp
    exact ⟨by simp only [awaitT]; omega, this.2⟩
  | recv k ih =>
    have := emitT_time ι s rE hs hE (k e) (t - 1) (by omega) (hp.2 e)
    exact ⟨by simp only [awaitT]; omega, this.2⟩
  | send o p ih => exact ⟨by simp only [awaitT, stepTime_fail]; omega, trivial⟩
  | opN q k ih =>
    have hk : ∀ n, SPTree.Timed.stepTime (awaitT ι e s rA rE (k n)) ≤ t - weightT ι q + D ∧
        SPTree.Timed.AllRet R (awaitT ι e s rA rE (k n)).2 :=
      fun n => ih n (t - weightT ι q) (by have := hp.1; omega) (hp.2 n)
    have hb := SPTree.Timed.stepTime_bind_le (runT ι q).2 (fun n => awaitT ι e s rA rE (k n))
      (t - weightT ι q + D) fun n => (hk n).1
    have hw : weightT ι q ≤ t := hp.1
    simp only [weightT, SPTree.Timed.stepTime] at hw hb
    refine ⟨?_, SPTree.Timed.allRet_bind_of
      (SPTree.Timed.allRet_of_forall (fun n => (hk n).2) _)⟩
    simp only [awaitT, SPTree.Timed.stepTime, SPTree.Timed.delay] at hb ⊢
    omega
  | fail => exact ⟨by simp only [awaitT, stepTime_fail]; omega, trivial⟩

end ProgE

/-! ## The costed loop -/

namespace Prog

variable {Op E O Q A σ β β' : Type}

/-- **The costed step of a loop**: an activation in costed trees of the residual of the current
iteration, restarting with `bodyT s` when it returns `s`. -/
noncomputable def loopSys.timed (ι : Op → ℕ × SPTree.Timed ℕ)
    (bodyT : σ → ProgE (Costed Op) E O σ) (p : ProgE (Costed Op) E O σ) (e : E) :
    ℕ × SPTree.Timed (ProgE (Costed Op) E O σ × O) :=
  ProgE.stepWithT ι (fun s e => ProgE.actT ι (bodyT s) e) p e

/-- **Erasure of a costed loop step.** When `bodyT` erases to `body`, the costed step of the
loop, compiled and its residual erased, is the step of the loop of `body`. -/
theorem loopSys.step_erase_timed (ι : Op → ℕ × SPTree.Timed ℕ)
    (bodyT : σ → ProgE (Costed Op) E O σ) (body : σ → Prog E O σ) (s₀ : σ)
    (hbody : ∀ s, ProgE.eraseT ι (bodyT s) = body s) (p : ProgE (Costed Op) E O σ) (e : E) :
    SPComp.bind (loopSys.timed ι bodyT p e).2.erase.compile
        (fun x => SPComp.pure (ProgE.eraseT ι x.1, x.2)) =
      (loopSys body s₀).step (ProgE.eraseT ι p) e :=
  ProgE.stepWithT_erase ι _ _ (fun s e => by rw [ProgE.actT_erase, hbody]) p e

/-- The costed guard of a step, the mirror of `MultiHybrid.guardNF`: the step `x` when its
compiled tree, mapped by `g`, never fails, and the return of `d` otherwise. -/
noncomputable def guardT (g : β → β') (x : ℕ × SPTree.Timed β) (d : β) :
    ℕ × SPTree.Timed β := by
  classical
  exact if SPComp.NoFail (SPComp.bind x.2.erase.compile fun y => SPComp.pure (g y)) then x
    else (0, .ret d)

/-- The costed guard erases to `MultiHybrid.guardNF`. -/
theorem guardT_erase (g : β → β') (x : ℕ × SPTree.Timed β) (d : β) :
    SPComp.bind (guardT g x d).2.erase.compile (fun y => SPComp.pure (g y)) =
      MultiHybrid.guardNF (SPComp.bind x.2.erase.compile fun y => SPComp.pure (g y)) (g d) := by
  unfold guardT MultiHybrid.guardNF
  split_ifs
  · rfl
  · exact ProgE.compile_ret_bind _ _

/-- The costed guard costs at most what its step costs, and returns its returns or `d`. -/
theorem guardT_time {R : β → Prop} {T : ℕ} (g : β → β') (x : ℕ × SPTree.Timed β) (d : β)
    (hx : SPTree.Timed.stepTime x ≤ T ∧ SPTree.Timed.AllRet R x.2) (hd : R d) :
    SPTree.Timed.stepTime (guardT g x d) ≤ T ∧ SPTree.Timed.AllRet R (guardT g x d).2 := by
  unfold guardT
  split_ifs
  · exact hx
  · exact ⟨by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret], hd⟩

/-- The costed outer output of a final decision, the mirror of `MultiHybrid.toOut`. -/
noncomputable def toOutT : β × (Q ⊕ O) → ℕ × SPTree.Timed (β × O)
  | (t, .inr o) => (0, .ret (t, o))
  | (_, .inl _) => (0, .fail)

/-- The costed outer output erases to `MultiHybrid.toOut`. -/
theorem toOutT_erase (g : β → β') (y : β × (Q ⊕ O)) :
    SPComp.bind (toOutT y).2.erase.compile (fun z => SPComp.pure (g z.1, z.2)) =
      MultiHybrid.toOut (g y.1, y.2) := by
  rcases y with ⟨t, q | o⟩
  · exact ProgE.compile_fail_bind _
  · exact ProgE.compile_ret_bind _ _

/-- The costed `start` step of a loop, guarded. -/
noncomputable def loopMulti.startT [Inhabited O] (ι : Op → ℕ × SPTree.Timed ℕ)
    (bodyT : σ → ProgE (Costed Op) (E ⊕ A) (Q ⊕ O) σ) (p : ProgE (Costed Op) (E ⊕ A) (Q ⊕ O) σ)
    (x : E ⊕ A) : ℕ × SPTree.Timed (ProgE (Costed Op) (E ⊕ A) (Q ⊕ O) σ × (Q ⊕ O)) :=
  guardT (fun y => (ProgE.eraseT ι y.1, y.2)) (loopSys.timed ι bodyT p x) (p, .inr default)

/-- The costed `finish` step of a loop, guarded: the step followed by its outer output. -/
noncomputable def loopMulti.finishT [Inhabited O] (ι : Op → ℕ × SPTree.Timed ℕ)
    (bodyT : σ → ProgE (Costed Op) (E ⊕ A) (Q ⊕ O) σ) (p : ProgE (Costed Op) (E ⊕ A) (Q ⊕ O) σ)
    (a : A) : ℕ × SPTree.Timed (ProgE (Costed Op) (E ⊕ A) (Q ⊕ O) σ × O) :=
  guardT (fun y => (ProgE.eraseT ι y.1, y.2))
    (SPTree.Timed.delay (loopSys.timed ι bodyT p (.inr a)).1
      ((loopSys.timed ι bodyT p (.inr a)).2.bind toOutT)) (p, default)

/-- **The costed loop simulator**: the costed multi-call simulator of the loop of the costed body
`bodyT` from `s₀` with fuel `n`, on costed residual programs. Its steps are the guarded costed
steps of the loop on outer events and answers. -/
noncomputable def loopMulti.timed [Inhabited O] (ι : Op → ℕ × SPTree.Timed ℕ)
    (bodyT : σ → ProgE (Costed Op) (E ⊕ A) (Q ⊕ O) σ) (s₀ : σ) (n : ℕ) :
    MultiHybrid.Timed (ProgE (Costed Op) (E ⊕ A) (Q ⊕ O) σ) E O Q A where
  init := .ret s₀
  fuel := n
  start p e := (loopMulti.startT ι bodyT p (.inl e)).2
  startCost p e := (loopMulti.startT ι bodyT p (.inl e)).1
  resume p a := (loopMulti.startT ι bodyT p (.inr a)).2
  resumeCost p a := (loopMulti.startT ι bodyT p (.inr a)).1
  finish p a := (loopMulti.finishT ι bodyT p a).2
  finishCost p a := (loopMulti.finishT ι bodyT p a).1

/-- **Erasure of the costed loop simulator.** When the costed body `bodyT` erases to `body`, the
costed loop simulator erases through `ProgE.eraseT ι` to the loop of `body`. -/
theorem loopMulti.erase_timed [Inhabited O] (ι : Op → ℕ × SPTree.Timed ℕ)
    (bodyT : σ → ProgE (Costed Op) (E ⊕ A) (Q ⊕ O) σ) (body : σ → Prog (E ⊕ A) (Q ⊕ O) σ)
    (hbody : ∀ s, ProgE.eraseT ι (bodyT s) = body s) (s₀ : σ) (n : ℕ) :
    MultiHybrid.Timed.ErasesHat (ProgE (Costed Op) (E ⊕ A) (Q ⊕ O) σ) E O Q A
      (ProgE.eraseT ι) id id id id (loopMulti.timed ι bodyT s₀ n) (loopMulti body s₀ n) := by
  refine ⟨rfl, rfl, fun p e => ?_, fun p a => ?_, fun p a => ?_⟩
  · simp only [Sum.map_id_id, id]
    exact (guardT_erase _ _ _).trans (congrArg (MultiHybrid.guardNF · _)
      (loopSys.step_erase_timed ι bodyT body s₀ hbody p _))
  · simp only [Sum.map_id_id, id]
    exact (guardT_erase _ _ _).trans (congrArg (MultiHybrid.guardNF · _)
      (loopSys.step_erase_timed ι bodyT body s₀ hbody p _))
  · simp only [id]
    refine (guardT_erase _ _ _).trans (congrArg (MultiHybrid.guardNF · _) ?_)
    rw [ProgE.compile_delay_bind, SPComp.bind_assoc,
      ← loopSys.step_erase_timed ι bodyT body s₀ hbody p (.inr a), SPComp.bind_assoc]
    simp only [SPComp.pure_bind, toOutT_erase]

/-! ## The time of the costed loop -/

/-- The invariant of a residual program in the `k`-th iteration of a loop with the graded
invariant `Inv`: the return of a state of `Inv k`, before the iteration, or a suffix of the
iteration of remaining cost at most `a + b * k` that returns states of `Inv (k + 1)`. -/
def loopMulti.IterInv (ι : Op → ℕ × SPTree.Timed ℕ) (Inv : ℕ → σ → Prop) (a b k : ℕ)
    (p : ProgE (Costed Op) E O σ) : Prop :=
  (∃ s, p = .ret s ∧ Inv k s) ∨ ProgE.Bound (ProgE.weightT ι) p (a + b * k) (Inv (k + 1))

/-- The invariant of a residual program after `j` activations: the invariant of the `k`-th
iteration for some `k ≤ j`. -/
def loopMulti.ActInv (ι : Op → ℕ × SPTree.Timed ℕ) (Inv : ℕ → σ → Prop) (a b j : ℕ)
    (p : ProgE (Costed Op) E O σ) : Prop :=
  ∃ k ≤ j, loopMulti.IterInv ι Inv a b k p

/-- An iteration from a state of `Inv i`, run up to its first output, costs at most `a + b * i`
and leaves a residual of the `i`-th iteration. -/
theorem loopSys.actT_time (ι : Op → ℕ × SPTree.Timed ℕ) (bodyT : σ → ProgE (Costed Op) E O σ)
    {Inv : ℕ → σ → Prop} {a b : ℕ}
    (h : ∀ i s, Inv i s → ProgE.Bound (ProgE.weightT ι) (bodyT s) (a + b * i) (Inv (i + 1)))
    {i : ℕ} {s : σ} (hs : Inv i s) (e : E) :
    SPTree.Timed.stepTime (ProgE.actT ι (bodyT s) e) ≤ a + b * i ∧
      SPTree.Timed.AllRet (fun y => loopMulti.IterInv ι Inv a b i y.1)
        (ProgE.actT ι (bodyT s) e).2 := by
  have := ProgE.awaitT_time ι (P := Inv (i + 1))
    (R := fun y : ProgE (Costed Op) E O σ × O => loopMulti.IterInv ι Inv a b i y.1)
    (T := a + b * i) (D := 0) e (fun o q => (0, .ret (q, o))) (fun _ => (0, .fail))
    (fun _ => (0, .fail))
    (fun o q u hu hq => ⟨by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret],
      Or.inr (hq.mono hu fun _ => id)⟩)
    (fun _ _ => ⟨by simp [ProgE.stepTime_fail], trivial⟩)
    (fun _ _ => ⟨by simp [ProgE.stepTime_fail], trivial⟩) (bodyT s) (a + b * i) le_rfl (h i s hs)
  exact ⟨(Nat.add_zero (a + b * i)) ▸ this.1, this.2⟩

/-- **Time of a costed loop step.** From a residual of the `k`-th iteration, a step finishes at
most that iteration and runs the next one up to its first output: it costs at most
`2 * a + b + 2 * b * k` and leaves a residual of the `k`-th or the `(k + 1)`-th iteration. -/
theorem loopSys.timed_time (ι : Op → ℕ × SPTree.Timed ℕ) (bodyT : σ → ProgE (Costed Op) E O σ)
    {Inv : ℕ → σ → Prop} {a b : ℕ}
    (h : ∀ i s, Inv i s → ProgE.Bound (ProgE.weightT ι) (bodyT s) (a + b * i) (Inv (i + 1)))
    {k : ℕ} {p : ProgE (Costed Op) E O σ} (hp : loopMulti.IterInv ι Inv a b k p) (e : E) :
    SPTree.Timed.stepTime (loopSys.timed ι bodyT p e) ≤ 2 * a + b + 2 * b * k ∧
      SPTree.Timed.AllRet (fun y => loopMulti.IterInv ι Inv a b k y.1 ∨
        loopMulti.IterInv ι Inv a b (k + 1) y.1) (loopSys.timed ι bodyT p e).2 := by
  have hk : b * (k + 1) = b * k + b := by ring
  rcases hp with ⟨s, rfl, hs⟩ | hp
  · have := loopSys.actT_time ι bodyT h hs e
    refine ⟨?_, SPTree.Timed.allRet_mono (fun _ hy => Or.inl hy) _ this.2⟩
    have h1 := this.1
    change SPTree.Timed.stepTime (ProgE.actT ι (bodyT s) e) ≤ _
    nlinarith
  · have := ProgE.awaitT_time ι (P := Inv (k + 1))
      (R := fun y : ProgE (Costed Op) E O σ × O => loopMulti.IterInv ι Inv a b k y.1 ∨
        loopMulti.IterInv ι Inv a b (k + 1) y.1)
      (T := a + b * k) (D := a + b * (k + 1)) e (fun o q => (0, .ret (q, o)))
      (fun s' => ProgE.actT ι (bodyT s') e) (fun _ => (0, .fail))
      (fun o q u hu hq => ⟨by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret],
        Or.inl (Or.inr (hq.mono hu fun _ => id))⟩)
      (fun s' hs' => ⟨(loopSys.actT_time ι bodyT h hs' e).1,
        SPTree.Timed.allRet_mono (fun _ hy => Or.inr hy) _
          (loopSys.actT_time ι bodyT h hs' e).2⟩)
      (fun _ _ => ⟨by simp [ProgE.stepTime_fail], trivial⟩) p (a + b * k) le_rfl hp
    refine ⟨?_, this.2⟩
    have h1 := this.1
    change SPTree.Timed.stepTime (ProgE.awaitT ι e _ _ _ p) ≤ _
    nlinarith

/-- A guarded costed loop step from a state of `ActInv j` costs at most
`(2 * a + b) + 2 * b * j` and returns states of `ActInv (j + 1)`. -/
theorem loopMulti.startT_time [Inhabited O] (ι : Op → ℕ × SPTree.Timed ℕ)
    (bodyT : σ → ProgE (Costed Op) (E ⊕ A) (Q ⊕ O) σ) {Inv : ℕ → σ → Prop} {a b : ℕ}
    (h : ∀ i s, Inv i s → ProgE.Bound (ProgE.weightT ι) (bodyT s) (a + b * i) (Inv (i + 1)))
    {j : ℕ} {p : ProgE (Costed Op) (E ⊕ A) (Q ⊕ O) σ} (hp : loopMulti.ActInv ι Inv a b j p)
    (x : E ⊕ A) :
    SPTree.Timed.stepTime (loopMulti.startT ι bodyT p x) ≤ (2 * a + b) + 2 * b * j ∧
      SPTree.Timed.AllRet (fun y => loopMulti.ActInv ι Inv a b (j + 1) y.1)
        (loopMulti.startT ι bodyT p x).2 := by
  obtain ⟨k, hkj, hk⟩ := hp
  have := loopSys.timed_time ι bodyT h hk x
  refine guardT_time _ _ _ ⟨le_trans this.1 ?_, SPTree.Timed.allRet_mono
    (fun y hy => hy.elim (fun h' => ⟨k, by omega, h'⟩) fun h' => ⟨k + 1, by omega, h'⟩) _
    this.2⟩ ⟨k, by omega, hk⟩
  have : 2 * b * k ≤ 2 * b * j := Nat.mul_le_mul_left _ hkj
  omega

/-- The guarded costed `finish` step from a state of `ActInv j` costs at most
`(2 * a + b) + 2 * b * j` and returns states of `ActInv (j + 1)`. -/
theorem loopMulti.finishT_time [Inhabited O] (ι : Op → ℕ × SPTree.Timed ℕ)
    (bodyT : σ → ProgE (Costed Op) (E ⊕ A) (Q ⊕ O) σ) {Inv : ℕ → σ → Prop} {a b : ℕ}
    (h : ∀ i s, Inv i s → ProgE.Bound (ProgE.weightT ι) (bodyT s) (a + b * i) (Inv (i + 1)))
    {j : ℕ} {p : ProgE (Costed Op) (E ⊕ A) (Q ⊕ O) σ} (hp : loopMulti.ActInv ι Inv a b j p)
    (x : A) :
    SPTree.Timed.stepTime (loopMulti.finishT ι bodyT p x) ≤ (2 * a + b) + 2 * b * j ∧
      SPTree.Timed.AllRet (fun y => loopMulti.ActInv ι Inv a b (j + 1) y.1)
        (loopMulti.finishT ι bodyT p x).2 := by
  obtain ⟨k, hkj, hk⟩ := hp
  have := loopSys.timed_time ι bodyT h hk (.inr x)
  have hout : ∀ y : ProgE (Costed Op) (E ⊕ A) (Q ⊕ O) σ × (Q ⊕ O),
      SPTree.Timed.stepTime (toOutT y) ≤ 0 := by
    rintro ⟨t, q | o⟩
    · exact (ProgE.stepTime_fail 0).le
    · simp [toOutT, SPTree.Timed.stepTime, SPTree.Timed.time_ret]
  have hb := SPTree.Timed.stepTime_bind_le (loopSys.timed ι bodyT p (.inr x)).2 toOutT 0 hout
  have hmono : 2 * b * k ≤ 2 * b * j := Nat.mul_le_mul_left _ hkj
  refine guardT_time _ _ _ ⟨?_, SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_mono
    (fun y hy => ?_) _ this.2)⟩ ⟨k, by omega, hk⟩
  · have h1 := this.1
    simp only [SPTree.Timed.stepTime_delay]
    simp only [SPTree.Timed.stepTime] at h1 hb ⊢
    omega
  · rcases y with ⟨t, q | o⟩
    · trivial
    · exact hy.elim (fun h' => ⟨k, by omega, h'⟩) fun h' => ⟨k + 1, by omega, h'⟩

/-- **Graded time of the `start` step of the costed loop simulator.** Under the graded bound
of the costed body, the `start` step from a state of `ActInv j` costs at most
`(2 * a + b) + 2 * b * j` and returns states of `ActInv (j + 1)`. -/
theorem loopMulti.start_time [Inhabited O] (ι : Op → ℕ × SPTree.Timed ℕ)
    (bodyT : σ → ProgE (Costed Op) (E ⊕ A) (Q ⊕ O) σ) (s₀ : σ) (n : ℕ) {Inv : ℕ → σ → Prop}
    {a b : ℕ} (h : ProgE.LoopBoundGraded (ProgE.weightT ι) bodyT s₀ Inv a b) {j : ℕ}
    {p : ProgE (Costed Op) (E ⊕ A) (Q ⊕ O) σ} (hp : loopMulti.ActInv ι Inv a b j p) (e : E) :
    SPTree.Timed.stepTime ((loopMulti.timed ι bodyT s₀ n).startCost p e,
        (loopMulti.timed ι bodyT s₀ n).start p e) ≤ (2 * a + b) + 2 * b * j ∧
      SPTree.Timed.AllRet (fun y => loopMulti.ActInv ι Inv a b (j + 1) y.1)
        ((loopMulti.timed ι bodyT s₀ n).start p e) :=
  loopMulti.startT_time ι bodyT h.2 hp (.inl e)

/-- **Graded time of the `resume` step of the costed loop simulator.** -/
theorem loopMulti.resume_time [Inhabited O] (ι : Op → ℕ × SPTree.Timed ℕ)
    (bodyT : σ → ProgE (Costed Op) (E ⊕ A) (Q ⊕ O) σ) (s₀ : σ) (n : ℕ) {Inv : ℕ → σ → Prop}
    {a b : ℕ} (h : ProgE.LoopBoundGraded (ProgE.weightT ι) bodyT s₀ Inv a b) {j : ℕ}
    {p : ProgE (Costed Op) (E ⊕ A) (Q ⊕ O) σ} (hp : loopMulti.ActInv ι Inv a b j p) (x : A) :
    SPTree.Timed.stepTime ((loopMulti.timed ι bodyT s₀ n).resumeCost p x,
        (loopMulti.timed ι bodyT s₀ n).resume p x) ≤ (2 * a + b) + 2 * b * j ∧
      SPTree.Timed.AllRet (fun y => loopMulti.ActInv ι Inv a b (j + 1) y.1)
        ((loopMulti.timed ι bodyT s₀ n).resume p x) :=
  loopMulti.startT_time ι bodyT h.2 hp (.inr x)

/-- **Graded time of the `finish` step of the costed loop simulator.** -/
theorem loopMulti.finish_time [Inhabited O] (ι : Op → ℕ × SPTree.Timed ℕ)
    (bodyT : σ → ProgE (Costed Op) (E ⊕ A) (Q ⊕ O) σ) (s₀ : σ) (n : ℕ) {Inv : ℕ → σ → Prop}
    {a b : ℕ} (h : ProgE.LoopBoundGraded (ProgE.weightT ι) bodyT s₀ Inv a b) {j : ℕ}
    {p : ProgE (Costed Op) (E ⊕ A) (Q ⊕ O) σ} (hp : loopMulti.ActInv ι Inv a b j p) (x : A) :
    SPTree.Timed.stepTime ((loopMulti.timed ι bodyT s₀ n).finishCost p x,
        (loopMulti.timed ι bodyT s₀ n).finish p x) ≤ (2 * a + b) + 2 * b * j ∧
      SPTree.Timed.AllRet (fun y => loopMulti.ActInv ι Inv a b (j + 1) y.1)
        ((loopMulti.timed ι bodyT s₀ n).finish p x) :=
  loopMulti.finishT_time ι bodyT h.2 hp x

/-- The initial state of the costed loop simulator satisfies `ActInv 0`. -/
theorem loopMulti.init_actInv [Inhabited O] (ι : Op → ℕ × SPTree.Timed ℕ)
    (bodyT : σ → ProgE (Costed Op) (E ⊕ A) (Q ⊕ O) σ) (s₀ : σ) (n : ℕ) {Inv : ℕ → σ → Prop}
    {a b : ℕ} (h : ProgE.LoopBoundGraded (ProgE.weightT ι) bodyT s₀ Inv a b) :
    loopMulti.ActInv ι Inv a b 0 (loopMulti.timed ι bodyT s₀ n).init :=
  ⟨0, le_rfl, Or.inl ⟨s₀, rfl, h.1⟩⟩

/-- **Time certificate of the costed loop simulator under a constant bound.** When the initial
state satisfies `Inv` and the costed body costs at most `a` from every state of `Inv` and
returns states of `Inv`, each step of the costed loop simulator costs at most `2 * a` on the
states reachable through `ActInv`. -/
theorem loopMulti.timeBoundInv_timed [Inhabited O] (ι : Op → ℕ × SPTree.Timed ℕ)
    (bodyT : σ → ProgE (Costed Op) (E ⊕ A) (Q ⊕ O) σ) (s₀ : σ) (n : ℕ) {Inv : σ → Prop}
    {a : ℕ} (h0 : Inv s₀) (h : ∀ s, Inv s → ProgE.Bound (ProgE.weightT ι) (bodyT s) a Inv) :
    (loopMulti.timed ι bodyT s₀ n).TimeBoundInv
      (fun p => ∃ j, loopMulti.ActInv ι (fun _ => Inv) a 0 j p) (2 * a) (2 * a) (2 * a) := by
  have hg := ProgE.LoopBoundGraded.of_bound (w := ProgE.weightT ι) (body := bodyT) h0 h
  refine ⟨⟨0, loopMulti.init_actInv ι bodyT s₀ n hg⟩, fun p e ⟨j, hp⟩ => ?_,
    fun p x ⟨j, hp⟩ => ?_, fun p x ⟨j, hp⟩ => ?_⟩
  · have := loopMulti.start_time ι bodyT s₀ n hg hp e
    exact ⟨by simpa using this.1, SPTree.Timed.allRet_mono (fun _ hy => ⟨j + 1, hy⟩) _ this.2⟩
  · have := loopMulti.resume_time ι bodyT s₀ n hg hp x
    exact ⟨by simpa using this.1, SPTree.Timed.allRet_mono (fun _ hy => ⟨j + 1, hy⟩) _ this.2⟩
  · have := loopMulti.finish_time ι bodyT s₀ n hg hp x
    exact ⟨by simpa using this.1, SPTree.Timed.allRet_mono (fun _ hy => ⟨j + 1, hy⟩) _ this.2⟩

/-- **Graded time certificate of the costed loop simulator.** Under the graded bound `a`, `b`
of the costed body, the costed loop simulator has the graded time bound `2 * a + b`, `2 * b` on
the invariant `ActInv`: the `j`-th activation costs at most `(2 * a + b) + 2 * b * j`. -/
theorem loopMulti.timeBoundGraded_timed [Inhabited O] (ι : Op → ℕ × SPTree.Timed ℕ)
    (bodyT : σ → ProgE (Costed Op) (E ⊕ A) (Q ⊕ O) σ) (s₀ : σ) (n : ℕ) {Inv : ℕ → σ → Prop}
    {a b : ℕ} (h : ProgE.LoopBoundGraded (ProgE.weightT ι) bodyT s₀ Inv a b) :
    (loopMulti.timed ι bodyT s₀ n).TimeBoundGraded (loopMulti.ActInv ι Inv a b)
      (2 * a + b) (2 * b) := by
  refine ⟨loopMulti.init_actInv ι bodyT s₀ n h, fun j p e hp => ?_, fun j p x hp => ?_,
    fun j p x hp => ?_⟩
  · have := loopMulti.start_time ι bodyT s₀ n h hp e
    exact this
  · have := loopMulti.resume_time ι bodyT s₀ n h hp x
    exact this
  · have := loopMulti.finish_time ι bodyT s₀ n h hp x
    exact this

end Prog

/-! ## Bodies whose operations are distribution samples -/

namespace ProgE

variable {Op E O α β : Type}

/-- Every effect operation of `p` satisfies `P`. -/
def AllOps (P : Op → Prop) : ProgE Op E O α → Prop
  | .ret _ => True
  | .recv k => ∀ e, AllOps P (k e)
  | .send _ p => AllOps P p
  | .opN q k => P q ∧ ∀ n, AllOps P (k n)
  | .fail => True

/-- `AllOps` along `bind`. -/
theorem allOps_bind {P : Op → Prop} {p : ProgE Op E O α} {f : α → ProgE Op E O β}
    (hp : AllOps P p) (hf : ∀ a, AllOps P (f a)) : AllOps P (p.bind f) := by
  induction p with
  | ret a => exact hf a
  | recv k ih => exact fun e => ih e (hp e)
  | send o p ih => exact ih hp
  | opN q k ih => exact ⟨hp.1, fun n => ih n (hp.2 n)⟩
  | fail => trivial

/-- A map of effect operations that fixes every operation of `p` fixes `p`. -/
theorem mapOp_eq_self (f : Op → Op) (p : ProgE Op E O α) (h : AllOps (fun q => f q = q) p) :
    mapOp f p = p := by
  induction p with
  | ret a => rfl
  | recv k ih => simp only [mapOp, fun e => ih e (h e)]
  | send o p ih => simp only [mapOp, ih h]
  | opN q k ih => simp only [mapOp, h.1, fun n => ih n (h.2 n)]
  | fail => rfl

/-- A time bound at a weight is a time bound at every smaller weight. -/
theorem Bound.mono_weight {w w' : Op → ℕ} (hw : ∀ q, w' q ≤ w q) {p : ProgE Op E O α} {t : ℕ}
    {P : α → Prop} (h : Bound w p t P) : Bound w' p t P := by
  induction p generalizing t with
  | ret a => exact h
  | recv k ih => exact ⟨h.1, fun e => ih e (h.2 e)⟩
  | send o p ih => exact ⟨h.1, ih h.2⟩
  | opN q k ih =>
    refine ⟨le_trans (hw q) h.1, fun n => (ih n (h.2 n)).mono ?_ fun _ => id⟩
    have := hw q
    omega
  | fail => trivial

/-- A graded loop bound at a weight is a graded loop bound at every smaller weight. -/
theorem LoopBoundGraded.mono_weight {σ : Type} {w w' : Op → ℕ} (hw : ∀ q, w' q ≤ w q)
    {body : σ → ProgE Op E O σ} {s₀ : σ} {Inv : ℕ → σ → Prop} {a b : ℕ}
    (h : LoopBoundGraded w body s₀ Inv a b) : LoopBoundGraded w' body s₀ Inv a b :=
  ⟨h.1, fun i s hs => (h.2 i s hs).mono_weight hw⟩

/-- A classical operation is a distribution sample: the lift of a sub-distribution, which does
not read or write the heap. -/
def IsSample (q : SPComp ℕ) : Prop := ∃ μ : Prob.SDistr ℕ, q = liftSDistr μ

/-- The tree interpretation of distribution samples: a sample of a sub-distribution `μ` is the
one-node tree sampling `μ`; any other operation is the failing tree. -/
noncomputable def sampleTree (q : SPComp ℕ) : ℕ × SPTree.Timed ℕ := by
  classical
  exact if h : IsSample q then (0, .sampleDist ℕ h.choose (fun _ => 0) .ret) else (0, .fail)

/-- The tree interpretation of a distribution sample compiles to the sample. -/
theorem opComp_sampleTree {q : SPComp ℕ} (h : IsSample q) : opComp sampleTree q = q := by
  unfold opComp sampleTree
  simp only [h, ↓reduceDIte, SPTree.Timed.erase_sampleDist, SPTree.Timed.erase_ret,
    SPTree.compile, SPComp.bind_pure]
  exact h.choose_spec.symm

/-- Each operation of the tree interpretation of samples weighs at most one unit. -/
theorem weightT_sampleTree_le (q : Costed (SPComp ℕ)) :
    weightT sampleTree q ≤ Costed.weight q := by
  rcases q with q | c
  · simp only [weightT, runT, Costed.weight, sampleTree]
    split
    · simp [SPTree.Timed.stepTime, SPTree.Timed.time_sampleDist, SPTree.Timed.time_ret]
    · simp [ProgE.stepTime_fail]
  · simp [weightT, runT, Costed.weight, SPTree.Timed.stepTime, SPTree.Timed.time_ret]

/-- `AllOps` of a weaker predicate. -/
theorem AllOps.mono {P P' : Op → Prop} (hP : ∀ q, P q → P' q) {p : ProgE Op E O α}
    (h : AllOps P p) : AllOps P' p := by
  induction p with
  | ret a => trivial
  | recv k ih => exact fun e => ih e (h e)
  | send o p ih => exact ih h
  | opN q k ih => exact ⟨hP q h.1, fun n => ih n (h.2 n)⟩
  | fail => trivial

/-- A mapped lift of a sub-distribution is a distribution sample. -/
theorem isSample_map_liftSDistr {γ : Type} (f : γ → ℕ) (d : Prob.SDistr γ) :
    IsSample (SPComp.map f (liftSDistr d)) :=
  ⟨d.bind fun b => Prob.SDistr.pure (f b), by
    funext h
    simp only [SPComp.map, SPComp.bind, liftSDistr, SPComp.pure, Prob.SDistr.bind_assoc,
      Prob.SDistr.pure_bind]⟩

/-- **Erasure of a priced body of samples.** When every operation of `body s` is a
distribution sample, the priced form erases under `sampleTree` to `body s`. -/
theorem eraseT_sampleTree_priced {σ : Type} (price : σ → ℕ) (body : σ → Prog E O σ) (s : σ)
    (h : AllOps IsSample (body s)) : eraseT sampleTree (priced price body s) = body s := by
  rw [eraseT, erase_priced]
  exact mapOp_eq_self _ _ (h.mono fun _ hq => opComp_sampleTree hq)

/-- **Graded bound of a priced body under the tree interpretation of samples.** A graded bound
at the weight `Costed.weight` is a graded bound at the weight `weightT sampleTree`. -/
theorem LoopBoundGraded.sampleTree {σ : Type} {body : σ → ProgE (Costed (SPComp ℕ)) E O σ}
    {s₀ : σ} {Inv : ℕ → σ → Prop} {a b : ℕ}
    (h : LoopBoundGraded Costed.weight body s₀ Inv a b) :
    LoopBoundGraded (weightT sampleTree) body s₀ Inv a b :=
  h.mono_weight weightT_sampleTree_le

/-! ### Interpretation by a family of costed trees -/

/-- The operation `q` is the compiled tree of a member of the family `F` of costed trees. -/
def InFamily (F : ℕ × SPTree.Timed ℕ → Prop) (q : SPComp ℕ) : Prop :=
  ∃ x, F x ∧ x.2.erase.compile = q

/-- The tree interpretation by the family `F` of costed trees: an operation that is the compiled
tree of a member of `F` is interpreted by that member, any other operation by `sampleTree`. An
inner simulator with a costed tree (its tree encoded by `encTree`) is interpreted this way. -/
noncomputable def treeBy (F : ℕ × SPTree.Timed ℕ → Prop) (q : SPComp ℕ) :
    ℕ × SPTree.Timed ℕ := by
  classical
  exact if h : InFamily F q then h.choose else sampleTree q

/-- The tree interpretation by a family compiles each operation of the family and each
distribution sample to itself. -/
theorem opComp_treeBy {F : ℕ × SPTree.Timed ℕ → Prop} {q : SPComp ℕ}
    (h : InFamily F q ∨ IsSample q) : opComp (treeBy F) q = q := by
  unfold opComp treeBy
  by_cases hq : InFamily F q
  · simp only [hq, ↓reduceDIte]
    exact hq.choose_spec.2
  · simp only [hq, ↓reduceDIte]
    exact opComp_sampleTree (h.resolve_left hq)

/-- When every member of `F` costs at most `T`, each operation of the tree interpretation by `F`
weighs at most `T + 1` times its unit weight. -/
theorem weightT_treeBy_le {F : ℕ × SPTree.Timed ℕ → Prop} {T : ℕ}
    (hF : ∀ x, F x → SPTree.Timed.stepTime x ≤ T) (q : Costed (SPComp ℕ)) :
    weightT (treeBy F) q ≤ (T + 1) * Costed.weight q := by
  rcases q with q | c
  · have hs := weightT_sampleTree_le (.op q)
    simp only [weightT, runT, Costed.weight, treeBy, Nat.mul_one] at hs ⊢
    split
    · next h =>
      have := hF _ h.choose_spec.1
      omega
    · omega
  · simp only [weightT, runT, Costed.weight, SPTree.Timed.stepTime, SPTree.Timed.time_ret]
    nlinarith

/-- A time bound scales with the weight: at `k` times the weight, `k ≥ 1` times the time. -/
theorem Bound.scale {Op' : Type} {w : Op' → ℕ} {k : ℕ} (hk : 1 ≤ k) {p : ProgE Op' E O α}
    {t : ℕ} {P : α → Prop} (h : Bound w p t P) : Bound (fun q => k * w q) p (k * t) P := by
  induction p generalizing t with
  | ret a => exact h
  | recv k' ih =>
    refine ⟨by nlinarith [h.1], fun e => (ih e (h.2 e)).mono ?_ fun _ => id⟩
    rw [Nat.mul_sub_one]
    omega
  | send o p ih =>
    refine ⟨by nlinarith [h.1], (ih h.2).mono ?_ fun _ => id⟩
    rw [Nat.mul_sub_one]
    omega
  | opN q k' ih =>
    refine ⟨Nat.mul_le_mul_left k h.1, fun n => (ih n (h.2 n)).mono ?_ fun _ => id⟩
    rw [Nat.mul_sub]
  | fail => trivial

/-- **Graded bound of a body under the tree interpretation by a family.** When every member of
`F` costs at most `T`, a graded bound `a`, `b` at the weight `Costed.weight` is the graded bound
`(T + 1) * a`, `(T + 1) * b` at the weight `weightT (treeBy F)`. -/
theorem LoopBoundGraded.treeBy {σ : Type} {F : ℕ × SPTree.Timed ℕ → Prop} {T : ℕ}
    (hF : ∀ x, F x → SPTree.Timed.stepTime x ≤ T) {body : σ → ProgE (Costed (SPComp ℕ)) E O σ}
    {s₀ : σ} {Inv : ℕ → σ → Prop} {a b : ℕ}
    (h : LoopBoundGraded Costed.weight body s₀ Inv a b) :
    LoopBoundGraded (weightT (ProgE.treeBy F)) body s₀ Inv ((T + 1) * a) ((T + 1) * b) :=
  ⟨h.1, fun i s hs => (((h.2 i s hs).scale (k := T + 1) (by omega)).mono_weight
    (weightT_treeBy_le hF)).mono (le_of_eq (by ring)) fun _ => id⟩

/-- **Erasure of a priced body under the tree interpretation by a family.** When every operation
of `body s` is the compiled tree of a member of `F` or a distribution sample, the priced form
erases under `treeBy F` to `body s`. -/
theorem eraseT_treeBy_priced {σ : Type} (F : ℕ × SPTree.Timed ℕ → Prop) (price : σ → ℕ)
    (body : σ → Prog E O σ) (s : σ) (h : AllOps (fun q => InFamily F q ∨ IsSample q) (body s)) :
    eraseT (treeBy F) (priced price body s) = body s := by
  rw [eraseT, erase_priced]
  exact mapOp_eq_self _ _ (h.mono fun _ hq => opComp_treeBy hq)

/-- The costed tree of codes of a costed tree on a countable type: its leaves encoded, as the
operation `Prog.sample` performs. -/
noncomputable def encTree {γ : Type} [Countable γ] (x : ℕ × SPTree.Timed γ) :
    ℕ × SPTree.Timed ℕ :=
  letI := Encodable.ofCountable γ
  SPTree.Timed.delay x.1 (x.2.map Encodable.encode fun _ => 0)

/-- The encoded costed tree compiles to the encoded computation. -/
theorem encTree_compile {γ : Type} [Countable γ] (x : ℕ × SPTree.Timed γ) :
    (encTree x).2.erase.compile =
      (letI := Encodable.ofCountable γ; SPComp.map Encodable.encode x.2.erase.compile) := by
  simp only [encTree, SPTree.Timed.delay, SPTree.Timed.erase_map, SPTree.compile_map]
  rfl

/-- Encoding the leaves adds no time. -/
theorem stepTime_encTree_le {γ : Type} [Countable γ] (x : ℕ × SPTree.Timed γ) :
    SPTree.Timed.stepTime (encTree x) ≤ SPTree.Timed.stepTime x := by
  have := SPTree.Timed.stepTime_map_le (letI := Encodable.ofCountable γ; Encodable.encode)
    (fun _ => 0) x.2 0 fun _ => le_rfl
  simp only [encTree, SPTree.Timed.stepTime_delay]
  simp only [SPTree.Timed.stepTime] at this ⊢
  omega

end ProgE

namespace Prog

variable {E O Q A α β : Type} {P : SPComp ℕ → Prop}

/-- `AllOps` of a sample from a countable type. -/
theorem allOps_sample [Countable β] {μ : SPComp β} {k : β → Prog E O α}
    (hμ : letI := Encodable.ofCountable β; P (SPComp.map Encodable.encode μ))
    (hk : ∀ b, ProgE.AllOps P (k b)) : ProgE.AllOps P (Prog.sample μ k) := by
  simp only [Prog.sample, sampleN, ProgE.AllOps]
  refine ⟨hμ, fun n => ?_⟩
  split
  · exact hk _
  · trivial

/-- The samples of a sample from a lifted sub-distribution are distribution samples. -/
theorem allOps_sample_liftSDistr [Countable β] {d : Prob.SDistr β} {k : β → Prog E O α}
    (hk : ∀ b, ProgE.AllOps ProgE.IsSample (k b)) :
    ProgE.AllOps ProgE.IsSample (Prog.sample (liftSDistr d) k) :=
  allOps_sample (ProgE.isSample_map_liftSDistr _ d) hk

/-- `recvO` has no operation. -/
theorem allOps_recvO : ProgE.AllOps P (recvO : Prog (E ⊕ A) (Q ⊕ O) E) := by
  intro x
  rcases x with e | a <;> trivial

/-- `call` has the operations of its continuation. -/
theorem allOps_call {q : Q} {k : A → Prog (E ⊕ A) (Q ⊕ O) α}
    (hk : ∀ a, ProgE.AllOps P (k a)) : ProgE.AllOps P (call (O := O) (E := E) q k) := by
  intro x
  rcases x with e | a
  · trivial
  · exact hk a

/-- `outE` has no operation. -/
theorem allOps_outE {o : O} : ProgE.AllOps P (outE (E := E) (A := A) (Q := Q) o) := trivial

end Prog

end CatCrypt.Crypto.Party
