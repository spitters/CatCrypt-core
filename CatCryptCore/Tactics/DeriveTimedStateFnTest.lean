/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Tactics.AutoTime
import CatCryptCore.Core.SPTree

/-!
# Tests for functions stored in data and in state fields

Minimal reductions of the two shapes in which a function is stored in data:

* a block (a function `Fin 2 → ℕ`) stored in a sum, matched and returned, then passed to a
  distinguisher (the shape of `chacha20UCReduction`, `o9Cha`), and the same block applied
  after the match (`o9ChaApp`), whose cost is the companion of the block's binder carried
  through the sum;
* a state structure with function fields computed by a function binder, bound by a `let` and
  updated by `Function.update` of a field applied to arguments (the shape of
  `oekeL2Reduction`, `o9Oeke`), and a function field of a state received from a tree applied
  (`o9OekeRead`), whose cost is the companion carried in the state's costed value.

Each is derived by `derive_timed`, its erasure theorem is pinned by an `example`, and the time
of the costed forms of `o9Cha`, `o9ChaApp` and `o9Oeke` is bounded by `time_bound`.

## Main results

* `o9Cha.timeBound`, `o9ChaApp.timeBound`, `o9Oeke.timeBound`
* `o9Sim.timeBound` — a structure of functions in a sum, with a curried sample applied
  partially; `o9Simu.timeBound` — such a result from a callee under `Sum.inr`
-/

public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimedStateFnTest

open CatCrypt.Core

/-! ## A function stored in a sum -/

/-- A block: a function of a lane index. -/
abbrev O9Blk := Fin 2 → ℕ

/-- A block stored in a sum, matched and returned, then passed to a distinguisher. -/
noncomputable def o9Cha (A : Unit → SPTree Bool) (D : O9Blk ⊕ Bool → SPTree Bool)
    (s : O9Blk) : SPTree Bool :=
  (SPTree.ret (Sum.inl s : O9Blk ⊕ Unit)).bind fun o =>
    (match o with
      | .inl a => (SPTree.ret a).bind fun b => SPTree.ret (Sum.inl b : O9Blk ⊕ Bool)
      | .inr u => (A u).bind fun b => SPTree.ret (Sum.inr b)).bind D

derive_timed o9Cha

example (A : Unit → SPTree.Timed Bool) (ACost : Unit → ℕ) (D : O9Blk ⊕ Bool → SPTree.Timed Bool)
    (DCost : O9Blk ⊕ Bool → ℕ) (s : O9Blk) (sCost : Fin 2 → ℕ) :
    (o9Cha.timed A ACost D DCost s sCost).2.erase =
      o9Cha (fun u => (A u).erase) (fun o => (D o).erase) s :=
  o9Cha.erase_timed A ACost D DCost s sCost

/-- The costed form of `o9Cha` takes the time of the distinguisher, its cost and two steps. -/
theorem o9Cha.timeBound (A : Unit → SPTree.Timed Bool) (ACost : Unit → ℕ)
    (D : O9Blk ⊕ Bool → SPTree.Timed Bool) (DCost : O9Blk ⊕ Bool → ℕ) (s : O9Blk)
    (sCost : Fin 2 → ℕ) {T d : ℕ} (hD : ∀ o, (D o).time ≤ T) (hd : ∀ o, DCost o ≤ d) :
    SPTree.Timed.stepTime (o9Cha.timed A ACost D DCost s sCost) ≤ T + d + 2 := by
  simp only [o9Cha.timed, SPTree.Timed.bind, Sum.map_inl, Sum.elim_inl]
  time_bound

/-- The block applied after the match: priced by the companion of `s`, carried in the sum. -/
noncomputable def o9ChaApp (D : ℕ ⊕ Bool → SPTree Bool) (s : O9Blk) : SPTree Bool :=
  (SPTree.ret (Sum.inl s : O9Blk ⊕ Unit)).bind fun o =>
    (match o with
      | .inl a => SPTree.ret (Sum.inl (a 0) : ℕ ⊕ Bool)
      | .inr _ => SPTree.ret (Sum.inr true)).bind D

derive_timed o9ChaApp

example (D : ℕ ⊕ Bool → SPTree.Timed Bool) (DCost : ℕ ⊕ Bool → ℕ) (s : O9Blk)
    (sCost : Fin 2 → ℕ) :
    (o9ChaApp.timed D DCost s sCost).2.erase = o9ChaApp (fun o => (D o).erase) s :=
  o9ChaApp.erase_timed D DCost s sCost

/-- The costed form of `o9ChaApp` takes the time of the distinguisher, its cost, the
companion of the block and four steps. -/
theorem o9ChaApp.timeBound (D : ℕ ⊕ Bool → SPTree.Timed Bool) (DCost : ℕ ⊕ Bool → ℕ)
    (s : O9Blk) (sCost : Fin 2 → ℕ) {T c d : ℕ} (hD : ∀ o, (D o).time ≤ T)
    (hd : ∀ o, DCost o ≤ d) (hs : ∀ i, sCost i ≤ c) :
    SPTree.Timed.stepTime (o9ChaApp.timed D DCost s sCost) ≤ T + c + d + 4 := by
  simp only [o9ChaApp.timed, SPTree.Timed.bind, Sum.map_inl, Sum.elim_inl]
  time_bound

/-! ## A state structure with function fields -/

/-- A state with function fields. -/
structure O9State where
  /-- The status of each session. -/
  sessions : ℕ → Option Bool
  /-- The number of guesses of each session. -/
  guessCount : ℕ → ℕ

/-- The state with the guess count of `sid` incremented. -/
def O9State.incGuess (st : O9State) (sid : ℕ) : O9State where
  sessions := st.sessions
  guessCount := Function.update st.guessCount sid (st.guessCount sid + 1)

/-- The state `st a`, bound by a `let`, updated twice and passed to a distinguisher. -/
noncomputable def o9Oeke (sid : ℕ → ℕ) (st : ℕ → O9State) (a : ℕ)
    (D : ℕ × O9State → SPTree Bool) (m : ℕ × ℕ) : SPTree Bool :=
  let s := st a
  (SPTree.ret (m.1, (s.incGuess (sid a)).incGuess m.2)).bind D

derive_timed o9Oeke

example (sid sidCost : ℕ → ℕ) (st : ℕ → O9State) (stCost : ℕ → ℕ) (a : ℕ)
    (D : ℕ × O9State → SPTree.Timed Bool) (DCost : ℕ × O9State → ℕ) (m : ℕ × ℕ) :
    (o9Oeke.timed sid sidCost st stCost a D DCost m).2.erase =
      o9Oeke sid st a (fun o => (D o).erase) m :=
  o9Oeke.erase_timed sid sidCost st stCost a D DCost m

/-- The costed form of `o9Oeke` takes the time of the distinguisher, its cost, the companion
of `st`, four companions of `sid` and twenty steps. -/
theorem o9Oeke.timeBound (sid sidCost : ℕ → ℕ) (st : ℕ → O9State) (stCost : ℕ → ℕ) (a : ℕ)
    (D : ℕ × O9State → SPTree.Timed Bool) (DCost : ℕ × O9State → ℕ) (m : ℕ × ℕ)
    {T b c d : ℕ} (hD : ∀ o, (D o).time ≤ T) (hd : ∀ o, DCost o ≤ d)
    (hs : ∀ x, sidCost x ≤ b) (hc : ∀ x, stCost x ≤ c) :
    SPTree.Timed.stepTime (o9Oeke.timed sid sidCost st stCost a D DCost m) ≤
      T + 4 * b + c + d + 20 := by
  time_bound

/-- The output step from state `s`. -/
noncomputable def o9Post (sid : ℕ) (s : O9State) (m : ℕ × ℕ) : SPTree (ℕ × O9State) :=
  .ret (m.1, s.incGuess sid)

/-- A function field of a state received from a tree, applied: priced by the companion in the
state's costed value. -/
noncomputable def o9OekeRead (sid : ℕ → ℕ) (st : ℕ → O9State) (a : ℕ) (m : ℕ × ℕ) :
    SPTree ℕ :=
  (o9Post (sid a) (st a) m).bind fun r => .ret (r.2.guessCount 0)

derive_timed o9OekeRead

example (sid sidCost : ℕ → ℕ) (st : ℕ → O9State) (stCost : ℕ → ℕ) (a : ℕ) (m : ℕ × ℕ)
    (gCost : ℕ → ℕ) :
    (o9OekeRead.timed sid sidCost st stCost a m gCost).2.erase = o9OekeRead sid st a m :=
  o9OekeRead.erase_timed sid sidCost st stCost a m gCost

/-! ## Structures holding functions in a result, a binder and a costed bind -/

/-- A value. -/
abbrev O9V := Fin 5

/-- Field operations stored in a parameter structure. -/
structure O9Par where
  /-- Addition. -/
  add : O9V → O9V → O9V
  /-- Multiplication. -/
  mul : O9V → O9V → O9V

/-- A polynomial by its coefficients. -/
structure O9Poly where
  /-- The coefficients. -/
  coeffs : Fin 2 → O9V

/-- A round: a polynomial and a challenge. -/
structure O9Round where
  /-- The polynomial. -/
  poly : O9Poly
  /-- The challenge. -/
  ch : O9V

/-- A proof: three rounds. -/
structure O9Proof where
  /-- The rounds. -/
  rounds : Fin 3 → O9Round

/-- A claim with a function field. -/
structure O9Claim where
  /-- The polynomial. -/
  g : O9V → O9V
  /-- The claimed sum. -/
  s : O9V

/-- Horner evaluation through the operations of `P`. -/
def O9Poly.eval (P : O9Par) (p : O9Poly) (x : O9V) : O9V :=
  Fin.foldl 2 (fun acc i => P.add (p.coeffs i) (P.mul x acc)) 0

/-- The rounds from sampled coefficients: the curried sample `raw` is applied partially. -/
def o9Build (P : O9Par) (raw : Fin 3 → Fin 2 → O9V) (ch : Fin 3 → O9V) (c : O9V) :
    Fin 3 → O9Round :=
  let getC : Fin 3 → O9V := fun i =>
    Fin.foldl i.val (fun t (j : Fin i.val) =>
      let idx : Fin 3 := ⟨j.val, lt_trans j.isLt i.isLt⟩
      O9Poly.eval P ⟨raw idx⟩ (P.add (ch idx) t)) c
  fun i => ⟨⟨raw i⟩, P.add (ch i) (getC i)⟩

/-- A simulator returning a structure of functions in a sum (the shape of
`sumcheck_blinded_simulator`). -/
noncomputable def o9Sim (P : O9Par) (claim : O9Claim) : SPTree (Bool ⊕ O9Proof) :=
  .sample (Fin 3 → Fin 2 → O9V) inferInstance ⟨fun _ _ => 0⟩ fun raw =>
  .sample (Fin 3 → O9V) inferInstance ⟨fun _ => 0⟩ fun ch =>
  let rounds : Fin 3 → O9Round := o9Build P raw ch claim.s
  .ret (Sum.inr ⟨rounds⟩)

derive_timed o9Sim

/-- The costed form of `o9Sim` takes its two samples. -/
theorem o9Sim.timeBound (P : O9Par) (claim : O9Claim) (addCost mulCost : O9V → O9V → ℕ) :
    SPTree.Timed.stepTime (o9Sim.timed P claim addCost mulCost) ≤ 2 := by
  time_bound

/-- A read trace. -/
structure O9R where
  /-- The records. -/
  records : Fin 3 → O9V

/-- A write trace. -/
structure O9W where
  /-- The records. -/
  records : Fin 3 → O9V
  /-- The initial records. -/
  init : Fin 2 → O9V

/-- A binder that is a pair of structures holding functions (the shape of
`lasso_simulator_uniform`): it keeps the convention of field paths. -/
noncomputable def o9Lasso (t : O9R × O9W) : SPTree O9V :=
  .sample O9V inferInstance ⟨0⟩ fun x => .ret (x + t.1.records 0 - t.1.records 0)

derive_timed o9Lasso

noncomputable example (t : O9R × O9W) (rCost : Fin 3 → ℕ) : ℕ × SPTree.Timed O9V :=
  o9Lasso.timed t rCost

/-- A structure holding functions. -/
structure O9SP where
  /-- A value. -/
  a : O9V
  /-- A function. -/
  f : Fin 2 → O9V

/-- Samples packed in a structure holding a function. -/
noncomputable def o9Full : SPTree O9SP :=
  .sample O9V inferInstance ⟨0⟩ fun a =>
  .sample (Fin 2 → O9V) inferInstance ⟨fun _ => 0⟩ fun f => .ret ⟨a, f⟩

derive_timed o9Full

/-- The result of a callee holding functions, under `Sum.inr` (the shape of
`starkSimulator_perfect`). -/
noncomputable def o9Simu (_t : ℕ) : SPTree (Bool ⊕ O9SP) :=
  o9Full.bind fun π => .ret (Sum.inr π)

derive_timed o9Simu

/-- The costed form of `o9Simu`, erased at its result, takes two steps. -/
theorem o9Simu.timeBound (t : ℕ) :
    SPTree.Timed.stepTime ((o9Simu.timed t).2.bind fun y =>
      (0, SPTree.Timed.ret (Sum.map id (fun x => O9SP.mk x.1 x.2.1) y))) ≤ 2 := by
  simp only [SPTree.Timed.stepTime, o9Simu.timed, o9Full.timed, SPTree.Timed.delay,
    SPTree.Timed.bind]
  time_bound

end CatCrypt.Tactics.DeriveTimedStateFnTest
