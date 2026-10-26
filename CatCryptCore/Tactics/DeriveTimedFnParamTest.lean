/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound

/-!
# Tests for the cost companions of function parameters of dependent matches

Miniatures of recursive helpers whose function parameter has a type that depends on another
argument of the match, derived by `derive_cost` and `derive_reduction`.

* `sumIdx`: a data function of an index function `r : Fin n → ℕ`, by recursion on `n`; its cost
  `sumIdx.timedCost` takes the companion of `r`.
* `countAcc`: a data function of a verifier `V : Tup ks → Bool`, by recursion on `ks`, called at
  two closures of `V` in each step.
* `drawIdx`: a recursive computation of an index function, reflected by `derive_reduction`
  through its caller `drawRed`; its costed tree and erasure theorem are derived, and its time
  theorem `drawIdx.tree.timeBound` is proved by induction (each level charges the companion
  of the closure `fun i => r i.succ`, the companion of `r` plus a constant).
* `sumRed`: a reduction computing `sumIdx` and `countAcc`, with its time theorem by
  `derive_time_bound`.
* `drawFn`: a recursive computation of an index function whose result holds a function,
  reflected through its caller `drawFnRed`; its erasure theorem uses the induction hypotheses
  of `drawFn.tree` instantiated at the companions of the recursive call.
* `chainK`: a recursive computation with a structure binder whose computation field is a
  primitive of its tree (a binder `ℕ → SPTree ℕ` of `chainK.tree`, passed to `chainK.tree` as
  the erasure of its costed binder), a function binder, an index function and a result holding
  a function; reflected through its caller `chainRed`, with the functional induction on
  `chainK.tree` at its application in the erasure theorem.
-/

@[expose] public section

namespace CatCrypt.Tactics.DeriveTimedFnParamTest

open CatCrypt.Core CatCrypt.Crypto

/-- The sum of an index function `r : Fin n → ℕ`, by recursion on `n`. -/
def sumIdx : (n : ℕ) → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, r => r 0 + sumIdx n (fun i => r i.succ)

derive_cost sumIdx

/-- Tuples of naturals indexed by a list. -/
def Tup : List ℕ → Type
  | [] => Unit
  | _ :: ks => ℕ × Tup ks

/-- The number of accepted tuples among a binary tree of tuples, for a verifier `V` on tuples
indexed by `ks`. -/
def countAcc : (ks : List ℕ) → (Tup ks → Bool) → ℕ
  | [], V => if V () then 1 else 0
  | k :: ks, V => countAcc ks (fun t => V (k, t)) + countAcc ks (fun t => V (k + 1, t))

derive_cost countAcc

/-- Draw `n` bits and return `r i` at each set bit. -/
noncomputable def drawIdx : (n : ℕ) → (Fin n → ℕ) → SPComp (List ℕ)
  | 0, _ => SPComp.pure []
  | n + 1, r => (SPComp.sample Bool).bind fun b =>
      (drawIdx n (fun i => r i.succ)).bind fun xs => SPComp.pure ((if b then r 0 else 0) :: xs)

/-- A reduction running `drawIdx` before the adversary. -/
noncomputable def drawRed (n : ℕ) (r : Fin n → ℕ) (A : List ℕ → SPComp Bool) : SPComp Bool :=
  (drawIdx n r).bind A

derive_reduction drawRed

/-- The time of the costed tree of `drawIdx`: per level, the cost of `r 0` and a constant. -/
theorem drawIdx.tree.timeBound : ∀ (n c : ℕ) (r rCost : Fin n → ℕ),
    (∀ i, rCost i ≤ c) →
      SPTree.Timed.stepTime (drawIdx.tree.timed n r rCost) ≤ (c + 4 * n + 20) * n + 20
  | 0, c, r, rCost, _ => by
    simp only [drawIdx.tree.timed, SPTree.Timed.stepTime, SPTree.Timed.delay]; time_bound
  | n + 1, c, r, rCost, h => by
    have ih := drawIdx.tree.timeBound n (c + 4) (fun i => r i.succ)
      (fun i => 1 + (rCost i.succ + 3)) (fun i => by have := h i.succ; omega)
    rw [drawIdx.tree.timed, SPTree.Timed.stepTime_delay]
    set X := drawIdx.tree.timed n (fun i => r i.succ) fun i => 1 + (rCost i.succ + 3)
    have hb := fun b : Bool => SPTree.Timed.stepTime_bind_le X.2
      (fun x => ((1 + if b = true then 1 + rCost 0 else 0),
        SPTree.Timed.ret ((if b = true then r 0 else 0) :: x))) (2 + c)
      (fun x => by
        have := h 0
        simp only [SPTree.Timed.stepTime, SPTree.Timed.time_ret]
        split <;> omega)
    simp only [SPTree.Timed.stepTime] at hb ih ⊢
    rw [SPTree.Timed.time_sample]
    refine (Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_left
      (Finset.sup_le (fun b _ => (?_ : _ ≤ X.1 + X.2.time + c + 3))) 1) 0) 1).trans ?_
    · have := hb b
      omega
    · nlinarith

/-- The time of the costed tree of `drawRed`: the time of `drawIdx`, the adversary's cost and
time, and a constant. -/
theorem drawRed.tree.timeBound (n c T a : ℕ) (r rCost : Fin n → ℕ)
    (A : List ℕ → SPTree.Timed Bool) (ACost : List ℕ → ℕ) (hr : ∀ i, rCost i ≤ c)
    (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a) :
    SPTree.Timed.stepTime (drawRed.tree.timed n r rCost A ACost) ≤
      (c + 4 * n + 20) * n + 20 + a + T + 10 := by
  have hd := drawIdx.tree.timeBound n c r rCost hr
  rw [drawRed.tree.timed, SPTree.Timed.stepTime_delay]
  have hb := SPTree.Timed.stepTime_bind_le (drawIdx.tree.timed n r rCost).2
    (fun x => (1 + ACost x, A x)) (1 + a + T) (fun x => by
      simp only [SPTree.Timed.stepTime]
      have := hA x
      have := hAc x
      omega)
  simp only [SPTree.Timed.stepTime] at hb hd ⊢
  generalize (c + 4 * n + 20) * n = m at hd ⊢
  omega

/-- A reduction computing the two data helpers. -/
noncomputable def sumRed (n : ℕ) (r : Fin n → ℕ) (ks : List ℕ) (V : Tup ks → Bool)
    (A : ℕ → SPComp Bool) : SPComp Bool :=
  A (sumIdx n r + countAcc ks V)

derive_reduction sumRed

derive_time_bound sumRed.tree

/-- Draw `n` bits; the result is a sum of the values `r i` and a function built from the bits. -/
noncomputable def drawFn : (n : ℕ) → (Fin n → ℕ) → SPComp (ℕ × (ℕ → ℕ))
  | 0, _ => SPComp.pure (0, id)
  | n + 1, r => (SPComp.sample Bool).bind fun b =>
      (drawFn n (fun i => r i.succ)).bind fun p =>
        SPComp.pure (p.1 + r 0, fun x => if b then p.2 x else x)

/-- A reduction applying the function of `drawFn` before the adversary. -/
noncomputable def drawFnRed (n : ℕ) (r : Fin n → ℕ) (A : ℕ → SPComp Bool) : SPComp Bool :=
  (drawFn n r).bind fun p => A (p.2 p.1)

derive_reduction drawFnRed

/-- A kit: a data function and a computation, as fields. -/
structure Kit where
  /-- A data function. -/
  f : ℕ → ℕ
  /-- A computation. -/
  step : ℕ → SPComp ℕ

/-- A chain of `n` steps of the kit from `x`, with an index function `r`, a function binder
`g`, and a result holding a function. -/
noncomputable def chainK (K : Kit) (g : ℕ → ℕ) :
    (n : ℕ) → (Fin n → ℕ) → ℕ → SPComp (ℕ × (ℕ → ℕ))
  | 0, _, x => SPComp.pure (K.f x, id)
  | n + 1, r, x => (K.step (r 0)).bind fun y =>
      (chainK K g n (fun i => r i.succ) (g x)).bind fun p =>
        SPComp.pure (p.1 + y, fun z => if y = 0 then p.2 z else z)

/-- A reduction running `chainK` before the adversary. -/
noncomputable def chainRed (K : Kit) (g : ℕ → ℕ) (n : ℕ) (r : Fin n → ℕ)
    (A : ℕ → SPComp Bool) : SPComp Bool :=
  (chainK K g n r 0).bind fun p => A (p.2 p.1)

derive_reduction chainRed

end CatCrypt.Tactics.DeriveTimedFnParamTest

end
