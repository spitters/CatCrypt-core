/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
public import CatCryptCore.Tactics.StdCosts
import CatCryptCore.Tactics.DeriveCost

/-!
# Tests for functions in values of computed types and tabulated closures

Rule (l) of `CatCryptCore.Tactics.DeriveTimed`: a projection of a value whose type is a
type-valued definition that does not unfold at reducible transparency (a type computed by
recursion), applied, is a table read. Rule (m): a closure over a finite domain placed in data
whose type has no costed form is tabulated where it is built, at the sum over its domain of the
cost of its body.

* `follow`: the continuation `s.2 c` of a strategy of the type `Strat n`, computed by recursion,
  read at one unit per step; the cost is `5 * n + 1`;
* `followTree`: the strategy drawn from a computation and followed (`derive_reduction`);
* `countAcc`: a rewinding sum over rounds with enumerated challenges (`FinEnum`), whose cost
  takes the recursive cost once per challenge, in the companion of the function mapped over the
  enumeration;
* `grid`: a closure over `Bool → Fin 2 → ℕ` stored in an optional pair, tabulated by a double
  sum, and the tree `gridTree` returning it, with its erasure theorem.

The tabulation of a closure into a value of a type computed by recursion, and the refusal of a
closure over an infinite domain, are tested in `CatCryptCoreTest.Tactics.DeriveTimedPredCostTest`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimedComputedTypeTest

open CatCrypt.Core

/-! ## A continuation read from a strategy of a computed type (rule (l)) -/

/-- Strategies of depth `n`: a message and a continuation for each move of `Fin 3`. -/
def Strat : ℕ → Type
  | 0 => ℕ
  | n + 1 => ℕ × (Fin 3 → Strat n)

/-- Follow a strategy along the moves `n % 3`, adding up its messages. -/
def follow : (n : ℕ) → Strat n → ℕ
  | 0, s => s
  | n + 1, s => s.1 + follow n (s.2 ⟨n % 3, Nat.mod_lt _ (by decide)⟩)

derive_cost follow

/-- A step reads the continuation at one unit, as a table, and adds the message. -/
example (n : ℕ) (s : Strat (n + 1)) :
    follow.timedCost (n + 1) s = follow.timedCost n (s.2 ⟨n % 3, Nat.mod_lt _ (by decide)⟩) + 5 := by
  rw [follow.timedCost.eq_2]
  omega

/-- The cost of following a strategy of depth `n` is `5 * n + 1`. -/
theorem follow_timedCost_eq : ∀ (n : ℕ) (s : Strat n), follow.timedCost n s = 5 * n + 1
  | 0, s => by rw [follow.timedCost.eq_1]
  | n + 1, s => by
    rw [follow.timedCost.eq_2]
    have := follow_timedCost_eq n (s.2 ⟨n % 3, Nat.mod_lt _ (by decide)⟩)
    omega

/-- Draw a strategy from `P` and follow it. -/
noncomputable def followTree (n : ℕ) (P : SPComp (Strat n)) : SPComp ℕ :=
  SPComp.bind P fun s => SPComp.pure (follow n s)

derive_reduction followTree

/-- The costed form: the costed computation of the strategy, then the derived cost of `follow`
at the strategy drawn, whose functions are tables. -/
example (n : ℕ) (P : SPTree.Timed (Strat n)) :
    followTree.tree.timed n P =
      P.bind fun s => (1 + follow.timedCost n s, SPTree.Timed.ret (follow n s)) := rfl

example (n : ℕ) (P : SPTree.Timed (Strat n)) :
    (followTree.tree.timed n P).2.erase = followTree.tree n P.erase :=
  followTree.tree.erase_timed n P

/-! ## Rewinding over enumerated challenges -/

/-- A round with a challenge set carrying an enumeration. -/
structure Rnd : Type 1 where
  /-- The challenges. -/
  C : Type
  /-- Their enumeration. -/
  [fe : FinEnum C]

attribute [instance] Rnd.fe

/-- Strategies for the rounds `rs`: a message and a continuation per challenge. -/
def RStrat : List Rnd → Type
  | [] => ℕ
  | r :: rs => ℕ × (r.C → RStrat rs)

/-- The sum of the leaf values of a strategy: at each round the strategy is rewound at every
challenge of the enumeration. -/
def countAcc : (rs : List Rnd) → RStrat rs → ℕ
  | [], s => s
  | r :: rs, s => ((FinEnum.toList r.C).map fun c => countAcc rs (s.2 c)).foldr (· + ·) 0

derive_cost countAcc

/-- The recursive cost occurs once, in the companion of the function mapped over the
enumeration, which `List.map.timedCost` charges once per challenge. -/
example (r : Rnd) (rs : List Rnd) (s : RStrat (r :: rs)) :
    countAcc.timedCost (r :: rs) s =
      1 + (1 + (List.foldr.timedCost (· + ·) (fun _ _ => 1) 0
          ((FinEnum.toList r.C).map fun c => countAcc rs (s.2 c)) +
        (1 + (List.map.timedCost (fun c => countAcc rs (s.2 c))
          (fun c => 1 + (countAcc.timedCost rs (s.2 c) + 1))
          (FinEnum.toList r.C) + (1 + FinEnum.toList.timedCost r.C))))) := by
  rw [countAcc.timedCost.eq_2]

/-! ## A closure over a finite domain in data without a costed form (rule (m)) -/

/-- A size and a table over `Bool × Fin 2` read from a list. -/
def grid (l : List ℕ) : Option (ℕ × (Bool → Fin 2 → ℕ)) :=
  some (l.length, fun b j => if b then l.getD j.val 0 else 0)

derive_cost grid

/-- The table is evaluated at its four points where it is built: a double sum over its domain of
the cost of its body, then the length. -/
example (l : List ℕ) :
    grid.timedCost l = (∑ b : Bool, ∑ j : Fin 2,
      (1 + if b = true then 1 + List.getD.timedCost l j.val 0 else 0)) +
        (1 + List.length.timedCost l) := rfl

/-- A tree returning the table. -/
noncomputable def gridTree (l : List ℕ) : SPTree (Option (ℕ × (Bool → Fin 2 → ℕ))) :=
  SPTree.ret (grid l)

derive_timed gridTree

example (l : List ℕ) : gridTree.timed l = (1 + grid.timedCost l, SPTree.Timed.ret (grid l)) := rfl

example (l : List ℕ) : (gridTree.timed l).2.erase = gridTree l := gridTree.erase_timed l

end CatCrypt.Tactics.DeriveTimedComputedTypeTest
