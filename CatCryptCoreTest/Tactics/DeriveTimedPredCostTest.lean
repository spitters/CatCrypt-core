/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.StdCosts
public import CatCryptCore.Core.SPTree

/-!
# Tests for decidable predicate companions and unmirrored closures in data

Rule (i) of `CatCryptCore.Tactics.DeriveTimed`: a predicate argument of a registered primitive
followed by a decision instance for it has a cost companion, the cost of deciding the predicate
at each argument, which the registered cost charges (`Finset.filter`: once per element).
Rule (j): a closure built into data whose type has no costed form is refused.

* a filter by a predicate whose decision calls a costly function, charged per element;
* a filter by a relation with a `DecidableRel` instance on pairs, and a registered primitive
  taking a relation and its `DecidableRel` instance;
* a registered primitive taking a predicate and its `DecidablePred` instance;
* the refusal of a closure stored in a value of a type computed by recursion;
* the cardinality of a filter by a costly predicate.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimedPredCostTest

open CatCrypt.Core

/-- A function whose cost grows with its argument. -/
def costly (n : ℕ) : ℕ := (List.range n).length

derive_cost costly

/-- `costly n` costs at least three units per unit of `n`. -/
theorem costly_timedCost_ge (n : ℕ) : 3 * n ≤ costly.timedCost n := by
  simp [costly.timedCost, List.length.timedCost_eq]; omega

/-! ### (a) A filter by a costly predicate -/

/-- The elements of `s` whose image under `costly` exceeds 3. -/
def bigOnes (s : Finset ℕ) : Finset ℕ := s.filter fun n => 3 < costly n

derive_cost bigOnes

/-- The filter decides the predicate once per element, at the cost of `costly`. -/
example (s : Finset ℕ) :
    bigOnes.timedCost s = ∑ i ∈ s, costly.timedCost i + 2 * s.card + 2 := by
  simp [bigOnes.timedCost, Finset.filter.timedCost_eq, Finset.sum_add_distrib]; omega

example (s : Finset ℕ) : 3 * ∑ i ∈ s, i ≤ bigOnes.timedCost s := by
  have h : 3 * ∑ i ∈ s, i ≤ ∑ i ∈ s, costly.timedCost i := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun i _ => costly_timedCost_ge i
  simp [bigOnes.timedCost, Finset.filter.timedCost_eq, Finset.sum_add_distrib]; omega

/-- A tree that returns `bigOnes s`. -/
noncomputable def bigOnesTree (s : Finset ℕ) : SPTree (Finset ℕ) := SPTree.ret (bigOnes s)

derive_timed bigOnesTree

example (s : Finset ℕ) : (bigOnesTree.timed s).2.erase = bigOnesTree s :=
  bigOnesTree.erase_timed s

/-! ### (b) A filter by a decidable relation on pairs -/

/-- A relation whose decision calls `costly`. -/
def below (a b : ℕ) : Prop := costly a < b

instance : DecidableRel below := fun a b => inferInstanceAs (Decidable (costly a < b))

/-- The pairs of `s` whose components are related by `below`. -/
def ordered (s : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) := s.filter fun q => below q.1 q.2

set_option derive_timed.priceProps true in
derive_cost ordered

/-- With `derive_timed.priceProps`, deciding `below q.1 q.2` costs the unfolded relation: one
unit for `below`, one for `<`, and `costly q.1`. -/
example (s : Finset (ℕ × ℕ)) :
    ordered.timedCost s = ∑ q ∈ s, costly.timedCost q.1 + 3 * s.card + 2 := by
  simp [ordered.timedCost, Finset.filter.timedCost_eq, Finset.sum_add_distrib]; omega

/-- A tree that returns `ordered s`. -/
noncomputable def orderedTree (s : Finset (ℕ × ℕ)) : SPTree (Finset (ℕ × ℕ)) :=
  SPTree.ret (ordered s)

set_option derive_timed.priceProps true in
derive_timed orderedTree

example (s : Finset (ℕ × ℕ)) : (orderedTree.timed s).2.erase = orderedTree s :=
  orderedTree.erase_timed s

/-- The pairs of elements of `s` related by `r` (a primitive with a registered cost). -/
def relPairs {α : Type} (r : α → α → Prop) [DecidableRel r] (s : Finset α) :
    Finset (α × α) :=
  (s ×ˢ s).filter fun q => r q.1 q.2

timed_cost relPairs := fun (α : Type) (_r : α → α → Prop) (rCost : α → α → ℕ)
  [DecidableRel _r] (s : Finset α) => ∑ a ∈ s, ∑ b ∈ s, (1 + rCost a b) + 1

/-- The pairs of `s` related by `below`, through the registered primitive. -/
def belowPairs (s : Finset ℕ) : Finset (ℕ × ℕ) := relPairs below s

set_option derive_timed.priceProps true in
derive_cost belowPairs

/-- The companion of the relation, `fun a b => 2 + costly.timedCost a`, is charged once per
pair. -/
example (s : Finset ℕ) :
    belowPairs.timedCost s = ∑ a ∈ s, ∑ _b ∈ s, (3 + costly.timedCost a) + 2 := by
  have h (a : ℕ) : 1 + (2 + costly.timedCost a) = 3 + costly.timedCost a := by omega
  simp only [belowPairs.timedCost, relPairs.timedCost, h]; omega

/-! ### (c) A registered primitive taking a decidable predicate -/

/-- The number of elements of `l` satisfying `p` (a primitive with a registered cost). -/
def countSat {α : Type} (p : α → Prop) [DecidablePred p] (l : List α) : ℕ :=
  (l.filter fun a => decide (p a)).length

timed_cost countSat := fun (α : Type) (_p : α → Prop) (pCost : α → ℕ) [DecidablePred _p]
  (l : List α) => (l.map fun a => 1 + pCost a).sum + 1

/-- The number of elements of `l` whose image under `costly` exceeds 3. -/
def countBig (l : List ℕ) : ℕ := countSat (fun n => 3 < costly n) l

derive_cost countBig

/-- The registered cost charges the companion `fun n => 1 + costly.timedCost n` per element. -/
example (l : List ℕ) :
    countBig.timedCost l = (l.map costly.timedCost).sum + 2 * l.length + 2 := by
  simp only [countBig.timedCost, countSat.timedCost]
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢; omega

/-- A tree that returns `countBig l`. -/
noncomputable def countBigTree (l : List ℕ) : SPTree ℕ := SPTree.ret (countBig l)

derive_timed countBigTree

example (l : List ℕ) : (countBigTree.timed l).1 = countBig.timedCost l + 1 := by
  simp [countBigTree.timed]; omega

example (l : List ℕ) : (countBigTree.timed l).2.erase = countBigTree l :=
  countBigTree.erase_timed l

/-! ### (e) The cardinality of a filter by a costly predicate -/

/-- The number of elements of `s` whose image under `costly` exceeds 3. -/
def countCostly (s : Finset ℕ) : ℕ := (s.filter fun n => 3 < costly n).card

derive_cost countCostly

/-- The filter charges `costly` per element; the cardinality of the filtered set at most one
unit per element of `s` and one more. -/
example (s : Finset ℕ) :
    countCostly.timedCost s ≤ ∑ i ∈ s, costly.timedCost i + 3 * s.card + 4 := by
  have h := Finset.card_filter_le s fun n => 3 < costly n
  simp [countCostly.timedCost, Finset.filter.timedCost_eq, Finset.card.timedCost_eq,
    Finset.sum_add_distrib]; omega

example (s : Finset ℕ) : ∑ i ∈ s, costly.timedCost i ≤ countCostly.timedCost s := by
  simp [countCostly.timedCost, Finset.filter.timedCost_eq, Finset.sum_add_distrib]; omega

/-- A tree that returns `countCostly s`. -/
noncomputable def countCostlyTree (s : Finset ℕ) : SPTree ℕ := SPTree.ret (countCostly s)

derive_timed countCostlyTree

example (s : Finset ℕ) : (countCostlyTree.timed s).2.erase = countCostlyTree s :=
  countCostlyTree.erase_timed s

/-! ### (d) A closure stored in a value of a type computed by recursion -/

/-- Trees of depth `n` with binary branching, a type computed by recursion on `n`. -/
def FTree : ℕ → Type
  | 0 => ℕ
  | n + 1 => ℕ × (Fin 2 → FTree n)

/-- A tree of depth `n` whose children are computed by a closure over a recursive call. -/
def grow : (n : ℕ) → ℕ → Option (FTree n)
  | 0, x => some x
  | n + 1, x => if h : (grow n x).isSome then some (x, fun _ => (grow n x).get h) else none

/--
error: derive_timed: a function bound in data: the value `some (x, fun x_1 ↦ (grow n x).get h)`
of type `Option (FTree (n + 1))` builds the closure `fun x_1 ↦ (grow n x).get h` of type
`Fin 2 → FTree n` at the position Option.some → Prod.snd (reached by unfolding
[`CatCrypt.Tactics.DeriveTimedPredCostTest.FTree`]); the type has no costed form, so the closure
would cost nothing to build and its applications would not be charged (rule (j))
-/
#guard_msgs (whitespace := lax) in
derive_cost grow

end CatCrypt.Tactics.DeriveTimedPredCostTest
