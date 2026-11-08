/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.StdCosts
public import CatCryptCore.Core.SPTree
import CatCryptCore.Tactics.DeriveCost
import CatCryptCore.Tactics.DeriveTimed

/-!
# Tests for the option `derive_timed.priceProps`

With the option set, a condition is priced by what decides it:

* `if x ∈ l` costs `List.elem.timedCost x l`, linear in `l.length`;
* `if l₁ = l₂` and `if l₁ ≠ l₂` cost `List.beq.timedCost l₁ l₂`;
* `if Refused ℓ c`, a definition valued in `Prop` wrapping `ℓ < c.length`, costs one more than the
  same test written inline, and the argument of the definition is priced once;
* a reduction with a priced condition keeps its erasure theorem.

The option is on by default. With the option set to `false`, each of these conditions costs its
data arguments only.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DerivePropCostTest

open CatCrypt.Core

/-! ## Membership -/

/-- A test of membership in a list. -/
def memProg (x : ℕ) (l : List ℕ) : ℕ := if x ∈ l then 0 else 1

set_option derive_timed.priceProps true in
derive_cost memProg

example (x : ℕ) (l : List ℕ) : memProg.timedCost x l = 2 + List.elem.timedCost x l := by
  unfold memProg.timedCost; omega

example (x : ℕ) (l : List ℕ) : memProg.timedCost x l ≤ 4 * l.length + 3 := by
  have := List.elem.timedCost_le x l
  unfold memProg.timedCost; omega

/-! ## Equality of lists -/

/-- A test of equality of two lists. -/
def eqProg (a b : List ℕ) : ℕ := if a = b then 0 else 1

set_option derive_timed.priceProps true in
derive_cost eqProg

example (a b : List ℕ) : eqProg.timedCost a b = 2 + List.beq.timedCost a b := by
  unfold eqProg.timedCost; omega

/-- A test of inequality of two lists. -/
def neProg (a b : List ℕ) : ℕ := if a ≠ b then 0 else 1

set_option derive_timed.priceProps true in
derive_cost neProg

example (a b : List ℕ) : neProg.timedCost a b = 2 + List.beq.timedCost a b := by
  unfold neProg.timedCost; omega

/-! ## A definition valued in `Prop` -/

/-- The index `ℓ` lies in the list `c`. -/
def Refused (ℓ : ℕ) (c : List ℕ) : Prop := ℓ < c.length

instance (ℓ : ℕ) (c : List ℕ) : Decidable (Refused ℓ c) :=
  inferInstanceAs (Decidable (ℓ < c.length))

/-- The test written inline. -/
def inlineProg (ℓ : ℕ) (c : List ℕ) : ℕ := if ℓ < c.length then 0 else 1

derive_cost inlineProg

example (ℓ : ℕ) (c : List ℕ) : inlineProg.timedCost ℓ c = 2 + List.length.timedCost c := by
  unfold inlineProg.timedCost; omega

/-- The test through the definition. -/
def refProg (ℓ : ℕ) (c : List ℕ) : ℕ := if Refused ℓ c then 0 else 1

set_option derive_timed.priceProps true in
derive_cost refProg

example (ℓ : ℕ) (c : List ℕ) : refProg.timedCost ℓ c = 3 + List.length.timedCost c := by
  unfold refProg.timedCost; omega

/-- The test through the definition at a computed argument, priced once. -/
def refAppendProg (ℓ : ℕ) (c : List ℕ) : ℕ := if Refused ℓ (c ++ c) then 0 else 1

set_option derive_timed.priceProps true in
derive_cost refAppendProg

example (ℓ : ℕ) (c : List ℕ) :
    refAppendProg.timedCost ℓ c =
      4 + List.append.timedCost c c + List.length.timedCost (c ++ c) := by
  unfold refAppendProg.timedCost; omega

/-! ## With the option off -/

/-- `memProg` priced without the option. -/
def memOffProg (x : ℕ) (l : List ℕ) : ℕ := if x ∈ l then 0 else 1

set_option derive_timed.priceProps false in
derive_cost memOffProg

example (x : ℕ) (l : List ℕ) : memOffProg.timedCost x l = 1 := by
  unfold memOffProg.timedCost; omega

/-- `eqProg` priced without the option. -/
def eqOffProg (a b : List ℕ) : ℕ := if a = b then 0 else 1

set_option derive_timed.priceProps false in
derive_cost eqOffProg

example (a b : List ℕ) : eqOffProg.timedCost a b = 1 := by
  unfold eqOffProg.timedCost; omega

/-- `refProg` priced without the option. -/
def refOffProg (ℓ : ℕ) (c : List ℕ) : ℕ := if Refused ℓ c then 0 else 1

set_option derive_timed.priceProps false in
derive_cost refOffProg

example (ℓ : ℕ) (c : List ℕ) : refOffProg.timedCost ℓ c = 1 := by
  unfold refOffProg.timedCost; omega

/-! ## With the default -/

/-- `memProg` priced at the default of the option. -/
def memDefProg (x : ℕ) (l : List ℕ) : ℕ := if x ∈ l then 0 else 1

derive_cost memDefProg

example (x : ℕ) (l : List ℕ) : memDefProg.timedCost x l = 2 + List.elem.timedCost x l := by
  unfold memDefProg.timedCost; omega

/-- `eqProg` priced at the default of the option. -/
def eqDefProg (a b : List ℕ) : ℕ := if a = b then 0 else 1

derive_cost eqDefProg

example (a b : List ℕ) : eqDefProg.timedCost a b = 2 + List.beq.timedCost a b := by
  unfold eqDefProg.timedCost; omega

/-- `refProg` priced at the default of the option. -/
def refDefProg (ℓ : ℕ) (c : List ℕ) : ℕ := if Refused ℓ c then 0 else 1

derive_cost refDefProg

example (ℓ : ℕ) (c : List ℕ) : refDefProg.timedCost ℓ c = 3 + List.length.timedCost c := by
  unfold refDefProg.timedCost; omega

/-! ## A reduction -/

/-- A reduction branching on a test of membership. -/
noncomputable def memRed (handler : ℕ → SPTree ℕ) (l : List ℕ) (x : ℕ) : SPTree ℕ :=
  if x ∈ l then handler 0 else handler 1

set_option derive_timed.priceProps true in
derive_timed memRed

example (handler : ℕ → SPTree.Timed ℕ) (handlerCost : ℕ → ℕ) (l : List ℕ) (x : ℕ) :
    (memRed.timed handler handlerCost l x).2.erase =
      memRed (fun y => (handler y).erase) l x :=
  memRed.erase_timed handler handlerCost l x

example (handler : ℕ → SPTree.Timed ℕ) (handlerCost : ℕ → ℕ) (l : List ℕ) (x : ℕ) :
    List.elem.timedCost x l ≤ (memRed.timed handler handlerCost l x).1 := by
  simp only [memRed.timed, SPTree.Timed.delay]
  omega

end CatCrypt.Tactics.DerivePropCostTest

end
