/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import CatCryptCore.Tactics.DeriveTimed
import CatCryptCore.Tactics.DeriveCost
public import CatCryptCore.Tactics.DeriveTimed.Basic
public import CatCryptCore.Tactics.StdCosts

/-!
# Tests for stores in data (rule (p))

Rule (p) of `CatCryptCore.Tactics.DeriveTimed`, under the option `derive_timed.storeData`: a
function with finite domains and a first-order codomain at a component of data is a store. It is
built by tabulation or by table writes, read at one unit per argument, and passed to a function
parameter with the companion zero.

The costs are those of the language D (`CatCryptCore.Complexity.D.Semantics`): a table built by
`ptab` evaluates each entry, a write `sset` takes one step, a read `sget` or `tget` one step.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimedStoreTest

open CatCrypt.Core

set_option derive_timed.storeData true

/-! ## Build: a closure placed at a store is tabulated -/

/-- A counter and a store over `Fin 4` built from it. -/
def mkStore (k : ℕ) : SPTree (ℕ × (Fin 4 → ℕ)) :=
  SPTree.ret (k, fun j => j.val + k)

derive_timedmkStore

/-- The store is tabulated at its four points, one addition each (`ptab`). -/
example (k : ℕ) : (mkStore.timed k).1 = ∑ _j : Fin 4, 1 := rfl

example (k : ℕ) : (mkStore.timed k).2.erase = mkStore k := mkStore.erase_timed k

/-- A counter and a store over `Fin 4`, written once per step. -/
def build : ℕ → ℕ × (Fin 4 → ℕ)
  | 0 => (0, fun _ => 0)
  | n + 1 => (n + 1, Function.update (build n).2 ⟨n % 4, Nat.mod_lt _ (by decide)⟩ n)

derive_costbuild

/-- The base case: the match and the constant store tabulated at its four points. -/
example : build.timedCost 0 = 1 + ∑ _j : Fin 4, 0 := by
  rw [build.timedCost]

/-- A step: the recursive call, the index and one table write (`sset`), no tabulation. -/
example (n : ℕ) : build.timedCost (n + 1) = build.timedCost n + 5 := by
  rw [build.timedCost, Function.update.timedCost_eq]
  omega

/-- A function parameter placed at a store: tabulated by its companion, one application at each
point. -/
def parStore (f : Fin 2 → ℕ) : SPTree (ℕ × (Fin 2 → ℕ)) := SPTree.ret (0, f)

derive_timedparStore

example (f fCost : Fin 2 → ℕ) : (parStore.timed f fCost).1 = ∑ j : Fin 2, (1 + fCost j) := rfl

/-- A kept `let` of a closure, applied and placed at a store. -/
def letStore (q : ℕ) : SPTree (ℕ × (Fin 2 → ℕ)) :=
  let g := fun j : Fin 2 => q * j.val
  SPTree.ret (g 1, g)

derive_timedletStore

/-- The closure is tabulated at the store, one multiplication at each point, and applied once. -/
example (q : ℕ) : (letStore.timed q).1 = ∑ _j : Fin 2, 1 + 1 := rfl

/-! ## Read: a store applied, read from data -/

/-- The entry `i` of the store of `s`. -/
def rd (s : ℕ × (Fin 4 → ℕ)) (i : Fin 4) : SPTree ℕ := SPTree.ret (s.2 i)

derive_timedrd

/-- One read (`sget`); the store has no cost companion. -/
example (s : ℕ × (Fin 4 → ℕ)) (i : Fin 4) : (rd.timed s i).1 = 1 := rfl

example (s : ℕ × (Fin 4 → ℕ)) (i : Fin 4) : (rd.timed s i).2.erase = rd s i :=
  rd.erase_timed s i

/-! ## Pass: a store read from data passed to a function parameter -/

/-- The sum of the three entries of `v`. -/
def sum3 (v : Fin 3 → ℕ) : ℕ := v 0 + v 1 + v 2

derive_costsum3

/-- The store of `s` passed to `sum3`: its companion is zero. -/
def useStore (s : ℕ × (Fin 3 → ℕ)) : SPTree ℕ := SPTree.ret (sum3 s.2)

derive_timeduseStore

/-- The call of `sum3` with the companion zero: each of its reads costs one unit. -/
example (s : ℕ × (Fin 3 → ℕ)) :
    (useStore.timed s).1 = 1 + sum3.timedCost s.2 (fun _ => 0) := rfl

/-! ## Refusal: a function over a domain that is not finite -/

/-- A box: a carrier with an insertion and a read. -/
structure Box where
  /-- The carrier. -/
  T : Type
  /-- Insert a key. -/
  put : T → ℕ → T
  /-- Read at a key. -/
  read : T → ℕ → ℕ

/-- A box and a value of its carrier. -/
structure Cell where
  /-- The box. -/
  bx : Box
  /-- The value. -/
  val : bx.T

/-- Read the entry of `p`, insert `x` into its value and read at `x`. -/
noncomputable def cellRed (tab : ℕ → Option Cell) (p x : ℕ) (D : ℕ → SPTree Bool) :
    SPTree Bool :=
  match tab p with
  | some c => D (c.bx.read (c.bx.put c.val x) x)
  | none => D 0

/--
error: derive_timed: a function bound in data: the field
`CatCrypt.Tactics.DeriveTimedStoreTest.Box.read` is applied in `c.bx.read
  (c.bx.put c.val x) x`; its type `c.bx.T → ℕ → ℕ` has the domain `c.bx.T`, which is not
finite, so it is not a store (rule (p))
-/
#guard_msgs (whitespace := lax) in
derive_timedcellRed

end CatCrypt.Tactics.DeriveTimedStoreTest
