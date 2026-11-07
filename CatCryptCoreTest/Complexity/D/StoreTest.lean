/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.TranslateDt
public import CatCryptCore.Complexity.D.Reflect

/-!
# Stores of D: tests

A store `Ty.store f a` is a table over a finite ground index `f` with values of type `a`, read
and written at a computed index by the primitive operations `Prim.sget` and `Prim.sset` of one
step each; a finite ground table `FTy.tab (n + 1) r` has the operations `Prim.tget` and
`Prim.tset`.

* `storeProg`: a store over `fin 2` of bytes, initialised by `ptab`, written at three indices
  and read at one: its value (`storeProg_den`) and its cost, the four `let`s, the three writes
  and the read (`storeProg_cost`); it is in the fragment of the soundness theorem
  (`storeProg_inDtFrag`, `storeProg_cost_le_dt`).
* `tabProg`: a table `Fin 4 → Bool` whose entry at a dynamic index is negated and read
  (`tabProg_cost`).
* `reflect_d` of `bumpT` (a table `Fin 4 → BitVec 8` in a pair: `tget`, `tset`) and of `bumpS`
  (a store `Bool → ℕ` in a pair: `sget`, `sset`), with the reflected terms fixed and the cost
  theorems `bumpT.d_cost`, `bumpS.d_cost`; the refusal of a function parameter written by
  `Function.update`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D.StoreTest

open CatCrypt.Core Tm

/-- A store over `fin 2` of bytes. -/
abbrev st : Ty := .store (.fin 2) (.word 8)

/-- The write of `v` at `i` into the store bound innermost. -/
def wr (i : Fin 3) (v : BitVec 8) {Γ : List Ty} : Tm (st :: Γ) st :=
  prim (.sset (.fin 2) (.word 8) trivial (FTy.decEq _))
    (pair (var .here) (pair (lit (.fin 2) i) (lit (.word 8) v)))

/-- A store of zeros, written at the indices `0`, `1`, `2` and read at `1`. -/
def storeProg : Tm [] (.word 8) :=
  letE (ptab (f := .fin 2) (B := fun _ => .word 8) fun _ => lit (.word 8) (0 : BitVec 8))
    (letE (wr 0 5) (letE (wr 1 6) (letE (wr 2 7)
      (prim (.sget (.fin 2) (.word 8) trivial) (pair (var .here) (lit (.fin 2) (1 : Fin 3)))))))

theorem storeProg_den : storeProg.den Env.nil = .ret (6 : BitVec 8) := by
  rfl

/-- Eight steps: the four `let`s (the initial table and the three writes bound), the three
writes and the read, one step each; the table of literals built by `ptab` and the literal
arguments cost nothing. -/
theorem storeProg_cost : storeProg.cost Env.nil = 8 := by
  decide

theorem storeProg_inDtFrag : storeProg.InDtFrag := by
  simp [storeProg, wr, InDtFrag, Tm.Pure, Prim.unitCost, Ty.isArr]

/-- The cost of `storeProg` is bounded by its allowance and the charges of `Tm.dt`. -/
theorem storeProg_cost_le_dt {η : EnvHat []} {ρ : Env []} (hρ : SimEnv η ρ) :
    storeProg.cost ρ ≤ storeProg.allow + SPTree.Timed.stepTime (storeProg.dt η) :=
  cost_le_dt storeProg storeProg_inDtFrag hρ

/-- A table `Fin 4 → Bool` (the innermost variable), its entry at the index `i` (the second
variable) negated, read at `i`. -/
def tabProg : Tm [.base (.tab 4 .bool), .fin 3] .bool :=
  letE (prim (.tset 3 .bool) (pair (var .here) (pair (var (.there .here))
      (prim .bnot (prim (.tget 3 .bool) (pair (var .here) (var (.there .here))))))))
    (prim (.tget 3 .bool) (pair (var .here) (var (.there (.there .here)))))

/-- Five steps: the `let`, the read and the negation of the entry, the write, and the final
read, one step each. -/
theorem tabProg_cost (t : Fin 4 → Bool) (i : Fin 4) :
    tabProg.cost ((Env.nil.cons (τ := .fin 3) i).cons (τ := .base (.tab 4 .bool)) t) = 5 := by
  rfl

/-- A table of bytes in a pair, its entry at `i` incremented: a table write and a table read. -/
def bumpT (s : (Fin 4 → BitVec 8) × Bool) (i : Fin 4) : (Fin 4 → BitVec 8) × Bool :=
  (Function.update s.1 i (s.1 i + 1), s.2)

reflect_d bumpT

example : bumpT.d = .pair (.prim (.tset 3 (.word 8)) (.pair (.fst (.var (.there .here)))
    (.pair (.var .here) (.prim (.wadd 8) (.pair (.prim (.tget 3 (.word 8))
      (.pair (.fst (.var (.there .here))) (.var .here))) (.lit (.word 8) (1 : BitVec 8)))))))
    (.snd (.var (.there .here))) := rfl

/-- The read, the addition and the write, one step each. -/
example (s : (Fin 4 → BitVec 8) × Bool) (i : Fin 4) :
    bumpT.d.cost (Env.cons (τ := .fin 3) i
      (Env.cons (τ := .prod (.base (.tab 4 (.word 8))) .bool) s Env.nil)) = 3 := by
  rw [bumpT.d_cost]
  rfl

/-- A store `Bool → ℕ` in a pair, its entry at `i` incremented: a store write and a store
read. -/
def bumpS (s : (Bool → ℕ) × Bool) (i : Bool) : (Bool → ℕ) × Bool :=
  (Function.update s.1 i (s.1 i + 1), s.2)

reflect_d bumpS

example : bumpS.d = .pair (.prim (.sset .bool .nat (Ty.FO_of_foB rfl) instDecidableEqBool)
    (.pair (.fst (.var (.there .here))) (.pair (.var .here) (.prim .natAdd
      (.pair (.prim (.sget .bool .nat (Ty.FO_of_foB rfl))
        (.pair (.fst (.var (.there .here))) (.var .here))) (.natLit 1))))))
    (.snd (.var (.there .here))) := rfl

/-- The read and the write, one step each, and the addition at its logarithmic cost. -/
example (s : (Bool → ℕ) × Bool) (i : Bool) :
    bumpS.d.cost (Env.cons (τ := .bool) i
      (Env.cons (τ := .prod (.store .bool .nat) .bool) s Env.nil)) =
      2 + Prim.natAdd.cost ((s.1 i, 1) : ℕ × ℕ) := by
  rw [bumpS.d_cost]
  change 0 + (0 + (0 + 0 + 1 + 0 + Prim.natAdd.cost ((s.1 i, 1) : ℕ × ℕ))) + 1 + 0 = _
  omega

/-- A function parameter written by `Function.update`. -/
def updP (f : Bool → ℕ) (b : Bool) : ℕ := (Function.update f b 0) b

/--
error: reflect_d: a function parameter written by Function.update in `Function.update f b
  0`; pass the table as a component of the state
-/
#guard_msgs in
reflect_d updP

end CatCrypt.Complexity.D.StoreTest
