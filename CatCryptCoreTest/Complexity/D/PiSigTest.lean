/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.TranslateDt

/-!
# Dependent products and sums of D: tests

The family `fam` over `Bool` is a byte at `true` and a boolean at `false`; `msg = sig bool fam`
is a message whose tag selects the type of its value, `rcd = pi bool fam` a record with a
component of each type.

* `sizeT`: a case analysis on a message (`scase`): one step plus the branch, its denotation
  and cost at both tags (`sizeT_den_true`, `sizeT_cost_true`, `sizeT_cost_false`), and the bound
  by the charges of `Tm.dt` from the soundness theorem at every message (`sizeT_cost_le_dt`).
* `mkT`: a record built by `ptab` from a byte, each component an operation of one step: the
  table costs the sum of its components (`mkT_cost`), and a component is read at a static index
  at no cost (`fstT_cost`).
* `readT`: a table of bytes read at a dynamic index (`fcase` on the index, then `papp`): one
  step, whatever the size of the table (`readT_cost`, `readT_cost_le_dt`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D.PiSigTest

open CatCrypt.Core Tm

/-- A byte at `true`, a boolean at `false`. -/
def fam (b : Bool) : Ty := bif b then .word 8 else .bool

/-- A message: a tag and a value of the type the tag selects. -/
abbrev msg : Ty := .sig .bool fam

/-- A record with a component of the type of each tag. -/
abbrev rcd : Ty := .pi .bool fam

/-- The size of the value of a message in bits: the bit length of the byte, one for a
boolean. -/
def sizeT : Tm [msg] .nat :=
  scase (var .here) fun b => match b with
    | true => prim (.wtoNat 8) (var .here)
    | false => natLit 1

theorem sizeT_den_true :
    sizeT.den (Env.nil.cons (⟨true, (5 : BitVec 8)⟩ : Val msg)) = .ret (5 : ℕ) := by
  rfl

/-- At a byte: the case analysis and the conversion. -/
theorem sizeT_cost_true (x : BitVec 8) :
    sizeT.cost (Env.nil.cons (⟨true, x⟩ : Val msg)) = 2 := by
  rfl

/-- At a boolean: the case analysis only. -/
theorem sizeT_cost_false (x : Bool) :
    sizeT.cost (Env.nil.cons (⟨false, x⟩ : Val msg)) = 1 := by
  rfl

theorem sizeT_inDtFrag : sizeT.InDtFrag := by
  refine ⟨rfl, fun b => ?_⟩
  cases b <;> simp [InDtFrag, Prim.unitCost, Ty.isArr]

/-- The cost of `sizeT` is bounded by its allowance and the charges of `Tm.dt` at every
message. -/
theorem sizeT_cost_le_dt {η : EnvHat [msg]} {ρ : Env [msg]} (hρ : SimEnv η ρ) :
    sizeT.cost ρ ≤ sizeT.allow + SPTree.Timed.stepTime (sizeT.dt η) :=
  cost_le_dt sizeT sizeT_inDtFrag hρ

/-- The record of a byte `x`: the byte `x XOR 1` and whether `x` is zero. -/
def mkT : Tm [.word 8] rcd :=
  ptab fun b => match b with
    | true => prim (.wxor 8) (pair (var .here) (lit (.word 8) (1 : BitVec 8)))
    | false => prim (.weq 8) (pair (var .here) (lit (.word 8) (0 : BitVec 8)))

/-- The table is built at the sum of the costs of its components. -/
theorem mkT_cost (x : BitVec 8) : mkT.cost (Env.nil.cons x) = 2 := by
  rfl

/-- The byte component of the record, read at a static index. -/
def fstT : Tm [.word 8] (.word 8) := papp mkT true

theorem fstT_den : fstT.den (Env.nil.cons (6 : BitVec 8)) = .ret (7 : BitVec 8) := by
  rfl

/-- A static read costs nothing beyond the table. -/
theorem fstT_cost (x : BitVec 8) : fstT.cost (Env.nil.cons x) = 2 := by
  rfl

/-- A table of bytes indexed by `Bool`, read at the index given by the second variable: a case
analysis on the index, then a static read. -/
def readT : Tm [.pi .bool fun _ => .word 8, .bool] (.word 8) :=
  fcase (var (.there .here)) fun b => papp (var .here) b

/-- A read at a dynamic index costs one step. -/
theorem readT_cost (h : Val (.pi .bool fun _ => .word 8)) (b : Bool) :
    readT.cost ((Env.nil.cons (τ := .bool) b).cons h) = 1 := by
  rfl

theorem readT_inDtFrag : readT.InDtFrag := ⟨rfl, fun _ => rfl⟩

/-- The cost of the read is bounded by its allowance and its charge, one unit. -/
theorem readT_cost_le_dt {η : EnvHat [.pi .bool fun _ => .word 8, .bool]}
    {ρ : Env [.pi .bool fun _ => .word 8, .bool]} (hρ : SimEnv η ρ) :
    readT.cost ρ ≤ readT.allow + SPTree.Timed.stepTime (readT.dt η) :=
  cost_le_dt readT readT_inDtFrag hρ

end CatCrypt.Complexity.D.PiSigTest
