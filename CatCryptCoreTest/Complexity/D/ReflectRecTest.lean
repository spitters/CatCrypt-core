/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.Reflect

/-!
# `reflect_d` on case analyses written with recursors

The recursors `Sum.rec`, `Option.rec`, `Bool.rec` and `Prod.rec` at a constant motive are the
case analyses `case`, `case` on `optEnc`, `ite` and the projections of a pair; each definition
below is reflected with its denotation theorem.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D.ReflectRecTest

/-- A case analysis of a sum by `Sum.rec`. -/
def sumR (x : ℕ ⊕ Bool) : ℕ :=
  Sum.rec (motive := fun _ => ℕ) (fun n => n + 1) (fun b => if b then 1 else 0) x

reflect_d sumR

example (x : ℕ ⊕ Bool) : sumR.d.den (Env.nil.cons x) = .ret (sumR x) := sumR.d_den x

/-- A case analysis of an optional value by `Option.rec`. -/
def optR (o : Option ℕ) : ℕ := Option.rec (motive := fun _ => ℕ) 0 (fun n => n + 2) o

reflect_d optR

example (o : Option ℕ) : optR.d.den (Env.nil.cons (Reflect.optEnc o)) = .ret (optR o) :=
  optR.d_den o

/-- A case analysis of a Boolean by `Bool.rec`. -/
def boolR (b : Bool) : ℕ := Bool.rec (motive := fun _ => ℕ) 3 4 b

reflect_d boolR

example (b : Bool) : boolR.d.den (Env.nil.cons b) = .ret (boolR b) := boolR.d_den b

/-- A pair taken apart by `Prod.rec`. -/
def prodR (p : ℕ × ℕ) : ℕ := Prod.rec (motive := fun _ => ℕ) (fun a b => a + b) p

reflect_d prodR

example (p : ℕ × ℕ) : prodR.d.den (Env.nil.cons p) = .ret (prodR p) := prodR.d_den p

end CatCrypt.Complexity.D.ReflectRecTest
