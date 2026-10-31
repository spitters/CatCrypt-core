/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.Reflect
public import CatCryptCore.Examples.CyclicGroupDDH
public import CatCryptCore.Examples.GroupParam

/-!
# Tests for `reflect_d` on record parameters and associated types

* `encOtp`: a record parameter `S : EncRec K M C` without type fields, a binder of the
  theorems; its pure field `S.enc` is a D function with its hypothesis, its program field
  `S.coins` a D function with the hypothesis of a computation parameter;
* `gpBlind`: a record `gp : GroupParam` with the type fields `G` and `Scalar`, unbundled into
  two finite ground types and the binders of its other fields; a sample over `gp.Scalar`;
* `crsShift`: a record `crs : ScalarCRS gp` over the unbundled `gp`, whose datum `crs.td` is a
  value of the context;
* `cgPow`: an instance `[CyclicGroup G]` with the associated type `CyclicGroup.Exp G`, unbundled;
  a sample over the exponents and the methods `pow` and `mul`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D.ReflectRecordTest

open CatCrypt.Core CatCrypt.Complexity.D CatCrypt.Examples CatCryptCore.Examples.CyclicGroupDDH

/-- An encryption record with a pure field and a program field. -/
structure EncRec (K M C : Type) where
  /-- Encryption. -/
  enc : K → M → C
  /-- A message drawn under a key. -/
  coins : K → SPComp M

/-- Sample a key, draw a message by `S.coins`, encrypt it by `S.enc` and call the adversary. -/
noncomputable def encOtp {K M C : Type} [Fintype K] [Nonempty K] (S : EncRec K M C)
    (A : C → SPComp Bool) : SPComp Bool := do
  let k ← SPComp.sample K
  let m ← S.coins k
  A (S.enc k m)

reflect_d encOtp

example := @encOtp.d_den

example := @encOtp.d_cost

/-- Sample a scalar `x` and call the adversary on `g · g^x`. -/
noncomputable def gpBlind (gp : GroupParam) (A : gp.G → SPComp Bool) : SPComp Bool := do
  let x ← SPComp.sample gp.Scalar
  A (gp.groupMul gp.generator (gp.exp x))

reflect_d gpBlind

example := @gpBlind.d_den

example := @gpBlind.d_cost

/-- A record over a group parameter holding a scalar. -/
structure ScalarCRS (gp : GroupParam) where
  /-- The scalar. -/
  td : gp.Scalar

/-- Subtract the scalar of the CRS by a function parameter. -/
def crsShift (gp : GroupParam) (crs : ScalarCRS gp) (sub : gp.Scalar → gp.Scalar → gp.Scalar)
    (x : gp.Scalar) : gp.Scalar :=
  sub x crs.td

reflect_d crsShift

example := @crsShift.d_den

example := @crsShift.d_cost

/-- Sample an exponent `e` and call the adversary on `g^e · g^e`. -/
noncomputable def cgPow {G : Type} [CyclicGroup G] (A : G → SPComp Bool) : SPComp Bool := do
  let e ← SPComp.sample (CyclicGroup.Exp G)
  A (CyclicGroup.mul (CyclicGroup.pow e) (CyclicGroup.pow e))

reflect_d cgPow

example := @cgPow.d_den

example := @cgPow.d_cost

end CatCrypt.Complexity.D.ReflectRecordTest
