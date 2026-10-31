/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.LinkTimed

/-!
# Tests of `link_timed` on a reduction over record parameters

`blindRed` takes a group parameter `gp : GroupRec`, whose carrier and scalars are type fields,
and a CRS `crs : ScalarCRS gp`. It samples a scalar, subtracts the scalar of the CRS and
divides by the field functions of `gp`, and calls the adversary. `derive_reduction` makes the
two field functions parameters of the tree with cost companions; `reflect_d` unbundles `gp`
into two finite ground types and the binders of its other fields and represents `crs.td` as a
value of the context; `link_timed` keeps the field binders in place and instantiates the binder
`gp` of `blindRed.tree.timed` by the unbundled record.

## Main definitions

* `GroupRec`, `ScalarCRS`, `blindRed`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.LinkTimedRecordTest

open CatCrypt.Core CatCrypt.Complexity.D CatCrypt.Complexity.D.Reflect

/-- A group parameter with its carrier and scalars as type fields. -/
structure GroupRec where
  /-- The carrier. -/
  G : Type
  /-- The scalars. -/
  S : Type
  /-- The scalars are finite. -/
  [finS : Fintype S]
  /-- The scalars are nonempty. -/
  [neS : Nonempty S]
  /-- The generator. -/
  gen : G
  /-- Scalar subtraction. -/
  sub : S → S → S
  /-- Scalar division. -/
  div : S → S → S

/-- A CRS over a group parameter. -/
structure ScalarCRS (gp : GroupRec) where
  /-- A group element. -/
  h : gp.G
  /-- The trapdoor. -/
  td : gp.S

/-- Sample a scalar `t` and call the adversary on `s / (t - td)`. -/
noncomputable def blindRed (gp : GroupRec) (crs : ScalarCRS gp) (A : gp.S → SPComp Bool)
    (s : gp.S) : SPComp Bool := do
  let t ← @SPComp.sample gp.S gp.finS gp.neS
  A (gp.div s (gp.sub t crs.td))

derive_reduction blindRed (adv := A)

reflect_d blindRed.tree

link_timed blindRed

example := @blindRed.tree.d_timedSim

example := @blindRed.tree.d_cost_le

end CatCrypt.Tactics.LinkTimedRecordTest
