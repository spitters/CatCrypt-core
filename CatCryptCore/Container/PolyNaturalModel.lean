/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import PolyFun.PFunctor.NaturalModel

/-!
# The natural-model structure of a universe polynomial

This module re-exports `PolyFun.PFunctor.NaturalModel`, which declares cartesian maps of
polynomials (`PFunctor.CartLens`), the Σ- and Π-structures of a universe polynomial and their
codes. It adds the bijectivity of the backward maps of the lens of a `CartLens`
(`PFunctor.CartLens.toLens_bijective`).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace PFunctor

namespace CartLens

variable {P Q : PFunctor.{u, u}}

/-- The backward maps of the lens of a cartesian map are bijections. -/
theorem toLens_bijective (l : CartLens P Q) (a : P.A) :
    Function.Bijective (l.toLens.toFunB a) :=
  (l.fibEquiv a).symm.bijective

end CartLens

end PFunctor
