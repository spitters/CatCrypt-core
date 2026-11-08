/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import PolyFun.PFunctor.Slice

/-!
# Dependent sums and products along a map, and polynomial functors

This module re-exports `PolyFun.PFunctor.Slice`, which declares the adjoint triple
`Σ_f ⊣ f* ⊣ Π_f` on families, the polynomial functor `PFunctor.Slice.ofMap` of a map, the
distributive law `PFunctor.Slice.distribEquiv` and the closure of indexed polynomials under Σ, Π
and pullback (`IPFunctor.sigmaPost`, `IPFunctor.piPost`, `IPFunctor.pbPre`, `IPFunctor.sigmaPre`,
`IPFunctor.piPre`).
-/
