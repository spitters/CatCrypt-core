/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.CategoryTheory.KleisliPMFMarkov

/-!
# `CatCryptCore.Category.KlPMF` (shim)

The Markov category structure on `KleisliCat PMF` is in
`CatCryptCore.ForMathlib.CategoryTheory.KleisliPMFMarkov`; this module re-exports it and
preserves the `CatCryptCore.Category.KlPMF` import path for downstream code.
-/

@[expose] public section
