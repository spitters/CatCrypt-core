/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Nominal.Fresh

/-!
# `CatCryptCore.Nominal.Fresh` (shim)

The nominal-sets theory lives upstream in the `nominal-lean` package (namespace
`CatCrypt.Nominal`); this module re-exports `Nominal.Fresh` and preserves the
`CatCryptCore.Nominal.Fresh` import path for downstream code.
-/
