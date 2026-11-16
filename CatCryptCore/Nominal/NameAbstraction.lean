/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Finiteness.Attr

/-!
# `CatCryptCore.Nominal.NameAbstraction` (shim)

The nominal-sets theory lives upstream in the `nominal-lean` package (namespace
`CatCrypt.Nominal`); this module re-exports `Nominal.NameAbstraction` and
preserves the `CatCryptCore.Nominal.NameAbstraction` import path for downstream code.
-/

@[expose] public section
