/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.FoldRange
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# `CatCryptCore.Hax.FoldRange` (shim)

The reasoning lemmas for `Hax.foldRange` are in `HaxLean.FoldRange` of the hax-lean
package; this module re-exports them and preserves the `CatCryptCore.Hax.FoldRange` import
path for downstream code, together with the Mathlib tactic modules `norm_num` and `ring`
that importers of this path use.
-/

@[expose] public section
