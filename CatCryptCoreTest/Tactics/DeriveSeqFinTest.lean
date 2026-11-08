/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
public import CatCryptCore.Tactics.StdCosts

/-!
# Tests of `derive_reduction` on sequences of computations

`bitsRed` runs `SPComp.seqVec n` over a family of sampling computations. Its tree calls the
registered tree `SPComp.seqFin.tree` at the trees of the components; its costed form calls
`SPComp.seqFin.tree.timed`, whose plain results `Fin n → Bool` are lifted to the costed closures
of the result type. No module imports this file.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveSeqFinTest

open CatCrypt.Core

/-- A sequence of `n` sampled bits, each combined with its position. -/
noncomputable def bitsRed (n : ℕ) : SPComp (Fin n → Bool) :=
  SPComp.seqVec n fun i => SPComp.bind (SPComp.sample Bool) fun b =>
    SPComp.pure (b && i.val == 0)

derive_reduction bitsRed

/-- The tree of `bitsRed` compiles to `bitsRed`. -/
example (n : ℕ) : (bitsRed.tree n).compile = bitsRed n := bitsRed.compile_tree n

end CatCrypt.Tactics.DeriveSeqFinTest
