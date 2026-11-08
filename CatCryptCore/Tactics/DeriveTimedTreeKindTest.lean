/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signatures.OracleProgTimed
import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
public import CatCryptCore.Tactics.StdCosts

/-!
# Tests of the oracle-program tree kind of `derive_timed`

A forger structure `MiniForger` with an oracle-program field, its costed mirror, an oracle
program `miniRun` whose `lift` node runs a computation tree, and a reduction `miniRed` building
a forger from it, with their derived costed forms and erasure theorems. The tree kind of oracle
programs is registered by `register_tree_kind` in `CatCryptCore.Crypto.Signatures.OracleProgTimed`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimedTreeKindTest

open CatCrypt.Core CatCrypt.Crypto

/-- A forger: an oracle program on a public key that outputs a candidate forgery. -/
structure MiniForger (PK Msg Sig : Type) : Type 1 where
  /-- The forger's program on a public key. -/
  run : PK → OracleProg Msg Sig (Msg × Sig)

derive_timed_structure MiniForger

/-- Sample a bit by a computation tree, query the oracle on `g pk`, output the message and the
answer. -/
noncomputable def miniRun {PK Msg Sig : Type} (g : PK → Msg) (pk : PK) :
    OracleProg Msg Sig (Msg × Sig) :=
  .lift (SPTree.compile (SPTree.sample Bool inferInstance ⟨true⟩ fun b => SPTree.ret b))
    fun _ => .query (g pk) fun s => .pure (g pk, s)

derive_timed miniRun

/-- The forger running `miniRun g`. -/
noncomputable def miniRed {PK Msg Sig : Type} (g : PK → Msg) : MiniForger PK Msg Sig where
  run pk := .lift (SPTree.compile (SPTree.sample Bool inferInstance ⟨true⟩ fun b => SPTree.ret b))
    fun _ => .query (g pk) fun s => .pure (g pk, s)

derive_reduction miniRed

end CatCrypt.Tactics.DeriveTimedTreeKindTest
