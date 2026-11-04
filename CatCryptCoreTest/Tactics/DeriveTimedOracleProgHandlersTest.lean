/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signatures.OracleProgTimed
public import CatCryptCore.Tactics.DeriveReduction

/-!
# Tests of the handler combinators of the oracle-program tree kind

Two reductions into `EUFCMAAdversary` whose oracle program replaces the queries of the
adversary's program by a handler program: `redBQ` through `OracleProg.bindQueries` and `redCL`
through `OracleProg.collectLog`. Each is derived by `derive_reduction`, through the costed
combinators `OracleProg.Timed.bindQueries` and `OracleProg.Timed.collectLog` registered in
`CatCryptCore.Crypto.Signatures.OracleProgTimed`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimedOracleProgHandlersTest

open CatCrypt.Core CatCrypt.Crypto

/-- A query handler: sample a bit by a computation tree, query the oracle at `f (e && b)`, and
return the bit with the answer. -/
noncomputable def qh (f : Bool → ℕ) (b : Bool) : OracleProg ℕ ℕ (Bool × ℕ) :=
  .lift (SPTree.compile (SPTree.sample Bool inferInstance ⟨true⟩ fun e => SPTree.ret e))
    fun e => .query (f (e && b)) fun ev => .pure (e, ev)

/-- The forger that answers the queries of `A` by `qh f`. -/
noncomputable def redBQ (f : Bool → ℕ) (A : Signatures.EUFCMAAdversary Bool ℕ ℕ (Bool × ℕ)) :
    Signatures.EUFCMAAdversary ℕ ℕ ℕ ℕ where
  run pk := ((A.run pk).bindQueries (qh f)).bind fun o => .pure (f o.1, o.2.2)

derive_reduction redBQ

/-- The forger that answers the queries of `A` by `qh f`, recording each answer, and outputs
the number of records. -/
noncomputable def redCL (f : Bool → ℕ)
    (A : Signatures.EUFCMAAdversary Bool ℕ ℕ (Bool × ℕ)) : Signatures.EUFCMAAdversary ℕ ℕ ℕ ℕ where
  run pk := (OracleProg.collectLog (fun b => (qh f b).bind fun r => .pure (r, [r.2]))
    (A.run pk)).bind fun x => .pure (x.2.length, pk)

derive_reduction redCL

end CatCrypt.Tactics.DeriveTimedOracleProgHandlersTest
