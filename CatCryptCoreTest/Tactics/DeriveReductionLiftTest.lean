/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signatures.OracleProgTimed
public import CatCryptCore.Tactics.DeriveReduction

/-!
# Tests of computations lifted into oracle programs and of handler binders

Reductions into `EUFCMAAdversary` derived by `derive_reduction`:

* `redHandler` takes a handler binder `h : Bool → OracleProg ℕ ℕ (ℕ × ℕ)`, whose erasure
  theorem is stated at `fun a => (h a).erase`;
* `redSample` lifts the sampling `SPComp.sample Bool`, reflected into a sampling node;
* `redMixed` lifts a sampling and a compiled computation tree;
* `redKeygen` lifts the key generation `S.keygen` of a scheme binder and answers queries by
  `implS`, which lifts `S.sign sk 1`: computation primitives with hypotheses;
* `redStep` lifts through `OracleProg.step`, unfolded.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveReductionLiftTest

open CatCrypt.Core CatCrypt.Crypto

/-- The forger that records the answers of the handler `h` to the queries of `A`. -/
noncomputable def redHandler (h : Bool → OracleProg ℕ ℕ (ℕ × ℕ))
    (A : Signatures.EUFCMAAdversary Bool ℕ ℕ (Bool × ℕ)) :
    Signatures.EUFCMAAdversary ℕ ℕ ℕ ℕ where
  run pk := (OracleProg.collectLog (fun b => (h b).bind fun r => .pure ((b, r.2), [r.2]))
    (A.run pk)).bind fun x => .pure (x.2.length, pk)

derive_reduction redHandler

/-- The forger that samples a bit and answers the queries of `A` by it. -/
noncomputable def redSample (A : Signatures.EUFCMAAdversary Bool ℕ ℕ ℕ) :
    Signatures.EUFCMAAdversary ℕ ℕ ℕ ℕ where
  run pk := .lift (SPComp.sample Bool) fun e =>
    ((A.run pk).bindQueries (fun b => .query (cond (e && b) 1 0) fun ev => .pure ev)).bind
      fun o => .pure (cond o.1 pk 0, o.2)

derive_reduction redSample

/-- The forger that samples a bit by a computation and one by a compiled computation tree. -/
noncomputable def redMixed (A : Signatures.EUFCMAAdversary Bool ℕ ℕ ℕ) :
    Signatures.EUFCMAAdversary ℕ ℕ ℕ ℕ where
  run pk := .lift (SPComp.sample Bool) fun e =>
    .lift (SPTree.compile (SPTree.sample Bool inferInstance ⟨true⟩ fun e => SPTree.ret e))
      fun e' => ((A.run pk).bindQueries (fun b => .query (cond (e && e' && b) 1 0) fun ev =>
        .pure ev)).bind fun o => .pure (cond o.1 pk 0, o.2)

derive_reduction redMixed

/-- A query handler that signs with `S` under `sk` or samples a bit, recording the answers. -/
noncomputable def implS (S : Signatures.SigScheme ℕ ℕ ℕ ℕ) (sk : ℕ) :
    Bool → OracleProg ℕ ℕ ((Bool × ℕ) × List ℕ)
  | true => .lift (S.sign sk 1) fun σ => .query σ fun c => .pure ((true, c), [c])
  | false => .lift (SPComp.sample Bool) fun e =>
      if e then .query 0 fun c => .pure ((e, c), []) else .pure ((e, 0), [])

/-- The forger that generates a key pair of `S` and answers the queries of `A` by `implS`. -/
noncomputable def redKeygen (S : Signatures.SigScheme ℕ ℕ ℕ ℕ)
    (A : Signatures.EUFCMAAdversary Bool ℕ ℕ (Bool × ℕ)) :
    Signatures.EUFCMAAdversary ℕ ℕ ℕ ℕ where
  run pk := .lift S.keygen fun ks =>
    (OracleProg.collectLog (implS S ks.2) (A.run (pk + ks.1))).bind fun x =>
      .pure (x.2.length, pk)

derive_reduction redKeygen

/-- The forger that generates a key pair of `S` and signs each query of `A`, through
`OracleProg.step`. -/
noncomputable def redStep (S : Signatures.SigScheme ℕ ℕ ℕ ℕ)
    (A : Signatures.EUFCMAAdversary Bool ℕ ℕ ℕ) :
    Signatures.EUFCMAAdversary ℕ ℕ ℕ ℕ where
  run pk := (OracleProg.step S.keygen).bind fun ks =>
    ((A.run pk).bindQueries (fun (b : Bool) =>
      (OracleProg.step (S.sign ks.2 (cond b 1 0))).bind fun σ => .pure σ)).bind
        fun o => .pure (cond o.1 pk 0, o.2)

derive_reduction redStep

end CatCrypt.Tactics.DeriveReductionLiftTest
