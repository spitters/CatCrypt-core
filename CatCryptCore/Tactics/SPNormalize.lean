/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Core.Code

/-!
# `sp_normalize` — minimal monad-law simp for `SPComp`

This file exports `sp_normalize`, a lightweight simp tactic that rewrites
`SPComp` expressions using only the monad laws and the class-to-concrete
redirections (`>>=` ↦ `SPComp.bind`, `pure` ↦ `SPComp.pure`).

## Scope

Depends only on `CatCrypt.Core.Code`, so it can be imported by any file
that wants to normalize `SPComp` monad chains — including files in
`Bridge/`, `Category/`, `Crypto/` that sit below the `PkgCoherence` tactic
layer in the dependency DAG.

For the extended leaf-closer that also unfolds `RawCode.eval`, see
`Tactics/PkgCoherenceBang.lean`.

## Simp set

* `SPComp.pure_bind` — `bind (pure a) f = f a`
* `SPComp.bind_pure` — `bind c pure = c`
* `SPComp.bind_assoc` — `bind (bind c f) g = bind c (fun a => bind (f a) g)`
* `SPComp.fail_bind` — `bind fail f = fail`
* `SPComp.monad_bind_eq` — `c >>= f = SPComp.bind c f` (class redirection)
* `SPComp.monad_pure_eq` — `Pure.pure a = SPComp.pure a` (class redirection)
-/

namespace CatCrypt.Tactics

/-- Normalize an `SPComp` expression via the monad laws + class-method
    redirection.  Designed as a drop-in replacement for

    ```
    simp only [SPComp.pure_bind, SPComp.bind_pure, SPComp.bind_assoc,
               SPComp.fail_bind, SPComp.monad_bind_eq, SPComp.monad_pure_eq]
    ```

    which is a very common idiom across `Crypto/*` proofs. -/
macro "sp_normalize" : tactic =>
  `(tactic| (
    simp only [
      CatCrypt.Core.SPComp.pure_bind, CatCrypt.Core.SPComp.bind_pure,
      CatCrypt.Core.SPComp.bind_assoc, CatCrypt.Core.SPComp.fail_bind,
      CatCrypt.Core.SPComp.monad_bind_eq, CatCrypt.Core.SPComp.monad_pure_eq]))

end CatCrypt.Tactics
