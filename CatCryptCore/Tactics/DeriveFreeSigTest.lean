/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveFreeSig
public import CatCryptCore.Core.SPTreeTimed
public import CatCryptCore.Crypto.Party.ProgE

/-!
# Tests of `derive_free_sig`

`derive_free_sig` run on two program-tree types; its run on `SPTree` is the signature of
`CatCryptCore.Core.SPTreeFree`.

* `Party.ProgE Op E O`, whose parameters precede the result type, with its bind;
* `SPTree.Timed`, a type in `Type 1` declared in a `meta section`.

Search words: polynomial functor, signature, free monad, deriving, tests.
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Tactics.DeriveFreeSigTest

open CatCrypt.Core

/-! ## `Party.ProgE`: parameters before the result type -/

derive_free_sig CatCrypt.Crypto.Party.ProgE (namespace := ProgEGen)
  (bind := CatCrypt.Crypto.Party.ProgE.bind)

/-- The generated equivalence of `ProgE` with the free monad over its signature. -/
example (Op E O α : Type) :
    CatCrypt.Crypto.Party.ProgE Op E O α ≃ PFunctor.FreeM (ProgEGen.Sig Op E O) α :=
  ProgEGen.equivFreeM

/-- The generated signature of `ProgE` is the sum of its four summands. -/
example (Op E O : Type) : PFunctor.Equiv (ProgEGen.Sig Op E O)
    (ProgEGen.Sig.recv Op E O + (ProgEGen.Sig.send Op E O +
      (ProgEGen.Sig.opN Op E O + ProgEGen.Sig.fail Op E O))) :=
  ProgEGen.sigEquivSum Op E O

/-! ## `SPTree.Timed`: a tree type in `Type 1` -/

derive_free_sig SPTree.Timed (namespace := TimedGen)

/-- The generated signature of `SPTree.Timed` has positions in `Type 1`. -/
example : PFunctor.{1, 0} := TimedGen.Sig

/-- The generated equivalence of `SPTree.Timed` with the free monad over its signature. -/
noncomputable example (α : Type) : SPTree.Timed α ≃ PFunctor.FreeM TimedGen.Sig α :=
  TimedGen.equivFreeM

end CatCrypt.Tactics.DeriveFreeSigTest

end
