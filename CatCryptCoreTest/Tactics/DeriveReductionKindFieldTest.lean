/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.QAdvTreeKind
public import CatCryptCore.Tactics.DeriveReduction

/-!
# Test of a tree-valued field of a binder of a kind other than oracle trees

`qRed` absorbs an oracle into the circuit `B.prog (pk + 1) true` of a structure binder `B`.
`derive_reduction qRed` makes the field `QS.prog` a tree primitive of `qRed.tree`, with a costed
binder and a cost companion, and proves `qRed.erase_timed` under the hypothesis relating the
erased costed primitive to the field.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveReductionKindFieldTest

open CatCrypt.Quantum.QROM

/-- A structure with a circuit field. -/
structure QS (m n w q : ℕ) (PK : Type) where
  /-- The circuit on a key and a bit. -/
  prog : PK → Bool → QAdv m n w q

/-- The circuit of `B` with the oracle `G pk` absorbed. -/
noncomputable def qRed {m n w q : ℕ} [NeZero n] (B : QS m n w q ℕ) (G : ℕ → Fin m → Fin n) :
    ℕ → QAdv m n w 0 := fun pk => absorbOracle (B.prog (pk + 1) true) (G pk)

derive_reduction qRed

end CatCrypt.Tactics.DeriveReductionKindFieldTest
