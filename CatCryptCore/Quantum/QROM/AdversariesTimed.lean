/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.QAdvTreeKind
public import CatCryptCore.Quantum.QROM.QMLWEAux
public import CatCryptCore.Quantum.QROM.QuantumOWCPA

/-!
# Costed mirrors of the QROM adversary structures

The costed mirrors, by `derive_timed_structure`, of the QROM adversary structures whose
fields are circuits of the tree kinds of `CatCryptCore.Quantum.QROM.QAdvTreeKind`: each circuit
field becomes a costed circuit with its cost companion, and the time bound of the mirror bounds
the cost of computing each circuit followed by its run. The mirrors are shared by the costed
forms of the reductions in the companion modules `*Timed` of the QROM files.

Search words: costed mirror, QROM adversary, KEM adversary, OW-CPA adversary, time bound.

## Main definitions

* `KEMQAdv.Timed`, `QOwAuxAdv.Timed`, `QIndAuxAdv.Timed`, `QAuxDist.Timed`, `TAdv.Timed`,
  `QOWAdv.Timed` — with their erasure relations `Erases` and time bounds `TimeBound`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Quantum.QROM

derive_timed_structure KEMQAdv

derive_timed_structure QOwAuxAdv

derive_timed_structure QIndAuxAdv

derive_timed_structure QAuxDist

derive_timed_structure TAdv

derive_timed_structure QOWAdv

end CatCrypt.Quantum.QROM
