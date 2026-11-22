/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.InstrumentCP
public import QuantumFoundations.InstrumentCP

/-!
# Projectors of the core as QuantumFoundations projectors

`CatCrypt.Quantum.GentleMeasurement.Projector` and
`Quantum.GentleMeasurement.Projector` of QuantumFoundations are structures with the
same fields. `Projector.toQF` sends a core projector to the QuantumFoundations
projector with the same matrix, and `Projector.toQF_val` states that the matrix is
unchanged, so a QuantumFoundations theorem about projectors applies to a core
projector through `toQF`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Quantum.GentleMeasurement

variable {d : ℕ}

/-- The QuantumFoundations projector with the same matrix as `P`. -/
def Projector.toQF (P : Projector d) : _root_.Quantum.GentleMeasurement.Projector (Fin d) :=
  ⟨P.val, P.self_adjoint, P.idempotent⟩

/-- `Projector.toQF` keeps the matrix. -/
@[simp] theorem Projector.toQF_val (P : Projector d) : P.toQF.val = P.val := rfl

end CatCrypt.Quantum.GentleMeasurement
