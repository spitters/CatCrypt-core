/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.CPMap
public import QuantumFoundations.MatrixMap

/-!
# Complete positivity: `IsCPMap` and `Quantum.MatrixMap.IsCP`

`CatCrypt.Quantum.IsCPMap` amplifies a map `Φ` on `Fin n × Fin n` matrices by `id_k ⊗ Φ`
(`tensorIdMap`), with the ancilla `Fin k` on the left of the index `Fin k × Fin n`.
QuantumFoundations' `Quantum.MatrixMap.IsCP` amplifies by `Φ ⊗ id_k`
(`Quantum.MatrixMap.amplify`), with the ancilla on the right of `Fin n × Fin k`. Swapping the
two factors of the index (`Prod.swap`) turns one amplification into the other and preserves
positive semidefiniteness, so the two predicates agree. The argument follows Quang Dao's
`Bridge/CPMap` in QuantumFoundations.

## Main results

* `CatCrypt.Quantum.tensorIdMap_submatrix_swap`: `id_k ⊗ Φ` is `Φ ⊗ id_k` conjugated by the
  swap of the index factors.
* `CatCrypt.Quantum.isCPMap_iff_isCP`: the two notions of complete positivity agree.
* `CatCrypt.Quantum.IsCPMap.isCP`, `CatCrypt.Quantum.isCPMap_of_isCP`: the two directions.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder
open Matrix

namespace CatCrypt.Quantum

variable {n : ℕ}

/-- Amplifying on the left, `id_k ⊗ Φ`, is amplifying on the right, `Φ ⊗ id_k`, after swapping
the factors of the index on the input and the output. -/
theorem tensorIdMap_submatrix_swap (Φ : _root_.Quantum.MatrixMap (Fin n) (Fin n)) (k : ℕ)
    (ρ : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ) :
    tensorIdMap Φ k (ρ.submatrix Prod.swap Prod.swap) =
      (Φ.amplify (Fin k) ρ).submatrix Prod.swap Prod.swap :=
  rfl

/-- Complete positivity with the ancilla on the left (`IsCPMap`) is complete positivity with the
ancilla on the right (`Quantum.MatrixMap.IsCP`). -/
theorem isCPMap_iff_isCP (Φ : _root_.Quantum.MatrixMap (Fin n) (Fin n)) :
    IsCPMap Φ ↔ _root_.Quantum.MatrixMap.IsCP Φ := by
  constructor
  · intro hΦ k ρ hρ
    have h := (hΦ k _ (hρ.submatrix Prod.swap)).submatrix Prod.swap
    rwa [tensorIdMap_submatrix_swap, submatrix_submatrix, Prod.swap_swap_eq,
      submatrix_id_id] at h
  · intro hΦ k M hM
    have h := (hΦ k _ (hM.submatrix Prod.swap)).submatrix Prod.swap
    rwa [← tensorIdMap_submatrix_swap, submatrix_submatrix, Prod.swap_swap_eq,
      submatrix_id_id] at h

/-- A map that is completely positive with the ancilla on the left is completely positive with
the ancilla on the right. -/
theorem IsCPMap.isCP {Φ : _root_.Quantum.MatrixMap (Fin n) (Fin n)} (hΦ : IsCPMap Φ) :
    _root_.Quantum.MatrixMap.IsCP Φ :=
  (isCPMap_iff_isCP Φ).1 hΦ

/-- A map that is completely positive with the ancilla on the right is completely positive with
the ancilla on the left. -/
theorem isCPMap_of_isCP {Φ : _root_.Quantum.MatrixMap (Fin n) (Fin n)}
    (hΦ : _root_.Quantum.MatrixMap.IsCP Φ) : IsCPMap Φ :=
  (isCPMap_iff_isCP Φ).2 hΦ

end CatCrypt.Quantum
