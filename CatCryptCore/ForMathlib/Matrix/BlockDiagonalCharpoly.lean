/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Characteristic polynomial of a block diagonal matrix

The characteristic matrix of a block diagonal matrix is block diagonal, so the characteristic
polynomial of `Matrix.blockDiagonal M` is the product of the characteristic polynomials of the
blocks `M z`.

## Main results

* `Matrix.charmatrix_blockDiagonal`: the characteristic matrix of `blockDiagonal M` is the block
  diagonal matrix of the characteristic matrices of the blocks.
* `Matrix.charpoly_blockDiagonal`: `(blockDiagonal M).charpoly = ∏ z, (M z).charpoly`.

## Search words

block diagonal matrix, characteristic polynomial, characteristic matrix, direct sum
-/

@[expose] public section

set_option autoImplicit false

namespace Matrix

variable {ζ H : Type} [DecidableEq ζ]

/-- The characteristic matrix of a block diagonal matrix is block diagonal. -/
theorem charmatrix_blockDiagonal [Fintype ζ] [Fintype H] [DecidableEq H] {R : Type}
    [CommRing R] (M : ζ → Matrix H H R) :
    charmatrix (blockDiagonal M) = blockDiagonal fun z => charmatrix (M z) := by
  ext ⟨a, z⟩ ⟨b, z'⟩
  by_cases hz : z = z' <;> by_cases hab : a = b <;> simp [blockDiagonal_apply, *]

/-- The characteristic polynomial of a block diagonal matrix is the product of those of its
blocks. -/
theorem charpoly_blockDiagonal [Fintype ζ] [Fintype H] [DecidableEq H] {R : Type} [CommRing R]
    (M : ζ → Matrix H H R) :
    (blockDiagonal M).charpoly = ∏ z, (M z).charpoly := by
  rw [charpoly, charmatrix_blockDiagonal, det_blockDiagonal]
  rfl

end Matrix
