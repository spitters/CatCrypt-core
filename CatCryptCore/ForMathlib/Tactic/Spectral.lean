/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Analysis.Matrix.Order

/-!
# The `spectral` tactic

For a Hermitian matrix `X`, `spectral hX with U d hU hU' hXd` introduces the eigenvector unitary
`U` as a matrix, the real eigenvalue vector `d` and the three facts that the spectral theorem
is used for. `U` and `d` are introduced by `set`, so that the later goal and hypotheses no
longer mention `hX` and rewriting with `hXd` meets no dependent motive.

## Main results

* `Matrix.IsHermitian.eigenvectorUnitary_star_mul_self`,
  `Matrix.IsHermitian.eigenvectorUnitary_mul_star_self`: unitarity of the eigenvector matrix.
* `Matrix.IsHermitian.spectral_eq`: `X = U * diagonal (fun i => (d i : 𝕜)) * star U`.
* the tactic `spectral hX with U d hU hU' hXd`.
-/

@[expose] public section

set_option autoImplicit false

open Matrix

namespace Matrix.IsHermitian

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n 𝕜}

/-- The eigenvector matrix of a Hermitian matrix satisfies `star U * U = 1`. -/
theorem eigenvectorUnitary_star_mul_self (hX : X.IsHermitian) :
    star (hX.eigenvectorUnitary : Matrix n n 𝕜) * (hX.eigenvectorUnitary : Matrix n n 𝕜) = 1 :=
  Unitary.coe_star_mul_self hX.eigenvectorUnitary

/-- The eigenvector matrix of a Hermitian matrix satisfies `U * star U = 1`. -/
theorem eigenvectorUnitary_mul_star_self (hX : X.IsHermitian) :
    (hX.eigenvectorUnitary : Matrix n n 𝕜) * star (hX.eigenvectorUnitary : Matrix n n 𝕜) = 1 :=
  Unitary.coe_mul_star_self hX.eigenvectorUnitary

/-- The spectral theorem of a Hermitian matrix in the form `X = U * diagonal d * star U`. -/
theorem spectral_eq (hX : X.IsHermitian) :
    X = (hX.eigenvectorUnitary : Matrix n n 𝕜) *
      diagonal (fun i => (hX.eigenvalues i : 𝕜)) *
        star (hX.eigenvectorUnitary : Matrix n n 𝕜) := by
  have h := hX.spectral_theorem
  rwa [Unitary.conjStarAlgAut_apply] at h

end Matrix.IsHermitian

/-- `spectral hX with U d hU hU' hXd` for `hX : X.IsHermitian` introduces the eigenvector
unitary `U` (a matrix), the eigenvalue vector `d`, `hU : star U * U = 1`, `hU' : U * star U = 1`
and `hXd : X = U * diagonal (fun i => (d i : 𝕜)) * star U`. -/
syntax (name := spectralTac) "spectral " term " with " Lean.binderIdent ppSpace
  Lean.binderIdent ppSpace ident ppSpace ident ppSpace ident : tactic

macro_rules
  | `(tactic| spectral $hX with $U $d $hU $hU' $hXd) =>
    `(tactic|
      (have $hU := Matrix.IsHermitian.eigenvectorUnitary_star_mul_self $hX
       have $hU' := Matrix.IsHermitian.eigenvectorUnitary_mul_star_self $hX
       have $hXd := Matrix.IsHermitian.spectral_eq $hX
       set $d := Matrix.IsHermitian.eigenvalues $hX
       set $U := Subtype.val (Matrix.IsHermitian.eigenvectorUnitary $hX)))
