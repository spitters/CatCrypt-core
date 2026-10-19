/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Advantage
public import CatCryptCore.Crypto.CryptoWord

/-!
# Learning With Errors (LWE) assumption

Decisional LWE: distinguish `(A, A·s + e)` from `(A, u)`, where `A` is a public
matrix, `s` a secret, `e` a small error and `u` uniform.

An instance `LWEDef M S E B` has a type `M` of public matrices, `S` of secrets, `E` of
errors and `B` of samples, the three samplers, and the LWE map `mulAddErr A s e = A·s + e`
into the samples. The algebra of the instance is in `mulAddErr`, so the one game covers
plain LWE (`M = ℤ_q^{m×n}`, `S = ℤ_q^n`, `E = B = ℤ_q^m`), Module-LWE (`M = R_q^{k×k}`,
`S = E = B = R_q^k`) and Ring-LWE (`M = S = E = B = R_q`), and a number of samples
sharing one secret, as a product of samples.

## Main definitions

* `LWEDef` — the samplers of the matrix, the secret and the error, and the map `A·s + e`
* `LWE_Adversary` — a distinguisher on a matrix and a sample
* `LWE_Game_Real`, `LWE_Game_Ideal` — the games with `b = A·s + e` and with `b` uniform
* `LWE_Advantage` — the distinguishing advantage

## Main results

* `LWE_Game_Real_isPure`, `LWE_Game_Ideal_isPure` — the games are heap-independent for a
  heap-independent distinguisher

## References

* Regev, *On lattices, learning with errors, random linear codes, and cryptography*,
  STOC 2005 / JACM 2009
* Lyubashevsky, Peikert, Regev, *On ideal lattices and learning with errors over rings*,
  EUROCRYPT 2010 (Ring-LWE)
* Langlois, Stehlé, *Worst-case to average-case reductions for module lattices*, Designs
  Codes Cryptogr. 2015 (Module-LWE)
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Assumptions

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

/-! ## LWE instances -/

/-- An LWE instance: samplers of the public matrix `A : M`, the secret `s : S` and the
error `e : E`, and the LWE map `mulAddErr A s e = A·s + e` into the samples `B`. -/
structure LWEDef (M S E B : Type) [SampleableType B] where
  /-- Sample the public matrix `A`. -/
  sampleA : SPComp M
  /-- Sample the secret `s`. -/
  sampleSecret : SPComp S
  /-- Sample the error `e`. -/
  sampleError : SPComp E
  /-- The LWE map `A·s + e`. -/
  mulAddErr : M → S → E → B
  /-- Sampling `A` is heap-independent. -/
  sampleA_isPure : SPComp.IsPure sampleA
  /-- Sampling the secret is heap-independent. -/
  sampleSecret_isPure : SPComp.IsPure sampleSecret
  /-- Sampling the error is heap-independent. -/
  sampleError_isPure : SPComp.IsPure sampleError

variable {M S E B : Type} [SampleableType B]

/-! ## LWE games -/

/-- An LWE distinguisher: receives the matrix `A` and a sample `b`. -/
abbrev LWE_Adversary (M B : Type) := M → B → SPComp Bool

/-- The real LWE game: `b = A·s + e`. -/
noncomputable def LWE_Game_Real (D : LWEDef M S E B) (A : LWE_Adversary M B) :
    SPComp Bool := do
  let a ← D.sampleA
  let s ← D.sampleSecret
  let e ← D.sampleError
  A a (D.mulAddErr a s e)

/-- The ideal LWE game: `b` is uniform, independent of `A`. -/
noncomputable def LWE_Game_Ideal (D : LWEDef M S E B) (A : LWE_Adversary M B) :
    SPComp Bool := do
  let a ← D.sampleA
  let u ← SPComp.sample B
  A a u

/-- The decisional LWE advantage: distinguishing `(A, A·s + e)` from `(A, u)`. -/
noncomputable def LWE_Advantage (D : LWEDef M S E B) (A : LWE_Adversary M B) : ℝ≥0∞ :=
  Advantage (LWE_Game_Real D A) (LWE_Game_Ideal D A)

/-! ## Purity -/

theorem LWE_Game_Real_isPure (D : LWEDef M S E B) (A : LWE_Adversary M B)
    (hA : ∀ x y, SPComp.IsPure (A x y)) :
    SPComp.IsPure (LWE_Game_Real D A) := by
  unfold LWE_Game_Real; simp only [SPComp.monad_bind_eq]
  aesop (add unsafe SPComp.bind_isPure, unsafe D.sampleA_isPure, unsafe D.sampleSecret_isPure,
      unsafe D.sampleError_isPure)

theorem LWE_Game_Ideal_isPure (D : LWEDef M S E B) (A : LWE_Adversary M B)
    (hA : ∀ x y, SPComp.IsPure (A x y)) :
    SPComp.IsPure (LWE_Game_Ideal D A) := by
  unfold LWE_Game_Ideal; simp only [SPComp.monad_bind_eq]
  aesop (add unsafe SPComp.bind_isPure, unsafe D.sampleA_isPure, unsafe SPComp.sample_isPure)

end CatCrypt.Crypto.Assumptions
