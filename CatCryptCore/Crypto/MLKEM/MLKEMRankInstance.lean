/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.MLKEM512Params

/-!
# An `MLWE_PKE_Scheme.Params` at every ML-KEM module rank

The parameter record of the base MLWE public-key encryption scheme over the ML-KEM
ring `(Z/3329Z)[X]/(X^256+1)` at module rank `k`, with seeded centered-binomial noise
at `η₁` for `s`, `e`, `r` and at `η₂` for `e₁`, `e₂`, and with the message space
`Fin 256 → Bool` encoded by the FIPS 203 `Decompress₁`/`Compress₁` pair. The ring,
the per-polynomial sampler and the message coding are those of
`MLKEM512Instance`; this module takes the rank as a parameter. The declarations live
in the namespace `MLKEMRankInstance`.

## Main definitions

* `Vec k`, `Mat k` — rank-`k` vectors and `k × k` matrices over `Rq`
* `vecAdd`, `vecDot`, `matVecMul`, `matTranspose` — the module algebra at rank `k`
* `sampleVec`, `dshortVec` — the seeded rank-`k` noise vectors and their law
* `paramsOfRankEta k η₁ η₂ : MLWE_PKE_Scheme.Params` — the parameter record
* `mlkem768Params` — the record at the ML-KEM-768 numbers `k = 3`, `η₁ = η₂ = 2`

## Main results

* `sampleVec_eq`, `sampleNoise_eq` — a uniform seed pushed through the samplers has
  the product of the short distributions
* `mlkem768_rank`, `mlkem768_eta1`, `mlkem768_eta2` — the numeric fields of
  `mlkem768Params` against `ConcreteParams.MLKEM768Params`

The base MLWE PKE has no ciphertext compression, so `toScheme mlkem768Params` is the
uncompressed scheme.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLKEM.MLKEMRankInstance

open CatCrypt.Prob
open CatCrypt.Util
open MLKEM512Instance (Rq ringMul ringAdd ringSub Msg msgEncode msgDecode PrfBlock
  samplePoly dshortPoly matTranspose_involutive ringAdd_right_bijective)

/-! ## The module at rank `k` -/

/-- Rank-`k` vectors over `Rq`. -/
abbrev Vec (k : ℕ) : Type := Fin k → Rq

/-- `k × k` matrices over `Rq`. -/
abbrev Mat (k : ℕ) : Type := Fin k → Fin k → Rq

/-- Addition of vectors, componentwise. -/
def vecAdd {k : ℕ} (u v : Vec k) : Vec k := u + v

/-- The dot product of two vectors: the sum of the componentwise ring products. -/
def vecDot {k : ℕ} (u v : Vec k) : Rq := ∑ i : Fin k, ringMul (u i) (v i)

/-- Matrix-vector multiplication over `Rq`. -/
def matVecMul {k : ℕ} (A : Mat k) (v : Vec k) : Vec k :=
  fun i => ∑ j : Fin k, ringMul (A i j) (v j)

/-- Matrix transpose. -/
def matTranspose {k : ℕ} (A : Mat k) : Mat k := fun i j => A j i

/-- Transposition of `k × k` matrices over `Rq` is an involution. -/
theorem matTranspose_involutive' (k : ℕ) : Function.Involutive (matTranspose (k := k)) :=
  fun _ => rfl

/-! ## The seeded centered-binomial samplers at rank `k` -/

/-- The PRF output blocks of a rank-`k` noise vector at parameter `η`. -/
abbrev PrfVecBlock (k η : ℕ) : Type := Fin k → PrfBlock η

/-- A rank-`k` noise vector from its PRF blocks, one block per component. -/
def sampleVec (k η : ℕ) (sd : PrfVecBlock k η) : Vec k := fun i => samplePoly η (sd i)

/-- The law of a rank-`k` noise vector: the uniform PRF blocks pushed through
`sampleVec k η`. -/
noncomputable def dshortVec (k η : ℕ) : SDistr (Vec k) :=
  (SDistr.uniform (PrfVecBlock k η)).bind fun sd => SDistr.pure (sampleVec k η sd)

/-- A uniform pair of seeds pushed through `sampleVec k η` twice is the product of two
independent draws from `dshortVec k η`. -/
theorem sampleVec_eq (k η : ℕ) :
    (SDistr.uniform (PrfVecBlock k η × PrfVecBlock k η)).bind
        (fun sd => SDistr.pure (sampleVec k η sd.1, sampleVec k η sd.2)) =
      (dshortVec k η).bind fun s => (dshortVec k η).bind fun e => SDistr.pure (s, e) := by
  rw [← SDistr.uniform_nested_eq_prod]
  simp only [dshortVec, SDistr.bind_assoc, SDistr.pure_bind]

/-- A uniform triple of seeds pushed through the encryption samplers is the product
of `dshortVec k η₁`, `dshortVec k η₂` and `dshortPoly η₂`. -/
theorem sampleNoise_eq (k η₁ η₂ : ℕ) :
    (SDistr.uniform (PrfVecBlock k η₁ × PrfVecBlock k η₂ × PrfBlock η₂)).bind
        (fun sd => SDistr.pure
          (sampleVec k η₁ sd.1, sampleVec k η₂ sd.2.1, samplePoly η₂ sd.2.2)) =
      (dshortVec k η₁).bind fun r => (dshortVec k η₂).bind fun e1 =>
        (dshortPoly η₂).bind fun e2 => SDistr.pure (r, e1, e2) := by
  rw [← SDistr.uniform_nested_eq_prod, ← SDistr.uniform_nested_eq_prod]
  simp only [dshortVec, dshortPoly, SDistr.bind_assoc, SDistr.pure_bind]

/-! ## The parameter record -/

/-- The base MLWE public-key encryption scheme at the ML-KEM ring, module rank `k`
and noise parameters `η₁`, `η₂`, with seeded centered-binomial samplers:
`dshort_vec` at `η₁`, `dshort_vec2` and `dshort_R` at `η₂`. -/
noncomputable def paramsOfRankEta (k η₁ η₂ : ℕ) : MLWE_PKE_Scheme.Params where
  R := Rq
  Vec := Vec k
  Mat := Mat k
  decR := inferInstance
  decVec := inferInstance
  finMat := inferInstance
  neMat := inferInstance
  finVec := inferInstance
  neVec := inferInstance
  dshort_vec := dshortVec k η₁
  dshort_vec2 := dshortVec k η₂
  mat_vec_mul := matVecMul
  mat_transpose := matTranspose
  vec_add := vecAdd
  vec_dot := vecDot
  ring_add := ringAdd
  ring_sub := ringSub
  PT := Msg
  finPT := inferInstance
  nePT := inferInstance
  decPT := inferInstance
  finR := inferInstance
  neR := inferInstance
  dshort_R := dshortPoly η₂
  m_encode := msgEncode
  m_decode := msgDecode
  mat_transpose_involutive := matTranspose_involutive' k
  ring_add_right_bijective := ringAdd_right_bijective
  Seed := PrfVecBlock k η₁ × PrfVecBlock k η₂ × PrfBlock η₂
  finSeed := inferInstance
  neSeed := inferInstance
  sampleShort := fun sd =>
    (sampleVec k η₁ sd.1, sampleVec k η₂ sd.2.1, samplePoly η₂ sd.2.2)
  sampleShort_eq := sampleNoise_eq k η₁ η₂
  KeySeed := PrfVecBlock k η₁ × PrfVecBlock k η₁
  finKeySeed := inferInstance
  neKeySeed := inferInstance
  sampleKey := fun ks => (sampleVec k η₁ ks.1, sampleVec k η₁ ks.2)
  sampleKey_eq := sampleVec_eq k η₁

/-- The parameter record at the ML-KEM-768 numbers: rank `k = 3`, noise parameters
`η₁ = η₂ = 2`. -/
noncomputable def mlkem768Params : MLWE_PKE_Scheme.Params :=
  paramsOfRankEta ConcreteParams.MLKEM768Params.k ConcreteParams.MLKEM768Params.eta1
    ConcreteParams.MLKEM768Params.eta2

/-- The module of `mlkem768Params` has rank `k = 3`. -/
theorem mlkem768_rank : ConcreteParams.MLKEM768Params.k = 3 := rfl

/-- The key and vector noise of `mlkem768Params` is drawn at `η₁ = 2`. -/
theorem mlkem768_eta1 : ConcreteParams.MLKEM768Params.eta1 = 2 := rfl

/-- The scalar encryption noise of `mlkem768Params` is drawn at `η₂ = 2`. -/
theorem mlkem768_eta2 : ConcreteParams.MLKEM768Params.eta2 = 2 := rfl

/-- The message space of `mlkem768Params` is the 256 bits of a 32-byte message. -/
theorem mlkem768_message_card : Fintype.card mlkem768Params.PT = 2 ^ 256 := by
  change Fintype.card (Fin 256 → Bool) = 2 ^ 256
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

end CatCrypt.Crypto.MLKEM.MLKEMRankInstance
