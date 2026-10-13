/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.MLWE_PKE_Scheme
public import CatCryptCore.Crypto.MLKEM.Sampler
public import CatCryptCore.Crypto.MLKEM.ConcreteParams
public import CatCryptCore.Crypto.Optimizer.Lattice.SignedNegacyclicConv
public import CatCryptCore.NonUniform.CenteredBinomial
public import CatCryptCore.Hax.CType

/-!
# An `MLWE_PKE_Scheme.Params` at the ML-KEM-512 numbers

A concrete parameter record for the base MLWE public-key encryption scheme, built
over the ML-KEM ring `(Z/3329Z)[X]/(X^256+1)` at module rank `2`, with the noise
distributions obtained as pushforwards of uniform PRF blocks along the FIPS 203
centered-binomial sampler `Sampler.sampleCBD_eta`, and with the message space
`Fin 256 → Bool` encoded by the FIPS 203 `Decompress₁`/`Compress₁` pair. The
declarations live in the namespace `MLKEM512Instance`.

## Main definitions

* `Rq`, `Vec`, `Mat` — the coefficient ring, rank-2 vectors and 2×2 matrices
* `ringMul`, `ringAdd`, `ringSub`, `vecAdd`, `vecDot`, `matVecMul`, `matTranspose` —
  the algebra, with `ringMul` the length-256 signed negacyclic convolution
* `PrfBlock`, `samplePoly`, `sampleVec`, `dshortPoly`, `dshortVec` — the seeded
  centered-binomial noise
* `msgEncode`, `msgDecode` — FIPS 203 `Decompress₁` and `Compress₁` on 256 bits
* `mlkem512Params : MLWE_PKE_Scheme.Params` — the parameter record
* `SamplerIsCbd` — the identification of the sampler pushforward with the 256-fold
  product of `CatCrypt.NonUniform.cbd`

## Main results

* `matTranspose_involutive`, `ringAdd_right_bijective` — the two side conditions of
  `MLWE_PKE_Basic.Params`
* `sampleVec_eq`, `sampleNoise_eq` — a uniform seed pushed through the samplers has
  the product of the short distributions
* `msgDecode_msgEncode` — the message encoding is a section of the decoding
* `mlkem512_degree`, `mlkem512_modulus`, `mlkem512_rank`, `mlkem512_eta1`,
  `mlkem512_eta2`, `mlkem512_keySeed`, `mlkem512_seed` — the numeric fields
  of the record against `ConcreteParams.MLKEM512Params`

## Scope

* **`dshort` and `cbd`.** `dshortPoly η` is *defined* as the pushforward of the
  uniform `64·η`-byte PRF block along `Sampler.sampleCBD_eta η`, so `sampleShort_eq`
  and `sampleKey_eq` hold by the product structure of the uniform seed. The
  identification of that pushforward with the 256-fold independent product of
  `CatCrypt.NonUniform.cbd η` is stated as `SamplerIsCbd`, and
  `MLKEM/SamplerCbd.lean` proves it for every `η > 0`, so `dshortPoly η` carries
  the centered-binomial law. No declaration in this file depends on the
  proposition.
* **Compression.** The base MLWE PKE has no ciphertext compression, so
  `toScheme mlkem512Params` is the uncompressed scheme. FIPS 203 K-PKE, which
  compresses `u` at `d_u = 10` and `v` at `d_v = 4`, is
  `CompressedPKE.mlkem512CompressedScheme`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLKEM.MLKEM512Instance

open CatCrypt.Prob
open CatCrypt.Util
open CatCrypt.Crypto.Optimizer.Lattice
open scoped ENNReal

/-! ## The ring and the module -/

/-- The ML-KEM coefficient ring `(Z/3329Z)[X]/(X^256+1)`, represented by the
coefficient vector of the degree-`< 256` representative. -/
abbrev Rq : Type := Fin 256 → Zq3329

/-- Rank-2 vectors over `Rq`: the module of ML-KEM-512. -/
abbrev Vec : Type := Fin 2 → Rq

/-- `2 × 2` matrices over `Rq`. -/
abbrev Mat : Type := Fin 2 → Fin 2 → Rq

/-- Multiplication in `Rq`: the length-256 signed negacyclic convolution, with the
sign `-1` exactly on the wrapped indices. -/
def ringMul (a b : Rq) : Rq := SignedNegacyclicConv.signedNegaConv a b

/-- Addition in `Rq`, coefficientwise. -/
def ringAdd (a b : Rq) : Rq := a + b

/-- Subtraction in `Rq`, coefficientwise. -/
def ringSub (a b : Rq) : Rq := a - b

/-- Addition of vectors, componentwise. -/
def vecAdd (u v : Vec) : Vec := u + v

/-- The dot product of two vectors: the sum of the componentwise ring products. -/
def vecDot (u v : Vec) : Rq := ∑ i : Fin 2, ringMul (u i) (v i)

/-- Matrix-vector multiplication over `Rq`. -/
def matVecMul (A : Mat) (v : Vec) : Vec := fun i => ∑ j : Fin 2, ringMul (A i j) (v j)

/-- Matrix transpose. -/
def matTranspose (A : Mat) : Mat := fun i j => A j i

/-- Transposition of `2 × 2` matrices over `Rq` is an involution. -/
theorem matTranspose_involutive : Function.Involutive matTranspose := fun _ => rfl

/-- Adding a fixed ring element on the right is a bijection of `Rq`. -/
theorem ringAdd_right_bijective (c : Rq) : Function.Bijective (fun v => ringAdd v c) :=
  (Equiv.addRight c).bijective

/-! ## The seeded centered-binomial samplers -/

/-- The PRF output block of one noise polynomial at parameter `η`: the `64 · η`
bytes that FIPS 203 Algorithm 8 expands into 256 coefficients. -/
abbrev PrfBlock (η : ℕ) : Type := Fin (64 * η) → UInt8

/-- The PRF output blocks of a rank-2 noise vector at parameter `η`. -/
abbrev PrfVecBlock (η : ℕ) : Type := Fin 2 → PrfBlock η

/-- One noise polynomial from its PRF block: FIPS 203 Algorithm 8
(`Sampler.sampleCBD_eta`) on the bytes of the block. -/
def samplePoly (η : ℕ) (b : PrfBlock η) : Rq := Sampler.sampleCBD_eta η (List.ofFn b)

/-- A rank-2 noise vector from its PRF blocks, one block per component. -/
def sampleVec (η : ℕ) (sd : PrfVecBlock η) : Vec := fun i => samplePoly η (sd i)

/-- The law of one noise polynomial: the uniform PRF block pushed through
`samplePoly η`. -/
noncomputable def dshortPoly (η : ℕ) : SDistr Rq :=
  (SDistr.uniform (PrfBlock η)).bind fun b => SDistr.pure (samplePoly η b)

/-- The law of a rank-2 noise vector: the uniform PRF blocks pushed through
`sampleVec η`. -/
noncomputable def dshortVec (η : ℕ) : SDistr Vec :=
  (SDistr.uniform (PrfVecBlock η)).bind fun sd => SDistr.pure (sampleVec η sd)

/-- The identification of `dshortPoly η` with the centered binomial law: the
uniform PRF block pushed through `Sampler.sampleCBD_eta η` is the 256-fold
independent product of `CatCrypt.NonUniform.cbd η` mapped into `Zq3329`. -/
def SamplerIsCbd (η : ℕ) : Prop :=
  dshortPoly η =
    (CatCrypt.NonUniform.replicateFin 256 (CatCrypt.NonUniform.cbd η)).bind fun c =>
      SDistr.pure (fun i => Zq3329.fromInt (c i))

/-- A uniform pair of seeds pushed through `sampleVec η` twice is the product of two
independent draws from `dshortVec η`. -/
theorem sampleVec_eq (η : ℕ) :
    (SDistr.uniform (PrfVecBlock η × PrfVecBlock η)).bind
        (fun sd => SDistr.pure (sampleVec η sd.1, sampleVec η sd.2)) =
      (dshortVec η).bind fun s => (dshortVec η).bind fun e => SDistr.pure (s, e) := by
  rw [← SDistr.uniform_nested_eq_prod]
  simp only [dshortVec, SDistr.bind_assoc, SDistr.pure_bind]

/-- A uniform triple of seeds pushed through the encryption samplers is the product
of `dshortVec η₁`, `dshortVec η₂` and `dshortPoly η₂`. -/
theorem sampleNoise_eq (η₁ η₂ : ℕ) :
    (SDistr.uniform (PrfVecBlock η₁ × PrfVecBlock η₂ × PrfBlock η₂)).bind
        (fun sd => SDistr.pure
          (sampleVec η₁ sd.1, sampleVec η₂ sd.2.1, samplePoly η₂ sd.2.2)) =
      (dshortVec η₁).bind fun r => (dshortVec η₂).bind fun e1 =>
        (dshortPoly η₂).bind fun e2 => SDistr.pure (r, e1, e2) := by
  rw [← SDistr.uniform_nested_eq_prod, ← SDistr.uniform_nested_eq_prod]
  simp only [dshortVec, dshortPoly, SDistr.bind_assoc, SDistr.pure_bind]

/-! ## The message space -/

/-- The ML-KEM message space: the 256 bits of a 32-byte message. -/
abbrev Msg : Type := Fin 256 → Bool

/-- FIPS 203 `Decompress₁`: `1 ↦ ⌈q/2⌋ = 1665`, `0 ↦ 0`. -/
def decompress1 (b : Bool) : Zq3329 := if b then (1665 : Zq3329) else 0

/-- FIPS 203 `Compress₁`: `⌈2x/q⌋ mod 2`, which for `q = 3329` is `1` exactly on the
residues `833, …, 2496`. -/
def compress1 (x : Zq3329) : Bool := decide (832 < x.val ∧ x.val ≤ 2496)

/-- The message encoding: `Decompress₁` on each of the 256 bits. -/
def msgEncode (m : Msg) : Rq := fun i => decompress1 (m i)

/-- The message decoding: `Compress₁` on each of the 256 coefficients. -/
def msgDecode (a : Rq) : Msg := fun i => compress1 (a i)

/-- The encoding is a section of the decoding: `Compress₁ ∘ Decompress₁ = id`. -/
theorem msgDecode_msgEncode (m : Msg) : msgDecode (msgEncode m) = m := by
  funext i
  cases h : m i <;> simp only [msgDecode, msgEncode, h, decompress1, compress1] <;> decide

/-! ## The parameter record -/

/-- The base MLWE public-key encryption scheme at the ML-KEM-512 ring, rank and
noise parameters, with seeded centered-binomial samplers: `dshort_vec` at `η₁`,
`dshort_vec2` and `dshort_R` at `η₂`. -/
noncomputable def paramsOfEta (η₁ η₂ : ℕ) : MLWE_PKE_Scheme.Params where
  R := Rq
  Vec := Vec
  Mat := Mat
  decR := inferInstance
  decVec := inferInstance
  finMat := inferInstance
  neMat := inferInstance
  finVec := inferInstance
  neVec := inferInstance
  dshort_vec := dshortVec η₁
  dshort_vec2 := dshortVec η₂
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
  mat_transpose_involutive := matTranspose_involutive
  ring_add_right_bijective := ringAdd_right_bijective
  Seed := PrfVecBlock η₁ × PrfVecBlock η₂ × PrfBlock η₂
  finSeed := inferInstance
  neSeed := inferInstance
  sampleShort := fun sd => (sampleVec η₁ sd.1, sampleVec η₂ sd.2.1, samplePoly η₂ sd.2.2)
  sampleShort_eq := sampleNoise_eq η₁ η₂
  KeySeed := PrfVecBlock η₁ × PrfVecBlock η₁
  finKeySeed := inferInstance
  neKeySeed := inferInstance
  sampleKey := fun ks => (sampleVec η₁ ks.1, sampleVec η₁ ks.2)
  sampleKey_eq := sampleVec_eq η₁

/-- The parameter record at the ML-KEM-512 noise parameters `η₁ = 3`, `η₂ = 2`. -/
noncomputable def mlkem512Params : MLWE_PKE_Scheme.Params :=
  paramsOfEta ConcreteParams.MLKEM512Params.eta1 ConcreteParams.MLKEM512Params.eta2

/-! ## The numeric fields against `ConcreteParams.MLKEM512Params` -/

/-- The ring has `n = 256` coefficients. -/
theorem mlkem512_degree : Fintype.card (Fin 256) = ConcreteParams.MLKEM512Params.n := by
  simp [ConcreteParams.MLKEM512Params]

/-- The coefficient field has `q = 3329` elements. -/
theorem mlkem512_modulus : Fintype.card Zq3329 = ConcreteParams.MLKEM512Params.q := by
  simp [ConcreteParams.MLKEM512Params, ZMod.card]

/-- The module has rank `k = 2`. -/
theorem mlkem512_rank : Fintype.card (Fin 2) = ConcreteParams.MLKEM512Params.k := by
  simp [ConcreteParams.MLKEM512Params]

/-- The key and vector noise is drawn at `η₁ = 3`. -/
theorem mlkem512_eta1 : ConcreteParams.MLKEM512Params.eta1 = 3 := rfl

/-- The scalar encryption noise is drawn at `η₂ = 2`. -/
theorem mlkem512_eta2 : ConcreteParams.MLKEM512Params.eta2 = 2 := rfl

/-- `dshort_vec` of the record is the `η₁` sampler pushforward. -/
theorem mlkem512_dshort_vec :
    mlkem512Params.dshort_vec = dshortVec ConcreteParams.MLKEM512Params.eta1 := rfl

/-- `dshort_vec2` of the record, the law of `e₁`, is the `η₂` sampler pushforward. -/
theorem mlkem512_dshort_vec2 :
    mlkem512Params.dshort_vec2 = dshortVec ConcreteParams.MLKEM512Params.eta2 := rfl

/-- `dshort_R` of the record is the `η₂` sampler pushforward. -/
theorem mlkem512_dshort_R :
    mlkem512Params.dshort_R = dshortPoly ConcreteParams.MLKEM512Params.eta2 := rfl

/-- The key seed is a pair of rank-2 blocks of `64 · η₁` PRF bytes per component:
the PRF output FIPS 203 expands into `s` and `e`. -/
theorem mlkem512_keySeed : mlkem512Params.KeySeed =
    ((Fin 2 → Fin (64 * ConcreteParams.MLKEM512Params.eta1) → UInt8) ×
      (Fin 2 → Fin (64 * ConcreteParams.MLKEM512Params.eta1) → UInt8)) := rfl

/-- The encryption seed is one rank-2 block at `η₁`, one rank-2 block at `η₂` and one
block at `η₂`: the PRF output FIPS 203 expands into `r`, `e₁` and `e₂`. -/
theorem mlkem512_seed : mlkem512Params.Seed =
    ((Fin 2 → Fin (64 * ConcreteParams.MLKEM512Params.eta1) → UInt8) ×
      (Fin 2 → Fin (64 * ConcreteParams.MLKEM512Params.eta2) → UInt8) ×
      (Fin (64 * ConcreteParams.MLKEM512Params.eta2) → UInt8)) := rfl

/-- The message space is the 256 bits of a 32-byte message. -/
theorem mlkem512_message_card : Fintype.card mlkem512Params.PT = 2 ^ 256 := by
  show Fintype.card (Fin 256 → Bool) = 2 ^ 256
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

end CatCrypt.Crypto.MLKEM.MLKEM512Instance
