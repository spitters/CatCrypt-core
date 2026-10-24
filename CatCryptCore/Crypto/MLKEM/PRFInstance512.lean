/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.PRFOracle
public import CatCryptCore.Crypto.MLKEM.XOFMatrix
public import CatCryptCore.Quantum.QROM.QMLWEAux

/-!
# The `PRF_η` oracle and the XOF matrix at ML-KEM-512

The `PRF_η` chain models FIPS 203 `PRF_η(σ, N)` as a random oracle whose rows
`ν : Nc → Fin n` are read at a 32-byte seed, and assumes that the row assemblies
`kg ∘ eK` and `enc` at uniform rows have the key and ciphertext distributions of
`mapCiphertext (toScheme P) f g` (the hypotheses `hKey`, `hEnc`). This module
instantiates the row type at ML-KEM-512 and proves both hypotheses there, and
bounds the change of a module-LWE advantage when the matrix is expanded from a
random-oracle XOF instead of drawn uniformly.

## Main definitions

* `Chunk`, `prfN` — a 64-byte string, and `2 ^ 512`, the number of such strings
  and the size of the oracle range `K × Sd` at 32-byte keys and seeds
* `Nonce`, `Row` — the oracle nonces `Fin 5 × Fin 3`, a pair `(N, j)` naming the
  `j`-th 64-byte chunk of `PRF_η(σ, N)`, and the rows `Nonce → Fin prfN`
* `prfBytes ν N b` — byte `b` of the 192-byte output of nonce `N` of the row `ν`
* `eE`, `eK` — the encryption seed `(r, e₁, e₂)` and the key seed `(s, e)` of
  `mlkem512Params` read from a row as in FIPS 203 Algorithms 13 and 14
* `kg512`, `enc512` — key generation from a matrix and a key seed, and
  compressed encryption with the noise read from a row
* `mlweSampleWith`, `extSampleWith` — the module-LWE samples with the matrix
  drawn from a given distribution

## Main results

* `pushesUniform_eE`, `pushesUniform_eK` — both seed assemblies send uniform rows
  to uniform seeds
* `avg_kg512_eK` — the hypothesis `hKey` at `mlkem512Params`
* `avg_enc512` — the hypothesis `hEnc` at `mlkem512Params`
* `absDiff_sdExp_bind_le_tvDist` — two sub-distributions followed by one
  continuation give `[0, 1]`-valued expectations at most `tvDist` apart
* `absDiff_mlweSampleWith_le`, `absDiff_extSampleWith_le` — every
  `[0, 1]`-valued distinguishing advantage on the (extended) module-LWE sample
  changes by at most `2 · tvDist dA U` when the uniform matrix `U` is replaced by
  `dA`
* `qMLWEAuxWith_le`, `qMLWEExtAuxWith_le` — the same for the quantum
  distinguishers with oracle access of `QMLWEAux`
* `tvDist_xofMatrixDistVia_le` — the XOF matrix under any relabelling `e` is
  within `k² · nonFillProb m` of uniform
* `absDiff_mlweSample_xof512_le` — at ML-KEM-512 (`k = 2`) with a stream of
  `m = 280` three-byte groups (five SHAKE-128 blocks), the change is at most
  `2 · 4 · C(560, 255) · (767 / 4096) ^ 305`

## The model

The oracle range of the chain is `Fin n` with `(K × Sd) ≃ Fin n`; at 32-byte
keys and seeds `n = 2 ^ 512`, so one oracle value is a 64-byte chunk and the
192-byte output of `PRF_η(σ, N)` occupies the three nonces `(N, 0)`, `(N, 1)`,
`(N, 2)`. The `η₂ = 2` blocks are the 128-byte prefixes. Encryption reads `r`
from `N = 0, 1`, `e₁` from `N = 2, 3` and `e₂` from `N = 4`; key generation reads
`s` from `N = 0, 1` and `e` from `N = 2, 3`. `avg_kg512_eK` is `hKey` with the
public randomness `Φ` the uniform matrix; with `Φ` the XOF family and the matrix
`SampleNTT(XOF(ρ))`, `hKey` holds up to the distance bounded in the second part
(`MLKEM512QROMPrf.kgX_close`). The XOF is a
random oracle truncated to `m` groups per matrix entry; FIPS 203 reads the XOF
until 256 coefficients are accepted, so the truncation at `m` is part of the
model, and `nonFillProb m` is the probability that the truncated stream does not
suffice. The relabelling `e : XOFMatrix.Mat 2 ≃ mlkem512Params.Mat` is a
parameter; FIPS 203 takes the entrywise inverse NTT.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal

noncomputable section

namespace CatCrypt.Crypto.MLKEM.PRFInstance512

open CatCrypt.Prob
open CatCrypt.Crypto.MLKEM.PRFOracle (avg avg_prod avg_fst PushesUniform)
open MLKEM512Instance (mlkem512Params)
open CompressedPKE (mapCiphertext MLKEM512CT mlkem512Compress mlkem512Decompress)
open MLWE_PKE_Scheme (toScheme)

/-! ## Pushforwards of the uniform distribution -/

section Push

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]

/-- An equivalence sends the uniform distribution to the uniform distribution. -/
theorem pushesUniform_equiv (e : α ≃ β) : PushesUniform e := by
  intro g
  unfold avg
  rw [Fintype.card_congr e]
  exact Fintype.sum_equiv e _ _ fun _ => rfl

/-- `PushesUniform` is closed under composition. -/
theorem pushesUniform_comp {e₁ : α → β} {e₂ : β → γ} (h₁ : PushesUniform e₁)
    (h₂ : PushesUniform e₂) : PushesUniform (e₂ ∘ e₁) :=
  fun g => (h₁ (g ∘ e₂)).trans (h₂ g)

/-- The first projection of a product with a nonempty factor pushes the uniform
distribution to the uniform distribution. -/
theorem pushesUniform_fst [Nonempty γ] : PushesUniform (Prod.fst : β × γ → β) :=
  fun g => avg_fst g

/-- Restricting a function along an embedding pushes the uniform distribution to
the uniform distribution. -/
theorem pushesUniform_restrict {ι ι' X : Type} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] [Fintype X] [Nonempty X] (j : ι' ↪ ι) :
    PushesUniform (fun x : ι → X => fun i => x (j i)) := by
  classical
  let E := Equiv.piEquivPiSubtypeProd (fun i => i ∈ Set.range j) (fun _ : ι => X)
  let F : ({i // i ∈ Set.range j} → X) ≃ (ι' → X) :=
    Equiv.arrowCongr (Equiv.ofInjective j j.injective).symm (Equiv.refl X)
  have h : (fun x : ι → X => fun i => x (j i)) = F ∘ Prod.fst ∘ E := by
    funext x i
    rfl
  rw [h]
  exact pushesUniform_comp (pushesUniform_comp (pushesUniform_equiv E) pushesUniform_fst)
    (pushesUniform_equiv F)

end Push

/-! ## The `PRF_η` rows at ML-KEM-512 -/

section Rows

/-- A 64-byte string: one value of the oracle at 32-byte keys and seeds. -/
abbrev Chunk : Type := Fin 64 → UInt8

/-- The size `2 ^ 512` of the oracle range `K × Sd` at 32-byte keys and seeds. -/
abbrev prfN : ℕ := 2 ^ (8 * 64)

/-- A byte has `2 ^ 8` values. -/
theorem card_uint8 : Fintype.card UInt8 = 2 ^ 8 := by
  rw [Fintype.card_congr (⟨UInt8.toFin, UInt8.ofFin, fun x => UInt8.ofFin_toFin x,
    fun x => UInt8.toFin_ofFin x⟩ : UInt8 ≃ Fin (2 ^ 8)), Fintype.card_fin]

/-- A string of `k` bytes has `2 ^ (8 k)` values. -/
theorem card_bytes (k : ℕ) : Fintype.card (Fin k → UInt8) = 2 ^ (8 * k) := by
  rw [Fintype.card_fun, Fintype.card_fin, card_uint8, ← pow_mul]

/-- The oracle values `Fin prfN` as 64-byte strings. -/
def chunkEquiv : Fin prfN ≃ Chunk :=
  (Fintype.equivFinOfCardEq (card_bytes 64)).symm

/-- The key and seed pair `K × Sd` of 32-byte strings as an oracle value. -/
def eKR512 : ((Fin 32 → UInt8) × (Fin 32 → UInt8)) ≃ Fin prfN :=
  Fintype.equivFinOfCardEq (by rw [Fintype.card_prod, card_bytes, ← pow_add])

/-- The number of oracle points `(σ, (N, j))` with a 32-byte seed `σ`. -/
abbrev prfM : ℕ := 2 ^ (8 * 32) * 15

/-- The oracle nonces: `(N, j)` is the `j`-th 64-byte chunk of `PRF_η(σ, N)`,
for the five FIPS 203 nonces `N` and the three chunks of the longest output. -/
abbrev Nonce : Type := Fin 5 × Fin 3

/-- The oracle points `(σ, (N, j))` with a 32-byte seed `σ`, numbered. -/
def eD512 : ((Fin 32 → UInt8) × Nonce) ≃ Fin prfM :=
  Fintype.equivFinOfCardEq (by
    rw [Fintype.card_prod, card_bytes, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin])

/-- A row of the oracle at one seed: a value for each nonce. -/
abbrev Row : Type := Nonce → Fin prfN

/-- Chunk `j` and byte `i` of it as byte `64 j + i` of a 192-byte output. -/
def blockEquiv : Fin 3 × Fin 64 ≃ Fin 192 :=
  (finProdFinEquiv : Fin 3 × Fin 64 ≃ Fin (3 * 64)).trans (finCongr (by norm_num))

/-- A row as the five 192-byte outputs `PRF_η(σ, N)`. -/
def rowEquiv : Row ≃ (Fin 5 × Fin 192 → UInt8) :=
  ((Equiv.arrowCongr (Equiv.refl Nonce) chunkEquiv).trans
    (Equiv.curry Nonce (Fin 64) UInt8).symm).trans
    ((Equiv.arrowCongr (Equiv.prodAssoc (Fin 5) (Fin 3) (Fin 64)) (Equiv.refl UInt8)).trans
      (Equiv.arrowCongr (Equiv.prodCongr (Equiv.refl (Fin 5)) blockEquiv) (Equiv.refl UInt8)))

/-- Byte `b` of the 192-byte output of nonce `N` of the row `ν`. -/
def prfBytes (ν : Row) (N : Fin 5) (b : Fin 192) : UInt8 := rowEquiv ν (N, b)

/-- The `η₁ = 3` block has 192 bytes. -/
theorem blockLen_eta1 : 64 * ConcreteParams.MLKEM512Params.eta1 ≤ 192 := by
  simp [ConcreteParams.MLKEM512Params]

/-- The `η₂ = 2` block has 128 bytes. -/
theorem blockLen_eta2 : 64 * ConcreteParams.MLKEM512Params.eta2 ≤ 192 := by
  simp [ConcreteParams.MLKEM512Params]

/-- The byte positions of the encryption seed `(r, e₁, e₂)`. -/
abbrev EncPos : Type :=
  (Fin 2 × Fin (64 * ConcreteParams.MLKEM512Params.eta1)) ⊕
    ((Fin 2 × Fin (64 * ConcreteParams.MLKEM512Params.eta2)) ⊕
      Fin (64 * ConcreteParams.MLKEM512Params.eta2))

/-- The output byte read at each position of the encryption seed: `r` from the
nonces `0, 1`, `e₁` from the nonces `2, 3`, `e₂` from the nonce `4`, each block a
prefix of the 192-byte output. -/
def encPos : EncPos ↪ Fin 5 × Fin 192 where
  toFun
    | .inl (i, b) => (⟨i, by omega⟩, Fin.castLE blockLen_eta1 b)
    | .inr (.inl (i, b)) => (⟨2 + i, by omega⟩, Fin.castLE blockLen_eta2 b)
    | .inr (.inr b) => (4, Fin.castLE blockLen_eta2 b)
  inj' := by
    rintro (⟨i, b⟩ | ⟨i, b⟩ | b) (⟨i', b'⟩ | ⟨i', b'⟩ | b') h <;>
      simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_castLE] at h <;>
      simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Prod.mk.injEq, Fin.ext_iff] <;>
      omega

/-- The encryption seed of `mlkem512Params` as a function of its byte positions. -/
def encSeedEquiv : (EncPos → UInt8) ≃ mlkem512Params.Seed :=
  (Equiv.sumArrowEquivProdArrow _ _ _).trans
    (Equiv.prodCongr (Equiv.curry _ _ _)
      ((Equiv.sumArrowEquivProdArrow _ _ _).trans
        (Equiv.prodCongr (Equiv.curry _ _ _) (Equiv.refl _))))

/-- The encryption seed `(r, e₁, e₂)` of `mlkem512Params` read from a row. -/
def eE (ν : Row) : mlkem512Params.Seed :=
  encSeedEquiv fun p => rowEquiv ν (encPos p)

/-- The components of `eE ν` are prefixes of the outputs of the nonces
`0, 1`, `2, 3` and `4`. -/
theorem eE_apply (ν : Row) :
    eE ν = (fun (i : Fin 2) b => prfBytes ν ⟨i, by omega⟩ (Fin.castLE blockLen_eta1 b),
      fun (i : Fin 2) b => prfBytes ν ⟨2 + i, by omega⟩ (Fin.castLE blockLen_eta2 b),
      fun b => prfBytes ν 4 (Fin.castLE blockLen_eta2 b)) :=
  rfl

/-- `eE` sends uniform rows to uniform encryption seeds. -/
theorem pushesUniform_eE : PushesUniform eE := by
  have h : eE = encSeedEquiv ∘ (fun x : Fin 5 × Fin 192 → UInt8 => fun p => x (encPos p)) ∘
      rowEquiv := rfl
  rw [h]
  exact pushesUniform_comp (pushesUniform_comp (pushesUniform_equiv rowEquiv)
    (pushesUniform_restrict encPos)) (pushesUniform_equiv encSeedEquiv)

/-- The byte positions of the key seed `(s, e)`. -/
abbrev KeyPos : Type :=
  (Fin 2 × Fin (64 * ConcreteParams.MLKEM512Params.eta1)) ⊕
    (Fin 2 × Fin (64 * ConcreteParams.MLKEM512Params.eta1))

/-- The output byte read at each position of the key seed: `s` from the nonces
`0, 1` and `e` from the nonces `2, 3`. -/
def keyPos : KeyPos ↪ Fin 5 × Fin 192 where
  toFun
    | .inl (i, b) => (⟨i, by omega⟩, Fin.castLE blockLen_eta1 b)
    | .inr (i, b) => (⟨2 + i, by omega⟩, Fin.castLE blockLen_eta1 b)
  inj' := by
    rintro (⟨i, b⟩ | ⟨i, b⟩) (⟨i', b'⟩ | ⟨i', b'⟩) h <;>
      simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_castLE] at h <;>
      simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Prod.mk.injEq, Fin.ext_iff] <;>
      omega

/-- The key seed of `mlkem512Params` as a function of its byte positions. -/
def keySeedEquiv : (KeyPos → UInt8) ≃ mlkem512Params.KeySeed :=
  (Equiv.sumArrowEquivProdArrow _ _ _).trans
    (Equiv.prodCongr (Equiv.curry _ _ _) (Equiv.curry _ _ _))

/-- The key seed `(s, e)` of `mlkem512Params` read from a row. -/
def eK (ν : Row) : mlkem512Params.KeySeed :=
  keySeedEquiv fun p => rowEquiv ν (keyPos p)

/-- `eK` sends uniform rows to uniform key seeds. -/
theorem pushesUniform_eK : PushesUniform eK := by
  have h : eK = keySeedEquiv ∘ (fun x : Fin 5 × Fin 192 → UInt8 => fun p => x (keyPos p)) ∘
      rowEquiv := rfl
  rw [h]
  exact pushesUniform_comp (pushesUniform_comp (pushesUniform_equiv rowEquiv)
    (pushesUniform_restrict keyPos)) (pushesUniform_equiv keySeedEquiv)

end Rows

/-! ## The hypotheses `hKey` and `hEnc` at ML-KEM-512 -/

section Scheme

/-- The FIPS 203 K-PKE at `mlkem512Params`: the base scheme with compressed
ciphertexts. -/
abbrev S512 := mapCiphertext (toScheme mlkem512Params) mlkem512Compress mlkem512Decompress

/-- Key generation from a matrix `A` and a key seed: the public key
`(A, A s + e)` and the secret key `s`, with `(s, e)` sampled from the seed. -/
def kg512 (A : mlkem512Params.Mat) (ks : mlkem512Params.KeySeed) :
    MLWE_PKE_Basic.PK mlkem512Params.toBasic × MLWE_PKE_Basic.SK mlkem512Params.toBasic :=
  ((A, mlkem512Params.vec_add (mlkem512Params.mat_vec_mul A (mlkem512Params.sampleKey ks).1)
      (mlkem512Params.sampleKey ks).2), (mlkem512Params.sampleKey ks).1)

/-- Compressed encryption with the noise `(r, e₁, e₂)` read from the row `ρ`. -/
def enc512 (pk : MLWE_PKE_Basic.PK mlkem512Params.toBasic) (m : mlkem512Params.PT)
    (ρ : Row) : MLKEM512CT :=
  S512.enc pk m (eE ρ)

/-- The hypothesis `hKey` at ML-KEM-512: key generation at a uniform matrix and
the key seed read from a uniform row has the public-key distribution of `S512`. -/
theorem avg_kg512_eK (g' : MLWE_PKE_Basic.PK mlkem512Params.toBasic → ℝ≥0∞) :
    (avg fun p : mlkem512Params.Mat × Row => g' (kg512 p.1 (eK p.2)).1) =
      ∑ ks, S512.keygen ks * g' ks.1 := by
  rw [avg_prod]
  simp only [fun A => pushesUniform_eK (fun ks => g' (kg512 A ks).1)]
  rw [← tsum_fintype (L := SummationFilter.unconditional _)]
  change _ = ∑' ks, ((PMF.uniformFintype mlkem512Params.Mat).bind fun A =>
    (PMF.uniformFintype mlkem512Params.KeySeed).map fun ks => kg512 A ks) ks * g' ks.1
  rw [PMF.tsum_bind_mul]
  simp only [KEM.FOTransformU.tsum_map_mul, PMF.uniformFintype_apply]
  unfold avg
  rw [tsum_fintype (L := SummationFilter.unconditional _)]
  simp only [tsum_fintype (L := SummationFilter.unconditional _)]

/-- The hypothesis `hEnc` at ML-KEM-512: encryption at a uniform row has the
ciphertext distribution of `S512`. -/
theorem avg_enc512 (pk : MLWE_PKE_Basic.PK mlkem512Params.toBasic) (m : mlkem512Params.PT)
    (g' : MLKEM512CT → ℝ≥0∞) :
    (avg fun ρ : Row => g' (enc512 pk m ρ)) =
      avg fun r : mlkem512Params.Seed => g' (S512.enc pk m r) :=
  pushesUniform_eE fun r => g' (S512.enc pk m r)

end Scheme

/-! ## The module-LWE samples with a non-uniform matrix -/

section XOF

open CatCrypt.Quantum.QROM (sdExp mlweSample extSample)
open XOFMatrix (absDiff_le_of_close)

/-- The expectation of a bind is the `d`-weighted average of the expectation of
the continuation. -/
theorem sdExp_bind {α β : Type} (d : SDistr α) (K : α → SDistr β) (g : β → ℝ≥0∞) :
    sdExp (d >>= K) g = ∑' o, d o * Option.elim o 0 (fun a => sdExp (K a) g) := by
  change ∑' x, (SDistr.bind d K) (some x) * g x = _
  simp only [SDistr.bind, PMF.bind_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun o => ?_
  cases o with
  | none => simp [SDistr.fail]
  | some a =>
    simp only [Option.elim, sdExp, ← ENNReal.tsum_mul_left, mul_assoc]

/-- The expectation of a `[0, 1]`-valued function is at most one. -/
theorem sdExp_le_one {α : Type} (d : SDistr α) {g : α → ℝ≥0∞} (hg : ∀ x, g x ≤ 1) :
    sdExp d g ≤ 1 :=
  calc sdExp d g ≤ ∑' x, d (some x) :=
        ENNReal.tsum_le_tsum fun x => mul_le_of_le_one_right' (hg x)
    _ ≤ ∑' o, d o := ENNReal.tsum_comp_le_tsum_of_injective (Option.some_injective _) _
    _ = 1 := d.tsum_coe

/-- Two sub-distributions followed by the same continuation give expectations of
a `[0, 1]`-valued function at most `tvDist` apart. -/
theorem absDiff_sdExp_bind_le_tvDist {α β : Type} (d₁ d₂ : SDistr α) (K : α → SDistr β)
    (g : β → ℝ≥0∞) (hg : ∀ x, g x ≤ 1) :
    absDiff (sdExp (d₁ >>= K) g) (sdExp (d₂ >>= K) g) ≤ tvDist d₁ d₂ := by
  rw [sdExp_bind, sdExp_bind]
  refine le_iSup₂_of_le (f := fun (f : Option α → ℝ≥0∞) (_ : ∀ x, f x ≤ 1) =>
    absDiff (∑' x, d₁ x * f x) (∑' x, d₂ x * f x))
    (fun o => Option.elim o 0 fun a => sdExp (K a) g) ?_ le_rfl
  rintro (_ | a)
  · exact zero_le_one
  · exact sdExp_le_one _ hg

/-- `absDiff a b ≤ t` gives `a ≤ b + t` and `b ≤ a + t`. -/
theorem le_add_of_absDiff_le {a b t : ℝ≥0∞} (h : absDiff a b ≤ t) : a ≤ b + t ∧ b ≤ a + t :=
  ⟨by rw [add_comm]; exact tsub_le_iff_right.mp (le_sup_left.trans h),
    by rw [add_comm]; exact tsub_le_iff_right.mp (le_sup_right.trans h)⟩

variable (B : MLWE_PKE_Basic.Params)

/-- The module-LWE sample `mlweSample` with the matrix drawn from `dA`. -/
def mlweSampleWith (dA : SDistr B.Mat) (b : Bool) : SDistr (B.Mat × B.Vec) := do
  let A ← dA
  if b then do
    let u ← SDistr.uniform B.Vec
    pure (A, u)
  else do
    let s ← B.dshort_vec
    let e ← B.dshort_vec
    pure (A, B.vec_add (B.mat_vec_mul A s) e)

/-- The extended module-LWE sample `extSample` with the matrix drawn from `dA`. -/
def extSampleWith (dA : SDistr B.Mat) (b : Bool) : SDistr (B.Mat × B.Vec × B.Vec × B.R) := do
  let A ← dA
  let t ← SDistr.uniform B.Vec
  if b then do
    let u ← SDistr.uniform B.Vec
    let v ← SDistr.uniform B.R
    pure (A, t, u, v)
  else do
    let r ← B.dshort_vec
    let e1 ← B.dshort_vec2
    let e2 ← B.dshort_R
    pure (A, t, B.vec_add (B.mat_vec_mul (B.mat_transpose A) r) e1,
      B.ring_add (B.vec_dot t r) e2)

/-- With a uniform matrix, `mlweSampleWith` is `mlweSample`. -/
theorem mlweSampleWith_uniform (b : Bool) :
    mlweSampleWith B (SDistr.uniform B.Mat) b = mlweSample B b := rfl

/-- With a uniform matrix, `extSampleWith` is `extSample`. -/
theorem extSampleWith_uniform (b : Bool) :
    extSampleWith B (SDistr.uniform B.Mat) b = extSample B b := rfl

/-- **Matrix change in the module-LWE sample.** For every `[0, 1]`-valued `g`, the
advantage of `g` on the sample with the matrix drawn from `dA` is within
`2 · tvDist dA U` of its advantage on `mlweSample`, `U` the uniform matrix. -/
theorem absDiff_mlweSampleWith_le (dA : SDistr B.Mat) (g : B.Mat × B.Vec → ℝ≥0∞)
    (hg : ∀ x, g x ≤ 1) :
    absDiff (sdExp (mlweSampleWith B dA false) g) (sdExp (mlweSampleWith B dA true) g) ≤
      absDiff (sdExp (mlweSample B false) g) (sdExp (mlweSample B true) g) +
        2 * tvDist dA (SDistr.uniform B.Mat) := by
  have h := fun b : Bool => le_add_of_absDiff_le
    (absDiff_sdExp_bind_le_tvDist dA (SDistr.uniform B.Mat) (g := g) (hg := hg) (K := fun A =>
      if b then do
        let u ← SDistr.uniform B.Vec
        pure (A, u)
      else do
        let s ← B.dshort_vec
        let e ← B.dshort_vec
        pure (A, B.vec_add (B.mat_vec_mul A s) e)))
  exact absDiff_le_of_close (h false).1 (h false).2 (h true).1 (h true).2

/-- **Matrix change in the extended module-LWE sample.** For every
`[0, 1]`-valued `g`, the advantage of `g` on the extended sample with the matrix
drawn from `dA` is within `2 · tvDist dA U` of its advantage on `extSample`. -/
theorem absDiff_extSampleWith_le (dA : SDistr B.Mat) (g : B.Mat × B.Vec × B.Vec × B.R → ℝ≥0∞)
    (hg : ∀ x, g x ≤ 1) :
    absDiff (sdExp (extSampleWith B dA false) g) (sdExp (extSampleWith B dA true) g) ≤
      absDiff (sdExp (extSample B false) g) (sdExp (extSample B true) g) +
        2 * tvDist dA (SDistr.uniform B.Mat) := by
  have h := fun b : Bool => le_add_of_absDiff_le
    (absDiff_sdExp_bind_le_tvDist dA (SDistr.uniform B.Mat) (g := g) (hg := hg) (K := fun A => do
      let t ← SDistr.uniform B.Vec
      if b then do
        let u ← SDistr.uniform B.Vec
        let v ← SDistr.uniform B.R
        pure (A, t, u, v)
      else do
        let r ← B.dshort_vec
        let e1 ← B.dshort_vec2
        let e2 ← B.dshort_R
        pure (A, t, B.vec_add (B.mat_vec_mul (B.mat_transpose A) r) e1,
          B.ring_add (B.vec_dot t r) e2)))
  exact absDiff_le_of_close (h false).1 (h false).2 (h true).1 (h true).2

end XOF

/-! ## Distinguishers with oracle access -/

section QAux

open CatCrypt.Quantum CatCrypt.Quantum.QROM
open CatCrypt.Crypto.PKE.Games (Scheme)

/-- A uniform average of a `[0, 1]`-valued function is at most one. -/
theorem sum_inv_mul_le_one {α : Type} [Fintype α] {f : α → ℝ≥0∞} (h : ∀ x, f x ≤ 1) :
    ∑ x, (Fintype.card α : ℝ≥0∞)⁻¹ * f x ≤ 1 :=
  calc ∑ x, (Fintype.card α : ℝ≥0∞)⁻¹ * f x ≤ ∑ _x : α, (Fintype.card α : ℝ≥0∞)⁻¹ :=
        Finset.sum_le_sum fun x _ => mul_le_of_le_one_right' (h x)
    _ = (Fintype.card α : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ 1 := ENNReal.mul_inv_le_one _

variable {m₁ m₂ n W q k c a : ℕ} {SK C R K Hash Z ι X : Type}
  [Fintype Z] [DecidableEq Z] [Fintype K] [Nonempty K] [Fintype C] [DecidableEq C]
  [DecidableEq Hash] [Fintype ι] (B : MLWE_PKE_Basic.Params)
  (S : Scheme (MLWE_PKE_Basic.PK B) SK B.PT C R)
  (hpk : MLWE_PKE_Basic.PK B → Hash) (eG : (B.PT × Hash) ≃ Fin m₁)
  (eJ : (Z × C) ≃ Fin m₂) (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)
  [NeZero n] [NeZero c]

/-- The acceptance probability `qAuxAcc` of a distinguisher with oracle access is
at most one. -/
theorem qAuxAcc_le_one (key : X → MLWE_PKE_Basic.PK B)
    (E : QAuxDist ι X (m₁ + m₂) n W q k c a C K) (x : X) :
    qAuxAcc S hpk eG eJ eKR eC eKa key E x ≤ 1 :=
  sum_inv_mul_le_one fun _ => sum_inv_mul_le_one fun _ => sum_inv_mul_le_one fun _ =>
    sum_inv_mul_le_one fun _ => sum_inv_mul_le_one fun _ => sum_inv_mul_le_one fun _ =>
      prTrue_Q_le_one _ _

/-- `qMLWEAux` with the matrix of the sample drawn from `dA`. -/
def qMLWEAuxWith (dA : SDistr B.Mat)
    (E : QAuxDist ι (MLWE_PKE_Basic.PK B) (m₁ + m₂) n W q k c a C K) : ℝ≥0∞ :=
  absDiff (sdExp (mlweSampleWith B dA false) (qAuxAcc S hpk eG eJ eKR eC eKa id E))
    (sdExp (mlweSampleWith B dA true) (qAuxAcc S hpk eG eJ eKR eC eKa id E))

/-- `qMLWEExtAux` with the matrix of the sample drawn from `dA`. -/
def qMLWEExtAuxWith (dA : SDistr B.Mat)
    (E : QAuxDist ι (B.Mat × B.Vec × B.Vec × B.R) (m₁ + m₂) n W q k c a C K) : ℝ≥0∞ :=
  absDiff (sdExp (extSampleWith B dA false)
      (qAuxAcc S hpk eG eJ eKR eC eKa (fun x => (x.1, x.2.1)) E))
    (sdExp (extSampleWith B dA true) (qAuxAcc S hpk eG eJ eKR eC eKa (fun x => (x.1, x.2.1)) E))

/-- The quantum module-LWE advantage with oracle access changes by at most
`2 · tvDist dA U` when the uniform matrix `U` is replaced by `dA`. -/
theorem qMLWEAuxWith_le (dA : SDistr B.Mat)
    (E : QAuxDist ι (MLWE_PKE_Basic.PK B) (m₁ + m₂) n W q k c a C K) :
    qMLWEAuxWith B S hpk eG eJ eKR eC eKa dA E ≤
      qMLWEAux B S hpk eG eJ eKR eC eKa E + 2 * tvDist dA (SDistr.uniform B.Mat) :=
  absDiff_mlweSampleWith_le B dA _ (qAuxAcc_le_one B S hpk eG eJ eKR eC eKa id E)

/-- The quantum extended module-LWE advantage with oracle access changes by at
most `2 · tvDist dA U` when the uniform matrix `U` is replaced by `dA`. -/
theorem qMLWEExtAuxWith_le (dA : SDistr B.Mat)
    (E : QAuxDist ι (B.Mat × B.Vec × B.Vec × B.R) (m₁ + m₂) n W q k c a C K) :
    qMLWEExtAuxWith B S hpk eG eJ eKR eC eKa dA E ≤
      qMLWEExtAux B S hpk eG eJ eKR eC eKa E + 2 * tvDist dA (SDistr.uniform B.Mat) :=
  absDiff_extSampleWith_le B dA _ (qAuxAcc_le_one B S hpk eG eJ eKR eC eKa _ E)

end QAux

/-! ## The XOF matrix at ML-KEM-512 -/

section XOF512

open CatCrypt.Quantum.QROM (sdExp mlweSample extSample)
open XOFMatrix (xofMatrixDistVia xofMatrixDistVia_minorant minorant_option
  tsum_le_add_of_minorant nonFillProb nonFillProb_le)

/-- The XOF matrix under any relabelling `e` is within `k² · nonFillProb m` of a
uniform matrix in total variation. -/
theorem tvDist_xofMatrixDistVia_le (k m : ℕ) {T : Type} [Fintype T] [Nonempty T]
    (e : XOFMatrix.Mat k ≃ T) :
    tvDist (xofMatrixDistVia (m := m) e) (SDistr.uniform T) ≤
      ((k * k : ℕ) : ℝ≥0∞) * nonFillProb m := by
  refine iSup₂_le fun f hf => ?_
  have h := tsum_le_add_of_minorant (xofMatrixDistVia (m := m) e) (SDistr.uniform T) _
    (minorant_option _ _ (xofMatrixDistVia_minorant (m := m) e)) f hf
  exact sup_le (tsub_le_iff_left.mpr h.1) (tsub_le_iff_left.mpr h.2)

/-- The ML-KEM-512 base parameters. -/
abbrev B512 : MLWE_PKE_Basic.Params := mlkem512Params.toBasic

/-- **The XOF hop at ML-KEM-512.** With the matrix `e (SampleNTT(XOF(ρ, j, i)))`
read from `k² = 4` independent uniform XOF streams of `m = 280` three-byte groups
(five SHAKE-128 blocks), every `[0, 1]`-valued distinguishing advantage on the
module-LWE sample is within `2 · 4 · C(560, 255) · (767 / 4096) ^ 305` of its
advantage with a uniform matrix. -/
theorem absDiff_mlweSample_xof512_le (e : XOFMatrix.Mat 2 ≃ B512.Mat)
    (g : B512.Mat × B512.Vec → ℝ≥0∞) (hg : ∀ x, g x ≤ 1) :
    absDiff (sdExp (mlweSampleWith B512 (xofMatrixDistVia (m := 280) e) false) g)
        (sdExp (mlweSampleWith B512 (xofMatrixDistVia (m := 280) e) true) g) ≤
      absDiff (sdExp (mlweSample B512 false) g) (sdExp (mlweSample B512 true) g) +
        2 * (((2 * 2 : ℕ) : ℝ≥0∞) *
          (((2 * 280).choose 255 : ℝ≥0∞) * (767 / 4096) ^ (2 * 280 - 255))) :=
  (absDiff_mlweSampleWith_le B512 _ g hg).trans (by
    gcongr
    exact (tvDist_xofMatrixDistVia_le 2 280 e).trans (by
      gcongr
      exact nonFillProb_le 280 (by norm_num)))

/-- **The XOF hop at ML-KEM-512, extended sample.** The bound of
`absDiff_mlweSample_xof512_le` for the extended module-LWE sample. -/
theorem absDiff_extSample_xof512_le (e : XOFMatrix.Mat 2 ≃ B512.Mat)
    (g : B512.Mat × B512.Vec × B512.Vec × B512.R → ℝ≥0∞) (hg : ∀ x, g x ≤ 1) :
    absDiff (sdExp (extSampleWith B512 (xofMatrixDistVia (m := 280) e) false) g)
        (sdExp (extSampleWith B512 (xofMatrixDistVia (m := 280) e) true) g) ≤
      absDiff (sdExp (extSample B512 false) g) (sdExp (extSample B512 true) g) +
        2 * (((2 * 2 : ℕ) : ℝ≥0∞) *
          (((2 * 280).choose 255 : ℝ≥0∞) * (767 / 4096) ^ (2 * 280 - 255))) :=
  (absDiff_extSampleWith_le B512 _ g hg).trans (by
    gcongr
    exact (tvDist_xofMatrixDistVia_le 2 280 e).trans (by
      gcongr
      exact nonFillProb_le 280 (by norm_num)))

end XOF512

end CatCrypt.Crypto.MLKEM.PRFInstance512
