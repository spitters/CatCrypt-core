/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.HKDF_UC
public import CatCryptCore.Crypto.KeyAgreement.Curve25519Subgroup

/-!
# The HKDF games at a key sampler

The Extract game with the input keying material drawn from a sampler, the Extract game with
the salt drawn from a sampler, and the multi-query Expand game with the PRK drawn from a
sampler, as games over a sampler (`SampledGame`) with one key draw in the real game and none
in the ideal game, whose output is uniform. At the uniform sampler their advantages are
`Extract_IKM_Advantage`, `Extract_Advantage` and `Expand_Seq_Advantage`.

When the key is the public part of a key pair whose law is certified against a reference
sampler (`SamplerCert`), the advantage of a distinguisher between the game keyed by key
generation and the ideal game is the advantage at the reference sampler plus the certified
bound, for one draw. For Curve25519, a public key that is the encoding `encU (g^e)` of a
subgroup element with `e` drawn from `signedClamp` (the X25519 public key under the
correctness hypothesis `X25519Hom`, `concreteDDH_X25519_keygen_snd`) is charged `Δ25519`
against the encoding of a uniform subgroup element.

The multi-query Expand game answers a list of queries under one PRK, the `info` of each
query a function of the earlier answers; its ideal game is a list of independent uniform
values (`uniformList`).

## Main definitions

* `uniformList W n` — `n` independent uniform values
* `expandSeq`, `expandSeqReal`, `Expand_Seq_Advantage` — the multi-query Expand game
* `extractIKMSampled`, `extractSaltSampled`, `expandSeqSampled` — the three games over a key
  sampler
* `Extract_IKM_AdvantageK`, `Extract_AdvantageK`, `Expand_Seq_AdvantageK` — their advantages at
  a sampler `μ`

## Main results

* `Extract_IKM_AdvantageK_uniform`, `Extract_AdvantageK_uniform`,
  `Expand_Seq_AdvantageK_uniform` — at the uniform sampler, the existing advantages
* `Extract_IKM_AdvantageK_eq` — at any sampler `μ`, the advantage against one draw from `μ`
  followed by Extract
* `extract_ikm_keygen_le`, `extract_salt_keygen_le`, `expand_seq_keygen_le` — for key
  generation whose public part is drawn from `c.μ`, the advantage against the game keyed by
  key generation is at most the advantage at `c.ν` plus `c.δ`
* `extract_ikm_G25519_le`, `extract_salt_G25519_le`, `expand_seq_G25519_le` — for key
  generation whose public part is `encU (g^e)` with `e` drawn from `signedClamp`, the
  advantage is at most the advantage at the encoding of a uniform element of `G25519 B` plus
  `Δ25519`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.HKDF_UC

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.NonUniform
open scoped ENNReal

/-! ## Uniform lists -/

/-- `n` independent uniform values, the first one sampled first. -/
noncomputable def uniformList (W : Type) [SampleableType W] : ℕ → SPComp (List W)
  | 0 => SPComp.pure []
  | n + 1 => SPComp.bind (SPComp.sample W) fun y =>
      SPComp.bind (uniformList W n) fun ys => SPComp.pure (y :: ys)

variable {W : Type} [SampleableType W]

/-- `n` uniform values are a heap-independent computation. -/
theorem uniformList_isPure (n : ℕ) : SPComp.IsPure (uniformList W n) := by
  induction n with
  | zero => exact SPComp.pure_isPure _
  | succ n ih =>
    exact SPComp.bind_isPure (SPComp.sample_isPure W) fun _ =>
      SPComp.bind_isPure ih fun _ => SPComp.pure_isPure _

/-- `a + b` uniform values are `a` uniform values followed by `b` uniform values. -/
theorem uniformList_add_bind (a b : ℕ) {β : Type} (f : List W → SPComp β) :
    (uniformList W (a + b)).bind f =
      (uniformList W a).bind fun l₁ => (uniformList W b).bind fun l₂ => f (l₁ ++ l₂) := by
  induction a generalizing f with
  | zero => simp [uniformList, SPComp.pure_bind]
  | succ a ih =>
    rw [Nat.add_right_comm]
    simp [uniformList, SPComp.bind_assoc, SPComp.pure_bind, ih]

/-- `n + 1` uniform values are `n` uniform values followed by one more. -/
theorem uniformList_succ_bind (n : ℕ) {β : Type} (f : List W → SPComp β) :
    (uniformList W (n + 1)).bind f =
      (uniformList W n).bind fun l => (SPComp.sample W).bind fun s => f (l ++ [s]) := by
  rw [uniformList_add_bind n 1]
  simp [uniformList, SPComp.bind_assoc, SPComp.pure_bind]

/-! ## The multi-query Expand game -/

/-- The answers to the Expand queries `qs` under `prk`, appended to the earlier
answers `os`: the query `q` is answered by `expand prk (q os)`. -/
def expandSeq (H : HKDFDef W) (prk : W) : List W → List (List W → W) → List W
  | os, [] => os
  | os, q :: qs => expandSeq H prk (os ++ [H.expand prk (q os)]) qs

/-- Real multi-query Expand game: the answers to `qs` under a uniform PRK. -/
noncomputable def expandSeqReal (H : HKDFDef W) (qs : List (List W → W)) : SPComp (List W) :=
  SPComp.bind (SPComp.sample W) fun prk => SPComp.pure (expandSeq H prk [] qs)

/-- Advantage of `A` in distinguishing the answers to the Expand queries `qs`
under a uniform PRK from `qs.length` independent uniform values; the `info` of
each query is a function of the earlier answers. This is the PRF security of
HKDF-Expand (RFC 5869, §2.3), HMAC under the PRK, against the adversary that
asks the queries `qs` (Krawczyk, CRYPTO 2010, §4; Bellare, CRYPTO 2006), a PRF
game with `qs.length` queries. It is a PRF game when the queries are distinct. -/
noncomputable def Expand_Seq_Advantage (H : HKDFDef W) (qs : List (List W → W))
    (A : List W → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (expandSeqReal H qs) (uniformList W qs.length) A

/-! ## The games over a key sampler -/

/-- The Extract game at the salt `salt` with the input keying material drawn from the
sampler; the ideal game is a uniform PRK. -/
noncomputable def extractIKMSampled (H : HKDFDef W) (salt : W) : SampledGame W W where
  nR := 1
  nI := 0
  real xs := SPComp.pure (H.extract salt (xs 0))
  ideal _ := extract_ideal

/-- The Extract game at the input keying material `ikm` with the salt drawn from the sampler;
the ideal game is a uniform PRK. -/
noncomputable def extractSaltSampled (H : HKDFDef W) (ikm : W) : SampledGame W W where
  nR := 1
  nI := 0
  real xs := SPComp.pure (H.extract (xs 0) ikm)
  ideal _ := extract_ideal

/-- The multi-query Expand game with the PRK drawn from the sampler; the ideal game is a list
of independent uniform values. -/
noncomputable def expandSeqSampled (H : HKDFDef W) (qs : List (List W → W)) :
    SampledGame W (List W) where
  nR := 1
  nI := 0
  real xs := SPComp.pure (expandSeq H (xs 0) [] qs)
  ideal _ := uniformList W qs.length

/-- The Extract advantage with the input keying material drawn from `μ`. -/
noncomputable def Extract_IKM_AdvantageK (H : HKDFDef W) (salt : W) (μ : SDistr W)
    (A : W → SPComp Bool) : ℝ≥0∞ :=
  (extractIKMSampled H salt).advAt μ A

/-- The Extract advantage with the salt drawn from `μ`. -/
noncomputable def Extract_AdvantageK (H : HKDFDef W) (ikm : W) (μ : SDistr W)
    (A : W → SPComp Bool) : ℝ≥0∞ :=
  (extractSaltSampled H ikm).advAt μ A

/-- The multi-query Expand advantage with the PRK drawn from `μ`. -/
noncomputable def Expand_Seq_AdvantageK (H : HKDFDef W) (qs : List (List W → W))
    (μ : SDistr W) (A : List W → SPComp Bool) : ℝ≥0∞ :=
  (expandSeqSampled H qs).advAt μ A

/-! ## The uniform sampler -/

/-- One draw from `μ` followed by `k`. -/
theorem sampleFrom_replicateFin_one_bind {X V : Type} (μ : SDistr X)
    (k : (Fin 1 → X) → SPComp V) :
    (sampleFrom (replicateFin 1 μ)).bind k = (sampleFrom μ).bind fun x => k fun _ => x := by
  rw [sampleFrom_replicateFin_succ_bind]
  congr 1; funext x
  rw [sampleFrom_replicateFin_zero_bind]
  exact congrArg k (funext fun i => Fin.cases rfl (fun j => j.elim0) i)

/-- At the uniform sampler, the Extract advantage with the input keying material drawn from
the sampler is `Extract_IKM_Advantage`. -/
theorem Extract_IKM_AdvantageK_uniform (H : HKDFDef W) (salt : W) (A : W → SPComp Bool) :
    Extract_IKM_AdvantageK H salt (SDistr.uniform W) A = Extract_IKM_Advantage H salt A := by
  simp only [Extract_IKM_AdvantageK, SampledGame.advAt, SampledGame.realAt,
    SampledGame.idealAt, extractIKMSampled, sampleFrom_replicateFin_one_bind,
    sampleFrom_replicateFin_zero_bind, sampleFrom_uniform, Extract_IKM_Advantage,
    extract_ikm_real]

/-- The Extract advantage with the input keying material drawn from `μ` is the advantage
against one draw from `μ` followed by Extract. -/
theorem Extract_IKM_AdvantageK_eq (H : HKDFDef W) (salt : W) (μ : SDistr W)
    (A : W → SPComp Bool) :
    Extract_IKM_AdvantageK H salt μ A =
      AdvantageA ((sampleFrom μ).bind fun x => SPComp.pure (H.extract salt x)) extract_ideal A := by
  simp only [Extract_IKM_AdvantageK, SampledGame.advAt, SampledGame.realAt,
    SampledGame.idealAt, extractIKMSampled, sampleFrom_replicateFin_one_bind,
    sampleFrom_replicateFin_zero_bind]

/-- At the uniform sampler, the Extract advantage with the salt drawn from the sampler is
`Extract_Advantage`. -/
theorem Extract_AdvantageK_uniform (H : HKDFDef W) (ikm : W) (A : W → SPComp Bool) :
    Extract_AdvantageK H ikm (SDistr.uniform W) A = Extract_Advantage H ikm A := by
  simp only [Extract_AdvantageK, SampledGame.advAt, SampledGame.realAt,
    SampledGame.idealAt, extractSaltSampled, sampleFrom_replicateFin_one_bind,
    sampleFrom_replicateFin_zero_bind, sampleFrom_uniform, Extract_Advantage, extract_real]

/-- At the uniform sampler, the multi-query Expand advantage with the PRK drawn from the
sampler is `Expand_Seq_Advantage`. -/
theorem Expand_Seq_AdvantageK_uniform (H : HKDFDef W) (qs : List (List W → W))
    (A : List W → SPComp Bool) :
    Expand_Seq_AdvantageK H qs (SDistr.uniform W) A = Expand_Seq_Advantage H qs A := by
  simp only [Expand_Seq_AdvantageK, SampledGame.advAt, SampledGame.realAt,
    SampledGame.idealAt, expandSeqSampled, sampleFrom_replicateFin_one_bind,
    sampleFrom_replicateFin_zero_bind, sampleFrom_uniform, Expand_Seq_Advantage,
    expandSeqReal]

/-! ## Keys drawn by key generation -/

section Keygen

variable {S : Type} (kg : SPComp (S × W)) (c : SamplerCert W)

omit [SampleableType W] in
/-- The public part of key generation drawn from `c.μ`, followed by `k`. -/
theorem keygen_bind_snd (hkg : kg.map Prod.snd = sampleFrom c.μ) {V : Type}
    (k : W → SPComp V) : kg.bind (fun x => k x.2) = (sampleFrom c.μ).bind k := by
  rw [← hkg, SPComp.map, SPComp.bind_assoc]
  simp only [SPComp.pure_bind]

/-- **Extract keyed by key generation**: with the input keying material the public part of
key generation drawn from `c.μ`, the advantage of `A` against the Extract game is at most the
advantage at the reference sampler `c.ν` plus `c.δ`. -/
theorem extract_ikm_keygen_le (hkg : kg.map Prod.snd = sampleFrom c.μ) (H : HKDFDef W)
    (salt : W) (A : W → SPComp Bool) :
    AdvantageA (kg.bind fun x => SPComp.pure (H.extract salt x.2)) extract_ideal A ≤
      Extract_IKM_AdvantageK H salt c.ν A + c.δ := by
  have h := advantageA_le_of_realizes (extractIKMSampled H salt) c id
    (P := kg.bind fun x => SPComp.pure (H.extract salt x.2)) (Q := extract_ideal)
    { real := by
        rw [SPComp.map_id, keygen_bind_snd kg c hkg (fun w => SPComp.pure (H.extract salt w))]
        simp only [SampledGame.realAt, extractIKMSampled, sampleFrom_replicateFin_one_bind]
      ideal := by
        rw [SPComp.map_id]
        simp only [SampledGame.idealAt, extractIKMSampled, sampleFrom_replicateFin_zero_bind] }
    A
  rw [show encodedRed id A = A from rfl] at h
  simpa [Extract_IKM_AdvantageK, extractIKMSampled, encodedRed] using h

/-- **Extract keyed by key generation, salt side**: with the salt the public part of key
generation drawn from `c.μ`, the advantage of `A` against the Extract game is at most the
advantage at the reference sampler `c.ν` plus `c.δ`. -/
theorem extract_salt_keygen_le (hkg : kg.map Prod.snd = sampleFrom c.μ) (H : HKDFDef W)
    (ikm : W) (A : W → SPComp Bool) :
    AdvantageA (kg.bind fun x => SPComp.pure (H.extract x.2 ikm)) extract_ideal A ≤
      Extract_AdvantageK H ikm c.ν A + c.δ := by
  have h := advantageA_le_of_realizes (extractSaltSampled H ikm) c id
    (P := kg.bind fun x => SPComp.pure (H.extract x.2 ikm)) (Q := extract_ideal)
    { real := by
        rw [SPComp.map_id, keygen_bind_snd kg c hkg (fun w => SPComp.pure (H.extract w ikm))]
        simp only [SampledGame.realAt, extractSaltSampled, sampleFrom_replicateFin_one_bind]
      ideal := by
        rw [SPComp.map_id]
        simp only [SampledGame.idealAt, extractSaltSampled, sampleFrom_replicateFin_zero_bind] }
    A
  rw [show encodedRed id A = A from rfl] at h
  simpa [Extract_AdvantageK, extractSaltSampled, encodedRed] using h

/-- **Multi-query Expand keyed by key generation**: with the PRK the public part of key
generation drawn from `c.μ`, the advantage of `A` against the multi-query Expand game is at
most the advantage at the reference sampler `c.ν` plus `c.δ`. -/
theorem expand_seq_keygen_le (hkg : kg.map Prod.snd = sampleFrom c.μ) (H : HKDFDef W)
    (qs : List (List W → W)) (A : List W → SPComp Bool) :
    AdvantageA (kg.bind fun x => SPComp.pure (expandSeq H x.2 [] qs))
        (uniformList W qs.length) A ≤
      Expand_Seq_AdvantageK H qs c.ν A + c.δ := by
  have h := advantageA_le_of_realizes (expandSeqSampled H qs) c id
    (P := kg.bind fun x => SPComp.pure (expandSeq H x.2 [] qs))
    (Q := uniformList W qs.length)
    { real := by
        rw [SPComp.map_id, keygen_bind_snd kg c hkg (fun w => SPComp.pure (expandSeq H w [] qs))]
        simp only [SampledGame.realAt, expandSeqSampled, sampleFrom_replicateFin_one_bind]
      ideal := by
        rw [SPComp.map_id]
        simp only [SampledGame.idealAt, expandSeqSampled, sampleFrom_replicateFin_zero_bind] }
    A
  rw [show encodedRed id A = A from rfl] at h
  simpa [Expand_Seq_AdvantageK, expandSeqSampled, encodedRed] using h

end Keygen

/-! ## Curve25519 public keys -/

section G25519

open CatCrypt.Crypto.ECC

variable {B : Curve25519Point} {S : Type} (kg : SPComp (S × Vector UInt8 32))

/-- Key generation whose public part is `encU (g^e)` with `e` drawn from `signedClamp` draws
it from the image of `signedClamp`. -/
theorem keygen_snd_signedClamp
    (hkg : kg.map Prod.snd = (sampleFrom signedClamp).map (encU ∘ (g25519Pow (B := B)))) :
    kg.map Prod.snd =
      sampleFrom (signedClampCert.map (encU ∘ (g25519Pow (B := B)))).μ := by
  rw [hkg, SamplerCert.map, ← sampleFrom_bind_sampleFrom, SPComp.map]
  simp only [sampleFrom_pure]
  rfl

/-- **Extract keyed by Curve25519 key generation**: with the input keying material the
encoding `encU (g^e)` of a subgroup element, `e` drawn from `signedClamp`, the advantage of `A`
is at most the advantage with the input keying material the encoding of a uniform element of
`G25519 B`, plus `Δ25519`. -/
theorem extract_ikm_G25519_le
    (hkg : kg.map Prod.snd = (sampleFrom signedClamp).map (encU ∘ (g25519Pow (B := B))))
    (H : HKDFDef (Vector UInt8 32)) (salt : Vector UInt8 32)
    (A : Vector UInt8 32 → SPComp Bool) :
    AdvantageA (kg.bind fun x => SPComp.pure (H.extract salt x.2)) extract_ideal A ≤
      Extract_IKM_AdvantageK H salt
        ((SDistr.uniform (ZMod curve25519SubgroupOrder)).bind fun e =>
          SDistr.pure (encU (g25519Pow (B := B) e))) A + Δ25519 :=
  extract_ikm_keygen_le kg _ (keygen_snd_signedClamp kg hkg) H salt A

/-- **Extract keyed by Curve25519 key generation, salt side**: as `extract_ikm_G25519_le`,
with the salt drawn by key generation. -/
theorem extract_salt_G25519_le
    (hkg : kg.map Prod.snd = (sampleFrom signedClamp).map (encU ∘ (g25519Pow (B := B))))
    (H : HKDFDef (Vector UInt8 32)) (ikm : Vector UInt8 32)
    (A : Vector UInt8 32 → SPComp Bool) :
    AdvantageA (kg.bind fun x => SPComp.pure (H.extract x.2 ikm)) extract_ideal A ≤
      Extract_AdvantageK H ikm
        ((SDistr.uniform (ZMod curve25519SubgroupOrder)).bind fun e =>
          SDistr.pure (encU (g25519Pow (B := B) e))) A + Δ25519 :=
  extract_salt_keygen_le kg _ (keygen_snd_signedClamp kg hkg) H ikm A

/-- **Multi-query Expand keyed by Curve25519 key generation**: as `extract_ikm_G25519_le`,
with the PRK drawn by key generation. -/
theorem expand_seq_G25519_le
    (hkg : kg.map Prod.snd = (sampleFrom signedClamp).map (encU ∘ (g25519Pow (B := B))))
    (H : HKDFDef (Vector UInt8 32)) (qs : List (List (Vector UInt8 32) → Vector UInt8 32))
    (A : List (Vector UInt8 32) → SPComp Bool) :
    AdvantageA (kg.bind fun x => SPComp.pure (expandSeq H x.2 [] qs))
        (uniformList (Vector UInt8 32) qs.length) A ≤
      Expand_Seq_AdvantageK H qs
        ((SDistr.uniform (ZMod curve25519SubgroupOrder)).bind fun e =>
          SDistr.pure (encU (g25519Pow (B := B) e))) A + Δ25519 :=
  expand_seq_keygen_le kg _ (keygen_snd_signedClamp kg hkg) H qs A

end G25519

end CatCrypt.Crypto.HKDF_UC
