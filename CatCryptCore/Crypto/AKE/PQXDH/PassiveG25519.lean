/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.PQXDHPassiveKeygen
public import CatCryptCore.Crypto.Libcrux.Bridge_X25519Group

/-!
# PQXDH over X25519 from a KEM assumption and DDH in the prime-order subgroup of Curve25519

The passive PQXDH bound with the replaced Diffie-Hellman values drawn by key generation
(`pqxdh_advantage_le_K`) at parameters whose Diffie-Hellman record is X25519
(`P.dh = concreteDDH_X25519`), under the RFC 7748 correctness of X25519 on the subgroup
`G25519 B` (`X25519Hom B`). The KEM advantage of the hop-0 reduction is unchanged. Each of the
four DDH advantages `DDH_AdvantageK concreteDDH_X25519` is at most the standard DDH advantage
in `G25519 B` of the reduction encoding the triple (`DDH_AdvantageK_X25519_le`), plus
`5 * Δ25519`. The KDF game over key generation is the encoded sampled game `kdfSampled B kdf`
at the sampler `signedClamp`: the KDF applied to the encodings `encU (g^e)` of four subgroup
elements and a uniform KEM input; at the uniform sampler its advantage is
`KDF_G25519_Advantage B kdf A`, the KDF as an extractor on the encodings of four uniform
subgroup elements and a uniform 32-byte string, and the change of sampler costs `4 * Δ25519`.
The session bound has `24 * Δ25519` in total.

## Main definitions

* `kdfSampled B kdf` — the KDF game as a game over four exponent draws (real) and none (ideal,
  a uniform key)
* `KDF_G25519_Advantage B kdf A` — its advantage at the uniform exponent sampler
* `pqxdhG25519Bound B P A` — the KEM advantage, four standard DDH advantages in `G25519 B`
  and the KDF advantage

## Main results

* `kdfSampled_realizes_X25519` — `KDF_Random_RealK` and the uniform key at X25519 are the
  game `kdfSampled B P.kdf` at `signedClamp`
* `KDF_Random_AdvantageK_X25519_le` — `KDF_Random_AdvantageK ≤ KDF_G25519_Advantage + 4 * Δ25519`
* `pqxdh_advantage_le_G25519` — for every distinguisher `D`, the advantage between the real
  and the ideal session at X25519 is at most `pqxdhG25519Bound` at the KI adversary of `D`
  plus `24 * Δ25519`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.PQXDH.G25519

open CatCrypt.Core CatCrypt.Prob CatCrypt.NonUniform CatCrypt.Crypto CatCrypt.Crypto.ECC
open CatCrypt.Crypto.Assumptions
open CatCrypt.Crypto.Signal.PQXDHPassive
open CatCrypt.Crypto.Libcrux.Bridge_X25519
open CatCrypt.Crypto.Libcrux.Bridge_X25519Group
open scoped ENNReal

/-- The KDF game over the exponents of `G25519 B`: the real view is the KDF of the encodings
of `g^x₀`, …, `g^x₃` for four exponent draws and of a uniform KEM input, the ideal view a
uniform key. -/
noncomputable def kdfSampled (B : Curve25519Point)
    (kdf : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 →
      Vector UInt8 32 → Vector UInt8 32) :
    SampledGame (ZMod curve25519SubgroupOrder) (Vector UInt8 32) where
  nR := 4
  nI := 0
  real xs := (SPComp.sample (Vector UInt8 32)).bind fun k =>
    SPComp.pure (kdf (encU (g25519Pow (xs 0) : G25519 B))
      (encU (g25519Pow (xs 1) : G25519 B)) (encU (g25519Pow (xs 2) : G25519 B))
      (encU (g25519Pow (xs 3) : G25519 B)) k)
  ideal _ := SPComp.sample (Vector UInt8 32)

/-- The advantage of `A` against the KDF game at the uniform exponent sampler: the KDF on the
encodings of four uniform elements of `G25519 B` and a uniform KEM input against a uniform
key. -/
noncomputable def KDF_G25519_Advantage (B : Curve25519Point)
    (kdf : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 →
      Vector UInt8 32 → Vector UInt8 32)
    (A : Vector UInt8 32 → SPComp Bool) : ℝ≥0∞ :=
  (kdfSampled B kdf).advAt (SDistr.uniform _) A

variable {B : Curve25519Point} [Fact (addOrderOf B = curve25519SubgroupOrder)]
variable {PK SK C Sd : Type} [SampleableType Sd]

omit [SampleableType Sd] in
/-- **The KDF game of X25519 realized in the subgroup**: under `X25519Hom B`, for parameters
whose Diffie-Hellman record is `concreteDDH_X25519`, the KDF on the public parts of four key
pairs and a uniform KEM input, and the uniform key, are the game `kdfSampled B P.kdf` at the
sampler `signedClamp`. -/
theorem kdfSampled_realizes_X25519 (h : X25519Hom B)
    (P : PassiveParams (Vector UInt8 32) PK SK C Sd) (hP : P.dh = concreteDDH_X25519) :
    Realizes (KDF_Random_RealK P) KDF_Random_Ideal (kdfSampled B P.kdf) signedClamp id where
  real := by
    have h2 : ∀ x y z w : ZMod curve25519SubgroupOrder,
        (Fin.cons x (Fin.cons y (Fin.cons z (Fin.cons w Fin.elim0))) : Fin 4 → _) 2 = z :=
      fun _ _ _ _ => rfl
    have h3 : ∀ x y z w : ZMod curve25519SubgroupOrder,
        (Fin.cons x (Fin.cons y (Fin.cons z (Fin.cons w Fin.elim0))) : Fin 4 → _) 3 = w :=
      fun _ _ _ _ => rfl
    simp only [KDF_Random_RealK, hP, SampledGame.realAt, kdfSampled, h2, h3,
      sampleFrom_replicateFin_succ_bind, sampleFrom_replicateFin_zero_bind, SPComp.map_id,
      SPComp.bind_assoc, SPComp.pure_bind, sampleFrom_signedClamp_bind, concreteDDH_X25519,
      Fin.cons_zero, Fin.cons_one, encU_pow_signedE, h.base_eq, sample_bool_bind_const]
  ideal := by
    simp only [KDF_Random_Ideal, SampledGame.idealAt, kdfSampled,
      sampleFrom_replicateFin_zero_bind, SPComp.map_id]

omit [SampleableType Sd] in
/-- **The KDF game over key generation at X25519**: under `X25519Hom B`, its advantage is at
most the advantage against the KDF on the encodings of four uniform subgroup elements and a
uniform KEM input, plus `Δ25519` for each of the four exponent draws. -/
theorem KDF_Random_AdvantageK_X25519_le (h : X25519Hom B)
    (P : PassiveParams (Vector UInt8 32) PK SK C Sd) (hP : P.dh = concreteDDH_X25519)
    (A : Vector UInt8 32 → SPComp Bool) :
    KDF_Random_AdvantageK P A ≤ KDF_G25519_Advantage B P.kdf A + 4 * Δ25519 := by
  have hR := advantageA_le_of_realizes (kdfSampled B P.kdf) signedClampCert id
    (kdfSampled_realizes_X25519 h P hP) A
  norm_num [kdfSampled] at hR
  exact hR

/-- The bound of the PQXDH session at X25519: the KEM advantage of the hop-0 reduction, the
standard DDH advantages in `G25519 B` of the four Diffie-Hellman hop reductions composed with
the encoding of the triple, and the KDF advantage on the encodings of four uniform subgroup
elements and a uniform KEM input of the KDF reduction. -/
noncomputable def pqxdhG25519Bound (B : Curve25519Point)
    [Fact (addOrderOf B = curve25519SubgroupOrder)]
    (P : PassiveParams (Vector UInt8 32) PK SK C Sd) (A : KI_Adversary P) : ℝ≥0∞ :=
  KEM_Advantage P (kemRed P A) +
    CatCryptCore.Examples.CyclicGroupDDH.DDH_Advantage (G25519 B)
      (encodedRed encU3 fun t => ddhRed1 P A t.1 t.2.1 t.2.2) +
    CatCryptCore.Examples.CyclicGroupDDH.DDH_Advantage (G25519 B)
      (encodedRed encU3 fun t => ddhRedK2 P A t.1 t.2.1 t.2.2) +
    CatCryptCore.Examples.CyclicGroupDDH.DDH_Advantage (G25519 B)
      (encodedRed encU3 fun t => ddhRedK3 P A t.1 t.2.1 t.2.2) +
    CatCryptCore.Examples.CyclicGroupDDH.DDH_Advantage (G25519 B)
      (encodedRed encU3 fun t => ddhRedK4 P A t.1 t.2.1 t.2.2) +
    KDF_G25519_Advantage B P.kdf (kdfReduction P A)

/-- **PQXDH at X25519 from a KEM assumption and DDH in the prime-order subgroup.** Under
`X25519Hom B`, for parameters whose Diffie-Hellman record is `concreteDDH_X25519` and every
distinguisher `D` of the key and the transcript, the advantage of `D` between the real and the
ideal session is at most `pqxdhG25519Bound B P` at `kiAdversaryOfDistinguisher P D`, plus
`24 * Δ25519`: `5 * Δ25519` for each of the four DDH hops and `4 * Δ25519` for the four
Diffie-Hellman inputs of the KDF. -/
theorem pqxdh_advantage_le_G25519 (h : X25519Hom B)
    (P : PassiveParams (Vector UInt8 32) PK SK C Sd) (hP : P.dh = concreteDDH_X25519)
    (D : Vector UInt8 32 × PQXDHTranscript (Vector UInt8 32) PK C → SPComp Bool) :
    AdvantageA (pqxdh_real P) (pqxdh_ideal P) D ≤
      pqxdhG25519Bound B P (kiAdversaryOfDistinguisher P D) + 24 * Δ25519 := by
  have hK := pqxdh_advantage_le_K P
    (hP ▸ concreteDDH_X25519_symmetric (x25519Commutes_of_hom h)) D
  refine hK.trans ?_
  set A := kiAdversaryOfDistinguisher P D
  have h1 := DDH_AdvantageK_X25519_le h (ddhRed1 P A)
  have h2 := DDH_AdvantageK_X25519_le h (ddhRedK2 P A)
  have h3 := DDH_AdvantageK_X25519_le h (ddhRedK3 P A)
  have h4 := DDH_AdvantageK_X25519_le h (ddhRedK4 P A)
  have h5 := KDF_Random_AdvantageK_X25519_le h P hP (kdfReduction P A)
  rw [← hP] at h1 h2 h3 h4
  unfold pqxdhKIReductionBoundK pqxdhG25519Bound
  refine (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add le_rfl h1) h2) h3) h4)
    h5).trans (le_of_eq ?_)
  ring

end CatCrypt.Crypto.Signal.PQXDH.G25519
