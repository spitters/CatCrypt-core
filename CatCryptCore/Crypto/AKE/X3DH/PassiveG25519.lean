/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DHPassiveKeygen
public import CatCryptCore.Crypto.Libcrux.Bridge_X25519Group

/-!
# X3DH over X25519 from DDH in the prime-order subgroup of Curve25519

The passive X3DH bound with the hybrid values drawn by key generation
(`x3dh_advantage_le_K`) at the parameters of X25519 functions `sm`, `bp`
(`P.dh = x25519DDHOf sm bp`), under their RFC 7748 correctness on the subgroup `G25519 B`
(`X25519HomOf sm bp B`); at the libcrux functions (`P.dh = concreteDDH_X25519`) the hypothesis
is `X25519Hom B`. Each of the four DDH advantages `DDH_AdvantageK (x25519DDHOf sm bp)` is at most
the standard DDH advantage in `G25519 B` of the reduction encoding the triple
(`DDH_AdvantageK_x25519DDHOf_le`), plus `5 * Δ25519`. The KDF game over key generation is the
encoded sampled game `kdfSampled B kdf` at the sampler `signedClamp`: the KDF applied to the
encodings `encU (g^e)` of four subgroup elements; at the uniform sampler its advantage is
`KDF_G25519_Advantage B kdf A`, the KDF as an extractor on the encodings of four uniform
subgroup elements, and the change of sampler costs `4 * Δ25519`. The session bound has
`24 * Δ25519` in total.

## Main definitions

* `kdfSampled B kdf` — the KDF game as a game over four exponent draws (real) and none (ideal,
  a uniform key)
* `KDF_G25519_Advantage B kdf A` — its advantage at the uniform exponent sampler
* `x3dhG25519Bound B P A` — four standard DDH advantages in `G25519 B` and the KDF advantage

## Main results

* `kdfSampled_realizes_x25519DDHOf`, `kdfSampled_realizes_X25519` — `KDF_Random_RealK` and
  the uniform key at X25519 functions are the game `kdfSampled B kdf` at `signedClamp`
* `KDF_Random_AdvantageK_x25519DDHOf_le`, `KDF_Random_AdvantageK_X25519_le` —
  `KDF_Random_AdvantageK ≤ KDF_G25519_Advantage + 4 * Δ25519`
* `x3dh_advantage_le_G25519_of_hom`, `x3dh_advantage_le_G25519` — for every distinguisher `D`,
  the advantage between the real and the ideal session at X25519 functions is at most
  `x3dhG25519Bound` at the KI adversary of `D` plus `24 * Δ25519`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.X3DH.G25519

open CatCrypt.Core CatCrypt.Prob CatCrypt.NonUniform CatCrypt.Crypto CatCrypt.Crypto.ECC
open CatCrypt.Crypto.Assumptions
open CatCrypt.Crypto.Signal.X3DH
open CatCrypt.Crypto.Signal.Session.X3DHHops
open CatCrypt.Crypto.Libcrux.Bridge_X25519
open CatCrypt.Crypto.Libcrux.Bridge_X25519Group
open scoped ENNReal

/-- The KDF game over the exponents of `G25519 B`: the real view is the KDF of the encodings
of `g^x₀`, …, `g^x₃` for four exponent draws, the ideal view a uniform key. -/
noncomputable def kdfSampled (B : Curve25519Point)
    (kdf : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 →
      Vector UInt8 32) :
    SampledGame (ZMod curve25519SubgroupOrder) (Vector UInt8 32) where
  nR := 4
  nI := 0
  real xs := SPComp.pure (kdf (encU (g25519Pow (xs 0) : G25519 B))
    (encU (g25519Pow (xs 1) : G25519 B)) (encU (g25519Pow (xs 2) : G25519 B))
    (encU (g25519Pow (xs 3) : G25519 B)))
  ideal _ := SPComp.sample (Vector UInt8 32)

/-- The advantage of `A` against the KDF game at the uniform exponent sampler: the KDF on the
encodings of four uniform elements of `G25519 B` against a uniform key. -/
noncomputable def KDF_G25519_Advantage (B : Curve25519Point)
    (kdf : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 →
      Vector UInt8 32)
    (A : Vector UInt8 32 → SPComp Bool) : ℝ≥0∞ :=
  (kdfSampled B kdf).advAt (SDistr.uniform _) A

variable {B : Curve25519Point} [Fact (addOrderOf B = curve25519SubgroupOrder)]
variable {sm : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32}
  {bp : Vector UInt8 32 → Vector UInt8 32}

/-- **The KDF game of X25519 functions realized in the subgroup**: under `X25519HomOf sm bp B`,
the KDF on the public parts of four key pairs of `x25519DDHOf sm bp` and the uniform key are the
game `kdfSampled B kdf` at the sampler `signedClamp`. -/
theorem kdfSampled_realizes_x25519DDHOf (h : X25519HomOf sm bp B)
    (kdf : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 →
      Vector UInt8 32) :
    SampledRealizes (KDF_Random_RealK ⟨x25519DDHOf sm bp, kdf⟩) KDF_Random_Ideal
      (kdfSampled B kdf) signedClamp id where
  real := by
    have h2 : ∀ x y z w : ZMod curve25519SubgroupOrder,
        (Fin.cons x (Fin.cons y (Fin.cons z (Fin.cons w Fin.elim0))) : Fin 4 → _) 2 = z :=
      fun _ _ _ _ => rfl
    have h3 : ∀ x y z w : ZMod curve25519SubgroupOrder,
        (Fin.cons x (Fin.cons y (Fin.cons z (Fin.cons w Fin.elim0))) : Fin 4 → _) 3 = w :=
      fun _ _ _ _ => rfl
    simp only [KDF_Random_RealK, SampledGame.realAt, kdfSampled, h2, h3,
      sampleFrom_replicateFin_succ_bind, sampleFrom_replicateFin_zero_bind, SPComp.map_id,
      SPComp.bind_assoc, SPComp.pure_bind, sampleFrom_signedClamp_bind,
      Fin.cons_zero, Fin.cons_one, encU_pow_signedE, h.base_eq, sample_bool_bind_const]
  ideal := by
    simp only [KDF_Random_Ideal, SampledGame.idealAt, kdfSampled,
      sampleFrom_replicateFin_zero_bind, SPComp.map_id]

/-- **The KDF game of X25519 realized in the subgroup**: under `X25519Hom B`, the KDF on the
public parts of four key pairs of `concreteDDH_X25519` and the uniform key are the game
`kdfSampled B kdf` at the sampler `signedClamp`. -/
theorem kdfSampled_realizes_X25519 (h : X25519Hom B)
    (kdf : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 →
      Vector UInt8 32) :
    SampledRealizes (KDF_Random_RealK ⟨concreteDDH_X25519, kdf⟩) KDF_Random_Ideal
      (kdfSampled B kdf) signedClamp id :=
  kdfSampled_realizes_x25519DDHOf h kdf

/-- **The KDF game over key generation of X25519 functions**: under `X25519HomOf sm bp B`, its
advantage is at most the advantage against the KDF on the encodings of four uniform subgroup
elements, plus `Δ25519` for each of the four exponent draws. -/
theorem KDF_Random_AdvantageK_x25519DDHOf_le (h : X25519HomOf sm bp B)
    (kdf : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 →
      Vector UInt8 32)
    (A : Vector UInt8 32 → SPComp Bool) :
    KDF_Random_AdvantageK ⟨x25519DDHOf sm bp, kdf⟩ A ≤
      KDF_G25519_Advantage B kdf A + 4 * Δ25519 := by
  have hR := advantageA_le_of_realizes (kdfSampled B kdf) signedClampCert id
    (kdfSampled_realizes_x25519DDHOf h kdf) A
  norm_num [kdfSampled] at hR
  exact hR

/-- **The KDF game over key generation at X25519**: under `X25519Hom B`, its advantage is at
most the advantage against the KDF on the encodings of four uniform subgroup elements, plus
`Δ25519` for each of the four exponent draws. -/
theorem KDF_Random_AdvantageK_X25519_le (h : X25519Hom B)
    (kdf : Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32 →
      Vector UInt8 32)
    (A : Vector UInt8 32 → SPComp Bool) :
    KDF_Random_AdvantageK ⟨concreteDDH_X25519, kdf⟩ A ≤
      KDF_G25519_Advantage B kdf A + 4 * Δ25519 :=
  KDF_Random_AdvantageK_x25519DDHOf_le h kdf A

/-- The bound of the X3DH session at X25519: the standard DDH advantages in `G25519 B` of the
four hop reductions composed with the encoding of the triple, and the KDF advantage on the
encodings of four uniform subgroup elements of the KDF reduction. -/
noncomputable def x3dhG25519Bound (B : Curve25519Point)
    [Fact (addOrderOf B = curve25519SubgroupOrder)] (P : X3DHParams (Vector UInt8 32))
    (A : KI_Adversary P) : ℝ≥0∞ :=
  CatCryptCore.Examples.CyclicGroupDDH.DDH_Advantage (G25519 B)
      (encodedRed encU3 fun t => ddhRed1 P A t.1 t.2.1 t.2.2) +
    CatCryptCore.Examples.CyclicGroupDDH.DDH_Advantage (G25519 B)
      (encodedRed encU3 fun t => ddhRedK2 P A t.1 t.2.1 t.2.2) +
    CatCryptCore.Examples.CyclicGroupDDH.DDH_Advantage (G25519 B)
      (encodedRed encU3 fun t => ddhRedK3 P A t.1 t.2.1 t.2.2) +
    CatCryptCore.Examples.CyclicGroupDDH.DDH_Advantage (G25519 B)
      (encodedRed encU3 fun t => ddhRedK4 P A t.1 t.2.1 t.2.2) +
    KDF_G25519_Advantage B P.kdf (kdfReduction P A)

/-- **X3DH at X25519 functions from DDH in the prime-order subgroup.** Under
`X25519HomOf sm bp B`, for parameters whose Diffie-Hellman record is `x25519DDHOf sm bp` and
every distinguisher `D` of the key and the transcript, the advantage of `D` between the real and
the ideal session is at most `x3dhG25519Bound B P` at `kiAdversaryOfDistinguisher P D`, plus
`24 * Δ25519`: `5 * Δ25519` for each of the four DDH hops and `4 * Δ25519` for the four KDF
inputs. -/
theorem x3dh_advantage_le_G25519_of_hom (h : X25519HomOf sm bp B)
    (P : X3DHParams (Vector UInt8 32)) (hP : P.dh = x25519DDHOf sm bp)
    (D : Vector UInt8 32 × X3DHTranscript (Vector UInt8 32) → SPComp Bool) :
    AdvantageA (x3dh_real P) (x3dh_ideal P) D ≤
      x3dhG25519Bound B P (kiAdversaryOfDistinguisher P D) + 24 * Δ25519 := by
  obtain ⟨dh, kdf⟩ := P
  subst hP
  have hK := x3dh_advantage_le_K ⟨x25519DDHOf sm bp, kdf⟩
    (x25519DDHOf_symmetric (x25519CommutesOf_of_hom h)) D
  refine hK.trans ?_
  set A := kiAdversaryOfDistinguisher ⟨x25519DDHOf sm bp, kdf⟩ D
  have h1 := DDH_AdvantageK_x25519DDHOf_le h (ddhRed1 ⟨x25519DDHOf sm bp, kdf⟩ A)
  have h2 := DDH_AdvantageK_x25519DDHOf_le h (ddhRedK2 ⟨x25519DDHOf sm bp, kdf⟩ A)
  have h3 := DDH_AdvantageK_x25519DDHOf_le h (ddhRedK3 ⟨x25519DDHOf sm bp, kdf⟩ A)
  have h4 := DDH_AdvantageK_x25519DDHOf_le h (ddhRedK4 ⟨x25519DDHOf sm bp, kdf⟩ A)
  have h5 := KDF_Random_AdvantageK_x25519DDHOf_le h kdf
    (kdfReduction ⟨x25519DDHOf sm bp, kdf⟩ A)
  unfold x3dhKIReductionBoundK x3dhG25519Bound
  refine (add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) h5).trans
    (le_of_eq ?_)
  ring

/-- **X3DH at X25519 from DDH in the prime-order subgroup.** Under `X25519Hom B`, for
parameters whose Diffie-Hellman record is `concreteDDH_X25519` and every distinguisher `D` of
the key and the transcript, the advantage of `D` between the real and the ideal session is at
most `x3dhG25519Bound B P` at `kiAdversaryOfDistinguisher P D`, plus `24 * Δ25519`: `5 * Δ25519`
for each of the four DDH hops and `4 * Δ25519` for the four KDF inputs. -/
theorem x3dh_advantage_le_G25519 (h : X25519Hom B) (P : X3DHParams (Vector UInt8 32))
    (hP : P.dh = concreteDDH_X25519)
    (D : Vector UInt8 32 × X3DHTranscript (Vector UInt8 32) → SPComp Bool) :
    AdvantageA (x3dh_real P) (x3dh_ideal P) D ≤
      x3dhG25519Bound B P (kiAdversaryOfDistinguisher P D) + 24 * Δ25519 :=
  x3dh_advantage_le_G25519_of_hom h P hP D

end CatCrypt.Crypto.Signal.X3DH.G25519
