/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DHPassiveHops
public import CatCryptCore.Crypto.Assumptions.DDHSampled

/-!
# X3DH key indistinguishability with the hybrid values drawn by key generation

The hybrids of `X3DHPassiveHops` replace a Diffie-Hellman value by a uniform element of `W`.
Here each replaced value is the public part of a fresh key pair of `P.dh.keygen`, and the KDF
game `KDF_Random_RealK` applies the KDF to the public parts of four fresh key pairs. Each
DDH hop is then an equality with the DDH advantage `DDH_AdvantageK` whose ideal value is drawn
by key generation, and the last hop an equality with the KDF advantage
`KDF_Random_AdvantageK`. When the public part of a key pair is not uniform on `W` (X25519 on
32-byte strings), these are the advantages of games whose real and ideal values have the same
range.

## The hops

```
x3dh_real ─ ddhRed1 ─ hybK1 ─ ddhRedK2 ─ hybK2 ─ ddhRedK3 ─ hybK3 ─ ddhRedK4 ─ hybK4
  ─ kdfReduction ─ x3dh_ideal
```

The reductions are those of `X3DHPassiveHops`, with the values replaced in the earlier hops
drawn by key generation (`ddhRedK2`, `ddhRedK3`, `ddhRedK4`); `ddhRed1` and `kdfReduction`
are unchanged.

## Main results

* `hopK1_advantage_eq_ddh` … `hopK5_advantage_eq_kdf` — each hop is an equality of
  advantages.
* `x3dh_ki_security_K` — the advantage of `A` between the real and the ideal session is at
  most `x3dhKIReductionBoundK P A`.
* `x3dh_advantage_le_K` — for every distinguisher `D` of the key and the transcript, the same
  bound at `kiAdversaryOfDistinguisher P D`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.Session.X3DHHops

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.Assumptions
open CatCrypt.Crypto.Signal.X3DH
open scoped ENNReal

variable {W : Type} [SampleableType W]

/-! ## Hybrids -/

/-- Hybrid 1 over key generation: `DH1` replaced by the public part of a fresh key pair. -/
noncomputable def x3dh_hybK1 (P : X3DHParams W) : SPComp (W × X3DHTranscript W) :=
  x3dh_hyb P fun _ik_a ik_b spk_b opk_b ek =>
    P.dh.keygen.bind fun r1 =>
    SPComp.pure (r1.2, P.dh.ecdh ek.1 ik_b.2, P.dh.ecdh ek.1 spk_b.2, P.dh.ecdh ek.1 opk_b.2)

/-- Hybrid 2 over key generation: `DH1` and `DH2` replaced. -/
noncomputable def x3dh_hybK2 (P : X3DHParams W) : SPComp (W × X3DHTranscript W) :=
  x3dh_hyb P fun _ik_a _ik_b spk_b opk_b ek =>
    P.dh.keygen.bind fun r1 => P.dh.keygen.bind fun r2 =>
    SPComp.pure (r1.2, r2.2, P.dh.ecdh ek.1 spk_b.2, P.dh.ecdh ek.1 opk_b.2)

/-- Hybrid 3 over key generation: `DH1`, `DH2` and `DH3` replaced. -/
noncomputable def x3dh_hybK3 (P : X3DHParams W) : SPComp (W × X3DHTranscript W) :=
  x3dh_hyb P fun _ik_a _ik_b _spk_b opk_b ek =>
    P.dh.keygen.bind fun r1 => P.dh.keygen.bind fun r2 => P.dh.keygen.bind fun r3 =>
    SPComp.pure (r1.2, r2.2, r3.2, P.dh.ecdh ek.1 opk_b.2)

/-- Hybrid 4 over key generation: the four Diffie-Hellman values replaced. -/
noncomputable def x3dh_hybK4 (P : X3DHParams W) : SPComp (W × X3DHTranscript W) :=
  x3dh_hyb P fun _ik_a _ik_b _spk_b _opk_b _ek =>
    P.dh.keygen.bind fun r1 => P.dh.keygen.bind fun r2 =>
    P.dh.keygen.bind fun r3 => P.dh.keygen.bind fun r4 =>
    SPComp.pure (r1.2, r2.2, r3.2, r4.2)

/-! ## The DDH reductions -/

/-- Hop-2 reduction over key generation: the DDH challenge `(g_a, g_b, z)` as
`(ek, ik_B, DH2)`, `DH1` the public part of a fresh key pair, `DH3` and `DH4` on Bob's
side. -/
noncomputable def ddhRedK2 (P : X3DHParams W) (A : KI_Adversary P) (g_a g_b z : W) :
    SPComp Bool :=
  P.dh.keygen.bind fun ik_a => P.dh.keygen.bind fun spk_b => P.dh.keygen.bind fun opk_b =>
  P.dh.keygen.bind fun r1 =>
  A.run (P.kdf r1.2 z (P.dh.ecdh spk_b.1 g_a) (P.dh.ecdh opk_b.1 g_a))
    (ik_a.2, g_b, g_a, spk_b.2, opk_b.2)

/-- Hop-3 reduction over key generation: the DDH challenge `(g_a, g_b, z)` as
`(ek, spk_B, DH3)`, `DH4` on Bob's side. -/
noncomputable def ddhRedK3 (P : X3DHParams W) (A : KI_Adversary P) (g_a g_b z : W) :
    SPComp Bool :=
  P.dh.keygen.bind fun ik_a => P.dh.keygen.bind fun ik_b => P.dh.keygen.bind fun opk_b =>
  P.dh.keygen.bind fun r1 => P.dh.keygen.bind fun r2 =>
  A.run (P.kdf r1.2 r2.2 z (P.dh.ecdh opk_b.1 g_a)) (ik_a.2, ik_b.2, g_a, g_b, opk_b.2)

/-- Hop-4 reduction over key generation: the DDH challenge `(g_a, g_b, z)` as
`(ek, opk_B, DH4)`. -/
noncomputable def ddhRedK4 (P : X3DHParams W) (A : KI_Adversary P) (g_a g_b z : W) :
    SPComp Bool :=
  P.dh.keygen.bind fun ik_a => P.dh.keygen.bind fun ik_b => P.dh.keygen.bind fun spk_b =>
  P.dh.keygen.bind fun r1 => P.dh.keygen.bind fun r2 => P.dh.keygen.bind fun r3 =>
  A.run (P.kdf r1.2 r2.2 r3.2 z) (ik_a.2, ik_b.2, g_a, spk_b.2, g_b)

/-- `ddhRedK2` at the public key `pub e`, when key generation returns `(x, pub x)` and `ecdh`
commutes on public keys. -/
theorem ddhRedK2_pub (P : X3DHParams W) (A : KI_Adversary P) {pub : W → W}
    (hkg : P.dh.keygen = (SPComp.sample W).bind (fun x => SPComp.pure (x, pub x)))
    (hc : ECDHSym.CommutesOnPub P.dh.ecdh pub) (e g_b z : W) :
    ddhRedK2 P A (pub e) g_b z =
      (SPComp.sample W).bind fun ik_a => (SPComp.sample W).bind fun spk_b =>
      (SPComp.sample W).bind fun opk_b => (SPComp.sample W).bind fun r1 =>
      A.run (P.kdf (pub r1) z (P.dh.ecdh e (pub spk_b)) (P.dh.ecdh e (pub opk_b)))
        (pub ik_a, g_b, pub e, pub spk_b, pub opk_b) := by
  simp only [ddhRedK2, ECDHSym.keygen_bind hkg, hc _ e]

/-- `ddhRedK3` at the public key `pub e`, as `ddhRedK2_pub`. -/
theorem ddhRedK3_pub (P : X3DHParams W) (A : KI_Adversary P) {pub : W → W}
    (hkg : P.dh.keygen = (SPComp.sample W).bind (fun x => SPComp.pure (x, pub x)))
    (hc : ECDHSym.CommutesOnPub P.dh.ecdh pub) (e g_b z : W) :
    ddhRedK3 P A (pub e) g_b z =
      (SPComp.sample W).bind fun ik_a => (SPComp.sample W).bind fun ik_b =>
      (SPComp.sample W).bind fun opk_b => (SPComp.sample W).bind fun r1 =>
      (SPComp.sample W).bind fun r2 =>
      A.run (P.kdf (pub r1) (pub r2) z (P.dh.ecdh e (pub opk_b)))
        (pub ik_a, pub ik_b, pub e, g_b, pub opk_b) := by
  simp only [ddhRedK3, ECDHSym.keygen_bind hkg, hc _ e]

/-! ## The KDF assumption over key generation -/

/-- The KDF on the public parts of four fresh key pairs. -/
noncomputable def KDF_Random_RealK (P : X3DHParams W) : SPComp W :=
  P.dh.keygen.bind fun r1 => P.dh.keygen.bind fun r2 =>
  P.dh.keygen.bind fun r3 => P.dh.keygen.bind fun r4 =>
  SPComp.pure (P.kdf r1.2 r2.2 r3.2 r4.2)

/-- The advantage of `A` between the KDF on the public parts of four fresh key pairs and a
uniform key: the KDF as an extractor on the source of key generation. -/
noncomputable def KDF_Random_AdvantageK (P : X3DHParams W) (A : W → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (KDF_Random_RealK P) KDF_Random_Ideal A

/-! ## The hops -/

/-- **Hop 1.** The advantage between the real session and hybrid 1 is the DDH advantage of
`ddhRed1` with the ideal value drawn by key generation. -/
theorem hopK1_advantage_eq_ddh (P : X3DHParams W) (A : KI_Adversary P) :
    Advantage (wrap_hybrid P A (x3dh_real P) true) (wrap_hybrid P A (x3dh_hybK1 P) true) =
    DDH_AdvantageK P.dh (ddhRed1 P A) := by
  advantage_eq_nf [wrap_hybrid, x3dh_real, x3dh_hybK1, x3dh_hyb, ddhRed1, DDH_AdvantageK,
    DDH_Game_IdealK, DDH_ViewIdealK]

/-- **Hop 2.** The advantage between hybrids 1 and 2 is the DDH advantage of `ddhRedK2`. -/
theorem hopK2_advantage_eq_ddh (P : X3DHParams W) (A : KI_Adversary P)
    (h_sym : ECDHSym.ECDHSymmetric P.dh) :
    Advantage (wrap_hybrid P A (x3dh_hybK1 P) true) (wrap_hybrid P A (x3dh_hybK2 P) true) =
    DDH_AdvantageK P.dh (ddhRedK2 P A) := by
  obtain ⟨pub, hkg, hc⟩ := h_sym
  simp only [DDH_AdvantageK, DDH_Game_Real, DDH_Game_IdealK, DDH_ViewIdealK, wrap_hybrid,
    x3dh_hybK1, x3dh_hybK2, x3dh_hyb, SPComp.monad_bind_eq, ECDHSym.keygen_bind hkg,
    SPComp.bind_assoc, SPComp.pure_bind, ddhRedK2_pub P A hkg hc]
  advantage_eq_nf

/-- **Hop 3.** The advantage between hybrids 2 and 3 is the DDH advantage of `ddhRedK3`. -/
theorem hopK3_advantage_eq_ddh (P : X3DHParams W) (A : KI_Adversary P)
    (h_sym : ECDHSym.ECDHSymmetric P.dh) :
    Advantage (wrap_hybrid P A (x3dh_hybK2 P) true) (wrap_hybrid P A (x3dh_hybK3 P) true) =
    DDH_AdvantageK P.dh (ddhRedK3 P A) := by
  obtain ⟨pub, hkg, hc⟩ := h_sym
  simp only [DDH_AdvantageK, DDH_Game_Real, DDH_Game_IdealK, DDH_ViewIdealK, wrap_hybrid,
    x3dh_hybK2, x3dh_hybK3, x3dh_hyb, SPComp.monad_bind_eq, ECDHSym.keygen_bind hkg,
    SPComp.bind_assoc, SPComp.pure_bind, ddhRedK3_pub P A hkg hc]
  advantage_eq_nf

/-- **Hop 4.** The advantage between hybrids 3 and 4 is the DDH advantage of `ddhRedK4`. -/
theorem hopK4_advantage_eq_ddh (P : X3DHParams W) (A : KI_Adversary P) :
    Advantage (wrap_hybrid P A (x3dh_hybK3 P) true) (wrap_hybrid P A (x3dh_hybK4 P) true) =
    DDH_AdvantageK P.dh (ddhRedK4 P A) := by
  advantage_eq_nf [wrap_hybrid, x3dh_hybK3, x3dh_hybK4, x3dh_hyb, ddhRedK4, DDH_AdvantageK,
    DDH_Game_IdealK, DDH_ViewIdealK]

/-- **Hop 5.** The advantage between hybrid 4 and the ideal session is the KDF advantage of
`kdfReduction` over key generation. -/
theorem hopK5_advantage_eq_kdf (P : X3DHParams W) (A : KI_Adversary P) :
    Advantage (wrap_hybrid P A (x3dh_hybK4 P) true) (wrap_hybrid P A (x3dh_ideal P) true) =
    KDF_Random_AdvantageK P (kdfReduction P A) := by
  advantage_eq_nf [wrap_hybrid, x3dh_hybK4, x3dh_ideal, x3dh_hyb, kdfReduction,
    KDF_Random_AdvantageK, KDF_Random_RealK, KDF_Random_Ideal]

/-! ## The bound -/

/-- Sum of the advantages of the five reductions built from `A`, the hybrid values drawn by
key generation: the DDH advantages `DDH_AdvantageK` of `ddhRed1`, `ddhRedK2`, `ddhRedK3`,
`ddhRedK4` and the KDF advantage `KDF_Random_AdvantageK` of `kdfReduction`. -/
noncomputable def x3dhKIReductionBoundK (P : X3DHParams W) (A : KI_Adversary P) : ℝ≥0∞ :=
  DDH_AdvantageK P.dh (ddhRed1 P A) + DDH_AdvantageK P.dh (ddhRedK2 P A) +
    DDH_AdvantageK P.dh (ddhRedK3 P A) + DDH_AdvantageK P.dh (ddhRedK4 P A) +
    KDF_Random_AdvantageK P (kdfReduction P A)

/-- **X3DH key indistinguishability over key generation.** When key generation returns pairs
`(x, pub x)` and `ecdh` commutes on public keys, the advantage of `A` between the real and the
ideal session is at most `x3dhKIReductionBoundK P A`. -/
theorem x3dh_ki_security_K (P : X3DHParams W) (A : KI_Adversary P)
    (h_sym : ECDHSym.ECDHSymmetric P.dh) :
    Advantage (wrap_hybrid P A (x3dh_real P) true) (wrap_hybrid P A (x3dh_ideal P) true) ≤
      x3dhKIReductionBoundK P A := by
  have h1 := (hopK1_advantage_eq_ddh P A).le
  have h2 := (hopK2_advantage_eq_ddh P A h_sym).le
  have h3 := (hopK3_advantage_eq_ddh P A h_sym).le
  have h4 := (hopK4_advantage_eq_ddh P A).le
  have h5 := (hopK5_advantage_eq_kdf P A).le
  unfold x3dhKIReductionBoundK
  hop_chain

/-- **X3DH against a distinguisher of the key and the transcript, over key generation.** For
every `D`, the advantage of `D` between the real and the ideal session is at most
`x3dhKIReductionBoundK` at `kiAdversaryOfDistinguisher P D`. -/
theorem x3dh_advantage_le_K (P : X3DHParams W) (h_sym : ECDHSym.ECDHSymmetric P.dh)
    (D : W × X3DHTranscript W → SPComp Bool) :
    AdvantageA (x3dh_real P) (x3dh_ideal P) D ≤
      x3dhKIReductionBoundK P (kiAdversaryOfDistinguisher P D) := by
  have hA := x3dh_ki_security_K P (kiAdversaryOfDistinguisher P D) h_sym
  rw [wrap_hybrid_kiAdversaryOfDistinguisher, wrap_hybrid_kiAdversaryOfDistinguisher] at hA
  unfold AdvantageA Advantage
  unfold Advantage at hA
  rwa [← prTrue_bind_freeze_eq (x3dh_real_isPure P) D,
    ← prTrue_bind_freeze_eq (x3dh_ideal_isPure P) D] at hA

end CatCrypt.Crypto.Signal.Session.X3DHHops
