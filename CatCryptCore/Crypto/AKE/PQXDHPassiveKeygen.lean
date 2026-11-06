/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.PQXDHPassiveHops
public import CatCryptCore.Crypto.Assumptions.DDHSampled

/-!
# PQXDH key indistinguishability with the hybrid values drawn by key generation

The hybrids of `PQXDHPassiveHops` replace a Diffie-Hellman value by a uniform element of `W`.
Here each replaced Diffie-Hellman value is the public part of a fresh key pair of
`P.dh.keygen`, and the KDF game `KDF_Random_RealK` applies the KDF to the public parts of four
fresh key pairs and a uniform KEM input. The KEM hop is that of `PQXDHPassiveHops`; its
replaced value, the KEM shared secret, stays uniform on `W`. Each DDH hop is then an equality
with the DDH advantage `DDH_AdvantageK` whose ideal value is drawn by key generation, and the
last hop an equality with the KDF advantage `KDF_Random_AdvantageK`. When the public part of a
key pair is not uniform on `W` (X25519 on 32-byte strings), these are the advantages of games
whose real and ideal Diffie-Hellman values have the same range.

## The hops

```
pqxdh_real ─ kemRed ─ hyb0 ─ ddhRed1 ─ hybK1 ─ ddhRedK2 ─ hybK2 ─ ddhRedK3 ─ hybK3 ─ ddhRedK4
  ─ hybK4 ─ kdfReduction ─ pqxdh_ideal
```

The reductions are those of `PQXDHPassiveHops`, with the Diffie-Hellman values replaced in the
earlier hops drawn by key generation (`ddhRedK2`, `ddhRedK3`, `ddhRedK4`); `kemRed`, `ddhRed1`
and `kdfReduction` are unchanged.

## Main results

* `hopK1_advantage_eq_ddh` … `hopK5_advantage_eq_kdf` — each DDH and KDF hop is an equality of
  advantages.
* `pqxdh_ki_security_K` — the advantage of `A` between the real and the ideal session is at
  most `pqxdhKIReductionBoundK P A`.
* `pqxdh_advantage_le_K` — for every distinguisher `D` of the key and the transcript, the same
  bound at `kiAdversaryOfDistinguisher P D`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.PQXDHPassive

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.Assumptions
open scoped ENNReal

variable {W PK SK C Sd : Type} [SampleableType W] [SampleableType Sd]

/-! ## Hybrids -/

/-- Hybrid 1 over key generation: as hybrid 0, with `DH1` replaced by the public part of a
fresh key pair. -/
noncomputable def pqxdh_hybK1 (P : PassiveParams W PK SK C Sd) :
    SPComp (W × PQXDHTranscript W PK C) :=
  pqxdh_hyb P (fun _ik_a ik_b spk_b opk_b ek =>
    P.dh.keygen.bind fun r1 =>
    SPComp.pure (r1.2, P.dh.ecdh ek.1 ik_b.2, P.dh.ecdh ek.1 spk_b.2, P.dh.ecdh ek.1 opk_b.2))
    fun _ => SPComp.sample W

/-- Hybrid 2 over key generation: as hybrid 0, with `DH1` and `DH2` replaced. -/
noncomputable def pqxdh_hybK2 (P : PassiveParams W PK SK C Sd) :
    SPComp (W × PQXDHTranscript W PK C) :=
  pqxdh_hyb P (fun _ik_a _ik_b spk_b opk_b ek =>
    P.dh.keygen.bind fun r1 => P.dh.keygen.bind fun r2 =>
    SPComp.pure (r1.2, r2.2, P.dh.ecdh ek.1 spk_b.2, P.dh.ecdh ek.1 opk_b.2))
    fun _ => SPComp.sample W

/-- Hybrid 3 over key generation: as hybrid 0, with `DH1`, `DH2` and `DH3` replaced. -/
noncomputable def pqxdh_hybK3 (P : PassiveParams W PK SK C Sd) :
    SPComp (W × PQXDHTranscript W PK C) :=
  pqxdh_hyb P (fun _ik_a _ik_b _spk_b opk_b ek =>
    P.dh.keygen.bind fun r1 => P.dh.keygen.bind fun r2 => P.dh.keygen.bind fun r3 =>
    SPComp.pure (r1.2, r2.2, r3.2, P.dh.ecdh ek.1 opk_b.2))
    fun _ => SPComp.sample W

/-- Hybrid 4 over key generation: the four Diffie-Hellman values replaced by the public parts
of fresh key pairs and the KEM input uniform. -/
noncomputable def pqxdh_hybK4 (P : PassiveParams W PK SK C Sd) :
    SPComp (W × PQXDHTranscript W PK C) :=
  pqxdh_hyb P (fun _ik_a _ik_b _spk_b _opk_b _ek =>
    P.dh.keygen.bind fun r1 => P.dh.keygen.bind fun r2 =>
    P.dh.keygen.bind fun r3 => P.dh.keygen.bind fun r4 =>
    SPComp.pure (r1.2, r2.2, r3.2, r4.2))
    fun _ => SPComp.sample W

/-! ## The DDH reductions -/

/-- Hop-2 reduction over key generation: the DDH challenge `(g_a, g_b, z)` as
`(ek, ik_B, DH2)`, `DH1` the public part of a fresh key pair, `DH3` and `DH4` on Bob's
side. -/
noncomputable def ddhRedK2 (P : PassiveParams W PK SK C Sd) (A : KI_Adversary P)
    (g_a g_b z : W) : SPComp Bool :=
  P.dh.keygen.bind fun ik_a => P.dh.keygen.bind fun spk_b => P.dh.keygen.bind fun opk_b =>
  P.dh.keygen.bind fun r1 =>
  (SPComp.sample Sd).bind fun sd => (SPComp.sample W).bind fun m =>
  (SPComp.sample W).bind fun k =>
  A.run (P.kdf r1.2 z (P.dh.ecdh spk_b.1 g_a) (P.dh.ecdh opk_b.1 g_a) k)
    (ik_a.2, g_b, g_a, spk_b.2, opk_b.2, (P.kemKeygen sd).1,
      (P.kemEncaps (P.kemKeygen sd).1 m).1)

/-- Hop-3 reduction over key generation: the DDH challenge `(g_a, g_b, z)` as
`(ek, spk_B, DH3)`, `DH4` on Bob's side. -/
noncomputable def ddhRedK3 (P : PassiveParams W PK SK C Sd) (A : KI_Adversary P)
    (g_a g_b z : W) : SPComp Bool :=
  P.dh.keygen.bind fun ik_a => P.dh.keygen.bind fun ik_b => P.dh.keygen.bind fun opk_b =>
  P.dh.keygen.bind fun r1 => P.dh.keygen.bind fun r2 =>
  (SPComp.sample Sd).bind fun sd => (SPComp.sample W).bind fun m =>
  (SPComp.sample W).bind fun k =>
  A.run (P.kdf r1.2 r2.2 z (P.dh.ecdh opk_b.1 g_a) k)
    (ik_a.2, ik_b.2, g_a, g_b, opk_b.2, (P.kemKeygen sd).1,
      (P.kemEncaps (P.kemKeygen sd).1 m).1)

/-- Hop-4 reduction over key generation: the DDH challenge `(g_a, g_b, z)` as
`(ek, opk_B, DH4)`. -/
noncomputable def ddhRedK4 (P : PassiveParams W PK SK C Sd) (A : KI_Adversary P)
    (g_a g_b z : W) : SPComp Bool :=
  P.dh.keygen.bind fun ik_a => P.dh.keygen.bind fun ik_b => P.dh.keygen.bind fun spk_b =>
  P.dh.keygen.bind fun r1 => P.dh.keygen.bind fun r2 => P.dh.keygen.bind fun r3 =>
  (SPComp.sample Sd).bind fun sd => (SPComp.sample W).bind fun m =>
  (SPComp.sample W).bind fun k =>
  A.run (P.kdf r1.2 r2.2 r3.2 z k)
    (ik_a.2, ik_b.2, g_a, spk_b.2, g_b, (P.kemKeygen sd).1,
      (P.kemEncaps (P.kemKeygen sd).1 m).1)

/-- `ddhRedK2` at the public key `pub e`, when key generation returns `(x, pub x)` and `ecdh`
commutes on public keys. -/
theorem ddhRedK2_pub (P : PassiveParams W PK SK C Sd) (A : KI_Adversary P) {pub : W → W}
    (hkg : P.dh.keygen = (SPComp.sample W).bind (fun x => SPComp.pure (x, pub x)))
    (hc : ECDHSym.CommutesOnPub P.dh.ecdh pub) (e g_b z : W) :
    ddhRedK2 P A (pub e) g_b z =
      (SPComp.sample W).bind fun ik_a => (SPComp.sample W).bind fun spk_b =>
      (SPComp.sample W).bind fun opk_b => (SPComp.sample W).bind fun r1 =>
      (SPComp.sample Sd).bind fun sd => (SPComp.sample W).bind fun m =>
      (SPComp.sample W).bind fun k =>
      A.run (P.kdf (pub r1) z (P.dh.ecdh e (pub spk_b)) (P.dh.ecdh e (pub opk_b)) k)
        (pub ik_a, g_b, pub e, pub spk_b, pub opk_b, (P.kemKeygen sd).1,
          (P.kemEncaps (P.kemKeygen sd).1 m).1) := by
  simp only [ddhRedK2, ECDHSym.keygen_bind hkg, hc _ e]

/-- `ddhRedK3` at the public key `pub e`, as `ddhRedK2_pub`. -/
theorem ddhRedK3_pub (P : PassiveParams W PK SK C Sd) (A : KI_Adversary P) {pub : W → W}
    (hkg : P.dh.keygen = (SPComp.sample W).bind (fun x => SPComp.pure (x, pub x)))
    (hc : ECDHSym.CommutesOnPub P.dh.ecdh pub) (e g_b z : W) :
    ddhRedK3 P A (pub e) g_b z =
      (SPComp.sample W).bind fun ik_a => (SPComp.sample W).bind fun ik_b =>
      (SPComp.sample W).bind fun opk_b => (SPComp.sample W).bind fun r1 =>
      (SPComp.sample W).bind fun r2 =>
      (SPComp.sample Sd).bind fun sd => (SPComp.sample W).bind fun m =>
      (SPComp.sample W).bind fun k =>
      A.run (P.kdf (pub r1) (pub r2) z (P.dh.ecdh e (pub opk_b)) k)
        (pub ik_a, pub ik_b, pub e, g_b, pub opk_b, (P.kemKeygen sd).1,
          (P.kemEncaps (P.kemKeygen sd).1 m).1) := by
  simp only [ddhRedK3, ECDHSym.keygen_bind hkg, hc _ e]

/-! ## The KDF assumption over key generation -/

/-- The KDF on the public parts of four fresh key pairs and a uniform KEM input. -/
noncomputable def KDF_Random_RealK (P : PassiveParams W PK SK C Sd) : SPComp W :=
  P.dh.keygen.bind fun r1 => P.dh.keygen.bind fun r2 =>
  P.dh.keygen.bind fun r3 => P.dh.keygen.bind fun r4 =>
  (SPComp.sample W).bind fun k =>
  SPComp.pure (P.kdf r1.2 r2.2 r3.2 r4.2 k)

/-- The advantage of `A` between the KDF on the public parts of four fresh key pairs and a
uniform KEM input, and a uniform key: the KDF as an extractor on the source of key generation
and a uniform KEM secret. -/
noncomputable def KDF_Random_AdvantageK (P : PassiveParams W PK SK C Sd)
    (A : W → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (KDF_Random_RealK P) KDF_Random_Ideal A

/-! ## The hops -/

/-- **Hop 1.** The advantage between hybrid 0 and hybrid 1 is the DDH advantage of `ddhRed1`
with the ideal value drawn by key generation. -/
theorem hopK1_advantage_eq_ddh (P : PassiveParams W PK SK C Sd) (A : KI_Adversary P) :
    Advantage (wrap_hybrid P A (pqxdh_hyb0 P) true) (wrap_hybrid P A (pqxdh_hybK1 P) true) =
    DDH_AdvantageK P.dh (ddhRed1 P A) := by
  advantage_eq_nf [wrap_hybrid, pqxdh_hyb0, pqxdh_hybK1, pqxdh_hyb, realDH, ddhRed1,
    DDH_AdvantageK, DDH_Game_IdealK, DDH_ViewIdealK]

/-- **Hop 2.** The advantage between hybrids 1 and 2 is the DDH advantage of `ddhRedK2`. -/
theorem hopK2_advantage_eq_ddh (P : PassiveParams W PK SK C Sd) (A : KI_Adversary P)
    (h_sym : ECDHSym.ECDHSymmetric P.dh) :
    Advantage (wrap_hybrid P A (pqxdh_hybK1 P) true) (wrap_hybrid P A (pqxdh_hybK2 P) true) =
    DDH_AdvantageK P.dh (ddhRedK2 P A) := by
  obtain ⟨pub, hkg, hc⟩ := h_sym
  simp only [DDH_AdvantageK, DDH_Game_Real, DDH_Game_IdealK, DDH_ViewIdealK, wrap_hybrid,
    pqxdh_hybK1, pqxdh_hybK2, pqxdh_hyb, SPComp.monad_bind_eq, ECDHSym.keygen_bind hkg,
    SPComp.bind_assoc, SPComp.pure_bind, ddhRedK2_pub P A hkg hc]
  advantage_eq_nf

/-- **Hop 3.** The advantage between hybrids 2 and 3 is the DDH advantage of `ddhRedK3`. -/
theorem hopK3_advantage_eq_ddh (P : PassiveParams W PK SK C Sd) (A : KI_Adversary P)
    (h_sym : ECDHSym.ECDHSymmetric P.dh) :
    Advantage (wrap_hybrid P A (pqxdh_hybK2 P) true) (wrap_hybrid P A (pqxdh_hybK3 P) true) =
    DDH_AdvantageK P.dh (ddhRedK3 P A) := by
  obtain ⟨pub, hkg, hc⟩ := h_sym
  simp only [DDH_AdvantageK, DDH_Game_Real, DDH_Game_IdealK, DDH_ViewIdealK, wrap_hybrid,
    pqxdh_hybK2, pqxdh_hybK3, pqxdh_hyb, SPComp.monad_bind_eq, ECDHSym.keygen_bind hkg,
    SPComp.bind_assoc, SPComp.pure_bind, ddhRedK3_pub P A hkg hc]
  advantage_eq_nf

/-- **Hop 4.** The advantage between hybrids 3 and 4 is the DDH advantage of `ddhRedK4`. -/
theorem hopK4_advantage_eq_ddh (P : PassiveParams W PK SK C Sd) (A : KI_Adversary P) :
    Advantage (wrap_hybrid P A (pqxdh_hybK3 P) true) (wrap_hybrid P A (pqxdh_hybK4 P) true) =
    DDH_AdvantageK P.dh (ddhRedK4 P A) := by
  advantage_eq_nf [wrap_hybrid, pqxdh_hybK3, pqxdh_hybK4, pqxdh_hyb, ddhRedK4, DDH_AdvantageK,
    DDH_Game_IdealK, DDH_ViewIdealK]

/-- **Hop 5.** The advantage between hybrid 4 and the ideal session is the KDF advantage of
`kdfReduction` over key generation. -/
theorem hopK5_advantage_eq_kdf (P : PassiveParams W PK SK C Sd) (A : KI_Adversary P) :
    Advantage (wrap_hybrid P A (pqxdh_hybK4 P) true) (wrap_hybrid P A (pqxdh_ideal P) true) =
    KDF_Random_AdvantageK P (kdfReduction P A) := by
  advantage_eq_nf [wrap_hybrid, pqxdh_hybK4, pqxdh_ideal, pqxdh_hyb, kdfReduction,
    KDF_Random_AdvantageK, KDF_Random_RealK, KDF_Random_Ideal]

/-! ## The bound -/

/-- Sum of the advantages of the six reductions built from `A`, the replaced Diffie-Hellman
values drawn by key generation: the KEM advantage of `kemRed`, the DDH advantages
`DDH_AdvantageK` of `ddhRed1`, `ddhRedK2`, `ddhRedK3`, `ddhRedK4` and the KDF advantage
`KDF_Random_AdvantageK` of `kdfReduction`. -/
noncomputable def pqxdhKIReductionBoundK (P : PassiveParams W PK SK C Sd)
    (A : KI_Adversary P) : ℝ≥0∞ :=
  KEM_Advantage P (kemRed P A) + DDH_AdvantageK P.dh (ddhRed1 P A) +
    DDH_AdvantageK P.dh (ddhRedK2 P A) + DDH_AdvantageK P.dh (ddhRedK3 P A) +
    DDH_AdvantageK P.dh (ddhRedK4 P A) + KDF_Random_AdvantageK P (kdfReduction P A)

/-- **PQXDH key indistinguishability over key generation.** When key generation returns pairs
`(x, pub x)` and `ecdh` commutes on public keys, the advantage of `A` between the real and the
ideal session is at most `pqxdhKIReductionBoundK P A`. -/
theorem pqxdh_ki_security_K (P : PassiveParams W PK SK C Sd) (A : KI_Adversary P)
    (h_sym : ECDHSym.ECDHSymmetric P.dh) :
    Advantage (wrap_hybrid P A (pqxdh_real P) true) (wrap_hybrid P A (pqxdh_ideal P) true) ≤
      pqxdhKIReductionBoundK P A := by
  have h0 := (hop0_advantage_eq_kem P A).le
  have h1 := (hopK1_advantage_eq_ddh P A).le
  have h2 := (hopK2_advantage_eq_ddh P A h_sym).le
  have h3 := (hopK3_advantage_eq_ddh P A h_sym).le
  have h4 := (hopK4_advantage_eq_ddh P A).le
  have h5 := (hopK5_advantage_eq_kdf P A).le
  unfold pqxdhKIReductionBoundK
  hop_chain

/-- **PQXDH against a distinguisher of the key and the transcript, over key generation.** For
every `D`, the advantage of `D` between the real and the ideal session is at most
`pqxdhKIReductionBoundK` at `kiAdversaryOfDistinguisher P D`. -/
theorem pqxdh_advantage_le_K (P : PassiveParams W PK SK C Sd)
    (h_sym : ECDHSym.ECDHSymmetric P.dh) (D : W × PQXDHTranscript W PK C → SPComp Bool) :
    AdvantageA (pqxdh_real P) (pqxdh_ideal P) D ≤
      pqxdhKIReductionBoundK P (kiAdversaryOfDistinguisher P D) := by
  have hA := pqxdh_ki_security_K P (kiAdversaryOfDistinguisher P D) h_sym
  rw [wrap_hybrid_kiAdversaryOfDistinguisher, wrap_hybrid_kiAdversaryOfDistinguisher] at hA
  unfold AdvantageA Advantage
  unfold Advantage at hA
  rwa [← prTrue_bind_freeze_eq (pqxdh_real_isPure P) D,
    ← prTrue_bind_freeze_eq (pqxdh_ideal_isPure P) D] at hA

end CatCrypt.Crypto.Signal.PQXDHPassive
