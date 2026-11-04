/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Advantage
public import CatCryptCore.Crypto.Assumptions.DDH
public import CatCryptCore.Tactics.AutoSets

/-!
# X3DH key indistinguishability against a passive adversary

One honest session of the X3DH key agreement between Alice (initiator) and Bob (responder),
and the key-indistinguishability game of a passive adversary, which sees the public keys of the
session and either the session key or a uniform key. The bound of this game in the standard
model, by the advantages of four DDH reductions and one KDF reduction, is
`CatCryptCore.Crypto.AKE.X3DHPassiveHops`. The multi-session statement against an active
adversary, from gap Diffie-Hellman with the KDF as a random oracle, is
`CatCryptCore.Crypto.AKE.X3DHSquareGDH` (`x3dh_realizesSim_gapDH`).

## Protocol

Alice holds the identity key `ik_A` and draws the ephemeral key `ek`; Bob holds the identity key
`ik_B`, the signed prekey `spk_B` and the one-time prekey `opk_B`. The four Diffie-Hellman
values are

1. `DH1 = dh(ik_A, spk_B)`,
2. `DH2 = dh(ek, ik_B)`,
3. `DH3 = dh(ek, spk_B)`,
4. `DH4 = dh(ek, opk_B)`,

and the session key is `SK = KDF(DH1, DH2, DH3, DH4)`. The transcript is the five public keys
`(ik_A, ik_B, ek, spk_B, opk_B)`.

## Main definitions

* `X3DHParams` — a Diffie-Hellman group `DDHDef W` and a KDF `W → W → W → W → W`.
* `x3dh_hyb P dh` — the session whose four KDF inputs are drawn by `dh` from the five key
  pairs; `x3dh_real` and `x3dh_hyb1` … `x3dh_hyb4` are its instances, with the first `i`
  Diffie-Hellman values replaced by uniform samples in `x3dh_hybi`.
* `x3dh_ideal` — the session with a uniform session key.
* `KI_Adversary`, `wrap_hybrid`, `X3DH_KI_Game`, `X3DH_KI_Advantage` — the
  key-indistinguishability game.

## References

* Marlinspike, Perrin — *The X3DH Key Agreement Protocol*, 2016
* Cohn-Gordon, Cremers, Dowling, Garratt, Stebila — *A Formal Security Analysis of the
  Signal Messaging Protocol*, EuroS&P 2017
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.X3DH

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.Assumptions
open scoped ENNReal

variable {W : Type} [SampleableType W]

/-! ## Parameters and keys -/

/-- X3DH parameters: the Diffie-Hellman group of `DDHDef` and a KDF combining the four
Diffie-Hellman values into a session key (`HKDF(DH1 ‖ DH2 ‖ DH3 ‖ DH4)` in the
specification). -/
structure X3DHParams (W : Type) [SampleableType W] where
  /-- The Diffie-Hellman group: key generation and the shared-secret function. -/
  dh : DDHDef W
  /-- The key derivation function on the four Diffie-Hellman values. -/
  kdf : W → W → W → W → W

/-- The transcript of a session: the public keys `(ik_A, ik_B, ek, spk_B, opk_B)`. -/
abbrev X3DHTranscript (W : Type) := W × W × W × W × W

/-! ## Protocol and hybrids -/

/-- The X3DH session with KDF inputs drawn by `dh`: the key pairs `ik_a`, `ik_b`, `spk_b`,
`opk_b`, `ek` drawn by `P.dh.keygen`, the four KDF inputs drawn by `dh` from them, the session
key and the transcript. -/
noncomputable def x3dh_hyb (P : X3DHParams W)
    (dh : W × W → W × W → W × W → W × W → W × W → SPComp (W × W × W × W)) :
    SPComp (W × X3DHTranscript W) :=
  P.dh.keygen.bind fun ik_a => P.dh.keygen.bind fun ik_b =>
  P.dh.keygen.bind fun spk_b => P.dh.keygen.bind fun opk_b =>
  P.dh.keygen.bind fun ek =>
  (dh ik_a ik_b spk_b opk_b ek).bind fun d =>
  SPComp.pure (P.kdf d.1 d.2.1 d.2.2.1 d.2.2.2, (ik_a.2, ik_b.2, ek.2, spk_b.2, opk_b.2))

/-- The honest session: the four Diffie-Hellman values computed on Alice's side. -/
noncomputable def x3dh_real (P : X3DHParams W) : SPComp (W × X3DHTranscript W) :=
  x3dh_hyb P fun ik_a ik_b spk_b opk_b ek =>
    SPComp.pure (P.dh.ecdh ik_a.1 spk_b.2, P.dh.ecdh ek.1 ik_b.2, P.dh.ecdh ek.1 spk_b.2,
      P.dh.ecdh ek.1 opk_b.2)

/-- Hybrid 1: `DH1` replaced by a uniform sample. -/
noncomputable def x3dh_hyb1 (P : X3DHParams W) : SPComp (W × X3DHTranscript W) :=
  x3dh_hyb P fun _ik_a ik_b spk_b opk_b ek =>
    (SPComp.sample W).bind fun r1 =>
    SPComp.pure (r1, P.dh.ecdh ek.1 ik_b.2, P.dh.ecdh ek.1 spk_b.2, P.dh.ecdh ek.1 opk_b.2)

/-- Hybrid 2: `DH1` and `DH2` replaced by uniform samples. -/
noncomputable def x3dh_hyb2 (P : X3DHParams W) : SPComp (W × X3DHTranscript W) :=
  x3dh_hyb P fun _ik_a _ik_b spk_b opk_b ek =>
    (SPComp.sample W).bind fun r1 => (SPComp.sample W).bind fun r2 =>
    SPComp.pure (r1, r2, P.dh.ecdh ek.1 spk_b.2, P.dh.ecdh ek.1 opk_b.2)

/-- Hybrid 3: `DH1`, `DH2` and `DH3` replaced by uniform samples. -/
noncomputable def x3dh_hyb3 (P : X3DHParams W) : SPComp (W × X3DHTranscript W) :=
  x3dh_hyb P fun _ik_a _ik_b _spk_b opk_b ek =>
    (SPComp.sample W).bind fun r1 => (SPComp.sample W).bind fun r2 =>
    (SPComp.sample W).bind fun r3 =>
    SPComp.pure (r1, r2, r3, P.dh.ecdh ek.1 opk_b.2)

/-- Hybrid 4: the four Diffie-Hellman values replaced by uniform samples. -/
noncomputable def x3dh_hyb4 (P : X3DHParams W) : SPComp (W × X3DHTranscript W) :=
  x3dh_hyb P fun _ik_a _ik_b _spk_b _opk_b _ek =>
    (SPComp.sample W).bind fun r1 => (SPComp.sample W).bind fun r2 =>
    (SPComp.sample W).bind fun r3 => (SPComp.sample W).bind fun r4 =>
    SPComp.pure (r1, r2, r3, r4)

/-- The ideal session: the five key pairs and a uniform session key. -/
noncomputable def x3dh_ideal (P : X3DHParams W) : SPComp (W × X3DHTranscript W) :=
  P.dh.keygen.bind fun ik_a => P.dh.keygen.bind fun ik_b =>
  P.dh.keygen.bind fun spk_b => P.dh.keygen.bind fun opk_b =>
  P.dh.keygen.bind fun ek =>
  (SPComp.sample W).bind fun sk => SPComp.pure (sk, (ik_a.2, ik_b.2, ek.2, spk_b.2, opk_b.2))

theorem x3dh_real_isPure (P : X3DHParams W) : SPComp.IsPure (x3dh_real P) := by
  simp only [x3dh_real, x3dh_hyb]
  aesop (rule_sets := [CatCryptRel]) (add safe P.dh.keygen_isPure) (config := { terminal := true })

theorem x3dh_ideal_isPure (P : X3DHParams W) : SPComp.IsPure (x3dh_ideal P) := by
  unfold x3dh_ideal
  aesop (rule_sets := [CatCryptRel]) (add safe P.dh.keygen_isPure) (config := { terminal := true })

/-! ## Key-indistinguishability game -/

/-- A passive adversary: given a key and a transcript, a guess whether the key is the session
key. -/
structure KI_Adversary (P : X3DHParams W) where
  /-- Given `(key, transcript)`, guess whether `key` is the session key. -/
  run : W → X3DHTranscript W → SPComp Bool
  run_isPure : ∀ key tr, SPComp.IsPure (run key tr)

/-- The adversary `A` run on a session drawn by `game`: on the session key when `b`, on a
uniform key otherwise. -/
noncomputable def wrap_hybrid (P : X3DHParams W) (A : KI_Adversary P)
    (game : SPComp (W × X3DHTranscript W)) (b : Bool) : SPComp Bool :=
  game.bind fun p => match b with
  | true => A.run p.1 p.2
  | false => (SPComp.sample W).bind fun k => A.run k p.2

/-- The key-indistinguishability game: the adversary on the honest session, given the session
key (`b = true`) or a uniform key (`b = false`). -/
noncomputable def X3DH_KI_Game (P : X3DHParams W) (A : KI_Adversary P) (b : Bool) :
    SPComp Bool :=
  wrap_hybrid P A (x3dh_real P) b

/-- The key-indistinguishability advantage. -/
noncomputable def X3DH_KI_Advantage (P : X3DHParams W) (A : KI_Adversary P) : ℝ≥0∞ :=
  Advantage (X3DH_KI_Game P A true) (X3DH_KI_Game P A false)

theorem X3DH_KI_Game_isPure (P : X3DHParams W) (A : KI_Adversary P) (b : Bool) :
    SPComp.IsPure (X3DH_KI_Game P A b) := by
  simp only [X3DH_KI_Game, wrap_hybrid, x3dh_real, x3dh_hyb]
  cases b <;>
    aesop (rule_sets := [CatCryptRel]) (add safe P.dh.keygen_isPure, safe A.run_isPure)
      (config := { terminal := true })

end CatCrypt.Crypto.Signal.X3DH
