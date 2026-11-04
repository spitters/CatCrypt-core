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
# PQXDH key indistinguishability against a passive adversary

One honest session of the PQXDH key agreement between Alice (initiator) and Bob (responder),
and the key-indistinguishability game of a passive adversary, which sees the public values of
the session and either the session key or a uniform key. The bound of this game in the standard
model, by the advantage of one KEM reduction, four DDH reductions and one KDF reduction, is
`CatCryptCore.Crypto.AKE.PQXDHPassiveHops`. The multi-session statement against an active
adversary, with the KDF as a random oracle, is `CatCryptCore.Crypto.AKE.PQXDHSquare` and its
hops.

## Protocol

PQXDH is X3DH (`CatCryptCore.Crypto.AKE.X3DHPassive`) with a post-quantum prekey. Bob holds
besides `ik_B`, `spk_B` and `opk_B` a KEM key pair `(pk, sk)` generated from a seed; Alice
encapsulates to `pk` with a uniform message `m`, obtaining `(ct, ss)`. The KEM is given by
deterministic functions of its randomness, the form of FIPS 203. The session key is
`SK = KDF(DH1, DH2, DH3, DH4, ss)` with the four Diffie-Hellman values of X3DH, and the
transcript is the five public Diffie-Hellman keys, `pk` and `ct`.

## Main definitions

* `PassiveParams` — a Diffie-Hellman group `DDHDef W`, a KEM on seeds `Sd` with public keys
  `PK`, secret keys `SK`, encapsulations `C` and shared secrets in `W`, and a KDF of five
  arguments.
* `pqxdh_hyb P dh ss` — the session whose four Diffie-Hellman inputs are drawn by `dh` from the
  five key pairs and whose KEM input is drawn by `ss` from the encapsulated secret;
  `pqxdh_real`, `pqxdh_hyb0` … `pqxdh_hyb4` are its instances.
* `pqxdh_ideal` — the session with a uniform session key.
* `KI_Adversary`, `wrap_hybrid`, `PQXDH_KI_Game`, `PQXDH_KI_Advantage` — the
  key-indistinguishability game.

## References

* Kret, Schmidt — *The PQXDH Key Agreement Protocol*, Signal, 2023
* Bhargavan, Jacomme, Kiefer, Schmidt — *Formal verification of the PQXDH Post-Quantum key
  agreement protocol for end-to-end secure messaging*, USENIX Security 2024
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.PQXDHPassive

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.Assumptions
open scoped ENNReal

variable {W PK SK C Sd : Type} [SampleableType W] [SampleableType Sd]

/-! ## Parameters -/

/-- PQXDH parameters: the Diffie-Hellman group of `DDHDef`, a KEM as deterministic functions of
its randomness (key generation from a seed `Sd`, encapsulation from a message `W` returning the
encapsulation and the shared secret, decapsulation), and a KDF of the four Diffie-Hellman
values and the KEM shared secret. -/
structure PassiveParams (W PK SK C Sd : Type) [SampleableType W] where
  /-- The Diffie-Hellman group: key generation and the shared-secret function. -/
  dh : DDHDef W
  /-- KEM key generation from a seed: `(pk, sk)`. -/
  kemKeygen : Sd → PK × SK
  /-- KEM encapsulation to `pk` with the message `m`: `(ct, ss)`. -/
  kemEncaps : PK → W → C × W
  /-- KEM decapsulation. -/
  kemDecaps : SK → C → W
  /-- The key derivation function on the four Diffie-Hellman values and the KEM secret. -/
  kdf : W → W → W → W → W → W

/-- Correctness of the KEM: decapsulation recovers the encapsulated secret for every seed and
message. -/
def PassiveParams.KemCorrect (P : PassiveParams W PK SK C Sd) : Prop :=
  ∀ (sd : Sd) (m : W),
    P.kemDecaps (P.kemKeygen sd).2 (P.kemEncaps (P.kemKeygen sd).1 m).1 =
      (P.kemEncaps (P.kemKeygen sd).1 m).2

/-- The transcript of a session: `(ik_A, ik_B, ek, spk_B, opk_B, pk, ct)`. -/
abbrev PQXDHTranscript (W PK C : Type) := W × W × W × W × W × PK × C

/-! ## Protocol and hybrids -/

/-- The PQXDH session with KDF inputs drawn by `dh` and `ss`: the key pairs `ik_a`, `ik_b`,
`spk_b`, `opk_b`, `ek` drawn by `P.dh.keygen`, the KEM seed and message drawn uniformly, the KEM
input drawn by `ss` from the encapsulated secret, the four Diffie-Hellman inputs drawn by `dh`,
the session key and the transcript. -/
noncomputable def pqxdh_hyb (P : PassiveParams W PK SK C Sd)
    (dh : W × W → W × W → W × W → W × W → W × W → SPComp (W × W × W × W))
    (ss : W → SPComp W) : SPComp (W × PQXDHTranscript W PK C) :=
  P.dh.keygen.bind fun ik_a => P.dh.keygen.bind fun ik_b =>
  P.dh.keygen.bind fun spk_b => P.dh.keygen.bind fun opk_b =>
  P.dh.keygen.bind fun ek =>
  (SPComp.sample Sd).bind fun sd => (SPComp.sample W).bind fun m =>
  (ss (P.kemEncaps (P.kemKeygen sd).1 m).2).bind fun k =>
  (dh ik_a ik_b spk_b opk_b ek).bind fun d =>
  SPComp.pure (P.kdf d.1 d.2.1 d.2.2.1 d.2.2.2 k,
    (ik_a.2, ik_b.2, ek.2, spk_b.2, opk_b.2, (P.kemKeygen sd).1,
      (P.kemEncaps (P.kemKeygen sd).1 m).1))

/-- The four Diffie-Hellman values computed on Alice's side. -/
noncomputable def realDH (P : PassiveParams W PK SK C Sd) (ik_a ik_b spk_b opk_b ek : W × W) :
    SPComp (W × W × W × W) :=
  SPComp.pure (P.dh.ecdh ik_a.1 spk_b.2, P.dh.ecdh ek.1 ik_b.2, P.dh.ecdh ek.1 spk_b.2,
    P.dh.ecdh ek.1 opk_b.2)

/-- The honest session: the four Diffie-Hellman values on Alice's side and the encapsulated
secret. -/
noncomputable def pqxdh_real (P : PassiveParams W PK SK C Sd) :
    SPComp (W × PQXDHTranscript W PK C) :=
  pqxdh_hyb P (realDH P) SPComp.pure

/-- Hybrid 0: the encapsulated secret replaced by a uniform sample. -/
noncomputable def pqxdh_hyb0 (P : PassiveParams W PK SK C Sd) :
    SPComp (W × PQXDHTranscript W PK C) :=
  pqxdh_hyb P (realDH P) fun _ => SPComp.sample W

/-- Hybrid 1: as hybrid 0, with `DH1` replaced by a uniform sample. -/
noncomputable def pqxdh_hyb1 (P : PassiveParams W PK SK C Sd) :
    SPComp (W × PQXDHTranscript W PK C) :=
  pqxdh_hyb P (fun _ik_a ik_b spk_b opk_b ek =>
    (SPComp.sample W).bind fun r1 =>
    SPComp.pure (r1, P.dh.ecdh ek.1 ik_b.2, P.dh.ecdh ek.1 spk_b.2, P.dh.ecdh ek.1 opk_b.2))
    fun _ => SPComp.sample W

/-- Hybrid 2: as hybrid 0, with `DH1` and `DH2` replaced by uniform samples. -/
noncomputable def pqxdh_hyb2 (P : PassiveParams W PK SK C Sd) :
    SPComp (W × PQXDHTranscript W PK C) :=
  pqxdh_hyb P (fun _ik_a _ik_b spk_b opk_b ek =>
    (SPComp.sample W).bind fun r1 => (SPComp.sample W).bind fun r2 =>
    SPComp.pure (r1, r2, P.dh.ecdh ek.1 spk_b.2, P.dh.ecdh ek.1 opk_b.2))
    fun _ => SPComp.sample W

/-- Hybrid 3: as hybrid 0, with `DH1`, `DH2` and `DH3` replaced by uniform samples. -/
noncomputable def pqxdh_hyb3 (P : PassiveParams W PK SK C Sd) :
    SPComp (W × PQXDHTranscript W PK C) :=
  pqxdh_hyb P (fun _ik_a _ik_b _spk_b opk_b ek =>
    (SPComp.sample W).bind fun r1 => (SPComp.sample W).bind fun r2 =>
    (SPComp.sample W).bind fun r3 =>
    SPComp.pure (r1, r2, r3, P.dh.ecdh ek.1 opk_b.2))
    fun _ => SPComp.sample W

/-- Hybrid 4: the five KDF inputs replaced by uniform samples. -/
noncomputable def pqxdh_hyb4 (P : PassiveParams W PK SK C Sd) :
    SPComp (W × PQXDHTranscript W PK C) :=
  pqxdh_hyb P (fun _ik_a _ik_b _spk_b _opk_b _ek =>
    (SPComp.sample W).bind fun r1 => (SPComp.sample W).bind fun r2 =>
    (SPComp.sample W).bind fun r3 => (SPComp.sample W).bind fun r4 =>
    SPComp.pure (r1, r2, r3, r4))
    fun _ => SPComp.sample W

/-- The ideal session: the five key pairs, the KEM seed and message, and a uniform session
key. -/
noncomputable def pqxdh_ideal (P : PassiveParams W PK SK C Sd) :
    SPComp (W × PQXDHTranscript W PK C) :=
  P.dh.keygen.bind fun ik_a => P.dh.keygen.bind fun ik_b =>
  P.dh.keygen.bind fun spk_b => P.dh.keygen.bind fun opk_b =>
  P.dh.keygen.bind fun ek =>
  (SPComp.sample Sd).bind fun sd => (SPComp.sample W).bind fun m =>
  (SPComp.sample W).bind fun sk =>
  SPComp.pure (sk, (ik_a.2, ik_b.2, ek.2, spk_b.2, opk_b.2, (P.kemKeygen sd).1,
    (P.kemEncaps (P.kemKeygen sd).1 m).1))

theorem pqxdh_real_isPure (P : PassiveParams W PK SK C Sd) : SPComp.IsPure (pqxdh_real P) := by
  simp only [pqxdh_real, pqxdh_hyb, realDH]
  aesop (rule_sets := [CatCryptRel]) (add safe P.dh.keygen_isPure) (config := { terminal := true })

theorem pqxdh_ideal_isPure (P : PassiveParams W PK SK C Sd) :
    SPComp.IsPure (pqxdh_ideal P) := by
  unfold pqxdh_ideal
  aesop (rule_sets := [CatCryptRel]) (add safe P.dh.keygen_isPure) (config := { terminal := true })

/-! ## Key-indistinguishability game -/

/-- A passive adversary: given a key and a transcript, a guess whether the key is the session
key. -/
structure KI_Adversary (P : PassiveParams W PK SK C Sd) where
  /-- Given `(key, transcript)`, guess whether `key` is the session key. -/
  run : W → PQXDHTranscript W PK C → SPComp Bool
  run_isPure : ∀ key tr, SPComp.IsPure (run key tr)

/-- The adversary `A` run on a session drawn by `game`: on the session key when `b`, on a
uniform key otherwise. -/
noncomputable def wrap_hybrid (P : PassiveParams W PK SK C Sd) (A : KI_Adversary P)
    (game : SPComp (W × PQXDHTranscript W PK C)) (b : Bool) : SPComp Bool :=
  game.bind fun p => match b with
  | true => A.run p.1 p.2
  | false => (SPComp.sample W).bind fun k => A.run k p.2

/-- The key-indistinguishability game: the adversary on the honest session, given the session
key (`b = true`) or a uniform key (`b = false`). -/
noncomputable def PQXDH_KI_Game (P : PassiveParams W PK SK C Sd) (A : KI_Adversary P)
    (b : Bool) : SPComp Bool :=
  wrap_hybrid P A (pqxdh_real P) b

/-- The key-indistinguishability advantage. -/
noncomputable def PQXDH_KI_Advantage (P : PassiveParams W PK SK C Sd) (A : KI_Adversary P) :
    ℝ≥0∞ :=
  Advantage (PQXDH_KI_Game P A true) (PQXDH_KI_Game P A false)

end CatCrypt.Crypto.Signal.PQXDHPassive
