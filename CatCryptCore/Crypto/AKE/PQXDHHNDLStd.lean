/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.PQXDHPassiveHops
public import CatCryptCore.Crypto.Messaging.TripleRatchet
import CatCryptCore.Tactics.BindSwap
import CatCryptCore.Tactics.AutoArms

/-!
# PQXDH against harvest-now-decrypt-later adversaries, one session, standard model

The single-session statement of PQXDH against an adversary that knows every Diffie-Hellman
secret, in the form of Bhargavan, Jacomme, Kiefer and Schmidt (Theorem 3): the adversary
receives the session key or a uniform key, the transcript, and the five Diffie-Hellman secret
keys `ik_A, ik_B, spk_B, opk_B, ek`, so that it knows the four Diffie-Hellman values. Its
advantage is at most the real-or-random advantage of the KEM against `hndlKemRed` plus the PRF
advantage of the key derivation, keyed by its fifth argument (the KEM secret), against
`hndlPrfRed` (`pqxdh_hndl_std_le`). No Diffie-Hellman assumption enters the bound.

## The hops

```
hndl_real ─ hndlKemRed ─ hndl_hyb0 ─ hndlPrfRed ─ hndl_ideal
```

Hop 0 replaces the encapsulated secret by a uniform sample, as hop 0 of
`CatCryptCore.Crypto.AKE.PQXDHPassiveHops`: the reduction `hndlKemRed` receives the public key,
the encapsulation and the challenge secret of the KEM game `KEM_Game_Real`/`KEM_Game_Ideal`,
draws the five key pairs and gives their secrets to the adversary.

Hop 1 replaces `KDF(DH1, DH2, DH3, DH4, k)` at a uniform `k` by a uniform key: the KDF as a PRF
keyed by its KEM input (`DualPRF_Right_Advantage`), queried once at the four Diffie-Hellman
values. The reduction `hndlPrfRed` is a one-query oracle adversary (`oneQueryAdv`).

## Main results

* `hop0_hndl_advantage_eq_kem`, `hop1_hndl_advantage_eq_prf` — the two hops, equalities.
* `pqxdh_hndl_std_le` — the bound.

## References

* Bhargavan, Jacomme, Kiefer, Schmidt — *Formal verification of the PQXDH Post-Quantum key
  agreement protocol for end-to-end secure messaging*, USENIX Security 2024
* Kret, Schmidt — *The PQXDH Key Agreement Protocol*, Signal, 2023
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.PQXDHPassive

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.Assumptions CatCrypt.Crypto.PRPPRF CatCrypt.Crypto.Messaging
open scoped ENNReal

variable {W PK SK C Sd : Type} [SampleableType W] [SampleableType Sd]

/-! ## The game -/

/-- The view of a harvest-now-decrypt-later adversary: the five Diffie-Hellman secret keys
`(ik_A, ik_B, spk_B, opk_B, ek)` and the transcript. -/
abbrev HNDLView (W PK C : Type) := (W × W × W × W × W) × PQXDHTranscript W PK C

/-- A harvest-now-decrypt-later adversary: a distinguisher of a key and the view. -/
abbrev HNDLAdversary (W PK C : Type) := W → HNDLView W PK C → SPComp Bool

/-- The session with the Diffie-Hellman secrets in the view, the KEM secret passed through
`ss`: the key `KDF(DH1, DH2, DH3, DH4, k)` and the view. -/
noncomputable def hndl_hyb (P : PassiveParams W PK SK C Sd) (ss : W → SPComp W) :
    SPComp (W × HNDLView W PK C) :=
  P.dh.keygen.bind fun ik_a => P.dh.keygen.bind fun ik_b =>
  P.dh.keygen.bind fun spk_b => P.dh.keygen.bind fun opk_b =>
  P.dh.keygen.bind fun ek =>
  (SPComp.sample Sd).bind fun sd => (SPComp.sample W).bind fun m =>
  (ss (P.kemEncaps (P.kemKeygen sd).1 m).2).bind fun k =>
  SPComp.pure (P.kdf (P.dh.ecdh ik_a.1 spk_b.2) (P.dh.ecdh ek.1 ik_b.2)
      (P.dh.ecdh ek.1 spk_b.2) (P.dh.ecdh ek.1 opk_b.2) k,
    ((ik_a.1, ik_b.1, spk_b.1, opk_b.1, ek.1),
      (ik_a.2, ik_b.2, ek.2, spk_b.2, opk_b.2, (P.kemKeygen sd).1,
        (P.kemEncaps (P.kemKeygen sd).1 m).1)))

/-- The real session: the key derived from the encapsulated secret. -/
noncomputable def hndl_real (P : PassiveParams W PK SK C Sd) : SPComp (W × HNDLView W PK C) :=
  hndl_hyb P SPComp.pure

/-- Hybrid 0: the key derived from a uniform KEM input. -/
noncomputable def hndl_hyb0 (P : PassiveParams W PK SK C Sd) : SPComp (W × HNDLView W PK C) :=
  hndl_hyb P fun _ => SPComp.sample W

/-- The ideal session: a uniform key with the view of the real session. -/
noncomputable def hndl_ideal (P : PassiveParams W PK SK C Sd) :
    SPComp (W × HNDLView W PK C) :=
  P.dh.keygen.bind fun ik_a => P.dh.keygen.bind fun ik_b =>
  P.dh.keygen.bind fun spk_b => P.dh.keygen.bind fun opk_b =>
  P.dh.keygen.bind fun ek =>
  (SPComp.sample Sd).bind fun sd => (SPComp.sample W).bind fun m =>
  (SPComp.sample W).bind fun sk =>
  SPComp.pure (sk, ((ik_a.1, ik_b.1, spk_b.1, opk_b.1, ek.1),
    (ik_a.2, ik_b.2, ek.2, spk_b.2, opk_b.2, (P.kemKeygen sd).1,
      (P.kemEncaps (P.kemKeygen sd).1 m).1)))

/-- The adversary `A` on a session. -/
noncomputable def hndlGame (A : HNDLAdversary W PK C) (game : SPComp (W × HNDLView W PK C)) :
    SPComp Bool :=
  game.bind fun p => A p.1 p.2

/-! ## The reductions -/

/-- Hop-0 reduction: the KEM challenge `(pk, ct, k)` as the public key, the encapsulation and
the KEM input of the KDF; the five key pairs drawn by the reduction, their secrets given to
`A`. -/
noncomputable def hndlKemRed (P : PassiveParams W PK SK C Sd) (A : HNDLAdversary W PK C)
    (pk : PK) (ct : C) (k : W) : SPComp Bool :=
  P.dh.keygen.bind fun ik_a => P.dh.keygen.bind fun ik_b =>
  P.dh.keygen.bind fun spk_b => P.dh.keygen.bind fun opk_b =>
  P.dh.keygen.bind fun ek =>
  A (P.kdf (P.dh.ecdh ik_a.1 spk_b.2) (P.dh.ecdh ek.1 ik_b.2) (P.dh.ecdh ek.1 spk_b.2)
      (P.dh.ecdh ek.1 opk_b.2) k)
    ((ik_a.1, ik_b.1, spk_b.1, opk_b.1, ek.1), (ik_a.2, ik_b.2, ek.2, spk_b.2, opk_b.2, pk, ct))

/-- The key derivation as a function of the four Diffie-Hellman values and the KEM input. -/
def kdfKem (P : PassiveParams W PK SK C Sd) (d : W × W × W × W) (k : W) : W :=
  P.kdf d.1 d.2.1 d.2.2.1 d.2.2.2 k

/-- The randomness of a session before its key: five key pairs, the KEM seed and the KEM
message. -/
noncomputable def hndlPre (P : PassiveParams W PK SK C Sd) :
    SPComp ((W × W) × (W × W) × (W × W) × (W × W) × (W × W) × Sd × W) :=
  P.dh.keygen.bind fun ik_a => P.dh.keygen.bind fun ik_b =>
  P.dh.keygen.bind fun spk_b => P.dh.keygen.bind fun opk_b =>
  P.dh.keygen.bind fun ek =>
  (SPComp.sample Sd).bind fun sd => (SPComp.sample W).bind fun m =>
  SPComp.pure (ik_a, ik_b, spk_b, opk_b, ek, sd, m)

/-- The four Diffie-Hellman values of the session randomness `x`. -/
def hndlDH (P : PassiveParams W PK SK C Sd)
    (x : (W × W) × (W × W) × (W × W) × (W × W) × (W × W) × Sd × W) : W × W × W × W :=
  (P.dh.ecdh x.1.1 x.2.2.1.2, P.dh.ecdh x.2.2.2.2.1.1 x.2.1.2,
    P.dh.ecdh x.2.2.2.2.1.1 x.2.2.1.2, P.dh.ecdh x.2.2.2.2.1.1 x.2.2.2.1.2)

/-- The view of the session randomness `x`. -/
def hndlViewOf (P : PassiveParams W PK SK C Sd)
    (x : (W × W) × (W × W) × (W × W) × (W × W) × (W × W) × Sd × W) : HNDLView W PK C :=
  ((x.1.1, x.2.1.1, x.2.2.1.1, x.2.2.2.1.1, x.2.2.2.2.1.1),
    (x.1.2, x.2.1.2, x.2.2.2.2.1.2, x.2.2.1.2, x.2.2.2.1.2, (P.kemKeygen x.2.2.2.2.2.1).1,
      (P.kemEncaps (P.kemKeygen x.2.2.2.2.2.1).1 x.2.2.2.2.2.2).1))

/-- Hop-1 reduction: a one-query adversary against the KDF keyed by its KEM input. It draws the
session randomness, queries the four Diffie-Hellman values and runs `A` on the answer and the
view. -/
noncomputable def hndlPrfRed (P : PassiveParams W PK SK C Sd) (A : HNDLAdversary W PK C) :
    OracleAdv (W × W × W × W) W Bool :=
  oneQueryAdv (hndlPre P) (hndlDH P) fun x y => A y (hndlViewOf P x)

/-! ## The hops -/

/-- **Hop 0.** The advantage between the real session and hybrid 0 is the KEM advantage of
`hndlKemRed`. -/
theorem hop0_hndl_advantage_eq_kem (P : PassiveParams W PK SK C Sd) (A : HNDLAdversary W PK C) :
    Advantage (hndlGame A (hndl_real P)) (hndlGame A (hndl_hyb0 P)) =
      KEM_Advantage P (hndlKemRed P A) := by
  advantage_eq_nf [hndlGame, hndl_real, hndl_hyb0, hndl_hyb, hndlKemRed,
    KEM_Advantage, KEM_Game_Real, KEM_Game_Ideal]

/-- **Hop 1.** The advantage between hybrid 0 and the ideal session is the PRF advantage of the
KDF keyed by its KEM input against `hndlPrfRed`. -/
theorem hop1_hndl_advantage_eq_prf (P : PassiveParams W PK SK C Sd) (A : HNDLAdversary W PK C) :
    Advantage (hndlGame A (hndl_hyb0 P)) (hndlGame A (hndl_ideal P)) =
      DualPRF_Right_Advantage (kdfKem P) (hndlPrfRed P A) := by
  unfold DualPRF_Right_Advantage hndlPrfRed
  rw [← advantage_oneQuery_eq]
  simp only [hndlGame, hndl_hyb0, hndl_hyb, hndl_ideal, hndlPre, SPComp.bind_assoc,
    SPComp.pure_bind]
  rfl

/-! ## The bound -/

/-- **PQXDH against harvest-now-decrypt-later adversaries, one session, standard model.** For
every adversary `A` that receives the five Diffie-Hellman secrets with the transcript, its
advantage between the real and the ideal session is at most the KEM advantage of
`hndlKemRed P A` plus the PRF advantage of the KDF keyed by its KEM input against
`hndlPrfRed P A`. -/
theorem pqxdh_hndl_std_le (P : PassiveParams W PK SK C Sd) (A : HNDLAdversary W PK C) :
    Advantage (hndlGame A (hndl_real P)) (hndlGame A (hndl_ideal P)) ≤
      KEM_Advantage P (hndlKemRed P A) + DualPRF_Right_Advantage (kdfKem P) (hndlPrfRed P A) := by
  have h0 := (hop0_hndl_advantage_eq_kem P A).le
  have h1 := (hop1_hndl_advantage_eq_prf P A).le
  hop_chain

end CatCrypt.Crypto.Signal.PQXDHPassive
