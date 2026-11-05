/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.PQXDHPassive
public import CatCryptCore.Crypto.AKE.X3DHPassiveHops
public import CatCryptCore.Tactics.BindSwap
public import CatCryptCore.Tactics.AutoArms

/-!
# PQXDH key indistinguishability from a KEM, DDH and a KDF assumption

The passive single-session statement of PQXDH in the standard model: the
key-indistinguishability advantage of an adversary `A` (`PQXDHPassive`) is at most the
real-or-random advantage of one KEM reduction, the DDH advantages of four reductions and the KDF
advantage of one reduction, all built from `A` (`PQXDH_KI_Advantage_from_assumptions`).

## The hops

```
pqxdh_real ─ kemRed ─ hyb0 ─ ddhRed1 ─ hyb1 ─ ddhRed2 ─ hyb2 ─ ddhRed3 ─ hyb3 ─ ddhRed4
  ─ hyb4 ─ kdfReduction ─ pqxdh_ideal
```

Hop 0 replaces the encapsulated secret by a uniform sample; its reduction `kemRed` receives the
public key, the encapsulation and the challenge secret of the KEM game, draws the five key
pairs and computes the four Diffie-Hellman values itself.

Hop `i` for `1 ≤ i ≤ 4` replaces `DHi` by a uniform sample, as in
`CatCryptCore.Crypto.AKE.X3DHPassiveHops`; its reduction `ddhRedi` embeds the DDH challenge
`(g_a, g_b, z)` as the two public keys of `DHi` and `z` as `DHi`, draws the other key pairs, the
KEM seed and message and the uniform KEM input itself. `ddhRed2` and `ddhRed3` compute the
remaining Diffie-Hellman values with `ek` on Bob's side, which equal Alice's values when key
generation returns pairs `(x, pub x)` and `ecdh` commutes on public keys
(`ECDHSym.ECDHSymmetric`).

Hop 5 replaces `KDF(r1, r2, r3, r4, r5)` on uniform inputs by a uniform key; its reduction
`kdfReduction` draws the key pairs, the KEM seed and message, and runs `A` on the challenge key.

Each hop is an equality of advantages, and the bound is the triangle inequality along the chain.
The bound is a sum over both the KEM and the Diffie-Hellman hops; the statement in which either
the KEM or the Diffie-Hellman route alone bounds a session, with the KDF as a random oracle, is
`CatCryptCore.Crypto.AKE.PQXDHSquareKEM` (`pqxdh_realizesSim_min`).

## Main results

* `pqxdh_ki_security_from_assumptions` — the advantage of `A` between the real and the ideal
  session is at most `pqxdhKIReductionBound P A`.
* `PQXDH_KI_Advantage_from_assumptions` — the same bound for `PQXDH_KI_Advantage`.
* `pqxdh_advantage_le` — for every distinguisher `D` of the key and the transcript, the same
  bound at the adversary `kiAdversaryOfDistinguisher P D`.

## References

* Kret, Schmidt — *The PQXDH Key Agreement Protocol*, Signal, 2023
* Krawczyk — *Cryptographic Extraction and Key Derivation: The HKDF Scheme*, CRYPTO 2010
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.PQXDHPassive

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.Assumptions
open scoped ENNReal

variable {W PK SK C Sd : Type} [SampleableType W] [SampleableType Sd]

/-! ## The KEM assumption -/

/-- The KEM game with the encapsulated secret: a uniform seed and message, and the adversary on
the public key, the encapsulation and its secret. -/
noncomputable def KEM_Game_Real (P : PassiveParams W PK SK C Sd)
    (A : PK → C → W → SPComp Bool) : SPComp Bool :=
  (SPComp.sample Sd).bind fun sd => (SPComp.sample W).bind fun m =>
  A (P.kemKeygen sd).1 (P.kemEncaps (P.kemKeygen sd).1 m).1 (P.kemEncaps (P.kemKeygen sd).1 m).2

/-- The KEM game with a uniform secret. -/
noncomputable def KEM_Game_Ideal (P : PassiveParams W PK SK C Sd)
    (A : PK → C → W → SPComp Bool) : SPComp Bool :=
  (SPComp.sample Sd).bind fun sd => (SPComp.sample W).bind fun m =>
  (SPComp.sample W).bind fun k =>
  A (P.kemKeygen sd).1 (P.kemEncaps (P.kemKeygen sd).1 m).1 k

/-- The real-or-random advantage of `A` against the KEM: the IND-CPA advantage of the KEM in
the form of Hofheinz, Hövelmanns and Kiltz (TCC 2017) for a KEM given by deterministic
functions of uniform randomness. -/
noncomputable def KEM_Advantage (P : PassiveParams W PK SK C Sd)
    (A : PK → C → W → SPComp Bool) : ℝ≥0∞ :=
  Advantage (KEM_Game_Real P A) (KEM_Game_Ideal P A)

/-! ## The reductions -/

/-- Hop-0 reduction: the KEM challenge `(pk, ct, k)` as the public key, the encapsulation and
the KEM input of the KDF. -/
noncomputable def kemRed (P : PassiveParams W PK SK C Sd) (A : KI_Adversary P) (pk : PK)
    (ct : C) (k : W) : SPComp Bool :=
  P.dh.keygen.bind fun ik_a => P.dh.keygen.bind fun ik_b =>
  P.dh.keygen.bind fun spk_b => P.dh.keygen.bind fun opk_b =>
  P.dh.keygen.bind fun ek =>
  A.run (P.kdf (P.dh.ecdh ik_a.1 spk_b.2) (P.dh.ecdh ek.1 ik_b.2) (P.dh.ecdh ek.1 spk_b.2)
      (P.dh.ecdh ek.1 opk_b.2) k)
    (ik_a.2, ik_b.2, ek.2, spk_b.2, opk_b.2, pk, ct)

/-- Hop-1 reduction: the DDH challenge `(g_a, g_b, z)` as `(ik_A, spk_B, DH1)`. -/
noncomputable def ddhRed1 (P : PassiveParams W PK SK C Sd) (A : KI_Adversary P)
    (g_a g_b z : W) : SPComp Bool :=
  P.dh.keygen.bind fun ik_b => P.dh.keygen.bind fun opk_b => P.dh.keygen.bind fun ek =>
  (SPComp.sample Sd).bind fun sd => (SPComp.sample W).bind fun m =>
  (SPComp.sample W).bind fun k =>
  A.run (P.kdf z (P.dh.ecdh ek.1 ik_b.2) (P.dh.ecdh ek.1 g_b) (P.dh.ecdh ek.1 opk_b.2) k)
    (g_a, ik_b.2, ek.2, g_b, opk_b.2, (P.kemKeygen sd).1, (P.kemEncaps (P.kemKeygen sd).1 m).1)

/-- Hop-2 reduction: the DDH challenge `(g_a, g_b, z)` as `(ek, ik_B, DH2)`, with `DH3` and
`DH4` on Bob's side. -/
noncomputable def ddhRed2 (P : PassiveParams W PK SK C Sd) (A : KI_Adversary P)
    (g_a g_b z : W) : SPComp Bool :=
  P.dh.keygen.bind fun ik_a => P.dh.keygen.bind fun spk_b => P.dh.keygen.bind fun opk_b =>
  (SPComp.sample Sd).bind fun sd => (SPComp.sample W).bind fun m =>
  (SPComp.sample W).bind fun k => (SPComp.sample W).bind fun r1 =>
  A.run (P.kdf r1 z (P.dh.ecdh spk_b.1 g_a) (P.dh.ecdh opk_b.1 g_a) k)
    (ik_a.2, g_b, g_a, spk_b.2, opk_b.2, (P.kemKeygen sd).1,
      (P.kemEncaps (P.kemKeygen sd).1 m).1)

/-- Hop-3 reduction: the DDH challenge `(g_a, g_b, z)` as `(ek, spk_B, DH3)`, with `DH4` on
Bob's side. -/
noncomputable def ddhRed3 (P : PassiveParams W PK SK C Sd) (A : KI_Adversary P)
    (g_a g_b z : W) : SPComp Bool :=
  P.dh.keygen.bind fun ik_a => P.dh.keygen.bind fun ik_b => P.dh.keygen.bind fun opk_b =>
  (SPComp.sample Sd).bind fun sd => (SPComp.sample W).bind fun m =>
  (SPComp.sample W).bind fun k => (SPComp.sample W).bind fun r1 =>
  (SPComp.sample W).bind fun r2 =>
  A.run (P.kdf r1 r2 z (P.dh.ecdh opk_b.1 g_a) k)
    (ik_a.2, ik_b.2, g_a, g_b, opk_b.2, (P.kemKeygen sd).1,
      (P.kemEncaps (P.kemKeygen sd).1 m).1)

/-- Hop-4 reduction: the DDH challenge `(g_a, g_b, z)` as `(ek, opk_B, DH4)`. -/
noncomputable def ddhRed4 (P : PassiveParams W PK SK C Sd) (A : KI_Adversary P)
    (g_a g_b z : W) : SPComp Bool :=
  P.dh.keygen.bind fun ik_a => P.dh.keygen.bind fun ik_b => P.dh.keygen.bind fun spk_b =>
  (SPComp.sample Sd).bind fun sd => (SPComp.sample W).bind fun m =>
  (SPComp.sample W).bind fun k => (SPComp.sample W).bind fun r1 =>
  (SPComp.sample W).bind fun r2 => (SPComp.sample W).bind fun r3 =>
  A.run (P.kdf r1 r2 r3 z k)
    (ik_a.2, ik_b.2, g_a, spk_b.2, g_b, (P.kemKeygen sd).1,
      (P.kemEncaps (P.kemKeygen sd).1 m).1)

/-- `ddhRed2` at the public key `pub e`, when key generation returns `(x, pub x)` and `ecdh`
commutes on public keys: `DH3`, `DH4` are Alice's values `ecdh e (pub spk_b)`,
`ecdh e (pub opk_b)`. -/
theorem ddhRed2_pub (P : PassiveParams W PK SK C Sd) (A : KI_Adversary P) {pub : W → W}
    (hkg : P.dh.keygen = (SPComp.sample W).bind (fun x => SPComp.pure (x, pub x)))
    (hc : ECDHSym.CommutesOnPub P.dh.ecdh pub) (e g_b z : W) :
    ddhRed2 P A (pub e) g_b z =
      (SPComp.sample W).bind fun ik_a => (SPComp.sample W).bind fun spk_b =>
      (SPComp.sample W).bind fun opk_b =>
      (SPComp.sample Sd).bind fun sd => (SPComp.sample W).bind fun m =>
      (SPComp.sample W).bind fun k => (SPComp.sample W).bind fun r1 =>
      A.run (P.kdf r1 z (P.dh.ecdh e (pub spk_b)) (P.dh.ecdh e (pub opk_b)) k)
        (pub ik_a, g_b, pub e, pub spk_b, pub opk_b, (P.kemKeygen sd).1,
          (P.kemEncaps (P.kemKeygen sd).1 m).1) := by
  simp only [ddhRed2, ECDHSym.keygen_bind hkg, hc _ e]

/-- `ddhRed3` at the public key `pub e`, as `ddhRed2_pub`: `DH4` is Alice's value
`ecdh e (pub opk_b)`. -/
theorem ddhRed3_pub (P : PassiveParams W PK SK C Sd) (A : KI_Adversary P) {pub : W → W}
    (hkg : P.dh.keygen = (SPComp.sample W).bind (fun x => SPComp.pure (x, pub x)))
    (hc : ECDHSym.CommutesOnPub P.dh.ecdh pub) (e g_b z : W) :
    ddhRed3 P A (pub e) g_b z =
      (SPComp.sample W).bind fun ik_a => (SPComp.sample W).bind fun ik_b =>
      (SPComp.sample W).bind fun opk_b =>
      (SPComp.sample Sd).bind fun sd => (SPComp.sample W).bind fun m =>
      (SPComp.sample W).bind fun k => (SPComp.sample W).bind fun r1 =>
      (SPComp.sample W).bind fun r2 =>
      A.run (P.kdf r1 r2 z (P.dh.ecdh e (pub opk_b)) k)
        (pub ik_a, pub ik_b, pub e, g_b, pub opk_b, (P.kemKeygen sd).1,
          (P.kemEncaps (P.kemKeygen sd).1 m).1) := by
  simp only [ddhRed3, ECDHSym.keygen_bind hkg, hc _ e]

/-! ## The KDF assumption -/

/-- The KDF on five uniform inputs. -/
noncomputable def KDF_Random_Real (P : PassiveParams W PK SK C Sd) : SPComp W :=
  (SPComp.sample W).bind fun k => (SPComp.sample W).bind fun r1 =>
  (SPComp.sample W).bind fun r2 => (SPComp.sample W).bind fun r3 =>
  (SPComp.sample W).bind fun r4 =>
  SPComp.pure (P.kdf r1 r2 r3 r4 k)

/-- A uniform key. -/
noncomputable def KDF_Random_Ideal : SPComp W :=
  SPComp.sample W

/-- The advantage of `A` between the KDF on five uniform inputs and a uniform key: the KDF as
an extractor on a uniform source (Krawczyk, CRYPTO 2010). It is a property of the function
`P.kdf` alone, at most the statistical distance of `kdf(U, U, U, U, U)` from `U`. -/
noncomputable def KDF_Random_Advantage (P : PassiveParams W PK SK C Sd)
    (A : W → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (KDF_Random_Real P) KDF_Random_Ideal A

/-- KDF reduction: the five key pairs drawn by `P.dh.keygen`, the KEM seed and message, and
`A` on the challenge key. -/
noncomputable def kdfReduction (P : PassiveParams W PK SK C Sd) (A : KI_Adversary P) (sk : W) :
    SPComp Bool :=
  P.dh.keygen.bind fun ik_a => P.dh.keygen.bind fun ik_b =>
  P.dh.keygen.bind fun spk_b => P.dh.keygen.bind fun opk_b =>
  P.dh.keygen.bind fun ek =>
  (SPComp.sample Sd).bind fun sd => (SPComp.sample W).bind fun m =>
  A.run sk (ik_a.2, ik_b.2, ek.2, spk_b.2, opk_b.2, (P.kemKeygen sd).1,
    (P.kemEncaps (P.kemKeygen sd).1 m).1)

/-! ## The hops -/

/-- **Hop 0.** The advantage between the real session and hybrid 0 is the KEM advantage of
`kemRed`. -/
theorem hop0_advantage_eq_kem (P : PassiveParams W PK SK C Sd) (A : KI_Adversary P) :
    Advantage (wrap_hybrid P A (pqxdh_real P) true) (wrap_hybrid P A (pqxdh_hyb0 P) true) =
    KEM_Advantage P (kemRed P A) := by
  advantage_eq_nf [wrap_hybrid, pqxdh_real, pqxdh_hyb0, pqxdh_hyb, realDH, kemRed,
    KEM_Advantage, KEM_Game_Real, KEM_Game_Ideal]

/-- **Hop 1.** The advantage between hybrids 0 and 1 is the DDH advantage of `ddhRed1`. -/
theorem hop1_advantage_eq_ddh (P : PassiveParams W PK SK C Sd) (A : KI_Adversary P) :
    Advantage (wrap_hybrid P A (pqxdh_hyb0 P) true) (wrap_hybrid P A (pqxdh_hyb1 P) true) =
    DDH_Advantage P.dh (ddhRed1 P A) := by
  advantage_eq_nf [wrap_hybrid, pqxdh_hyb0, pqxdh_hyb1, pqxdh_hyb, realDH, ddhRed1]

/-- **Hop 2.** The advantage between hybrids 1 and 2 is the DDH advantage of `ddhRed2`. -/
theorem hop2_advantage_eq_ddh (P : PassiveParams W PK SK C Sd) (A : KI_Adversary P)
    (h_sym : ECDHSym.ECDHSymmetric P.dh) :
    Advantage (wrap_hybrid P A (pqxdh_hyb1 P) true) (wrap_hybrid P A (pqxdh_hyb2 P) true) =
    DDH_Advantage P.dh (ddhRed2 P A) := by
  obtain ⟨pub, hkg, hc⟩ := h_sym
  simp only [DDH_Advantage, DDH_Game_Real, DDH_Game_Ideal, wrap_hybrid, pqxdh_hyb1,
    pqxdh_hyb2, pqxdh_hyb, SPComp.monad_bind_eq, ECDHSym.keygen_bind hkg, SPComp.bind_assoc,
    SPComp.pure_bind, ddhRed2_pub P A hkg hc]
  advantage_eq_nf

/-- **Hop 3.** The advantage between hybrids 2 and 3 is the DDH advantage of `ddhRed3`. -/
theorem hop3_advantage_eq_ddh (P : PassiveParams W PK SK C Sd) (A : KI_Adversary P)
    (h_sym : ECDHSym.ECDHSymmetric P.dh) :
    Advantage (wrap_hybrid P A (pqxdh_hyb2 P) true) (wrap_hybrid P A (pqxdh_hyb3 P) true) =
    DDH_Advantage P.dh (ddhRed3 P A) := by
  obtain ⟨pub, hkg, hc⟩ := h_sym
  simp only [DDH_Advantage, DDH_Game_Real, DDH_Game_Ideal, wrap_hybrid, pqxdh_hyb2,
    pqxdh_hyb3, pqxdh_hyb, SPComp.monad_bind_eq, ECDHSym.keygen_bind hkg, SPComp.bind_assoc,
    SPComp.pure_bind, ddhRed3_pub P A hkg hc]
  advantage_eq_nf

/-- **Hop 4.** The advantage between hybrids 3 and 4 is the DDH advantage of `ddhRed4`. -/
theorem hop4_advantage_eq_ddh (P : PassiveParams W PK SK C Sd) (A : KI_Adversary P) :
    Advantage (wrap_hybrid P A (pqxdh_hyb3 P) true) (wrap_hybrid P A (pqxdh_hyb4 P) true) =
    DDH_Advantage P.dh (ddhRed4 P A) := by
  advantage_eq_nf [wrap_hybrid, pqxdh_hyb3, pqxdh_hyb4, pqxdh_hyb, ddhRed4]

/-- **Hop 5.** The advantage between hybrid 4 and the ideal session is the KDF advantage of
`kdfReduction`. -/
theorem hop5_advantage_eq_kdf (P : PassiveParams W PK SK C Sd) (A : KI_Adversary P) :
    Advantage (wrap_hybrid P A (pqxdh_hyb4 P) true) (wrap_hybrid P A (pqxdh_ideal P) true) =
    KDF_Random_Advantage P (kdfReduction P A) := by
  advantage_eq_nf [wrap_hybrid, pqxdh_hyb4, pqxdh_ideal, pqxdh_hyb, kdfReduction,
    KDF_Random_Advantage, KDF_Random_Real, KDF_Random_Ideal]

/-! ## The bound -/

/-- Sum of the advantages of the six reductions built from `A`: the KEM advantage of `kemRed`,
the DDH advantages of `ddhRed1` … `ddhRed4` and the KDF advantage of `kdfReduction`. -/
noncomputable def pqxdhKIReductionBound (P : PassiveParams W PK SK C Sd) (A : KI_Adversary P) :
    ℝ≥0∞ :=
  KEM_Advantage P (kemRed P A) + DDH_Advantage P.dh (ddhRed1 P A) +
    DDH_Advantage P.dh (ddhRed2 P A) + DDH_Advantage P.dh (ddhRed3 P A) +
    DDH_Advantage P.dh (ddhRed4 P A) + KDF_Random_Advantage P (kdfReduction P A)

/-- **PQXDH key indistinguishability, passive, standard model.** When key generation returns
pairs `(x, pub x)` and `ecdh` commutes on public keys, the advantage of `A` between the real
and the ideal session is at most `pqxdhKIReductionBound P A`. -/
theorem pqxdh_ki_security_from_assumptions (P : PassiveParams W PK SK C Sd)
    (A : KI_Adversary P) (h_sym : ECDHSym.ECDHSymmetric P.dh) :
    Advantage (wrap_hybrid P A (pqxdh_real P) true) (wrap_hybrid P A (pqxdh_ideal P) true) ≤
      pqxdhKIReductionBound P A := by
  have h0 := (hop0_advantage_eq_kem P A).le
  have h1 := (hop1_advantage_eq_ddh P A).le
  have h2 := (hop2_advantage_eq_ddh P A h_sym).le
  have h3 := (hop3_advantage_eq_ddh P A h_sym).le
  have h4 := (hop4_advantage_eq_ddh P A).le
  have h5 := (hop5_advantage_eq_kdf P A).le
  unfold pqxdhKIReductionBound
  hop_chain

/-- The game with a uniform key is the adversary on the ideal session: the session key of
`pqxdh_real` is not used. -/
theorem PQXDH_KI_Game_false_eq (P : PassiveParams W PK SK C Sd) (A : KI_Adversary P) :
    PQXDH_KI_Game P A false = wrap_hybrid P A (pqxdh_ideal P) true := by
  bind_swap_nf [PQXDH_KI_Game, wrap_hybrid, pqxdh_real, pqxdh_ideal, pqxdh_hyb, realDH]

/-- **PQXDH key indistinguishability, `PQXDH_KI_Advantage` form.** -/
theorem PQXDH_KI_Advantage_from_assumptions (P : PassiveParams W PK SK C Sd)
    (h_sym : ECDHSym.ECDHSymmetric P.dh) (A : KI_Adversary P) :
    PQXDH_KI_Advantage P A ≤ pqxdhKIReductionBound P A := by
  rw [PQXDH_KI_Advantage, PQXDH_KI_Game_false_eq]
  exact pqxdh_ki_security_from_assumptions P A h_sym

/-! ## Distinguishers of the key and the transcript

As in `X3DHPassiveHops`: `freezeDistinguisher D` runs `D` at `Heap.empty` and keeps the heap;
the two sessions are heap-independent, so freezing preserves the advantage. -/

/-- `D` run at `Heap.empty`, with the heap unchanged. -/
noncomputable def freezeDistinguisher (D : W × PQXDHTranscript W PK C → SPComp Bool) :
    W → PQXDHTranscript W PK C → SPComp Bool :=
  fun sk tr h => (D (sk, tr) Heap.empty).bind (fun (b, _) => SDistr.pure (b, h))

omit [SampleableType W] [SampleableType Sd] in
/-- The frozen distinguisher is `IsPure`. -/
theorem freezeDistinguisher_isPure (D : W × PQXDHTranscript W PK C → SPComp Bool) (sk : W)
    (tr : PQXDHTranscript W PK C) : SPComp.IsPure (freezeDistinguisher D sk tr) := by
  refine ⟨(D (sk, tr) Heap.empty).bind (fun p => SDistr.pure p.1), fun h => ?_⟩
  unfold freezeDistinguisher
  grind

/-- The KI adversary of a distinguisher, by freezing. -/
noncomputable def kiAdversaryOfDistinguisher (P : PassiveParams W PK SK C Sd)
    (D : W × PQXDHTranscript W PK C → SPComp Bool) : KI_Adversary P where
  run := freezeDistinguisher D
  run_isPure := freezeDistinguisher_isPure D

omit [SampleableType W] [SampleableType Sd] in
/-- On a heap-independent game, `prTrue` at `Heap.empty` is unchanged by freezing the
distinguisher. -/
theorem prTrue_bind_freeze_eq {f : SPComp (W × PQXDHTranscript W PK C)} (hf : SPComp.IsPure f)
    (D : W × PQXDHTranscript W PK C → SPComp Bool) :
    prTrue (f.bind D) Heap.empty =
    prTrue (f.bind (fun p => freezeDistinguisher D p.1 p.2)) Heap.empty := by
  obtain ⟨d, hd⟩ := hf
  have eq1 : (f.bind D) Heap.empty = d.bind (fun p => D p Heap.empty) := by
    simp only [SPComp.bind, hd Heap.empty, SDistr.bind_assoc, SDistr.pure_bind]
  have eq2 : (f.bind (fun p => freezeDistinguisher D p.1 p.2)) Heap.empty =
      (d.bind (fun p => D p Heap.empty)).bind (fun q => SDistr.pure (q.1, Heap.empty)) := by
    simp only [SPComp.bind, hd Heap.empty, SDistr.bind_assoc, SDistr.pure_bind,
      freezeDistinguisher]
  unfold prTrue
  rw [eq1, eq2]
  exact (Session.X3DHHops.tsum_freeze_eq _).symm

omit [SampleableType Sd] in
/-- `wrap_hybrid` at the adversary of a distinguisher is the game followed by the frozen
distinguisher. -/
theorem wrap_hybrid_kiAdversaryOfDistinguisher (P : PassiveParams W PK SK C Sd)
    (D : W × PQXDHTranscript W PK C → SPComp Bool) (g : SPComp (W × PQXDHTranscript W PK C)) :
    wrap_hybrid P (kiAdversaryOfDistinguisher P D) g true =
      g.bind (fun p => freezeDistinguisher D p.1 p.2) :=
  rfl

/-- **PQXDH against a distinguisher of the key and the transcript.** For every `D`, the
advantage of `D` between the real and the ideal session is at most `pqxdhKIReductionBound` at
`kiAdversaryOfDistinguisher P D`. -/
theorem pqxdh_advantage_le (P : PassiveParams W PK SK C Sd) (h_sym : ECDHSym.ECDHSymmetric P.dh)
    (D : W × PQXDHTranscript W PK C → SPComp Bool) :
    AdvantageA (pqxdh_real P) (pqxdh_ideal P) D ≤
      pqxdhKIReductionBound P (kiAdversaryOfDistinguisher P D) := by
  have hA := pqxdh_ki_security_from_assumptions P (kiAdversaryOfDistinguisher P D) h_sym
  rw [wrap_hybrid_kiAdversaryOfDistinguisher, wrap_hybrid_kiAdversaryOfDistinguisher] at hA
  unfold AdvantageA Advantage
  unfold Advantage at hA
  rwa [← prTrue_bind_freeze_eq (pqxdh_real_isPure P) D,
    ← prTrue_bind_freeze_eq (pqxdh_ideal_isPure P) D] at hA

end CatCrypt.Crypto.Signal.PQXDHPassive
