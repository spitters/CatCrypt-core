/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DHPassive
public import CatCryptCore.Tactics.BindSwap
public import CatCryptCore.Tactics.AutoArms

/-!
# X3DH key indistinguishability from DDH and a KDF assumption

The passive single-session statement of X3DH in the standard model: the
key-indistinguishability advantage of an adversary `A` (`X3DHPassive`) is at most the DDH
advantages of four reductions and the KDF advantage of one reduction, all built from `A`
(`X3DH_KI_Advantage_from_assumptions`).

## The hops

```
x3dh_real ─ ddhRed1 ─ hyb1 ─ ddhRed2 ─ hyb2 ─ ddhRed3 ─ hyb3 ─ ddhRed4 ─ hyb4
  ─ kdfReduction ─ x3dh_ideal
```

Hop `i ≤ 4` replaces `DHi` by a uniform sample; its reduction `ddhRedi` embeds the DDH
challenge `(g_a, g_b, z)` as the two public keys of `DHi` and `z` as `DHi`, and draws the
other key pairs itself.

* `ddhRed1`: `g_a = ik_A`, `g_b = spk_B`; it holds `ek` and computes `DH2`, `DH3`, `DH4` on
  Alice's side.
* `ddhRed2`, `ddhRed3`, `ddhRed4`: `g_a = ek`, with `g_b = ik_B`, `spk_B`, `opk_B`. The
  reduction does not hold the secret of `ek` and computes the remaining Diffie-Hellman values
  with `ek` on Bob's side, `dh(spk_B, ek)` and `dh(opk_B, ek)`. These equal Alice's values when
  key generation returns pairs `(x, pub x)` and `ecdh` commutes on public keys
  (`ECDHSym.ECDHSymmetric`); `ddhRed2_pub` and `ddhRed3_pub` state the reductions at a public
  key `pub e` with Alice's values. `ddhRed4` needs no other Diffie-Hellman value.

Hop 5 replaces `KDF(r1, r2, r3, r4)` on uniform inputs by a uniform key; its reduction
`kdfReduction` draws the key pairs and runs `A` on the challenge key.

Each hop is an equality of advantages (`hop1_advantage_eq_ddh` … `hop5_advantage_eq_kdf`), and
the bound is the triangle inequality along the chain.

## Main results

* `x3dh_ki_security_from_assumptions` — the advantage of `A` between the real and the ideal
  session is at most `x3dhKIReductionBound P A`.
* `X3DH_KI_Advantage_from_assumptions` — the same bound for `X3DH_KI_Advantage`.
* `x3dh_advantage_le` — for every distinguisher `D` of the key and the transcript, the same
  bound at the adversary `kiAdversaryOfDistinguisher P D`.

## References

* Cohn-Gordon, Cremers, Dowling, Garratt, Stebila — *A Formal Security Analysis of the
  Signal Messaging Protocol*, EuroS&P 2017 (the game of key indistinguishability)
* Krawczyk — *Cryptographic Extraction and Key Derivation: The HKDF Scheme*, CRYPTO 2010
  (the KDF as an extractor)
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.Session.X3DHHops

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.Assumptions
open CatCrypt.Crypto.Signal.X3DH
open scoped ENNReal

variable {W : Type} [SampleableType W]

/-! ## The DDH reductions -/

/-- Hop-1 reduction: the DDH challenge `(g_a, g_b, z)` as `(ik_A, spk_B, DH1)`. -/
noncomputable def ddhRed1 (P : X3DHParams W) (A : KI_Adversary P) (g_a g_b z : W) :
    SPComp Bool :=
  P.dh.keygen.bind fun ik_b => P.dh.keygen.bind fun opk_b => P.dh.keygen.bind fun ek =>
  A.run (P.kdf z (P.dh.ecdh ek.1 ik_b.2) (P.dh.ecdh ek.1 g_b) (P.dh.ecdh ek.1 opk_b.2))
    (g_a, ik_b.2, ek.2, g_b, opk_b.2)

/-- Hop-2 reduction: the DDH challenge `(g_a, g_b, z)` as `(ek, ik_B, DH2)`, with `DH3` and
`DH4` on Bob's side. -/
noncomputable def ddhRed2 (P : X3DHParams W) (A : KI_Adversary P) (g_a g_b z : W) :
    SPComp Bool :=
  P.dh.keygen.bind fun ik_a => P.dh.keygen.bind fun spk_b => P.dh.keygen.bind fun opk_b =>
  (SPComp.sample W).bind fun r1 =>
  A.run (P.kdf r1 z (P.dh.ecdh spk_b.1 g_a) (P.dh.ecdh opk_b.1 g_a))
    (ik_a.2, g_b, g_a, spk_b.2, opk_b.2)

/-- Hop-3 reduction: the DDH challenge `(g_a, g_b, z)` as `(ek, spk_B, DH3)`, with `DH4` on
Bob's side. -/
noncomputable def ddhRed3 (P : X3DHParams W) (A : KI_Adversary P) (g_a g_b z : W) :
    SPComp Bool :=
  P.dh.keygen.bind fun ik_a => P.dh.keygen.bind fun ik_b => P.dh.keygen.bind fun opk_b =>
  (SPComp.sample W).bind fun r1 => (SPComp.sample W).bind fun r2 =>
  A.run (P.kdf r1 r2 z (P.dh.ecdh opk_b.1 g_a)) (ik_a.2, ik_b.2, g_a, g_b, opk_b.2)

/-- Hop-4 reduction: the DDH challenge `(g_a, g_b, z)` as `(ek, opk_B, DH4)`. -/
noncomputable def ddhRed4 (P : X3DHParams W) (A : KI_Adversary P) (g_a g_b z : W) :
    SPComp Bool :=
  P.dh.keygen.bind fun ik_a => P.dh.keygen.bind fun ik_b => P.dh.keygen.bind fun spk_b =>
  (SPComp.sample W).bind fun r1 => (SPComp.sample W).bind fun r2 =>
  (SPComp.sample W).bind fun r3 =>
  A.run (P.kdf r1 r2 r3 z) (ik_a.2, ik_b.2, g_a, spk_b.2, g_b)

/-- `ddhRed2` at the public key `pub e`, when key generation returns `(x, pub x)` and `ecdh`
commutes on public keys: the key pairs are uniform private keys with their public keys, and
`DH3`, `DH4` are Alice's values `ecdh e (pub spk_b)`, `ecdh e (pub opk_b)`. -/
theorem ddhRed2_pub (P : X3DHParams W) (A : KI_Adversary P) {pub : W → W}
    (hkg : P.dh.keygen = (SPComp.sample W).bind (fun x => SPComp.pure (x, pub x)))
    (hc : ECDHSym.CommutesOnPub P.dh.ecdh pub) (e g_b z : W) :
    ddhRed2 P A (pub e) g_b z =
      (SPComp.sample W).bind fun ik_a => (SPComp.sample W).bind fun spk_b =>
      (SPComp.sample W).bind fun opk_b => (SPComp.sample W).bind fun r1 =>
      A.run (P.kdf r1 z (P.dh.ecdh e (pub spk_b)) (P.dh.ecdh e (pub opk_b)))
        (pub ik_a, g_b, pub e, pub spk_b, pub opk_b) := by
  simp only [ddhRed2, ECDHSym.keygen_bind hkg, hc _ e]

/-- `ddhRed3` at the public key `pub e`, as `ddhRed2_pub`: `DH4` is Alice's value
`ecdh e (pub opk_b)`. -/
theorem ddhRed3_pub (P : X3DHParams W) (A : KI_Adversary P) {pub : W → W}
    (hkg : P.dh.keygen = (SPComp.sample W).bind (fun x => SPComp.pure (x, pub x)))
    (hc : ECDHSym.CommutesOnPub P.dh.ecdh pub) (e g_b z : W) :
    ddhRed3 P A (pub e) g_b z =
      (SPComp.sample W).bind fun ik_a => (SPComp.sample W).bind fun ik_b =>
      (SPComp.sample W).bind fun opk_b => (SPComp.sample W).bind fun r1 =>
      (SPComp.sample W).bind fun r2 =>
      A.run (P.kdf r1 r2 z (P.dh.ecdh e (pub opk_b)))
        (pub ik_a, pub ik_b, pub e, g_b, pub opk_b) := by
  simp only [ddhRed3, ECDHSym.keygen_bind hkg, hc _ e]

/-! ## The KDF assumption -/

/-- The KDF on four uniform inputs. -/
noncomputable def KDF_Random_Real (P : X3DHParams W) : SPComp W :=
  (SPComp.sample W).bind fun r1 => (SPComp.sample W).bind fun r2 =>
  (SPComp.sample W).bind fun r3 => (SPComp.sample W).bind fun r4 =>
  SPComp.pure (P.kdf r1 r2 r3 r4)

/-- A uniform key. -/
noncomputable def KDF_Random_Ideal : SPComp W :=
  SPComp.sample W

/-- The advantage of `A` between the KDF on four uniform inputs and a uniform key.

This is the KDF as an extractor on a uniform source (Krawczyk, CRYPTO 2010, the
extraction property of HKDF, there for sources of sufficient min-entropy; here the source is
four independent uniform elements of `W`). It is a property of the function `P.kdf` alone:
for every `A` the advantage is at most the statistical distance of `kdf(U, U, U, U)` from
`U`, and it is zero when every key has the same number of preimages under `P.kdf`. The
analysis of Cohn-Gordon et al. (EuroS&P 2017) models the KDF as a random oracle, under which
this distance is negligible. -/
noncomputable def KDF_Random_Advantage (P : X3DHParams W) (A : W → SPComp Bool) :
    ℝ≥0∞ :=
  AdvantageA (KDF_Random_Real P) KDF_Random_Ideal A

/-- KDF reduction: the five key pairs drawn by `P.dh.keygen` and `A` on the challenge key. -/
noncomputable def kdfReduction (P : X3DHParams W) (A : KI_Adversary P) (sk : W) :
    SPComp Bool :=
  P.dh.keygen.bind fun ik_a => P.dh.keygen.bind fun ik_b =>
  P.dh.keygen.bind fun spk_b => P.dh.keygen.bind fun opk_b =>
  P.dh.keygen.bind fun ek => A.run sk (ik_a.2, ik_b.2, ek.2, spk_b.2, opk_b.2)

/-! ## The hops -/

/-- **Hop 1.** The advantage between the real session and hybrid 1 is the DDH advantage of
`ddhRed1`. -/
theorem hop1_advantage_eq_ddh (P : X3DHParams W) (A : KI_Adversary P) :
    Advantage (wrap_hybrid P A (x3dh_real P) true) (wrap_hybrid P A (x3dh_hyb1 P) true) =
    DDH_Advantage P.dh (ddhRed1 P A) := by
  advantage_eq_nf [wrap_hybrid, x3dh_real, x3dh_hyb1, x3dh_hyb, ddhRed1]

/-- **Hop 2.** The advantage between hybrids 1 and 2 is the DDH advantage of `ddhRed2`. -/
theorem hop2_advantage_eq_ddh (P : X3DHParams W) (A : KI_Adversary P)
    (h_sym : ECDHSym.ECDHSymmetric P.dh) :
    Advantage (wrap_hybrid P A (x3dh_hyb1 P) true) (wrap_hybrid P A (x3dh_hyb2 P) true) =
    DDH_Advantage P.dh (ddhRed2 P A) := by
  obtain ⟨pub, hkg, hc⟩ := h_sym
  simp only [DDH_Advantage, DDH_Game_Real, DDH_Game_Ideal, wrap_hybrid, x3dh_hyb1, x3dh_hyb2,
    x3dh_hyb, SPComp.monad_bind_eq, ECDHSym.keygen_bind hkg, SPComp.bind_assoc,
    SPComp.pure_bind, ddhRed2_pub P A hkg hc]
  advantage_eq_nf

/-- **Hop 3.** The advantage between hybrids 2 and 3 is the DDH advantage of `ddhRed3`. -/
theorem hop3_advantage_eq_ddh (P : X3DHParams W) (A : KI_Adversary P)
    (h_sym : ECDHSym.ECDHSymmetric P.dh) :
    Advantage (wrap_hybrid P A (x3dh_hyb2 P) true) (wrap_hybrid P A (x3dh_hyb3 P) true) =
    DDH_Advantage P.dh (ddhRed3 P A) := by
  obtain ⟨pub, hkg, hc⟩ := h_sym
  simp only [DDH_Advantage, DDH_Game_Real, DDH_Game_Ideal, wrap_hybrid, x3dh_hyb2, x3dh_hyb3,
    x3dh_hyb, SPComp.monad_bind_eq, ECDHSym.keygen_bind hkg, SPComp.bind_assoc,
    SPComp.pure_bind, ddhRed3_pub P A hkg hc]
  advantage_eq_nf

/-- **Hop 4.** The advantage between hybrids 3 and 4 is the DDH advantage of `ddhRed4`. -/
theorem hop4_advantage_eq_ddh (P : X3DHParams W) (A : KI_Adversary P) :
    Advantage (wrap_hybrid P A (x3dh_hyb3 P) true) (wrap_hybrid P A (x3dh_hyb4 P) true) =
    DDH_Advantage P.dh (ddhRed4 P A) := by
  advantage_eq_nf [wrap_hybrid, x3dh_hyb3, x3dh_hyb4, x3dh_hyb, ddhRed4]

/-- **Hop 5.** The advantage between hybrid 4 and the ideal session is the KDF advantage of
`kdfReduction`. -/
theorem hop5_advantage_eq_kdf (P : X3DHParams W) (A : KI_Adversary P) :
    Advantage (wrap_hybrid P A (x3dh_hyb4 P) true) (wrap_hybrid P A (x3dh_ideal P) true) =
    KDF_Random_Advantage P (kdfReduction P A) := by
  advantage_eq_nf [wrap_hybrid, x3dh_hyb4, x3dh_ideal, x3dh_hyb, kdfReduction,
    KDF_Random_Real, KDF_Random_Ideal]

/-! ## The bound -/

/-- Sum of the advantages of the five reductions built from `A`: the DDH advantages of
`ddhRed1` … `ddhRed4` and the KDF advantage of `kdfReduction`. -/
noncomputable def x3dhKIReductionBound (P : X3DHParams W) (A : KI_Adversary P) : ℝ≥0∞ :=
  DDH_Advantage P.dh (ddhRed1 P A) + DDH_Advantage P.dh (ddhRed2 P A) +
    DDH_Advantage P.dh (ddhRed3 P A) + DDH_Advantage P.dh (ddhRed4 P A) +
    KDF_Random_Advantage P (kdfReduction P A)

/-- **X3DH key indistinguishability, passive, standard model.** When key generation returns
pairs `(x, pub x)` and `ecdh` commutes on public keys, the advantage of `A` between the real
and the ideal session is at most `x3dhKIReductionBound P A`. -/
theorem x3dh_ki_security_from_assumptions (P : X3DHParams W) (A : KI_Adversary P)
    (h_sym : ECDHSym.ECDHSymmetric P.dh) :
    Advantage (wrap_hybrid P A (x3dh_real P) true) (wrap_hybrid P A (x3dh_ideal P) true) ≤
      x3dhKIReductionBound P A := by
  have h1 := (hop1_advantage_eq_ddh P A).le
  have h2 := (hop2_advantage_eq_ddh P A h_sym).le
  have h3 := (hop3_advantage_eq_ddh P A h_sym).le
  have h4 := (hop4_advantage_eq_ddh P A).le
  have h5 := (hop5_advantage_eq_kdf P A).le
  unfold x3dhKIReductionBound
  hop_chain

/-- The game with a uniform key is the adversary on the ideal session: the session key of
`x3dh_real` is not used. -/
theorem X3DH_KI_Game_false_eq (P : X3DHParams W) (A : KI_Adversary P) :
    X3DH_KI_Game P A false = wrap_hybrid P A (x3dh_ideal P) true := by
  bind_swap_nf [X3DH_KI_Game, wrap_hybrid, x3dh_real, x3dh_ideal, x3dh_hyb]

/-- **X3DH key indistinguishability, `X3DH_KI_Advantage` form.** -/
theorem X3DH_KI_Advantage_from_assumptions (P : X3DHParams W)
    (h_sym : ECDHSym.ECDHSymmetric P.dh) (A : KI_Adversary P) :
    X3DH_KI_Advantage P A ≤ x3dhKIReductionBound P A := by
  rw [X3DH_KI_Advantage, X3DH_KI_Game_false_eq]
  exact x3dh_ki_security_from_assumptions P A h_sym

/-! ## Distinguishers of the key and the transcript

`AdvantageA (x3dh_real P) (x3dh_ideal P) D` ranges over every distinguisher `D`, while a
`KI_Adversary` is heap-independent. `freezeDistinguisher D` runs `D` at `Heap.empty` and
keeps the heap; the two sessions are heap-independent, so they see `D` only at `Heap.empty`,
and freezing preserves the advantage (`prTrue_bind_freeze_eq`). -/

/-- `D` run at `Heap.empty`, with the heap unchanged. -/
noncomputable def freezeDistinguisher (D : W × X3DHTranscript W → SPComp Bool) :
    W → X3DHTranscript W → SPComp Bool :=
  fun sk tr h => (D (sk, tr) Heap.empty).bind (fun (b, _) => SDistr.pure (b, h))

omit [SampleableType W] in
/-- The frozen distinguisher is `IsPure`. -/
theorem freezeDistinguisher_isPure (D : W × X3DHTranscript W → SPComp Bool) (sk : W)
    (tr : X3DHTranscript W) : SPComp.IsPure (freezeDistinguisher D sk tr) := by
  refine ⟨(D (sk, tr) Heap.empty).bind (fun p => SDistr.pure p.1), fun h => ?_⟩
  unfold freezeDistinguisher
  grind

/-- The KI adversary of a distinguisher, by freezing. -/
noncomputable def kiAdversaryOfDistinguisher (P : X3DHParams W)
    (D : W × X3DHTranscript W → SPComp Bool) : KI_Adversary P where
  run := freezeDistinguisher D
  run_isPure := freezeDistinguisher_isPure D

/-- Post-composing a sub-distribution with `fun q => SDistr.pure (q.1, Heap.empty)` keeps
the mass of the outputs `(true, _)`. -/
theorem tsum_freeze_eq (s : SDistr (Bool × Heap)) :
    ∑' h, (s.bind (fun q => SDistr.pure (q.1, Heap.empty))) (some (true, h)) =
    ∑' h, s (some (true, h)) := by
  simp_all [ENNReal.tsum_prod', SDistr.bind, PMF.bind_apply, ENNReal.tsum_comm,
    SDistr.tsum_option_eq_add, SDistr.fail_apply_some, mul_zero, tsum_zero, zero_add,
    SDistr.pure_apply_some, Prod.mk.injEq]

omit [SampleableType W] in
/-- On a heap-independent game, `prTrue` at `Heap.empty` is unchanged by freezing the
distinguisher. -/
theorem prTrue_bind_freeze_eq {f : SPComp (W × X3DHTranscript W)} (hf : SPComp.IsPure f)
    (D : W × X3DHTranscript W → SPComp Bool) :
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
  exact (tsum_freeze_eq _).symm

/-- `wrap_hybrid` at the adversary of a distinguisher is the game followed by the frozen
distinguisher. -/
theorem wrap_hybrid_kiAdversaryOfDistinguisher (P : X3DHParams W)
    (D : W × X3DHTranscript W → SPComp Bool) (g : SPComp (W × X3DHTranscript W)) :
    wrap_hybrid P (kiAdversaryOfDistinguisher P D) g true =
      g.bind (fun p => freezeDistinguisher D p.1 p.2) :=
  rfl

/-- **X3DH against a distinguisher of the key and the transcript.** For every `D`, the
advantage of `D` between the real and the ideal session is at most `x3dhKIReductionBound` at
`kiAdversaryOfDistinguisher P D`. -/
theorem x3dh_advantage_le (P : X3DHParams W) (h_sym : ECDHSym.ECDHSymmetric P.dh)
    (D : W × X3DHTranscript W → SPComp Bool) :
    AdvantageA (x3dh_real P) (x3dh_ideal P) D ≤
      x3dhKIReductionBound P (kiAdversaryOfDistinguisher P D) := by
  have hA := x3dh_ki_security_from_assumptions P (kiAdversaryOfDistinguisher P D) h_sym
  rw [wrap_hybrid_kiAdversaryOfDistinguisher, wrap_hybrid_kiAdversaryOfDistinguisher] at hA
  unfold AdvantageA Advantage
  unfold Advantage at hA
  rwa [← prTrue_bind_freeze_eq (x3dh_real_isPure P) D,
    ← prTrue_bind_freeze_eq (x3dh_ideal_isPure P) D] at hA

end CatCrypt.Crypto.Signal.Session.X3DHHops
