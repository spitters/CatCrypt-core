/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DHPassive
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.AutoTime

/-!
# Signal X3DH offline deniability against the responder

Offline deniability in the sense of Vatandas, Gennaro, Ithurburn and Krawczyk
(ACNS 2020): a judge that holds the long-term secret keys of both parties is given
a session (Alice's ephemeral public key and the session key) together with all key
pairs, and must decide whether Alice took part in it or the session was produced
without her. The session is evidence against Alice only if no party other than
Alice could have produced it.

## The judge's view and the responder's simulator

`x3dh_judge_real P` is the judge's view of an honest X3DH execution: the key pairs
of Alice's identity key and Bob's identity, signed and one-time prekeys, Alice's
ephemeral public key, and the session key Alice derives. `x3dh_real_eq_judge_real`
states that `x3dh_real` is a projection of this view.

`x3dh_responder_sim P ik_a_pub ik_b spk_b opk_b` is the simulator run by Bob: from
Alice's public identity key and Bob's own key pairs it draws an ephemeral key pair,
keeps its public half, and derives the session key on Bob's side of the four
Diffie-Hellman values. It uses no secret of Alice.

## Main results

* `x3dh_judge_real_eq_sim` — with `ECDHSymmetric P.dh`, the judge's view of the
  real execution and of Bob's simulation are the same distribution;
* `x3dh_judge_advantage_eq_zero` — every judge has advantage zero between them;
* `x3dh_responder_sim.tree.timeBound_timed`, `x3dh_judge_sim.tree.timeBound_timed` —
  the simulator costs one key generation, the key derivation and four Diffie-Hellman
  values plus a constant, from the costed forms of `derive_reduction`.

## Scope

What is proved: when key generation returns pairs `(x, pub x)` and `ecdh` commutes on public
keys, the judge's view of the honest execution equals the judge's view of Bob's simulation,
in which Bob's four key pairs are drawn by `P.dh.keygen` and the simulator uses Bob's secret
keys and Alice's public identity key only. The statement covers a responder whose prekeys
are drawn by `P.dh.keygen`.

## References

* Vatandas, Gennaro, Ithurburn, Krawczyk — *On the Cryptographic Deniability
  of the Signal Protocol*, ACNS 2020
* Unger, Goldberg — *Deniable Key Exchanges for Secure Messaging*, CCS 2015
* Di Raimondo, Gennaro, Krawczyk — *Deniable Authentication and Key Exchange*,
  CCS 2006
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.Deniability

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.Signal.X3DH
open scoped ENNReal

variable {W : Type} [SampleableType W]

/-! ## The judge's view -/

/-- The key pairs `(private, public)` of Alice's identity key and of Bob's identity,
signed and one-time prekeys. -/
abbrev X3DH_KeyPairs (W : Type) := (W × W) × (W × W) × (W × W) × (W × W)

/-- The view of a judge holding every long-term secret: the key pairs, Alice's
ephemeral public key and the session key. -/
abbrev X3DH_JudgeView (W : Type) := X3DH_KeyPairs W × W × W

/-- The judge's view of an honest X3DH execution: five key pairs drawn by
`P.dh.keygen`, and the session key Alice derives from her identity and ephemeral
secret keys and Bob's public keys. -/
noncomputable def x3dh_judge_real (P : X3DHParams W) : SPComp (X3DH_JudgeView W) :=
  P.dh.keygen.bind fun ik_a => P.dh.keygen.bind fun ik_b =>
  P.dh.keygen.bind fun spk_b => P.dh.keygen.bind fun opk_b =>
  P.dh.keygen.bind fun ek =>
  SPComp.pure ((ik_a, ik_b, spk_b, opk_b), ek.2,
    P.kdf (P.dh.ecdh ik_a.1 spk_b.2) (P.dh.ecdh ek.1 ik_b.2) (P.dh.ecdh ek.1 spk_b.2)
      (P.dh.ecdh ek.1 opk_b.2))

/-- Bob's simulator: from Alice's public identity key `ik_a_pub` and Bob's key pairs,
an ephemeral public key and the session key derived on Bob's side of the four
Diffie-Hellman values. -/
noncomputable def x3dh_responder_sim (P : X3DHParams W) (ik_a_pub : W)
    (ik_b spk_b opk_b : W × W) : SPComp (W × W) :=
  P.dh.keygen.bind fun ek =>
  SPComp.pure (ek.2,
    P.kdf (P.dh.ecdh spk_b.1 ik_a_pub) (P.dh.ecdh ik_b.1 ek.2) (P.dh.ecdh spk_b.1 ek.2)
      (P.dh.ecdh opk_b.1 ek.2))

/-- The judge's view of Bob's simulation: the four long-term key pairs drawn by
`P.dh.keygen`, and the output of `x3dh_responder_sim` on Alice's public identity key
and Bob's key pairs. -/
noncomputable def x3dh_judge_sim (P : X3DHParams W) : SPComp (X3DH_JudgeView W) :=
  P.dh.keygen.bind fun ik_a => P.dh.keygen.bind fun ik_b =>
  P.dh.keygen.bind fun spk_b => P.dh.keygen.bind fun opk_b =>
  (x3dh_responder_sim P ik_a.2 ik_b spk_b opk_b).bind fun r =>
  SPComp.pure ((ik_a, ik_b, spk_b, opk_b), r.1, r.2)

derive_reduction x3dh_responder_sim

derive_reduction x3dh_judge_sim

/-- **Time of the responder's simulator**: one key generation of time at most `Tk`, the
key derivation of cost at most `ck` and four Diffie-Hellman values of cost at most `ce`
each. -/
theorem x3dh_responder_sim.tree.timeBound_timed (P : X3DHParams W) (ik_a_pub : W)
    (ik_b spk_b opk_b : W × W) (kdf : W → W → W → W → W) (kdfCost : W → W → W → W → ℕ)
    (ecdh : W → W → W) (ecdhCost : W → W → ℕ) (keygen : SPTree.Timed (W × W))
    {Tk ck ce : ℕ} (hk : keygen.time ≤ Tk) (hkc : ∀ a b c d, kdfCost a b c d ≤ ck)
    (hec : ∀ a b, ecdhCost a b ≤ ce) :
    SPTree.Timed.stepTime (x3dh_responder_sim.tree.timed P ik_a_pub ik_b spk_b opk_b kdf
      kdfCost ecdh ecdhCost keygen) ≤ Tk + ck + 4 * ce + 5 := by
  time_bound

/-- **Time of the simulated view**: four key generations followed by the responder's
simulator, five key generations of time at most `Tk` in all, the key derivation of cost at
most `ck` and four Diffie-Hellman values of cost at most `ce` each. -/
theorem x3dh_judge_sim.tree.timeBound_timed (P : X3DHParams W)
    (kdf : W → W → W → W → W) (kdfCost : W → W → W → W → ℕ)
    (ecdh : W → W → W) (ecdhCost : W → W → ℕ) (keygen : SPTree.Timed (W × W))
    {Tk ck ce : ℕ} (hk : keygen.time ≤ Tk) (hkc : ∀ a b c d, kdfCost a b c d ≤ ck)
    (hec : ∀ a b, ecdhCost a b ≤ ce) :
    SPTree.Timed.stepTime (x3dh_judge_sim.tree.timed P kdf kdfCost ecdh ecdhCost keygen) ≤
      5 * Tk + ck + 4 * ce + 5 := by
  time_bound

/-- `x3dh_real` is the projection of the judge's view onto the session key and the
transcript. -/
theorem x3dh_real_eq_judge_real (P : X3DHParams W) :
    x3dh_real P = (x3dh_judge_real P).bind fun v =>
      SPComp.pure (v.2.2, (v.1.1.2, v.1.2.1.2, v.2.1, v.1.2.2.1.2, v.1.2.2.2.2)) := by
  simp only [x3dh_real, x3dh_hyb, x3dh_judge_real, SPComp.bind_assoc, SPComp.pure_bind]

/-- **Offline deniability of X3DH against the responder.** When `P.dh.keygen` draws
`(x, pub x)` and `P.dh.ecdh` commutes on public keys (`ECDHSymmetric`), the view of a
judge holding all key pairs is the same distribution for the honest execution and for
Bob's simulation, which uses Alice's public identity key only. -/
theorem x3dh_judge_real_eq_sim (P : X3DHParams W)
    (h_sym : Assumptions.ECDHSym.ECDHSymmetric P.dh) :
    x3dh_judge_real P = x3dh_judge_sim P := by
  obtain ⟨pub, hkg, hc⟩ := h_sym
  unfold x3dh_judge_real x3dh_judge_sim x3dh_responder_sim
  simp only [Assumptions.ECDHSym.keygen_bind hkg, SPComp.bind_assoc, SPComp.pure_bind]
  unfold Assumptions.ECDHSym.CommutesOnPub at hc
  simp only [hc]

/-- Every judge `J` of the view has advantage zero between the honest execution and
Bob's simulation. -/
theorem x3dh_judge_advantage_eq_zero (P : X3DHParams W)
    (h_sym : Assumptions.ECDHSym.ECDHSymmetric P.dh) (J : X3DH_JudgeView W → SPComp Bool) :
    Advantage ((x3dh_judge_real P).bind J) ((x3dh_judge_sim P).bind J) = 0 := by
  rw [x3dh_judge_real_eq_sim P h_sym, Advantage_self]

end CatCrypt.Crypto.Signal.Deniability
