/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DHDeniability
public import CatCryptCore.Crypto.AKE.PQXDHPassive
import CatCryptCore.Tactics.BindSwap
public meta import CatCryptCore.Tactics.BindSwap
import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
import CatCryptCore.Tactics.AutoTime
public import CatCryptCore.Tactics.AutoTime.Basic
public import CatCryptCore.Tactics.StdCosts

/-!
# Signal PQXDH offline deniability against the responder

Offline deniability of PQXDH against a semi-honest judge (Fiedler and Janson, PoPETs 2024),
in the model of `CatCryptCore.Crypto.AKE.X3DHDeniability`: a judge that holds the long-term
secrets of both parties is given a session and must decide whether Alice took part in it or
Bob produced it alone.

## The judge's view and the responder's simulator

`pqxdh_judge_real P` is the judge's view of an honest PQXDH session of
`CatCryptCore.Crypto.AKE.PQXDHPassive`: the key pairs `X3DH_KeyPairs` of Alice's identity key
and Bob's identity, signed and one-time prekeys, the seed of Bob's KEM key pair, Alice's
ephemeral public key, the encapsulation Alice sends and the session key Alice derives from the
four Diffie-Hellman values and the encapsulated secret. `pqxdh_real_eq_judge_real` states that
the session `pqxdh_real` is a projection of this view.

`pqxdh_responder_sim P ik_a_pub ik_b spk_b opk_b pk` is the simulator run by Bob: from Alice's
public identity key, Bob's key pairs and his own KEM public key it draws an ephemeral key pair
and an encapsulation message, encapsulates to `pk`, and derives the session key on Bob's side
of the four Diffie-Hellman values with the encapsulated secret. It uses no secret of Alice.

## Main results

* `pqxdh_judge_real_eq_sim` — with `ECDHSymmetric P.dh`, the judge's view of the real session
  and of Bob's simulation are the same distribution;
* `pqxdh_judge_advantage_eq_zero` — every judge has advantage zero between them;
* `pqxdh_responder_sim.tree.timeBound_timed`, `pqxdh_judge_sim.tree.timeBound_timed` — the
  simulator costs one key generation, one sample, two encapsulation calls, the key derivation
  and four Diffie-Hellman values plus a constant, from the costed forms of `derive_reduction`.

## References

* Fiedler, Janson — *A Deniability Analysis of Signal's Initial Handshake PQXDH*, PoPETs 2024
* Vatandas, Gennaro, Ithurburn, Krawczyk — *On the Cryptographic Deniability of the Signal
  Protocol*, ACNS 2020
* Kret, Schmidt — *The PQXDH Key Agreement Protocol*, Signal, 2023
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.PQXDHDeniability

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.Signal.Deniability (X3DH_KeyPairs)
open CatCrypt.Crypto.Signal.PQXDHPassive
open scoped ENNReal

variable {W PK SK C Sd : Type} [SampleableType W] [SampleableType Sd]

/-! ## The judge's view -/

/-- The view of a judge holding every long-term secret: the key pairs of Alice's identity key
and Bob's identity, signed and one-time prekeys, the seed of Bob's KEM key pair, Alice's
ephemeral public key, the encapsulation and the session key. -/
abbrev PQXDH_JudgeView (W C Sd : Type) := X3DH_KeyPairs W × Sd × W × C × W

/-- The judge's view of an honest PQXDH session: four key pairs drawn by `P.dh.keygen`, the
seed of Bob's KEM key pair, Alice's ephemeral key pair and encapsulation message, and the
session key Alice derives from her identity and ephemeral secret keys, Bob's public keys and
the secret she encapsulates to Bob's KEM public key. -/
noncomputable def pqxdh_judge_real (P : PassiveParams W PK SK C Sd) :
    SPComp (PQXDH_JudgeView W C Sd) :=
  P.dh.keygen.bind fun ik_a => P.dh.keygen.bind fun ik_b =>
  P.dh.keygen.bind fun spk_b => P.dh.keygen.bind fun opk_b =>
  (SPComp.sample Sd).bind fun sd =>
  P.dh.keygen.bind fun ek => (SPComp.sample W).bind fun m =>
  SPComp.pure ((ik_a, ik_b, spk_b, opk_b), sd, ek.2,
    (P.kemEncaps (P.kemKeygen sd).1 m).1,
    P.kdf (P.dh.ecdh ik_a.1 spk_b.2) (P.dh.ecdh ek.1 ik_b.2) (P.dh.ecdh ek.1 spk_b.2)
      (P.dh.ecdh ek.1 opk_b.2) (P.kemEncaps (P.kemKeygen sd).1 m).2)

/-- Bob's simulator: from Alice's public identity key `ik_a_pub`, Bob's key pairs and his KEM
public key `pk`, an ephemeral public key, an encapsulation to `pk`, and the session key derived
on Bob's side of the four Diffie-Hellman values with the encapsulated secret. -/
noncomputable def pqxdh_responder_sim (P : PassiveParams W PK SK C Sd) (ik_a_pub : W)
    (ik_b spk_b opk_b : W × W) (pk : PK) : SPComp (W × C × W) :=
  P.dh.keygen.bind fun ek => (SPComp.sample W).bind fun m =>
  SPComp.pure (ek.2, (P.kemEncaps pk m).1,
    P.kdf (P.dh.ecdh spk_b.1 ik_a_pub) (P.dh.ecdh ik_b.1 ek.2) (P.dh.ecdh spk_b.1 ek.2)
      (P.dh.ecdh opk_b.1 ek.2) (P.kemEncaps pk m).2)

/-- The judge's view of Bob's simulation: the four long-term key pairs drawn by
`P.dh.keygen`, the seed of Bob's KEM key pair, and the output of `pqxdh_responder_sim` on
Alice's public identity key, Bob's key pairs and his KEM public key. -/
noncomputable def pqxdh_judge_sim (P : PassiveParams W PK SK C Sd) :
    SPComp (PQXDH_JudgeView W C Sd) :=
  P.dh.keygen.bind fun ik_a => P.dh.keygen.bind fun ik_b =>
  P.dh.keygen.bind fun spk_b => P.dh.keygen.bind fun opk_b =>
  (SPComp.sample Sd).bind fun sd =>
  (pqxdh_responder_sim P ik_a.2 ik_b spk_b opk_b (P.kemKeygen sd).1).bind fun r =>
  SPComp.pure ((ik_a, ik_b, spk_b, opk_b), sd, r.1, r.2.1, r.2.2)

derive_reduction pqxdh_responder_sim

derive_reduction pqxdh_judge_sim

omit [SampleableType Sd] in
/-- **Time of the responder's simulator**: one key generation of time at most `Tk`, one
sample, two encapsulation calls of cost at most `cn` each, the key derivation of cost at most
`ck` and four Diffie-Hellman values of cost at most `ce` each. -/
theorem pqxdh_responder_sim.tree.timeBound_timed (P : PassiveParams W PK SK C Sd)
    (ik_a_pub : W) (ik_b spk_b opk_b : W × W) (pk : PK) (encaps : PK → W → C × W)
    (encapsCost : PK → W → ℕ) (kdf : W → W → W → W → W → W)
    (kdfCost : W → W → W → W → W → ℕ) (ecdh : W → W → W) (ecdhCost : W → W → ℕ)
    (keygen : SPTree.Timed (W × W)) {Tk cn ck ce : ℕ} (hk : keygen.time ≤ Tk)
    (hn : ∀ a b, encapsCost a b ≤ cn) (hkc : ∀ a b c d e, kdfCost a b c d e ≤ ck)
    (hec : ∀ a b, ecdhCost a b ≤ ce) :
    SPTree.Timed.stepTime (pqxdh_responder_sim.tree.timed P ik_a_pub ik_b spk_b opk_b pk
      encaps encapsCost kdf kdfCost ecdh ecdhCost keygen) ≤
      Tk + 2 * cn + ck + 4 * ce + 8 := by
  time_bound

omit [SampleableType Sd] in
/-- The costed form of the responder's simulator charges no step before its first key
generation. -/
@[simp] theorem pqxdh_responder_sim.tree.timed_fst (P : PassiveParams W PK SK C Sd)
    (ik_a_pub : W) (ik_b spk_b opk_b : W × W) (pk : PK) (encaps : PK → W → C × W)
    (encapsCost : PK → W → ℕ) (kdf : W → W → W → W → W → W)
    (kdfCost : W → W → W → W → W → ℕ) (ecdh : W → W → W) (ecdhCost : W → W → ℕ)
    (keygen : SPTree.Timed (W × W)) :
    (pqxdh_responder_sim.tree.timed P ik_a_pub ik_b spk_b opk_b pk
      encaps encapsCost kdf kdfCost ecdh ecdhCost keygen).1 = 0 := by
  unfold pqxdh_responder_sim.tree.timed
  cases keygen <;> rfl

/-- **Time of the simulated view**: four key generations, the sample of the KEM seed, the KEM
key generation of cost at most `cg`, and the responder's simulator: five key generations of
time at most `Tk` in all, two encapsulation calls of cost at most `cn` each, the key
derivation of cost at most `ck` and four Diffie-Hellman values of cost at most `ce` each. -/
theorem pqxdh_judge_sim.tree.timeBound_timed (P : PassiveParams W PK SK C Sd)
    (kemKeygen : Sd → PK × SK) (kemKeygenCost : Sd → ℕ) (encaps : PK → W → C × W)
    (encapsCost : PK → W → ℕ) (kdf : W → W → W → W → W → W)
    (kdfCost : W → W → W → W → W → ℕ) (ecdh : W → W → W) (ecdhCost : W → W → ℕ)
    (keygen : SPTree.Timed (W × W)) {Tk cg cn ck ce : ℕ} (hk : keygen.time ≤ Tk)
    (hg : ∀ s, kemKeygenCost s ≤ cg) (hn : ∀ a b, encapsCost a b ≤ cn)
    (hkc : ∀ a b c d e, kdfCost a b c d e ≤ ck) (hec : ∀ a b, ecdhCost a b ≤ ce) :
    SPTree.Timed.stepTime (pqxdh_judge_sim.tree.timed P kemKeygen kemKeygenCost encaps
      encapsCost kdf kdfCost ecdh ecdhCost keygen) ≤
      5 * Tk + cg + 2 * cn + ck + 4 * ce + 11 := by
  time_bound

/-- **Offline deniability of PQXDH against the responder.** When `P.dh.keygen` draws
`(x, pub x)` and `P.dh.ecdh` commutes on public keys (`ECDHSymmetric`), the view of a judge
holding all key pairs and Bob's KEM seed is the same distribution for the honest session and
for Bob's simulation, which uses Alice's public identity key only. -/
theorem pqxdh_judge_real_eq_sim (P : PassiveParams W PK SK C Sd)
    (h_sym : Assumptions.ECDHSym.ECDHSymmetric P.dh) :
    pqxdh_judge_real P = pqxdh_judge_sim P := by
  obtain ⟨pub, hkg, hc⟩ := h_sym
  unfold pqxdh_judge_real pqxdh_judge_sim pqxdh_responder_sim
  simp only [Assumptions.ECDHSym.keygen_bind hkg, SPComp.bind_assoc, SPComp.pure_bind]
  unfold Assumptions.ECDHSym.CommutesOnPub at hc
  simp only [hc]

/-- Every judge `J` of the view has advantage zero between the honest session and Bob's
simulation. -/
theorem pqxdh_judge_advantage_eq_zero (P : PassiveParams W PK SK C Sd)
    (h_sym : Assumptions.ECDHSym.ECDHSymmetric P.dh) (J : PQXDH_JudgeView W C Sd → SPComp Bool) :
    Advantage ((pqxdh_judge_real P).bind J) ((pqxdh_judge_sim P).bind J) = 0 := by
  rw [pqxdh_judge_real_eq_sim P h_sym, Advantage_self]

/-- `pqxdh_real` is the projection of the judge's view onto the session key and the
transcript. -/
theorem pqxdh_real_eq_judge_real (P : PassiveParams W PK SK C Sd) :
    pqxdh_real P = (pqxdh_judge_real P).bind fun v =>
      SPComp.pure (v.2.2.2.2, (v.1.1.2, v.1.2.1.2, v.2.2.1, v.1.2.2.1.2, v.1.2.2.2.2,
        (P.kemKeygen v.2.1).1, v.2.2.2.1)) := by
  simp only [pqxdh_real, pqxdh_hyb, realDH, pqxdh_judge_real, SPComp.bind_assoc,
    SPComp.pure_bind]
  bind_swap_nf [P.dh.keygen_isPure]

end CatCrypt.Crypto.Signal.PQXDHDeniability
