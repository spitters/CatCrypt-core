/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signal.DoubleRatchet_CKA
public import CatCryptCore.Crypto.Messaging.TripleRatchet

/-!
# The Signal triple ratchet

The triple ratchet of Dodis, Jost, Katsumata, Prest and Schmidt runs the Diffie–Hellman CKA
and a KEM CKA side by side. The Signal triple ratchet is the instance of the core triple
ratchet (`CatCrypt.Crypto.Messaging.TripleRatchet`) in which

* the CKA is `prodCKA (dhCKA G) (kemCKA kem)`: the Diffie–Hellman ratchet over the cyclic group
  `G` and the KEM ratchet of the KEM `kem`; the CKA message of an epoch is the Diffie–Hellman
  value, the KEM ciphertext (none in the first epoch) and the next KEM encapsulation key;
* the root step is `trRoot root` for a dual PRF `root : RK × G → K → RK × W`, which maps the
  root key, the Diffie–Hellman key and the KEM key to the next root key and the chain key of
  the epoch;
* the FS-AEAD of each epoch is the Signal symmetric ratchet of an `FSAEADConfig`, presented to
  the core game by `FSAEAD.toPRG`, `FSAEAD.toAEAD` and `signalMsgs`.

The adversary sees the public value of the CKA initialisation, the CKA messages of all epochs
(Diffie–Hellman values, KEM encapsulation keys and KEM ciphertexts) and the ciphertexts of all
epochs; in the ideal game the ciphertexts are uniform.

## Main definitions

* `TRConfig` — the KEM with its purity facts, the root dual PRF and the symmetric ratchet
* `trCKA`, `TRView` — the CKA of the triple ratchet and the view of the adversary
* `tr_real`, `tr_ideal`, `TR_Advantage` — the secure-messaging game of the Signal triple ratchet
* `trDDHBound`, `trKEMBound`, `trHybridBound` — the DDH chain, the KEM chain and their minimum

## Main results

* `tr_real_isPure`, `tr_ideal_isPure` — the games do not touch the heap
* `tr_advantage_bound` — for every adversary, the advantage is at most the minimum of the DDH
  chain and the KEM chain (core `tr_advantage_le_min`): the Signal triple ratchet is
  confidential if DDH holds in `G` or the KEM is IND-CPA secure, given the dual-PRF security of
  the root step in the corresponding argument and the FS-AEAD security of the symmetric ratchet

## References

* Y. Dodis, D. Jost, S. Katsumata, T. Prest, R. Schmidt, *Triple Ratchet: A Bandwidth
  Efficient Hybrid-Secure Signal Protocol*, EUROCRYPT 2025
* J. Alwen, S. Coretti, Y. Dodis, *The Double Ratchet: Security Notions, Proofs, and
  Modularization for the Signal Protocol*, EUROCRYPT 2019
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.TripleRatchet

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Messaging
  CatCrypt.Crypto.Assumptions CatCrypt.Crypto.PRPPRF CatCrypt.Examples.KEMDEM
  CatCryptCore.Examples.CyclicGroupDDH CatCrypt.Crypto.Signal.DoubleRatchet_CKA
open scoped ENNReal

variable (G : Type) [CyclicGroup G] {PK SK K KC RK W : Type} [CryptoWord W]

/-- Configuration of the Signal triple ratchet over the cyclic group `G`: the KEM, whose key
generation and encapsulation do not touch the heap, the root dual PRF and the symmetric
ratchet. -/
structure TRConfig (PK SK K KC RK W : Type) [CryptoWord W] where
  /-- The KEM of the post-quantum ratchet. -/
  kem : KEMScheme PK SK K KC
  /-- The key generation of the KEM does not touch the heap. -/
  kgen_isPure : SPComp.IsPure kem.kgen
  /-- The encapsulation of the KEM does not touch the heap. -/
  encap_isPure : ∀ pk, SPComp.IsPure (kem.encap pk)
  /-- The root step: root key and Diffie–Hellman key (left), KEM key (right). -/
  root : RK × G → K → RK × W
  /-- The symmetric ratchet of each epoch. -/
  chain : FSAEAD.FSAEADConfig W

/-- The CKA of the Signal triple ratchet: the Diffie–Hellman CKA and the KEM CKA. -/
noncomputable abbrev trCKA [Inhabited K] (cfg : TRConfig G PK SK K KC RK W) :=
  prodCKA (dhCKA G) (kemCKA cfg.kem)

/-- The view of the adversary: the CKA public values and messages, and the ciphertexts. -/
abbrev TRView (KC PK W : Type) := SMView (G × (Option KC × PK)) W

variable [Inhabited K] [Fintype K] [Nonempty K] [Fintype RK] [Nonempty RK]

/-- The real secure-messaging game of the Signal triple ratchet over the epochs with plaintexts
`msgs`. -/
noncomputable def tr_real (cfg : TRConfig G PK SK K KC RK W) (msgs : List (List W)) :
    SPComp (TRView G KC PK W) :=
  sm_real (trCKA G cfg) (trRoot cfg.root) (FSAEAD.toPRG cfg.chain) (FSAEAD.toAEAD cfg.chain)
    (signalMsgs msgs)

/-- The ideal secure-messaging game of the Signal triple ratchet: the CKA run and uniform
ciphertexts. -/
noncomputable def tr_ideal (cfg : TRConfig G PK SK K KC RK W) (msgs : List (List W)) :
    SPComp (TRView G KC PK W) :=
  sm_ideal (Ct := W) (trCKA G cfg) (signalMsgs msgs)

/-- Advantage of the distinguisher `A` against the Signal triple ratchet. -/
noncomputable def TR_Advantage (cfg : TRConfig G PK SK K KC RK W) (msgs : List (List W))
    (A : TRView G KC PK W → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (tr_real G cfg msgs) (tr_ideal G cfg msgs) A

/-! ## The games do not touch the heap -/

omit [Fintype K] [Nonempty K] [Fintype RK] [Nonempty RK] in
/-- The initialisation of the triple-ratchet CKA does not touch the heap. -/
theorem trCKA_init_isPure (cfg : TRConfig G PK SK K KC RK W) :
    SPComp.IsPure (trCKA G cfg).init :=
  prodCKA_init_isPure _ _ (dhCKA_init_isPure G) (kemCKA_init_isPure cfg.kem cfg.kgen_isPure)

omit [Fintype K] [Nonempty K] [Fintype RK] [Nonempty RK] in
/-- The send step of the triple-ratchet CKA does not touch the heap. -/
theorem trCKA_send_isPure (cfg : TRConfig G PK SK K KC RK W) (s) :
    SPComp.IsPure ((trCKA G cfg).send s) :=
  prodCKA_send_isPure _ _ (dhCKA_send_isPure G)
    (kemCKA_send_isPure cfg.kem cfg.kgen_isPure cfg.encap_isPure) s

omit [Fintype K] [Nonempty K] in
/-- The real game does not touch the heap. -/
theorem tr_real_isPure (cfg : TRConfig G PK SK K KC RK W) (msgs : List (List W)) :
    SPComp.IsPure (tr_real G cfg msgs) :=
  sm_real_isPure _ (trCKA_init_isPure G cfg) (trCKA_send_isPure G cfg) _ _ _ _

omit [Fintype K] [Nonempty K] [Fintype RK] [Nonempty RK] in
/-- The ideal game does not touch the heap. -/
theorem tr_ideal_isPure (cfg : TRConfig G PK SK K KC RK W) (msgs : List (List W)) :
    SPComp.IsPure (tr_ideal G cfg msgs) :=
  sm_ideal_isPure _ (trCKA_init_isPure G cfg) (trCKA_send_isPure G cfg) _

/-! ## The bound -/

variable [DecidableEq G] [Fintype KC] [Nonempty KC] [DecidableEq K] [DecidableEq RK]

/-- The DDH chain at the adversary `A`: per epoch, the DDH advantage of `ckaDDHRed` at the
one-sided product reduction, the dual-PRF advantage of the root step keyed by its left argument
at `trRootRedL`, and the FS-AEAD advantage at `smAEADRed`. -/
noncomputable def trDDHBound (cfg : TRConfig G PK SK K KC RK W) (msgs : List (List W))
    (A : TRView G KC PK W → SPComp Bool) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range (signalMsgs msgs).length,
      DDH_Advantage G (ckaDDHRed t ((signalMsgs msgs).length - (t + 1))
        (prodCKARed₁ (kemCKA cfg.kem) t ((signalMsgs msgs).length - (t + 1))
          (trCKARed mixLeft (trRoot cfg.root) (FSAEAD.toPRG cfg.chain)
            (FSAEAD.toAEAD cfg.chain) (signalMsgs msgs) t A))) +
    ∑ t ∈ Finset.range (signalMsgs msgs).length,
      DualPRF_Left_Advantage cfg.root
        (trRootRedL (trCKA G cfg) cfg.root (FSAEAD.toPRG cfg.chain) (FSAEAD.toAEAD cfg.chain)
          (signalMsgs msgs) t ((signalMsgs msgs).length - (t + 1)) A) +
    ∑ t ∈ Finset.range (signalMsgs msgs).length,
      Messaging.FSAEAD_Advantage (FSAEAD.toPRG cfg.chain) (FSAEAD.toAEAD cfg.chain)
        ((signalMsgs msgs).getD t [])
        (smAEADRed (trCKA G cfg) (FSAEAD.toPRG cfg.chain) (FSAEAD.toAEAD cfg.chain)
          (signalMsgs msgs) t ((signalMsgs msgs).length - (t + 1)) A)

/-- The KEM chain at the adversary `A`: per epoch, the KEM IND-CPA advantage of `kemCKARed` at
the one-sided product reduction, the dual-PRF advantage of the root step keyed by its right
argument at `trRootRedR`, and the FS-AEAD advantage at `smAEADRed`. -/
noncomputable def trKEMBound (cfg : TRConfig G PK SK K KC RK W) (msgs : List (List W))
    (A : TRView G KC PK W → SPComp Bool) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range (signalMsgs msgs).length,
      KEM_CPA_Advantage cfg.kem (kemCKARed cfg.kem t ((signalMsgs msgs).length - (t + 1))
        (prodCKARedR (dhCKA G) t ((signalMsgs msgs).length - (t + 1))
          (trCKARed mixRight (trRoot cfg.root) (FSAEAD.toPRG cfg.chain)
            (FSAEAD.toAEAD cfg.chain) (signalMsgs msgs) t A))) +
    ∑ t ∈ Finset.range (signalMsgs msgs).length,
      DualPRF_Right_Advantage cfg.root
        (trRootRedR (trCKA G cfg) cfg.root (FSAEAD.toPRG cfg.chain) (FSAEAD.toAEAD cfg.chain)
          (signalMsgs msgs) t ((signalMsgs msgs).length - (t + 1)) A) +
    ∑ t ∈ Finset.range (signalMsgs msgs).length,
      Messaging.FSAEAD_Advantage (FSAEAD.toPRG cfg.chain) (FSAEAD.toAEAD cfg.chain)
        ((signalMsgs msgs).getD t [])
        (smAEADRed (trCKA G cfg) (FSAEAD.toPRG cfg.chain) (FSAEAD.toAEAD cfg.chain)
          (signalMsgs msgs) t ((signalMsgs msgs).length - (t + 1)) A)

/-- The bound of the Signal triple ratchet at the adversary `A`: the minimum of the DDH chain
and the KEM chain. -/
noncomputable def trHybridBound (cfg : TRConfig G PK SK K KC RK W) (msgs : List (List W))
    (A : TRView G KC PK W → SPComp Bool) : ℝ≥0∞ :=
  min (trDDHBound G cfg msgs A) (trKEMBound G cfg msgs A)

/-- **Hybrid confidentiality of the Signal triple ratchet.** For every adversary `A`, the
advantage against the secure-messaging game of the Signal triple ratchet is at most the minimum
of the DDH chain `trDDHBound` and the KEM chain `trKEMBound` (core `tr_advantage_le_min`): the
protocol is confidential if DDH holds in `G` or the KEM is IND-CPA secure, given the dual-PRF
security of the root step in the corresponding argument and the FS-AEAD security of the
symmetric ratchet. -/
theorem tr_advantage_bound (cfg : TRConfig G PK SK K KC RK W) (msgs : List (List W))
    (A : TRView G KC PK W → SPComp Bool) :
    TR_Advantage G cfg msgs A ≤ trHybridBound G cfg msgs A :=
  tr_advantage_le_min G cfg.kem cfg.kgen_isPure cfg.encap_isPure cfg.root
    (FSAEAD.toPRG cfg.chain) (FSAEAD.toAEAD cfg.chain) (signalMsgs msgs) A

end CatCrypt.Crypto.Signal.TripleRatchet
