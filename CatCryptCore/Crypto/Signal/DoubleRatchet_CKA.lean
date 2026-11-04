/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signal.FSAEAD
public import CatCryptCore.Crypto.Messaging.DoubleRatchet
public import CatCryptCore.Crypto.Messaging.KEMCKA

/-!
# Confidentiality of the Signal double ratchet with the Diffie–Hellman CKA

The Signal double ratchet is the instance of the core double ratchet
(`CatCrypt.Crypto.Messaging.sm_real`/`sm_ideal`) in which

* the CKA is the Diffie–Hellman ratchet `dhCKA G` over a cyclic group `G`;
* the root KDF is the HKDF root step `Messaging.hkdfRoot kdf`: from the root key `rk` (the
  HKDF salt) and the DH output `I` (the input keying material) it derives the next root key
  and the initial chain key of the epoch;
* the FS-AEAD of each epoch is the Signal symmetric ratchet of an `FSAEADConfig`, presented to
  the core game by `FSAEAD.toPRG`, `FSAEAD.toAEAD` and `FSAEAD.toMsgs`.

## Main definitions

* `signalMsgs` — the messages of the epochs as core FS-AEAD messages
* `signalDRBound` — the bound of `signal_dr_confidentiality` as a function of the adversary

## Main results

* `signal_dr_confidentiality` — for every adversary `A`, the secure-messaging advantage of the
  Signal double ratchet is at most the DDH advantages of `ckaDDHRed` at `smCKARed`, the PRG
  advantages of the HKDF root step at `smRootRed`, and the FS-AEAD advantages of the Signal
  symmetric ratchet (`FSAEAD.FSAEAD_Advantage`) at `smAEADRed`, summed over the epochs

## References

* J. Alwen, S. Coretti, Y. Dodis, *The Double Ratchet: Security Notions, Proofs, and
  Modularization for the Signal Protocol*, EUROCRYPT 2019, §5
* T. Perrin, M. Marlinspike, *The Double Ratchet Algorithm*, §5.2 (`KDF_RK`)
* Cohn-Gordon et al. — EuroS&P 2017 (X3DH + DR analysis)
* Canetti et al. — ePrint 2022/376 (UC Double Ratchet)
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.DoubleRatchet_CKA

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Messaging
  CatCryptCore.Examples.CyclicGroupDDH
open scoped ENNReal

/-! ## The Signal double ratchet as a core double ratchet -/

section Signal

variable {RK W : Type} [Fintype RK] [Nonempty RK] [CryptoWord W]

/-- The plaintexts of the epochs as core FS-AEAD messages, epoch by epoch. -/
def signalMsgs (msgs : List (List W)) : List (List (W × W)) := msgs.map FSAEAD.toMsgs

/-- The bound of `signal_dr_confidentiality` at the adversary `A`: the DDH advantages of
`ckaDDHRed` at `smCKARed`, the PRG advantages of the HKDF root step at `smRootRed`, and the
FS-AEAD advantages of the Signal symmetric ratchet at `smAEADRed`, summed over the epochs. -/
noncomputable def signalDRBound (G : Type) [CyclicGroup G] (kdf : RK → G → RK × W)
    (cfg : FSAEAD.FSAEADConfig W) (msgs : List (List W)) (A : SMView G W → SPComp Bool) :
    ℝ≥0∞ :=
  ∑ t ∈ Finset.range msgs.length,
      DDH_Advantage G (ckaDDHRed t (msgs.length - (t + 1))
        (smCKARed (hkdfRoot kdf) (FSAEAD.toPRG cfg) (FSAEAD.toAEAD cfg)
          (signalMsgs msgs) t A)) +
    ∑ t ∈ Finset.range msgs.length,
      Assumptions.PRG_Advantage (hkdfRoot kdf)
        (smRootRed (dhCKA G) (hkdfRoot kdf) (FSAEAD.toPRG cfg) (FSAEAD.toAEAD cfg)
          (signalMsgs msgs) t (msgs.length - (t + 1)) A) +
    ∑ t ∈ Finset.range msgs.length,
      FSAEAD.FSAEAD_Advantage cfg (msgs.getD t [])
        (smAEADRed (dhCKA G) (FSAEAD.toPRG cfg) (FSAEAD.toAEAD cfg)
          (signalMsgs msgs) t (msgs.length - (t + 1)) A)

/-- **Confidentiality of the Signal double ratchet.** For every adversary `A` against the
secure-messaging game of the Signal double ratchet (Diffie–Hellman CKA over `G`, HKDF root step
`hkdfRoot kdf`, symmetric ratchet `cfg`) over the epochs with plaintexts `msgs`, the advantage
is at most the sum over the epochs `t` of the DDH advantage of `ckaDDHRed` at `smCKARed`, the
PRG advantage of the HKDF root step at `smRootRed`, and the FS-AEAD advantage of the Signal
symmetric ratchet on the plaintexts of epoch `t` at `smAEADRed`. -/
theorem signal_dr_confidentiality (G : Type) [CyclicGroup G] (kdf : RK → G → RK × W)
    (cfg : FSAEAD.FSAEADConfig W) (msgs : List (List W)) (A : SMView G W → SPComp Bool) :
    SM_Advantage (dhCKA G) (hkdfRoot kdf) (FSAEAD.toPRG cfg) (FSAEAD.toAEAD cfg)
        (signalMsgs msgs) A ≤
      ∑ t ∈ Finset.range msgs.length,
          DDH_Advantage G (ckaDDHRed t (msgs.length - (t + 1))
            (smCKARed (hkdfRoot kdf) (FSAEAD.toPRG cfg) (FSAEAD.toAEAD cfg)
              (signalMsgs msgs) t A)) +
        ∑ t ∈ Finset.range msgs.length,
          Assumptions.PRG_Advantage (hkdfRoot kdf)
            (smRootRed (dhCKA G) (hkdfRoot kdf) (FSAEAD.toPRG cfg) (FSAEAD.toAEAD cfg)
              (signalMsgs msgs) t (msgs.length - (t + 1)) A) +
        ∑ t ∈ Finset.range msgs.length,
          FSAEAD.FSAEAD_Advantage cfg (msgs.getD t [])
            (smAEADRed (dhCKA G) (FSAEAD.toPRG cfg) (FSAEAD.toAEAD cfg)
              (signalMsgs msgs) t (msgs.length - (t + 1)) A) := by
  have h := sm_dh_advantage_le G (hkdfRoot kdf) (FSAEAD.toPRG cfg) (FSAEAD.toAEAD cfg)
    (signalMsgs msgs) A
  have hlen : (signalMsgs msgs).length = msgs.length := List.length_map _
  have hget : ∀ t, (signalMsgs msgs).getD t [] = FSAEAD.toMsgs (msgs.getD t []) := by
    intro t
    simp only [signalMsgs, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases msgs[t]? <;> rfl
  simp only [hlen, hget, ← FSAEAD.FSAEAD_Advantage_eq_messaging] at h
  exact h

end Signal

end CatCrypt.Crypto.Signal.DoubleRatchet_CKA
