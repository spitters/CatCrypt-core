/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.SymmRatchet
public import CatCryptCore.Crypto.Encryption
public import CatCryptCore.Crypto.Messaging.FSAEAD

/-!
# Forward-Secure AEAD (FS-AEAD)

This file defines Forward-Secure Authenticated Encryption with Associated Data,
combining a PRG chain (symmetric ratchet) with per-message encryption.

FS-AEAD is the "symmetric ratchet" component of the Signal Double Ratchet:
within each epoch, the chain key evolves via a PRG and each step produces a
message key used for encryption.

## Main definitions

* `FSAEADConfig` — configuration: PRG + encryption scheme
* `fsaead_real'` — real FS-AEAD game (PRG chain + encrypt), the ratchet game `attack_real`
* `fsaead_ideal` — ideal FS-AEAD game (random ciphertexts + random chain key)
* `toPRG`, `toAEAD`, `toMsgs` — the configuration and the messages as core FS-AEAD data

## Main results

* `fsaead_security` — the advantage is at most PRG advantages of the FS-PRG reductions plus
  CPA advantages of the per-position encryption reductions
* `fsaead_real_isPure` — real game is heap-independent
* `fsaead_ideal_isPure` — ideal game is heap-independent
* `FSAEAD_Advantage_eq_messaging` — the advantage is the core FS-AEAD advantage
  (`CatCrypt.Crypto.Messaging.FSAEAD_Advantage`) of `toPRG cfg`, `toAEAD cfg`, `toMsgs msgs`
* `fsaead_advantage_le_messaging` — the bound of the core FS-AEAD theorem: PRG advantages of
  the FS-PRG reductions plus AEAD advantages of the encryption reductions

## Proof strategy

The games of this file are the ratchet games of `CatCrypt.Examples.SymmRatchet`, which are the
core FS-AEAD games (`Ratchet_Advantage_eq_fsaead`); the bound is core
`Messaging.fsaead_advantage_le`.

## References

* Canetti et al., "Universally Composable Double Ratchet", ePrint 2022/376
* Perrin & Marlinspike, "The Double Ratchet Algorithm"
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.FSAEAD

open CatCrypt.Core CatCrypt.Crypto CatCrypt.Prob
open CatCrypt.Examples.SymmRatchet
open scoped ENNReal

/-! ## Configuration -/

/-- FS-AEAD configuration.

The chain key evolves via a PRG (producing a message key and new chain key),
and each message key is used for encryption. The PRG is deterministic
(stretch : Word → Word × Word), and encryption uses `EncDef` (Word → Word → Word).

This reuses the SymmRatchet types (`PRGDef`, `EncDef`, `Word`). -/
structure FSAEADConfig (W : Type) where
  /-- Chain key PRG: old_chain_key → (message_key, new_chain_key) -/
  prg : PRGDef W
  /-- Per-message encryption: key → message → ciphertext -/
  enc : EncDef W

variable {W : Type} [CryptoWord W]

/-! ## Real Game -/

/-- FS-AEAD real game: a uniform initial chain key, then for each message the PRG step and
the encryption under the message key; the ratchet game `attack_real` of `cfg`. -/
noncomputable def fsaead_real' (cfg : FSAEADConfig W) (msgs : List W) :
    SPComp (List W × W) :=
  attack_real cfg.prg cfg.enc msgs

/-! ## Ideal Game -/

/-- FS-AEAD ideal game: all ciphertexts random, final chain key random.

Independent of messages and chain key — provides no information to adversary. -/
noncomputable def fsaead_ideal (msgs : List W) : SPComp (List W × W) :=
  attack_ideal msgs

/-! ## Advantage -/

/-- FS-AEAD advantage: distinguishing real from ideal. -/
noncomputable def FSAEAD_Advantage (cfg : FSAEADConfig W) (msgs : List W)
    (A : List W × W → SPComp Bool) : ENNReal :=
  Ratchet_Advantage cfg.prg cfg.enc msgs A

/-! ## IsPure Proofs -/

/-- FS-AEAD real game (with random initial key) is heap-independent: `attack_real` is a
`sample` followed by a `mapLoop` of deterministic steps. -/
theorem fsaead_real_isPure (cfg : FSAEADConfig W) (msgs : List W) :
    SPComp.IsPure (fsaead_real' cfg msgs) := by
  unfold fsaead_real' attack_real
  aesop (rule_sets := [CatCryptRel]) (add safe apply mapLoop_isPure)

/-- FS-AEAD ideal game is heap-independent: `attack_ideal` is a `mapLoop` of samples followed
by a `sample`. -/
theorem fsaead_ideal_isPure (msgs : List W) :
    SPComp.IsPure (fsaead_ideal msgs) := by
  unfold fsaead_ideal attack_ideal
  aesop (rule_sets := [CatCryptRel]) (add safe apply mapLoop_isPure)

/-! ## Security Theorems -/

/-- **FS-AEAD security.** For every adversary `A`, the advantage is at most the sum of the PRG
advantages of the FS-PRG reductions plus the sum over the message positions of the CPA
advantages of the per-position encryption reductions; `forward_secrecy_bound` at
`cfg.prg` and `cfg.enc`. -/
theorem fsaead_security (cfg : FSAEADConfig W) (msgs : List W)
    (A : List W × W → SPComp Bool) :
    FSAEAD_Advantage cfg msgs A ≤
      ∑ i ∈ Finset.range msgs.length, Assumptions.PRG_Advantage cfg.prg.core
          (Messaging.fsprgRed cfg.prg.core msgs.length i
            (Messaging.fsaeadPost cfg.enc.aead (ratchetMsgs msgs) A)) +
        ∑ j ∈ Finset.range msgs.length, CPA_Advantage cfg.enc (msgs.getD j default)
          (Messaging.fsaeadRed cfg.enc.aead (ratchetMsgs msgs) j (msgs.length - (j + 1)) A) :=
  forward_secrecy_bound cfg.prg cfg.enc msgs A

/-- FS-AEAD security for XOR encryption: the CPA term vanishes (one-time pad), leaving the
forward-secure PRG advantage of the distinguisher that encrypts the messages under its keys. -/
theorem fsaead_security_xor (prg : PRGDef Word) (msgs : List Word)
    (A : List Word × Word → SPComp Bool) :
    FSAEAD_Advantage ⟨prg, xorEnc⟩ msgs A ≤
    PRG_Stretch_Advantage prg msgs.length (fun km => (encrypt_keys xorEnc msgs km).bind A) :=
  forward_secrecy_xor_stretch prg msgs A

/-! ## The core FS-AEAD game

The game of this file is the core FS-AEAD confidentiality game
(`CatCrypt.Crypto.Messaging.FSAEAD_Advantage`) of the PRG `toPRG cfg`, the encryption-only
scheme `toAEAD cfg` and the messages `toMsgs msgs`. -/

/-- The chain-key PRG of `cfg` as a core PRG with states and outputs in `W`. -/
def toPRG (cfg : FSAEADConfig W) : Assumptions.PRGDef W (W × W) := cfg.prg.core

/-- The encryption of `cfg` as a core AEAD scheme that ignores the associated data. -/
def toAEAD (cfg : FSAEADConfig W) : Assumptions.AEADDef W W := cfg.enc.aead

/-- The messages of the game as pairs of a plaintext and associated data, the associated data
being the plaintext. -/
def toMsgs (msgs : List W) : List (W × W) := ratchetMsgs msgs

/-- `FSAEAD_Advantage` is the core FS-AEAD advantage of `toPRG cfg`, `toAEAD cfg` and
`toMsgs msgs`. -/
theorem FSAEAD_Advantage_eq_messaging (cfg : FSAEADConfig W) (msgs : List W)
    (A : List W × W → SPComp Bool) :
    FSAEAD_Advantage cfg msgs A =
      Messaging.FSAEAD_Advantage (toPRG cfg) (toAEAD cfg) (toMsgs msgs) A :=
  Ratchet_Advantage_eq_fsaead cfg.prg cfg.enc msgs A

/-- **FS-AEAD security from PRG and one-time encryption security.** For every adversary `A`,
the advantage is at most the PRG advantages of the FS-PRG reductions plus the one-ciphertext
real-or-random advantages of the encryption reductions of the core FS-AEAD theorem. -/
theorem fsaead_advantage_le_messaging (cfg : FSAEADConfig W) (msgs : List W)
    (A : List W × W → SPComp Bool) :
    FSAEAD_Advantage cfg msgs A ≤
      ∑ i ∈ Finset.range (toMsgs msgs).length,
          Assumptions.PRG_Advantage (toPRG cfg) (Messaging.fsprgRed (toPRG cfg)
            (toMsgs msgs).length i (Messaging.fsaeadPost (toAEAD cfg) (toMsgs msgs) A)) +
        ∑ j ∈ Finset.range (toMsgs msgs).length,
          Assumptions.AEAD_Advantage (toAEAD cfg) ((toMsgs msgs).getD j default).1
            ((toMsgs msgs).getD j default).2
            (Messaging.fsaeadRed (toAEAD cfg) (toMsgs msgs) j
              ((toMsgs msgs).length - (j + 1)) A) := by
  rw [FSAEAD_Advantage_eq_messaging]
  exact Messaging.fsaead_advantage_le _ _ _ A

end CatCrypt.Crypto.Signal.FSAEAD
