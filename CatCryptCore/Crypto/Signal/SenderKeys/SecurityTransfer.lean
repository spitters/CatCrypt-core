/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signal.SenderKeys.Security
public import CatCryptCore.Crypto.UCConcrete
public import CatCryptCore.Crypto.UCDSL

/-!
# Sender Keys: concrete UC statement

The real and the ideal Sender Keys games are heap-independent (`PureGame` instances), and
`sender_keys_security` bounds the advantage of every distinguisher `D` by
`senderKeysGameBound deps trace () D` (`GameAdvBoundC` instance). The concrete UC statement
`sender_keys_uc_secure` follows by `UCFromGameC.uc`.

## Main results

* `sender_keys_uc_secure` — the real game concretely UC-emulates the ideal game, with the bound
  of adversary `A` and environment `Z` the confidentiality bound at the distinguisher
  `envReduction A Z`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.SenderKeys.SecurityTransfer

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCDSL
open CatCrypt.Crypto.Assumptions CatCrypt.Crypto.Messaging
open CatCrypt.Crypto.Signal.SenderKeys.Dependencies
open CatCrypt.Crypto.Signal.SenderKeys.Games
open CatCrypt.Crypto.Signal.SenderKeys.Security
open scoped ENNReal

variable {W : Type} [CryptoWord W]

/-- The confidentiality bound of `sender_keys_security` at the distinguisher `D`. -/
noncomputable def senderKeysGameBound (deps : SenderKeysCrypto W) (trace : SenderTrace W) :
    Unit → (View W → SPComp Bool) → ℝ≥0∞ :=
  fun _ D =>
    ∑ i ∈ Finset.range trace.length,
        PRG_Advantage (senderKeysPRG deps) (fsprgRed (senderKeysPRG deps) trace.length i
          (fsaeadPost (senderKeysAEAD deps) trace (senderKeysPost deps D))) +
      ∑ j ∈ Finset.range trace.length,
        AEAD_Advantage (senderKeysAEAD deps) (trace.getD j default).1 (trace.getD j default).2
          (fsaeadRed (senderKeysAEAD deps) trace j (trace.length - (j + 1))
            (senderKeysPost deps D))

instance sender_keys_real_pureGame (deps : SenderKeysCrypto W) (trace : SenderTrace W) :
    PureGame (fun _ : Unit => sender_keys_real deps trace) :=
  ⟨fun _ => sender_keys_real_isPure deps trace⟩

instance sender_keys_ideal_pureGame (deps : SenderKeysCrypto W) (trace : SenderTrace W) :
    PureGame (fun _ : Unit => sender_keys_ideal deps trace) :=
  ⟨fun _ => sender_keys_ideal_isPure deps trace⟩

/-- Every distinguisher `D` separates the Sender Keys games by at most
`senderKeysGameBound deps trace () D` (`sender_keys_security`). -/
instance sender_keys_gameAdvBoundC (deps : SenderKeysCrypto W) (trace : SenderTrace W) :
    GameAdvBoundC (fun _ : Unit => sender_keys_real deps trace)
      (fun _ : Unit => sender_keys_ideal deps trace) (senderKeysGameBound deps trace) :=
  ⟨fun _ D => sender_keys_security deps trace D⟩

/-- **Sender Keys concrete UC emulation.** The real Sender Keys game concretely UC-emulates the
ideal game (uniform ciphertexts, signed with the signing key); the bound for adversary `A` and
environment `Z` is the confidentiality bound at the distinguisher `envReduction A Z`. -/
theorem sender_keys_uc_secure (deps : SenderKeysCrypto W) (trace : SenderTrace W) (V : Type) :
    UCEmulatesCSim (UCSpec.ofGame Unit (View W) V)
      (UCProtocol.ofGame fun _ => sender_keys_real deps trace)
      (UCProtocol.ofGame fun _ => sender_keys_ideal deps trace) id
      (gameUCBound (senderKeysGameBound deps trace)) :=
  UCFromGameC.uc

end CatCrypt.Crypto.Signal.SenderKeys.SecurityTransfer
