/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signal.SenderKeys.Dependencies
public import CatCryptCore.Crypto.Messaging.FSAEAD

/-!
# Sender Keys games

The real and the ideal game of Sender Keys confidentiality. A trace is the list of messages
`(plaintext, aad)` the sender broadcasts; the adversary sees the verification key and the
broadcasts `(iteration, ciphertext, signature)`.

* Real (`sender_keys_real`): a uniform chain key; message `j` is encrypted under the `j`-th
  message key of the chain (`senderCts`, the encryptions `Messaging.encAll` under the outputs
  `Messaging.fsprgRun` of the generator `senderKeysPRG`); a key pair is generated and the
  ciphertexts are signed (`senderKeysSign`).
* Ideal (`sender_keys_ideal`): uniform ciphertexts, signed in the same way.

Signatures are real in both games: confidentiality is stated against the forward-secure AEAD
game of core `Messaging.FSAEAD`, and authenticity separately against EUF-CMA.

## Main definitions

* `SenderTrace`, `WireBroadcast`, `View`
* `senderCts` — the ciphertexts of a trace from a chain key
* `signCts`, `senderKeysSign` — the signing of a list of ciphertexts and the view
* `sender_keys_real`, `sender_keys_ideal`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.SenderKeys.Games

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.Signal.SenderKeys.Dependencies
open scoped ENNReal

variable {W : Type} [CryptoWord W]

/-- A message of the sender: `(plaintext, aad)`. -/
abbrev SenderInput (W : Type) : Type := W × W

/-- The messages of a Sender Keys session, in order. -/
abbrev SenderTrace (W : Type) : Type := List (SenderInput W)

/-- A broadcast on the wire: `(iteration, ciphertext, signature)`. -/
abbrev WireBroadcast (W : Type) : Type := ℕ × W × W

/-- The view of the adversary: the verification key of the sender and the broadcasts. -/
structure View (W : Type) where
  /-- The verification key of the sender. -/
  verifyKey : W
  /-- The broadcasts in order. -/
  broadcasts : List (WireBroadcast W)

/-- The ciphertexts of the trace from the chain key `c`: message `j` encrypted under the
`j`-th message key of the chain. -/
def senderCts (deps : SenderKeysCrypto W) (trace : SenderTrace W) (c : W) : List W :=
  Messaging.encAll (senderKeysAEAD deps) (Messaging.fsprgRun (senderKeysPRG deps) trace.length c).1
    trace

/-- The broadcasts of the ciphertexts `cts` from iteration `j`, each signed with `sk`. -/
noncomputable def signCts (deps : SenderKeysCrypto W) (sk : W) :
    List W → ℕ → SPComp (List (WireBroadcast W))
  | [], _ => SPComp.pure []
  | ct :: cts, j => SPComp.bind (deps.sign sk ct) fun σ =>
      SPComp.bind (signCts deps sk cts (j + 1)) fun rest => SPComp.pure ((j, ct, σ) :: rest)

/-- The view of the ciphertexts `cts`: a fresh key pair and the signed broadcasts. -/
noncomputable def senderKeysSign (deps : SenderKeysCrypto W) (cts : List W) : SPComp (View W) :=
  SPComp.bind deps.keygen fun ks =>
    SPComp.bind (signCts deps ks.2 cts 0) fun bs =>
      SPComp.pure { verifyKey := ks.1, broadcasts := bs }

/-- The real game: the signed ciphertexts of the trace from a uniform chain key. -/
noncomputable def sender_keys_real (deps : SenderKeysCrypto W) (trace : SenderTrace W) :
    SPComp (View W) :=
  SPComp.bind (SPComp.sample W) fun c => senderKeysSign deps (senderCts deps trace c)

/-- The ideal game: `trace.length` uniform ciphertexts, signed. -/
noncomputable def sender_keys_ideal (deps : SenderKeysCrypto W) (trace : SenderTrace W) :
    SPComp (View W) :=
  SPComp.bind (SPComp.sample (Fin trace.length → W)) fun v => senderKeysSign deps (List.ofFn v)

theorem signCts_isPure (deps : SenderKeysCrypto W) (sk : W) (cts : List W) (j : ℕ) :
    SPComp.IsPure (signCts deps sk cts j) := by
  induction cts generalizing j with
  | nil => exact SPComp.pure_isPure _
  | cons ct cts ih =>
    exact SPComp.bind_isPure (deps.sign_isPure _ _) fun _ =>
      SPComp.bind_isPure (ih _) fun _ => SPComp.pure_isPure _

theorem senderKeysSign_isPure (deps : SenderKeysCrypto W) (cts : List W) :
    SPComp.IsPure (senderKeysSign deps cts) :=
  SPComp.bind_isPure deps.keygen_isPure fun _ =>
    SPComp.bind_isPure (signCts_isPure _ _ _ _) fun _ => SPComp.pure_isPure _

theorem sender_keys_real_isPure (deps : SenderKeysCrypto W) (trace : SenderTrace W) :
    SPComp.IsPure (sender_keys_real deps trace) :=
  SPComp.bind_isPure (SPComp.sample_isPure _) fun _ => senderKeysSign_isPure _ _

theorem sender_keys_ideal_isPure (deps : SenderKeysCrypto W) (trace : SenderTrace W) :
    SPComp.IsPure (sender_keys_ideal deps trace) :=
  SPComp.bind_isPure (SPComp.sample_isPure _) fun _ => senderKeysSign_isPure _ _

/-- The sender's trace has at least as many messages as `senderCts` has ciphertexts. -/
theorem length_senderCts_le (deps : SenderKeysCrypto W) (trace : SenderTrace W) (c : W) :
    (senderCts deps trace c).length ≤ trace.length := by
  simp [senderCts, Messaging.encAll]

end CatCrypt.Crypto.Signal.SenderKeys.Games
