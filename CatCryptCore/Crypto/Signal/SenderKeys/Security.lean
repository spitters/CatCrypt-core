/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signal.SenderKeys.Games
public import CatCryptCore.Crypto.Signatures.EUFCMA

/-!
# Sender Keys security

## Confidentiality

The real game of Sender Keys is the forward-secure AEAD game of core `Messaging.FSAEAD` at the
generator `senderKeysPRG deps`, the cipher `senderKeysAEAD deps` and the trace, followed by the
distinguisher `senderKeysPost deps D`, which generates a key pair, signs the ciphertexts and
runs `D` on the view; the ideal game is the ideal FS-AEAD game followed by the same
distinguisher (`sender_keys_real_bind_eq`, `sender_keys_ideal_bind_eq`). The bound
`sender_keys_security` is then `Messaging.fsaead_advantage_le`: for every distinguisher `D`, with
`n = trace.length`, the advantage is at most

  `∑ i < n, PRG_Advantage (senderKeysPRG deps) (fsprgRed … (fsaeadPost … (senderKeysPost deps D)))`
  `+ ∑ j < n, AEAD_Advantage (senderKeysAEAD deps) pt_j aad_j`
  `      (fsaeadRed … (senderKeysPost deps D))`.

Signatures are real in both games, so no signature assumption enters this bound.

## Authenticity

A forger sees the real view and outputs a broadcast `(iter, ct, σ)`; it wins when `σ`
verifies on `ct` and `ct` is not the ciphertext of a broadcast of the view. The signature
covers the ciphertext only, so the iteration of a forgery is not constrained. The forgery game
is the EUF-CMA game of the forger `senderKeysForger deps trace F`, which samples the chain key,
computes the ciphertexts, asks the signing oracle for their signatures (`signQueries`) and runs
`F` on the view (`sender_keys_authenticity`).

## Main results

* `sender_keys_security` — confidentiality, per distinguisher
* `sender_keys_authenticity` — the forgery probability is at most the EUF-CMA advantage of
  `senderKeysForger`

## References

* Balbás, Collins, Gajland, *WhatsUpp with Sender Keys? Analysis, Improvements and Security
  Proofs*, ASIACRYPT 2023
* J. Alwen, S. Coretti, Y. Dodis, *The Double Ratchet: Security Notions, Proofs, and
  Modularization for the Signal Protocol*, EUROCRYPT 2019, §4.3
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.SenderKeys.Security

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.Assumptions CatCrypt.Crypto.Messaging
open CatCrypt.Crypto.Signal.SenderKeys.Dependencies
open CatCrypt.Crypto.Signal.SenderKeys.Games
open CatCrypt.Crypto.Signatures
open scoped ENNReal

variable {W : Type} [CryptoWord W]

/-! ## Confidentiality -/

/-- The FS-AEAD distinguisher of a Sender Keys distinguisher `D`: on the ciphertexts and the
generator state it generates a key pair, signs the ciphertexts and runs `D` on the view; the
state is not used. -/
noncomputable def senderKeysPost (deps : SenderKeysCrypto W) (D : View W → SPComp Bool)
    (x : List W × W) : SPComp Bool :=
  SPComp.bind (senderKeysSign deps x.1) D

/-- The real game followed by `D` is the real FS-AEAD game followed by `senderKeysPost`. -/
theorem sender_keys_real_bind_eq (deps : SenderKeysCrypto W) (trace : SenderTrace W)
    (D : View W → SPComp Bool) :
    (sender_keys_real deps trace).bind D =
      (fsaead_real (senderKeysPRG deps) (senderKeysAEAD deps) trace).bind
        (senderKeysPost deps D) := by
  simp only [sender_keys_real, fsaead_real, senderKeysPost, senderCts, SPComp.monad_bind_eq,
    SPComp.bind_assoc, SPComp.pure_bind]

/-- The ideal game followed by `D` is the ideal FS-AEAD game followed by `senderKeysPost`. -/
theorem sender_keys_ideal_bind_eq (deps : SenderKeysCrypto W) (trace : SenderTrace W)
    (D : View W → SPComp Bool) :
    (sender_keys_ideal deps trace).bind D =
      (fsaead_ideal (St := W) (C := W) trace).bind (senderKeysPost deps D) := by
  simp only [sender_keys_ideal, fsaead_ideal, senderKeysPost, SPComp.monad_bind_eq,
    SPComp.bind_assoc, SPComp.pure_bind, CatCrypt.Relational.dead_sample]

/-- **Sender Keys confidentiality.** For every trace and every distinguisher `D`, the advantage
of `D` against the real and the ideal Sender Keys games is at most the PRG advantages of the
FS-PRG reductions plus the AEAD advantages of the FS-AEAD reductions, all built from
`senderKeysPost deps D`: the bound of `Messaging.fsaead_advantage_le`. -/
theorem sender_keys_security (deps : SenderKeysCrypto W) (trace : SenderTrace W)
    (D : View W → SPComp Bool) :
    AdvantageA (sender_keys_real deps trace) (sender_keys_ideal deps trace) D ≤
      ∑ i ∈ Finset.range trace.length,
          PRG_Advantage (senderKeysPRG deps) (fsprgRed (senderKeysPRG deps) trace.length i
            (fsaeadPost (senderKeysAEAD deps) trace (senderKeysPost deps D))) +
        ∑ j ∈ Finset.range trace.length,
          AEAD_Advantage (senderKeysAEAD deps) (trace.getD j default).1 (trace.getD j default).2
            (fsaeadRed (senderKeysAEAD deps) trace j (trace.length - (j + 1))
              (senderKeysPost deps D)) := by
  have h : AdvantageA (sender_keys_real deps trace) (sender_keys_ideal deps trace) D =
      FSAEAD_Advantage (senderKeysPRG deps) (senderKeysAEAD deps) trace
        (senderKeysPost deps D) := by
    simp only [AdvantageA, FSAEAD_Advantage, sender_keys_real_bind_eq, sender_keys_ideal_bind_eq]
  rw [h]
  exact fsaead_advantage_le _ _ trace _

/-! ## Authenticity -/

/-- The signed pair `(ct, σ)` of a broadcast `(iter, ct, σ)`. -/
def signedPair (b : WireBroadcast W) : W × W := (b.2.1, b.2.2)

/-- The oracle program that asks the signing oracle for a signature on each ciphertext in turn
and returns the broadcasts `(j + k, ct_k, σ_k)`. -/
def signQueries : List W → ℕ → OracleProg W W (List (WireBroadcast W))
  | [], _ => .pure []
  | ct :: cts, j => .query ct fun σ =>
      (signQueries cts (j + 1)).bind fun rest => .pure ((j, ct, σ) :: rest)

/-- Forgery game: the real game, then the forger `F` on its view; `true` when the output
verifies on a ciphertext absent from the view. -/
noncomputable def senderKeysForgeryGame (deps : SenderKeysCrypto W) (trace : SenderTrace W)
    (F : View W → SPComp (WireBroadcast W)) : SPComp Bool :=
  SPComp.bind (sender_keys_real deps trace) fun v =>
    SPComp.bind (F v) fun out =>
      SPComp.pure (deps.verify v.verifyKey out.2.1 out.2.2 &&
        !(v.broadcasts.map fun b => b.2.1).contains out.2.1)

/-- Forgery probability of `F`: the probability that the forgery game outputs `true`, at the
empty heap. -/
noncomputable def SenderKeysForgery_Advantage (deps : SenderKeysCrypto W)
    (trace : SenderTrace W) (F : View W → SPComp (WireBroadcast W)) : ℝ≥0∞ :=
  prTrue (senderKeysForgeryGame deps trace F) Heap.empty

/-- The EUF-CMA reduction on the verification key `vk`, for a forger `F` given as a
computation tree: sample a chain key, compute the ciphertexts of the trace, obtain their
signatures from the signing oracle, run `F` on the view and output the signed pair of its
broadcast. -/
noncomputable def senderKeysForgeryRed (deps : SenderKeysCrypto W) (trace : SenderTrace W)
    (F : View W → SPTree (WireBroadcast W)) (vk : W) : OracleProg W W (W × W) :=
  .lift (SPTree.compile (SPTree.sample W inferInstance ⟨default⟩ fun c => SPTree.ret c)) fun c =>
    (signQueries (senderCts deps trace c) 0).bind fun bs =>
      .lift (SPTree.compile (F { verifyKey := vk, broadcasts := bs })) fun out =>
        .pure (out.2.1, out.2.2)

/-- The EUF-CMA forger built from `F`, running `senderKeysForgeryRed`. -/
noncomputable def senderKeysForger (deps : SenderKeysCrypto W) (trace : SenderTrace W)
    (F : View W → SPTree (WireBroadcast W)) : EUFCMAAdversary W W W W where
  run := senderKeysForgeryRed deps trace F

/-- The compiled uniform-sample tree of `W` is the uniform sample of `W`. -/
theorem compile_sample_ret_eq_sample :
    SPTree.compile (SPTree.sample W inferInstance ⟨default⟩ fun c => SPTree.ret c) =
      SPComp.sample W := by
  simp only [SPTree.compile]
  exact SPComp.bind_pure _

/-- Running `signQueries` against the logged signing oracle signs the ciphertexts as
`signCts` does, and its log is the list of signed pairs of the broadcasts. -/
theorem runLog_signQueries (deps : SenderKeysCrypto W) (sk : W) (cts : List W) (j : ℕ) :
    (signQueries cts j).runLog (deps.sign sk) =
      SPComp.bind (signCts deps sk cts j) fun bs => SPComp.pure (bs, bs.map signedPair) := by
  induction cts generalizing j with
  | nil => simp [signQueries, signCts, OracleProg.runLog, SPComp.pure_bind]
  | cons ct cts ih =>
    simp only [OracleProg.runLog] at ih
    simp only [signQueries, signCts, OracleProg.runLog, OracleProg.runWith_query,
      OracleProg.logging, OracleProg.runWith_bind, OracleProg.runWith_pure, ih,
      SPComp.bind_assoc, SPComp.pure_bind]
    simp [signedPair]

/-- The forgery game of the compiled forger `F` is the EUF-CMA game of
`senderKeysForger deps trace F`. -/
theorem senderKeysForgeryGame_eq_eufcmaGame (deps : SenderKeysCrypto W)
    (trace : SenderTrace W) (F : View W → SPTree (WireBroadcast W)) :
    senderKeysForgeryGame deps trace (fun v => (F v).compile) =
      eufcmaGame (senderKeysSigScheme deps) (senderKeysForger deps trace F) := by
  unfold senderKeysForgeryGame sender_keys_real senderKeysSign eufcmaGame senderKeysForger
    senderKeysForgeryRed senderKeysSigScheme
  simp only [OracleProg.runLog] at *
  simp only [SPComp.bind_assoc, SPComp.pure_bind, OracleProg.runWith_lift,
    OracleProg.runWith_bind, OracleProg.runWith_pure, compile_sample_ret_eq_sample]
  rw [SPComp.isPure_bind_comm_left (SPComp.sample W) deps.keygen _ (SPComp.sample_isPure _)]
  refine congrArg _ (funext fun ks => congrArg _ (funext fun c => ?_))
  have h := runLog_signQueries deps ks.2 (senderCts deps trace c) 0
  simp only [OracleProg.runLog] at h
  simp only [h, SPComp.bind_assoc, SPComp.pure_bind, List.append_nil, List.map_map,
    signedPair, Function.comp_def]

/-- **Sender Keys authenticity.** For every forger `F` with the sender's view, given as a
computation tree, the probability that `F` outputs a broadcast whose signature verifies on a
ciphertext the sender did not broadcast is at most the EUF-CMA advantage of
`senderKeysForger deps trace F` against `senderKeysSigScheme deps`. -/
theorem sender_keys_authenticity (deps : SenderKeysCrypto W) (trace : SenderTrace W)
    (F : View W → SPTree (WireBroadcast W)) :
    SenderKeysForgery_Advantage deps trace (fun v => (F v).compile) ≤
      eufcmaAdvantage (senderKeysSigScheme deps) (senderKeysForger deps trace F) :=
  le_of_eq (by
    unfold SenderKeysForgery_Advantage eufcmaAdvantage
    rw [senderKeysForgeryGame_eq_eufcmaGame])

end CatCrypt.Crypto.Signal.SenderKeys.Security
