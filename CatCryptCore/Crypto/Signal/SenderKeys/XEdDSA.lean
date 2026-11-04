/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signal.SenderKeys.SecurityTimed
public import CatCryptCore.Crypto.Signal.Zkgroup.XEdDSA

/-!
# Sender Keys authenticity with XEdDSA signatures in the random-oracle model

`sender_keys_authenticity` bounds the forgery probability of a Sender Keys forger by the
EUF-CMA advantage of a reduction against the abstract signature scheme of `SenderKeysCrypto`.
Signal signs each Sender Keys message with XEdDSA (libsignal `SenderKeyMessage`, signed with
the sender's signing key). This module states authenticity with the signature scheme the
Fiat–Shamir signature of `xeddsaSigma = FiatShamirROM.schnorrSigma RistrettoParam`, XEdDSA in
the random-oracle model, and bounds the forgery probability through the forking reduction of
`schnorr_fs_rom_eufcma` by the discrete-logarithm advantage of an explicit adversary.

The group is `RistrettoParam`, a cyclic group of prime order `l = curve25519_l`; libsignal's
XEdDSA works on the Edwards form of Curve25519, whose group has cofactor 8, and the reduction
from that group to its prime-order subgroup is not part of this statement.

## The forgery experiment

The challenger samples an XEdDSA key pair and plays the sender: it samples the chain key,
computes the ciphertexts of the trace with the key-derivation and AEAD functions of `deps`,
and signs each ciphertext with the signing oracle of the Fiat–Shamir game, whose hash
function is the random oracle. The forger `F` receives the verification key and the signed
broadcasts and outputs a broadcast; it wins when the signature verifies under the random
oracle on a ciphertext the sender did not sign. This is the EUF-CMA experiment of the
Fiat–Shamir game (`FiatShamirROM.eufcmaGame`) against the adversary `senderKeysXAdv deps
trace F`, which runs the sender with its signing oracle and asks `trace.length` signing
queries and no hash query; `SenderKeysX_Forgery_Advantage` is its success probability.

## Main definitions

* `xSignThen` — the signing queries of the sender's ciphertexts, then a continuation
* `senderKeysXRun`, `senderKeysXAdv` — the sender and forger as a Fiat–Shamir adversary
* `SenderKeysX_Forgery_Advantage` — the forgery probability

## Main results

* `isQueryBound₂_senderKeysXRun` — no hash query and `trace.length` signing queries
* `sender_keys_authenticity_xeddsa` — the forgery probability `ε` of every forger satisfies
  `ε'·(ε' − 1/q) ≤ DL_Advantage (dlOfWitness RistrettoParam (extractReduction A))` with
  `ε' = ε − n(n + 1)/q`, `n = trace.length`, `q` the order of ristretto255 and
  `A = senderKeysXAdv deps trace F`

## References

* T. Perrin, *The XEdDSA and VXEdDSA Signature Schemes*, 2016
* D. Pointcheval, J. Stern, *Security Arguments for Digital Signatures and Blind Signatures*,
  J. Cryptology 2000
* Balbás, Collins, Gajland, *WhatsUpp with Sender Keys?*, ASIACRYPT 2023
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.SenderKeys.XEdDSA

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.FiatShamirROM
  CatCrypt.Crypto.OracleForking CatCrypt.Crypto.Signal.Zkgroup
  CatCrypt.Crypto.Signal.Zkgroup.XEdDSA CatCrypt.Crypto.Ristretto255
  CatCrypt.Crypto.Signal.SenderKeys.Dependencies CatCrypt.Crypto.Signal.SenderKeys.Games
open scoped ENNReal

variable {W : Type} [CryptoWord W]

/-- An XEdDSA signature: a commitment and a response. -/
abbrev XSig : Type := xeddsaSigma.Com × xeddsaSigma.Resp

/-- The view of the forger: the verification key and the broadcasts with their signatures,
`none` for a rejected signing attempt. -/
structure XView (W : Type) where
  /-- The sender's verification key. -/
  verifyKey : xeddsaSigma.Stmt
  /-- The broadcasts: iteration, ciphertext, signature. -/
  broadcasts : List (ℕ × W × Option XSig)

/-- A broadcast output by a forger: iteration, ciphertext, signature. -/
abbrev XBroadcast (W : Type) : Type := ℕ × W × XSig

/-- The signature of an answer to a signing query. -/
def sigOf : Answer xeddsaSigma → Option XSig
  | .inl _ => none
  | .inr σ => σ

/-- The signing queries of the ciphertexts `cts` from iteration `j`, with the broadcasts `acc`
so far, followed by the continuation `k` on all broadcasts. -/
def xSignThen {α : Type} (k : List (ℕ × W × Option XSig) → OracleAdv (Query xeddsaSigma W)
    (Answer xeddsaSigma) α) : List W → ℕ → List (ℕ × W × Option XSig) →
    OracleAdv (Query xeddsaSigma W) (Answer xeddsaSigma) α
  | [], _, acc => k acc
  | ct :: cts, j, acc => .query (.inr ct) fun a =>
      xSignThen k cts (j + 1) (acc ++ [(j, ct, sigOf a)])

/-- The sender and the forger `F` as an adversary of the Fiat–Shamir game on the verification
key `pk`: sample the chain key, sign the ciphertexts of the trace with the signing oracle, run
`F` on the view and output its ciphertext and signature. -/
noncomputable def senderKeysXRun (deps : SenderKeysCrypto W) (trace : SenderTrace W)
    (F : XView W → PMF (XBroadcast W)) (pk : xeddsaSigma.Stmt) :
    OracleAdv (Query xeddsaSigma W) (Answer xeddsaSigma) (Forgery xeddsaSigma W) :=
  .rand (PMF.uniformFintype W) fun c =>
    xSignThen (fun bs => .rand (F ⟨pk, bs⟩) fun out => .ret (out.2.1, out.2.2))
      (senderCts deps trace c) 0 []

derive_timed senderKeysXRun

open OracleAdv.Timed in
/-- **Time of the signing queries.** With the continuation of time at most `s` and cost at
most `m`, the costed signing queries of `cts` after the broadcasts `acc` run in time at most
`(2 (|acc| + |cts|) + 8) |cts| + m + s + 2`: per ciphertext one query and the extension of the
list of broadcasts. -/
theorem xSignThen.timeBound_timed {α : Type}
    (k : List (ℕ × W × Option XSig) → OracleAdv.Timed (Query xeddsaSigma W) (Answer xeddsaSigma) α)
    (kCost : List (ℕ × W × Option XSig) → ℕ) {m s : ℕ} (hk : ∀ acc, (k acc).TimeBound s)
    (hkc : ∀ acc, kCost acc ≤ m) (cts : List W) (j : ℕ) (acc : List (ℕ × W × Option XSig)) :
    StepTimeBound (xSignThen.timed k kCost cts j acc)
      ((2 * (acc.length + cts.length) + 8) * cts.length + m + s + 2) := by
  induction cts generalizing j acc with
  | nil =>
    rw [xSignThen.timed.eq_1]
    have := hkc acc
    exact (stepTimeBound_delay (n := m + s + 1) ⟨by omega, (hk acc).mono (by omega)⟩).mono
      (by simp; omega)
  | cons ct cts ih =>
    rw [xSignThen.timed.eq_2]
    have e : (2 * (acc.length + (cts.length + 1)) + 8) * (cts.length + 1) =
        (2 * (acc.length + 1 + cts.length) + 8) * cts.length +
          (2 * (acc.length + cts.length + 1) + 8) := by ring
    refine (stepTimeBound_delay (n := (2 * (acc.length + 1 + cts.length) + 8) * cts.length +
      (2 * (acc.length + cts.length + 1) + 8) + m + s + 1) ?_).mono
      (by simp only [List.length_cons]; omega)
    simp only [StepTimeBound, TimeBound]
    refine ⟨Nat.zero_le _, by omega, fun a => ?_⟩
    obtain ⟨h1, h2⟩ := ih (j + 1) (acc ++ [(j, ct, sigOf a)])
    simp only [List.length_append, List.length_singleton] at h1 h2
    rw [List.append.timedCost_eq]
    generalize (2 * (acc.length + 1 + cts.length) + 8) * cts.length = Q at *
    exact ⟨by omega, h2.mono (by omega)⟩

open OracleAdv.Timed in
/-- **Time of the Sender Keys adversary.** With the forger of cost at most `a`, and the chain
step and `aead_encrypt` of cost at most `t`, the costed adversary on a trace of length `n` runs
in time at most `(2 n + 8) n + 2 n t + 10 n + a + 16`. -/
theorem senderKeysXRun.timeBound_timed (deps : SenderKeysCrypto W) (trace : SenderTrace W)
    (F : XView W → PMF (XBroadcast W)) (FCost : XView W → ℕ) (pk : xeddsaSigma.Stmt)
    (stretchCost : SenderKeysCrypto W → W → ℕ) (ec : W → W → W → W → ℕ) {a t : ℕ}
    (hFc : ∀ v, FCost v ≤ a) (hs : ∀ x, stretchCost deps x ≤ t)
    (he : ∀ k n x p, ec k n x p ≤ t) :
    StepTimeBound (senderKeysXRun.timed deps trace F FCost pk stretchCost ec)
      ((2 * trace.length + 8) * trace.length + 2 * (trace.length * t) + 10 * trace.length +
        a + 16) := by
  unfold senderKeysXRun.timed
  simp only [StepTimeBound, TimeBound]
  refine ⟨Nat.zero_le _, by omega, fun c => ?_⟩
  obtain ⟨hX1, hX2⟩ := xSignThen.timeBound_timed (W := W)
    (fun bs => OracleAdv.Timed.rand (F { verifyKey := pk, broadcasts := bs }) (fun _ => 0)
      fun out => OracleAdv.Timed.ret (out.2.1, out.2.2))
    (fun bs => 1 + FCost { verifyKey := pk, broadcasts := bs }) (m := 1 + a) (s := 1)
    (fun _ => ⟨le_rfl, fun _ => ⟨Nat.zero_le _, trivial⟩⟩)
    (fun bs => by have := hFc { verifyKey := pk, broadcasts := bs }; omega)
    (senderCts deps trace c) 0 []
  have hlen := length_senderCts_le deps trace c
  have h1 := Messaging.fsprgRun.timedCost_le (senderKeysPRG deps) (stretchCost deps) hs
    trace.length c
  have h2 := List.zipWith.timedCost_le (β := W × W)
    (fun k m => (senderKeysAEAD deps).encrypt k m.1 m.2)
    (fun k m => 1 + ec k default m.2 m.1) (k := t + 1)
    (fun k m => by have := he k default m.2 m.1; omega)
    (Messaging.fsprgRun (senderKeysPRG deps) trace.length c).1 trace
  rw [Messaging.fsprgRun_length] at h2
  have h3 := List.length.timedCost_eq trace
  have e1 : trace.length * (t + 3) = trace.length * t + 3 * trace.length := by ring
  have e2 : (t + 1 + 3) * trace.length = trace.length * t + 4 * trace.length := by ring
  have hmul := Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 2
    (show ([] : List (ℕ × W × Option XSig)).length + (senderCts deps trace c).length ≤
      trace.length by simpa using hlen)) 8) hlen
  generalize (2 * (([] : List (ℕ × W × Option XSig)).length + (senderCts deps trace c).length) +
    8) * (senderCts deps trace c).length = P at *
  generalize (2 * trace.length + 8) * trace.length = Q at *
  exact ⟨by omega, hX2.mono (by omega)⟩

/-- The signing queries followed by a continuation without hash queries and with at most `q`
signing queries ask no hash query and at most `cts.length + q` signing queries. -/
theorem isQueryBound₂_xSignThen {α : Type}
    (k : List (ℕ × W × Option XSig) → OracleAdv (Query xeddsaSigma W) (Answer xeddsaSigma) α)
    {q : ℕ}
    (hk : ∀ acc, IsQueryBound₂ (k acc) 0 q) (cts : List W) (j : ℕ)
    (acc : List (ℕ × W × Option XSig)) :
    IsQueryBound₂ (xSignThen k cts j acc) 0 (cts.length + q) := by
  induction cts generalizing j acc with
  | nil => simpa [xSignThen] using hk acc
  | cons ct cts ih =>
    rw [List.length_cons, Nat.add_right_comm]
    exact fun a => ih (j + 1) _

/-- The adversary `senderKeysXRun` asks no hash query and at most `trace.length` signing
queries. -/
theorem isQueryBound₂_senderKeysXRun (deps : SenderKeysCrypto W) (trace : SenderTrace W)
    (F : XView W → PMF (XBroadcast W)) (pk : xeddsaSigma.Stmt) :
    IsQueryBound₂ (senderKeysXRun deps trace F pk) 0 trace.length := fun c => by
  have hlen := length_senderCts_le deps trace c
  have h := isQueryBound₂_xSignThen (W := W)
    (fun bs => .rand (F ⟨pk, bs⟩) fun out => .ret (out.2.1, out.2.2))
    (q := trace.length - (senderCts deps trace c).length)
    (fun _ _ => trivial) (senderCts deps trace c) 0 []
  rwa [Nat.add_sub_cancel' hlen] at h

/-- The sender and the forger `F` as an EUF-CMA adversary of the Fiat–Shamir game of XEdDSA
with no hash query and `trace.length` signing queries. -/
noncomputable def senderKeysXAdv (deps : SenderKeysCrypto W) (trace : SenderTrace W)
    (F : XView W → PMF (XBroadcast W)) : Adversary xeddsaSigma W 0 trace.length where
  run := senderKeysXRun deps trace F
  isQueryBound := isQueryBound₂_senderKeysXRun deps trace F

/-- The forgery probability of `F` against Sender Keys with XEdDSA signatures in the
random-oracle model: the success probability of the EUF-CMA experiment of the Fiat–Shamir game
in which the challenger plays the sender with its signing oracle. -/
noncomputable def SenderKeysX_Forgery_Advantage (deps : SenderKeysCrypto W)
    (trace : SenderTrace W) (F : XView W → PMF (XBroadcast W)) : ℝ≥0∞ :=
  eufcmaAdvantage (senderKeysXAdv deps trace F)

/-- **Sender Keys authenticity with XEdDSA in the random-oracle model.** For every forger `F`,
with `ε` its forgery probability, `n = trace.length` and `q` the order of ristretto255,

  `ε'·(ε' − 1/q) ≤ DL_Advantage (dlOfWitness RistrettoParam (extractReduction A))`,
  `ε' = ε − n(n + 1)/q`,

for the adversary `A = senderKeysXAdv deps trace F` and the forking reduction
`extractReduction A`, which runs `A` at most twice (`schnorr_fs_rom_eufcma` with no hash query
of the adversary). -/
theorem sender_keys_authenticity_xeddsa (deps : SenderKeysCrypto W) (trace : SenderTrace W)
    (F : XView W → PMF (XBroadcast W)) :
    (SenderKeysX_Forgery_Advantage deps trace F -
        ((trace.length * (0 + 1 + trace.length) : ℕ) : ℝ≥0∞) /
          Fintype.card RistrettoParam.Scalar) *
      ((SenderKeysX_Forgery_Advantage deps trace F -
          ((trace.length * (0 + 1 + trace.length) : ℕ) : ℝ≥0∞) /
            Fintype.card RistrettoParam.Scalar) /
          ((0 + 1 : ℕ) : ℝ≥0∞) - 1 / Fintype.card RistrettoParam.Scalar) ≤
      RistrettoParam.DL_Advantage (dlOfWitness RistrettoParam
        (extractReduction (senderKeysXAdv deps trace F))) :=
  schnorr_fs_rom_eufcma (senderKeysXAdv deps trace F)

end CatCrypt.Crypto.Signal.SenderKeys.XEdDSA
