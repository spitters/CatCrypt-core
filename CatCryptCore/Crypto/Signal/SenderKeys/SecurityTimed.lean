/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signal.SenderKeys.Security
public import CatCryptCore.Crypto.Signatures.OracleProgTimed
public import CatCryptCore.Tactics.DeriveReduction

/-!
# Running time of the Sender Keys reductions

Two reductions are defined in `Security`: the FS-AEAD distinguisher `senderKeysPost`, which
generates a key pair, signs the ciphertexts and runs the distinguisher, and the EUF-CMA
reduction `senderKeysForgeryRed`, which samples a chain key, computes the ciphertexts, asks
the signing oracle once per ciphertext (`signQueries`) and runs the forger once. Their costed
forms and erasure theorems come from `derive_reduction` and `derive_timed`; the reductions of
the confidentiality bound into which `senderKeysPost` is substituted are the core reductions
`Messaging.fsprgRed` and `Messaging.fsaeadRed`, with their own time theorems.

## Main results

* `senderKeysPost.tree.timeBound_timed` — with key generation of time `K`, signing of time
  `S` and cost `c`, and the distinguisher of time `T` and cost `a`, the costed distinguisher on
  `n` ciphertexts runs in time at most `K + n (S + c + 4) + T + a + 4`
* `signQueries.timeBound_timed` — `n` signing queries run in time `4 n + 1`
* `senderKeysForgeryRed.timeBound_timed` — with the forger of time `T` and cost `a`, and the
  primitives of cost at most `t`, the costed reduction on a trace of length `n` runs in time at
  most `T + a + 2 n t + 16 n + 20`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.SenderKeys.Security

open CatCrypt.Core CatCrypt.Crypto.Messaging
open CatCrypt.Crypto.Signal.SenderKeys.Dependencies CatCrypt.Crypto.Signal.SenderKeys.Games

variable {W : Type} [CryptoWord W]

/-! ## The FS-AEAD distinguisher -/

derive_reduction senderKeysPost (adv := D)

/-- The costed signing of `n` ciphertexts, with signing of time at most `S` and cost at most
`c`, runs in time at most `n (S + c + 4) + 1`. -/
theorem signCts.tree.timeBound_timed (deps : SenderKeysCrypto W) (sk : W)
    (sign : W → W → SPTree.Timed W) (signCost : W → W → ℕ) {S c : ℕ}
    (hs : ∀ a b, (sign a b).time ≤ S) (hc : ∀ a b, signCost a b ≤ c) (cts : List W) (j : ℕ) :
    SPTree.Timed.stepTime (Games.signCts.tree.timed deps sk cts j sign signCost) ≤
      cts.length * (S + c + 4) + 1 := by
  induction cts generalizing j with
  | nil => simp [Games.signCts.tree.timed.eq_1, SPTree.Timed.delay, SPTree.Timed.stepTime,
      SPTree.Timed.time_ret]
  | cons ct cts ih =>
    rw [Games.signCts.tree.timed.eq_2, SPTree.Timed.stepTime_delay, SPTree.Timed.stepTime_delay]
    have := ih (j + 1)
    set R := Games.signCts.tree.timed deps sk cts (j + 1) sign signCost
    have hR : ∀ σ : W, SPTree.Timed.stepTime (R.2.bind fun bs =>
        ((0 : ℕ), SPTree.Timed.ret ((j, ct, σ) :: bs))) ≤ R.2.time := fun σ =>
      (SPTree.Timed.stepTime_bind_le R.2 _ 0 fun _ => by
        simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret]).trans (Nat.add_zero _).le
    have hb := SPTree.Timed.stepTime_bind_le (sign sk ct)
      (fun σ => SPTree.Timed.delay (2 + R.1) (R.2.bind fun bs =>
        ((0 : ℕ), SPTree.Timed.ret ((j, ct, σ) :: bs))))
      (SPTree.Timed.stepTime R + 2) fun σ => by
        rw [SPTree.Timed.stepTime_delay]
        have := hR σ
        simp only [SPTree.Timed.stepTime] at this ⊢
        omega
    have := hs sk ct
    have := hc sk ct
    simp only [List.length_cons]
    rw [Nat.succ_mul]
    omega

/-- **Time of the FS-AEAD distinguisher of Sender Keys.** With key generation of time at most
`K`, signing of time at most `S` and cost at most `c`, and the distinguisher `D` of time at
most `T` and cost at most `a`, the costed distinguisher on the ciphertexts `x.1` runs in time
at most `K + |x.1| (S + c + 4) + T + a + 4`. -/
theorem senderKeysPost.tree.timeBound_timed (deps : SenderKeysCrypto W)
    (D : View W → SPTree.Timed Bool) (DCost : View W → ℕ) (x : List W × W)
    (keygen : SPTree.Timed (W × W)) (sign : W → W → SPTree.Timed W) (signCost : W → W → ℕ)
    {K S c T a : ℕ} (hk : keygen.time ≤ K) (hs : ∀ a b, (sign a b).time ≤ S)
    (hc : ∀ a b, signCost a b ≤ c) (hD : ∀ v, (D v).time ≤ T) (hDc : ∀ v, DCost v ≤ a) :
    SPTree.Timed.stepTime (senderKeysPost.tree.timed deps D DCost x keygen sign signCost) ≤
      K + x.1.length * (S + c + 4) + T + a + 4 := by
  rw [senderKeysPost.tree.timed]
  set B := keygen.bind fun ks => SPTree.Timed.delay
      (1 + (Games.signCts.tree.timed deps ks.2 x.1 0 sign signCost).1)
      ((Games.signCts.tree.timed deps ks.2 x.1 0 sign signCost).2.bind fun bs =>
        ((0 : ℕ), SPTree.Timed.ret ({ verifyKey := ks.1, broadcasts := bs } : View W)))
  have h1 : SPTree.Timed.stepTime B ≤ K + (x.1.length * (S + c + 4) + 2) :=
    (SPTree.Timed.stepTime_bind_le keygen _ (x.1.length * (S + c + 4) + 2) fun ks => by
      rw [SPTree.Timed.stepTime_delay]
      have hS := signCts.tree.timeBound_timed deps ks.2 sign signCost hs hc x.1 0
      have := SPTree.Timed.stepTime_bind_le
        (Games.signCts.tree.timed deps ks.2 x.1 0 sign signCost).2
        (fun bs => ((0 : ℕ), SPTree.Timed.ret ({ verifyKey := ks.1, broadcasts := bs } : View W)))
        0 fun _ => by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret]
      simp only [SPTree.Timed.stepTime] at this hS ⊢
      omega).trans (Nat.add_le_add_right hk _)
  have h2 := SPTree.Timed.stepTime_bind_le B.2 (fun v => (1 + DCost v, D v)) (T + a + 1)
    fun v => by
      have := hD v; have := hDc v
      simp only [SPTree.Timed.stepTime]; omega
  rw [SPTree.Timed.stepTime_delay]
  simp only [SPTree.Timed.stepTime] at h1 h2 ⊢
  omega

/-! ## The EUF-CMA reduction -/

derive_timed senderKeysForgeryRed

omit [CryptoWord W] in
open OracleProg.Timed in
/-- The costed signing queries on a list of `n` ciphertexts run in time `4 n + 1`. -/
theorem signQueries.timeBound_timed (cts : List W) (j : ℕ) :
    StepTimeBound (signQueries.timed cts j) (4 * cts.length + 1) := by
  induction cts generalizing j with
  | nil =>
    rw [signQueries.timed.eq_1]
    simp [delay, StepTimeBound, TimeBound]
  | cons ct cts ih =>
    rw [signQueries.timed.eq_2]
    obtain ⟨hR1, hR2⟩ := ih (j + 1)
    simp only [delay, StepTimeBound, TimeBound, List.length_cons]
    refine ⟨by omega, by omega, fun o => ?_⟩
    obtain ⟨hB1, hB2⟩ := timeBound_bind (n := 0) hR2
      (f := fun rest => ((0 : ℕ),
        (OracleProg.Timed.pure ((j, ct, o) :: rest) :
          OracleProg.Timed W W (List (WireBroadcast W)))))
      (fun _ => ⟨le_rfl, trivial⟩)
    exact ⟨by omega, hB2.mono (by omega)⟩

open OracleProg.Timed in
/-- **Time of the Sender Keys EUF-CMA reduction.** For a costed forger `F` of time at most `T`
with cost companion at most `a`, and the chain step and `aead_encrypt` of cost at most `t`,
the costed reduction on a trace of length `n` runs in time at most
`T + a + 2 n t + 16 n + 20`. -/
theorem senderKeysForgeryRed.timeBound_timed (deps : SenderKeysCrypto W)
    (trace : SenderTrace W) (F : View W → SPTree.Timed (WireBroadcast W))
    (FCost : View W → ℕ) (vk : W) (stretchCost : SenderKeysCrypto W → W → ℕ)
    (ec : W → W → W → W → ℕ) {T a t : ℕ}
    (hF : ∀ v, (F v).time ≤ T) (hFc : ∀ v, FCost v ≤ a) (hs : ∀ x, stretchCost deps x ≤ t)
    (he : ∀ k n x p, ec k n x p ≤ t) :
    StepTimeBound (senderKeysForgeryRed.timed deps trace F FCost vk stretchCost ec)
      (T + a + 2 * (trace.length * t) + 16 * trace.length + 20) := by
  simp only [senderKeysForgeryRed.timed, StepTimeBound, TimeBound, SPTree.Timed.time_sample,
    SPTree.Timed.time_ret, Nat.add_zero]
  have hs0 : (Finset.univ.sup fun _ : W => (0 : ℕ)) = 0 := by simp
  rw [hs0]
  refine ⟨Nat.zero_le _, by omega, fun b => ?_⟩
  obtain ⟨hP1, hP2⟩ := signQueries.timeBound_timed (senderCts deps trace b) 0
  have hlen := length_senderCts_le deps trace b
  obtain ⟨hQ1, hQ2⟩ := timeBound_bind (n := 1 + a + T) hP2
    (f := fun bs => (1 + FCost { verifyKey := vk, broadcasts := bs },
      lift (WireBroadcast W) (F { verifyKey := vk, broadcasts := bs }) (fun _ => 0)
        fun out => OracleProg.Timed.pure (out.2.1, out.2.2)))
    (fun bs => by
      have := hF { verifyKey := vk, broadcasts := bs }
      have := hFc { verifyKey := vk, broadcasts := bs }
      exact ⟨by omega, by omega, fun _ => ⟨Nat.zero_le _, trivial⟩⟩)
  have h1 := fsprgRun.timedCost_le (senderKeysPRG deps) (stretchCost deps) hs trace.length b
  have h2 := List.zipWith.timedCost_le (β := W × W)
    (fun k m => (senderKeysAEAD deps).encrypt k m.1 m.2)
    (fun k m => 1 + ec k default m.2 m.1) (k := t + 1)
    (fun k m => by have := he k default m.2 m.1; omega)
    (fsprgRun (senderKeysPRG deps) trace.length b).1 trace
  rw [fsprgRun_length] at h2
  have h3 := List.length.timedCost_eq trace
  have e1 : trace.length * (t + 3) = trace.length * t + 3 * trace.length := by ring
  have e2 : (t + 1 + 3) * trace.length = trace.length * t + 4 * trace.length := by ring
  exact ⟨by omega, hQ2.mono (by omega)⟩

end CatCrypt.Crypto.Signal.SenderKeys.Security
