/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.SecurityDefs
import CatCryptCore.Prob.XorBij
import CatCryptCore.Tactics

/-!
# Basic Hash Protocol: Perfect Authentication and the Unlinkability Counterexample

The Basic Hash RFID protocol from the proof-ladders benchmark. A tag holding a
key `k` answers a reader challenge nonce `n` with the pair `(n, H(k, n))`; the
reader recomputes `H(k, n)` and accepts iff it matches.

This file establishes the two distinctive facts of the challenge for the XOR
hash `H(k, n) = k ⊕ n`:

1. **Perfect authentication.** For a *bijection family* hash — one where
   `k ↦ H(k, n)` is a bijection for each fixed nonce `n` — the authentication
   advantage of every adversary is exactly `0`. The XOR hash is such a family
   (`k ↦ k ⊕ n` is a bijection), so it authenticates perfectly. The argument is
   the bijection-coupling technique shared with `CatCrypt.Examples.OTP` and
   `CatCrypt.Examples.PRF`: over a uniform key, `H(k, n)` is uniform and
   independent of `n`, coupling the real game with a fresh uniform sample.

2. **The unlinkability counterexample.** Perfect single-session authentication
   does *not* give multi-session unlinkability. The XOR outputs across two
   sessions are correlated: with a shared key,
   `H(k, n₁) ⊕ H(k, n₂) = n₁ ⊕ n₂` *deterministically*. A distinguisher testing
   this fixed relation succeeds with certainty against the shared-key (real)
   game, whereas against independent keys the same relation can fail — so the
   two unlinkability games are distinguishable. This is why unlinkability needs a
   genuine PRF, not merely a bijection family.

## Main definitions

* `HashFunc` — a keyed hash function `Word → Word → Word`.
* `xorHash` — the XOR hash `H(k, n) = k ⊕ n`.
* `auth_real` / `auth_ideal` — the authentication real/ideal games.
* `PerfectAuth` — perfect authentication as an `rHoare` coupling.
* `unlink_real` / `unlink_ideal` — the two-session unlinkability games.
* `unlink_distinguisher` — the correlation-testing distinguisher.

## Main results

* `auth_perfect_bij` — any bijection-family hash authenticates perfectly.
* `auth_perfect_xor` — the XOR hash authenticates perfectly.
* `auth_zero_advantage_xor` — zero authentication advantage for the XOR hash.
* `xorHash_correlated` — `H(k,n₁) ⊕ H(k,n₂) = n₁ ⊕ n₂` (the structural leak).
* `unlink_real_always_true` — the distinguisher always accepts the real game.
* `unlink_ideal_not_always_true` — the distinguisher can reject the ideal game.

## References

* proof-ladders protocol-ladder benchmark
* [Vaudenay, On Privacy Models for RFID]
* [Rosulek, The Joy of Cryptography, §6 (pseudorandom functions)]
-/

namespace CatCrypt.Examples.BasicHash

open CatCrypt.Core
open CatCrypt.Crypto
open CatCrypt.Prob
open CatCrypt.Prob.XorBij
open CatCrypt.Relational
open scoped ENNReal

/-! ## Type Definitions -/

/-- Word type (base type for keys, nonces, responses). -/
abbrev Word := Bool

/-! ## Hash Function -/

/-- A keyed hash function for the Basic Hash protocol. -/
structure HashFunc where
  /-- The hash function: key → nonce → response. -/
  h : Word → Word → Word

/-! ## Protocol Operations -/

/-- Tag session: sample a fresh nonce and compute the hash response. -/
noncomputable def tag_session (H : HashFunc) (k : Word) : SPComp (Word × Word) := do
  let n ← SPComp.sample Word
  SPComp.pure (n, H.h k n)

/-- Reader verification: check that the response matches the expected hash. -/
def reader_verify (H : HashFunc) (k : Word) (n : Word) (r : Word) : Bool :=
  decide (H.h k n = r)

/-! ## XOR Hash -/

/-- XOR-based hash: `H(k, n) = k ⊕ n`.

This is a perfect single-query hash (a bijection family) but fails
unlinkability across sessions. -/
def xorHash : HashFunc where
  h k n := xor k n

/-- XOR hash verification is correct: a tag's own response always verifies. -/
theorem xorHash_verify_correct (k n : Word) :
    reader_verify xorHash k n (xorHash.h k n) = true := by
  simp [reader_verify, xorHash]

/-! ## Authentication Game -/

/-- Authentication real game: sample a key and compute `H(k, n)` for the
challenge nonce `n`. -/
noncomputable def auth_real (H : HashFunc) (n : Word) : SPComp Word := do
  let k ← SPComp.sample Word
  SPComp.pure (H.h k n)

/-- Authentication ideal game: return a uniformly random response. -/
noncomputable def auth_ideal : SPComp Word :=
  SPComp.sample Word

/-- Authentication advantage: distinguishing a real response from random. -/
noncomputable def Auth_Advantage (H : HashFunc) (n : Word)
    (A : Word → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (auth_real H n) auth_ideal A

/-- Perfect authentication: the real and ideal games are perfectly
indistinguishable (coupled by `eqPost`). -/
def PerfectAuth (H : HashFunc) : Prop :=
  ∀ n, rHoare eqPre (auth_real H n) auth_ideal eqPost

/-! ## Authentication Security Proofs -/

/-- Any hash whose per-nonce map `k ↦ H(k, n)` is a bijection achieves perfect
authentication: the bijection carries the uniform key onto a uniform output,
coupling the real game with the ideal uniform sample. -/
theorem auth_perfect_bij (H : HashFunc)
    (hbij : ∀ n, Function.Bijective (H.h · n)) : PerfectAuth H :=
  fun n => rHoare_sample_bij (Equiv.ofBijective _ (hbij n))

/-- The XOR hash has perfect authentication: `k ↦ k ⊕ n` is a bijection for
each nonce `n`. -/
theorem auth_perfect_xor : PerfectAuth xorHash :=
  fun n => rHoare_sample_bij (boolXorBij n)

/-- Perfect authentication implies zero advantage for every adversary. -/
theorem auth_zero_advantage (H : HashFunc) (hPerf : PerfectAuth H) :
    ∀ n A, Auth_Advantage H n A = 0 :=
  fun n A => advantage_zero_of_rHoare _ _ (hPerf n) A

/-- **The XOR hash authenticates perfectly**: zero authentication advantage for
every nonce and every adversary. -/
theorem auth_zero_advantage_xor :
    ∀ n A, Auth_Advantage xorHash n A = 0 :=
  auth_zero_advantage xorHash auth_perfect_xor

/-! ## Unlinkability Game (2 Sessions)

Unlinkability asks whether an adversary can tell if two sessions share a key.
The real game uses one key for both sessions; the ideal game uses independent
keys. Perfect authentication constrains only a *single* session, and — as the
counterexample below shows — says nothing about correlation across sessions.
-/

/-- Unlinkability real game: one shared key for both sessions. -/
noncomputable def unlink_real (H : HashFunc) (n1 n2 : Word) :
    SPComp (Word × Word) := do
  let k ← SPComp.sample Word
  SPComp.pure (H.h k n1, H.h k n2)

/-- Unlinkability ideal game: independent keys per session. -/
noncomputable def unlink_ideal (H : HashFunc) (n1 n2 : Word) :
    SPComp (Word × Word) := do
  let k1 ← SPComp.sample Word
  let k2 ← SPComp.sample Word
  SPComp.pure (H.h k1 n1, H.h k2 n2)

/-- Unlinkability advantage. -/
noncomputable def Unlink_Advantage (H : HashFunc) (n1 n2 : Word)
    (A : Word × Word → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (unlink_real H n1 n2) (unlink_ideal H n1 n2) A

/-! ## XOR Hash Unlinkability Counterexample

The XOR outputs of two sessions under a shared key satisfy the fixed relation
`H(k,n₁) ⊕ H(k,n₂) = n₁ ⊕ n₂`, independent of the key. A distinguisher testing
this relation accepts the real game with certainty; against independent keys it
can reject. Hence the XOR hash — though a perfect authenticator — is not
unlinkable, motivating a genuine PRF for multi-session privacy.
-/

/-- Key-correlation leak: with a shared key the XOR of the two responses is a
fixed function of the nonces, independent of the key. This is the structural
weakness that breaks unlinkability. -/
theorem xorHash_correlated (k n1 n2 : Word) :
    xor (xor k n1) (xor k n2) = xor n1 n2 := by
  cases k <;> cases n1 <;> cases n2 <;> rfl

/-- Correlation-testing distinguisher: accept iff the XOR of the two responses
equals the XOR of the two nonces (which holds exactly when the key is shared). -/
noncomputable def unlink_distinguisher (n1 n2 : Word) :
    Word × Word → SPComp Bool :=
  fun (r1, r2) => SPComp.pure (xor r1 r2 == xor n1 n2)

/-- **Against the real game the distinguisher always accepts**: with a shared
key the XOR of the outputs deterministically equals the XOR of the nonces, so
the run reduces to sampling the (discarded) key and returning `true`. -/
theorem unlink_real_always_true (n1 n2 : Word) :
    (unlink_real xorHash n1 n2).bind (unlink_distinguisher n1 n2) =
    SPComp.bind (SPComp.sample Word) (fun _ => SPComp.pure true) := by
  simp only [unlink_real, unlink_distinguisher, xorHash, SPComp.monad_bind_eq,
    SPComp.bind_assoc, SPComp.pure_bind]
  bind_align; rw [xorHash_correlated]; simp

/-- **Against the ideal game the distinguisher can reject**: for distinct nonces
there are independent keys making the correlation check fail, so the real and
ideal unlinkability games genuinely differ. -/
theorem unlink_ideal_not_always_true (n1 n2 : Word) (hne : n1 ≠ n2) :
    ∃ k1 k2 : Word,
      (xor (xorHash.h k1 n1) (xorHash.h k2 n2) == xor n1 n2) = false := by
  cases n1 <;> cases n2
    <;> first | exact absurd rfl hne | exact ⟨false, true, rfl⟩

end CatCrypt.Examples.BasicHash
