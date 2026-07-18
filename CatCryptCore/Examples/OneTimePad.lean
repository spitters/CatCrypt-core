/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.SecurityDefs
import CatCryptCore.Prob.XorBij
import CatCryptCore.Tactics
import CatCryptCore.Deep.OracleGamePackage
import CatCryptCore.Deep.ReflectUCHelpers
import CatCryptCore.Crypto.NomPkgBridge

/-!
# One-Time Pad: Perfect IND-CPA Security

The one-time pad has perfect IND-CPA security. Following Rosulek, The Joy of
Cryptography, §2 (one-time secrecy).

This file defines the one-time pad over `Bool` as a core `EncScheme`, proves it
correct, and shows it achieves *perfect* IND-CPA security: the IND-CPA advantage
of every adversary is exactly `0`.

## Overview

The one-time pad is the symmetric scheme with `Key = Plaintext = Ciphertext =
Bool`, key generation sampling a uniform bit, and both encryption and decryption
given by XOR:
```
Enc(k, m) = k ⊕ m      Dec(k, c) = k ⊕ c
```

The security argument is the bijection-coupling technique. For any fixed message
`m`, XOR-by-`m` is a bijection of the uniform key, so `k ⊕ m` is uniformly
distributed and independent of `m`. Consequently the two IND-CPA games
(encrypting `m₀` vs `m₁`) are each equidistributed with a uniform sample; by
transitivity they couple with one another, and `INDCPA_Adv_zero_of_rHoare`
collapses the advantage to `0`.

## Main definitions

* `BoolOTP` — the one-time pad as a core `EncScheme` over `Bool`.

## Main results

* `otp_correct` — the one-time pad is correct (`decrypt (encrypt m k) k = m`).
* `otp_perfect_indcpa` — the one-time pad has perfect IND-CPA security:
  `INDCPA_Adv BoolOTP m₀ m₁ A = 0` for every adversary `A`.

## References

* [Rosulek, The Joy of Cryptography, §2 (one-time secrecy)]
* [Shannon, Communication Theory of Secrecy Systems, 1949]
-/

namespace CatCrypt.Examples.OTP

open CatCrypt.Core
open CatCrypt.Crypto
open CatCrypt.Crypto.SecurityDefs
open CatCrypt.Prob
open CatCrypt.Prob.XorBij
open CatCrypt.Relational

/-! ## One-Time Pad Definition -/

/-- The one-time pad encryption scheme over `Bool`.

- `Key = Plaintext = Ciphertext = Bool`
- `keyGen` samples a uniform bit
- `encrypt k m = k ⊕ m`
- `decrypt k c = some (k ⊕ c)` -/
noncomputable def BoolOTP : EncScheme where
  Key := Bool
  Plaintext := Bool
  Ciphertext := Bool
  finKey := inferInstance
  neKey := ⟨false⟩
  finCt := inferInstance
  neCt := ⟨false⟩
  keyGen := SPComp.sample Bool
  encrypt := fun k m => SPComp.pure (xor k m)
  decrypt := fun k c => SPComp.pure (some (xor k c))

/-! ## Correctness -/

/-- The one-time pad is correct: decryption recovers the message. -/
theorem otp_correct : BoolOTP.Correct := by
  apply EncScheme.correct_of_simple_correct BoolOTP
    (encryptF := fun k m => xor k m) (decryptF := fun k c => some (xor k c))
  all_goals (intro a b; simp [BoolOTP])

/-! ## Perfect IND-CPA Security -/

/-- Coupling: the two IND-CPA games for the one-time pad are equidistributed.

Both `encrypt k m₀` and `encrypt k m₁` over a uniform key `k` are equidistributed
with a plain uniform sample (XOR-by-a-fixed-message is a bijection of the key),
so the real and ideal games couple by transitivity through the uniform sample. -/
theorem otp_indcpa_coupling (m₀ m₁ : Bool) :
    rHoare eqPre
      (INDCPA_Game BoolOTP m₀ m₁ true)
      (INDCPA_Game BoolOTP m₀ m₁ false)
      eqPost := by
  simp only [INDCPA_Game, BoolOTP, if_true, Bool.false_eq_true, if_false,
    SPComp.monad_bind_eq]
  ssprove_couple_bij (boolXorBij (xor m₀ m₁))

/-- **The one-time pad has perfect IND-CPA security**: every adversary has IND-CPA
advantage exactly `0`. -/
theorem otp_perfect_indcpa (m₀ m₁ : Bool) (A : BoolOTP.Ciphertext → SPComp Bool) :
    INDCPA_Adv BoolOTP m₀ m₁ A = 0 :=
  INDCPA_Adv_zero_of_rHoare BoolOTP m₀ m₁ (otp_indcpa_coupling m₀ m₁) A

/-! ## Reflection into the Package / UC Stack

The shallow result `otp_perfect_indcpa` is an empty-heap statement about a single
distinguisher applied to the two IND-CPA game bodies. This section lifts it to a
*composable* statement about deep nominal packages linked with an arbitrary
adversary package, following the stack
`shallow game → rawCode% → NomPackage.ofOracle → DeepNomAdvantage → sdist → UC`.

The two IND-CPA game bodies `INDCPA_Game BoolOTP m₀ m₁ true/false` are, after
unfolding `BoolOTP`, the single family `k ← sample Bool; pure (k ⊕ m)` at the
messages `m₀` and `m₁`. Reflecting this family with `rawCode%` and exporting it as
the oracle `(1, Unit, Bool)` yields the real/ideal package pair. Because
XOR-by-`m` is a bijection of the uniform key, every reflected body evaluates to
the *same* uniform sample, so the two games are indistinguishable against **any**
adversary package — the package-level form of one-time secrecy. -/

open CatCrypt.Deep

/-- The reflected IND-CPA oracle body for message `m`: sample a uniform key and
    return the one-time-pad ciphertext `k ⊕ m`. Instantiated at `m₀` for bit
    `true` and `m₁` for bit `false`, this is the whole IND-CPA game family. -/
noncomputable def otpGameRaw (m : Bool) : RawCode Bool :=
  rawCode% (SPComp.bind (SPComp.sample Bool) (fun k => SPComp.pure (xor k m)))

instance instValidOtpGameRaw (m : Bool) : IsValid (∅ : LocSet) (otpGameRaw m) := by
  unfold otpGameRaw; infer_instance

/-- The reflected body evaluates back to the shallow IND-CPA game body. -/
theorem otpGameRaw_eval (m : Bool) :
    (otpGameRaw m).eval =
      SPComp.bind (SPComp.sample Bool) (fun k => SPComp.pure (xor k m)) := by
  simp [otpGameRaw, RawCode.eval]

/-- The reflected body's evaluation is the uniform sample, independent of `m`:
    XOR-by-`m` is a bijection of the uniform key. This is the distribution-level
    core of one-time secrecy, here as an `SPComp` *equality*. -/
theorem otpGameRaw_eval_eq (m : Bool) : (otpGameRaw m).eval = SPComp.sample Bool := by
  simpa [otpGameRaw_eval, boolXorBij_apply, SPComp.bind_pure] using SPComp.sample_bind_equiv (boolXorBij m) fun b => SPComp.pure b

/-- The reflected body evaluation is the shallow IND-CPA game (bit `true` at `m₀`). -/
theorem otpGameRaw_eval_indcpa_true (m₀ m₁ : Bool) :
    (otpGameRaw m₀).eval = INDCPA_Game BoolOTP m₀ m₁ true :=
  by simp [otpGameRaw_eval, INDCPA_Game, BoolOTP, SPComp.monad_bind_eq]

/-- The reflected body evaluation is the shallow IND-CPA game (bit `false` at `m₁`). -/
theorem otpGameRaw_eval_indcpa_false (m₀ m₁ : Bool) :
    (otpGameRaw m₁).eval = INDCPA_Game BoolOTP m₀ m₁ false :=
  by simp [otpGameRaw_eval, INDCPA_Game, BoolOTP, SPComp.monad_bind_eq]

/-- Real IND-CPA game as an oracle-exporting nominal package: exports the single
    oracle `(1, Unit, Bool)`, implemented by the reflected body at `m₀`. -/
noncomputable def otpGameTrue (m₀ : Bool) : NomPackage :=
  NomPackage.ofOracle 1 Unit Bool (fun _ => otpGameRaw m₀)

/-- Ideal IND-CPA game: the same oracle export, implemented by the body at `m₁`. -/
noncomputable def otpGameFalse (m₁ : Bool) : NomPackage :=
  NomPackage.ofOracle 1 Unit Bool (fun _ => otpGameRaw m₁)

/-- The two reflected IND-CPA bodies (encrypting `m₀` vs `m₁`) have equal
    evaluations: each is the uniform sample by `otpGameRaw_eval_eq`, so they
    coincide. This single body-`.eval` equality is what the `ReflectUCHelpers`
    `ofOracle` combinators consume — the whole perfect stack follows from it with
    no `IsPure`/`NoFail` bridge on the adversary. -/
theorem otp_eval_eq (m₀ m₁ : Bool) :
    (otpGameRaw m₀).eval = (otpGameRaw m₁).eval :=
  (otpGameRaw_eval_eq m₀).trans (otpGameRaw_eval_eq m₁).symm

/-- **Zero deep-nominal advantage against every adversary package.** The
    reflected real/ideal games are perfectly indistinguishable in the deep
    package model — the package-level form of `otp_perfect_indcpa`. -/
theorem otp_deepnom_zero (m₀ m₁ : Bool) (A : NomPackage) :
    DeepNomAdvantage (otpGameTrue m₀) (otpGameFalse m₁) A = 0 :=
  deepNomAdvantage_ofOracle_zero _ _ (fun _ => otp_eval_eq m₀ m₁) A

/-- **Package-level UC security** (`NomPkgSecure`): the reflected one-time pad
    games emulate each other with zero adversary-dependent error, so the pair
    composes via `NomPkgSecure_trans`. -/
theorem otp_nompkg_secure (m₀ m₁ : Bool) :
    NomPkgSecure (otpGameTrue m₀) (otpGameFalse m₁) (fun _ => 0) :=
  nomPkgSecure_ofOracle _ _ (fun _ => otp_eval_eq m₀ m₁)

/-- **Statistical distance zero** between the two linked-game families: the linked
    runs coincide against every adversary, so `sdist_self` collapses the distance
    — no `IsPure`/`NoFail` post-processing bridge is needed. -/
theorem otp_sdist_zero (m₀ m₁ : Bool) :
    sdist (fun A : NomPackage => runPkg (DeepPackage.link A.pkg (otpGameTrue m₀).pkg))
          (fun A : NomPackage => runPkg (DeepPackage.link A.pkg (otpGameFalse m₁).pkg)) = 0 :=
  sdist_ofOracle_zero _ _ (fun _ => otp_eval_eq m₀ m₁)

/-- **Perfect UC emulation** of the linked-game families, over the trivial-leak
    interface (`out = Bool`, `leak = Empty`): the real game UC-emulates the ideal
    game with error `0` via the identity simulator (composition plumbing). -/
theorem otp_uc (m₀ m₁ : Bool) :
    UCEmulates 0 ⟨NomPackage, Bool, Empty, Empty, Bool⟩
      (fun A => SPComp.map (Sum.inl : Bool → Bool ⊕ Empty)
        (runPkg (DeepPackage.link A.pkg (otpGameTrue m₀).pkg)))
      (fun A => SPComp.map (Sum.inl : Bool → Bool ⊕ Empty)
        (runPkg (DeepPackage.link A.pkg (otpGameFalse m₁).pkg))) :=
  uc_ofOracle _ _ (fun _ => otp_eval_eq m₀ m₁)

/-- **Reflection mirrors the shallow game.** Against the forwarding adversary, the
    deep-nominal advantage of the reflected games equals the shallow IND-CPA
    advantage of `BoolOTP` under the identity distinguisher — which is `0` by
    `otp_perfect_indcpa`. This certifies that the package construction computes
    the same quantity the shallow proof bounds. -/
theorem otp_deepnom_forward_eq_indcpa (m₀ m₁ : Bool) :
    DeepNomAdvantage (otpGameTrue m₀) (otpGameFalse m₁) forwardAdv =
    INDCPA_Adv BoolOTP m₀ m₁ SPComp.pure := by
  unfold DeepNomAdvantage otpGameTrue otpGameFalse
  rw [runPkg_link_forward (otpGameRaw m₀), runPkg_link_forward (otpGameRaw m₁),
    otpGameRaw_eval_indcpa_true m₀ m₁, otpGameRaw_eval_indcpa_false m₀ m₁,
    INDCPA_Adv, AdvantageA]
  congr 1 <;> exact (SPComp.bind_pure _).symm

end CatCrypt.Examples.OTP
