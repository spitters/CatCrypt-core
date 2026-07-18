/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.SecurityDefs
import CatCryptCore.Examples.OneTimePad
import CatCryptCore.Prob.Support
import CatCryptCore.Tactics

/-!
# Encrypt-then-MAC: a composed authenticated-encryption scheme

Encrypt-then-MAC is the standard construction that turns a confidentiality-only
encryption scheme into an authenticated one: encrypt the message, then MAC the
resulting ciphertext, and transmit `(ciphertext, tag)`. Decryption first checks
the tag and only decrypts if it verifies. Following Rosulek, *The Joy of
Cryptography*, §9-10 (MACs and authenticated encryption; Construction 10.9,
Claim 10.10).

This file gives the construction as a *combinator* on core's `EncScheme`, proves
its correctness generically, and then studies the XOR / one-time-pad
instantiation, for which it achieves **perfect** IND-CPA security (advantage
exactly `0`).

## The construction

Given an encryption scheme `E` and a MAC `macF : MacKey → E.Ciphertext → Tag`,
`EtM E … macF` is the scheme with

* `Key = E.Key × MacKey`, `Ciphertext = E.Ciphertext × Tag`;
* `keyGen` samples an encryption key and a MAC key independently;
* `encrypt (ke, km) m = let c ← E.encrypt ke m; (c, macF km c)`;
* `decrypt (ke, km) (c, t) = if t = macF km c then E.decrypt ke c else ⊥`.

## Main results

* `EtM` — the Encrypt-then-MAC combinator on `EncScheme`.
* `EtM_correct` — the combinator preserves correctness: if `E` is correct, so is
  `EtM E … macF`. An honestly produced ciphertext always carries a matching tag,
  so decryption clears the tag check and recovers the message.
* `BoolEtM` — the XOR instantiation: OTP encryption composed with the XOR MAC
  `macF km c = km ⊕ c` over `Bool`.
* `boolEtM_correct` — `BoolEtM` is correct (via `EtM_correct` and `otp_correct`).
* `boolEtM_perfect_indcpa` — **`BoolEtM` has perfect IND-CPA security**: every
  adversary has IND-CPA advantage exactly `0`.

## On the `Adv_CCA ≤ Adv_MAC + Adv_CPA + Adv_MAC` bound

The general Encrypt-then-MAC theorem bounds the *authenticated* (IND-CCA)
advantage by the MAC's forging advantage plus the base scheme's IND-CPA
advantage. Core currently exposes an IND-CPA game (`INDCPA_Game`) but no IND-CCA
game, so the cleanest core-provable headline is the perfect IND-CPA security of
the XOR instantiation, proved by the bijection-coupling technique of
`OneTimePad.lean`.

## References

* [Rosulek, The Joy of Cryptography, §9-10; Construction 10.9, Claim 10.10]
* [Bellare & Namprempre, Authenticated Encryption: Relations among Notions]
-/

namespace CatCrypt.Examples.EncryptThenMAC

open CatCrypt.Core
open CatCrypt.Crypto
open CatCrypt.Crypto.SecurityDefs
open CatCrypt.Prob
open CatCrypt.Prob.XorBij
open CatCrypt.Relational
open CatCrypt.Examples.OTP

/-! ## The Encrypt-then-MAC combinator -/

/-- **Encrypt-then-MAC**. Given an encryption scheme `E` and a deterministic MAC
`macF : MacKey → E.Ciphertext → Tag`, produce the authenticated scheme that
appends `macF km c` to each ciphertext `c` and refuses to decrypt a ciphertext
whose tag does not verify. -/
noncomputable def EtM (E : EncScheme) (MacKey Tag : Type)
    [Fintype MacKey] [Nonempty MacKey] [Fintype Tag] [Nonempty Tag] [DecidableEq Tag]
    (macF : MacKey → E.Ciphertext → Tag) : EncScheme where
  Key := E.Key × MacKey
  Plaintext := E.Plaintext
  Ciphertext := E.Ciphertext × Tag
  finKey := inferInstance
  neKey := inferInstance
  finCt := inferInstance
  neCt := inferInstance
  keyGen := do
    let ke ← E.keyGen
    let km ← SPComp.sample MacKey
    SPComp.pure (ke, km)
  encrypt := fun k m => do
    let c ← E.encrypt k.1 m
    SPComp.pure (c, macF k.2 c)
  decrypt := fun k ct =>
    if ct.2 = macF k.2 ct.1 then E.decrypt k.1 ct.1 else SPComp.pure none

/-! ## Correctness of the combinator -/

/-- Encrypt-then-MAC preserves correctness. An honestly generated ciphertext
`(c, macF km c)` carries the matching tag, so decryption passes the tag check and
falls through to `E.decrypt`, which recovers the message by `hE`. -/
theorem EtM_correct (E : EncScheme) (MacKey Tag : Type)
    [Fintype MacKey] [Nonempty MacKey] [Fintype Tag] [Nonempty Tag] [DecidableEq Tag]
    (macF : MacKey → E.Ciphertext → Tag) (hE : E.Correct) :
    (EtM E MacKey Tag macF).Correct := by
  intro k m h ct h' hct result h'' hres
  -- Unfold the composed encryption to a `bind` over `E.encrypt`, at heap `h`.
  simp only [EtM] at hct
  -- Extract the intermediate ciphertext `c` and heap `hc` produced by `E.encrypt`.
  obtain ⟨c, hc, hEnc, hPure⟩ := SDistr.bind_support_witness_pair hct
  -- The pure step pins down `ct = (c, macF k.2 c)` and `h' = hc`.
  simp only [SPComp.pure] at hPure
  rw [← SDistr.mem_support_iff, SDistr.mem_support_pure_iff, Prod.ext_iff] at hPure
  obtain ⟨hct_eq, hh_eq⟩ := hPure
  subst hct_eq hh_eq
  -- Decryption clears the tag check (the tag is `macF k.2 c` by construction).
  simp only [EtM] at hres
  -- Now `E.decrypt` recovers the message by correctness of `E`.
  exact hE k.1 m h c hc ((SDistr.mem_support_iff _ _).2 hEnc) result h'' hres

/-! ## The XOR / one-time-pad instantiation -/

/-- The XOR MAC over `Bool`: `macF km c = km ⊕ c`. -/
def boolXorMac (km c : Bool) : Bool := xor km c

/-- **Encrypt-then-MAC over `Bool`**: OTP encryption composed with the XOR MAC.

`Key = Bool × Bool` (an encryption key and a MAC key), `Plaintext = Bool`,
`Ciphertext = Bool × Bool` (the OTP ciphertext and its tag). -/
noncomputable def BoolEtM : EncScheme :=
  EtM BoolOTP Bool Bool boolXorMac

/-- `BoolEtM` is correct, by `EtM_correct` and correctness of the one-time pad. -/
theorem boolEtM_correct : BoolEtM.Correct :=
  EtM_correct BoolOTP Bool Bool boolXorMac otp_correct

/-! ## Perfect IND-CPA security of the XOR instantiation -/

/-- The `BoolEtM` ciphertext as a pure function of the (encryption, MAC) key pair
and the message: `k ↦ (k.1 ⊕ m, k.2 ⊕ (k.1 ⊕ m))`. -/
def encF (k : Bool × Bool) (m : Bool) : Bool × Bool :=
  (xor k.1 m, xor k.2 (xor k.1 m))

/-- The `BoolEtM` IND-CPA game, collapsed to a single `Bool × Bool` key sample
followed by a pure ciphertext — the shape used by `OneTimePad.lean`. The two
independent key samples fuse into one product sample (`sample_prod_eq`), and the
OTP encryption's `pure` bind collapses (`SPComp.pure_bind`). -/
private theorem boolEtM_indcpa_game_eq (m₀ m₁ b : Bool) :
    INDCPA_Game BoolEtM m₀ m₁ b =
      (do
        let k ← SPComp.sample (Bool × Bool)
        SPComp.pure (encF k (if b then m₀ else m₁))) := by
  simp only [INDCPA_Game, BoolEtM, EtM, BoolOTP, boolXorMac, encF,
    SPComp.monad_bind_eq, SPComp.sample_prod_eq, SPComp.pure_bind]

/-- Coupling: the two IND-CPA games for `BoolEtM` are equidistributed.

The map `(ke, km) ↦ (ke ⊕ (m₀ ⊕ m₁), km)` is a bijection of the key space that
carries the `m₀`-ciphertext onto the `m₁`-ciphertext: the OTP component becomes
`ke ⊕ (m₀ ⊕ m₁) ⊕ m₁ = ke ⊕ m₀`, and the tag follows since it is a function of
that component and the (unchanged) MAC key. -/
theorem boolEtM_indcpa_coupling (m₀ m₁ : Bool) :
    rHoare eqPre
      (INDCPA_Game BoolEtM m₀ m₁ true)
      (INDCPA_Game BoolEtM m₀ m₁ false)
      eqPost := by
  rw [boolEtM_indcpa_game_eq, boolEtM_indcpa_game_eq]
  simp only [if_true, if_false, Bool.false_eq_true, SPComp.monad_bind_eq]
  ssprove_couple_bij (prodBoolXorBij (xor m₀ m₁, false))
  simp [encF]

/-- **`BoolEtM` has perfect IND-CPA security**: every adversary has IND-CPA
advantage exactly `0`. -/
theorem boolEtM_perfect_indcpa (m₀ m₁ : Bool) (A : BoolEtM.Ciphertext → SPComp Bool) :
    INDCPA_Adv BoolEtM m₀ m₁ A = 0 :=
  INDCPA_Adv_zero_of_rHoare BoolEtM m₀ m₁ (boolEtM_indcpa_coupling m₀ m₁) A

end CatCrypt.Examples.EncryptThenMAC
