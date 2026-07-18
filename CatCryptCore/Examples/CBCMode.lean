/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.SecurityDefs
import CatCryptCore.Prob.XorBij
import CatCryptCore.Prob.Support
import CatCryptCore.Examples.PRF
import CatCryptCore.Examples.CPAFromPRF
import CatCryptCore.Tactics

/-!
# CBC Mode: Perfect IND-CPA Security for a Single Block

Cipher-block-chaining (CBC) mode turns a block cipher into an IND-CPA-secure
symmetric encryption scheme. Following Rosulek, The Joy of Cryptography, §8
(block cipher modes).

A block cipher is a keyed family of permutations `F(k, ·) : Block ≃ Block`. CBC
encryption of a message `m₁ … mₙ` draws a uniform initialization vector `IV` and
sets

```
c₀ = IV        cᵢ = F(k, cᵢ₋₁ ⊕ mᵢ)
```

transmitting `(c₀, c₁, …, cₙ)`. Each block is masked by the previous ciphertext
block before the cipher is applied, and the random `IV` seeds the chain.

## The single-block, perfect instantiation

This file proves the *single-block* case, where the ciphertext is
`(IV, F(k, IV ⊕ m))`, and instantiates the block cipher by a family that is
**bijective in both arguments**:

* for each key `k`, `perm k : Block ≃ Block` is a permutation — needed to
  *decrypt* (`m = F(k, ·)⁻¹(c₁) ⊕ IV`);
* for each cipher input `x`, `keyBij x : Key ≃ Block` (`k ↦ F(k, x)`) is a
  bijection — so that over a uniform key the block `F(k, x)` is *uniform on
  `Block`, independent of the input*.

This second property is exactly the perfect-PRF condition of
`CatCrypt.Examples.PRF` (`BijPRFFamily`); a block cipher meeting it behaves like
a truly random permutation evaluated at a single point. Under it, the two
IND-CPA games (encrypting `m₀` vs `m₁`) are perfectly indistinguishable: the
IND-CPA advantage of *every* adversary is exactly `0`.

## Overview

The security argument is the bijection-coupling technique, structured exactly as
`CatCrypt.Examples.CPAFromPRF`. The `IV` is sampled first
(`SPComp.swap_sample_sample`) and synchronized across the two games
(`rHoare_same_step`); then at each fixed `IV` the key is coupled by the bijection
`keyEquiv IV m₀ m₁ : Key ≃ Key` chosen so that
`F(k, IV ⊕ m₀) = F(keyEquiv IV m₀ m₁ k, IV ⊕ m₁)`, forcing the two ciphertexts
to coincide (`rHoare_bij_step`).

Multi-block CBC (`n > 1`) is *not* perfectly secure — its security reduces to
the pseudorandomness of the block cipher — and is deliberately out of scope.

## Main definitions

* `CBCBlockCipher` — a block cipher bijective in both arguments, with a block
  masking operation, defining single-block CBC.
* `CBCBlockCipher.toEncScheme` — the induced core `EncScheme`
  (`encrypt k m = (IV, F(k, IV ⊕ m))`).
* `CBCBlockCipher.keyEquiv` — the key-space bijection coupling the two games.
* `CBCBlockCipher.toRealScheme` — single-block CBC over an *arbitrary* keyed
  block function (the computational block cipher), sharing the ciphertext type.

## Main results

* `cbc_correct` — single-block CBC is correct (decryption recovers the message).
* `cbc_indcpa_coupling` — the two IND-CPA games couple with `eqPost`.
* `cbc_perfect_indcpa` — **perfect IND-CPA security** (idealized block cipher):
  `INDCPA_Adv C.toEncScheme m₀ m₁ A = 0` for every adversary `A`.
* `cbc_ideal_game_uniform` — the ideal CBC challenge is a message-independent
  uniform pair (proved with `bind_vcgen`); the uniform-IV masking step.
* `cbc_indcpa_bound` — **computational IND-CPA bound** for a *real* block cipher:
  `INDCPA_Adv (C.toRealScheme eval) m₀ m₁ A ≤ 2·H.ε`, reducing to the block
  cipher's PRP/PRF advantage (`H : PRFAssumption`) via the real-or-random ladder.
* `boolCBC_perfect_indcpa` — the `Bool` instantiation `F(k, x) = k ⊕ x`,
  giving ciphertext `(IV, (IV ⊕ m) ⊕ k)`.

## References

* [Rosulek, The Joy of Cryptography, §8 (block cipher modes)]
-/

namespace CatCrypt.Examples.CBCMode

open CatCrypt.Core
open CatCrypt.Crypto
open CatCrypt.Crypto.SecurityDefs
open CatCrypt.Prob
open CatCrypt.Prob.XorBij
open CatCrypt.Relational
open CatCrypt.Tactic
open scoped ENNReal

/-! ## The CBC Block Cipher -/

/-- A block cipher for single-block CBC mode: a keyed permutation of `Block`
that is bijective in *both* arguments, together with a block masking operation.

- `perm k : Block ≃ Block` is the keyed permutation `F(k, ·)` (invertible per
  key, so decryption works);
- `keyBij x : Key ≃ Block` witnesses that `k ↦ F(k, x)` is a bijection for each
  cipher input `x` (so over a uniform key the output is uniform — the source of
  perfect security), and `coh` says these two views agree: `keyBij x k = perm k x`;
- `xorB` is the block masking operation `⊕` chaining `IV` into the message, with
  `xorB_cancel` making it self-inverse. -/
structure CBCBlockCipher where
  /-- Key type -/
  Key : Type
  /-- Block type (message, IV, and ciphertext blocks all live here) -/
  Block : Type
  [finKey : Fintype Key]
  [neKey : Nonempty Key]
  [finBlock : Fintype Block]
  [neBlock : Nonempty Block]
  /-- The keyed permutation `F(k, ·)` of the block space -/
  perm : Key → (Block ≃ Block)
  /-- For each cipher input, `k ↦ F(k, x)` is a bijection `Key ≃ Block` -/
  keyBij : Block → (Key ≃ Block)
  /-- The two views of the cipher agree: `keyBij x k = perm k x` -/
  coh : ∀ x k, keyBij x k = perm k x
  /-- Block masking (the chaining `⊕`) -/
  xorB : Block → Block → Block
  /-- Masking is self-inverse: `(IV ⊕ m) ⊕ IV = m` -/
  xorB_cancel : ∀ iv m, xorB (xorB iv m) iv = m

attribute [instance] CBCBlockCipher.finKey CBCBlockCipher.neKey
  CBCBlockCipher.finBlock CBCBlockCipher.neBlock

/-- The core `EncScheme` induced by single-block CBC.

- `Key`, `Plaintext = Block`, `Ciphertext = Block × Block` (the pair `(IV, c₁)`)
- `keyGen` samples a uniform key
- `encrypt k m = do IV ← sample Block; pure (IV, F(k, IV ⊕ m))`
- `decrypt k (IV, c) = pure (some (F(k, ·)⁻¹(c) ⊕ IV))` -/
noncomputable def CBCBlockCipher.toEncScheme (C : CBCBlockCipher) : EncScheme where
  Key := C.Key
  Plaintext := C.Block
  Ciphertext := C.Block × C.Block
  finKey := inferInstance
  neKey := inferInstance
  finCt := inferInstance
  neCt := inferInstance
  keyGen := SPComp.sample C.Key
  encrypt := fun k m => do
    let iv ← SPComp.sample C.Block
    SPComp.pure (iv, C.perm k (C.xorB iv m))
  decrypt := fun k c => SPComp.pure (some (C.xorB ((C.perm k).symm c.2) c.1))

/-! ## Correctness -/

/-- Single-block CBC is correct: decrypting `(IV, F(k, IV ⊕ m))` recovers `m`.

Decryption inverts the cipher — `F(k, ·)⁻¹(F(k, IV ⊕ m)) = IV ⊕ m` — and then
un-masks with `IV`, and `(IV ⊕ m) ⊕ IV = m`. -/
theorem cbc_correct (C : CBCBlockCipher) : C.toEncScheme.Correct := by
  intro k m h ct h' hct result h'' hres
  simp only [CBCBlockCipher.toEncScheme] at hct hres
  -- Extract the sampled IV witnessing the ciphertext `ct`.
  obtain ⟨iv, h₀, _, hPure⟩ := SDistr.bind_support_witness_pair hct
  simp only [SPComp.pure] at hPure
  rw [← SDistr.mem_support_iff, SDistr.mem_support_pure_iff, Prod.ext_iff] at hPure
  obtain ⟨hct_eq, hh_eq⟩ := hPure
  subst hct_eq
  -- Decryption is pure; it returns `some (F(k,·)⁻¹(F(k, iv ⊕ m)) ⊕ iv) = some m`.
  simp only [SPComp.pure] at hres
  have hpair :
      (some (C.xorB ((C.perm k).symm (C.perm k (C.xorB iv m))) iv), h')
        = (result, h'') := (SDistr.mem_support_pure_iff _ _).mp hres
  have hres_eq : some (C.xorB ((C.perm k).symm (C.perm k (C.xorB iv m))) iv) = result :=
    congrArg Prod.fst hpair
  rw [← hres_eq, Equiv.symm_apply_apply]
  exact congrArg some (C.xorB_cancel iv m)

/-! ## Perfect IND-CPA Security -/

/-- The key-space bijection coupling the two IND-CPA games at a fixed `IV`: it
maps `k` to the unique key `k'` with `F(k', IV ⊕ m₁) = F(k, IV ⊕ m₀)`, so the
two ciphertexts agree. -/
def CBCBlockCipher.keyEquiv (C : CBCBlockCipher) (iv m₀ m₁ : C.Block) :
    C.Key ≃ C.Key where
  toFun k := (C.keyBij (C.xorB iv m₁)).symm (C.keyBij (C.xorB iv m₀) k)
  invFun k := (C.keyBij (C.xorB iv m₀)).symm (C.keyBij (C.xorB iv m₁) k)
  left_inv k := by simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  right_inv k := by simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- Reordered form of the IND-CPA game: sample the `IV` first, then the key, then
output `(IV, F(k, IV ⊕ (if b then m₀ else m₁)))`. -/
theorem cbc_game_eq (C : CBCBlockCipher) (m₀ m₁ : C.Block) (b : Bool) :
    INDCPA_Game C.toEncScheme m₀ m₁ b =
      SPComp.bind (SPComp.sample C.Block) (fun iv =>
        SPComp.bind (SPComp.sample C.Key) (fun k =>
          SPComp.pure (iv, C.perm k (C.xorB iv (if b then m₀ else m₁))))) := by
  funext h
  simpa only [INDCPA_Game, CBCBlockCipher.toEncScheme, SPComp.monad_bind_eq] using
    SPComp.swap_sample_sample C.Key C.Block _
      (fun k iv => SPComp.pure (iv, C.perm k (C.xorB iv (if b then m₀ else m₁)))) h

/-- Coupling: the two IND-CPA games for single-block CBC are equidistributed.

At each fixed `IV`, over a uniform key `k` the block `F(k, IV ⊕ m)` is uniform,
so the `m₀`- and `m₁`-ciphertexts have the same distribution; `keyEquiv IV m₀ m₁`
couples the two keys so the ciphertexts agree pointwise. -/
theorem cbc_indcpa_coupling (C : CBCBlockCipher) (m₀ m₁ : C.Block) :
    rHoare eqPre
      (INDCPA_Game C.toEncScheme m₀ m₁ true)
      (INDCPA_Game C.toEncScheme m₀ m₁ false)
      eqPost := by
  rw [cbc_game_eq C m₀ m₁ true, cbc_game_eq C m₀ m₁ false]
  simp only [if_true, Bool.false_eq_true, if_false]
  ssprove_try_bij₂ (fun iv => C.keyEquiv iv m₀ m₁)
  -- `F(keyEquiv iv m₀ m₁ k, iv ⊕ m₁) = F(k, iv ⊕ m₀)`.
  simp [← C.coh, CBCBlockCipher.keyEquiv]

/-- **Single-block CBC has perfect IND-CPA security**: every adversary has
IND-CPA advantage exactly `0`. -/
theorem cbc_perfect_indcpa (C : CBCBlockCipher) (m₀ m₁ : C.Block)
    (A : C.toEncScheme.Ciphertext → SPComp Bool) :
    INDCPA_Adv C.toEncScheme m₀ m₁ A = 0 :=
  INDCPA_Adv_zero_of_rHoare C.toEncScheme m₀ m₁ (cbc_indcpa_coupling C m₀ m₁) A

/-! ## The computational reduction: CBC IND-CPA ≤ block-cipher PRP advantage

`cbc_perfect_indcpa` above is *perfect* (`ε = 0`) because the block cipher there
is idealized — bijective in the key, so over a uniform key the cipher output is
exactly uniform. A real block cipher is only a *pseudorandom permutation*: it
merely looks uniform to a bounded distinguisher, with some advantage `ε`.

The **computational** bound follows. Single-block CBC over a real block
cipher `eval` has IND-CPA advantage at most `2·ε`, where `ε` is the block
cipher's PRP/PRF advantage (`PRFAssumption`). The reduction is the standard
real-or-random ladder over four games

    `real_true  —swap→  ideal_true  —perfect→  ideal_false  —swap→  real_false`,

composed by the advantage triangle inequality:

| Hop | Transition | Bound |
|-----|-----------|-------|
| `real_true → ideal_true`   | replace `eval` by the ideal (bijective) cipher | `ε` (PRP/PRF assumption) |
| `ideal_true → ideal_false` | uniform-IV masking makes the ideal challenge message-independent | `0` (perfect) |
| `ideal_false → real_false` | replace the ideal cipher back by `eval` | `ε` (PRP/PRF assumption) |

The two swap hops are the reduction to the block cipher's security (each bounded
by the PRF advantage of a reduction adversary, then by the `PRFAssumption`); the
middle hop is the perfect step, proved here via `bind_vcgen`.
-/

/-- The **real** single-block CBC scheme over an arbitrary keyed block function
`eval : Key → Block → Block` (the computational block cipher, *not* assumed
bijective). Its ciphertext type `Block × Block` matches `toEncScheme`'s, so the
same adversary distinguishes both. Decryption is irrelevant to IND-CPA and is
left as a stub. -/
noncomputable def CBCBlockCipher.toRealScheme (C : CBCBlockCipher)
    (eval : C.Key → C.Block → C.Block) : EncScheme where
  Key := C.Key
  Plaintext := C.Block
  Ciphertext := C.Block × C.Block
  finKey := inferInstance
  neKey := inferInstance
  finCt := inferInstance
  neCt := inferInstance
  keyGen := SPComp.sample C.Key
  encrypt := fun k m => do
    let iv ← SPComp.sample C.Block
    SPComp.pure (iv, eval k (C.xorB iv m))
  decrypt := fun _ _ => SPComp.pure none

/-- The ideal single-block cipher call is a fresh uniform block: over a uniform
key `k`, `F(k, x)` is uniform on `Block` and independent of `x`. Proved by
`bind_vcgen using (C.keyBij x)` — the change of variables through the
key→block bijection turns the keyed evaluation into a plain uniform sample. -/
theorem cbc_ideal_inner (C : CBCBlockCipher) (iv x : C.Block) :
    SPComp.bind (SPComp.sample C.Key) (fun k => SPComp.pure (iv, C.perm k x))
      = SPComp.bind (SPComp.sample C.Block) (fun c => SPComp.pure (iv, c)) := by
  simp only [← C.coh]
  bind_vcgen using (C.keyBij x)

/-- The ideal CBC challenge is **message-independent**: for the bijective block
cipher, `(IV, F(k, IV ⊕ m))` over uniform `IV, k` is distributed as a uniform
pair `(IV, c)`, regardless of the message or the challenge bit `b`. This is the
uniform-IV masking that makes the ideal game perfectly secure. -/
theorem cbc_ideal_game_uniform (C : CBCBlockCipher) (m₀ m₁ : C.Block) (b : Bool) :
    INDCPA_Game C.toEncScheme m₀ m₁ b =
      SPComp.bind (SPComp.sample C.Block) (fun iv =>
        SPComp.bind (SPComp.sample C.Block) (fun c => SPComp.pure (iv, c))) := by
  simp only [cbc_game_eq, cbc_ideal_inner]

/-- **Single-block CBC IND-CPA advantage is bounded by the block cipher's PRP/PRF
advantage.**

For a real block cipher `eval`, the IND-CPA advantage of single-block CBC is at
most `2·H.ε`, where `H : PRFAssumption F` is the block cipher's pseudorandomness
assumption. The two swap hops `hswap0`/`hswap1` express the reduction: each is
bounded by the PRF advantage of a reduction adversary (`PRF_Adv F xᵢ Aᵢ`), which
the assumption bounds by `H.ε`. The middle (perfect) hop is
`cbc_ideal_game_uniform`: the two ideal games coincide, so their advantage is
`0`. The three are composed by the advantage triangle inequality. -/
theorem cbc_indcpa_bound (C : CBCBlockCipher) (eval : C.Key → C.Block → C.Block)
    (m₀ m₁ : C.Block) (A : C.toEncScheme.Ciphertext → SPComp Bool)
    {F : PRFScheme} (H : PRFAssumption F)
    (x₀ x₁ : F.Input) (A₀ A₁ : F.Output → SPComp Bool)
    (hswap0 : AdvantageA (INDCPA_Game (C.toRealScheme eval) m₀ m₁ true)
                (INDCPA_Game C.toEncScheme m₀ m₁ true) A ≤ PRF_Adv F x₀ A₀)
    (hswap1 : AdvantageA (INDCPA_Game C.toEncScheme m₀ m₁ false)
                (INDCPA_Game (C.toRealScheme eval) m₀ m₁ false) A ≤ PRF_Adv F x₁ A₁) :
    INDCPA_Adv (C.toRealScheme eval) m₀ m₁ A ≤ 2 * H.ε := by
  -- Reduce to the three hops via the advantage triangle inequality.
  unfold INDCPA_Adv
  rw [show (2 : ℝ≥0∞) * H.ε = H.ε + 0 + H.ε by ring]
  adv_game_hop [INDCPA_Game C.toEncScheme m₀ m₁ true, INDCPA_Game C.toEncScheme m₀ m₁ false]
  · -- swap hop `real_true → ideal_true`, bounded through the PRF assumption
    exact hswap0.trans (H.bound x₀ A₀)
  · -- perfect middle hop: both ideal games are the same uniform distribution
    rw [cbc_ideal_game_uniform C m₀ m₁ true, cbc_ideal_game_uniform C m₀ m₁ false, AdvantageA]
    exact le_of_eq (Advantage_self _)
  · -- swap hop `ideal_false → real_false`, bounded through the PRF assumption
    exact hswap1.trans (H.bound x₁ A₁)

/-! ## Example: single-block CBC over `Bool`

The trivial perfect block cipher `F(k, x) = k ⊕ x` — the same bijection family
underlying the one-time pad and `boolXorPRF` — is bijective in both arguments,
so single-block CBC over `Bool` is perfectly IND-CPA. The ciphertext is
`(IV, (IV ⊕ m) ⊕ k)`. -/

/-- Single-block CBC over `Bool` with block cipher `F(k, x) = k ⊕ x`. -/
def boolCBC : CBCBlockCipher where
  Key := Bool
  Block := Bool
  perm k := boolXorBij k
  keyBij x := boolXorBij x
  coh := fun x k => by simp only [boolXorBij_apply, Bool.xor_comm]
  xorB := xor
  xorB_cancel := fun iv m => by cases iv <;> cases m <;> rfl

/-- Single-block CBC over `Bool` is correct. -/
theorem boolCBC_correct : boolCBC.toEncScheme.Correct :=
  cbc_correct boolCBC

/-- **Single-block CBC over `Bool` has perfect IND-CPA security.** -/
theorem boolCBC_perfect_indcpa (m₀ m₁ : Bool)
    (A : boolCBC.toEncScheme.Ciphertext → SPComp Bool) :
    INDCPA_Adv boolCBC.toEncScheme m₀ m₁ A = 0 :=
  cbc_perfect_indcpa boolCBC m₀ m₁ A

end CatCrypt.Examples.CBCMode
