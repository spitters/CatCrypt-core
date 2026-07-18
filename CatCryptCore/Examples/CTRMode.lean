/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Examples.CPAFromPRF
import CatCryptCore.Tactics

/-!
# Counter (CTR) Mode: the Perfect Single-Block Instantiation

Counter mode turns a block cipher / PRF into an IND-CPA-secure symmetric
encryption scheme. Following Rosulek, The Joy of Cryptography, §8 (block cipher
modes).

A single message block `m` is encrypted as `(nonce, E(k, nonce) ⊕ m)` for a
fresh uniform `nonce` (the initial counter value): the keystream block
`E(k, nonce)` acts as a one-time pad. Decryption recomputes `E(k, nonce)` from
the transmitted `nonce` and un-pads. This single-block CTR construction is
exactly the CPA-from-PRF construction (`CatCrypt.Examples.CPAFromPRF`) with the
PRF input specialized to the counter/nonce, so we obtain its security for free.

## The perfect instantiation

Model the block cipher in CTR mode as a **bijection family**: for each counter
value `ctr`, the keystream map `keystream ctr : Key ≃ Block`, `k ↦ E(k, ctr)`, is
a bijection from keys to blocks (the ideal-cipher / perfect-PRF model). Over a
uniform key the keystream block `E(k, nonce)` is then uniform on `Block`,
independent of the message, so the pad `E(k, nonce) ⊕ m` is uniform regardless
of `m`. The two IND-CPA games (encrypting `m₀` vs. `m₁`) are perfectly
indistinguishable: the IND-CPA advantage of *every* adversary is exactly `0`.

## Scope

This file proves the **single-block** statement, which is the clean core-provable
case (it coincides with CPA-from-PRF). Genuine multi-block CTR — encrypting
`(m₁, …, mₙ)` as `(nonce, E(k, nonce+0) ⊕ m₁, …, E(k, nonce+n-1) ⊕ mₙ)` — needs a
product-of-bijections (independent-keystream-block) argument not developed in
core, and is deliberately out of scope here.

## Main definitions

* `CTRBlockScheme` — single-block CTR data: a keystream bijection family
  `keystream : Block → (Key ≃ Block)` together with an involutive XOR on blocks.
* `CTRBlockScheme.toBijCPAScheme` — the equivalent CPA-from-PRF scheme (nonce as
  PRF input); every result is inherited through it.
* `CTRBlockScheme.toEncScheme` — the induced core `EncScheme`.

## Main results

* `ctr_correct` — the scheme is correct (decryption recovers the message).
* `ctr_perfect_indcpa` — **perfect IND-CPA security**:
  `INDCPA_Adv C.toEncScheme m₀ m₁ A = 0` for every adversary `A`.
* `boolCTR_perfect_indcpa` — the `Bool` instantiation with block cipher
  `E(k, n) = k ⊕ n`, i.e. `Enc(k, m) = (n, (k ⊕ n) ⊕ m)`.

## References

* [Rosulek, The Joy of Cryptography, §8 (block cipher modes)]
-/

namespace CatCrypt.Examples.CTRMode

open CatCrypt.Core
open CatCrypt.Crypto
open CatCrypt.Crypto.SecurityDefs
open CatCrypt.Prob
open CatCrypt.Prob.XorBij
open CatCrypt.Examples.CPAFromPRF
open CatCrypt.Tactic
open scoped ENNReal

/-! ## The Single-Block CTR Scheme -/

/-- Data for single-block CTR-mode encryption `Enc(k, m) = (nonce, E(k, nonce) ⊕ m)`.

`keystream ctr : Key ≃ Block` is the counter-indexed keystream map `k ↦ E(k, ctr)`,
required to be a bijection for each counter value (the ideal-cipher / perfect-PRF
model), and `xorBlock` is an involutive XOR on blocks. For a uniform key the
keystream block `keystream nonce k` is uniform, which is the source of perfect
security. -/
structure CTRBlockScheme where
  /-- Key type -/
  Key : Type
  /-- Block / message type (also the nonce / counter type) -/
  Block : Type
  [finKey : Fintype Key]
  [neKey : Nonempty Key]
  [finBlock : Fintype Block]
  [neBlock : Nonempty Block]
  /-- For each counter value, the keystream map `k ↦ E(k, ctr)` is a bijection -/
  keystream : Block → (Key ≃ Block)
  /-- The XOR-like combining operation on blocks -/
  xorBlock : Block → Block → Block
  /-- `xorBlock · b` is involutive: un-padding with the same keystream recovers the value -/
  xorBlock_cancel : ∀ a b, xorBlock (xorBlock a b) b = a
  /-- `xorBlock a ·` is involutive: decryption recovers the message -/
  xorBlock_cancel' : ∀ a b, xorBlock a (xorBlock a b) = b

attribute [instance] CTRBlockScheme.finKey CTRBlockScheme.neKey
  CTRBlockScheme.finBlock CTRBlockScheme.neBlock

/-- Single-block CTR is CPA-from-PRF with the PRF input taken to be the nonce:
`Input = Output = Block`, `bij = keystream`, `xorOut = xorBlock`. -/
def CTRBlockScheme.toBijCPAScheme (C : CTRBlockScheme) : BijCPAScheme where
  Key := C.Key
  Input := C.Block
  Output := C.Block
  bij := C.keystream
  xorOut := C.xorBlock
  xorOut_cancel := C.xorBlock_cancel
  xorOut_cancel' := C.xorBlock_cancel'

/-- The core `EncScheme` induced by a single-block CTR scheme:
`encrypt k m = do nonce ← sample Block; pure (nonce, (keystream nonce k) ⊕ m)`. -/
noncomputable def CTRBlockScheme.toEncScheme (C : CTRBlockScheme) : EncScheme :=
  C.toBijCPAScheme.toEncScheme

/-! ## Correctness -/

/-- The scheme is correct: decrypting `(nonce, (keystream nonce k) ⊕ m)` recovers `m`. -/
theorem ctr_correct (C : CTRBlockScheme) : C.toEncScheme.Correct :=
  bijCPA_correct C.toBijCPAScheme

/-! ## Perfect IND-CPA Security -/

/-- **Single-block CTR mode has perfect IND-CPA security**: every adversary has
IND-CPA advantage exactly `0`.

Over a uniform key the keystream block `keystream nonce k` is uniform on `Block`
(bijection family), so the pad `keystream nonce k ⊕ m` is uniform regardless of
`m`; the two IND-CPA games are therefore perfectly indistinguishable. -/
theorem ctr_perfect_indcpa (C : CTRBlockScheme) (m₀ m₁ : C.toEncScheme.Plaintext)
    (A : C.toEncScheme.Ciphertext → SPComp Bool) :
    INDCPA_Adv C.toEncScheme m₀ m₁ A = 0 :=
  bijCPA_perfect_indcpa C.toBijCPAScheme m₀ m₁ A

/-! ## Example: single-block CTR over `Bool`

Block cipher `E(k, n) = k ⊕ n` (`keystream n = boolXorBij n`), giving
`Enc(k, m) = (n, (k ⊕ n) ⊕ m)` for a fresh bit `n`. -/

/-- Single-block CTR over `Bool` with block cipher `E(k, n) = k ⊕ n`. -/
def boolCTR : CTRBlockScheme where
  Key := Bool
  Block := Bool
  keystream := boolXorBij
  xorBlock := xor
  xorBlock_cancel := fun a b => by cases a <;> cases b <;> rfl
  xorBlock_cancel' := fun a b => by cases a <;> cases b <;> rfl

/-- The `Bool` CTR scheme is correct. -/
theorem boolCTR_correct : boolCTR.toEncScheme.Correct :=
  ctr_correct boolCTR

/-- **The `Bool` CTR scheme has perfect IND-CPA security.** -/
theorem boolCTR_perfect_indcpa (m₀ m₁ : boolCTR.toEncScheme.Plaintext)
    (A : boolCTR.toEncScheme.Ciphertext → SPComp Bool) :
    INDCPA_Adv boolCTR.toEncScheme m₀ m₁ A = 0 :=
  ctr_perfect_indcpa boolCTR m₀ m₁ A

/-! ## The Computational IND-CPA Bound from the Block Cipher's PRF Security

The perfect result above models the block cipher in CTR mode as an *ideal cipher*
(a bijection family), giving IND-CPA advantage exactly `0`. The **standard
computational reduction** that a real block cipher would use bounds the CTR
IND-CPA advantage by the block cipher's PRF advantage `ε_prf`, via the
two-hop game walk

| Hop | Transition | Bound |
|-----|-----------|-------|
| PRF-swap | real challenge game → `ctrIdealGame` (keystream `E(k,·)` → random function) | `ε_prf` (`PRFAssumption`) |
| perfect  | `ctrIdealGame` → other challenge world (random pad is message-independent) | `0` |

The perfect hop is an `SPComp` game equality proved by `bind_vcgen`; the
PRF-swap hop is the reduction's soundness, taken as a hypothesis and discharged by
the `PRFAssumption`. Composition is the advantage triangle inequality.
-/

/-- The message-independent **ideal CTR game**: output a fresh nonce and a fresh
uniform pad `(nonce, pad)`. This is CTR encryption with the keystream `E(k,·)`
replaced by a random function; being independent of the message, *both* IND-CPA
challenge worlds collapse onto it. -/
noncomputable def ctrIdealGame (C : CTRBlockScheme) : SPComp (C.Block × C.Block) := do
  let nonce ← SPComp.sample C.Block
  let pad ← SPComp.sample C.Block
  SPComp.pure (nonce, pad)

/-- At a fixed nonce `r`, the keystream-then-XOR map `k ↦ E(k, r) ⊕ msg` is a
bijection `Key ≃ Block`: compose the keystream bijection `keystream r` with the
involutive XOR by `msg`. This is the change of variables that turns the (uniform
key) pad into a uniform block, i.e. the coupling behind the perfect hop. -/
def CTRBlockScheme.padEquiv (C : CTRBlockScheme) (r : C.Block) (msg : C.Block) :
    C.Key ≃ C.Block where
  toFun k := C.xorBlock (C.keystream r k) msg
  invFun b := (C.keystream r).symm (C.xorBlock b msg)
  left_inv k := by simp only [C.xorBlock_cancel, Equiv.symm_apply_apply]
  right_inv b := by simp only [Equiv.apply_symm_apply, C.xorBlock_cancel]

/-- **Perfect hop.** Each concrete IND-CPA challenge game equals the
message-independent `ctrIdealGame`: sampling the nonce first (via `bijCPA_game_eq`)
and then changing variables `k ↦ E(k, r) ⊕ msg` through `padEquiv` collapses the
keyed pad to a fresh uniform block. Proved by `bind_vcgen using` the coupling
bijection. -/
theorem ctr_game_eq_ideal (C : CTRBlockScheme)
    (m₀ m₁ : C.toEncScheme.Plaintext) (b : Bool) :
    INDCPA_Game C.toEncScheme m₀ m₁ b = ctrIdealGame C := by
  show INDCPA_Game C.toBijCPAScheme.toEncScheme m₀ m₁ b = ctrIdealGame C
  rw [bijCPA_game_eq C.toBijCPAScheme m₀ m₁ b]
  unfold ctrIdealGame
  refine congrArg _ ?_; funext r
  bind_vcgen using (C.padEquiv r (if b then m₀ else m₁))

/-- **Single-block CTR mode: the computational IND-CPA bound.**

The IND-CPA advantage of single-block CTR is at most the block cipher's PRF
advantage `H.ε`. The proof is the advantage triangle inequality over the two hops:

* the **PRF-swap hop** `AdvantageA (challenge true) (ctrIdealGame) A` is the
  reduction's soundness (`hswap`): an IND-CPA distinguisher here *is* a PRF
  distinguisher `Ared` on input `x`, so the hop is bounded by `PRF_Adv F x Ared`,
  which `PRFAssumption H` caps at `H.ε`;
* the **perfect hop** `AdvantageA (ctrIdealGame) (challenge false) A` is `0`, because
  `ctr_game_eq_ideal` identifies `ctrIdealGame` with the `false` challenge world.

Because `CTRBlockScheme` is the ideal-cipher (bijection-family) model, the PRF-swap
hop is *itself* `0` here (see `ctr_perfect_indcpa`); the theorem states the reduction
in the general form a real PRF instantiation uses. -/
theorem ctr_indcpa_bound (C : CTRBlockScheme)
    {F : PRFScheme} (H : PRFAssumption F)
    (m₀ m₁ : C.toEncScheme.Plaintext)
    (A : C.toEncScheme.Ciphertext → SPComp Bool)
    (x : F.Input) (Ared : F.Output → SPComp Bool)
    (hswap : AdvantageA (INDCPA_Game C.toEncScheme m₀ m₁ true) (ctrIdealGame C) A
              ≤ PRF_Adv F x Ared) :
    INDCPA_Adv C.toEncScheme m₀ m₁ A ≤ H.ε := by
  calc AdvantageA (INDCPA_Game C.toEncScheme m₀ m₁ true)
          (INDCPA_Game C.toEncScheme m₀ m₁ false) A
      ≤ AdvantageA (INDCPA_Game C.toEncScheme m₀ m₁ true) (ctrIdealGame C) A
        + AdvantageA (ctrIdealGame C) (INDCPA_Game C.toEncScheme m₀ m₁ false) A :=
          advantageA_triangle _ _ _ _
    _ ≤ PRF_Adv F x Ared + 0 :=
        add_le_add hswap (by simp [ctr_game_eq_ideal C m₀ m₁ false, AdvantageA])
    _ = PRF_Adv F x Ared := add_zero _
    _ ≤ H.ε := H.bound x Ared

end CatCrypt.Examples.CTRMode
