/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.CryptoWord
public import CatCryptCore.Crypto.PRPPRFSwitching

/-!
# PRP (Pseudorandom Permutation), SPRP, and PRP/PRF Switching

Abstract PRP/SPRP definitions and the PRP/PRF switching lemma for
block cipher security. Used by CMAC, AES-GCM, and other constructions.

## Main definitions

### Weak PRP (forward-only)
* `PRP_Real` / `PRP_Ideal` — weak PRP game (forward oracle only)
* `PRP_Advantage` — PRF-distinguishing advantage of the block cipher

### Strong PRP (forward + inverse)
* `SPRP_Adversary` — adversary with access to both `enc` and `dec` oracles
* `SPRP_Advantage` — strong PRP advantage

### PRF
* `PRFDef` / `PRF_Real` — pseudorandom function game
* `PRF_Advantage` — PRF advantage (single-query)

### PRP/PRF Switching
* `PRP_PRF_SwitchingBound` — birthday bound `q(q-1)/(2|W|)`
* `RF_RP_Advantage_le_PRP_PRF_SwitchingBound` — the adaptive random-function/random-injection
  advantage of a `q`-query adversary (`CatCryptCore.Crypto.PRPPRFSwitching`) is at most
  `PRP_PRF_SwitchingBound q |R|`
* `PRP_q_Advantage_le_PRP_Full_Bound` — the adaptive PRP advantage is at most
  `PRP_Full_Bound` of the adaptive PRF advantage

## Cross-Validation

| Property | This file | Textbook | EasyCrypt | SSProve (Rocq) |
|----------|-----------|----------|-----------|----------------|
| Weak PRP | `PRP_Real`/`Ideal` | BS Def. 4.1 | `WeakPRP.IND` | — |
| Strong PRP | `SPRP_Advantage` | BS Def. 4.2 | `StrongPRP.IND` | `PRPCCA.v` |
| PRF | `PRF_Real` vs `PRP_Ideal` | BS Def. 4.2 | `PRF.IND` | `PRF.v` |
| Switching | `RF_RP_Advantage_le_PRP_PRF_SwitchingBound` | BS Thm. 4.4 | `RP_RF` (proved) | (explicit gap) |

## References

* Boneh & Shoup, *A Graduate Course in Applied Cryptography*, §4.1-4.4
* Katz & Lindell, *Introduction to Modern Cryptography*, §3.6, Def. 3.24-3.25
* Bellare, Kilian, Rogaway. *The Security of the Cipher Block Chaining
  Message Authentication Code.* JCSS 2000.
-/

@[expose] public section

namespace CatCrypt.Crypto.Assumptions

open CatCrypt.Core CatCrypt.Prob
open scoped ENNReal

variable {W : Type} [SampleableType W]

/-! ## PRP Definition -/

/-- Abstract PRP (pseudorandom permutation / block cipher) scheme.

A PRP is a keyed family of permutations: for each key k,
E(k, ·) is a bijection on the block space W. -/
structure PRPDef (W : Type) [SampleableType W] where
  /-- Block cipher: key → plaintext → ciphertext -/
  enc : W → W → W
  /-- Inverse: key → ciphertext → plaintext -/
  dec : W → W → W

/-- PRP real game: keyed permutation. -/
noncomputable def PRP_Real (P : PRPDef W) (x : W) : SPComp W := do
  let k ← SPComp.sample W
  pure (P.enc k x)

/-- PRP ideal game: uniformly random output (i.e., random **function**, not
random permutation).

This deliberately uses a random function as the ideal object, following the
convention where the PRP/PRF switching lemma (Boneh-Shoup Thm. 4.4) bridges
the gap between a random function and a random permutation. The switching
bound is `q(q-1)/(2|W|)` — see `PRP_PRF_SwitchingBound` below.

Consequently, `PRP_Advantage` measures the PRF-distinguishing advantage of
the block cipher, and the full PRP security bound is:

    Adv_PRP ≤ PRP_Advantage + PRP_PRF_SwitchingBound q |W| -/
noncomputable def PRP_Ideal (x : W) : SPComp W :=
  SPComp.sample W

/-- PRP advantage: distinguishing the keyed permutation from a random
**function** (not a random permutation).  See `PRP_Ideal` and
`PRP_PRF_SwitchingBound` for the full picture. -/
noncomputable def PRP_Advantage (P : PRPDef W) (x : W)
    (A : W → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (PRP_Real P x) (PRP_Ideal x) A

/-! ## PRF Definition (keyed function) -/

/-- Abstract PRF (pseudorandom function) scheme. -/
structure PRFDef (W : Type) [SampleableType W] where
  /-- PRF evaluation: key → input → output -/
  eval : W → W → W

/-- PRF real game (single-query): sample key, return F_k(x).

This is the single-query formulation. The standard multi-query PRF game
(Boneh-Shoup Def. 4.1) gives the adversary adaptive access to the oracle.
The multi-query bound is: Adv_q ≤ q · Adv_1 via hybrid argument.
See `CatCrypt.Crypto.MultiQueryPRF.prf_multi_query_bound`. -/
noncomputable def PRF_Real (F : PRFDef W) (x : W) : SPComp W := do
  let k ← SPComp.sample W
  pure (F.eval k x)

/-- PRF advantage (single-query): distinguishing F_k(x) from random. -/
noncomputable def PRF_Advantage (F : PRFDef W) (x : W)
    (A : W → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (PRF_Real F x) (PRP_Ideal x) A

/-! ## Strong PRP (SPRP)

The strong PRP game gives the adversary access to both the forward
permutation `enc` and the inverse `dec`. This is needed by protocols
that use block cipher decryption (e.g., CBC mode).

EasyCrypt: `StrongPRP.IND` in `PRP.eca`.
SSProve (Rocq): `EVAL` game in `PRPCCA.v` with `lookup`/`invlookup`. -/

/-- Strong PRP adversary: receives both forward and inverse oracles.

    The adversary can query `enc_oracle(x) = E(k, x)` and
    `dec_oracle(y) = D(k, y)` and tries to distinguish from
    a random permutation and its inverse. -/
structure SPRP_Adversary (W : Type) where
  /-- The adversary: receives forward and inverse oracles, outputs a bit. -/
  run : (enc_oracle : W → SPComp W) → (dec_oracle : W → SPComp W) → SPComp Bool

/-- Strong PRP real game: adversary gets keyed `enc` and `dec`. -/
noncomputable def SPRP_Real (P : PRPDef W) (A : SPRP_Adversary W) : SPComp Bool := do
  let k ← SPComp.sample W
  A.run (fun x => SPComp.pure (P.enc k x)) (fun y => SPComp.pure (P.dec k y))

/-- Strong PRP ideal game: adversary gets independent random functions.

    In the true ideal game the oracles would be a random permutation
    and its inverse (maintaining consistency). We approximate with
    independent random functions; the difference is bounded by the
    birthday term `PRP_PRF_SwitchingBound`. -/
noncomputable def SPRP_Ideal (A : SPRP_Adversary W) : SPComp Bool :=
  A.run (fun _ => SPComp.sample W) (fun _ => SPComp.sample W)

/-- Strong PRP advantage. -/
noncomputable def SPRP_Advantage (P : PRPDef W) (A : SPRP_Adversary W) : ℝ≥0∞ :=
  Advantage (SPRP_Real P A) (SPRP_Ideal A)

/-! ## PRP/PRF Switching Lemma -/

/-- PRP/PRF switching bound: the difference between a random permutation
    and a random function for q queries is at most q(q-1)/(2|W|).

    This is the standard birthday-bound result (Boneh-Shoup Thm. 4.4,
    Bellare-Rogaway 2006). `RF_RP_Advantage_le_PRP_PRF_SwitchingBound` below bounds the
    adaptive switching game of `CatCryptCore.Crypto.PRPPRFSwitching` by this term. -/
noncomputable def PRP_PRF_SwitchingBound (q : ℕ) (domainSize : ℕ) : ℝ≥0∞ :=
  (q * (q - 1) : ℕ) / (2 * domainSize : ℕ)

/-! ## Composition: full PRP bound -/

/-- Full PRP security bound: PRP advantage + switching bound.

    For a block cipher `P` making at most `q` queries:

        Adv_PRP(A) ≤ Adv_PRF(A') + q(q-1)/(2|W|)

    where `Adv_PRF` is the advantage against the keyed function
    and the switching bound accounts for the random-function-vs-random-permutation
    gap. `PRP_q_Advantage_le_PRP_Full_Bound` below proves this bound for the adaptive
    games of `CatCryptCore.Crypto.PRPPRFSwitching`. -/
noncomputable def PRP_Full_Bound (ε_prf : ℝ≥0∞) (q : ℕ) (domainSize : ℕ) : ℝ≥0∞ :=
  ε_prf + PRP_PRF_SwitchingBound q domainSize

/-! ## Connection to the adaptive switching game -/

/-- `PRP_PRF_SwitchingBound q N` is `⌊q(q-1)/2⌋ / N`, the form of the bound in
`PRPPRF.RF_RP_Advantage_le`: `q(q-1)` is even. -/
theorem PRP_PRF_SwitchingBound_eq_div (q N : ℕ) :
    PRP_PRF_SwitchingBound q N = ((q * (q - 1) / 2 : ℕ) : ℝ≥0∞) / (N : ℝ≥0∞) := by
  obtain ⟨m, hm⟩ := Nat.even_mul_pred_self q
  unfold PRP_PRF_SwitchingBound
  rw [hm, ← two_mul, Nat.mul_div_cancel_left _ two_pos, Nat.cast_mul, Nat.cast_mul]
  exact ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)

section Switching

open CatCrypt.Crypto.PRPPRF

variable {D R K : Type} [DecidableEq D] [DecidableEq R] [Fintype R] [Nonempty R]
  [Fintype K] [Nonempty K]

/-- **PRP/PRF switching with `PRP_PRF_SwitchingBound`.** An adversary asking at most `q`
adaptive queries distinguishes the lazy random function from the lazy random injection
with advantage at most `PRP_PRF_SwitchingBound q |R|`. -/
theorem RF_RP_Advantage_le_PRP_PRF_SwitchingBound (A : OracleAdv D R Bool) (q : ℕ)
    (hA : A.IsQueryBound q) :
    RF_RP_Advantage A ≤ PRP_PRF_SwitchingBound q (Fintype.card R) :=
  (RF_RP_Advantage_le A q hA).trans_eq (PRP_PRF_SwitchingBound_eq_div q _).symm

/-- **Full PRP bound for the adaptive games.** For an adversary asking at most `q`
adaptive queries, the PRP advantage of a keyed function `P` is at most
`PRP_Full_Bound` of its PRF advantage: the PRF advantage plus
`PRP_PRF_SwitchingBound q |R|`. -/
theorem PRP_q_Advantage_le_PRP_Full_Bound (P : K → D → R) (A : OracleAdv D R Bool) (q : ℕ)
    (hA : A.IsQueryBound q) :
    PRP_q_Advantage P A ≤ PRP_Full_Bound (PRF_q_Advantage P A) q (Fintype.card R) :=
  (advantage_triangle _ (rfGame A) _).trans
    (add_le_add le_rfl (RF_RP_Advantage_le_PRP_PRF_SwitchingBound A q hA))

end Switching

/-! ## IsPure Proofs -/

theorem PRP_Real_isPure (P : PRPDef W) (x : W) :
    SPComp.IsPure (PRP_Real P x) := by
  unfold PRP_Real
  exact SPComp.bind_isPure (SPComp.sample_isPure _) fun _ => SPComp.pure_isPure _

theorem PRP_Ideal_isPure (x : W) :
    SPComp.IsPure (PRP_Ideal x) :=
  SPComp.sample_isPure _

end CatCrypt.Crypto.Assumptions
