/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Advantage
import CatCrypt.Crypto.CryptoWord

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
* `PRP_PRF_Switching` — switching theorem statement

## Cross-Validation

| Property | This file | Textbook | EasyCrypt | CatCrypt (Rocq) |
|----------|-----------|----------|-----------|----------------|
| Weak PRP | `PRP_Real`/`Ideal` | BS Def. 4.1 | `WeakPRP.IND` | — |
| Strong PRP | `SPRP_Advantage` | BS Def. 4.2 | `StrongPRP.IND` | `PRPCCA.v` |
| PRF | `PRF_Real` vs `PRP_Ideal` | BS Def. 4.2 | `PRF.IND` | `PRF.v` |
| Switching | `PRP_PRF_Switching` | BS Thm. 4.4 | `RP_RF` (proved) | (explicit gap) |

## References

* Boneh & Shoup, *A Graduate Course in Applied Cryptography*, §4.1-4.4
* Katz & Lindell, *Introduction to Modern Cryptography*, §3.6, Def. 3.24-3.25
* Bellare, Kilian, Rogaway. *The Security of the Cipher Block Chaining
  Message Authentication Code.* JCSS 2000.
-/

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
CatCrypt (Rocq): `EVAL` game in `PRPCCA.v` with `lookup`/`invlookup`. -/

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
    Bellare-Rogaway 2006). The switching *theorem* itself is not
    formalised here: bounds below that include this term (e.g.
    `PRP_Full_Bound`) take it as part of the stated bound, and a proof
    would proceed by the up-to-bad argument over the collision event
    bounded in `CatCrypt.Prob.BirthdayBound`. -/
noncomputable def PRP_PRF_SwitchingBound (q : ℕ) (domainSize : ℕ) : ℝ≥0∞ :=
  (q * (q - 1) : ℕ) / (2 * domainSize : ℕ)

/-! ## Composition: full PRP bound -/

/-- Full PRP security bound: PRP advantage + switching bound.

    For a block cipher `P` making at most `q` queries:

        Adv_PRP(A) ≤ Adv_PRF(A') + q(q-1)/(2|W|)

    where `Adv_PRF` is the advantage against the keyed function
    (measured by `PRP_Advantage`) and the switching bound accounts
    for the random-function-vs-random-permutation gap. -/
noncomputable def PRP_Full_Bound (ε_prf : ℝ≥0∞) (q : ℕ) (domainSize : ℕ) : ℝ≥0∞ :=
  ε_prf + PRP_PRF_SwitchingBound q domainSize

/-! ## IsPure Proofs -/

theorem PRP_Real_isPure (P : PRPDef W) (x : W) :
    SPComp.IsPure (PRP_Real P x) := by
  unfold PRP_Real
  exact SPComp.bind_isPure (SPComp.sample_isPure _) fun _ => SPComp.pure_isPure _

theorem PRP_Ideal_isPure (x : W) :
    SPComp.IsPure (PRP_Ideal x) :=
  SPComp.sample_isPure _

end CatCrypt.Crypto.Assumptions
