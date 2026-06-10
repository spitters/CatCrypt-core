/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Advantage
import CatCrypt.Crypto.Assumptions.DDH
import CatCrypt.Tactics

/-!
# Computational Diffie-Hellman (CDH) Assumption

The CDH assumption: given `(g^a, g^b)`, compute the shared secret `g^{ab}`.
This is the computational analogue of DDH; DDH ⟹ CDH but not vice versa.

## Main definitions

* `CDH_Game` — the CDH game
* `CDH_Advantage` — probability of computing the shared secret
* `CDHSecure` — CDH hardness assumption
* `DL_Adversary_DDH` — discrete log adversary over `DDHDef`
* `DL_Game_DDH` — discrete log game over `DDHDef`
* `cdh_of_dl_ddh` — CDH adversary from DL adversary (CDH ⟹ DL reduction)

## Cross-Validation

| Property | This file | Textbook |
|----------|-----------|----------|
| Challenge | `(g^a, g^b)` | Boneh-Shoup Def. 11.1 |
| Target | Compute `ecdh(a, g^b) = g^{ab}` | Compute `g^{ab}` |
| Group | `DDHDef W` | Cyclic group of prime order |
| CDH ⟹ DL | `cdh_of_dl_ddh` | BS Prop. 11.4 |

**Equivalent formalizations:**
- EasyCrypt: `CDH` theory in `theories/crypto/DiffieHellman.ec`
- SSProve (Rocq): not formalized (only DDH)

**Relationship to other assumptions:**
- DDH ⟹ CDH (if you can't distinguish, you can't compute)
- CDH ⟹ DL (if you can compute DH, you can compute discrete logs)
- co-CDH (in `CoCDH.lean`) is the Type-III bilinear variant

See also `CDH_DL.lean` for the CDH ⟹ DL reduction over `PairingGroup`.

## References

* Boneh & Shoup, *A Graduate Course in Applied Cryptography*, §11.3, Def. 11.1; §11.3 Prop. 11.4
* Diffie & Hellman, *New Directions in Cryptography*, IEEE-IT 1976
-/

namespace CatCrypt.Crypto.Assumptions

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

variable {W : Type} [SampleableType W] [DecidableEq W]

/-! ## CDH Game -/

/-- CDH adversary: given `(g^a, g^b)`, attempts to compute the shared
    secret `ecdh(a, g^b) = g^{ab}`. -/
abbrev CDH_Adversary (W : Type) := W → W → SPComp W

/-- CDH game: sample key pairs `(a, g^a)` and `(b, g^b)`, give `(g^a, g^b)`
    to adversary, check if output equals `ecdh(a, g^b)`.

    Returns `true` if the adversary computes the correct shared secret. -/
noncomputable def CDH_Game (D : DDHDef W) (A : CDH_Adversary W) : SPComp Bool := do
  let ⟨a, g_a⟩ ← D.keygen
  let ⟨_, g_b⟩ ← D.keygen
  let answer ← A g_a g_b
  let target := D.ecdh a g_b  -- = g^{ab}
  SPComp.pure (decide (answer = target))

/-- CDH advantage: probability that the adversary computes `g^{ab}`. -/
noncomputable def CDH_Advantage (D : DDHDef W) (A : CDH_Adversary W) : ℝ≥0∞ :=
  prTrue (CDH_Game D A) Heap.empty

/-- CDH hardness: all adversaries have bounded advantage. -/
def CDHSecure (D : DDHDef W) (ε : ℝ≥0∞) : Prop :=
  ∀ (A : CDH_Adversary W), CDH_Advantage D A ≤ ε

/-! ## Reduction: DDH ⟹ CDH

If an adversary can compute `g^{ab}` (break CDH), it can also
distinguish `(g^a, g^b, g^{ab})` from `(g^a, g^b, random)` (break DDH),
by computing the answer and comparing. -/

/-- Construct a DDH adversary from a CDH adversary: compute the
    alleged shared secret and check if it matches the challenge. -/
noncomputable def ddh_of_cdh (A : CDH_Adversary W) : DDH_Adversary W :=
  fun g_a g_b challenge => do
    let answer ← A g_a g_b
    SPComp.pure (decide (answer = challenge))

/-! ## IsPure Proofs -/

theorem CDH_Game_isPure (D : DDHDef W) (A : CDH_Adversary W)
    (hA : ∀ x y, SPComp.IsPure (A x y)) :
    SPComp.IsPure (CDH_Game D A) := by
  unfold CDH_Game
  apply SPComp.bind_isPure D.keygen_isPure; intro ⟨a, g_a⟩
  apply SPComp.bind_isPure D.keygen_isPure; intro ⟨_, g_b⟩
  apply SPComp.bind_isPure (hA g_a g_b); intro answer
  exact SPComp.pure_isPure _

/-! ## Reduction: CDH ⟹ DL (abstract DDHDef setting)

The standard direction: CDH hard implies DL hard (BS Prop. 11.4).
Equivalently, by contrapositive: if you can solve DL (find private keys
from public keys), you can solve CDH.

In the abstract `DDHDef` setting, a "discrete log adversary" receives a
public key `g^a` and returns a private key `a'` such that the corresponding
public key matches. We define this via `keygen`'s structure: the adversary
must recover the private component from the public component.

**Reduction.** Given a DL adversary that finds `a` from `g^a`:
1. Receive CDH challenge `(g^a, g^b)`
2. Run the DL adversary on `g^a` to recover `a`
3. Compute `ecdh(a, g^b) = g^{ab}`

This gives a CDH adversary whose advantage equals the DL advantage. -/

/-- DL adversary over abstract DDHDef: given a public key `g^a`,
    attempts to find the corresponding private key `a`. -/
abbrev DL_Adversary_DDH (W : Type) := W → SPComp W

/-- DL game over abstract DDHDef: sample a key pair `(a, g^a)`,
    give `g^a` to the adversary, check if the adversary's output `a'`
    yields the same public key (i.e., `ecdh(a', G) = g^a` conceptually,
    but since we only have `ecdh : W → W → W`, we check that the adversary
    can reproduce the DH shared secret).

    Concretely: sample `(a, g^a)` and `(b, g^b)`, give `g^a` to the
    adversary to get `a'`, then check `ecdh(a', g^b) = ecdh(a, g^b)`. -/
noncomputable def DL_Game_DDH (D : DDHDef W) (A : DL_Adversary_DDH W) : SPComp Bool := do
  let ⟨a, g_a⟩ ← D.keygen
  let ⟨_, g_b⟩ ← D.keygen
  let a' ← A g_a
  SPComp.pure (decide (D.ecdh a' g_b = D.ecdh a g_b))

/-- DL advantage over abstract DDHDef. -/
noncomputable def DL_Advantage_DDH (D : DDHDef W) (A : DL_Adversary_DDH W) : ℝ≥0∞ :=
  prTrue (DL_Game_DDH D A) Heap.empty

/-- Construct a CDH adversary from a DL adversary.

    Given a DL adversary that finds private keys from public keys:
    1. Receive `(g^a, g^b)`
    2. Run the DL adversary on `g^a` to get candidate private key `a'`
    3. Compute `ecdh(a', g^b)` as the alleged shared secret -/
noncomputable def cdh_of_dl_ddh (D : DDHDef W)
    (A_dl : DL_Adversary_DDH W) : CDH_Adversary W :=
  fun g_a _g_b => do
    let a' ← A_dl g_a
    SPComp.pure (D.ecdh a' _g_b)

/-- CDH ⟹ DL bound: any DL adversary yields a CDH adversary with
    at least as much advantage.

    `CDH_Advantage D (cdh_of_dl_ddh D A_dl) ≥ DL_Advantage_DDH D A_dl`

    Equivalently (for the standard "hardness implies hardness" direction):
    `DL_Advantage_DDH D A_dl ≤ CDH_Advantage D (cdh_of_dl_ddh D A_dl)` -/
theorem dl_le_cdh_ddh (D : DDHDef W)
    (A_dl : DL_Adversary_DDH W) :
    DL_Advantage_DDH D A_dl ≤ CDH_Advantage D (cdh_of_dl_ddh D A_dl) := by
  -- The two games are equal: both sample (a, g_a), (_, g_b), run A_dl(g_a)
  -- to get a', and check ecdh(a', g_b) = ecdh(a, g_b).
  -- CDH_Game inlines cdh_of_dl_ddh which does A_dl(g_a) >>= pure(ecdh(a', g_b)),
  -- then checks answer = target. After bind_assoc + pure_bind, this is identical.
  have hgame : DL_Game_DDH D A_dl = CDH_Game D (cdh_of_dl_ddh D A_dl) := by
    unfold DL_Game_DDH CDH_Game cdh_of_dl_ddh
    -- The CDH side has a nested bind: (A_dl g_a >>= fun a' => pure(ecdh a' g_b)) >>= fun answer => pure(decide(...))
    -- Flatten with bind_assoc then simplify pure_bind
    simp only [SPComp.monad_bind_eq]
    simp only [SPComp.bind_assoc, SPComp.pure_bind]
  unfold DL_Advantage_DDH CDH_Advantage
  rw [hgame]

/-- Corollary: CDH security implies DL security.

    If `D` is `ε`-CDH-secure, then for any DL adversary, the DL advantage
    is at most `ε`. -/
theorem cdh_secure_implies_dl_secure (D : DDHDef W)
    (ε : ℝ≥0∞) (h_cdh : CDHSecure D ε)
    (A_dl : DL_Adversary_DDH W) :
    DL_Advantage_DDH D A_dl ≤ ε := by
  calc DL_Advantage_DDH D A_dl
      ≤ CDH_Advantage D (cdh_of_dl_ddh D A_dl) := dl_le_cdh_ddh D A_dl
    _ ≤ ε := h_cdh _

end CatCrypt.Crypto.Assumptions
