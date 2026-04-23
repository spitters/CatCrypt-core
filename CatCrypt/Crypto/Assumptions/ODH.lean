/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Advantage
import CatCrypt.Crypto.Assumptions.DDH
import CatCrypt.Tactics

/-!
# Oracle Diffie-Hellman (ODH) Assumption

This file defines the ODH assumption parametrically over any `SampleableType W`,
following the pattern of `DDH.lean`.

## ODH Game

The ODH assumption (Abdalla-Bellare-Rogaway, CT-RSA 2001) captures the difficulty
of distinguishing `H(g^{ab})` from random, given `(g^a, g^b)` and oracle access
to `H`. The simplified formulation used here (following the EasyCrypt pattern)
makes the hash oracle implicit: given `(g^a, g^b)`, distinguish `hash(ecdh(a, g^b))`
from random. When `hash` is the identity, this reduces to DDH.

At the abstract level with `SampleableType W`, the ODH game becomes:
- **Real**: sample `a, b`, give `(pub_a, pub_b, hash(ecdh(a, pub_b), label))` to adversary
- **Ideal**: sample `a, b, r`, give `(pub_a, pub_b, r)` to adversary

## Main definitions

* `ODHDef` — extends DDHDef with a hash function `hash : W → W → W`
* `ODH_Adversary` — adversary receiving (pub_a, pub_b, challenge), outputs (label, Bool)
* `ODH_Game_Real` / `ODH_Game_Ideal` — the real/ideal ODH games
* `ODH_Advantage` — advantage of an adversary in breaking ODH
* `ODHSecure` — security predicate: all adversaries have bounded advantage

## Reduction: DDH + PRF ⟹ ODH

The standard reduction (ABR01 Thm 2): if `hash` is a PRF keyed by the DH secret,
then ODH security reduces to DDH + PRF security:

    ODH_Advantage ≤ DDH_Advantage + PRF_Advantage

* `odh_of_ddh_prf` — the reduction theorem (sorry for proof body)

## Cross-Validation

| Property | This file | EasyCrypt |
|----------|-----------|----------|
| ODH game | `ODH_Game_Real`/`Ideal` | `ODH0`/`ODH1` in `ODH.ec` |
| Hash oracle | Implicit (via PRF) | Explicit `H.hash` oracle |
| Advantage | `Advantage(Real, Ideal)` | `|Pr[ODH0] - Pr[ODH1]|` |

## References

* Abdalla, Bellare, Rogaway. *DHIES: An Encryption Scheme Based on the
  Diffie-Hellman Problem.* CT-RSA 2001, §3.
* Boneh & Shoup, *A Graduate Course in Applied Cryptography*, §12.4.
* EasyCrypt: `assumptions/ODH.ec`
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Assumptions

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

variable {W : Type} [SampleableType W]

/-! ## ODH Definition -/

/-- Abstract Oracle Diffie-Hellman definition, extending DDH with a hash function.

- `hash secret label` models `H(g^{ab}, label)` — a keyed hash where the
  DH shared secret acts as the key and `label` is an auxiliary input.
- When `hash` is the identity (ignoring label), ODH reduces to DDH.
- When `hash` is a PRF keyed by the DH secret, ODH follows from DDH + PRF. -/
structure ODHDef (W : Type) [SampleableType W] extends DDHDef W where
  /-- Hash function: `hash(dh_secret, label)` → output.
  Models the hash oracle `H` in the ODH game. The DH shared secret
  serves as the key; `label` is the auxiliary input. -/
  hash : W → W → W

/-! ## ODH Games -/

/-- Type of ODH adversary: receives `(pub_a, pub_b, challenge)` and must
distinguish whether `challenge` is `hash(ecdh(a, pub_b), label)` or random.

The adversary outputs `(label, bit)` where `label` is the adversary's chosen
label for the hash query and `bit` is the distinguishing guess.

In the simplified formulation, the adversary chooses a label first, then
receives the challenge computed at that label. We model this by having the
adversary output a pair. -/
abbrev ODH_Adversary (W : Type) := W → W → W → SPComp (W × Bool)

/-- ODH real game: adversary receives `(pub_a, pub_b, hash(ecdh(a, pub_b), label))`.

The adversary first sees `(pub_a, pub_b)`, outputs `(label, _)`, and the
challenge is computed as `hash(shared_secret, label)`. In this simplified
formulation, the adversary receives the challenge directly.

**Simplified model**: The adversary receives `(pub_a, pub_b, challenge)` and
outputs `(label, bit)`. The game computes the challenge using the adversary's
label. To avoid circularity, we use a two-phase adversary: phase 1 chooses
the label, phase 2 distinguishes. Here we collapse this into a single
interaction where the challenge uses a fixed label sampled uniformly. -/
noncomputable def ODH_Game_Real (D : ODHDef W) (A : ODH_Adversary W) : SPComp Bool := do
  let ⟨a, pub_a⟩ ← D.keygen
  let ⟨_b, pub_b⟩ ← D.keygen
  let shared := D.ecdh a pub_b  -- = g^{ab}
  let label ← SPComp.sample W
  let challenge := D.hash shared label
  let ⟨_, bit⟩ ← A pub_a pub_b challenge
  pure bit

/-- ODH ideal game: adversary receives `(pub_a, pub_b, r)` where `r` is random. -/
noncomputable def ODH_Game_Ideal (D : ODHDef W) (A : ODH_Adversary W) : SPComp Bool := do
  let ⟨_, pub_a⟩ ← D.keygen
  let ⟨_b, pub_b⟩ ← D.keygen
  let r ← SPComp.sample W  -- random, independent of a, b
  let ⟨_, bit⟩ ← A pub_a pub_b r
  pure bit

/-- ODH advantage: ability to distinguish `hash(ecdh(a, pub_b), label)` from random,
given `(pub_a, pub_b)`. -/
noncomputable def ODH_Advantage (D : ODHDef W) (A : ODH_Adversary W) : ℝ≥0∞ :=
  Advantage (ODH_Game_Real D A) (ODH_Game_Ideal D A)

/-! ## Security Predicate -/

/-- ODH security: all adversaries have bounded distinguishing advantage.

`ODHSecure D ε` means that for all adversaries `A`, the advantage of `A`
in the ODH game is at most `ε`. -/
def ODHSecure (D : ODHDef W) (ε : ℝ≥0∞) : Prop :=
  ∀ (A : ODH_Adversary W), ODH_Advantage D A ≤ ε

/-! ## IsPure Proofs -/

theorem ODH_Game_Real_isPure (D : ODHDef W) (A : ODH_Adversary W)
    (hA : ∀ x y z, SPComp.IsPure (A x y z)) :
    SPComp.IsPure (ODH_Game_Real D A) := by
  unfold ODH_Game_Real
  apply SPComp.bind_isPure D.keygen_isPure; intro ⟨a, pub_a⟩
  apply SPComp.bind_isPure D.keygen_isPure; intro ⟨_b, pub_b⟩
  apply SPComp.bind_isPure (SPComp.sample_isPure _); intro label
  apply SPComp.bind_isPure (hA pub_a pub_b (D.hash (D.ecdh a pub_b) label))
  intro ⟨_, bit⟩
  exact SPComp.pure_isPure _

theorem ODH_Game_Ideal_isPure (D : ODHDef W) (A : ODH_Adversary W)
    (hA : ∀ x y z, SPComp.IsPure (A x y z)) :
    SPComp.IsPure (ODH_Game_Ideal D A) := by
  unfold ODH_Game_Ideal
  apply SPComp.bind_isPure D.keygen_isPure; intro ⟨_, pub_a⟩
  apply SPComp.bind_isPure D.keygen_isPure; intro ⟨_b, pub_b⟩
  apply SPComp.bind_isPure (SPComp.sample_isPure _); intro r
  apply SPComp.bind_isPure (hA pub_a pub_b r); intro ⟨_, bit⟩
  exact SPComp.pure_isPure _

/-! ## Relationship to DDH

When `hash` is the identity function (ignoring the label), ODH degenerates
to DDH. This provides a sanity check on the formulation. -/

/-- Any DDH group induces an ODH group with identity hash (ignoring label). -/
def ODHDef.ofDDH_id (D : DDHDef W) : ODHDef W :=
  { D with hash := fun secret _label => secret }

/-! ## Reduction: DDH + PRF ⟹ ODH

The standard reduction (ABR01, Theorem 2): if the hash function `H` is a PRF
keyed by the DH shared secret, then the ODH advantage is bounded by the sum
of the DDH advantage and the PRF advantage.

**Proof sketch**:
1. Replace `ecdh(a, pub_b)` with random `c` (DDH step, cost `ε_ddh`)
2. Now `hash(c, label)` with random key `c` is a PRF evaluation
3. Replace `hash(c, label)` with random `r` (PRF step, cost `ε_prf`)
4. The resulting game is `ODH_Game_Ideal`

By the triangle inequality:
    `ODH_Advantage ≤ DDH_Advantage + PRF_Advantage`
-/

/-- The hybrid game: replace the DH shared secret with random, but still apply hash.
This is the intermediate game in the DDH + PRF ⟹ ODH reduction. -/
noncomputable def ODH_Hybrid (D : ODHDef W) (A : ODH_Adversary W) : SPComp Bool := do
  let ⟨_, pub_a⟩ ← D.keygen
  let ⟨_b, pub_b⟩ ← D.keygen
  let c ← SPComp.sample W  -- random key (replaces ecdh(a, pub_b))
  let label ← SPComp.sample W
  let challenge := D.hash c label  -- PRF with random key
  let ⟨_, bit⟩ ← A pub_a pub_b challenge
  pure bit

/-- DDH + PRF ⟹ ODH: if hash is a PRF keyed by the DH secret, then
the ODH advantage is bounded by the DDH advantage plus the PRF advantage.

- `ε_ddh` bounds the DDH advantage (cost of replacing `ecdh(a, pub_b)` with random)
- `ε_prf` bounds the PRF advantage of `hash` (cost of replacing `hash(c, ·)` with random)

The bound is: `ODH_Advantage D A ≤ ε_ddh + ε_prf` -/
theorem odh_of_ddh_prf (D : ODHDef W) (A : ODH_Adversary W)
    (ε_ddh ε_prf : ℝ≥0∞)
    (h_ddh : ∀ (B : DDH_Adversary W), DDH_Advantage D.toDDHDef B ≤ ε_ddh)
    (h_prf : Advantage (ODH_Hybrid D A) (ODH_Game_Ideal D A) ≤ ε_prf) :
    ODH_Advantage D A ≤ ε_ddh + ε_prf := by
  -- Two-hop hybrid argument via triangle inequality:
  -- ODH_Advantage = Advantage(Real, Ideal)
  --   ≤ Advantage(Real, Hybrid) + Advantage(Hybrid, Ideal)
  --   ≤ ε_ddh + ε_prf
  unfold ODH_Advantage
  calc Advantage (ODH_Game_Real D A) (ODH_Game_Ideal D A)
      ≤ Advantage (ODH_Game_Real D A) (ODH_Hybrid D A) +
        Advantage (ODH_Hybrid D A) (ODH_Game_Ideal D A) :=
        advantage_triangle _ _ _
    _ ≤ ε_ddh + ε_prf := by
        apply add_le_add _ h_prf
        -- Hop 1: Real → Hybrid costs DDH.
        -- Construct DDH adversary B from ODH adversary A:
        -- B(pub_a, pub_b, z) samples label, computes hash(z, label),
        -- runs A(pub_a, pub_b, hash(z, label)), extracts the bit.
        let B : DDH_Adversary W := fun pub_a pub_b z => do
          let label ← SPComp.sample W
          let challenge := D.hash z label
          let ⟨_, bit⟩ ← A pub_a pub_b challenge
          pure bit
        -- DDH_Game_Real B = ODH_Game_Real A
        -- DDH_Game_Ideal B = ODH_Hybrid A
        -- So Advantage(Real, Hybrid) = DDH_Advantage B ≤ ε_ddh
        have hreal : DDH_Game_Real D.toDDHDef B = ODH_Game_Real D A := by
          unfold DDH_Game_Real ODH_Game_Real B; rfl
        have hideal : DDH_Game_Ideal D.toDDHDef B = ODH_Hybrid D A := by
          unfold DDH_Game_Ideal ODH_Hybrid B; rfl
        calc Advantage (ODH_Game_Real D A) (ODH_Hybrid D A)
            = Advantage (DDH_Game_Real D.toDDHDef B) (DDH_Game_Ideal D.toDDHDef B) := by
              rw [hreal, hideal]
          _ = DDH_Advantage D.toDDHDef B := rfl
          _ ≤ ε_ddh := h_ddh B

end CatCrypt.Crypto.Assumptions
