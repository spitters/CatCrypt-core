/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Advantage
public import CatCryptCore.Crypto.Assumptions.DDH
public import CatCryptCore.Crypto.Assumptions.PRP
public import CatCryptCore.Tactics

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

## Reduction: DDH + PRF ⟹ ODH

The standard reduction (ABR01 Thm 2), with `hash` viewed as the PRF
`ODHDef.toPRFDef D` keyed by the DH secret. For every ODH adversary `A`
(`odh_le_ddh_add_prf`):

    ODH_Advantage D A ≤ DDH_Advantage D.toDDHDef (ddhAdvOfODH D A)
      + ∑ label, |W|⁻¹ · PRF_Advantage D.toPRFDef label (prfAdvOfODH D A)

The second term is the PRF advantage averaged over the uniformly sampled label.

* `ddhAdvOfODH` — DDH adversary: samples a label and runs `A` on `hash(z, label)`
* `prfAdvOfODH` — PRF adversary: samples both public keys and runs `A`
* `odh_le_ddh_add_prf` — the reduction theorem

The predicate `ODHSecure D ε := ∀ A, ODH_Advantage D A ≤ ε` (no users) and the theorem
`odh_of_ddh_prf`, which assumed `∀ B, DDH_Advantage D.toDDHDef B ≤ ε_ddh` and the PRF hop
itself as hypotheses, are removed; `odh_le_ddh_add_prf` replaces the latter.

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

@[expose] public section

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

/-! ## IsPure Proofs -/

theorem ODH_Game_Real_isPure (D : ODHDef W) (A : ODH_Adversary W)
    (hA : ∀ x y z, SPComp.IsPure (A x y z)) :
    SPComp.IsPure (ODH_Game_Real D A) := by
  unfold ODH_Game_Real
  apply SPComp.bind_isPure D.keygen_isPure; intro ⟨a, pub_a⟩
  apply SPComp.bind_isPure D.keygen_isPure; intro ⟨_b, pub_b⟩
  apply SPComp.bind_isPure (SPComp.sample_isPure _); intro label
  simp_all [SPComp.bind_isPure, SPComp.pure_isPure]

theorem ODH_Game_Ideal_isPure (D : ODHDef W) (A : ODH_Adversary W)
    (hA : ∀ x y z, SPComp.IsPure (A x y z)) :
    SPComp.IsPure (ODH_Game_Ideal D A) := by
  unfold ODH_Game_Ideal
  apply SPComp.bind_isPure D.keygen_isPure; intro ⟨_, pub_a⟩
  apply SPComp.bind_isPure D.keygen_isPure; intro ⟨_b, pub_b⟩
  apply SPComp.bind_isPure (SPComp.sample_isPure _); intro r
  simp_all [SPComp.bind_isPure, SPComp.pure_isPure]

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

**Proof**:
1. Replace `ecdh(a, pub_b)` with random `c` (`ODH_Hybrid`); the two games are the
   DDH games of `ddhAdvOfODH D A`.
2. In `ODH_Hybrid`, for each label, `hash(c, label)` with random key `c` is the real
   PRF game of `prfAdvOfODH D A`, and `ODH_Game_Ideal` is the ideal one.
3. The triangle inequality adds the two hops.
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

/-- The hash of an ODH group as a PRF keyed by its first argument. -/
def ODHDef.toPRFDef (D : ODHDef W) : PRFDef W where
  eval := D.hash

/-- DDH adversary from an ODH adversary: on `(pub_a, pub_b, z)`, sample a label and run
    `A` on `hash(z, label)`. -/
noncomputable def ddhAdvOfODH (D : ODHDef W) (A : ODH_Adversary W) : DDH_Adversary W :=
  fun pub_a pub_b z => do
    let label ← SPComp.sample W
    let challenge := D.hash z label
    let ⟨_, bit⟩ ← A pub_a pub_b challenge
    pure bit

/-- PRF adversary from an ODH adversary: on a challenge `z`, sample both key pairs and
    run `A` on `(pub_a, pub_b, z)`. -/
noncomputable def prfAdvOfODH (D : ODHDef W) (A : ODH_Adversary W) : W → SPComp Bool :=
  fun z => do
    let ⟨_, pub_a⟩ ← D.keygen
    let ⟨_b, pub_b⟩ ← D.keygen
    let ⟨_, bit⟩ ← A pub_a pub_b z
    pure bit

/-- Hop 1: the real ODH game and the hybrid are the real and ideal DDH games of
    `ddhAdvOfODH D A`. -/
theorem odh_real_hybrid_eq_ddh (D : ODHDef W) (A : ODH_Adversary W) :
    Advantage (ODH_Game_Real D A) (ODH_Hybrid D A) =
      DDH_Advantage D.toDDHDef (ddhAdvOfODH D A) := rfl

/-- `keygen` commutes with a later uniform sample. -/
private theorem keygen_sample_comm {β : Type} (D : ODHDef W) (k : W × W → W → SPComp β) :
    D.keygen.bind (fun p => (SPComp.sample W).bind fun c => k p c) =
      (SPComp.sample W).bind (fun c => D.keygen.bind fun p => k p c) :=
  SPComp.isPure_bind_comm _ _ _ D.keygen_isPure (SPComp.sample_isPure W)

/-- The hybrid game, with the label sampled first, is the average over the label of the
    real PRF game of `prfAdvOfODH D A`. -/
theorem odh_hybrid_eq_prf_real (D : ODHDef W) (A : ODH_Adversary W) :
    ODH_Hybrid D A = (SPComp.sample W).bind fun label =>
      (PRF_Real D.toPRFDef label).bind (prfAdvOfODH D A) := by
  show D.keygen.bind (fun p => D.keygen.bind fun q => (SPComp.sample W).bind fun c =>
      (SPComp.sample W).bind fun label => (A p.2 q.2 (D.hash c label)).bind fun o =>
        SPComp.pure o.2) = _
  simp only [keygen_sample_comm]
  rw [SPComp.isPure_bind_comm _ _ _ (SPComp.sample_isPure W) (SPComp.sample_isPure W)]
  unfold PRF_Real ODHDef.toPRFDef prfAdvOfODH
  simp only [SPComp.monad_bind_eq, SPComp.monad_pure_eq, SPComp.bind_assoc, SPComp.pure_bind]

/-- The ideal game, preceded by an unused label sample, is the average over the label of
    the ideal PRF game of `prfAdvOfODH D A`. -/
theorem prTrue_odh_ideal_eq_prf_ideal (D : ODHDef W) (A : ODH_Adversary W) :
    prTrue (ODH_Game_Ideal D A) Heap.empty =
      prTrue ((SPComp.sample W).bind fun label =>
        (PRP_Ideal label).bind (prfAdvOfODH D A)) Heap.empty := by
  have hgame : ODH_Game_Ideal D A = (SPComp.sample W).bind (prfAdvOfODH D A) := by
    show D.keygen.bind (fun p => D.keygen.bind fun q => (SPComp.sample W).bind fun r =>
        (A p.2 q.2 r).bind fun o => SPComp.pure o.2) = _
    simp only [keygen_sample_comm]
    rfl
  rw [prTrue_bind_sample, hgame]
  simp only [PRP_Ideal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc]
  rw [ENNReal.mul_inv_cancel (by simp) (ENNReal.natCast_ne_top _), one_mul]

/-- Averaging over a uniform prefix: the advantage between `sample α >>= f` and
    `sample α >>= g` is at most the average of the advantages between `f x` and `g x`. -/
theorem advantage_sample_bind_le_avg {α : Type} [Fintype α] [Nonempty α]
    (f g : α → SPComp Bool) :
    Advantage ((SPComp.sample α).bind f) ((SPComp.sample α).bind g) ≤
      ∑ x : α, (Fintype.card α : ℝ≥0∞)⁻¹ * Advantage (f x) (g x) := by
  show (prTrue ((SPComp.sample α).bind f) Heap.empty -
      prTrue ((SPComp.sample α).bind g) Heap.empty) ⊔
    (prTrue ((SPComp.sample α).bind g) Heap.empty -
      prTrue ((SPComp.sample α).bind f) Heap.empty) ≤ _
  rw [prTrue_bind_sample, prTrue_bind_sample]
  have hf : ∀ x, prTrue (f x) Heap.empty ≤ Advantage (f x) (g x) + prTrue (g x) Heap.empty :=
    fun x => le_tsub_add.trans (add_le_add_left (le_max_left _ _) _)
  have hg : ∀ x, prTrue (g x) Heap.empty ≤ Advantage (f x) (g x) + prTrue (f x) Heap.empty :=
    fun x => le_tsub_add.trans (add_le_add_left (le_max_right _ _) _)
  refine max_le ?_ ?_ <;>
  · rw [tsub_le_iff_right, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun x _ => by
      rw [← mul_add]; gcongr; first | exact hf x | exact hg x

/-- **DDH + PRF ⟹ ODH** (ABR01, Thm 2). For every ODH adversary `A`,

    `ODH_Advantage D A ≤ DDH_Advantage D.toDDHDef (ddhAdvOfODH D A)
      + ∑ label, |W|⁻¹ · PRF_Advantage D.toPRFDef label (prfAdvOfODH D A)`. -/
theorem odh_le_ddh_add_prf (D : ODHDef W) (A : ODH_Adversary W) :
    ODH_Advantage D A ≤ DDH_Advantage D.toDDHDef (ddhAdvOfODH D A) +
      ∑ label : W, (Fintype.card W : ℝ≥0∞)⁻¹ *
        PRF_Advantage D.toPRFDef label (prfAdvOfODH D A) := by
  unfold ODH_Advantage
  have hA : Advantage (ODH_Hybrid D A) (ODH_Game_Ideal D A) =
      Advantage ((SPComp.sample W).bind fun label =>
          (PRF_Real D.toPRFDef label).bind (prfAdvOfODH D A))
        ((SPComp.sample W).bind fun label =>
          (PRP_Ideal label).bind (prfAdvOfODH D A)) := by
    unfold Advantage
    rw [odh_hybrid_eq_prf_real, prTrue_odh_ideal_eq_prf_ideal]
  calc Advantage (ODH_Game_Real D A) (ODH_Game_Ideal D A)
      ≤ Advantage (ODH_Game_Real D A) (ODH_Hybrid D A) +
          Advantage (ODH_Hybrid D A) (ODH_Game_Ideal D A) := advantage_triangle _ _ _
    _ ≤ _ := add_le_add (odh_real_hybrid_eq_ddh D A).le
        (hA.trans_le (advantage_sample_bind_le_avg _ _))

end CatCrypt.Crypto.Assumptions
