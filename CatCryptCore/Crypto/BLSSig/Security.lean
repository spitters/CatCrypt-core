/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.Assumptions.CoCDH

/-!
# BLS EUF-CMA Security via the co-CDH Reduction (ROM)

Existential unforgeability of BLS signatures, reduced to the computational
co-Diffie-Hellman assumption in the bilinear group, with the hash-to-curve
function `H` modelled as a random oracle to `G₁`.

## The reduction

The forgery-extraction lemma `forgery_is_cocdh_solution`: a signature that passes
the pairing check on a message whose random-oracle hash is the co-CDH challenge
`g₁ ^ᵍ a`, under a public key `pk = g₂ ^ʰ b`, is exactly the co-CDH answer
`g₁ ^ᵍ (a·b)` — the element `CoCDH_Game` (`Assumptions/CoCDH.lean`) asks an
adversary to produce. It is proved from the pairing: bilinearity (`e_zpowZMod_id`)
plus non-degeneracy/injectivity of `e(·, g₂)` (`e_inj_left`, derived from
`PairingGroup.e_first_arg_eq_one`). No pairing axiom is added.

The reduction `blsReduction` turns a BLS forger into a co-CDH solver. It receives
the matched-exponent co-CDH instance `(g₁ ^ᵍ x, g₂ ^ʰ x, u)`, runs the forger on
`pk = g₂ ^ʰ x` and challenge hash `u`, and answers the forger's chosen-message
signing queries with `(g₁ ^ᵍ x) ^ᵍ r = (g₁ ^ᵍ r) ^ᵍ x` (`zpowZMod₁_zpowZMod₁` +
`mul_comm`), i.e. the BLS signature on the message whose oracle hash is `g₁ ^ᵍ r`.
The simulated signing oracle is identical to the real one, so the co-CDH game with
`blsReduction F` equals the BLS forgery game (`blsForgeGame_eq_cocdh`), giving the
bound `blsForgeAdvantage F ≤ ε` whenever co-CDH is `ε`-hard
(`bls_forge_reduces_to_cocdh`).

This is a Type-III BLS reduction: the secret exponent `x` is available in both
source groups (`g₁ ^ᵍ x`, `g₂ ^ʰ x`), which is what lets the reduction sign. This
matched-exponent form is the hardness assumption for the minimal-signature BLS
scheme (`BLSCoCDHSecure`).

## Modelling boundaries

* `H` is a random oracle to `G₁` (the BLS ROM assumption): the challenge hash `u`
  is uniform in `G₁` and the signing oracle is keyed on the hash discrete log `r`.
* The reduction is for a single random-oracle challenge message (selective ROM);
  the multi-query adaptive variant adds the usual `q_H` guessing factor.
* `BLSCoCDHSecure` is the matched-exponent (Type-III) co-CDH assumption.

## References

* Boneh, Lynn, Shacham. *Short Signatures from the Weil Pairing.*
  J. Cryptology, 2004, §3 (security from co-CDH in the ROM).
-/

namespace CatCryptCore.Crypto.BLSSig

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.PairingGroup
open scoped ENNReal

variable (P : PairingGroup)

/-! ## Pairing injectivity and the BLS identity -/

/-- Injectivity of `e(·, g₂)`: pairing with the second generator is injective
    on `G₁`. Follows from non-degeneracy (`e_first_arg_eq_one`). -/
theorem e_inj_left {a b : P.G₁} (h : P.e a P.g₂ = P.e b P.g₂) : a = b := by
  have h1 : P.e (a * b⁻¹) P.g₂ = 1 := by
    rw [P.e_mul_left, e_inv_left, h]; exact mul_inv_cancel _
  exact mul_inv_eq_one.mp (e_first_arg_eq_one (a * b⁻¹) h1)

/-- The BLS identity over `P`: `e(u ^ᵍ x, g₂) = e(u, g₂ ^ʰ x)`. -/
theorem e_zpowZMod_id (u : P.G₁) (x : ZMod P.p) :
    P.e (zpowZMod₁ (P := P) u x) P.g₂ = P.e u (zpowZMod₂ (P := P) P.g₂ x) := by
  unfold zpowZMod₁ zpowZMod₂
  rw [e_zpow_left_general, e_zpow_right]

/-! ## Forgery extraction (the heart of unforgeability) -/

/-- A signature passing the BLS pairing check `e(σ, g₂) = e(u, g₂ ^ʰ x)` is
    forced to be `u ^ᵍ x`. -/
theorem forgery_extracts {u σ : P.G₁} {x : ZMod P.p}
    (h : P.e σ P.g₂ = P.e u (zpowZMod₂ (P := P) P.g₂ x)) :
    σ = zpowZMod₁ (P := P) u x := by
  apply e_inj_left
  rw [e_zpowZMod_id]; exact h

/-- The pairing check is equivalent to being the co-CDH-style answer. -/
theorem verify_iff_isAnswer (u σ : P.G₁) (x : ZMod P.p) :
    (P.e σ P.g₂ = P.e u (zpowZMod₂ (P := P) P.g₂ x)) ↔
      (σ = zpowZMod₁ (P := P) u x) := by
  constructor
  · exact forgery_extracts P
  · intro h; subst h; exact e_zpowZMod_id P u x

/-- **Forgery is a co-CDH solution.** A BLS signature `σ` verifying on a message
    whose hash is the co-CDH challenge `g₁ ^ᵍ a`, under `pk = g₂ ^ʰ b`, equals
    `g₁ ^ᵍ (a·b)` — the target of `Assumptions.CoCDH_Game`. -/
theorem forgery_is_cocdh_solution {a b : ZMod P.p} {σ : P.G₁}
    (h : P.e σ P.g₂ =
      P.e (zpowZMod₁ (P := P) P.g₁ a) (zpowZMod₂ (P := P) P.g₂ b)) :
    σ = zpowZMod₁ (P := P) P.g₁ (a * b) := by
  have hx := forgery_extracts P (u := zpowZMod₁ (P := P) P.g₁ a) (x := b) h
  rwa [zpowZMod₁_zpowZMod₁] at hx

/-! ## Matched-exponent co-CDH (the Type-III BLS assumption) -/

/-- co-CDH solver for the matched-exponent (Type-III) instance: given
    `(g₁ ^ᵍ x, g₂ ^ʰ x, u)`, output `u ^ᵍ x`. The pairing makes the answer
    verifiable (`e(u^x, g₂) = e(u, g₂^x)`) but not computable. -/
abbrev BLSCoCDHAdversary (P : PairingGroup) :=
  P.G₁ → P.G₂ → P.G₁ → SPComp P.G₁

/-- Matched-exponent co-CDH game: sample `x ← Zₚ` and `u ← G₁`, hand the
    adversary `(g₁ ^ᵍ x, g₂ ^ʰ x, u)`, win iff it returns `u ^ᵍ x`. -/
noncomputable def BLSCoCDH_Game (A : BLSCoCDHAdversary P) : SPComp Bool := do
  let x ← SPComp.sample (ZMod P.p)
  let u ← SPComp.sample P.G₁
  let answer ← A (zpowZMod₁ (P := P) P.g₁ x) (zpowZMod₂ (P := P) P.g₂ x) u
  SPComp.pure (decide (answer = zpowZMod₁ (P := P) u x))

/-- Matched-exponent co-CDH advantage. -/
noncomputable def BLSCoCDH_Advantage (A : BLSCoCDHAdversary P) : ℝ≥0∞ :=
  prTrue (BLSCoCDH_Game P A) Heap.empty

/-- Matched-exponent co-CDH hardness assumption. -/
def BLSCoCDHSecure (ε : ℝ≥0∞) : Prop :=
  ∀ (A : BLSCoCDHAdversary P), BLSCoCDH_Advantage P A ≤ ε

/-! ## The BLS forgery game and the reduction -/

/-- A BLS forger in the random-oracle model.

    Given the public key `pk`, the random-oracle hash `u = H(m*)` of the
    challenge message, and a chosen-message signing oracle keyed on the hash
    discrete log `r` (returning the BLS signature on the message whose oracle
    hash is `g₁ ^ᵍ r`), the forger outputs a candidate forgery `σ ∈ G₁` on the
    challenge message. -/
structure BLSForger (P : PairingGroup) where
  /-- `run pk u signOracle` produces a candidate forgery on the challenge
      message hashing to `u`. -/
  run : P.G₂ → P.G₁ → (ZMod P.p → SPComp P.G₁) → SPComp P.G₁

/-- BLS forgery game (ROM, single challenge message). Sample the key `x` and the
    challenge hash `u`; the forger gets `pk = g₂ ^ʰ x`, the hash `u`, and the
    real signing oracle `r ↦ (g₁ ^ᵍ r) ^ᵍ x`; it wins iff its output passes the
    BLS pairing check `e(σ, g₂) = e(u, pk)`. -/
noncomputable def blsForgeGame (F : BLSForger P) : SPComp Bool := do
  let x ← SPComp.sample (ZMod P.p)
  let u ← SPComp.sample P.G₁
  let σ ← F.run (zpowZMod₂ (P := P) P.g₂ x) u
            (fun r => SPComp.pure (zpowZMod₁ (P := P) (zpowZMod₁ (P := P) P.g₁ r) x))
  SPComp.pure (decide (P.e σ P.g₂ = P.e u (zpowZMod₂ (P := P) P.g₂ x)))

/-- BLS forgery advantage. -/
noncomputable def blsForgeAdvantage (F : BLSForger P) : ℝ≥0∞ :=
  prTrue (blsForgeGame P F) Heap.empty

/-- BLS existential unforgeability in the ROM: all forgers bounded by `ε`. -/
def BLSForgeSecure (ε : ℝ≥0∞) : Prop :=
  ∀ (F : BLSForger P), blsForgeAdvantage P F ≤ ε

/-- **The reduction**: a BLS forger becomes a matched-exponent co-CDH solver.

    On instance `(gx = g₁ ^ᵍ x, hx = g₂ ^ʰ x, u)` it sets `pk = hx`, hands the
    forger the challenge hash `u`, and answers signing queries with
    `gx ^ᵍ r = (g₁ ^ᵍ x) ^ᵍ r`, returning the forger's output as the candidate
    `u ^ᵍ x`. -/
noncomputable def blsReduction (F : BLSForger P) : BLSCoCDHAdversary P :=
  fun gx hx u => F.run hx u (fun r => SPComp.pure (zpowZMod₁ (P := P) gx r))

/-- The reduction simulates the BLS forgery game exactly: the co-CDH game on
    `blsReduction F` is, as a probabilistic program, the BLS forgery game.

    The signing oracle matches because `(g₁ ^ᵍ x) ^ᵍ r = (g₁ ^ᵍ r) ^ᵍ x`
    (`zpowZMod₁_zpowZMod₁`, `mul_comm`); the win condition matches because the
    pairing check is equivalent to `σ = u ^ᵍ x` (`verify_iff_isAnswer`). -/
theorem blsForgeGame_eq_cocdh (F : BLSForger P) :
    blsForgeGame P F = BLSCoCDH_Game P (blsReduction P F) := by
  unfold blsForgeGame BLSCoCDH_Game blsReduction
  congr 1
  funext x
  congr 1
  funext u
  have hsign :
      (fun r => SPComp.pure (zpowZMod₁ (P := P) (zpowZMod₁ (P := P) P.g₁ r) x)) =
      (fun r => SPComp.pure (zpowZMod₁ (P := P) (zpowZMod₁ (P := P) P.g₁ x) r)) := by
    funext r
    rw [zpowZMod₁_zpowZMod₁, zpowZMod₁_zpowZMod₁, mul_comm]
  rw [hsign]
  congr 1
  funext σ
  congr 1
  exact decide_eq_decide.mpr (verify_iff_isAnswer P u σ x)

/-- Advantage transfer: the BLS forgery advantage equals the co-CDH advantage of
    the reduction. -/
theorem blsForgeAdvantage_eq_cocdh (F : BLSForger P) :
    blsForgeAdvantage P F = BLSCoCDH_Advantage P (blsReduction P F) := by
  unfold blsForgeAdvantage BLSCoCDH_Advantage
  rw [blsForgeGame_eq_cocdh]

/-- **BLS EUF reduces to co-CDH**: if matched-exponent co-CDH is `ε`-hard, every
    BLS forger has advantage at most `ε`. The conclusion bounds forgery using the
    co-CDH hypothesis. -/
theorem bls_forge_reduces_to_cocdh (ε : ℝ≥0∞) (h : BLSCoCDHSecure P ε)
    (F : BLSForger P) : blsForgeAdvantage P F ≤ ε := by
  rw [blsForgeAdvantage_eq_cocdh]; exact h _

/-- **BLS is EUF-secure in the ROM under co-CDH.** If matched-exponent (Type-III)
    co-CDH on `P` is `ε`-hard, every BLS forger has advantage at most `ε`. -/
theorem bls_forge_secure_of_cocdh (ε : ℝ≥0∞) (h : BLSCoCDHSecure P ε) :
    BLSForgeSecure P ε :=
  fun F => bls_forge_reduces_to_cocdh P ε h F

end CatCryptCore.Crypto.BLSSig
