/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.PairingGroup
import CatCryptCore.Crypto.Advantage

/-!
# t-Strong Diffie-Hellman Assumption

This file defines the t-SDH (t-Strong Diffie-Hellman) assumption, which is the
core hardness assumption for KZG polynomial commitments.

## Main definitions

* `tSDH_Game` — The t-SDH game: adversary receives SRS `[g₁, g₁^α, ..., g₁^(αᵗ)]`
  and must output `(c, g₁^(1/(α+c)))` for some `c ∈ Zₚ`
* `tSDH_Advantage` — Advantage of an adversary in breaking t-SDH

## Cross-Validation

| Property | This file | Paper |
|----------|-----------|-------|
| Challenge | `srs₁ α t` = `[g₁^{α⁰}, ..., g₁^{αᵗ}]` | KZG §3.1 |
| Verification | `e(h, g₂^{α+c}) = e(g₁, g₂)` | Boneh-Boyen Def. 3 |
| Advantage | `prTrue(tSDH_Game)` | `Pr[t-SDH]` |

**Equivalent formalizations:**
- EasyCrypt: `SDH` theory in KZG formalization (Palak-Haines)

## References

* [Boneh, Boyen, *Short Signatures Without Random Oracles*, EUROCRYPT 2004, Def. 3]
* [Kate, Zaverucha, Goldberg, *Constant-Size Commitments to Polynomials*, ASIACRYPT 2010, §3.1]
-/

namespace CatCrypt.Crypto.Assumptions

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open PairingGroup
open scoped ENNReal

variable (P : PairingGroup)

/-! ## t-SDH Game -/

/-- Type of t-SDH adversary: receives SRS of size t+1, outputs (c, h) where
    h should equal g₁^(1/(α+c)). -/
abbrev tSDH_Adversary (t : ℕ) :=
  (Fin (t + 1) → P.G₁) → SPComp (ZMod P.p × P.G₁)

/-- The t-SDH game: sample secret α, compute SRS, run adversary, check solution.

    The adversary wins if it outputs `(c, h)` such that `h = g₁^(1/(α+c))`,
    which we verify using the pairing: `e(h, g₂^α · g₂^c) = e(g₁, g₂)`. -/
noncomputable def tSDH_Game (t : ℕ) (A : tSDH_Adversary P t) : SPComp Bool := do
  let α ← SPComp.sample (ZMod P.p)
  let pk := srs₁ (P := P) α t
  let (c, h) ← A pk
  -- Verify: e(h, g₂^(α+c)) = e(g₁, g₂)
  -- This checks h = g₁^(1/(α+c)) using the bilinear pairing
  let lhs := P.e h (P.g₂ ^ʰ (α + c))
  let rhs := P.e P.g₁ P.g₂
  SPComp.pure (decide (lhs = rhs))

/-- Advantage of adversary A in breaking the t-SDH assumption -/
noncomputable def tSDH_Advantage (t : ℕ) (A : tSDH_Adversary P t) : ℝ≥0∞ :=
  prTrue (tSDH_Game P t A) Heap.empty

/-! ## Extended t-SDH Game (with verification key)

The standard formulation (Kate et al., Boneh-Boyen) provides the adversary with
both the G₁ SRS and the G₂ verification key `vk = (g₂, g₂^α)`. -/

/-- Extended t-SDH adversary: receives both SRS in G₁ and verification key in G₂. -/
abbrev tSDH_Adversary_ext (t : ℕ) :=
  (Fin (t + 1) → P.G₁) → (P.G₂ × P.G₂) → SPComp (ZMod P.p × P.G₁)

/-- Extended t-SDH game: adversary receives pk and vk = (g₂, g₂^α). -/
noncomputable def tSDH_Game_ext (t : ℕ) (A : tSDH_Adversary_ext P t) : SPComp Bool := do
  let α ← SPComp.sample (ZMod P.p)
  let pk := srs₁ (P := P) α t
  let vk := srs₂ (P := P) α
  let (c, h) ← A pk vk
  let lhs := P.e h (P.g₂ ^ʰ (α + c))
  let rhs := P.e P.g₁ P.g₂
  SPComp.pure (decide (lhs = rhs))

/-- Advantage in the extended t-SDH game. -/
noncomputable def tSDH_Advantage_ext (t : ℕ) (A : tSDH_Adversary_ext P t) : ℝ≥0∞ :=
  prTrue (tSDH_Game_ext P t A) Heap.empty

/-- Any basic t-SDH adversary can be lifted to an extended one (ignoring vk).
    The advantage is preserved. -/
theorem tSDH_Advantage_eq_ext (t : ℕ) (A : tSDH_Adversary P t) :
    tSDH_Advantage P t A = tSDH_Advantage_ext P t (fun pk _vk => A pk) := by
  simp only [tSDH_Advantage, tSDH_Advantage_ext, tSDH_Game, tSDH_Game_ext]

/-! ## Useful lemma: SRS evaluation equals polynomial commitment -/

/-- The SRS at position i is g₁^(αⁱ) -/
theorem srs₁_eq (α : ZMod P.p) (t : ℕ) (i : Fin (t + 1)) :
    srs₁ (P := P) α t i = P.g₁ ^ᵍ (α ^ i.val) := rfl

end CatCrypt.Crypto.Assumptions
