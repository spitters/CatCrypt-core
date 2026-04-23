/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.PairingGroup
import CatCrypt.Crypto.Advantage

/-!
# Computational co-Diffie-Hellman (co-CDH) Assumption

The co-CDH assumption in bilinear groups: given `(g₁, g₂, g₁^a, g₂^b)`,
compute `g₁^{ab}`.

This is the standard hardness assumption underlying BLS signatures
(Boneh-Lynn-Shacham 2004). It is equivalent to CDH in G₂ when
the pairing exists, but stated in the Type III setting.

## Main definitions

* `CoCDH_Adversary` — adversary that attempts to compute g₁^{ab}
* `CoCDH_Game` — the co-CDH game
* `CoCDH_Advantage` — probability of solving co-CDH
* `CoCDHSecure` — co-CDH hardness assumption

## Cross-Validation

| Property | This file | Paper |
|----------|-----------|-------|
| Challenge | `(g₁^a, g₂^b)` | BLS04 §3 |
| Target | Compute `g₁^{ab}` | BLS04 §3 |
| Group | `PairingGroup P` (Type-III) | Bilinear group `(G₁, G₂, G_T)` |

**Relationship to other assumptions:**
- CDH in G₁ ⟹ co-CDH (co-CDH is weaker: adversary gets cross-group info)
- co-CDH is the standard BLS assumption; CDH in G₁ is sometimes used instead

## References

* Boneh, Lynn, Shacham. *Short Signatures from the Weil Pairing.*
  J. Cryptology, 2004, §3.
-/

namespace CatCrypt.Crypto.Assumptions

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.PairingGroup
open scoped ENNReal

variable (P : PairingGroup)

/-! ## co-CDH Game -/

/-- co-CDH adversary: given (g₁^a, g₂^b), attempts to compute g₁^{ab}.

    The adversary receives elements from both source groups and must
    produce an element of G₁. -/
abbrev CoCDH_Adversary := P.G₁ → P.G₂ → SPComp P.G₁

/-- co-CDH game: sample a, b ← Zₚ; adversary receives (g₁^a, g₂^b)
    and wins if it outputs g₁^{ab}.

    Returns `true` if the adversary's output equals g₁^{ab}. -/
noncomputable def CoCDH_Game (A : CoCDH_Adversary P) : SPComp Bool := do
  let a ← SPComp.sample (ZMod P.p)
  let b ← SPComp.sample (ZMod P.p)
  let challenge₁ := zpowZMod₁ (P := P) P.g₁ a  -- g₁^a
  let challenge₂ := zpowZMod₂ (P := P) P.g₂ b  -- g₂^b
  let answer ← A challenge₁ challenge₂
  let target := zpowZMod₁ (P := P) P.g₁ (a * b)  -- g₁^{ab}
  SPComp.pure (decide (answer = target))

/-- co-CDH advantage: probability that the adversary computes g₁^{ab}. -/
noncomputable def CoCDH_Advantage (A : CoCDH_Adversary P) : ℝ≥0∞ :=
  prTrue (CoCDH_Game P A) Heap.empty

/-- co-CDH hardness: all adversaries have bounded advantage. -/
def CoCDHSecure (ε : ℝ≥0∞) : Prop :=
  ∀ (A : CoCDH_Adversary P), CoCDH_Advantage P A ≤ ε

end CatCrypt.Crypto.Assumptions
