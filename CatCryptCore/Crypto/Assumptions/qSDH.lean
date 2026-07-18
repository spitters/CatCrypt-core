/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.Advantage

/-!
# q-Strong Diffie-Hellman (q-SDH) Assumption

The q-SDH assumption is the core hardness assumption for BBS/BBS+ signatures
and anonymous credentials. It generalizes the strong DH assumption to a
setting where the adversary receives multiple powers of a secret exponent.

## q-SDH Game

Given a group of prime order p with generator g:
- The challenger samples a secret `x ← Zₚ`
- The adversary receives `(g, g^x, g^{x²}, ..., g^{x^q})`
- The adversary must output `(c, g^{1/(x+c)})` for some `c ∈ Zₚ \ {-x}`

## Main definitions

* `qSDH_Group` — abstract group supporting q-SDH
* `qSDH_Game` — the q-SDH game
* `qSDH_Advantage` — advantage of an adversary

## Cross-Validation

| Property | This file | Paper |
|----------|-----------|-------|
| Challenge | `qSDH_challenge x q` = `(g, g^x, ..., g^{x^q})` | BB04 Def. 3 |
| Verification | `h^{x+c} = g` | BB04 Def. 3 |
| Group | `qSDH_Group` (abstract cyclic group) | Type-III pairing G₁ |

**Relationship to t-SDH (`Assumptions/tSDH.lean`):**
- `tSDH` uses `PairingGroup` with bilinear pairing verification
- `qSDH` uses an abstract group with exponentiation-based verification
- Both capture the same hardness assumption in different algebraic settings

**Equivalent formalizations:**
- EasyCrypt: `SDH` theory (Tessaro-Zhu BBS formalization)

## References

* [Boneh, Boyen. *Short Signatures Without Random Oracles.* EUROCRYPT 2004, Def. 3]
* [Tessaro, Zhu. *Revisiting BBS Signatures.* EUROCRYPT 2023]
-/

namespace CatCrypt.Crypto.Assumptions

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

/-! ## q-SDH Group Definition -/

/-- Abstract group supporting the q-SDH assumption.

    This captures a cyclic group of prime order where exponentiation
    and the q-SDH challenge are well-defined.

    For BBS signatures, this is a Type-III pairing group, but we abstract
    over the pairing structure since q-SDH only needs the G₁ component. -/
structure qSDH_Group where
  /-- Group element type -/
  G : Type
  /-- Scalar/exponent type (≅ Zₚ) -/
  Scalar : Type
  /-- Generator -/
  gen : G
  /-- Scalar multiplication (exponentiation): `g^a` -/
  smul : Scalar → G → G
  /-- Scalar addition -/
  scalarAdd : Scalar → Scalar → Scalar
  /-- Scalar multiplication -/
  scalarMul : Scalar → Scalar → Scalar
  /-- Scalar inverse (for `1/(x+c)`) -/
  scalarInv : Scalar → Scalar
  /-- Zero scalar -/
  scalarZero : Scalar
  /-- One scalar (multiplicative identity, for `x^0 = 1`) -/
  scalarOne : Scalar
  /-- Decidable equality on G -/
  [decG : DecidableEq G]
  /-- Decidable equality on Scalar -/
  [decScalar : DecidableEq Scalar]
  /-- Group is finite -/
  [finG : Fintype G]
  /-- Group is nonempty -/
  [neG : Nonempty G]
  /-- Scalar is finite (for uniform sampling) -/
  [finScalar : Fintype Scalar]
  /-- Scalar is nonempty -/
  [neScalar : Nonempty Scalar]

attribute [instance] qSDH_Group.decG qSDH_Group.decScalar
  qSDH_Group.finG qSDH_Group.neG qSDH_Group.finScalar qSDH_Group.neScalar

variable (QG : qSDH_Group)

/-- Notation: `g^a` as scalar multiplication. -/
local notation:70 g " ^ˢ " a => qSDH_Group.smul a g

/-- Iterated scalar multiplication: compute `x^i` in the scalar field. -/
def scalarPow (x : QG.Scalar) : ℕ → QG.Scalar
  | 0 => QG.scalarOne
  | n + 1 => QG.scalarMul x (scalarPow x n)

/-- The q-SDH challenge: `(g, g^x, g^{x²}, ..., g^{x^q})`.

    Given secret `x`, compute the tuple of q+1 group elements. -/
def qSDH_challenge (x : QG.Scalar) (q : ℕ) : Fin (q + 1) → QG.G :=
  fun i => QG.smul (scalarPow QG x i.val) QG.gen

/-! ## q-SDH Game -/

/-- Type of q-SDH adversary: receives the challenge tuple,
    outputs `(c, h)` where `h` should equal `g^{1/(x+c)}`. -/
abbrev qSDH_Adversary (q : ℕ) :=
  (Fin (q + 1) → QG.G) → SPComp (QG.Scalar × QG.G)

/-- The q-SDH game.

    1. Sample secret `x ← Zₚ`
    2. Compute challenge `(g, g^x, ..., g^{x^q})`
    3. Adversary outputs `(c, h)`
    4. Verify: `h = g^{1/(x+c)}`, i.e., `h^{x+c} = g`

    We verify by checking `smul (scalarAdd x c) h = gen`. -/
noncomputable def qSDH_Game (q : ℕ) (A : qSDH_Adversary QG q) : SPComp Bool := do
  let x ← SPComp.sample QG.Scalar
  let challenge := qSDH_challenge QG x q
  let (c, h) ← A challenge
  -- Verify: h^(x+c) = g, i.e., h = g^{1/(x+c)}
  let lhs := QG.smul (QG.scalarAdd x c) h
  SPComp.pure (decide (lhs = QG.gen))

/-- Advantage of adversary A in breaking the q-SDH assumption. -/
noncomputable def qSDH_Advantage (q : ℕ) (A : qSDH_Adversary QG q) : ℝ≥0∞ :=
  prTrue (qSDH_Game QG q A) Heap.empty

/-! ## IsPure -/

theorem qSDH_Game_isPure (q : ℕ) (A : qSDH_Adversary QG q)
    (hA : ∀ ch, SPComp.IsPure (A ch)) :
    SPComp.IsPure (qSDH_Game QG q A) := by
  unfold qSDH_Game
  apply SPComp.bind_isPure (SPComp.sample_isPure _); intro x
  apply SPComp.bind_isPure (hA _); intro ⟨c, h⟩
  exact SPComp.pure_isPure _

end CatCrypt.Crypto.Assumptions
