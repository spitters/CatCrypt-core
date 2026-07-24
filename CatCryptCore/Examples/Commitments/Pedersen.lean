/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Examples.Commitments.CommitmentScheme
import CatCryptCore.Crypto.Assumptions.DL
import CatCryptCore.Crypto.PairingGroup
import CatCryptCore.Crypto.UCDSL
import CatCryptCore.Crypto.ForkingLemma
import Mathlib.Algebra.Field.ZMod

/-!
# Pedersen Commitment Scheme

This file defines the Pedersen commitment scheme over a pairing group and proves:

1. **Perfect hiding**: The hiding advantage is exactly 0 for any adversary.
   The proof uses a bijection argument: for any two messages `m₀, m₁`, the map
   `r ↦ r + β⁻¹ · (m₁ - m₀)` is a bijection on `ZMod p` (when `β ≠ 0`),
   making the commitment distributions identical.

2. **Computational binding from DLog**: Any adversary that breaks binding
   can be used to solve the discrete logarithm problem. Specifically,
   `Binding_Advantage ≤ DL_Advantage` via an explicit reduction.

3. **UC wrapping**: Perfect hiding lifts to UC emulation at ε = 0.

## Construction

Given a pairing group with generators `g₁` and a second generator `h = g₁^β`
(where `β` is the secret trapdoor, unknown to the committer):

* `commit(m, r) = g₁^m · h^r = g₁^(m + β·r)`
* `verify(C, m, r) = (C == g₁^m · h^r)`

## References

* [Pedersen, Non-Interactive and Information-Theoretic Secure Verifiable
  Secret Sharing, CRYPTO 1991]
* [CatCrypt KZGPed hiding — bijection argument pattern]
-/

namespace CatCrypt.Examples.Commitments.Pedersen

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open CatCrypt.Crypto.PairingGroup CatCrypt.Crypto.ForkingLemma
open CatCrypt.Examples.Commitments
open CatCrypt.Crypto.UCDSL
open scoped ENNReal

/-! ## Pedersen Parameters -/

/-- Parameters for the Pedersen commitment scheme.

The scheme operates in the source group `G₁` of a pairing group `P`.
The second generator `h = g₁^β` is determined by the secret exponent `β`.
Both messages and randomness live in `ZMod P.p`.

The key security property is that `β` is unknown to the committer:
- **Hiding** holds unconditionally (information-theoretically) when `β ≠ 0`
- **Binding** holds computationally, assuming DLog is hard -/
structure PedersenParams where
  /-- The underlying pairing group -/
  P : PairingGroup
  /-- The secret exponent determining h = g₁^β -/
  β : ZMod P.p
  /-- β is nonzero (otherwise h = 1 and hiding fails) -/
  hβ : β ≠ 0

namespace PedersenParams

variable (pp : PedersenParams)

/-- The second generator h = g₁^β -/
noncomputable def h : pp.P.G₁ := pp.P.g₁ ^ᵍ pp.β

private instance : Fact (Nat.Prime pp.P.p) := pp.P.instPrime

/-! ## Commitment Operations -/

/-- Pedersen commitment: `C = g₁^m · h^r = g₁^(m + β·r)`.

The commitment is computed as a product of two group elements:
one determined by the message, one by the randomness. -/
noncomputable def commit (m r : ZMod pp.P.p) : pp.P.G₁ :=
  (pp.P.g₁ ^ᵍ m) * (pp.h ^ᵍ r)

/-- The commitment equals `g₁^(m + β·r)` when expressed as a single exponentiation. -/
theorem commit_eq_zpow (m r : ZMod pp.P.p) :
    pp.commit m r = pp.P.g₁ ^ᵍ (m + pp.β * r) := by
  simp only [commit, h, zpowZMod₁_zpowZMod₁, zpowZMod₁_add]

/-- Verification: check that `C = g₁^m · h^r`. -/
noncomputable def verify (C : pp.P.G₁) (m r : ZMod pp.P.p) : Bool :=
  decide (C = pp.commit m r)

/-! ## Hiding Game -/

/-- Pedersen hiding adversary: chooses two messages, then distinguishes from commitment. -/
structure PedHidingAdv where
  /-- Choose two messages -/
  choose : SPComp (ZMod pp.P.p × ZMod pp.P.p)
  /-- Distinguish given commitment -/
  distinguish : pp.P.G₁ → SPComp Bool

/-- Pedersen hiding game with bit `b`: commit to `m_b` with fresh randomness. -/
noncomputable def PedHiding_Game (A : pp.PedHidingAdv) (b : Bool) : SPComp Bool := do
  let (m₀, m₁) ← A.choose
  let m := if b then m₁ else m₀
  let r ← SPComp.sample (ZMod pp.P.p)
  A.distinguish (pp.commit m r)

/-- Pedersen hiding advantage. -/
noncomputable def PedHiding_Advantage (A : pp.PedHidingAdv) : ℝ≥0∞ :=
  Advantage (pp.PedHiding_Game A false) (pp.PedHiding_Game A true)

/-! ## Perfect Hiding Proof -/

/-- Key algebraic identity: shifting the randomness by `δ = β⁻¹ · (m₁ - m₀)`
transforms a commitment to `m₀` into a commitment to `m₁`.

Specifically: `commit(m₁, r) = commit(m₀, r + β⁻¹·(m₁ - m₀))`. -/
private theorem commit_shift (m₀ m₁ r : ZMod pp.P.p) :
    pp.commit m₁ r = pp.commit m₀ (r + pp.β⁻¹ * (m₁ - m₀)) := by
  rw [commit_eq_zpow, commit_eq_zpow]
  congr 1
  field_simp [pp.hβ]
  ring

/-- For any two messages, the commitment games are equal.

This is the core of perfect hiding: sampling `r` uniformly and computing
`commit(m₀, r)` gives the same distribution as `commit(m₁, r)`, because
the bijection `r ↦ r + β⁻¹·(m₁ - m₀)` preserves uniformity. -/
theorem commit_game_eq (A : pp.PedHidingAdv) (m₀ m₁ : ZMod pp.P.p) :
    (SPComp.bind (SPComp.sample (ZMod pp.P.p)) fun r => A.distinguish (pp.commit m₀ r)) =
    (SPComp.bind (SPComp.sample (ZMod pp.P.p)) fun r => A.distinguish (pp.commit m₁ r)) := by
  conv_rhs => arg 2; ext r; rw [commit_shift pp m₀ m₁ r]
  exact (SPComp.sample_bind_equiv (Equiv.addRight (pp.β⁻¹ * (m₁ - m₀)))
    (fun r => A.distinguish (pp.commit m₀ r))).symm

/-- **Perfect hiding**: The Pedersen hiding advantage is exactly 0.

For any adversary `A`, the hiding games for bit 0 and bit 1 produce identical
distributions, regardless of which messages the adversary chooses. -/
theorem pedersen_perfect_hiding (A : pp.PedHidingAdv) :
    pp.PedHiding_Advantage A = 0 := by
  unfold PedHiding_Advantage PedHiding_Game
  simp only [SPComp.monad_bind_eq]
  -- Both games: choose >>= fun (m₀, m₁) => sample r >>= distinguish(commit(m_b, r))
  -- Show they are equal by showing inner games are equal for all (m₀, m₁)
  have h : (SPComp.bind A.choose fun p =>
              SPComp.bind (SPComp.sample (ZMod pp.P.p)) fun r =>
                A.distinguish (pp.commit (if false then p.2 else p.1) r)) =
           (SPComp.bind A.choose fun p =>
              SPComp.bind (SPComp.sample (ZMod pp.P.p)) fun r =>
                A.distinguish (pp.commit (if true then p.2 else p.1) r)) := by
    congr 1; funext ⟨m₀, m₁⟩
    simp only [ite_true]
    exact commit_game_eq pp A m₀ m₁
  simp only [Advantage, h, tsub_self, max_self]

/-! ## Binding Game and DLog Reduction -/

/-- The DLog game specialized for Pedersen: sample `β`, give `h = g₁^β` to adversary.

We need a game where `β` is sampled (rather than fixed as in `PedersenParams`),
so the reduction works for any `β`. The adversary outputs `(m₁, m₂, r₁, r₂)`. -/
noncomputable def PedBinding_Game_sampled
    (P : PairingGroup) (A : P.G₁ → SPComp (ZMod P.p × ZMod P.p × ZMod P.p × ZMod P.p)) :
    SPComp Bool :=
  SPComp.bind (SPComp.sample (ZMod P.p)) fun β =>
  SPComp.bind (A (P.g₁ ^ᵍ β)) fun out =>
    let m₁ := out.1
    let m₂ := out.2.1
    let r₁ := out.2.2.1
    let r₂ := out.2.2.2
    SPComp.pure (decide (m₁ ≠ m₂ ∧
      zpowZMod₁ (P := P) P.g₁ (m₁ + β * r₁) =
      zpowZMod₁ (P := P) P.g₁ (m₂ + β * r₂)))

/-- The DLog reduction adversary: given `h = g₁^β` and a binding break
`(m₁, m₂, r₁, r₂)` with `m₁ ≠ m₂` and `g₁^(m₁ + β·r₁) = g₁^(m₂ + β·r₂)`,
extract `β = (m₁ - m₂) · (r₂ - r₁)⁻¹`. -/
noncomputable def binding_to_dlog (P : PairingGroup)
    (A : P.G₁ → SPComp (ZMod P.p × ZMod P.p × ZMod P.p × ZMod P.p)) :
    DL_Adversary P :=
  fun h_elem =>
  SPComp.bind (A h_elem) fun out =>
    let m₁ := out.1
    let m₂ := out.2.1
    let r₁ := out.2.2.1
    let r₂ := out.2.2.2
    SPComp.pure ((m₁ - m₂) * (r₂ - r₁)⁻¹)

/-! ## Algebraic Core Lemmas -/

/-- Injectivity of `g₁^·` : if `g₁ ^ᵍ a = g₁ ^ᵍ b` then `a = b` in `ZMod p`. -/
private theorem zpowZMod₁_g₁_injective (P : PairingGroup) (a b : ZMod P.p)
    (h : zpowZMod₁ (P := P) P.g₁ a = zpowZMod₁ (P := P) P.g₁ b) : a = b := by
  rw [← sub_eq_zero, ← zpowZMod₁_eq_one_iff, zpowZMod₁_sub, h, mul_inv_cancel]

/-- When `m₁ ≠ m₂` and `m₁ + β·r₁ = m₂ + β·r₂` in `ZMod p`,
we can extract `β = (m₁ - m₂) · (r₂ - r₁)⁻¹`.

This is the algebraic heart of the binding-to-DLog reduction. -/
private theorem binding_extracts_dlog (P : PairingGroup) [Fact (Nat.Prime P.p)]
    (β m₁ m₂ r₁ r₂ : ZMod P.p)
    (hne : m₁ ≠ m₂)
    (hcommit : m₁ + β * r₁ = m₂ + β * r₂) :
    (m₁ - m₂) * (r₂ - r₁)⁻¹ = β := by
  have hexp : m₁ - m₂ = β * (r₂ - r₁) := by linear_combination hcommit
  have hr_ne : r₂ - r₁ ≠ 0 := fun heq => hne (by linear_combination hcommit + β * heq)
  rw [hexp, mul_assoc, mul_inv_cancel₀ hr_ne, mul_one]

/-! ## Binding Security Bound -/

/-- **Computational binding from DLog**: Breaking Pedersen binding implies solving DLog.

Given an adversary `A` that breaks binding with advantage `ε`, we construct
a DLog adversary `binding_to_dlog A` with advantage at least `ε`.

The proof proceeds by:
1. Unfolding both games to expose the common `sample β >>= (A (g₁^β) >>= ...)`
2. Applying `prTrue_bind_mono` at each bind layer
3. Using the algebraic lemma to show a binding break implies a DLog solution -/
theorem pedersen_binding_le_dlog (P : PairingGroup)
    (A : P.G₁ → SPComp (ZMod P.p × ZMod P.p × ZMod P.p × ZMod P.p)) :
    prTrue (PedBinding_Game_sampled P A) Heap.empty ≤
    DL_Advantage P (binding_to_dlog P A) := by
  unfold DL_Advantage DL_Game binding_to_dlog PedBinding_Game_sampled
  simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
  -- Both games: sample β >>= (A (g₁^β) >>= pure ∘ decide ∘ check)
  -- Apply monotonicity through the outer sample bind
  apply prTrue_bind_mono
  intro β _h_β
  -- Apply monotonicity through the adversary bind
  apply prTrue_bind_mono
  intro out _h_out
  -- Now prove: binding check → DLog check
  apply prTrue_pure_decide_mono
  intro ⟨hne, hcommit⟩
  -- hcommit : g₁^(m₁ + β·r₁) = g₁^(m₂ + β·r₂)
  -- By injectivity of g₁^·: m₁ + β·r₁ = m₂ + β·r₂
  have hexp_eq : out.1 + β * out.2.2.1 = out.2.1 + β * out.2.2.2 :=
    zpowZMod₁_g₁_injective P _ _ hcommit
  -- By algebraic extraction: (m₁ - m₂)·(r₂ - r₁)⁻¹ = β
  exact binding_extracts_dlog P β out.1 out.2.1 out.2.2.1 out.2.2.2 hne hexp_eq

/-! ## UC Wrapping -/

/-- **UC security for Pedersen hiding (perfect, ε = 0)**.

Since the commitment distributions are independent of the committed message
(by the bijection argument), UC emulation holds at ε = 0
via `UCEmulates_of_game_eq`. -/
theorem pedersen_hiding_uc (V : Type) :
    UCEmulates 0 (UCSpec.ofGame (ZMod pp.P.p × ZMod pp.P.p) pp.P.G₁ V)
      (UCProtocol.ofGame (fun (p : ZMod pp.P.p × ZMod pp.P.p) =>
        SPComp.bind (SPComp.sample (ZMod pp.P.p)) fun r =>
          SPComp.pure (pp.commit p.1 r)))
      (UCProtocol.ofGame (fun (p : ZMod pp.P.p × ZMod pp.P.p) =>
        SPComp.bind (SPComp.sample (ZMod pp.P.p)) fun r =>
          SPComp.pure (pp.commit p.2 r))) := by
  apply UCEmulates_of_game_eq
  funext ⟨m₀, m₁⟩
  conv_rhs => arg 2; ext r; rw [commit_shift pp m₀ m₁ r]
  exact (SPComp.sample_bind_equiv (Equiv.addRight (pp.β⁻¹ * (m₁ - m₀)))
    (fun r => SPComp.pure (pp.commit m₀ r))).symm

/-! ## Combined Security Statement -/

/-- **Full Pedersen security**: perfect hiding and computational binding.

* **Hiding**: The hiding advantage is 0 for any adversary (information-theoretic).
* **Binding**: The binding advantage is bounded by the DLog advantage (computational).

Together, these give the standard Pedersen security guarantee:
the scheme is perfectly hiding and computationally binding under DLog. -/
theorem pedersen_full_security :
    (∀ A, pp.PedHiding_Advantage A = 0) ∧
    (∀ A, prTrue (PedBinding_Game_sampled pp.P A) Heap.empty ≤
          DL_Advantage pp.P (binding_to_dlog pp.P A)) :=
  ⟨pedersen_perfect_hiding pp, pedersen_binding_le_dlog pp.P⟩

end PedersenParams

end CatCrypt.Examples.Commitments.Pedersen
