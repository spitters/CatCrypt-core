/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.Advantage
import CatCryptCore.Relational.Rules
import CatCryptCore.Prob.XorBij
import CatCryptCore.Tactics.Basic

/-!
# Universal Hashing and Carter-Wegman MAC

This file formalizes universal hash families and the Carter-Wegman one-time MAC
construction from Chapter 12 of "The Joy of Cryptography".

## Main definitions

* `UHFamily` — universal hash family structure
* `boolPairwiseHash` — pairwise-independent hash over Bool: H(k₁,k₂)(m) = (k₁∧m) ⊕ k₂
* `uh_forge_real`, `uh_forge_ideal` — forgery games
* `IsUniversal` — universality property

## Main results

* `boolHash_forge_advantage` — forgery advantage ≤ 1/2 for Bool hash
* `boolPairwiseHash_is_universal` — Bool hash is 1/2-universal

## References

* [Rosulek, The Joy of Cryptography, Chapter 12]
* [Carter & Wegman, Universal Classes of Hash Functions, 1979]
-/

namespace CatCryptCore.Examples.UniversalHash

open CatCrypt.Core
open CatCrypt.Prob
open CatCrypt.Crypto
open CatCrypt.Prob.XorBij
open CatCrypt.Relational

open scoped ENNReal

/-! ## Universal Hash Family -/

/-- A universal hash family with collision bound ε. -/
structure UHFamily where
  KeyType : Type
  MsgType : Type
  TagType : Type
  [finKey : Fintype KeyType]
  [neKey : Nonempty KeyType]
  [decEqTag : DecidableEq TagType]
  hash : KeyType → MsgType → TagType
  epsilon : ENNReal

attribute [instance] UHFamily.finKey UHFamily.neKey UHFamily.decEqTag

/-- Pairwise-independent hash over Bool. -/
noncomputable def boolPairwiseHash : UHFamily where
  KeyType := Bool × Bool
  MsgType := Bool
  TagType := Bool
  hash := fun ⟨k₁, k₂⟩ m => xor (k₁ && m) k₂
  epsilon := (2 : ENNReal)⁻¹

/-! ## Forgery Games -/

/-- Real forgery game: sample key, check if adversary's guess matches hash on new message. -/
noncomputable def uh_forge_real (H : UHFamily) (_m m_star : H.MsgType)
    (t_star : H.TagType) : SPComp Bool := do
  let k ← SPComp.sample H.KeyType
  SPComp.pure (t_star == H.hash k m_star)

/-- Ideal forgery game: forgery always fails. -/
noncomputable def uh_forge_ideal : SPComp Bool := SPComp.pure false

/-- Forgery advantage. -/
noncomputable def UH_Forgery_Advantage (H : UHFamily) (m m_star : H.MsgType)
    (t_star : H.TagType) (A : Bool → SPComp Bool) : ENNReal :=
  AdvantageA (uh_forge_real H m m_star t_star) uh_forge_ideal A

/-! ## IsPure Proofs -/

theorem uh_forge_real_isPure (H : UHFamily) (m m_star : H.MsgType)
    (t_star : H.TagType) : SPComp.IsPure (uh_forge_real H m m_star t_star) := by
  unfold uh_forge_real; simp only [SPComp.monad_bind_eq]
  exact SPComp.bind_isPure (SPComp.sample_isPure _) (fun _ => SPComp.pure_isPure _)

theorem uh_forge_ideal_isPure : SPComp.IsPure uh_forge_ideal :=
  SPComp.pure_isPure _

/-! ## Arithmetic Helpers -/

/-- 2 × 4⁻¹ = 2⁻¹ in ENNReal. -/
private theorem two_mul_four_inv : 2 * (4 : ENNReal)⁻¹ = (2 : ENNReal)⁻¹ := by
  rw [show (4 : ENNReal) = 2 * 2 from by norm_num,
      ENNReal.mul_inv (Or.inl (by norm_num : (2 : ENNReal) ≠ 0))
                       (Or.inl (by norm_num : (2 : ENNReal) ≠ ⊤)),
      ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num : (2 : ENNReal) ≠ 0)
                                           (by norm_num : (2 : ENNReal) ≠ ⊤), one_mul]

/-- 4⁻¹ + 4⁻¹ = 2⁻¹ in ENNReal. -/
private theorem four_inv_add : (4 : ENNReal)⁻¹ + (4 : ENNReal)⁻¹ = (2 : ENNReal)⁻¹ := by
  rw [← two_mul]; exact two_mul_four_inv

/-- Doubling a quarter gives a half: 4⁻¹*x + 4⁻¹*x = 2⁻¹*x in ENNReal. -/
private theorem four_inv_double (x : ENNReal) :
    (4 : ENNReal)⁻¹ * x + (4 : ENNReal)⁻¹ * x = (2 : ENNReal)⁻¹ * x := by
  rw [← add_mul, four_inv_add]

/-! ## Core prTrue Equality -/

/-- For the Bool pairwise hash forgery game with m_star ≠ m,
    the prTrue distribution equals that of uniform Bool sampling.

    The proof expands the sums over Bool × Bool, computes the hash values,
    and uses arithmetic to show the 4-element sum equals the 2-element sum. -/
private theorem forge_prTrue_eq (m m_star : Bool) (t_star : Bool)
    (h_diff : m_star ≠ m) (A : Bool → SPComp Bool) (h₀ : Heap) :
    prTrue ((uh_forge_real boolPairwiseHash m m_star t_star).bind A) h₀ =
    prTrue ((SPComp.sample Bool).bind A) h₀ := by
  unfold uh_forge_real boolPairwiseHash
  simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
  rw [prTrue_bind_sample, prTrue_bind_sample]
  simp only [Fintype.card_prod, Fintype.card_bool]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, show (2 * 2 : ℕ) = 4 from rfl, Nat.cast_ofNat]
  cases m_star <;> cases t_star <;> (
    simp only [Bool.false_and, Bool.true_and, xor_false_right, xor_true_right,
               Bool.not_false, Bool.not_true,
               show (false == false) = true from rfl,
               show (false == true) = false from rfl,
               show (true == false) = false from rfl,
               show (true == true) = true from rfl]
    simp only [← add_mul, four_inv_add, add_comm, add_left_comm]
    try rw [← add_assoc, four_inv_double])

/-! ## Main Security Theorem -/

/-- For the Bool hash, forgery advantage ≤ 1/2.
    Uses forge_prTrue_eq to show the advantage equals that of sample Bool vs pure false. -/
theorem boolHash_forge_advantage (m m_star : Bool) (t_star : Bool)
    (h_diff : m_star ≠ m) (A : Bool → SPComp Bool) :
    UH_Forgery_Advantage boolPairwiseHash m m_star t_star A ≤ (2 : ENNReal)⁻¹ := by
  unfold UH_Forgery_Advantage uh_forge_ideal AdvantageA Advantage
  rw [forge_prTrue_eq m m_star t_star h_diff A]
  exact advantage_sample_vs_pure_false A

/-- Concrete instance: Bool hash MAC security bound. -/
theorem boolPairwiseHash_mac_security (m m_star : Bool) (t_star : Bool)
    (h_diff : m_star ≠ m) (A : Bool → SPComp Bool) :
    UH_Forgery_Advantage boolPairwiseHash m m_star t_star A ≤
    boolPairwiseHash.epsilon :=
  boolHash_forge_advantage m m_star t_star h_diff A

/-! ## Collision Game and Universality -/

/-- Collision probability game. -/
noncomputable def collision_game (H : UHFamily) (m₁ m₂ : H.MsgType) : SPComp Bool := do
  let k ← SPComp.sample H.KeyType
  SPComp.pure (H.hash k m₁ == H.hash k m₂)

/-- A hash family is ε-universal. -/
def IsUniversal (H : UHFamily) : Prop :=
  ∀ m₁ m₂, m₁ ≠ m₂ →
    ∀ A, AdvantageA (collision_game H m₁ m₂) (SPComp.pure false) A ≤ H.epsilon

/-- Collision prTrue equals uniform Bool prTrue (same argument as forge). -/
private theorem collision_prTrue_eq (m₁ m₂ : Bool) (h_ne : m₁ ≠ m₂)
    (A : Bool → SPComp Bool) (h₀ : Heap) :
    prTrue ((collision_game boolPairwiseHash m₁ m₂).bind A) h₀ =
    prTrue ((SPComp.sample Bool).bind A) h₀ := by
  unfold collision_game boolPairwiseHash
  simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
  rw [prTrue_bind_sample, prTrue_bind_sample]
  simp only [Fintype.card_prod, Fintype.card_bool]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, show (2 * 2 : ℕ) = 4 from rfl, Nat.cast_ofNat]
  -- m₁ ≠ m₂: only two cases — (true, false) or (false, true)
  rcases m₁ with _ | _ <;> rcases m₂ with _ | _ <;>
    simp_all only [ne_eq, not_true_eq_false] <;> (
    simp only [Bool.false_and, Bool.true_and, xor_false_right, xor_true_right,
               Bool.not_false, Bool.not_true,
               show (false == false) = true from rfl,
               show (false == true) = false from rfl,
               show (true == false) = false from rfl,
               show (true == true) = true from rfl]
    simp only [← add_mul, four_inv_add, add_comm]
    try rw [← add_assoc, four_inv_double])

/-- The Bool pairwise hash is 1/2-universal. -/
theorem boolPairwiseHash_is_universal : IsUniversal boolPairwiseHash := by
  intro m₁ m₂ hne A
  unfold AdvantageA Advantage
  rw [collision_prTrue_eq m₁ m₂ hne A]
  exact advantage_sample_vs_pure_false A

end CatCryptCore.Examples.UniversalHash
