/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Advantage
public import CatCryptCore.Relational.Rules
public import CatCryptCore.Prob.XorBij
public import CatCryptCore.Tactics.Basic

/-!
# Universal Hashing and Carter-Wegman MAC

This file formalizes universal hash families and the Carter-Wegman one-time MAC
construction from Chapter 12 of "The Joy of Cryptography".

## Main definitions

* `UHFamily` — universal hash family structure
* `boolPairwiseHash` — pairwise-independent hash over Bool: H(k₁,k₂)(m) = (k₁∧m) ⊕ k₂
* `uh_forge_game`, `UH_Forgery_Prob` — one-time forgery game: the adversary
  receives the tag of a message `m` and wins with a valid tag on a message
  `m* ≠ m`
* `IsUniversal` — universality property

## Main results

* `boolHash_forge_prob_le` — one-time forgery probability ≤ 1/2 for the Bool hash
* `boolPairwiseHash_is_universal` — Bool hash is 1/2-universal

`uh_forge_game`, `UH_Forgery_Prob` and `boolHash_forge_prob_le` replace
`uh_forge_real`, `uh_forge_ideal`, `UH_Forgery_Advantage`, `forge_prTrue_eq` and
`boolHash_forge_advantage`, whose game fixed the forgery and gave the adversary
no tag.

## References

* [Rosulek, The Joy of Cryptography, Chapter 12]
* [Carter & Wegman, Universal Classes of Hash Functions, 1979]
-/

@[expose] public section

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

/-! ## One-Time Forgery Game -/

open Classical in
/-- One-time forgery game: sample a key `k`, give the adversary the tag
`hash k m` of the message `m`, and return whether its output `(m*, t*)`
satisfies `m* ≠ m` and `t* = hash k m*`. -/
noncomputable def uh_forge_game (H : UHFamily) (m : H.MsgType)
    (A : H.TagType → SPComp (H.MsgType × H.TagType)) : SPComp Bool :=
  SPComp.bind (SPComp.sample H.KeyType) fun k =>
    SPComp.bind (A (H.hash k m)) fun f =>
      SPComp.pure (decide (f.1 ≠ m) && f.2 == H.hash k f.1)

/-- One-time forgery probability of `A` after seeing the tag of `m`. -/
noncomputable def UH_Forgery_Prob (H : UHFamily) (m : H.MsgType)
    (A : H.TagType → SPComp (H.MsgType × H.TagType)) : ENNReal :=
  prTrue (uh_forge_game H m A) Heap.empty

/-! ## Events of a Computation -/

/-- `prTrue` of a computation followed by a Boolean test of its result is the
mass of the results that pass the test. -/
theorem prTrue_bind_pure_test {α : Type} (c : SPComp α) (P : α → Bool) (h₀ : Heap) :
    prTrue (SPComp.bind c fun x => SPComp.pure (P x)) h₀ =
      ∑' y : α × Heap, if P y.1 = true then c h₀ (some y) else 0 := by
  unfold prTrue
  simp only [SPComp.bind, SPComp.pure, SDistr.bind, PMF.bind_apply]
  rw [ENNReal.tsum_comm, SDistr.tsum_option_eq_add]
  simp only [SDistr.fail, SDistr.pure, PMF.pure_apply, Option.some.injEq, Prod.mk.injEq,
    reduceCtorEq, if_false, mul_zero, tsum_zero, zero_add]
  refine tsum_congr fun y => ?_
  rw [ENNReal.tsum_mul_left]
  cases hP : P y.1 <;> simp

/-- Two disjoint tests of the result of one computation have total probability
at most `1`. -/
theorem prTrue_bind_pure_test_add_le {α : Type} (c : SPComp α) (P Q : α → Bool)
    (hPQ : ∀ x, ¬ (P x = true ∧ Q x = true)) (h₀ : Heap) :
    prTrue (SPComp.bind c fun x => SPComp.pure (P x)) h₀ +
      prTrue (SPComp.bind c fun x => SPComp.pure (Q x)) h₀ ≤ 1 := by
  rw [prTrue_bind_pure_test, prTrue_bind_pure_test, ← ENNReal.tsum_add]
  have h := prTrue_le_one (SPComp.bind c fun x => SPComp.pure (P x || Q x)) h₀
  rw [prTrue_bind_pure_test] at h
  refine le_trans (le_of_eq (tsum_congr fun y => ?_)) h
  have := hPQ y.1
  cases hp : P y.1 <;> cases hq : Q y.1 <;> simp_all

/-! ## Arithmetic Helpers -/

/-- 2 × 4⁻¹ = 2⁻¹ in ENNReal. -/
theorem two_mul_four_inv : 2 * (4 : ENNReal)⁻¹ = (2 : ENNReal)⁻¹ := by
  rw [show (4 : ENNReal) = 2 * 2 from by norm_num,
      ENNReal.mul_inv (Or.inl (by norm_num : (2 : ENNReal) ≠ 0))
                       (Or.inl (by norm_num : (2 : ENNReal) ≠ ⊤)),
      ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num : (2 : ENNReal) ≠ 0)
                                           (by norm_num : (2 : ENNReal) ≠ ⊤), one_mul]

/-- 4⁻¹ + 4⁻¹ = 2⁻¹ in ENNReal. -/
theorem four_inv_add : (4 : ENNReal)⁻¹ + (4 : ENNReal)⁻¹ = (2 : ENNReal)⁻¹ := by
  rw [← two_mul]; exact two_mul_four_inv

/-- Doubling a quarter gives a half: 4⁻¹*x + 4⁻¹*x = 2⁻¹*x in ENNReal. -/
theorem four_inv_double (x : ENNReal) :
    (4 : ENNReal)⁻¹ * x + (4 : ENNReal)⁻¹ * x = (2 : ENNReal)⁻¹ * x := by
  rw [← add_mul, four_inv_add]

/-! ## Main Security Theorem -/

/-- **One-time forgery bound for the Bool pairwise hash.** After seeing the tag
of `m`, any adversary outputs a valid tag on a message `m* ≠ m` with
probability at most `1/2`. The four keys form two pairs with equal tag on `m`;
within a pair the tags on `m* ≠ m` differ, so a fixed forgery is valid for at
most one key of the pair. -/
theorem boolHash_forge_prob_le (m : Bool) (A : Bool → SPComp (Bool × Bool)) :
    UH_Forgery_Prob boolPairwiseHash m A ≤ (2 : ENNReal)⁻¹ := by
  have pair : ∀ a b c d : ENNReal, a + c ≤ 1 → b + d ≤ 1 →
      4⁻¹ * a + 4⁻¹ * b + (4⁻¹ * c + 4⁻¹ * d) ≤ (2 : ENNReal)⁻¹ := by
    intro a b c d hac hbd
    calc 4⁻¹ * a + 4⁻¹ * b + (4⁻¹ * c + 4⁻¹ * d)
        = 4⁻¹ * (a + c) + 4⁻¹ * (b + d) := by ring
      _ ≤ 4⁻¹ * 1 + 4⁻¹ * 1 := by gcongr
      _ = (2 : ENNReal)⁻¹ := by rw [mul_one, four_inv_add]
  unfold UH_Forgery_Prob uh_forge_game boolPairwiseHash
  rw [prTrue_bind_sample]
  simp only [Fintype.card_prod, Fintype.card_bool]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, show (2 * 2 : ℕ) = 4 from rfl, Nat.cast_ofNat]
  cases m <;> simp only [Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true,
    Bool.xor_false, Bool.xor_true]
  · exact pair _ _ _ _
      (prTrue_bind_pure_test_add_le _ _ _ (fun f => by rcases f with ⟨_ | _, _ | _⟩ <;> simp) _)
      (prTrue_bind_pure_test_add_le _ _ _ (fun f => by rcases f with ⟨_ | _, _ | _⟩ <;> simp) _)
  · rw [add_comm (4⁻¹ * _) (4⁻¹ * prTrue ((A false).bind _) _)]
    exact pair _ _ _ _
      (prTrue_bind_pure_test_add_le _ _ _ (fun f => by rcases f with ⟨_ | _, _ | _⟩ <;> simp) _)
      (prTrue_bind_pure_test_add_le _ _ _ (fun f => by rcases f with ⟨_ | _, _ | _⟩ <;> simp) _)

/-- Concrete instance: the one-time forgery probability of the Bool hash MAC is
at most its collision bound `ε = 1/2`. -/
theorem boolPairwiseHash_mac_security (m : Bool) (A : Bool → SPComp (Bool × Bool)) :
    UH_Forgery_Prob boolPairwiseHash m A ≤ boolPairwiseHash.epsilon :=
  boolHash_forge_prob_le m A

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
theorem collision_prTrue_eq (m₁ m₂ : Bool) (h_ne : m₁ ≠ m₂)
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
