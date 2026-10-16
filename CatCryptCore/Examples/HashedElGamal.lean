/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.CyclicGroupDDH
public import CatCryptCore.Prob.XorBij
public import CatCryptCore.Tactics.Triangle

/-!
# Hashed ElGamal Encryption

Hashed ElGamal masks the message with a hash of the Diffie-Hellman shared
secret rather than a group element, so it encrypts messages of an arbitrary
type (group elements or otherwise) and achieves IND-CPA security under the
DDH assumption in the ROM.

## Construction

Given a cyclic group G with generator g:
- `keyGen`: Sample `sk ← Exp`; output `(sk, pk = g^sk)`
- `encrypt(pk, m)`: Sample `r ← Exp`; output `(g^r, m ⊕ H(pk^r))`
- `decrypt(sk, (c₁, c₂))`: Output `c₂ ⊕ H(c₁^sk)`

where H : G → {0,1}^n is a hash function and ⊕ is XOR.

## Security

`heg_indcpa_le_ddh`: if `H ∘ pow` maps a uniform exponent to a uniform bit, then
for every adversary the IND-CPA advantage is at most the sum of the DDH
advantages of the two reductions `heg_ddh_reduction H m₀ A` and
`heg_ddh_reduction H m₁ A`. The earlier form of this theorem assumed the
message independence of the ideal DDH world (`h_ideal_indep`), which is the
hash-uniformity hop itself; it is now proved (`heg_ddh_ideal_indep`).

The reduction:
- Given DDH challenge (g^a, g^b, z)
- Set pk = g^a, c₁ = g^b
- If z = g^(ab): H(z) masks m correctly (real game)
- If z = g^c:   H(z) is fresh random (ideal/OTP game)

## References

* [Abdalla, Bellare & Rogaway, The Oracle Diffie-Hellman Assumptions, 2001]
* [Shoup, A Proposal for an ISO Standard for PKE, 2001]
-/

@[expose] public section

set_option autoImplicit false

namespace CatCryptCore.Examples.HashedElGamal

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCryptCore.Examples.CyclicGroupDDH
open CatCrypt.Relational
open scoped ENNReal

/-! ## Hash Function Type -/

/-- A hash function from group elements to the plaintext space.
    In the ROM, this would be modeled as a random oracle. -/
structure HashFunc (G : Type) [CG : CyclicGroup G] (PT : Type) where
  hash : G → PT

/-! ## Hashed ElGamal Scheme -/

variable {G : Type} [CG : CyclicGroup G]

/-- Hashed ElGamal key generation: sample secret key, compute public key. -/
noncomputable def heg_keyGen : SPComp (CG.Exp × G) := do
  let sk ← SPComp.sample CG.Exp
  return (sk, CG.pow sk)

/-- Hashed ElGamal encryption with XOR masking (for Bool plaintext).

    encrypt(pk, m) = (g^r, m ⊕ H(pk^r)) for random r.

    Here we use Bool as the plaintext type and xor as the masking operation. -/
noncomputable def heg_encrypt_bool (H : G → Bool)
    (pk : G) (m : Bool) : SPComp (G × Bool) := do
  let r ← SPComp.sample CG.Exp
  let c₁ := CG.pow r
  let shared := CG.elemPow pk r  -- pk^r = g^(sk·r)
  let mask := H shared
  return (c₁, xor mask m)

/-- Hashed ElGamal decryption for Bool plaintext.

    decrypt(sk, (c₁, c₂)) = c₂ ⊕ H(c₁^sk) -/
noncomputable def heg_decrypt_bool (H : G → Bool)
    (sk : CG.Exp) (ct : G × Bool) : Bool :=
  let (c₁, c₂) := ct
  let shared := CG.elemPow c₁ sk  -- c₁^sk = g^(r·sk)
  let mask := H shared
  xor mask c₂

/-! ## Correctness -/

/-- Decryption inverts encryption: H(pk^r) ⊕ (H(pk^r) ⊕ m) = m.

    Correctness relies on:
    - pk^r = g^(sk·r) = (g^r)^sk = c₁^sk
    - H is deterministic
    - XOR is self-inverse -/
theorem heg_correct_bool (H : G → Bool) (sk : CG.Exp) (m : Bool) (r : CG.Exp) :
    let pk := CG.pow sk
    let shared := CG.elemPow pk r
    heg_decrypt_bool H sk (CG.pow r, xor (H shared) m) = m := by
  simp only [heg_decrypt_bool]
  -- Need: xor (H (elemPow (pow r) sk)) (xor (H (elemPow (pow sk) r)) m) = m
  -- By elemPow_pow: elemPow (pow e) a = pow (expMul e a)
  -- So both sides reduce to pow (expMul sk r) = pow (expMul r sk) by pow_comm
  have hcomm : CG.elemPow (CG.pow r) sk = CG.elemPow (CG.pow sk) r := by
    rw [CyclicGroup.elemPow_pow, CyclicGroup.elemPow_pow, CG.pow_comm]
  rw [hcomm]
  cases (H (CG.elemPow (CG.pow sk) r)) <;> cases m <;> rfl

/-! ## IND-CPA Security Game -/

/-- Real IND-CPA game for Hashed ElGamal:
    sample (sk, pk), sample r, return (g^r, H(pk^r) ⊕ m). -/
noncomputable def heg_real (H : G → Bool) (m : Bool) : SPComp (G × Bool) := do
  let sk ← SPComp.sample CG.Exp
  let pk := CG.pow sk
  heg_encrypt_bool H pk m

/-- Ideal game (random mask): replace H(g^(sk·r)) with a random bit.
    This is the OTP game — perfectly secure. -/
noncomputable def heg_ideal (m : Bool) : SPComp (G × Bool) := do
  let _sk ← SPComp.sample CG.Exp
  let r ← SPComp.sample CG.Exp
  let c₁ := CG.pow r
  let mask ← SPComp.sample Bool
  return (c₁, xor mask m)

/-! ## DDH-based Security Reduction -/

/-- DDH distinguisher from a Hashed ElGamal IND-CPA adversary.

Given DDH challenge (g^a, g^b, z):
- pk := g^a, c₁ := g^b
- If z = g^(ab): encrypt = (g^b, H(g^(ab)) ⊕ m) = real game
- If z = g^c:    encrypt = (g^b, H(g^c) ⊕ m) with independent H(g^c) -/
noncomputable def heg_ddh_reduction (H : G → Bool) (m : Bool)
    (A : (G × Bool) → SPComp Bool)
    (challenge : DDHTriple G) : SPComp Bool :=
  let (_ga, gb, z) := challenge
  -- Use _ga as pk, gb as c₁, H(z) as mask
  let ct := (gb, xor (H z) m)
  A ct

/-- LHS normal form: heg_real.bind A as explicit double-sample. -/
theorem heg_real_bind_eq (H : G → Bool) (m : Bool)
    (A : (G × Bool) → SPComp Bool) :
    (heg_real H m).bind A =
    SPComp.bind (SPComp.sample CG.Exp) (fun sk =>
      SPComp.bind (SPComp.sample CG.Exp) (fun r =>
        A (CG.pow r, xor (H (CG.pow (CG.expMul sk r))) m))) := by
  unfold heg_real heg_encrypt_bool
  simp only [SPComp.monad_bind_eq, SPComp.bind_assoc]
  congr 1; funext sk; congr 1; funext r
  simp only [CyclicGroup.elemPow_pow]
  show (SPComp.pure (CG.pow r, xor (H (CG.pow (CG.expMul sk r))) m)).bind A =
       A (CG.pow r, xor (H (CG.pow (CG.expMul sk r))) m)
  grind

/-- RHS normal form: DDH_real.bind reduction as explicit double-sample. -/
theorem ddh_real_bind_red_eq (H : G → Bool) (m : Bool)
    (A : (G × Bool) → SPComp Bool) :
    (DDH_real G).bind (heg_ddh_reduction H m A) =
    SPComp.bind (SPComp.sample CG.Exp) (fun a =>
      SPComp.bind (SPComp.sample CG.Exp) (fun b =>
        A (CG.pow b, xor (H (CG.pow (CG.expMul a b))) m))) := by
  unfold DDH_real heg_ddh_reduction
  simp only [SPComp.monad_bind_eq, SPComp.bind_assoc]
  congr 1; funext a; congr 1; funext b
  show (SPComp.pure (CG.pow a, CG.pow b, CG.pow (CG.expMul a b))).bind
      (fun challenge => A (challenge.2.1, xor (H challenge.2.2) m)) =
    A (CG.pow b, xor (H (CG.pow (CG.expMul a b))) m)
  grind

/-- Program equality: the real Hashed ElGamal game composed with adversary A
    equals the DDH real game composed with the DDH reduction. -/
theorem heg_real_eq_ddh_real (H : G → Bool) (m : Bool)
    (A : (G × Bool) → SPComp Bool) :
    (heg_real H m).bind A = (DDH_real G).bind (heg_ddh_reduction H m A) := by
  grind [heg_real_bind_eq, ddh_real_bind_red_eq]

/-- The DDH reduction run on the ideal DDH triple, in sampled form: the mask is
`H (g^c)` for an exponent `c` independent of the ciphertext component `g^b`. -/
theorem ddh_ideal_bind_red_eq (H : G → Bool) (m : Bool)
    (A : (G × Bool) → SPComp Bool) :
    (DDH_ideal G).bind (heg_ddh_reduction H m A) =
    SPComp.bind (SPComp.sample CG.Exp) (fun _a =>
      SPComp.bind (SPComp.sample CG.Exp) (fun b =>
        SPComp.bind (SPComp.bind (SPComp.sample CG.Exp) fun c => SPComp.pure (H (CG.pow c)))
          (fun mask => A (CG.pow b, xor mask m)))) := by
  unfold DDH_ideal heg_ddh_reduction
  simp only [SPComp.monad_bind_eq, SPComp.monad_pure_eq, SPComp.bind_assoc, SPComp.pure_bind]

/-- **The ideal DDH world does not depend on the message.** If `H ∘ pow` maps a
uniform exponent to a uniform bit, the DDH reduction run on the ideal DDH triple
has the same distribution for the messages `m₀` and `m₁`: the mask `H (g^c)` is a
uniform bit independent of `g^b`, and `mask ↦ mask ⊕ m` is a bijection of `Bool`. -/
theorem heg_ddh_ideal_indep (H : G → Bool)
    (hH : SPComp.bind (SPComp.sample CG.Exp) (fun c => SPComp.pure (H (CG.pow c))) =
      SPComp.sample Bool)
    (m₀ m₁ : Bool) (A : (G × Bool) → SPComp Bool) :
    (DDH_ideal G).bind (heg_ddh_reduction H m₀ A) =
      (DDH_ideal G).bind (heg_ddh_reduction H m₁ A) := by
  have hmask : ∀ (gb : G) (m : Bool),
      SPComp.bind (SPComp.sample Bool) (fun mask => A (gb, xor mask m)) =
        SPComp.bind (SPComp.sample Bool) (fun mask => A (gb, mask)) := fun gb m =>
    SPComp.sample_bind_equiv (CatCrypt.Prob.XorBij.boolXorBij m) (fun mask => A (gb, mask))
  rw [ddh_ideal_bind_red_eq, ddh_ideal_bind_red_eq, hH]
  simp only [hmask]

/-- **Hashed ElGamal IND-CPA advantage is bounded by two DDH advantages.**

If `H ∘ pow` maps a uniform exponent to a uniform bit (`hH`, an
information-theoretic property of the hash), then for every adversary `A`

    `Adv(heg_real m₀, heg_real m₁) A ≤ DDH_Advantage (red m₀ A) + DDH_Advantage (red m₁ A)`,

where `red m A = heg_ddh_reduction H m A`. The real game is the real DDH world
against the reduction (`heg_real_eq_ddh_real`); the two ideal DDH worlds
coincide (`heg_ddh_ideal_indep`). -/
theorem heg_indcpa_le_ddh (H : G → Bool)
    (hH : SPComp.bind (SPComp.sample CG.Exp) (fun c => SPComp.pure (H (CG.pow c))) =
      SPComp.sample Bool)
    (m₀ m₁ : Bool) (A : (G × Bool) → SPComp Bool) :
    AdvantageA (heg_real H m₀) (heg_real H m₁) A ≤
    DDH_Advantage G (heg_ddh_reduction H m₀ A) +
    DDH_Advantage G (heg_ddh_reduction H m₁ A) := by
  unfold AdvantageA
  rw [heg_real_eq_ddh_real H m₀ A, heg_real_eq_ddh_real H m₁ A]
  have htri := advantage_triangle
    ((DDH_real G).bind (heg_ddh_reduction H m₀ A))
    ((DDH_ideal G).bind (heg_ddh_reduction H m₀ A))
    ((DDH_real G).bind (heg_ddh_reduction H m₁ A))
  nth_rewrite 2 [heg_ddh_ideal_indep H hH m₀ m₁ A] at htri
  rw [Advantage_sym ((DDH_ideal G).bind (heg_ddh_reduction H m₁ A))] at htri
  exact htri

/-! ## Perfect Security with Random Oracle

When H is a truly random function (perfect hash), the encryption
mask is uniformly random regardless of the shared secret, giving
perfect IND-CPA security. -/

omit CG in
/-- OTP core: with a uniform mask, `(c₁, mask ⊕ m)` has the same distribution as
    `(c₁, mask)` — the message `m` is masked away. This is the one-time-pad
    bijection (`boolXorBij m`) applied inside the sampled mask, giving perfect
    secrecy of the ideal Hashed ElGamal game. -/
theorem heg_ideal_mask_indep (c₁ : G) (m : Bool) :
    (SPComp.sample Bool).bind (fun mask => SPComp.pure (c₁, xor mask m)) =
    (SPComp.sample Bool).bind (fun mask => SPComp.pure (c₁, mask)) := by
  funext h
  rw [SPComp.sample_bind_pure Bool (fun mask => (c₁, xor mask m)) h,
      SPComp.sample_bind_pure Bool (fun mask => (c₁, mask)) h]
  exact SDistr.uniform_bind_equiv_comp (CatCrypt.Prob.XorBij.boolXorBij m)
    (fun mask => SDistr.pure ((c₁, mask), h))

/-- Perfect secrecy of the ideal game: the two ideal games for distinct messages
    are the *same distribution*. Only the innermost mask depends on the message,
    and the OTP bijection removes that dependence. -/
theorem heg_ideal_indep (m₀ m₁ : Bool) :
    heg_ideal (G := G) m₀ = heg_ideal (G := G) m₁ := by
  unfold heg_ideal
  simp only [SPComp.monad_bind_eq, SPComp.monad_pure_eq]
  congr 1; funext _sk; congr 1; funext r
  rw [heg_ideal_mask_indep (CG.pow r) m₀, heg_ideal_mask_indep (CG.pow r) m₁]

/-- With a perfect random oracle, Hashed ElGamal has **zero** IND-CPA advantage:
    the two ideal games are the same distribution (`heg_ideal_indep`), so every
    adversary distinguishes them with advantage `0`. This is the OTP/perfect-secrecy
    endpoint the DDH reduction (`heg_indcpa_le_ddh`) targets. -/
theorem heg_perfect_hash_security (m₀ m₁ : Bool)
    (A : (G × Bool) → SPComp Bool) :
    AdvantageA (heg_ideal (G := G) m₀) (heg_ideal (G := G) m₁) A = 0 := by
  rw [heg_ideal_indep m₀ m₁]
  simp only [AdvantageA, Advantage_self]

end CatCryptCore.Examples.HashedElGamal
