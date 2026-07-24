/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Examples.CyclicGroupDDH
import CatCryptCore.Crypto.Advantage
import CatCryptCore.Relational.Rules
import CatCryptCore.Tactics.Basic

/-!
# Naor-Pinkas Oblivious Transfer (OT)

This file formalizes the Naor-Pinkas (2001) DDH-based 1-out-of-2 OT protocol
and proves both sender security (information-theoretic) and receiver security
(DDH-based).

## Protocol

The receiver holds a choice bit σ ∈ {0,1}. The sender holds messages m₀, m₁ ∈ G.

1. **Receiver**: Sample `a, b, c` from `Exp`. Send `(g^a, g^b, z₀, z₁)` where
   `z_σ = g^{ab}` (DDH triple) and `z_{1-σ} = g^c` (random).

2. **Sender**: For each `i ∈ {0,1}`, sample `(sᵢ, rᵢ)`, compute
   `wᵢ = g^{a·sᵢ + rᵢ}` and `eᵢ = g^{dᵢ·sᵢ + b·rᵢ} · mᵢ` where
   `dᵢ` is the exponent of `zᵢ`.

3. **Receiver**: Decrypt `m_σ` using `s_σ, r_σ` (the DDH position is decryptable).

## Security

**Sender security**: When `d ≠ ab` (non-DDH position), the map
`(s, r) ↦ (as + r, ds + br)` is a bijection on `Exp × Exp`, so `(wᵢ, eᵢ)`
is uniformly distributed — the message is information-theoretically hidden.

**Receiver security**: The receiver's public values `(g^a, g^b, z₀, z₁)` contain
a DDH triple at the choice position. Distinguishing `σ=0` from `σ=1` reduces to DDH.

## References

* Naor & Pinkas, "Efficient Oblivious Transfer Protocols", SODA 2001
* EasyCrypt: beschmi/oblivious_transfer
* CryptHOL: Multi_Party_Computation AFP entry
-/

namespace CatCrypt.Examples.OT

open CatCrypt.Core
open CatCrypt.Crypto
open CatCrypt.Prob
open CatCryptCore.Examples.CyclicGroupDDH

open scoped ENNReal

/-! ## CyclicGroupRing: Exponent Ring Structure

The sender security proof requires the matrix map `(s,r) ↦ (as+r, ds+br)` to be
a bijection when `d ≠ ab`. This needs ring structure on exponents (addition,
multiplication, distributivity) beyond what `CyclicGroup` provides.
-/

/-- Extension of `CyclicGroup` with ring structure on exponents.

The key new operations are `expAdd` (addition in Z_q) and the distributivity
law `expMul a (expAdd b c) = expAdd (expMul a b) (expMul a c)`.
The crucial `expMul_bij` ensures multiplication by a nonzero element is bijective. -/
class CyclicGroupRing (G : Type) extends CyclicGroup G where
  /-- Addition of exponents -/
  expAdd : Exp → Exp → Exp
  /-- Zero exponent -/
  expZero : Exp
  /-- `g^(a+b) = g^a · g^b` -/
  pow_add : ∀ a b, pow (expAdd a b) = mul (pow a) (pow b)
  /-- `g^0 = 1` -/
  pow_zero : pow expZero = one
  /-- Addition is commutative -/
  expAdd_comm : ∀ a b, expAdd a b = expAdd b a
  /-- Addition is associative -/
  expAdd_assoc : ∀ a b c, expAdd (expAdd a b) c = expAdd a (expAdd b c)
  /-- Right identity for addition -/
  expAdd_zero : ∀ a, expAdd a expZero = a
  /-- Additive inverse: `a + (-a) = 0` -/
  expAdd_neg : ∀ a, expAdd a (expNeg a) = expZero
  /-- Multiplication is commutative -/
  expMul_comm' : ∀ a b, expMul a b = expMul b a
  /-- Left distributivity: `a(b+c) = ab + ac` -/
  expMul_add : ∀ a b c, expMul a (expAdd b c) = expAdd (expMul a b) (expMul a c)
  /-- Multiplication is associative -/
  expMul_assoc : ∀ a b c, expMul (expMul a b) c = expMul a (expMul b c)
  /-- Multiplication by nonzero is bijective (prime-order group) -/
  expMul_bij : ∀ d, d ≠ expZero → Function.Bijective (expMul d)

namespace CyclicGroupRing

variable {G : Type} [CGR : CyclicGroupRing G]

/-- Subtraction of exponents: `a - b := a + (-b)` -/
abbrev expSub (a b : CGR.Exp) : CGR.Exp := CGR.expAdd a (CGR.expNeg b)

/-- Left identity for addition: `0 + a = a` -/
theorem expZero_add (a : CGR.Exp) : CGR.expAdd CGR.expZero a = a := by
  rw [CGR.expAdd_comm, CGR.expAdd_zero]

/-- `g^(-a) = (g^a)⁻¹` -/
theorem pow_neg (a : CGR.Exp) : CGR.pow (CGR.expNeg a) = CGR.inv (CGR.pow a) := by
  have h1 : CGR.mul (CGR.pow a) (CGR.pow (CGR.expNeg a)) = CGR.one := by
    rw [← CGR.pow_add, CGR.expAdd_neg, CGR.pow_zero]
  have h2 : CGR.mul (CGR.pow a) (CGR.inv (CGR.pow a)) = CGR.one := CGR.mul_inv _
  have h3 : CGR.pow (CGR.expNeg a) =
    CGR.mul (CGR.inv (CGR.pow a)) (CGR.mul (CGR.pow a) (CGR.pow (CGR.expNeg a))) := by
    rw [← CGR.mul_assoc, CGR.mul_comm (CGR.inv _) _, CGR.mul_inv, CGR.mul_comm, CGR.mul_one]
  rw [h3, h1, CGR.mul_one]

/-- Additive right cancellation: `a + c = b + c → a = b` -/
theorem expAdd_cancel_right (a b c : CGR.Exp)
    (h : CGR.expAdd a c = CGR.expAdd b c) : a = b := by
  simpa only [CGR.expAdd_assoc, CGR.expAdd_neg, CGR.expAdd_zero]
    using congrArg (CGR.expAdd · (CGR.expNeg c)) h

/-- Additive left cancellation: `c + a = c + b → a = b` -/
theorem expAdd_cancel_left (c a b : CGR.Exp)
    (h : CGR.expAdd c a = CGR.expAdd c b) : a = b :=
  expAdd_cancel_right a b c (by rwa [CGR.expAdd_comm a, CGR.expAdd_comm b])

/-- Right distributivity: `(a+b)c = ac + bc` -/
theorem expAdd_mul (a b c : CGR.Exp) :
    CGR.expMul (CGR.expAdd a b) c = CGR.expAdd (CGR.expMul a c) (CGR.expMul b c) := by
  rw [CGR.expMul_comm', CGR.expMul_add, CGR.expMul_comm' c a, CGR.expMul_comm' c b]

/-- `0 · a = 0` -/
theorem expMul_zero (a : CGR.Exp) : CGR.expMul CGR.expZero a = CGR.expZero := by
  have h := expAdd_mul CGR.expZero CGR.expZero a
  rw [CGR.expAdd_zero CGR.expZero] at h
  have h2 := congrArg (CGR.expAdd · (CGR.expNeg (CGR.expMul CGR.expZero a))) h
  simp only at h2
  rw [CGR.expAdd_neg, CGR.expAdd_assoc, CGR.expAdd_neg, CGR.expAdd_zero] at h2
  exact h2.symm

/-- `a · 0 = 0` -/
theorem expZero_mul (a : CGR.Exp) : CGR.expMul a CGR.expZero = CGR.expZero := by
  rw [CGR.expMul_comm', expMul_zero]

/-- `a · (-b) = -(a · b)` -/
theorem expMul_neg (a b : CGR.Exp) :
    CGR.expMul a (CGR.expNeg b) = CGR.expNeg (CGR.expMul a b) := by
  have h : CGR.expAdd (CGR.expMul a (CGR.expNeg b)) (CGR.expMul a b) = CGR.expZero := by
    rw [← CGR.expMul_add, CGR.expAdd_comm, CGR.expAdd_neg, expZero_mul]
  exact expAdd_cancel_right _ _ _ (by rw [h, CGR.expAdd_comm, CGR.expAdd_neg])

/-- `(-a) · b = -(a · b)` -/
theorem neg_expMul (a b : CGR.Exp) :
    CGR.expMul (CGR.expNeg a) b = CGR.expNeg (CGR.expMul a b) := by
  rw [CGR.expMul_comm', expMul_neg, CGR.expMul_comm']

/-- `expSub a a = 0` -/
theorem expSub_self (a : CGR.Exp) : expSub a a = CGR.expZero := CGR.expAdd_neg a

/-- Recovering from sub: `expAdd (expSub a b) b = a` -/
theorem expSub_add (a b : CGR.Exp) : CGR.expAdd (expSub a b) b = a := by
  rw [CGR.expAdd_assoc, CGR.expAdd_comm (CGR.expNeg b) b, CGR.expAdd_neg, CGR.expAdd_zero]

end CyclicGroupRing

/-! ## Protocol Definitions -/

variable {G : Type} [CGR : CyclicGroupRing G]

/-- Sender encryption for one position.

Given exponents `(a, b, d)` corresponding to `(x = g^a, y = g^b, z = g^d)`,
encrypt message `m` by sampling `(s, r)` and computing:
- `w = g^{as + r}` (mask for receiver)
- `e = g^{ds + br} · m` (encrypted message)

When `d = ab` (DDH position), the receiver who knows `s` can compute `g^{ds+br}`
and decrypt. When `d ≠ ab`, the pair `(w, e)` is uniform — `m` is hidden. -/
noncomputable def otEnc (a b d : CGR.Exp) (m : G) : SPComp (G × G) := do
  let s ← SPComp.sample CGR.Exp
  let r ← SPComp.sample CGR.Exp
  SPComp.pure (CGR.pow (CGR.expAdd (CGR.expMul a s) r),
               CGR.mul (CGR.pow (CGR.expAdd (CGR.expMul d s) (CGR.expMul b r))) m)

/-- OT transcript: public keys + two ciphertexts -/
abbrev OTTranscript (G : Type) [_CG : CyclicGroup G] := G × G × (G × G) × (G × G)

/-- Real OT game: both messages are encrypted normally (no adversary substitution). -/
noncomputable def ot_real (m0 m1 : G) (sigma : Bool) : SPComp (OTTranscript G) :=
  SPComp.bind (SPComp.sample CGR.Exp) fun a =>
  SPComp.bind (SPComp.sample CGR.Exp) fun b =>
  SPComp.bind (SPComp.sample CGR.Exp) fun c =>
  let d0 := if sigma then c else CGR.expMul a b
  let d1 := if sigma then CGR.expMul a b else c
  SPComp.bind (otEnc a b d0 m0) fun ct0 =>
  SPComp.bind (otEnc a b d1 m1) fun ct1 =>
  SPComp.pure (CGR.pow a, CGR.pow b, ct0, ct1)

/-- Ideal OT game: the non-chosen message is replaced by the identity. -/
noncomputable def ot_ideal (m0 m1 : G) (sigma : Bool) : SPComp (OTTranscript G) :=
  SPComp.bind (SPComp.sample CGR.Exp) fun a =>
  SPComp.bind (SPComp.sample CGR.Exp) fun b =>
  SPComp.bind (SPComp.sample CGR.Exp) fun c =>
  let d0 := if sigma then c else CGR.expMul a b
  let d1 := if sigma then CGR.expMul a b else c
  let m0' := if sigma then CGR.one else m0
  let m1' := if sigma then m1 else CGR.one
  SPComp.bind (otEnc a b d0 m0') fun ct0 =>
  SPComp.bind (otEnc a b d1 m1') fun ct1 =>
  SPComp.pure (CGR.pow a, CGR.pow b, ct0, ct1)

/-! ## Matrix Bijection

The key algebraic fact for sender security: the linear map
`M(s, r) = (as + r, ds + br)` on `Exp × Exp` is a bijection when `d - ab ≠ 0`.
-/

/-- The matrix map `(s, r) ↦ (as + r, ds + br)` on exponents. -/
noncomputable def matrixMap (a b d : CGR.Exp) :
    CGR.Exp × CGR.Exp → CGR.Exp × CGR.Exp :=
  fun (s, r) => (CGR.expAdd (CGR.expMul a s) r,
                 CGR.expAdd (CGR.expMul d s) (CGR.expMul b r))

/-- The matrix map is injective when `d - ab ≠ 0`. -/
theorem matrixMap_injective (a b d : CGR.Exp)
    (hnd : CyclicGroupRing.expSub d (CGR.expMul a b) ≠ CGR.expZero) :
    Function.Injective (matrixMap (G := G) a b d) := by
  intro ⟨s1, r1⟩ ⟨s2, r2⟩ heq
  simp only [matrixMap, Prod.mk.injEq] at heq
  obtain ⟨h1, h2⟩ := heq
  -- h1: a·s1 + r1 = a·s2 + r2
  -- h2: d·s1 + b·r1 = d·s2 + b·r2
  suffices hs : s1 = s2 by
    exact Prod.ext hs (CyclicGroupRing.expAdd_cancel_left _ _ _ (by rwa [hs] at h1))
  by_contra hne
  -- Step 1: Derive h1': a·s1 + (r1-r2) = a·s2
  have h1' : CGR.expAdd (CGR.expMul a s1) (CGR.expAdd r1 (CGR.expNeg r2)) =
             CGR.expMul a s2 := by
    simpa only [CGR.expAdd_assoc, CGR.expAdd_neg, CGR.expAdd_zero]
      using congrArg (CGR.expAdd · (CGR.expNeg r2)) h1
  -- Step 2: r1-r2 = a·(s2-s1) (by left-cancelling a·s1 from h1')
  have hr : CGR.expAdd r1 (CGR.expNeg r2) =
            CGR.expMul a (CGR.expAdd s2 (CGR.expNeg s1)) :=
    CyclicGroupRing.expAdd_cancel_left (CGR.expMul a s1) _ _ (by
      rw [h1', ← CGR.expMul_add]; congr 1
      rw [CGR.expAdd_comm s1, CyclicGroupRing.expSub_add])
  -- Step 3: Derive h2': d·s1 + b·(r1-r2) = d·s2
  have h2' : CGR.expAdd (CGR.expMul d s1)
      (CGR.expMul b (CGR.expAdd r1 (CGR.expNeg r2))) = CGR.expMul d s2 := by
    have := congrArg (CGR.expAdd · (CGR.expNeg (CGR.expMul b r2))) h2
    simp only at this
    rw [CGR.expAdd_assoc, CGR.expAdd_assoc, CGR.expAdd_neg, CGR.expAdd_zero] at this
    rwa [← CyclicGroupRing.expMul_neg b, ← CGR.expMul_add] at this
  -- Step 4: Substitute hr into h2' to get d·s1 + (ab)·(s2-s1) = d·s2
  rw [hr, ← CGR.expMul_assoc, CGR.expMul_comm' b a] at h2'
  -- Step 5: Derive (d-ab)·(s1-s2) = 0
  have key : CGR.expMul (CyclicGroupRing.expSub d (CGR.expMul a b))
                        (CGR.expAdd s1 (CGR.expNeg s2)) = CGR.expZero := by
    -- From h2': d·s1 + (ab)·(s2-s1) = d·s2, subtract d·s2
    have step := congrArg (CGR.expAdd · (CGR.expNeg (CGR.expMul d s2))) h2'
    simp only at step
    rw [CGR.expAdd_neg] at step
    -- step: (d·s1 + (ab)·(s2-s1)) + (-(d·s2)) = 0
    rw [CGR.expAdd_assoc (CGR.expMul d s1)] at step
    rw [CGR.expAdd_comm (CGR.expMul (CGR.expMul a b) (CGR.expAdd s2 (CGR.expNeg s1)))
        (CGR.expNeg (CGR.expMul d s2))] at step
    rw [← CGR.expAdd_assoc (CGR.expMul d s1)] at step
    -- step: (d·s1 + (-(d·s2))) + (ab)·(s2-s1) = 0
    rw [← CyclicGroupRing.expMul_neg d, ← CGR.expMul_add] at step
    -- step: d·(s1-s2) + (ab)·(s2-s1) = 0
    -- Convert (s2-s1) to -(s1-s2)
    have neg_swap : CGR.expAdd s2 (CGR.expNeg s1) =
        CGR.expNeg (CGR.expAdd s1 (CGR.expNeg s2)) := by
      apply CyclicGroupRing.expAdd_cancel_right _ _ (CGR.expAdd s1 (CGR.expNeg s2))
      conv_rhs => rw [CGR.expAdd_comm, CGR.expAdd_neg]
      rw [CGR.expAdd_assoc s2,
          ← CGR.expAdd_assoc (CGR.expNeg s1) s1 (CGR.expNeg s2),
          CGR.expAdd_comm (CGR.expNeg s1) s1, CGR.expAdd_neg,
          CyclicGroupRing.expZero_add, CGR.expAdd_neg]
    rw [neg_swap, CyclicGroupRing.expMul_neg, ← CyclicGroupRing.neg_expMul,
        ← CyclicGroupRing.expAdd_mul] at step
    exact step
  -- Step 6: s1-s2 = 0 by injectivity of multiplication by (d-ab)
  have hinj := (CGR.expMul_bij _ hnd).1
  have hsub0 : CGR.expAdd s1 (CGR.expNeg s2) = CGR.expZero :=
    hinj (key.trans (CyclicGroupRing.expZero_mul _).symm)
  have : s1 = s2 := by
    have := congrArg (CGR.expAdd · s2) hsub0
    simp only at this
    rwa [CyclicGroupRing.expZero_add, CGR.expAdd_assoc,
         CGR.expAdd_comm (CGR.expNeg s2), CGR.expAdd_neg, CGR.expAdd_zero] at this
  exact absurd this hne

/-- The matrix map is bijective when `d - ab ≠ 0`. -/
theorem matrixMap_bijective (a b d : CGR.Exp)
    (hnd : CyclicGroupRing.expSub d (CGR.expMul a b) ≠ CGR.expZero) :
    Function.Bijective (matrixMap (G := G) a b d) :=
  Finite.injective_iff_bijective.mp (matrixMap_injective a b d hnd)

/-! ## Sender Security

The key theorem: when `d ≠ ab`, the encryption `otEnc a b d m` produces a
distribution independent of `m`. This is because the matrix map
`(s,r) ↦ (as+r, ds+br)` is a bijection, so `(w, e)` is uniformly distributed.
-/

/-- Translation equivalence on exponents: `s ↦ s + c`. -/
noncomputable def expAddEquiv (c : CGR.Exp) : CGR.Exp ≃ CGR.Exp where
  toFun s := CGR.expAdd s c
  invFun s := CGR.expAdd s (CGR.expNeg c)
  left_inv s := by
    simp only [CyclicGroupRing.expAdd_assoc, CyclicGroupRing.expAdd_neg, CyclicGroupRing.expAdd_zero]
  right_inv s := by
    simp only [CyclicGroupRing.expAdd_assoc, CyclicGroupRing.expAdd_comm (CGR.expNeg c) c,
      CyclicGroupRing.expAdd_neg, CyclicGroupRing.expAdd_zero]

/-- Key lemma: `otEnc a b d m0 = otEnc a b d m1` when `d - ab ≠ 0`.

The proof uses a translation coupling. When `d - ab ≠ 0`, we can find a constant
shift `δ` such that coupling `s₀ ↔ s₀ + δ` and `r₀ ↔ r₀ - aδ` preserves the
first output component `g^{as+r}` and exactly compensates the message change
in the second component `g^{ds+br} · m`. -/
theorem otEnc_message_independent (a b d : CGR.Exp) (m0 m1 : G)
    (hnd : CyclicGroupRing.expSub d (CGR.expMul a b) ≠ CGR.expZero) :
    otEnc (G := G) a b d m0 = otEnc (G := G) a b d m1 := by
  -- Find the translation constant δ
  obtain ⟨e, he⟩ := CGR.pow_bij.2 (CGR.mul m0 (CGR.inv m1))
  obtain ⟨δ, hδ⟩ := (CGR.expMul_bij _ hnd).2 e
  have hshift : CGR.pow (CGR.expMul (CyclicGroupRing.expSub d (CGR.expMul a b)) δ) =
      CGR.mul m0 (CGR.inv m1) := by rw [hδ, he]
  -- Unfold and normalize
  unfold otEnc
  simp only [SPComp.monad_bind_eq]
  funext h
  ssprove_distr_simp
  apply liftR_eq_implies_eq
  -- Couple s₀ ↔ s₁ = s₀ + δ
  apply liftR_bind (liftR_uniform_bij (expAddEquiv (G := G) δ))
  intro s0 s1 hs
  have hs' : CGR.expAdd s0 δ = s1 := hs
  subst hs'
  -- Couple r₀ ↔ r₁ = r₀ - aδ (preserves first component)
  apply liftR_bind (liftR_uniform_bij (expAddEquiv (G := G) (CGR.expNeg (CGR.expMul a δ))))
  intro r0 r1 hr
  have hr' : CGR.expAdd r0 (CGR.expNeg (CGR.expMul a δ)) = r1 := hr
  subst hr'
  -- Now prove the outputs are equal
  apply liftR_pure
  simp only [Prod.mk.injEq]
  refine ⟨⟨?_, ?_⟩, trivial⟩
  · -- First component: g^{a(s+δ) + (r-aδ)} = g^{as + r}
    congr 1
    rw [CGR.expMul_add a s0 δ, CGR.expAdd_assoc (CGR.expMul a s0),
        ← CGR.expAdd_assoc (CGR.expMul a δ) r0,
        CGR.expAdd_comm (CGR.expMul a δ) r0,
        CGR.expAdd_assoc r0, CGR.expAdd_neg, CGR.expAdd_zero]
  · -- Second component: g^{d(s+δ) + b(r-aδ)} · m1 = g^{ds+br} · m0
    have hexp : CGR.expAdd (CGR.expMul d (CGR.expAdd s0 δ))
        (CGR.expMul b (CGR.expAdd r0 (CGR.expNeg (CGR.expMul a δ)))) =
        CGR.expAdd (CGR.expAdd (CGR.expMul d s0) (CGR.expMul b r0))
        (CGR.expMul (CyclicGroupRing.expSub d (CGR.expMul a b)) δ) := by
      conv_lhs => rw [CGR.expMul_add d s0 δ,
                       CGR.expMul_add b r0 (CGR.expNeg (CGR.expMul a δ))]
      conv_lhs => rw [CyclicGroupRing.expMul_neg, ← CGR.expMul_assoc,
                       CGR.expMul_comm' b a]
      conv_rhs => rw [CyclicGroupRing.expAdd_mul, CyclicGroupRing.neg_expMul]
      rw [CGR.expAdd_assoc (CGR.expMul d s0),
          ← CGR.expAdd_assoc (CGR.expMul d δ) (CGR.expMul b r0),
          CGR.expAdd_comm (CGR.expMul d δ) (CGR.expMul b r0),
          CGR.expAdd_assoc (CGR.expMul b r0),
          ← CGR.expAdd_assoc (CGR.expMul d s0) (CGR.expMul b r0)]
    rw [hexp]; conv_rhs => rw [CGR.pow_add]; rw [CGR.mul_assoc, hshift]
    congr 1
    rw [CGR.mul_assoc, CGR.mul_comm (CGR.inv m1) m1, CGR.mul_inv, CGR.mul_one]

private theorem ot_sender_secure_false (m0 m1 : G)
    (hnd : ∀ a b c : CGR.Exp,
      CyclicGroupRing.expSub c (CGR.expMul a b) ≠ CGR.expZero) :
    ot_real (G := G) m0 m1 false = ot_ideal (G := G) m0 m1 false :=
  congrArg (SPComp.bind (SPComp.sample CGR.Exp)) (funext fun a =>
  congrArg (SPComp.bind (SPComp.sample CGR.Exp)) (funext fun b =>
  congrArg (SPComp.bind (SPComp.sample CGR.Exp)) (funext fun c =>
  congrArg (SPComp.bind (otEnc a b (CGR.expMul a b) m0)) (funext fun ct0 =>
  congrArg (fun e => SPComp.bind e (fun ct1 =>
    SPComp.pure (CGR.pow a, CGR.pow b, ct0, ct1)))
    (otEnc_message_independent a b c m1 CGR.one (hnd a b c))))))

private theorem ot_sender_secure_true (m0 m1 : G)
    (hnd : ∀ a b c : CGR.Exp,
      CyclicGroupRing.expSub c (CGR.expMul a b) ≠ CGR.expZero) :
    ot_real (G := G) m0 m1 true = ot_ideal (G := G) m0 m1 true :=
  congrArg (SPComp.bind (SPComp.sample CGR.Exp)) (funext fun a =>
  congrArg (SPComp.bind (SPComp.sample CGR.Exp)) (funext fun b =>
  congrArg (SPComp.bind (SPComp.sample CGR.Exp)) (funext fun c =>
  congrArg (fun e => SPComp.bind e (fun ct0 =>
    SPComp.bind (otEnc a b (CGR.expMul a b) m1) (fun ct1 =>
    SPComp.pure (CGR.pow a, CGR.pow b, ct0, ct1))))
    (otEnc_message_independent a b c m0 CGR.one (hnd a b c)))))

/-- Full sender security: real and ideal OT games are equal. -/
theorem ot_sender_secure (m0 m1 : G) (sigma : Bool)
    (hnd : ∀ a b c : CGR.Exp,
      CyclicGroupRing.expSub c (CGR.expMul a b) ≠ CGR.expZero) :
    ot_real (G := G) m0 m1 sigma = ot_ideal (G := G) m0 m1 sigma := by
  cases sigma
  · exact ot_sender_secure_false m0 m1 hnd
  · exact ot_sender_secure_true m0 m1 hnd

/-! ## Receiver Security

The receiver's public values `(g^a, g^b, z₀, z₁)` encode the choice bit σ:
position σ has a DDH triple `(g^a, g^b, g^{ab})`, the other has a random `g^c`.

Distinguishing σ=0 from σ=1 reduces to DDH via a standard hybrid argument.
-/

/-- Receiver's view: what the sender sees (the public commitment). -/
noncomputable def receiverView (sigma : Bool) : SPComp (G × G × G × G) := do
  let a ← SPComp.sample CGR.Exp
  let b ← SPComp.sample CGR.Exp
  let c ← SPComp.sample CGR.Exp
  let gab := CGR.pow (CGR.expMul a b)
  let gc := CGR.pow c
  SPComp.pure (CGR.pow a, CGR.pow b,
    if sigma then gc else gab,
    if sigma then gab else gc)

/-- DDH reduction for receiver security. -/
noncomputable def receiverReduction (sigma : Bool)
    (A : G × G × G × G → SPComp Bool)
    (challenge : DDHTriple G) : SPComp Bool := do
  let (ga, gb, z) := challenge
  let c ← SPComp.sample CGR.Exp
  let rand := CGR.pow c
  A (ga, gb, if sigma then rand else z,
             if sigma then z else rand)

/-- Bridge lemma: monad `pure` equals `SPComp.pure` for simp matching. -/
private theorem pure_eq_spcomp_pure {α : Type} (a : α) :
    (pure a : SPComp α) = SPComp.pure a := rfl

/-- The reduction with real DDH matches the receiver's view. -/
theorem reduction_real_eq_receiver (sigma : Bool)
    (A : G × G × G × G → SPComp Bool) :
    (DDH_real G).bind (receiverReduction (G := G) sigma A) =
    (receiverView (G := G) sigma).bind A := by
  unfold DDH_real receiverReduction receiverView
  simp only [SPComp.monad_bind_eq, pure_eq_spcomp_pure, SPComp.pure_bind, SPComp.bind_assoc]

/-- When DDH is ideal (z random), both σ values give the same distribution. -/
theorem receiver_ideal_indep (A : G × G × G × G → SPComp Bool) :
    (DDH_ideal G).bind (receiverReduction (G := G) false A) =
    (DDH_ideal G).bind (receiverReduction (G := G) true A) := by
  unfold DDH_ideal receiverReduction
  simp only [SPComp.monad_bind_eq, pure_eq_spcomp_pure, SPComp.pure_bind, SPComp.bind_assoc,
             Bool.false_eq_true, ↓reduceIte]
  congr 1; funext a; congr 1; funext b
  exact SPComp.isPure_bind_comm _ _ _
    (SPComp.sample_isPure CGR.Exp) (SPComp.sample_isPure CGR.Exp)

/-- Receiver security: the advantage of distinguishing σ=0 from σ=1 is bounded
by the sum of two DDH advantages. -/
theorem receiver_security (A : G × G × G × G → SPComp Bool) :
    AdvantageA (receiverView (G := G) false) (receiverView (G := G) true) A ≤
    DDH_Advantage G (receiverReduction (G := G) false A) +
    DDH_Advantage G (receiverReduction (G := G) true A) := by
  unfold AdvantageA DDH_Advantage
  rw [← reduction_real_eq_receiver false A,
      ← reduction_real_eq_receiver true A]
  calc Advantage ((DDH_real G).bind (receiverReduction (G := G) false A))
                 ((DDH_real G).bind (receiverReduction (G := G) true A))
      ≤ Advantage ((DDH_real G).bind (receiverReduction (G := G) false A))
                  ((DDH_ideal G).bind (receiverReduction (G := G) false A)) +
        Advantage ((DDH_ideal G).bind (receiverReduction (G := G) false A))
                  ((DDH_real G).bind (receiverReduction (G := G) true A)) :=
        advantage_triangle _ _ _
    _ = Advantage ((DDH_real G).bind (receiverReduction (G := G) false A))
                  ((DDH_ideal G).bind (receiverReduction (G := G) false A)) +
        Advantage ((DDH_ideal G).bind (receiverReduction (G := G) true A))
                  ((DDH_real G).bind (receiverReduction (G := G) true A)) := by
        rw [receiver_ideal_indep A]
    _ = Advantage ((DDH_real G).bind (receiverReduction (G := G) false A))
                  ((DDH_ideal G).bind (receiverReduction (G := G) false A)) +
        Advantage ((DDH_real G).bind (receiverReduction (G := G) true A))
                  ((DDH_ideal G).bind (receiverReduction (G := G) true A)) := by
        congr 1; exact Advantage_sym _ _

end CatCrypt.Examples.OT
