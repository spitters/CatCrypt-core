/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Examples.CyclicGroupDDH
import CatCryptCore.Examples.INDCPA
import CatCryptCore.Crypto.Advantage
import CatCryptCore.Prob.XorBij
import CatCryptCore.Relational.Rules
import CatCryptCore.Tactics.Basic

/-!
# ElGamal Encryption and DDH Security

The ElGamal public-key encryption scheme over a cyclic group with explicit
exponents, and its IND-CPA security under the Decisional Diffie–Hellman (DDH)
assumption.

The cyclic-group interface `CyclicGroup` and the DDH games (`DDH_real`,
`DDH_ideal`, `DDH_Advantage`) are reused from `CatCryptCore.Examples.CyclicGroupDDH`.

## Overview

ElGamal encryption operates in a cyclic group `G` of prime order with generator `g`:

* **Key generation**: sample random `x` from `Z_q`, output `(pk = g^x, sk = x)`.
* **Encryption**: for message `m` and randomness `r`, output `(c₁ = g^r, c₂ = pk^r · m)`.
* **Decryption**: given `(c₁, c₂)` and `sk = x`, compute `c₂ · c₁^(-x) = m`.

## Security

ElGamal is IND-CPA secure under the DDH assumption:

- **DDH problem**: distinguish `(g^a, g^b, g^(ab))` from `(g^a, g^b, g^c)` for random `a, b, c`.
- **Reduction**: an IND-CPA adversary for ElGamal yields a DDH distinguisher.

The proof uses a game-based approach: define the ElGamal scheme, build the reduction
from IND-CPA to DDH, and prove the security bound via message-independence of the ideal
game (a bijection-coupling argument).

## References

* [Taher ElGamal, *A Public Key Cryptosystem and a Signature Scheme Based on Discrete
  Logarithms*, 1985]
* [Boneh & Shoup, *A Graduate Course in Applied Cryptography*, Chapter 11]
* [SSProve: theories/Crypt/examples/PKE/ElGamal.v]
-/

set_option autoImplicit false

namespace CatCryptCore.Examples.ElGamalDDH

open CatCrypt.Core
open CatCrypt.Crypto
open CatCrypt.Prob
open CatCrypt.Relational
open CatCryptCore.Examples.CyclicGroupDDH
open CatCryptCore.Examples.CyclicGroupDDH.CyclicGroup
open scoped ENNReal

/-! ## Decryption Correctness Identity -/

/-- Key algebraic identity underlying decryption: `c₂ · c₁^(-sk)` recovers the
message when `c₁ = g^r`, `c₂ = m · pk^r`, `pk = g^sk`. That is
`m · g^(sk·r) · g^(-sk·r) = m`. -/
theorem decrypt_correct {G : Type} [CG : CyclicGroup G] (m : G) (sk r : CG.Exp) :
    CG.mul (CG.mul m (CG.pow (CG.expMul sk r))) (CG.inv (CG.pow (CG.expMul sk r))) = m := by
  rw [CG.mul_assoc, CG.mul_inv, CG.mul_one]

/-! ## ElGamal Encryption Scheme -/

/-- ElGamal encryption scheme for a cyclic group `G`. The scheme is determined by
the group, so the structure carries no configuration. -/
structure ElGamalScheme (G : Type) [CG : CyclicGroup G] where
  /-- The scheme is determined by the group. -/
  mk ::

namespace ElGamalScheme

variable {G : Type} [CG : CyclicGroup G]

/-- Secret key type: an exponent. -/
abbrev SecretKey (G : Type) [CG : CyclicGroup G] := CG.Exp

/-- Public key type: a group element. -/
abbrev PublicKey (G : Type) [_CG : CyclicGroup G] := G

/-- Message type: a group element. -/
abbrev Message (G : Type) [_CG : CyclicGroup G] := G

/-- Ciphertext type: a pair of group elements `(c₁, c₂)`. -/
abbrev Ciphertext (G : Type) [_CG : CyclicGroup G] := G × G

/-- Key generation: sample random `x`, output `(sk = x, pk = g^x)`. -/
noncomputable def keyGen (G : Type) [CG : CyclicGroup G] : SPComp (SecretKey G × PublicKey G) := do
  let sk ← SPComp.sample CG.Exp
  return (sk, CG.pow sk)

/-- Encryption: `Enc(pk, m) = (g^r, m · pk^r)` for random `r`. -/
noncomputable def encrypt (G : Type) [CG : CyclicGroup G]
    (pk : PublicKey G) (m : Message G) : SPComp (Ciphertext G) := do
  let r ← SPComp.sample CG.Exp
  let c1 := CG.pow r
  let c2 := CG.mul m (CyclicGroup.elemPow pk r)
  return (c1, c2)

/-- Decryption: `Dec(sk, (c₁, c₂)) = c₂ · c₁^(-sk)`. -/
noncomputable def decrypt (G : Type) [CG : CyclicGroup G]
    (sk : SecretKey G) (ct : Ciphertext G) : SPComp (Option (Message G)) := do
  let (c1, c2) := ct
  let c1_neg_sk := CG.inv (CyclicGroup.elemPow c1 sk)
  return some (CG.mul c2 c1_neg_sk)

/-- ElGamal presented as an `EncScheme`. -/
noncomputable def toEncScheme (G : Type) [CG : CyclicGroup G] : EncScheme where
  Key := SecretKey G × PublicKey G
  Plaintext := Message G
  Ciphertext := Ciphertext G
  finKey := inferInstance
  neKey := inferInstance
  finCt := inferInstance
  neCt := inferInstance
  keyGen := keyGen G
  encrypt := fun (_, pk) m => encrypt G pk m
  decrypt := fun (sk, _) ct => decrypt G sk ct

end ElGamalScheme

/-! ## IND-CPA Security Game for ElGamal

The IND-CPA game for public-key encryption: the challenger generates `(pk, sk)`,
the adversary receives `pk`, chooses two messages `m₀`, `m₁`, and tries to guess
which one was encrypted. -/

/-- IND-CPA real game for ElGamal: encrypt `m₀`. -/
noncomputable def ElGamal_INDCPA_real (G : Type) [CG : CyclicGroup G]
    (m0 _m1 : G) : SPComp (G × ElGamalScheme.Ciphertext G) := do
  let (_, pk) ← ElGamalScheme.keyGen G
  let ct ← ElGamalScheme.encrypt G pk m0
  return (pk, ct)

/-- IND-CPA ideal game for ElGamal: encrypt `m₁`. -/
noncomputable def ElGamal_INDCPA_ideal (G : Type) [CG : CyclicGroup G]
    (_m0 m1 : G) : SPComp (G × ElGamalScheme.Ciphertext G) := do
  let (_, pk) ← ElGamalScheme.keyGen G
  let ct ← ElGamalScheme.encrypt G pk m1
  return (pk, ct)

/-- IND-CPA advantage for ElGamal. -/
noncomputable def ElGamal_INDCPA_Advantage (G : Type) [CG : CyclicGroup G]
    (m0 m1 : G) (A : G × ElGamalScheme.Ciphertext G → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (ElGamal_INDCPA_real G m0 m1) (ElGamal_INDCPA_ideal G m0 m1) A

/-! ## Security Reduction: IND-CPA to DDH

Given a DDH challenge `(g^a, g^b, z)`, set `pk = g^a` and answer the encryption
query for message `m` with `(g^b, m · z)`. If `z = g^(ab)` this is a valid ElGamal
ciphertext; if `z = g^c` it masks the message with an independent element. -/

/-- The reduction from IND-CPA to DDH: given an IND-CPA adversary `A`, use the DDH
challenge `(g^a, g^b, z)` to simulate the IND-CPA game with `pk = g^a` and
`ct = (g^b, m · z)`. -/
noncomputable def Reduction (G : Type) [CG : CyclicGroup G]
    (m : G) (A : G × ElGamalScheme.Ciphertext G → SPComp Bool)
    (challenge : DDHTriple G) : SPComp Bool := do
  let (ga, gb, z) := challenge
  let pk := ga
  let ct : ElGamalScheme.Ciphertext G := (gb, CG.mul m z)
  A (pk, ct)

/-! ## Main Security Theorem -/

/-- Simplify `keyGen` bind. -/
private theorem keyGen_bind_eq (G : Type) [CG : CyclicGroup G] (m : G) :
    ElGamal_INDCPA_real G m m =
    SPComp.bind (SPComp.sample CG.Exp) (fun sk =>
      SPComp.bind (ElGamalScheme.encrypt G (CG.pow sk) m) (fun ct =>
        SPComp.pure (CG.pow sk, ct))) := by
  unfold ElGamal_INDCPA_real ElGamalScheme.keyGen
  simp only [SPComp.monad_bind_eq, SPComp.bind_assoc]
  congr 1
  funext a
  show ((SPComp.pure (a, CG.pow a)).bind fun __discr ↦
      (ElGamalScheme.encrypt G __discr.2 m).bind fun ct ↦ SPComp.pure (__discr.2, ct)) =
    (ElGamalScheme.encrypt G (CG.pow a) m).bind fun ct ↦ SPComp.pure (CG.pow a, ct)
  rw [SPComp.pure_bind]

/-- Simplify `encrypt`. -/
private theorem encrypt_eq (G : Type) [CG : CyclicGroup G] (m : G) (pk : G) :
    ElGamalScheme.encrypt G pk m =
    SPComp.bind (SPComp.sample CG.Exp) (fun r =>
      SPComp.pure (CG.pow r, CG.mul m (CyclicGroup.elemPow pk r))) := by
  unfold ElGamalScheme.encrypt
  simp only [SPComp.monad_bind_eq]
  rfl

/-- Fully simplified form of `ElGamal_INDCPA_real`. -/
private theorem ElGamal_INDCPA_real_simplified (G : Type) [CG : CyclicGroup G] (m : G) :
    ElGamal_INDCPA_real G m m = (do
      let sk ← SPComp.sample CG.Exp
      let r ← SPComp.sample CG.Exp
      SPComp.pure (CG.pow sk, (CG.pow r, CG.mul m (CG.pow (CG.expMul sk r))))) := by
  rw [keyGen_bind_eq]
  simp only [SPComp.monad_bind_eq]
  congr 1
  funext sk
  rw [encrypt_eq]
  simp only [SPComp.bind_assoc, SPComp.pure_bind]
  congr 1
  funext r
  rw [CyclicGroup.elemPow_pow]

/-- Simplify the LHS of the reduction to explicit samples and application. -/
private theorem reduction_real_lhs_eq (G : Type) [CG : CyclicGroup G] (m : G)
    (A : G × ElGamalScheme.Ciphertext G → SPComp Bool) :
    (DDH_real G).bind (Reduction G m A) =
    SPComp.bind (SPComp.sample CG.Exp) (fun a =>
      SPComp.bind (SPComp.sample CG.Exp) (fun b =>
        A (CG.pow a, (CG.pow b, CG.mul m (CG.pow (CG.expMul a b)))))) := by
  unfold DDH_real Reduction
  simp only [SPComp.monad_bind_eq, SPComp.bind_assoc]
  congr 1
  funext a
  congr 1
  funext b
  show (SPComp.pure (CG.pow a, CG.pow b, CG.pow (CG.expMul a b))).bind (fun challenge =>
      A (challenge.1, challenge.2.1, CG.mul m challenge.2.2)) =
    A (CG.pow a, (CG.pow b, CG.mul m (CG.pow (CG.expMul a b))))
  rw [SPComp.pure_bind]

/-- Simplify the RHS of the reduction to explicit samples and application. -/
private theorem reduction_real_rhs_eq (G : Type) [CG : CyclicGroup G] (m : G)
    (A : G × ElGamalScheme.Ciphertext G → SPComp Bool) :
    (ElGamal_INDCPA_real G m m).bind A =
    SPComp.bind (SPComp.sample CG.Exp) (fun a =>
      SPComp.bind (SPComp.sample CG.Exp) (fun b =>
        A (CG.pow a, (CG.pow b, CG.mul m (CG.pow (CG.expMul a b)))))) := by
  rw [ElGamal_INDCPA_real_simplified]
  simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]

/-- The DDH real game with the reduction equals the IND-CPA real game with the
adversary. -/
theorem reduction_real_eq_indcpa_real (G : Type) [CG : CyclicGroup G] (m : G)
    (A : G × ElGamalScheme.Ciphertext G → SPComp Bool) :
    (DDH_real G).bind (Reduction G m A) =
    (ElGamal_INDCPA_real G m m).bind A := by
  rw [reduction_real_lhs_eq, reduction_real_rhs_eq]

/-- When `z = g^c` for random `c`, the ciphertext is independent of the message:
for any messages `m₀`, `m₁`, the DDH ideal game composed with the reduction gives
the same distribution. The map `m · g^c` is a bijection for fixed `m`, so `m · g^c`
is uniform, and the two games are coupled by the induced exponent bijection. -/
theorem reduction_ideal_indep_message (G : Type) [CG : CyclicGroup G] (m0 m1 : G)
    (A : G × ElGamalScheme.Ciphertext G → SPComp Bool) :
    (DDH_ideal G).bind (Reduction G m0 A) =
    (DDH_ideal G).bind (Reduction G m1 A) := by
  have ddh_red_eq : ∀ (m : G),
      (DDH_ideal G).bind (Reduction G m A) =
      (SPComp.sample CG.Exp).bind (fun a =>
        (SPComp.sample CG.Exp).bind (fun b =>
          (SPComp.sample CG.Exp).bind (fun c =>
            A (CG.pow a, (CG.pow b, CG.mul m (CG.pow c)))))) := by
    intro m
    unfold DDH_ideal Reduction
    simp only [SPComp.monad_bind_eq, SPComp.bind_assoc]
    apply congrArg; funext a
    apply congrArg; funext b
    apply congrArg; funext c
    exact SPComp.pure_bind (CG.pow a, CG.pow b, CG.pow c)
      (fun challenge => A (challenge.1, challenge.2.1, CG.mul m challenge.2.2))
  rw [ddh_red_eq, ddh_red_eq]
  funext h
  ssprove_distr_simp
  apply liftR_eq_implies_eq
  apply liftR_bind (liftR_refl _)
  intro a a' haa'; simp only at haa'; rw [haa']
  apply liftR_bind (liftR_refl _)
  intro b b' hbb'; simp only at hbb'; rw [hbb']
  have mul_bij : ∀ (m : G), Function.Bijective (fun b => CG.mul m (CG.pow b)) := by
    intro m
    constructor
    · intro b1 b2 heq
      have hmul : ∀ x, CG.mul (CG.inv m) (CG.mul m x) = x := fun x => by
        rw [← CG.mul_assoc, CG.mul_comm (CG.inv m) m, CG.mul_inv, CG.mul_comm, CG.mul_one]
      have hp : CG.pow b1 = CG.pow b2 := by
        calc CG.pow b1 = CG.mul (CG.inv m) (CG.mul m (CG.pow b1)) := (hmul _).symm
          _ = CG.mul (CG.inv m) (CG.mul m (CG.pow b2)) := by simp only at heq; rw [heq]
          _ = CG.pow b2 := hmul _
      exact CG.pow_bij.1 hp
    · intro y
      obtain ⟨x, hx⟩ := CG.pow_bij.2 (CG.mul (CG.inv m) y)
      use x
      calc CG.mul m (CG.pow x) = CG.mul m (CG.mul (CG.inv m) y) := by rw [hx]
        _ = CG.mul (CG.mul m (CG.inv m)) y := by rw [CG.mul_assoc]
        _ = CG.mul CG.one y := by rw [CG.mul_inv]
        _ = y := by rw [CG.mul_comm, CG.mul_one]
  let msgBij : CG.Exp ≃ CG.Exp :=
    (Equiv.ofBijective (fun b => CG.mul m0 (CG.pow b)) (mul_bij m0)).trans
    (Equiv.ofBijective (fun b => CG.mul m1 (CG.pow b)) (mul_bij m1)).symm
  have hc := liftR_uniform_bij msgBij
  apply liftR_bind hc
  intro c c' hcc'
  rw [← hcc']
  have heq : CG.mul m0 (CG.pow c) = CG.mul m1 (CG.pow (msgBij c)) := by
    simp only [msgBij, Equiv.trans_apply]
    let e1 := Equiv.ofBijective (fun b => CG.mul m1 (CG.pow b)) (mul_bij m1)
    let e0 := Equiv.ofBijective (fun b => CG.mul m0 (CG.pow b)) (mul_bij m0)
    have h1 : CG.mul m1 (CG.pow (e1.symm ((e0 c)))) = e1 (e1.symm (e0 c)) := rfl
    have h2 : e1 (e1.symm (e0 c)) = e0 c := e1.apply_symm_apply (e0 c)
    have h3 : e0 c = CG.mul m0 (CG.pow c) := rfl
    simp only [e1, e0] at h1 h2 h3
    rw [h1, h2, h3]
  conv_lhs => rw [heq]
  exact liftR_refl _

/-- `ElGamal_INDCPA_real` ignores the second message argument. -/
private theorem INDCPA_real_ignores_m1 (G : Type) [CG : CyclicGroup G] (m0 m1 m1' : G) :
    ElGamal_INDCPA_real G m0 m1 = ElGamal_INDCPA_real G m0 m1' := by
  unfold ElGamal_INDCPA_real; rfl

/-- `ElGamal_INDCPA_ideal` equals `ElGamal_INDCPA_real` with the second message. -/
private theorem INDCPA_ideal_eq_real_m1 (G : Type) [CG : CyclicGroup G] (m0 m1 : G) :
    ElGamal_INDCPA_ideal G m0 m1 = ElGamal_INDCPA_real G m1 m1 := by
  unfold ElGamal_INDCPA_ideal ElGamal_INDCPA_real; rfl

/-- ElGamal IND-CPA security reduces to DDH: for any adversary `A` and messages
`m₀`, `m₁`, the IND-CPA advantage is bounded by the sum of the DDH advantages of
the reductions using `m₀` and `m₁`.

The proof hops through: IND-CPA real (encrypt `m₀`) = DDH real reduction with `m₀`;
DDH ideal reduction with `m₀` = DDH ideal reduction with `m₁` (message
independence); DDH real reduction with `m₁` = IND-CPA ideal (encrypt `m₁`). -/
theorem elgamal_indcpa_security (G : Type) [CG : CyclicGroup G]
    (m0 m1 : G) (A : G × ElGamalScheme.Ciphertext G → SPComp Bool) :
    ElGamal_INDCPA_Advantage G m0 m1 A ≤
    DDH_Advantage G (Reduction G m0 A) + DDH_Advantage G (Reduction G m1 A) := by
  unfold ElGamal_INDCPA_Advantage DDH_Advantage AdvantageA
  have h_real_eq : ElGamal_INDCPA_real G m0 m1 = ElGamal_INDCPA_real G m0 m0 :=
    INDCPA_real_ignores_m1 G m0 m1 m0
  have h_ideal_eq : ElGamal_INDCPA_ideal G m0 m1 = ElGamal_INDCPA_real G m1 m1 :=
    INDCPA_ideal_eq_real_m1 G m0 m1
  have h_red_m0 : (DDH_real G).bind (Reduction G m0 A) = (ElGamal_INDCPA_real G m0 m0).bind A :=
    reduction_real_eq_indcpa_real G m0 A
  have h_red_m1 : (DDH_real G).bind (Reduction G m1 A) = (ElGamal_INDCPA_real G m1 m1).bind A :=
    reduction_real_eq_indcpa_real G m1 A
  have h_ideal_indep : (DDH_ideal G).bind (Reduction G m0 A) = (DDH_ideal G).bind (Reduction G m1 A) :=
    reduction_ideal_indep_message G m0 m1 A
  rw [h_real_eq, h_ideal_eq, ← h_red_m0, ← h_red_m1]
  have htri := advantage_triangle
    ((DDH_real G).bind (Reduction G m0 A))
    ((DDH_ideal G).bind (Reduction G m0 A))
    ((DDH_real G).bind (Reduction G m1 A))
  calc Advantage ((DDH_real G).bind (Reduction G m0 A)) ((DDH_real G).bind (Reduction G m1 A))
      ≤ Advantage ((DDH_real G).bind (Reduction G m0 A)) ((DDH_ideal G).bind (Reduction G m0 A)) +
        Advantage ((DDH_ideal G).bind (Reduction G m0 A)) ((DDH_real G).bind (Reduction G m1 A)) := htri
    _ = Advantage ((DDH_real G).bind (Reduction G m0 A)) ((DDH_ideal G).bind (Reduction G m0 A)) +
        Advantage ((DDH_ideal G).bind (Reduction G m1 A)) ((DDH_real G).bind (Reduction G m1 A)) := by
        rw [h_ideal_indep]
    _ = Advantage ((DDH_real G).bind (Reduction G m0 A)) ((DDH_ideal G).bind (Reduction G m0 A)) +
        Advantage ((DDH_real G).bind (Reduction G m1 A)) ((DDH_ideal G).bind (Reduction G m1 A)) := by
        congr 1
        unfold Advantage
        rw [max_comm]

/-! ## Correctness of ElGamal -/

/-- ElGamal correctness: decryption recovers the original message. For secret key
`sk` and message `m`, encrypting with `c₁ = g^r` and `c₂ = m · g^(sk·r)` and then
decrypting via `c₂ · (g^(sk·r))⁻¹` returns `m`. -/
theorem elgamal_correct (G : Type) [CG : CyclicGroup G] :
    ∀ (sk : CG.Exp) (m : G),
    let _pk := CG.pow sk
    ∀ (r : CG.Exp),
    let _c1 := CG.pow r
    let c2 := CG.mul m (CG.pow (CG.expMul sk r))
    let decrypted := CG.mul c2 (CG.inv (CG.pow (CG.expMul sk r)))
    decrypted = m := by
  intro sk m _pk r _c1 c2 decrypted
  simp only [c2, decrypted]
  rw [CG.mul_assoc, CG.mul_inv, CG.mul_one]

/-! ## Bijection Lemmas for the Security Proof -/

/-- `g^(-)` is a bijection from `Exp` to `G`. -/
theorem pow_bijective (G : Type) [CG : CyclicGroup G] :
    Function.Bijective CG.pow := CG.pow_bij

/-- For any `m : G`, the map `b ↦ m · g^b` is a bijection: multiplication by `m`
is a bijection and `g^b` is a bijection. This couples `m₀ · g^c` and `m₁ · g^c'`
to the same distribution when `c` and `c'` are coupled. -/
theorem mul_pow_bijective (G : Type) [CG : CyclicGroup G] (m : G) :
    Function.Bijective (fun b => CG.mul m (CG.pow b)) := by
  constructor
  · intro b1 b2 heq
    have hmul : ∀ x, CG.mul (CG.inv m) (CG.mul m x) = x := by
      intro x
      rw [← CG.mul_assoc, CG.mul_comm (CG.inv m) m, CG.mul_inv, CG.mul_comm, CG.mul_one]
    have h : CG.pow b1 = CG.pow b2 := by
      calc CG.pow b1 = CG.mul (CG.inv m) (CG.mul m (CG.pow b1)) := (hmul _).symm
        _ = CG.mul (CG.inv m) (CG.mul m (CG.pow b2)) := by
            simp only at heq
            rw [heq]
        _ = CG.pow b2 := hmul _
    exact CG.pow_bij.1 h
  · intro y
    obtain ⟨x, hx⟩ := CG.pow_bij.2 (CG.mul (CG.inv m) y)
    use x
    calc CG.mul m (CG.pow x) = CG.mul m (CG.mul (CG.inv m) y) := by rw [hx]
      _ = CG.mul (CG.mul m (CG.inv m)) y := by rw [CG.mul_assoc]
      _ = CG.mul CG.one y := by rw [CG.mul_inv]
      _ = y := by rw [CG.mul_comm, CG.mul_one]

/-- Equivalence from `Exp` to `G` via `pow`, for coupling arguments. -/
noncomputable def powEquiv (G : Type) [CG : CyclicGroup G] : CG.Exp ≃ G :=
  Equiv.ofBijective CG.pow CG.pow_bij

/-- Equivalence from `Exp` to `G` via `b ↦ m · g^b`, for coupling arguments. -/
noncomputable def mulPowEquiv (G : Type) [CG : CyclicGroup G] (m : G) : CG.Exp ≃ G :=
  Equiv.ofBijective (fun b => CG.mul m (CG.pow b)) (mul_pow_bijective G m)

end CatCryptCore.Examples.ElGamalDDH
