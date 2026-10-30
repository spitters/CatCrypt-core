/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.ElGamalDDH

/-!
# ElGamal IND-CPA with a key-dependent message, reduced to DDH

The IND-CPA game of ElGamal over a cyclic group in which the challenge message is a function
`m : G → G` of the public key: the challenger samples a key pair `(sk, pk)` and returns `pk`
and an encryption of `m pk`. The advantage of an adversary distinguishing the messages `m₀`
and `m₁` is at most the sum of the DDH advantages of two explicit reductions
`ReductionKeyMsg m₀ A` and `ReductionKeyMsg m₁ A`.

A message that does not depend on the key is the case `m := fun _ => m`, the game
`ElGamal_INDCPA_real` of `CatCryptCore.Examples.ElGamalDDH`.

## Main definitions

* `ElGamal_INDCPA_keyMsg m` — key generation, then the public key and an encryption of `m pk`.
* `ReductionKeyMsg m A` — the DDH adversary: on `(g^a, g^b, z)` it runs `A` on the public key
  `g^a` and the ciphertext `(g^b, m (g^a) · z)`.

## Main results

* `elgamal_indcpa_keyMsg_security` — the IND-CPA advantage is at most
  `DDH_Advantage (ReductionKeyMsg m₀ A) + DDH_Advantage (ReductionKeyMsg m₁ A)`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCryptCore.Examples.ElGamalDDH

open CatCrypt.Core
open CatCrypt.Crypto
open CatCrypt.Prob
open CatCrypt.Relational
open CatCryptCore.Examples.CyclicGroupDDH
open scoped ENNReal

variable (G : Type) [CG : CyclicGroup G]

/-- The IND-CPA game of ElGamal with a key-dependent message `m`: sample a key pair, return the
public key `pk` and an encryption of `m pk`. -/
noncomputable def ElGamal_INDCPA_keyMsg (m : G → G) :
    SPComp (G × ElGamalScheme.Ciphertext G) := do
  let (_, pk) ← ElGamalScheme.keyGen G
  let ct ← ElGamalScheme.encrypt G pk (m pk)
  return (pk, ct)

/-- The reduction from key-dependent-message IND-CPA to DDH: on the challenge `(g^a, g^b, z)`,
run `A` on the public key `g^a` and the ciphertext `(g^b, m (g^a) · z)`. -/
noncomputable def ReductionKeyMsg (m : G → G) (A : G × ElGamalScheme.Ciphertext G → SPComp Bool)
    (challenge : DDHTriple G) : SPComp Bool := do
  let (ga, gb, z) := challenge
  A (ga, (gb, CG.mul (m ga) z))

variable {G}

/-- The key-dependent-message game followed by `A`, as explicit samples. -/
theorem keyMsg_bind_eq (m : G → G) (A : G × ElGamalScheme.Ciphertext G → SPComp Bool) :
    (ElGamal_INDCPA_keyMsg G m).bind A =
      SPComp.bind (SPComp.sample CG.Exp) fun a =>
        SPComp.bind (SPComp.sample CG.Exp) fun b =>
          A (CG.pow a, (CG.pow b, CG.mul (m (CG.pow a)) (CG.pow (CG.expMul a b)))) := by
  unfold ElGamal_INDCPA_keyMsg ElGamalScheme.keyGen ElGamalScheme.encrypt
  simp only [SPComp.monad_bind_eq, SPComp.monad_pure_eq, SPComp.bind_assoc, SPComp.pure_bind,
    CyclicGroup.elemPow_pow]

/-- The real DDH game followed by `ReductionKeyMsg m A` is the key-dependent-message game
followed by `A`. -/
theorem reductionKeyMsg_real_eq (m : G → G) (A : G × ElGamalScheme.Ciphertext G → SPComp Bool) :
    (DDH_real G).bind (ReductionKeyMsg G m A) = (ElGamal_INDCPA_keyMsg G m).bind A := by
  rw [keyMsg_bind_eq]
  unfold DDH_real ReductionKeyMsg
  simp only [SPComp.monad_bind_eq, SPComp.monad_pure_eq, SPComp.bind_assoc, SPComp.pure_bind]

/-- The ideal DDH game followed by `ReductionKeyMsg m A` does not depend on `m`: for each public
key, `c ↦ m (g^a) · g^c` is a bijection onto `G`. -/
theorem reductionKeyMsg_ideal_indep (m₀ m₁ : G → G)
    (A : G × ElGamalScheme.Ciphertext G → SPComp Bool) :
    (DDH_ideal G).bind (ReductionKeyMsg G m₀ A) = (DDH_ideal G).bind (ReductionKeyMsg G m₁ A) := by
  have h : ∀ m : G → G, (DDH_ideal G).bind (ReductionKeyMsg G m A) =
      SPComp.bind (SPComp.sample CG.Exp) fun a =>
        SPComp.bind (SPComp.sample CG.Exp) fun b =>
          SPComp.bind (SPComp.sample G) fun z => A (CG.pow a, (CG.pow b, z)) := by
    intro m
    unfold DDH_ideal ReductionKeyMsg
    simp only [SPComp.monad_bind_eq, SPComp.monad_pure_eq, SPComp.bind_assoc, SPComp.pure_bind]
    refine congrArg _ (funext fun a => congrArg _ (funext fun b => ?_))
    exact SPComp.sample_bind_equiv (mulPowEquiv G (m (CG.pow a)))
      (fun z => A (CG.pow a, (CG.pow b, z)))
  rw [h m₀, h m₁]

/-- **ElGamal IND-CPA with key-dependent messages reduces to DDH.** For messages `m₀ m₁ : G → G`
of the public key and every adversary `A`, the advantage is at most the sum of the DDH
advantages of the reductions `ReductionKeyMsg m₀ A` and `ReductionKeyMsg m₁ A`. -/
theorem elgamal_indcpa_keyMsg_security (m₀ m₁ : G → G)
    (A : G × ElGamalScheme.Ciphertext G → SPComp Bool) :
    AdvantageA (ElGamal_INDCPA_keyMsg G m₀) (ElGamal_INDCPA_keyMsg G m₁) A ≤
      DDH_Advantage G (ReductionKeyMsg G m₀ A) + DDH_Advantage G (ReductionKeyMsg G m₁ A) := by
  unfold DDH_Advantage AdvantageA
  rw [← reductionKeyMsg_real_eq, ← reductionKeyMsg_real_eq]
  calc Advantage ((DDH_real G).bind (ReductionKeyMsg G m₀ A))
        ((DDH_real G).bind (ReductionKeyMsg G m₁ A))
      ≤ Advantage ((DDH_real G).bind (ReductionKeyMsg G m₀ A))
          ((DDH_ideal G).bind (ReductionKeyMsg G m₀ A)) +
        Advantage ((DDH_ideal G).bind (ReductionKeyMsg G m₀ A))
          ((DDH_real G).bind (ReductionKeyMsg G m₁ A)) := advantage_triangle _ _ _
    _ = _ := by
        rw [reductionKeyMsg_ideal_indep m₀ m₁ A, advantage_symm
          ((DDH_ideal G).bind (ReductionKeyMsg G m₁ A))]

end CatCryptCore.Examples.ElGamalDDH
