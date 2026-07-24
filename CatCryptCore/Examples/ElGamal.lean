/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.SecurityDefs
import CatCryptCore.Crypto.Assumptions.DDH
import CatCryptCore.Crypto.PairingGroup
import CatCryptCore.Tactics

/-!
# ElGamal Public-Key Encryption: IND-CPA Security from DDH

ElGamal encryption over an abstract prime-order group, and its reduction to the
Decisional Diffie–Hellman assumption. Following Rosulek, *The Joy of Cryptography*
(ElGamal / DDH).

We work in the group `P.G₁` of a `PairingGroup P` — an abstract cyclic group of
prime order `P.p` with generator `g₁` and `ZMod P.p`-exponentiation `x ^ᵍ a`. No
concrete curve is used.

## The scheme

* Secret key `sk : ZMod p`, public key `pk = g₁ ^ᵍ sk`.
* `Enc(sk, m)` samples `r ← ZMod p` and outputs `(g₁ ^ᵍ r, (g₁ ^ᵍ sk) ^ᵍ r · m)`.
* `Dec(sk, (c₁, c₂)) = c₂ · (c₁ ^ᵍ sk)⁻¹`.

Messages are group elements (`Plaintext = P.G₁`), ciphertexts are pairs
(`Ciphertext = P.G₁ × P.G₁`).

## The reduction (Rosulek)

The DDH structure `elgamalDDH : DDHDef P.G₁` samples `s ← ZMod p` and publishes
`g₁ ^ᵍ s`, with `ecdh (g₁ ^ᵍ a) (g₁ ^ᵍ b) = g₁ ^ᵍ (a·b)` (the true shared secret,
defined through the discrete-log bijection `expEquiv : ZMod p ≃ G₁`).

Given a fixed message `m`, the reduction adversary `elgamalReduction m A` turns a
DDH triple `(g^a, g^b, Z)` into the ciphertext `(g^b, Z · m)` and runs the IND-CPA
distinguisher `A` on it. When `Z = g^{ab}` this is a real ElGamal encryption of `m`
under `pk = g^a` with randomness `r = b`; when `Z` is uniform, `Z · m` is uniform
and independent of `m`.

The classic three-hop argument (real `m₀` → uniform → real `m₁`, the middle games
coinciding because multiplication by `m` is a bijection of the uniform mask) yields
the bound `INDCPA_Adv ≤ DDH_Advantage(m₀) + DDH_Advantage(m₁)`.

## Main results

* `elgamalDDH` / `elgamalEnc` — the DDH structure and the encryption scheme.
* `elgamalEnc_correct` — decryption inverts encryption.
* `elgamal_real₀_eq` / `elgamal_real₁_eq` — each IND-CPA game equals a real DDH game
  composed with the reduction adversary (exact distribution equalities).
* `elgamal_ideal_eq` — the two ideal DDH games coincide (the mask absorbs the
  message).
* `elgamal_indcpa_le_ddh` — **the headline**: for every message pair and every
  distinguisher,
  `INDCPA_Adv elgamalEnc m₀ m₁ A ≤`
  `DDH_Advantage elgamalDDH (elgamalReduction m₀ A) + DDH_Advantage elgamalDDH (elgamalReduction m₁ A)`.

## References

* [Rosulek, *The Joy of Cryptography*, §15 (ElGamal / DDH)]
* [Boneh & Shoup, *A Graduate Course in Applied Cryptography*, §11.4]
* `CatCryptCore.Crypto.Assumptions.DDH` for the DDH game and advantage.
* `CatCryptCore.Crypto.PairingGroup` for the abstract prime-order group.
-/

namespace CatCrypt.Examples.ElGamal

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.PairingGroup
open CatCrypt.Crypto.Assumptions
open CatCrypt.Crypto.SecurityDefs
open scoped ENNReal

variable {P : PairingGroup}

/-! ## Sampleability of the group -/

/-- `P.G₁` is a sampleable type (finite, nonempty, decidable equality, inhabited):
    everything but the inhabitant comes from the `PairingGroup` instances. -/
noncomputable instance samplerG₁ (P : PairingGroup) : SampleableType P.G₁ :=
  { inhabited := Inhabited.mk 1 }

/-! ## Discrete-log bijection

`s ↦ g₁ ^ᵍ s` is injective (trivial kernel) and, since `|ZMod p| = p = |G₁|`,
bijective. Its inverse is the (noncomputable) discrete log, which we use to give
`ecdh` its intended meaning `g^a, g^b ↦ g^{ab}`. -/

/-- `s ↦ g₁ ^ᵍ s` is injective. -/
private theorem exp_injective : Function.Injective (fun s : ZMod P.p => P.g₁ ^ᵍ s) := by
  intro a b hab
  simp only at hab
  have h1 : P.g₁ ^ᵍ (a - b) = 1 := by
    rw [zpowZMod₁_sub, hab, mul_inv_cancel]
  have h2 : a - b = 0 := (zpowZMod₁_eq_one_iff (a - b)).mp h1
  exact sub_eq_zero.mp h2

/-- `s ↦ g₁ ^ᵍ s` is bijective (equal cardinalities). -/
private theorem exp_bijective : Function.Bijective (fun s : ZMod P.p => P.g₁ ^ᵍ s) := by
  haveI : NeZero P.p := ⟨P.instPrime.out.ne_zero⟩
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨exp_injective, ?_⟩
  rw [ZMod.card, P.cardG₁]

/-- The discrete-log equivalence `ZMod p ≃ G₁`, `a ↦ g₁ ^ᵍ a`. -/
noncomputable def expEquiv (P : PairingGroup) : ZMod P.p ≃ P.G₁ :=
  Equiv.ofBijective _ exp_bijective

@[simp] theorem expEquiv_apply (a : ZMod P.p) : expEquiv P a = P.g₁ ^ᵍ a :=
  rfl

/-- Discrete log of `g₁ ^ᵍ a` is `a`. -/
@[simp] theorem dlog_exp (a : ZMod P.p) : (expEquiv P).symm (P.g₁ ^ᵍ a) = a := by
  rw [← expEquiv_apply, Equiv.symm_apply_apply]

/-! ## The ElGamal DDH structure -/

/-- ElGamal's Diffie–Hellman operation: `ecdh X Y = g₁ ^ᵍ (dlog X · dlog Y)`, i.e.
    `ecdh (g^a) (g^b) = g^{ab}`. -/
noncomputable def elgamalEcdh (X Y : P.G₁) : P.G₁ :=
  P.g₁ ^ᵍ ((expEquiv P).symm X * (expEquiv P).symm Y)

/-- On honest key pairs, `ecdh` computes the true shared secret. -/
theorem elgamalEcdh_exp (a b : ZMod P.p) :
    elgamalEcdh (P.g₁ ^ᵍ a) (P.g₁ ^ᵍ b) = P.g₁ ^ᵍ (a * b) := by
  simp only [elgamalEcdh, dlog_exp]

/-- ElGamal key generation: sample `s`, publish `g₁ ^ᵍ s` (as both key components). -/
noncomputable def elgamalKeygen : SPComp (P.G₁ × P.G₁) := do
  let s ← SPComp.sample (ZMod P.p)
  SPComp.pure (P.g₁ ^ᵍ s, P.g₁ ^ᵍ s)

theorem elgamalKeygen_isPure : SPComp.IsPure (elgamalKeygen (P := P)) := by
  unfold elgamalKeygen
  exact SPComp.bind_isPure (SPComp.sample_isPure _) fun s => SPComp.pure_isPure _

/-- The DDH group underlying ElGamal, over the abstract prime-order group `P.G₁`. -/
noncomputable def elgamalDDH (P : PairingGroup) : DDHDef P.G₁ where
  ecdh := elgamalEcdh
  keygen := elgamalKeygen
  keygen_isPure := elgamalKeygen_isPure

/-! ## The ElGamal encryption scheme -/

/-- ElGamal as a core `EncScheme` over `P.G₁`. -/
noncomputable def elgamalEnc (P : PairingGroup) : EncScheme where
  Key := ZMod P.p
  Plaintext := P.G₁
  Ciphertext := P.G₁ × P.G₁
  finKey := haveI : NeZero P.p := ⟨P.instPrime.out.ne_zero⟩; inferInstance
  neKey := haveI : NeZero P.p := ⟨P.instPrime.out.ne_zero⟩; inferInstance
  finCt := inferInstance
  neCt := inferInstance
  keyGen := SPComp.sample (ZMod P.p)
  encrypt := fun sk m => do
    let r ← SPComp.sample (ZMod P.p)
    SPComp.pure (P.g₁ ^ᵍ r, (P.g₁ ^ᵍ sk) ^ᵍ r * m)
  decrypt := fun sk c => SPComp.pure (some (c.2 * (c.1 ^ᵍ sk)⁻¹))

/-- **Correctness** (algebraic core): for every secret key, randomness, and message,
    the ElGamal decryption formula inverts the encryption formula. -/
theorem elgamal_dec_enc (sk r : ZMod P.p) (m : P.G₁) :
    ((P.g₁ ^ᵍ sk) ^ᵍ r * m) * ((P.g₁ ^ᵍ r) ^ᵍ sk)⁻¹ = m := by
  rw [zpowZMod₁_zpowZMod₁, zpowZMod₁_zpowZMod₁, mul_comm sk r,
    mul_comm ((P.g₁ ^ᵍ (r * sk))) m, mul_assoc, mul_inv_cancel, mul_one]

/-! ## The reduction adversary -/

/-- The Rosulek reduction: on a DDH triple `(g^a, g^b, Z)`, form the ciphertext
    `(g^b, Z · m)` and run the IND-CPA distinguisher `A`. -/
noncomputable def elgamalReduction (m : P.G₁) (A : (P.G₁ × P.G₁) → SPComp Bool) :
    DDH_Adversary P.G₁ :=
  fun _g_a g_b z => A (g_b, z * m)

/-! ## Game equalities -/

/-- The real IND-CPA game encrypting `m₀` (the `true` branch), post-composed with the
    distinguisher, is exactly the real DDH game with the `m₀`-reduction. -/
theorem elgamal_real₀_eq (m₀ m₁ : P.G₁) (A : (P.G₁ × P.G₁) → SPComp Bool) :
    SPComp.bind (INDCPA_Game (elgamalEnc P) m₀ m₁ true) A =
      DDH_Game_Real (elgamalDDH P) (elgamalReduction m₀ A) := by
  simp only [INDCPA_Game, DDH_Game_Real, elgamalEnc, elgamalDDH, elgamalKeygen,
    elgamalReduction, if_true, ssprove_simpl]
  bind_align
  rw [elgamalEcdh_exp, zpowZMod₁_zpowZMod₁]

/-- The real IND-CPA game encrypting `m₁` (the `false` branch) equals the real DDH
    game with the `m₁`-reduction. -/
theorem elgamal_real₁_eq (m₀ m₁ : P.G₁) (A : (P.G₁ × P.G₁) → SPComp Bool) :
    SPComp.bind (INDCPA_Game (elgamalEnc P) m₀ m₁ false) A =
      DDH_Game_Real (elgamalDDH P) (elgamalReduction m₁ A) := by
  simp only [INDCPA_Game, DDH_Game_Real, elgamalEnc, elgamalDDH, elgamalKeygen,
    elgamalReduction, Bool.false_eq_true, if_false, ssprove_simpl]
  bind_align
  rw [elgamalEcdh_exp, zpowZMod₁_zpowZMod₁]

/-- Absorbing the mask: for any first component `gb`, sampling the DDH mask `c` and
    running `A` on `(gb, c · m)` has the same distribution as running `A` on `(gb, c)`
    — multiplication by `m` is a bijection of the uniform mask. -/
private theorem mask_absorb (gb m : P.G₁) (A : (P.G₁ × P.G₁) → SPComp Bool) :
    (SPComp.sample P.G₁ >>= fun c => A (gb, c * m)) =
      (SPComp.sample P.G₁ >>= fun c => A (gb, c)) := by
  simpa using SPComp.sample_bind_equiv (Equiv.mulRight m) (fun c => A (gb, c))

/-- The two ideal DDH games (with the `m₀`- and `m₁`-reductions) coincide: after the
    mask is absorbed, neither depends on the message. -/
theorem elgamal_ideal_eq (m₀ m₁ : P.G₁) (A : (P.G₁ × P.G₁) → SPComp Bool) :
    DDH_Game_Ideal (elgamalDDH P) (elgamalReduction m₀ A) =
      DDH_Game_Ideal (elgamalDDH P) (elgamalReduction m₁ A) := by
  simp only [DDH_Game_Ideal, elgamalDDH, elgamalReduction, mask_absorb]

/-! ## The IND-CPA → DDH reduction bound -/

/-- **ElGamal is IND-CPA secure under DDH.** For every message pair `m₀, m₁` and
    every distinguisher `A`, the IND-CPA advantage against ElGamal is bounded by the
    sum of the DDH advantages of the two reduction adversaries:

    `INDCPA_Adv elgamalEnc m₀ m₁ A ≤`
    `  DDH_Advantage elgamalDDH (elgamalReduction m₀ A)`
    `  + DDH_Advantage elgamalDDH (elgamalReduction m₁ A)`.

    This is the standard three-hop reduction of Rosulek, *The Joy of Cryptography*:
    the two real games are DDH-real games (`elgamal_real₀_eq`, `elgamal_real₁_eq`),
    the two ideal games coincide (`elgamal_ideal_eq`), and the triangle inequality
    for `Advantage` glues the hops. -/
theorem elgamal_indcpa_le_ddh (m₀ m₁ : P.G₁) (A : (P.G₁ × P.G₁) → SPComp Bool) :
    INDCPA_Adv (elgamalEnc P) m₀ m₁ A ≤
      DDH_Advantage (elgamalDDH P) (elgamalReduction m₀ A) +
      DDH_Advantage (elgamalDDH P) (elgamalReduction m₁ A) := by
  -- The IND-CPA advantage is the advantage between the two real DDH games.
  have hadv : INDCPA_Adv (elgamalEnc P) m₀ m₁ A =
      Advantage (DDH_Game_Real (elgamalDDH P) (elgamalReduction m₀ A))
                (DDH_Game_Real (elgamalDDH P) (elgamalReduction m₁ A)) := by
    simp only [INDCPA_Adv, AdvantageA]
    rw [← elgamal_real₀_eq m₀ m₁ A, ← elgamal_real₁_eq m₀ m₁ A]
  -- The two ideal games coincide, so the middle hop has zero advantage.
  have hmid : Advantage (DDH_Game_Ideal (elgamalDDH P) (elgamalReduction m₀ A))
                        (DDH_Game_Ideal (elgamalDDH P) (elgamalReduction m₁ A)) = 0 := by
    rw [elgamal_ideal_eq m₀ m₁ A, Advantage_self]
  rw [hadv]
  simp only [DDH_Advantage]
  -- Abbreviations for the four DDH games (real/ideal, m₀/m₁).
  set R0r := DDH_Game_Real (elgamalDDH P) (elgamalReduction m₀ A)
  set R1r := DDH_Game_Real (elgamalDDH P) (elgamalReduction m₁ A)
  set R0i := DDH_Game_Ideal (elgamalDDH P) (elgamalReduction m₀ A)
  set R1i := DDH_Game_Ideal (elgamalDDH P) (elgamalReduction m₁ A)
  calc Advantage R0r R1r
      ≤ Advantage R0r R0i + Advantage R0i R1r := advantage_triangle _ _ _
    _ ≤ Advantage R0r R0i + (Advantage R0i R1i + Advantage R1i R1r) := by
          gcongr; exact advantage_triangle _ _ _
    _ = Advantage R0r R0i + (0 + Advantage R1i R1r) := by rw [hmid]
    _ = Advantage R0r R0i + Advantage R1r R1i := by
          rw [zero_add, Advantage_sym R1i R1r]

/-- **ElGamal real-or-random secrecy equals a single DDH advantage.** The analog of
    SSProve-Rocq's `OT_CPA_elgamal` (`AdvOf (OT_CPA elgamal) A = AdvOf (LDDH G) (A ∘ RED)`),
    whose `OT_CPA` game is a real-or-random one-time-secrecy game: the `true` branch
    encrypts `m₀`, the `false` branch returns a ciphertext whose second component is
    uniform and independent of the message.

    The left game is a real ElGamal encryption of `m₀` post-composed with the
    distinguisher; the right is the ideal random-ciphertext game. Their distinguishing
    advantage is the DDH advantage of the single reduction `elgamalReduction m₀ A`, with
    no factor of `2` and no two-term sum:

    `Advantage (bind (INDCPA_Game ⋯ m₀ m₁ true) A) (DDH_Game_Ideal ⋯ (elgamalReduction m₁ A))`
    `  = DDH_Advantage (elgamalDDH P) (elgamalReduction m₀ A)`.

    The ideal game on the left uses the `m₁`-reduction, yet the advantage is the
    `m₀`-reduction's, because the two ideal games coincide (`elgamal_ideal_eq`) — the
    uniform mask absorbs the message. The real game is a DDH-real game
    (`elgamal_real₀_eq`).

    The two-message `INDCPA_Adv` (encrypt `m₀` vs encrypt `m₁`) is a different quantity
    that needs the two-term bound `elgamal_indcpa_le_ddh`, since a real encryption of `m₁`
    is not the ideal random ciphertext. -/
theorem elgamal_indcpa_eq_ddh (m₀ m₁ : P.G₁) (A : (P.G₁ × P.G₁) → SPComp Bool) :
    Advantage (SPComp.bind (INDCPA_Game (elgamalEnc P) m₀ m₁ true) A)
              (DDH_Game_Ideal (elgamalDDH P) (elgamalReduction m₁ A))
      = DDH_Advantage (elgamalDDH P) (elgamalReduction m₀ A) := by
  simp only [elgamal_real₀_eq, DDH_Advantage]
  rw [elgamal_ideal_eq m₀ m₁ A]
