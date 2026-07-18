/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.SecurityDefs
import CatCryptCore.Crypto.Assumptions.DDH
import CatCryptCore.Crypto.PairingGroup
import CatCryptCore.Examples.ElGamal
import CatCryptCore.Tactics

/-!
# Diffie–Hellman Key Agreement: Key-Indistinguishability from DDH

The Diffie–Hellman key exchange over an abstract prime-order group, and the proof
that its key-indistinguishability advantage *equals* the Decisional Diffie–Hellman
advantage of an explicit reduction. Following Rosulek, *The Joy of Cryptography*
(Diffie–Hellman).

We work in the group `P.G₁` of a `PairingGroup P` — an abstract cyclic group of
prime order `P.p` with generator `g₁` and `ZMod P.p`-exponentiation `x ^ᵍ a`. No
concrete curve is used. The DH group structure (`elgamalDDH`, `elgamalEcdh`) is
shared with `CatCryptCore.Examples.ElGamal`.

## The protocol

* Alice samples `a ← ZMod p` and publishes `g₁ ^ᵍ a`.
* Bob samples `b ← ZMod p` and publishes `g₁ ^ᵍ b`.
* Both parties compute the shared key `k = g₁ ^ᵍ (a·b)` — Alice as `(g₁^b)^a`,
  Bob as `(g₁^a)^b`.

The public **transcript** is the pair `(g₁ ^ᵍ a, g₁ ^ᵍ b)`.

## Security (Rosulek)

Key indistinguishability: to an eavesdropper who sees the transcript, the real
shared key `g₁ ^ᵍ (a·b)` is indistinguishable from a uniform group element. The
real experiment `KA_Game_Real` hands the distinguisher `(transcript, g^{ab})`; the
ideal experiment `KA_Game_Ideal` hands it `(transcript, uniform)`. These two
distributions are, verbatim, the real and ideal DDH challenge distributions — so
DH key indistinguishability *is* DDH.

## The reduction

`dhReduction D` repackages a key-indistinguishability distinguisher
`D : (G₁ × G₁) → G₁ → SPComp Bool` into a DDH adversary
`fun g_a g_b z => D (g_a, g_b) z`: the DDH triple `(g^a, g^b, z)` is presented as a
transcript `(g^a, g^b)` together with a candidate key `z`. Because the DDH group's
`keygen` samples `s` and publishes `g^s`, and `elgamalEcdh (g^a) (g^b) = g^{ab}`
(via the discrete-log bijection), the DDH real/ideal games unfold to exactly the
DH key-agreement real/ideal experiments.

## Main results

* `KA_Game_Real` / `KA_Game_Ideal` / `KA_Advantage` — the DH key-agreement
  experiments and the key-indistinguishability advantage.
* `dhReduction` — the (transcript-repackaging) DDH adversary.
* `ka_real_eq` / `ka_ideal_eq` — each key-agreement experiment equals the
  corresponding DDH game under the reduction (exact distribution equalities).
* `ka_advantage_eq_ddh` — **the headline**: the DH key-indistinguishability
  advantage *equals* the DDH advantage of the reduction,
  `KA_Advantage P D = DDH_Advantage (elgamalDDH P) (dhReduction D)`.
* `ka_secure_under_ddh` — DH key agreement is secure under DDH: if every DDH
  adversary has advantage at most `ε`, so does every key distinguisher.

## References

* [Rosulek, *The Joy of Cryptography*, §14–15 (Diffie–Hellman / DDH)]
* [Boneh & Shoup, *A Graduate Course in Applied Cryptography*, §11.4, Def. 11.2]
* `CatCryptCore.Crypto.Assumptions.DDH` for the DDH games and advantage.
* `CatCryptCore.Examples.ElGamal` for the shared DH group (`elgamalDDH`).
* `CatCryptCore.Crypto.PairingGroup` for the abstract prime-order group.
-/

namespace CatCrypt.Examples.DiffieHellman

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.PairingGroup
open CatCrypt.Crypto.Assumptions
open CatCrypt.Examples.ElGamal
open scoped ENNReal

variable {P : PairingGroup}

/-! ## The key-agreement experiments -/

/-- A key-indistinguishability distinguisher: given the public transcript
    `(g₁ ^ᵍ a, g₁ ^ᵍ b)` and a candidate shared key, output a guess bit. -/
abbrev KA_Distinguisher (W : Type) := (W × W) → W → SPComp Bool

/-- **Real** DH key-agreement experiment: Alice publishes `g₁ ^ᵍ a`, Bob publishes
    `g₁ ^ᵍ b`, and the shared key is the true DH secret `g₁ ^ᵍ (a·b)`. The
    distinguisher receives the transcript together with the real key. -/
noncomputable def KA_Game_Real (P : PairingGroup) (D : KA_Distinguisher P.G₁) :
    SPComp Bool := do
  let a ← SPComp.sample (ZMod P.p)
  let b ← SPComp.sample (ZMod P.p)
  D (P.g₁ ^ᵍ a, P.g₁ ^ᵍ b) (P.g₁ ^ᵍ (a * b))

/-- **Ideal** DH key-agreement experiment: same transcript `(g₁ ^ᵍ a, g₁ ^ᵍ b)`,
    but the key is a fresh uniform group element, independent of the transcript. -/
noncomputable def KA_Game_Ideal (P : PairingGroup) (D : KA_Distinguisher P.G₁) :
    SPComp Bool := do
  let a ← SPComp.sample (ZMod P.p)
  let b ← SPComp.sample (ZMod P.p)
  let k ← SPComp.sample P.G₁
  D (P.g₁ ^ᵍ a, P.g₁ ^ᵍ b) k

/-- Key-indistinguishability advantage: the ability to tell the real shared key
    from a uniform one, given the transcript. -/
noncomputable def KA_Advantage (P : PairingGroup) (D : KA_Distinguisher P.G₁) :
    ℝ≥0∞ :=
  Advantage (KA_Game_Real P D) (KA_Game_Ideal P D)

/-! ## The reduction -/

/-- The reduction to DDH: present the DDH triple `(g^a, g^b, z)` as a transcript
    `(g^a, g^b)` together with a candidate shared key `z`, and run the
    key-indistinguishability distinguisher `D`. -/
noncomputable def dhReduction (D : KA_Distinguisher P.G₁) : DDH_Adversary P.G₁ :=
  fun g_a g_b z => D (g_a, g_b) z

/-! ## Game equalities -/

/-- The real key-agreement experiment equals the real DDH game under the reduction:
    the DDH group's `keygen` samples `s` and publishes `g^s`, and
    `elgamalEcdh (g^a) (g^b) = g^{ab}` is exactly the true DH shared key. -/
theorem ka_real_eq (D : KA_Distinguisher P.G₁) :
    KA_Game_Real P D = DDH_Game_Real (elgamalDDH P) (dhReduction D) := by
  simp only [KA_Game_Real, DDH_Game_Real, elgamalDDH, elgamalKeygen, dhReduction,
    SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
  bind_align
  simp only [dlog_exp]

/-- The ideal key-agreement experiment equals the ideal DDH game under the
    reduction: both replace the shared key with a fresh uniform group element. -/
theorem ka_ideal_eq (D : KA_Distinguisher P.G₁) :
    KA_Game_Ideal P D = DDH_Game_Ideal (elgamalDDH P) (dhReduction D) := by
  simp only [KA_Game_Ideal, DDH_Game_Ideal, elgamalDDH, elgamalKeygen, dhReduction,
    SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]

/-! ## Key indistinguishability equals DDH -/

/-- **DH key indistinguishability is DDH.** For every distinguisher `D`, the DH
    key-agreement key-indistinguishability advantage equals the DDH advantage of the
    reduction:

    `KA_Advantage P D = DDH_Advantage (elgamalDDH P) (dhReduction D)`.

    This is an exact equality, not merely a bound: the two key-agreement experiments
    are, verbatim, the real and ideal DDH challenge distributions (`ka_real_eq`,
    `ka_ideal_eq`). Rosulek, *The Joy of Cryptography* (Diffie–Hellman). -/
theorem ka_advantage_eq_ddh (D : KA_Distinguisher P.G₁) :
    KA_Advantage P D = DDH_Advantage (elgamalDDH P) (dhReduction D) := by
  rw [KA_Advantage, DDH_Advantage, ka_real_eq, ka_ideal_eq]

/-- **DH key agreement is secure under DDH.** If every DDH adversary over the group
    has advantage at most `ε`, then every key-indistinguishability distinguisher
    against the DH key exchange has advantage at most `ε`. -/
theorem ka_secure_under_ddh (ε : ℝ≥0∞)
    (h_ddh : ∀ A : DDH_Adversary P.G₁, DDH_Advantage (elgamalDDH P) A ≤ ε)
    (D : KA_Distinguisher P.G₁) :
    KA_Advantage P D ≤ ε := by
  simpa only [ka_advantage_eq_ddh] using h_ddh (dhReduction D)

end CatCrypt.Examples.DiffieHellman
