/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.Assumptions.DL
import CatCryptCore.Crypto.ForkingLemma
import CatCryptCore.Tactics

/-!
# Schnorr's Σ-Protocol: Special Soundness and the Forking Reduction to DL

Schnorr's identification/signature scheme, over an abstract prime-order group.
Following Rosulek, *The Joy of Cryptography* (Σ-protocols), and the standard
Schnorr → Discrete-Logarithm reduction (Pointcheval–Stern / Bellare–Neven).

We work in the group `P.G₁` of a `PairingGroup P` — an abstract cyclic group of
prime order `P.p` with generator `g₁` and `ZMod P.p`-exponentiation `x ^ᵍ a`.
No concrete curve is used.

## The protocol

A statement is a public key `pk : G₁`; the witness is its discrete log
`w : ZMod p` with `g₁ ^ᵍ w = pk`. A transcript `(a, c, s)` consists of a
commitment `a : G₁`, a challenge `c : ZMod p`, and a response `s : ZMod p`, and
is *accepting* when

```
g₁ ^ᵍ s = a * (pk ^ᵍ c).
```

The honest prover samples `r`, sends `a = g₁ ^ᵍ r`, and answers `s = r + w·c`.

## Main results

* `schnorrAccepts` — the acceptance relation of a transcript.
* `schnorr_special_soundness` — **special soundness**: two accepting transcripts
  `(a, c₁, s₁)`, `(a, c₂, s₂)` sharing the commitment `a` with `c₁ ≠ c₂` yield the
  witness `w = (s₁ - s₂) / (c₁ - c₂)` with `g₁ ^ᵍ w = pk`. Pure group algebra, no
  probabilistic reasoning.
* `schnorr_honest_accepts` — the honest transcript always verifies (completeness).
* `SchnorrForger` / `schnorr_forking_bound` — a decomposed (Fiat–Shamir, single
  random-oracle query) forger, and the direct instantiation of the core forking
  lemma: fork success ≥ `acc² - acc/|ZMod p|`.
* `dlFromForking` / `dlFromForking_correct` — a discrete-log solver built from any
  forger via forking + special-soundness extraction, together with the guarantee
  that on a successful fork it returns the true discrete log.

## References

* [Rosulek, *The Joy of Cryptography*, Σ-protocols / signatures]
* [Pointcheval, Stern, *Security arguments for digital signatures and blind
  signatures*, J. Cryptology 2000]
* [Bellare, Neven, *Multi-signatures in the plain public-key model*, CCS 2006]
* `CatCryptCore.Crypto.ForkingLemma` for the general forking lemma.
* `CatCryptCore.Crypto.Assumptions.DL` for the discrete-log game.
-/

namespace CatCrypt.Examples.Schnorr

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.PairingGroup
open CatCrypt.Crypto.ForkingLemma
open scoped ENNReal

variable {P : PairingGroup}

/-! ## General `zpowZMod₁` homomorphism lemmas

`PairingGroup.lean` proves the exponent-homomorphism laws for the generator
`g₁`; special soundness needs them for the *arbitrary* public key `pk`, so we
lift them to a general base element. Every element of `G₁` has order dividing the
prime `p`, so `x ^ᵍ` is a `ZMod p`-module action just like `g₁ ^ᵍ`. -/

/-- `x ^ᵍ a = x ^ a.val` as a `ℕ`-power. -/
private theorem zpowZMod₁_eq_natpow (x : P.G₁) (a : ZMod P.p) :
    zpowZMod₁ (P := P) x a = x ^ a.val := by
  rw [zpowZMod₁, zpow_natCast]

/-- Exponent-additivity for a general base: `x ^ᵍ (a + b) = (x ^ᵍ a) * (x ^ᵍ b)`. -/
private theorem zpowZMod₁_add_gen (x : P.G₁) (a b : ZMod P.p) :
    zpowZMod₁ (P := P) x (a + b) =
    zpowZMod₁ (P := P) x a * zpowZMod₁ (P := P) x b := by
  simp [zpowZMod₁_eq_natpow, ← pow_add, pow_mod_G₁, ZMod.val_add]

/-- Exponent-negation for a general base: `(x ^ᵍ a)⁻¹ = x ^ᵍ (-a)`. -/
private theorem zpowZMod₁_neg_gen (x : P.G₁) (a : ZMod P.p) :
    (zpowZMod₁ (P := P) x a)⁻¹ = zpowZMod₁ (P := P) x (-a) := by
  have h : zpowZMod₁ (P := P) x (-a) * zpowZMod₁ (P := P) x a = 1 := by
    rw [← zpowZMod₁_add_gen, neg_add_cancel, zpowZMod₁_eq_natpow, ZMod.val_zero, pow_zero]
  exact (mul_eq_one_iff_eq_inv.mp h).symm

/-- Exponent-subtraction for a general base: `x ^ᵍ (a - b) = (x ^ᵍ a) * (x ^ᵍ b)⁻¹`. -/
private theorem zpowZMod₁_sub_gen (x : P.G₁) (a b : ZMod P.p) :
    zpowZMod₁ (P := P) x (a - b) =
    zpowZMod₁ (P := P) x a * (zpowZMod₁ (P := P) x b)⁻¹ := by
  rw [sub_eq_add_neg, zpowZMod₁_add_gen, zpowZMod₁_neg_gen]

/-- In `ZMod P.p` (prime `p`) every nonzero element is invertible:
    `a * a⁻¹ = 1`. Proved via `ZMod.mul_inv_eq_gcd` and primality, matching
    the ambient `ZMod.instInv` used throughout. -/
private theorem scalar_mul_inv_cancel (a : ZMod P.p) (ha : a ≠ 0) :
    a * a⁻¹ = 1 := by
  field_simp

/-! ## The Schnorr relation -/

/-- A Schnorr transcript `(a, c, s)` for public key `pk` is *accepting* when
    `g₁ ^ᵍ s = a * (pk ^ᵍ c)`. -/
def schnorrAccepts (pk a : P.G₁) (c s : ZMod P.p) : Prop :=
  (P.g₁ ^ᵍ s) = a * (pk ^ᵍ c)

/-- Boolean acceptance test (decidable, for use as a forking-lemma predicate). -/
noncomputable def schnorrVerify (pk a : P.G₁) (c s : ZMod P.p) : Bool :=
  decide ((P.g₁ ^ᵍ s) = a * (pk ^ᵍ c))

@[simp, grind =] theorem schnorrVerify_eq_true {pk a : P.G₁} {c s : ZMod P.p} :
    schnorrVerify pk a c s = true ↔ schnorrAccepts pk a c s := by
  simp only [schnorrVerify, schnorrAccepts, decide_eq_true_eq]

/-! ## Completeness -/

/-- **Completeness.** The honest transcript `(g₁ ^ᵍ r, c, r + w·c)` for the
    public key `pk = g₁ ^ᵍ w` always verifies. -/
theorem schnorr_honest_accepts (w r c : ZMod P.p) :
    schnorrAccepts (P.g₁ ^ᵍ w) (P.g₁ ^ᵍ r) c (r + w * c) := by
  rw [schnorrAccepts, zpowZMod₁_zpowZMod₁, zpowZMod₁_add]

/-! ## Special soundness -/

/-- **Special soundness.** Two accepting transcripts that share the commitment
    `a` but use distinct challenges `c₁ ≠ c₂` reveal the witness:
    `pk = g₁ ^ᵍ ((s₁ - s₂) / (c₁ - c₂))`.

    This is the algebraic heart of Schnorr's knowledge soundness — and, in the
    ROM/forking reduction, the discrete-log extractor. Pure group algebra: no
    probability. -/
theorem schnorr_special_soundness (pk a : P.G₁) (c₁ c₂ s₁ s₂ : ZMod P.p)
    (hv₁ : schnorrAccepts pk a c₁ s₁)
    (hv₂ : schnorrAccepts pk a c₂ s₂)
    (hne : c₁ ≠ c₂) :
    pk = P.g₁ ^ᵍ ((s₁ - s₂) * (c₁ - c₂)⁻¹) := by
  have hd_ne : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr hne
  have hdd : (c₁ - c₂) * (c₁ - c₂)⁻¹ = 1 := scalar_mul_inv_cancel _ hd_ne
  -- Dividing the two verification equations cancels the shared commitment `a`:
  --   g₁ ^ᵍ (s₁ - s₂) = pk ^ᵍ (c₁ - c₂).
  have hstep : (P.g₁ ^ᵍ (s₁ - s₂)) = (pk ^ᵍ (c₁ - c₂)) := by
    rw [zpowZMod₁_sub, zpowZMod₁_sub_gen]
    unfold schnorrAccepts at hv₁ hv₂
    rw [hv₁, hv₂, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]
  -- Raise both sides to `(c₁-c₂)⁻¹`; the `pk` side becomes `pk ^ᵍ 1 = pk`.
  have hpk : pk = zpowZMod₁ (P := P) (P.g₁ ^ᵍ (s₁ - s₂)) (c₁ - c₂)⁻¹ := by
    rw [hstep, zpowZMod₁_zpowZMod₁, hdd, zpowZMod₁_one]
  rw [hpk, zpowZMod₁_zpowZMod₁]

/-- Boolean-hypothesis form of special soundness, matching the forking-lemma
    acceptance predicate. -/
theorem schnorr_special_soundness_bool (pk a : P.G₁) (c₁ c₂ s₁ s₂ : ZMod P.p)
    (hv₁ : schnorrVerify pk a c₁ s₁ = true)
    (hv₂ : schnorrVerify pk a c₂ s₂ = true)
    (hne : c₁ ≠ c₂) :
    pk = P.g₁ ^ᵍ ((s₁ - s₂) * (c₁ - c₂)⁻¹) :=
  schnorr_special_soundness pk a c₁ c₂ s₁ s₂
    (schnorrVerify_eq_true.mp hv₁) (schnorrVerify_eq_true.mp hv₂) hne

/-! ## Forking reduction to Discrete Log

The forking reduction exercises the core forking lemma. A Fiat–Shamir Schnorr forger making a
single random-oracle query decomposes into a probabilistic *coins* phase (choose
a message and commitment `a`) and a deterministic *respond* phase (given the
challenge `c` from the oracle, produce the response `s`). Replaying the forger on
the same coins but a fresh challenge yields two accepting transcripts that share
the commitment — exactly the hypothesis of `schnorr_special_soundness`. -/

variable (P) in
/-- A decomposed Schnorr forger (single random-oracle query). -/
structure SchnorrForger (Msg S : Type) where
  /-- Probabilistic commit phase: produce internal state, message, commitment `a`. -/
  coins : P.G₁ → SPComp (S × Msg × P.G₁)
  /-- Deterministic response phase: given state and challenge `c`, produce `s`. -/
  respond : S → ZMod P.p → ZMod P.p

variable {Msg S : Type}

/-- View a `SchnorrForger` as a core `ForkableAdversary`. The response type
    carries `(a, c, s)` so the acceptance predicate can run verification. -/
noncomputable def SchnorrForger.toForkable (A : SchnorrForger P Msg S) :
    ForkableAdversary P.G₁ (S × Msg × P.G₁) (ZMod P.p)
      (P.G₁ × ZMod P.p × ZMod P.p) where
  coins := A.coins
  respond := fun _pk st c => (st.2.2, c, A.respond st.1 c)

/-- Acceptance predicate for the forking lemma: run Schnorr verification. -/
noncomputable def romAccept (pk : P.G₁) :
    (P.G₁ × ZMod P.p × ZMod P.p) → Bool :=
  fun t => schnorrVerify pk t.1 t.2.1 t.2.2

/-- **Forking bound.** For any public key, the fork-success probability is at
    least `acc² - acc / |ZMod p|` — a direct instantiation of the core forking
    lemma `fork_success_ge`. Two successful runs share the commitment and (with
    probability accounted for by the `- acc/|R|` term) use distinct challenges,
    so special soundness extracts the discrete log. -/
theorem schnorr_forking_bound (A : SchnorrForger P Msg S) (pk : P.G₁) :
    forkSuccProb A.toForkable pk (romAccept pk) ≥
      acceptProb A.toForkable pk (romAccept pk) ^ 2 -
      acceptProb A.toForkable pk (romAccept pk) / Fintype.card (ZMod P.p) :=
  fork_success_ge A.toForkable pk (romAccept pk)

/-- A discrete-log solver built from a Schnorr forger: fork, and on success
    extract via special soundness; otherwise fall back to a random guess. -/
noncomputable def dlFromForking (A : SchnorrForger P Msg S) :
    P.G₁ → SPComp (ZMod P.p) := fun pk => do
  let (st, _m, a) ← A.coins pk
  let c₁ ← SPComp.sample (ZMod P.p)
  let s₁ := A.respond st c₁
  let c₂ ← SPComp.sample (ZMod P.p)
  let s₂ := A.respond st c₂
  if schnorrVerify pk a c₁ s₁ && schnorrVerify pk a c₂ s₂ && decide (c₁ ≠ c₂) then
    SPComp.pure ((s₁ - s₂) * (c₁ - c₂)⁻¹)
  else
    SPComp.sample (ZMod P.p)

/-- **Extraction correctness.** On a successful fork — both transcripts accept
    and the challenges differ — the extracted scalar is the true discrete log of
    `pk`. This is exactly `schnorr_special_soundness` applied to the two replayed
    transcripts. -/
theorem dlFromForking_correct (A : SchnorrForger P Msg S)
    (pk a : P.G₁) (st : S) (c₁ c₂ : ZMod P.p)
    (hv₁ : schnorrVerify pk a c₁ (A.respond st c₁) = true)
    (hv₂ : schnorrVerify pk a c₂ (A.respond st c₂) = true)
    (hne : c₁ ≠ c₂) :
    (P.g₁ ^ᵍ ((A.respond st c₁ - A.respond st c₂) * (c₁ - c₂)⁻¹)) = pk :=
  (schnorr_special_soundness_bool pk a c₁ c₂ _ _ hv₁ hv₂ hne).symm

end CatCrypt.Examples.Schnorr
