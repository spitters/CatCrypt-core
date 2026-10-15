/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.SecurityDefs
public import CatCryptCore.Crypto.ForkingLemma
public import CatCryptCore.Prob.XorBij
public import CatCryptCore.Tactics

/-!
# Bijection-Family MAC: Forgery Probability Without Tag Queries

A message-authentication code built from a *bijection family*: for each message
`m`, the map `k ↦ mac k m` is a bijection from keys to tags. Following Rosulek,
The Joy of Cryptography, §9 (MACs).

Over a uniform key the tag `mac k m*` is uniform on the tag space, so a forgery
`(m*, t*)` chosen without tag queries verifies with probability exactly
`1 / |Tag|`. The result is stated for EUF-CMA adversaries with query bound `0`
(`OracleAdv.IsQueryBound A 0`). A bijection family gives no bound after one
tag query: for the XOR MAC, the tag `k ⊕ m` on one message determines the key.

## Main definitions

* `BijMACFamily` — a family of key→tag bijections indexed by message.
* `BijMACFamily.toMACScheme` — the core `MACScheme` it induces (`mac k m = bij m k`).
* `boolXorMAC` — the XOR MAC over `Bool` (`mac k m = k ⊕ m`), the MAC counterpart
  of the one-time pad.

## Main results

* `bijMAC_forgery_filter` — a fixed forgery verifies under exactly one key.
* `bijMAC_euf_cma_adv_of_isQueryBound_zero` — an EUF-CMA adversary without tag
  queries has advantage exactly `1 / |Tag|` against a bijection-family MAC.
* `boolXorMAC_euf_cma_adv_of_isQueryBound_zero` — the same for the `Bool` XOR
  MAC, with value `1 / 2`.

These replace `bijMAC_forgery_prob`, `bijMAC_euf_cma_adv` and
`boolXorMAC_forgery_prob`, which concerned a game whose forgery was a fixed
parameter and whose adversary saw no tag.

## References

* [Rosulek, The Joy of Cryptography, §9 (MACs)]
* [Wegman & Carter, New hash functions and their use in authentication, 1981]
-/

@[expose] public section

namespace CatCrypt.Examples.MAC

open CatCrypt.Core
open CatCrypt.Crypto
open CatCrypt.Crypto.SecurityDefs
open CatCrypt.Crypto.ForkingLemma
open CatCrypt.Prob
open CatCrypt.Prob.XorBij
open scoped ENNReal

/-! ## Bijection-Family MAC -/

/-- A MAC given by a family of bijections `bij m : Key ≃ Tag`, one per message.

For a uniform key, `bij m` maps the uniform key distribution onto the uniform
tag distribution, which forces the forgery probability down to `1 / |Tag|`. -/
structure BijMACFamily where
  /-- Key type -/
  Key : Type
  /-- Message type -/
  Message : Type
  /-- Tag type -/
  Tag : Type
  [finKey : Fintype Key]
  [neKey : Nonempty Key]
  [finTag : Fintype Tag]
  [neTag : Nonempty Tag]
  [decTag : DecidableEq Tag]
  /-- For each message, a bijection from keys to tags -/
  bij : Message → (Key ≃ Tag)

attribute [instance] BijMACFamily.finKey BijMACFamily.neKey BijMACFamily.finTag
  BijMACFamily.neTag BijMACFamily.decTag

/-- The core `MACScheme` induced by a bijection family: `mac k m = bij m k`,
verification recomputing and comparing (the `MACScheme` default). -/
def BijMACFamily.toMACScheme (B : BijMACFamily) : MACScheme where
  Key := B.Key
  Message := B.Message
  Tag := B.Tag
  mac := fun k m => B.bij m k

@[simp, grind =] theorem toMACScheme_mac (B : BijMACFamily) (k : B.Key) (m : B.Message) :
    B.toMACScheme.mac k m = B.bij m k := rfl

@[simp, grind =] theorem toMACScheme_verify (B : BijMACFamily) (k : B.Key) (m : B.Message)
    (t : B.Tag) : B.toMACScheme.verify k m t = (t == B.bij m k) := rfl

/-! ## Forgery Probability -/

/-- A fixed forgery attempt `(m*, t*)` verifies under exactly one key: the map
`k ↦ bij m* k` is a bijection, so `bij m* k = t*` pins `k = (bij m*).symm t*`. -/
theorem bijMAC_forgery_filter (B : BijMACFamily) (m_star : B.Message) (t_star : B.Tag) :
    (Finset.univ.filter
      (fun k : B.Key => (B.toMACScheme.verify k m_star t_star))).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨(B.bij m_star).symm t_star, ?_⟩
  ext k
  grind

/-- Over a uniform key, a fixed forgery `(m*, t*)` verifies with probability
`1 / |Tag|`. -/
theorem bijMAC_forgery_prob_key (B : BijMACFamily) (m_star : B.Message) (t_star : B.Tag) :
    ∑' k : B.Key, (Fintype.card B.Key : ℝ≥0∞)⁻¹ *
        (if B.toMACScheme.verify k m_star t_star = true then 1 else 0)
      = 1 / (Fintype.card B.Tag : ℝ≥0∞) := by
  rw [tsum_fintype, ← Finset.mul_sum, Finset.sum_boole, bijMAC_forgery_filter,
    Fintype.card_congr (B.bij m_star)]
  simp

/-- **EUF-CMA without tag queries.** An EUF-CMA adversary that asks no tag
query wins against a bijection-family MAC with probability exactly
`1 / |Tag|`. Its forgery is distributed independently of the key, and each
fixed forgery verifies under exactly one key (`bijMAC_forgery_filter`). -/
theorem bijMAC_euf_cma_adv_of_isQueryBound_zero (B : BijMACFamily)
    (A : EUF_CMA_Adversary B.toMACScheme) (hA : A.IsQueryBound 0) :
    EUF_CMA_Adv B.toMACScheme A = 1 / (Fintype.card B.Tag : ℝ≥0∞) := by
  unfold EUF_CMA_Adv EUF_CMA_Real
  rw [PMF.bind_apply]
  simp only [PMF.uniformOfFintype_apply]
  induction A with
  | ret r =>
    simp only [OracleAdv.run_ret, PMF.pure_map, PMF.pure_apply, List.not_mem_nil,
      not_false_eq_true, decide_true, Bool.and_true]
    refine (tsum_congr fun k => ?_).trans (bijMAC_forgery_prob_key B r.1 r.2)
    simp only [@eq_comm Bool true]
    rfl
  | rand p c ih =>
    simp only [OracleAdv.run_rand, PMF.map_bind, PMF.bind_apply]
    have key : ∀ X : B.toMACScheme.Key → _ → ℝ≥0∞,
        (∀ i, ∑' k, (Fintype.card B.toMACScheme.Key : ℝ≥0∞)⁻¹ * X k i =
          1 / (Fintype.card B.Tag : ℝ≥0∞)) →
        ∑' k, (Fintype.card B.toMACScheme.Key : ℝ≥0∞)⁻¹ * ∑' i, p i * X k i =
          1 / (Fintype.card B.Tag : ℝ≥0∞) := by
      intro X hX
      simp_rw [← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      have hc : ∀ i, ∑' k, (Fintype.card B.toMACScheme.Key : ℝ≥0∞)⁻¹ * (p i * X k i) =
          p i * (1 / (Fintype.card B.Tag : ℝ≥0∞)) := fun i => by
        rw [← hX i, ← ENNReal.tsum_mul_left]
        exact tsum_congr fun k => by ring
      rw [tsum_congr hc, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    exact key _ fun i => ih i (hA i)
  | query d k ih => exact hA.elim

/-! ## Example: the XOR MAC over `Bool`

`mac k m = k ⊕ m` is the bijection family `m ↦ boolXorBij m`; it is the MAC
counterpart of the one-time pad and the XOR PRF. Without tag queries a forger
wins with probability `1 / 2`. -/

/-- The XOR MAC over `Bool` as a bijection family: `bij m = boolXorBij m`. -/
def boolXorMAC : BijMACFamily where
  Key := Bool
  Message := Bool
  Tag := Bool
  bij := boolXorBij

/-- An EUF-CMA adversary without tag queries wins against the `Bool` XOR MAC
with probability exactly `1 / 2`. -/
theorem boolXorMAC_euf_cma_adv_of_isQueryBound_zero
    (A : EUF_CMA_Adversary boolXorMAC.toMACScheme) (hA : A.IsQueryBound 0) :
    EUF_CMA_Adv boolXorMAC.toMACScheme A = 1 / 2 := by
  refine (bijMAC_euf_cma_adv_of_isQueryBound_zero boolXorMAC A hA).trans ?_
  simp [show Fintype.card boolXorMAC.Tag = 2 from rfl]

end CatCrypt.Examples.MAC
