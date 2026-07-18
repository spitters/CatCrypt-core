/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.SecurityDefs
import CatCryptCore.Crypto.ForkingLemma
import CatCryptCore.Prob.XorBij
import CatCryptCore.Tactics

/-!
# Bijection-Family MAC: Optimal Information-Theoretic Unforgeability

A message-authentication code built from a *bijection family* achieves the
information-theoretically optimal forgery probability `1 / |Tag|`. Following
Rosulek, The Joy of Cryptography, §9 (MACs).

For each message `m`, if the map `k ↦ mac k m` is a bijection from keys to tags,
then over a uniform key the tag `mac k m` is uniform on the tag space. A fixed
forgery attempt `(m*, t*)` therefore verifies for *exactly one* key, so the
single-query EUF-CMA game accepts the forgery with probability exactly
`1 / |Tag|` — the smallest a forger can be forced below by an honest random tag,
and the best any `|Tag|`-tag MAC can achieve against a blind guess.

## Overview

This mirrors the bijection-coupling examples (`CatCrypt.Examples.OTP`,
`CatCrypt.Examples.PRF`). Where those collapse a *distinguishing* advantage to
`0`, a MAC's forgery probability is not `0` (a forger may always guess a tag);
the sharp statement is that it equals `1 / |Tag|`. The forgery probability is a
`prTrue` of the real game, computed by `prTrue_sample_pure_bool`: it counts the
keys under which the forgery verifies, divided by `|Key|`. The bijection makes
that count exactly `1`, and `|Key| = |Tag|` since `bij m*` is an equivalence.

## Main definitions

* `BijMACFamily` — a family of key→tag bijections indexed by message.
* `BijMACFamily.toMACScheme` — the core `MACScheme` it induces (`mac k m = bij m k`).
* `boolXorMAC` — the XOR MAC over `Bool` (`mac k m = k ⊕ m`), the MAC counterpart
  of the one-time pad.

## Main results

* `bijMAC_forgery_prob` — the single-query EUF-CMA forgery probability of a
  bijection-family MAC is exactly `1 / |Tag|`.
* `bijMAC_euf_cma_adv` — the same, phrased through the core `EUF_CMA_Adv` game
  with the identity (no-post-processing) forger.
* `boolXorMAC_forgery_prob` — the `Bool` XOR MAC has forgery probability `1 / 2`.

## References

* [Rosulek, The Joy of Cryptography, §9 (MACs)]
* [Wegman & Carter, New hash functions and their use in authentication, 1981]
-/

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

/-- **Optimal forgery probability.** For a bijection-family MAC the single-query
EUF-CMA game accepts a fixed forgery `(m*, t*)` with probability exactly
`1 / |Tag|`.

The real game samples a key `k` and returns `verify k m* t* = (t* == bij m* k)`;
`prTrue_sample_pure_bool` turns this into `#{k | forgery verifies} / |Key|`. The
forgery verifies for exactly one `k` (`bijMAC_forgery_filter`), and
`|Key| = |Tag|` because `bij m*` is an equivalence. -/
theorem bijMAC_forgery_prob (B : BijMACFamily) (m m_star : B.Message) (t_star : B.Tag) :
    prTrue (EUF_CMA_Real B.toMACScheme m m_star t_star) Heap.empty
      = 1 / (Fintype.card B.Tag : ℝ≥0∞) := by
  rw [show EUF_CMA_Real B.toMACScheme m m_star t_star
        = SPComp.bind (SPComp.sample B.Key)
            (fun k => SPComp.pure (B.toMACScheme.verify k m_star t_star)) from rfl,
      prTrue_sample_pure_bool, bijMAC_forgery_filter, Fintype.card_congr (B.bij m_star)]
  simp

/-- **Forgery probability through the core `EUF_CMA_Adv` game.** With the identity
forger (no post-processing of the verification bit), the bijection-family MAC's
EUF-CMA advantage is exactly `1 / |Tag|`. -/
theorem bijMAC_euf_cma_adv (B : BijMACFamily) (m m_star : B.Message) (t_star : B.Tag) :
    EUF_CMA_Adv B.toMACScheme m m_star t_star SPComp.pure
      = 1 / (Fintype.card B.Tag : ℝ≥0∞) := by
  simp only [EUF_CMA_Adv, SPComp.monad_bind_eq, SPComp.bind_pure, bijMAC_forgery_prob]

/-! ## Example: the XOR MAC over `Bool`

`mac k m = k ⊕ m` is the bijection family `m ↦ boolXorBij m`; it is the MAC
counterpart of the one-time pad and the XOR PRF, and attains the optimal 1-bit
forgery probability `1 / 2`. -/

/-- The XOR MAC over `Bool` as a bijection family: `bij m = boolXorBij m`. -/
def boolXorMAC : BijMACFamily where
  Key := Bool
  Message := Bool
  Tag := Bool
  bij := boolXorBij

/-- The `Bool` XOR MAC has forgery probability exactly `1 / 2`. -/
theorem boolXorMAC_forgery_prob (m m_star t_star : Bool) :
    prTrue (EUF_CMA_Real boolXorMAC.toMACScheme m m_star t_star) Heap.empty
      = 1 / 2 := by
  simp [bijMAC_forgery_prob, show Fintype.card boolXorMAC.Tag = 2 from rfl]

end CatCrypt.Examples.MAC
