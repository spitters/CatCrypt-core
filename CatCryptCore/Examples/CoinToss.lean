/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.Advantage
import CatCryptCore.Prob.SDistr
import Mathlib.Data.ZMod.Basic

/-!
# Coin Tossing Protocol

This file formalizes a two-party coin tossing protocol over `ZMod p`
and proves its output uniformity via an additive bijection argument.

## Protocol

Two parties each sample a random element from `ZMod p` and output their sum.
The result is uniformly distributed, because for any fixed `a`, the map
`b ↦ a + b` is a bijection on `ZMod p`.

## Main definitions

* `coinTossReal` — real protocol: sample two elements and output their sum
* `coinTossIdeal` — ideal functionality: sample one uniform element

## Main results

* `add_uniform_eq_uniform` — adding a constant to a uniform sample is uniform
* `coinToss_eq` — real and ideal coin toss produce identical distributions
-/

namespace CatCryptCore.Examples.CoinToss

open CatCrypt.Core CatCrypt.Prob

variable (p : Nat) [hp : Fact (Nat.Prime p)]

/-! ## Additive bijection on ZMod p -/

/-- Addition by a fixed element is a bijection on `ZMod p`. -/
noncomputable def addEquiv (a : ZMod p) : ZMod p ≃ ZMod p :=
  Equiv.addLeft a

instance : NeZero p := ⟨Nat.Prime.ne_zero hp.out⟩

/-! ## Protocol Definitions -/

/-- Real coin toss: both parties sample, output the sum. -/
noncomputable def coinTossReal (_ : Unit) : SPComp (ZMod p) :=
  SPComp.bind (SPComp.sample (ZMod p)) fun a =>
  SPComp.bind (SPComp.sample (ZMod p)) fun b =>
  SPComp.pure (a + b)

/-- Ideal coin toss: sample a single uniform element. -/
noncomputable def coinTossIdeal (_ : Unit) : SPComp (ZMod p) :=
  SPComp.sample (ZMod p)

/-! ## Helper Lemmas -/

/-- Sampling uniformly and adding a constant gives the same distribution as
    sampling uniformly. This is the key step: `a + b` for uniform `b` is uniform. -/
theorem add_uniform_eq_uniform (a : ZMod p) (h : Heap) :
    (SPComp.bind (SPComp.sample (ZMod p)) (fun b => SPComp.pure (a + b))) h =
    (SPComp.sample (ZMod p)) h := by
  rw [SPComp.sample_bind_pure]
  show (SDistr.uniform (ZMod p)).bind (fun b => SDistr.pure (a + b, h)) =
       (SDistr.uniform (ZMod p)).bind (fun b => SDistr.pure (b, h))
  exact SDistr.uniform_bind_equiv_comp (addEquiv p a) (fun b => SDistr.pure (b, h))

/-! ## Main Theorem -/

/-- The inner computation: sampling `b` and returning `a + b` equals just sampling. -/
private theorem inner_eq (a : ZMod p) :
    SPComp.bind (SPComp.sample (ZMod p)) (fun b => SPComp.pure (a + b)) =
    SPComp.sample (ZMod p) := by
  funext h; exact add_uniform_eq_uniform p a h

/-- The real coin toss protocol is distributionally equivalent to the ideal
    functionality. Both produce a uniform element of `ZMod p`. -/
theorem coinToss_eq : coinTossReal p = coinTossIdeal p := by
  funext _
  simp only [coinTossReal, coinTossIdeal]
  -- Goal: sample >>= (fun a => sample >>= (fun b => pure (a + b))) = sample
  -- Rewrite inner computation: sample >>= (fun b => pure (a + b)) = sample
  simp_rw [inner_eq p]
  -- reduces to sample >>= (fun _ => sample) = sample at SPComp level
  funext h
  -- Unfold SPComp.bind and SPComp.sample to SDistr operations
  show ((SDistr.uniform (ZMod p)).bind (fun a => SDistr.pure (a, h))).bind
    (fun x => (SDistr.uniform (ZMod p)).bind (fun b => SDistr.pure (b, x.2))) =
    (SDistr.uniform (ZMod p)).bind (fun a => SDistr.pure (a, h))
  rw [SDistr.bind_assoc]
  simp only [SDistr.pure_bind]
  exact SDistr.uniform_bind_const (α := ZMod p) _

end CatCryptCore.Examples.CoinToss
