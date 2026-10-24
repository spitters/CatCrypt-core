/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Assumptions.CR
public import CatCryptCore.NonUniform.UnaryRules

/-!
# Collision-search adversaries given by coins

A collision-search adversary that draws coins `c` from a probability mass function `ρ` and
outputs the pair `f k c` under the key `k` is `CR_Search_Adversary.ofCoins ρ f`. Its
advantage is a probability over the product of the uniform key and the coins.

## Main definitions

* `CR_Search_Adversary.ofCoins` — the adversary sampling coins from `ρ` and outputting
  `f k c`

## Main results

* `CR_Search_Advantage_ofCoins` — the advantage of `ofCoins ρ f` is the probability, over
  a uniform key `k` and coins `c ∼ ρ`, that `f k c` is a pair of distinct inputs with the
  same hash
* `CR_Search_Advantage_ofCoins_le` — a bound on the collision probability under every key
  bounds the advantage
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Assumptions

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.NonUniform
open CatCrypt.Crypto.ForkingLemma
open scoped ENNReal

variable {h : HashScheme} {C : Type}

/-- The collision-search adversary that samples coins `c` from `ρ` and outputs `f k c`
under the key `k`. -/
noncomputable def CR_Search_Adversary.ofCoins (ρ : PMF C)
    (f : h.Key → C → h.Input × h.Input) : CR_Search_Adversary h :=
  fun k => SPComp.bind (sampleFrom (ofPMF ρ)) (SPComp.pure ∘ f k)

/-- The collision event of the pair `f k c`: distinct inputs with the same hash under
`k`. -/
def coinsCollision (f : h.Key → C → h.Input × h.Input) (k : h.Key) (c : C) : Bool :=
  decide (h.hash k (f k c).1 = h.hash k (f k c).2 ∧ (f k c).1 ≠ (f k c).2)

/-- The advantage of `ofCoins ρ f` is the probability, over a uniform key `k` and coins
`c ∼ ρ`, that `f k c` is a pair of distinct inputs with the same hash under `k`. -/
theorem CR_Search_Advantage_ofCoins (ρ : PMF C) (f : h.Key → C → h.Input × h.Input) :
    CR_Search_Advantage h (CR_Search_Adversary.ofCoins ρ f) =
      ((PMF.uniformFintype h.Key).bind fun k => ρ.map (coinsCollision f k)) true := by
  unfold CR_Search_Advantage CR_Search_Game CR_Search_Adversary.ofCoins
  rw [show SPComp.sample h.Key = sampleFrom (ofPMF (PMF.uniformFintype h.Key)) from rfl]
  simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, Function.comp_apply, SPComp.pure_bind]
  rw [prTrue_bind_sampleFrom, PMF.bind_apply]
  refine tsum_congr fun k => ?_
  rw [ofPMF_apply_some, prTrue_bind_sampleFrom, PMF.map_apply]
  congr 1
  refine tsum_congr fun c => ?_
  rw [ofPMF_apply_some]
  rcases hfc : f k c with ⟨x₁, x₂⟩
  simp [coinsCollision, hfc, prTrue_pure_bool]

/-- If under every key the coins give a collision with probability at most `ε`, the
advantage of `ofCoins ρ f` is at most `ε`. -/
theorem CR_Search_Advantage_ofCoins_le (ρ : PMF C) (f : h.Key → C → h.Input × h.Input)
    (ε : ℝ≥0∞) (hε : ∀ k, ρ.map (coinsCollision f k) true ≤ ε) :
    CR_Search_Advantage h (CR_Search_Adversary.ofCoins ρ f) ≤ ε := by
  rw [CR_Search_Advantage_ofCoins, PMF.bind_apply]
  calc ∑' k, PMF.uniformFintype h.Key k * ρ.map (coinsCollision f k) true
      ≤ ∑' k, PMF.uniformFintype h.Key k * ε :=
        ENNReal.tsum_le_tsum fun k => by gcongr; exact hε k
    _ = ε := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end CatCrypt.Crypto.Assumptions
