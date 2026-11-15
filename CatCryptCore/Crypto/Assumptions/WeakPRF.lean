/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.CyclicGroupDDH
public import CatCryptCore.Crypto.HybridArgument
public import CatCryptCore.Crypto.GeneralForkingLemma
public import CatCryptCore.Relational.DeadSample

/-!
# Weak pseudorandom functions, and `x ↦ x^k` as a weak PRF under DDH

A function family `f : K → X → Y` is a weak PRF when, for a uniform key `k`, the samples
`(x_i, f k x_i)` at `q` uniform points `x_i` are indistinguishable from `q` uniform pairs
`(x_i, y_i)`. The adversary chooses no input; it receives the `q` samples at once.

For a cyclic group `G` of exponent ring `Exp`, the family `x ↦ x^k` (`expFn G`) is a weak PRF
under DDH (Chase, Perrin, Zaverucha, CCS 2020, Theorem 5). The proof is a hybrid over the `q`
positions: the hybrid `i` has uniform outputs below the position `i` and the outputs `x^k` from
`i` on. The reduction of the hop `i` (`wprfHybRed`), on a DDH triple `(X, Y, Z)`, draws
exponents `r_j, s_j` for the other positions, uses the points `g^{r_j}`, the uniform outputs
`g^{s_j}` below `i` and the outputs `X^{r_j}` above `i`, puts `(Y, Z)` at the position `i`, and
runs the adversary. On a real triple `X = g^a` plays the key `a` and `Y = g^b` the point at `i`;
on an ideal triple `Z` is the uniform output at `i`.

## Main definitions

* `WeakPRF_Real`, `WeakPRF_Ideal`, `WeakPRF_Advantage` — the weak-PRF game for `q` samples
* `expFn G` — the family `x ↦ x^k` over a cyclic group
* `WeakPRF.wprfHybRed` — the DDH reduction of the hop `i`

## Main results

* `WeakPRF.expFn_advantage_le` — for every adversary `A` making `q` samples,
  `WeakPRF_Advantage (expFn G) q A ≤ ∑ i : Fin q, DDH_Advantage G (wprfHybRed A i)`

## References

* M. Chase, T. Perrin, G. Zaverucha, *The Signal Private Group System and Anonymous
  Credentials Supporting Efficient Verifiable Encryption*, CCS 2020, Theorem 5
* D. Naor, O. Reingold, *Number-theoretic constructions of efficient pseudo-random functions*,
  FOCS 1997 (DDH and the function `x ↦ x^k`)
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Assumptions

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCryptCore.Examples.CyclicGroupDDH
open scoped ENNReal

/-! ## The weak-PRF game -/

section Game

variable {K X Y : Type} [Fintype K] [Nonempty K] [Fintype X] [Nonempty X] [Fintype Y]
  [Nonempty Y]

/-- The real weak-PRF game for `q` samples: a uniform key `k` and `q` uniform points `x_i`,
shown with the values `f k x_i`. -/
noncomputable def WeakPRF_Real (f : K → X → Y) (q : ℕ) : SPComp (Fin q → X × Y) :=
  SPComp.bind (SPComp.sample K) fun k => SPComp.bind (SPComp.sample (Fin q → X)) fun xs =>
    SPComp.pure fun j => (xs j, f k (xs j))

/-- The ideal weak-PRF game for `q` samples: `q` uniform pairs `(x_i, y_i)`. -/
noncomputable def WeakPRF_Ideal (X Y : Type) [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (q : ℕ) : SPComp (Fin q → X × Y) :=
  SPComp.bind (SPComp.sample (Fin q → X)) fun xs => SPComp.bind (SPComp.sample (Fin q → Y))
    fun ys => SPComp.pure fun j => (xs j, ys j)

/-- The weak-PRF advantage of the distinguisher `A` against `f` with `q` samples. -/
noncomputable def WeakPRF_Advantage (f : K → X → Y) (q : ℕ) (A : (Fin q → X × Y) → SPComp Bool) :
    ℝ≥0∞ :=
  AdvantageA (WeakPRF_Real f q) (WeakPRF_Ideal X Y q) A

end Game

/-! ## The family `x ↦ x^k` over a cyclic group -/

/-- The family `x ↦ x^k` over the cyclic group `G`, keyed by an exponent `k`. -/
noncomputable def expFn (G : Type) [CG : CyclicGroup G] (k : CG.Exp) (x : G) : G :=
  CyclicGroup.elemPow x k

namespace WeakPRF

variable {G : Type} [CG : CyclicGroup G] {q : ℕ}

/-- The points of the reduction of the hop `i` with the DDH value `X`: the point `g^{r_j}`,
with the uniform output `g^{s_j}` below `i` and the output `X^{r_j}` from `i` on. -/
noncomputable def redPts (X : G) (i : ℕ) (r s : Fin q → CG.Exp) : Fin q → G × G :=
  fun j => (CG.pow (r j), if j.val < i then CG.pow (s j) else CyclicGroup.elemPow X (r j))

/-- The hybrid game `i`: a uniform key `a`, and the points `redPts (g^a) i r s` for uniform
exponents `r, s`. -/
noncomputable def hybN (A : (Fin q → G × G) → SPComp Bool) (i : ℕ) : SPComp Bool :=
  SPComp.bind (SPComp.sample CG.Exp) fun a => SPComp.bind (SPComp.sample (Fin q → CG.Exp))
    fun r => SPComp.bind (SPComp.sample (Fin q → CG.Exp)) fun s =>
      A (redPts (CG.pow a) i r s)

/-- **The reduction of the hop `i` to DDH.** On a triple `(X, Y, Z)`, draw exponents `r, s`,
put `(Y, Z)` at the position `i` of `redPts X i r s`, and run `A`. -/
noncomputable def wprfHybRed (A : (Fin q → G × G) → SPComp Bool) (i : Fin q)
    (ch : DDHTriple G) : SPComp Bool :=
  SPComp.bind (SPComp.sample (Fin q → CG.Exp)) fun r =>
    SPComp.bind (SPComp.sample (Fin q → CG.Exp)) fun s =>
      A (Function.update (redPts ch.1 i r s) i (ch.2.1, ch.2.2))

/-- A real DDH value at the position `i` gives the points of the hybrid `i` at the updated
exponents. -/
theorem update_redPts_real (i : Fin q) (r s : Fin q → CG.Exp) (a b : CG.Exp) :
    Function.update (redPts (CG.pow a) i r s) i (CG.pow b, CG.pow (CG.expMul a b)) =
      redPts (CG.pow a) i (Function.update r i b) s := by
  funext j
  rcases eq_or_ne j i with rfl | h
  · simp [redPts, CyclicGroup.elemPow_pow]
  · simp [redPts, Function.update_of_ne h]

/-- A uniform DDH value at the position `i` gives the points of the hybrid `i + 1` at the
updated exponents. -/
theorem update_redPts_ideal (X : G) (i : Fin q) (r s : Fin q → CG.Exp) (b c : CG.Exp) :
    Function.update (redPts X i r s) i (CG.pow b, CG.pow c) =
      redPts X (i + 1) (Function.update r i b) (Function.update s i c) := by
  funext j
  rcases eq_or_ne j i with rfl | h
  · simp [redPts]
  · have hv : j.val ≠ i.val := fun h' => h (Fin.ext h')
    by_cases hj : j.val < i.val
    · simp [redPts, Function.update_of_ne h, hj, Nat.lt_succ_of_lt hj]
    · have hj' : ¬ j.val < i.val + 1 := by omega
      simp [redPts, Function.update_of_ne h, hj, hj']

/-- Drawing a value at the position `i` of two uniform exponent families, in either order. -/
theorem sample_update₂ (i : Fin q) (K : (Fin q → CG.Exp) → (Fin q → CG.Exp) → SPComp Bool) :
    (SPComp.bind (SPComp.sample CG.Exp) fun b => SPComp.bind (SPComp.sample CG.Exp) fun c =>
      SPComp.bind (SPComp.sample (Fin q → CG.Exp)) fun r =>
        SPComp.bind (SPComp.sample (Fin q → CG.Exp)) fun s =>
          K (Function.update r i b) (Function.update s i c)) =
      SPComp.bind (SPComp.sample (Fin q → CG.Exp)) fun r =>
        SPComp.bind (SPComp.sample (Fin q → CG.Exp)) fun s => K r s := by
  have h1 : ∀ b : CG.Exp, (SPComp.bind (SPComp.sample CG.Exp) fun c =>
      SPComp.bind (SPComp.sample (Fin q → CG.Exp)) fun r =>
        SPComp.bind (SPComp.sample (Fin q → CG.Exp)) fun s =>
          K (Function.update r i b) (Function.update s i c)) =
      SPComp.bind (SPComp.sample (Fin q → CG.Exp)) fun r =>
        SPComp.bind (SPComp.sample (Fin q → CG.Exp)) fun s => K (Function.update r i b) s := by
    intro b
    rw [SPComp.isPure_bind_comm_left _ _ _ (SPComp.sample_isPure _)]
    congr 1
    funext r
    rw [SPComp.isPure_bind_comm_left _ _ _ (SPComp.sample_isPure _)]
    exact GeneralForkingLemma.sample_update_eq_sample i fun s => K (Function.update r i b) s
  simp only [h1]
  rw [SPComp.isPure_bind_comm_left _ _ _ (SPComp.sample_isPure _)]
  exact GeneralForkingLemma.sample_update_eq_sample i fun r =>
    SPComp.bind (SPComp.sample (Fin q → CG.Exp)) fun s => K r s

/-- The real DDH game against the reduction of the hop `i` is the hybrid `i`. -/
theorem ddhReal_bind_wprfHybRed (A : (Fin q → G × G) → SPComp Bool) (i : Fin q) :
    SPComp.bind (DDH_real G) (wprfHybRed A i) = hybN A i := by
  simp only [DDH_real, bind, pure, SPComp.bind_assoc, SPComp.pure_bind, wprfHybRed,
    update_redPts_real]
  unfold hybN
  congr 1
  funext a
  rw [SPComp.isPure_bind_comm_left _ _ _ (SPComp.sample_isPure _)]
  exact GeneralForkingLemma.sample_update_eq_sample i fun r =>
    SPComp.bind (SPComp.sample (Fin q → CG.Exp)) fun s => A (redPts (CG.pow a) i r s)

/-- The ideal DDH game against the reduction of the hop `i` is the hybrid `i + 1`. -/
theorem ddhIdeal_bind_wprfHybRed (A : (Fin q → G × G) → SPComp Bool) (i : Fin q) :
    SPComp.bind (DDH_ideal G) (wprfHybRed A i) = hybN A (i + 1) := by
  simp only [DDH_ideal, bind, pure, SPComp.bind_assoc, SPComp.pure_bind, wprfHybRed,
    update_redPts_ideal]
  unfold hybN
  congr 1
  funext a
  exact sample_update₂ i fun r s => A (redPts (CG.pow a) (i + 1) r s)

/-- The hybrid `0` is the real weak-PRF game of `expFn G`. -/
theorem hybN_zero (A : (Fin q → G × G) → SPComp Bool) :
    hybN A 0 = SPComp.bind (WeakPRF_Real (expFn G) q) A := by
  have hpts : ∀ (a : CG.Exp) (r s : Fin q → CG.Exp),
      redPts (CG.pow a) 0 r s = fun j => (CG.pow (r j), expFn G a (CG.pow (r j))) := by
    intro a r s
    funext j
    simp only [redPts, expFn, CyclicGroup.elemPow_pow, Nat.not_lt_zero, ite_false, CG.pow_comm]
  simp only [hybN, hpts, Relational.dead_sample, WeakPRF_Real, SPComp.bind_assoc,
    SPComp.pure_bind]
  congr 1
  funext a
  exact SPComp.sample_bind_equiv (Equiv.arrowCongr (Equiv.refl _)
    (Equiv.ofBijective CG.pow CG.pow_bij)) fun xs => A fun j => (xs j, expFn G a (xs j))

/-- The hybrid `q` is the ideal weak-PRF game. -/
theorem hybN_last (A : (Fin q → G × G) → SPComp Bool) :
    hybN A q = SPComp.bind (WeakPRF_Ideal G G q) A := by
  have hpts : ∀ (a : CG.Exp) (r s : Fin q → CG.Exp),
      redPts (CG.pow a) q r s = fun j => (CG.pow (r j), CG.pow (s j)) := by
    intro a r s
    funext j
    simp [redPts, j.isLt]
  let e : (Fin q → CG.Exp) ≃ (Fin q → G) :=
    Equiv.arrowCongr (Equiv.refl _) (Equiv.ofBijective CG.pow CG.pow_bij)
  simp only [hybN, hpts, Relational.dead_sample, WeakPRF_Ideal, SPComp.bind_assoc,
    SPComp.pure_bind]
  rw [← SPComp.sample_bind_equiv e]
  congr 1
  funext r
  rw [← SPComp.sample_bind_equiv e]
  rfl

/-- **`x ↦ x^k` is a weak PRF under DDH** (Chase, Perrin, Zaverucha, CCS 2020, Theorem 5).
For every distinguisher `A` receiving `q` samples, the weak-PRF advantage against `expFn G` is
at most the sum over the positions `i` of the DDH advantages of the hop reductions
`wprfHybRed A i`. -/
theorem expFn_advantage_le (A : (Fin q → G × G) → SPComp Bool) :
    WeakPRF_Advantage (expFn G) q A ≤ ∑ i : Fin q, DDH_Advantage G (wprfHybRed A i) := by
  have h := HybridArgument.advantage_hybrid_dep_bool (hybN A) q
  rw [hybN_zero, hybN_last] at h
  refine h.trans (le_of_eq ?_)
  rw [← Fin.sum_univ_eq_sum_range (fun i => Advantage (hybN A i) (hybN A (i + 1))) q]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [DDH_Advantage, AdvantageA, ddhReal_bind_wprfHybRed, ddhIdeal_bind_wprfHybRed]

end WeakPRF

end CatCrypt.Crypto.Assumptions
