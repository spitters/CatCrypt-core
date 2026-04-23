/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Bridges.VCVioBridge.Monad
import CatCrypt.Crypto.Advantage

/-!
# VCVio Bridge — Relational / Advantage transfer (Phase 4)

Bridges VCVio's probability-level reasoning (`Pr[= x | mx]`, `evalDist`) to
CatCrypt's relational and advantage-level reasoning (`Advantage`, `prTrue`) via
`probCompLift`.

The main content is the **probability-preservation lemma**: the probability that
`probCompLift mx` returns `true` from the empty heap is exactly `Pr[= true | mx]`.
This is what makes VCVio's quantitative reductions transfer into CatCrypt
`Advantage` bounds.

## Main results

* `probCompLift_apply` — pointwise evaluation of `probCompLift mx h`
* `prTrue_probCompLift` — `prTrue (probCompLift mx) Heap.empty = Pr[= true | mx]`
* `advantage_probCompLift_le_of_probOutput_diff` — VCVio probability bounds
  transfer to CatCrypt advantage bounds

## Note on the full `RelTriple ↔ rHoare` equivalence

Upstream VCVio's relational program logic (`VCVio.ProgramLogic.Relational`) is
built on `SPMF.Coupling`; CatCrypt's `rHoare` (`CatCrypt.Relational.Judgment`)
is built on `CatCrypt.Prob.Coupling`. The two coupling structures carry the same
information but differ in how the marginal laws are stated. A full
isomorphism proof is out of scope here — the quantitative bridges in this file
cover the primary use case (transferring VCVio advantage bounds into CatCrypt
`Advantage` / `UCEmulates` statements).
-/

namespace CatCrypt.Crypto.VCVioBridge

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

/-! ## Pointwise evaluation of `probCompLift` -/

/-- Evaluating `probCompLift mx` at an output `(a, h')` starting from heap `h`:
    the heap must be unchanged (`h = h'`) and the probability is that of `mx`
    returning `a`. For any other final heap, the probability is `0`. -/
theorem probCompLift_apply {α : Type} (mx : ProbComp α) (h h' : Heap) (a : α) :
    (probCompLift mx h) (some (a, h')) =
      if h = h' then ProbComp.toSDistr mx (some a) else 0 := by
  unfold probCompLift sdistrToSPComp
  show (SDistr.bind (ProbComp.toSDistr mx) (fun a' => SDistr.pure (a', h))) _ = _
  unfold SDistr.bind SDistr.pure SDistr.fail
  rw [PMF.bind_apply]
  -- Goal: ∑' oa, (ProbComp.toSDistr mx) oa *
  --       (match oa with | some a' => PMF.pure (some (a', h)) | none => PMF.pure none)
  --         (some (a, h'))
  --    = if h = h' then ProbComp.toSDistr mx (some a) else 0
  rw [tsum_option_split]
  simp only [PMF.pure_apply, reduceCtorEq, ite_false, mul_zero, zero_add]
  -- Goal: ∑' a', mx (some a') * (if some (a', h) = some (a, h') then 1 else 0)
  --     = if h = h' then mx (some a) else 0
  by_cases hh : h = h'
  · subst hh
    simp only [ite_true]
    rw [tsum_eq_single a]
    · simp
    · intro b hb
      simp [Ne.symm hb]
  · simp only [hh, ite_false]
    -- Every summand is zero since (a', h) = (a, h') would force h = h'.
    apply ENNReal.tsum_eq_zero.mpr
    intro a'
    rcases eq_or_ne a' a with rfl | hne_a
    · simp [Ne.symm hh]
    · simp [Ne.symm hne_a]

/-! ## Probability preservation -/

/-- The key compatibility lemma: the probability that `probCompLift mx` returns
    `true` (starting from the empty heap) is exactly the VCVio `Pr[= true | mx]`.

    This is the identity that lets VCVio's probability bounds transfer to
    CatCrypt's `Advantage` statements. -/
theorem prTrue_probCompLift (mx : ProbComp Bool) :
    prTrue (probCompLift mx) Heap.empty = Pr[= true | mx] := by
  unfold prTrue
  -- Goal: ∑' h, (probCompLift mx Heap.empty) (some (true, h)) = Pr[= true | mx]
  have heq : ∀ h, (probCompLift mx Heap.empty) (some (true, h))
                 = if Heap.empty = h then ProbComp.toSDistr mx (some true) else 0 :=
    fun h => probCompLift_apply mx Heap.empty h true
  rw [tsum_congr heq]
  rw [tsum_eq_single Heap.empty]
  · simp
    rfl
  · intro h hne
    simp [Ne.symm hne]

/-! ## Advantage transfer -/

/-- VCVio probability bounds transfer to CatCrypt advantage bounds. If two
    `ProbComp Bool` games have `Pr[= true | ·]` differing by at most `ε`, then
    their `probCompLift`s have `Advantage` at most `ε`. -/
theorem advantage_probCompLift_le_of_probOutput_diff
    (mx₀ mx₁ : ProbComp Bool) {ε : ℝ≥0∞}
    (h₀ : Pr[= true | mx₀] - Pr[= true | mx₁] ≤ ε)
    (h₁ : Pr[= true | mx₁] - Pr[= true | mx₀] ≤ ε) :
    Advantage (probCompLift mx₀) (probCompLift mx₁) ≤ ε := by
  unfold Advantage
  simp only [prTrue_probCompLift]
  exact max_le h₀ h₁

/-- Perfect-indistinguishability transfer: equal `evalDist` implies zero
    `Advantage` on the lifts. -/
theorem advantage_probCompLift_eq_zero_of_evalDist_eq
    (mx₀ mx₁ : ProbComp Bool) (h : evalDist mx₀ = evalDist mx₁) :
    Advantage (probCompLift mx₀) (probCompLift mx₁) = 0 := by
  unfold Advantage
  simp only [prTrue_probCompLift, probOutput_def, h]
  simp

end CatCrypt.Crypto.VCVioBridge
