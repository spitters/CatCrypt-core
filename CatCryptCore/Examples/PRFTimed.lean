/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.PRF
public import CatCryptCore.Tactics.DeriveTimed

/-!
# Time of the inner cascade reduction

The costed forms of the reduction `cascadeRedInner` of `CatCryptCore.Examples.PRF` and of the
answer map `mapAns`, derived by `derive_timed`. The reduction samples the outer key and runs
the adversary with every answer mapped by `F k₂`; `mapAns` is a structural recursion over the
oracle tree, so its costed form is a recursion over the costed tree of the adversary, whose time
follows from `OracleAdv.Timed.timeBound_fold`.

## Cost model

The registered costs of `CatCryptCore.Crypto.OracleAdversaryTimed`: one unit per `rand` and
per `query` node; `F k x` costs `FCost k x`, its cost companion; the rules of
`CatCryptCore.Tactics.DeriveTimed` for the bookkeeping.

## Main results

* `mapAns.timeBound_timed` — answers mapped by `f`, each evaluation of `f` costing at most
  `e`: time `(5 + e) * T + 1`
* `cascadeRedInner.timeBound_timed` — an adversary of time `T` gives a reduction of time
  `(6 + e) * T + 3` when every evaluation of `F` costs at most `e`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Examples.PRF

open CatCrypt.Crypto

derive_timed mapAns

derive_timed cascadeRedInner

/-- An adversary of time `T` with every answer mapped by `f`, each evaluation of `f` costing
at most `e`, runs in time at most `(5 + e) * T + 1`. -/
theorem mapAns.timeBound_timed {D R R' α : Type} (f : R → R') (fCost : R → ℕ) {e : ℕ}
    (he : ∀ x, fCost x ≤ e) {A : OracleAdv.Timed D R' α} {n : ℕ} (hA : A.TimeBound n) :
    OracleAdv.Timed.StepTimeBound (mapAns.timed f fCost A) ((5 + e) * n + 1) := by
  have key : ∀ x, 5 + e + x ≤ (1 + (4 + e)) * (1 + x) := fun x => by
    rw [Nat.mul_add, Nat.mul_one]
    have := Nat.le_mul_of_pos_left x (show 0 < 1 + (4 + e) by omega)
    omega
  have h := OracleAdv.Timed.timeBound_fold (h := 4 + e) (r := 1)
    (fun A (_ : Unit) => mapAns.timed f fCost A) ?_ ?_ ?_ hA ()
  · rwa [show 1 + (4 + e) = 5 + e by omega] at h
  · intro a s
    exact ⟨by simp only [mapAns.timed]; omega, trivial⟩
  · intro γ p c k s M hM0 hM hk
    rw [mapAns.timed]
    simp only [OracleAdv.Timed.StepTimeBound, OracleAdv.Timed.TimeBound]
    refine ⟨by omega, by omega, fun b => ?_⟩
    have h1 := hM b
    have h2 := hk b ()
    have h4 := key (c b)
    exact ⟨by have := h2.1; omega, h2.2.mono (by omega)⟩
  · intro d c k s M hM0 hM hk
    rw [mapAns.timed]
    simp only [OracleAdv.Timed.StepTimeBound, OracleAdv.Timed.TimeBound]
    refine ⟨by omega, by omega, fun b => ?_⟩
    have h1 := hM (f b)
    have h2 := hk (f b) ()
    have h3 := he b
    have h4 := key (c (f b))
    exact ⟨by have := h2.1; omega, h2.2.mono (by omega)⟩

/-- **Time of the inner cascade reduction.** An adversary of time `T` gives a reduction of
time at most `(6 + e) * T + 3` when every evaluation of `F` costs at most `e`. -/
theorem cascadeRedInner.timeBound_timed {K D : Type} [Fintype K] [Nonempty K] (F : K → D → D)
    (FCost : K → D → ℕ) {e : ℕ} (he : ∀ k x, FCost k x ≤ e)
    {A : OracleAdv.Timed D D Bool} {n : ℕ} (hA : A.TimeBound n) :
    OracleAdv.Timed.StepTimeBound (cascadeRedInner.timed F FCost A) ((6 + e) * n + 3) := by
  refine ⟨Nat.zero_le _, ?_⟩
  simp only [cascadeRedInner.timed, OracleAdv.Timed.TimeBound]
  refine ⟨by omega, fun k₂ => ?_⟩
  have h := mapAns.timeBound_timed (F k₂) (fun a => 1 + FCost k₂ a) (e := 1 + e)
    (fun x => by have := he k₂ x; omega) hA
  rw [show 5 + (1 + e) = 6 + e by omega] at h
  exact ⟨by have := h.1; omega, h.2.mono (by omega)⟩

end CatCrypt.Examples.PRF
