/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.PRF
import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Tactics.DeriveTimed.Basic
public import CatCryptCore.Tactics.StdCosts

/-!
# Time of the cascade reductions

The costed forms of the reductions `cascadeRedInner` and `cascadeRedOuter` of
`CatCryptCore.Examples.PRF`, of the answer map `mapAns` and of the simulated random injection
`simRP`, derived by `derive_timed`, with their erasure theorems. The inner reduction samples
the outer key and runs the adversary with every answer mapped by `F k₂`; `mapAns` is a
structural recursion over the oracle tree, so its costed form is a recursion over the costed
tree of the adversary, whose time follows from `OracleAdv.Timed.timeBound_fold`.

The outer reduction runs the adversary through `simRP`, a structural recursion over the oracle
tree that keeps the table of a lazily sampled random injection: a query is looked up in the
table, and a new query draws a fresh answer outside the used answers. The cost of a node grows
with the table, whose length is at most the length of the initial table plus the time of the
adversary, so the time is cubic in the time of the adversary. `derive_time_rec simRP` with this
bound states the theorem but does not prove it: `time_bound` leaves the arithmetic leaf
`0 + 1 + 1 ≤ T * P + 1` of the `rand` case open, which needs `1 ≤ T` from the time bound of the
adversary and a product of two variables. The theorem `simRP.timeBound` is proved by induction
on the adversary from the costed form, with the step `simRPTime_step`.

## Cost model

The registered costs of `CatCryptCore.Crypto.OracleAdversaryTimed`: one unit per `rand` and
per `query` node; `F k x` costs `FCost k x`, its cost companion; the rules of
`CatCryptCore.Tactics.DeriveTimed` for the bookkeeping; the registered costs of
`CatCryptCore.Tactics.StdCosts` for the lookup in the table (`List.lookup`, a comparison at one
unit), the set of used answers (`List.map`, `List.toFinset`) and the enumeration of the domain
(`Finset.univ`, its cardinality). The test that a fresh answer exists,
`(PRPPRF.usedAnswers t)ᶜ.Nonempty`, is a definition valued in `Prop` and costs one unit and its
data arguments (`derive_timed.priceProps`).

## Main results

* `mapAns.timeBound_timed` — answers mapped by `f`, each evaluation of `f` costing at most
  `e`: time `(5 + e) * T + 1`
* `cascadeRedInner.timeBound_timed` — an adversary of time `T` gives a reduction of time
  `(6 + e) * T + 3` when every evaluation of `F` costs at most `e`
* `simRP.timeBound` — on a table of length `l`, an adversary of time `T` on a domain of `N`
  elements is simulated in time at most `simRPTime N l T`
* `cascadeRedOuter.timeBound` — an adversary of time `T` gives a reduction of time
  `T * (T ^ 2 + 10 * T + 2 * N + 30) + 2`
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

derive_timed simRP

derive_timed cascadeRedOuter

/-- The time bound of `simRP t A`, for a table `t` of length `l` and an adversary `A` of time
`T` on a domain of `N` elements: each of the at most `T` nodes of `A` is charged, besides its own
step, at most `P = L ^ 2 + 10 * L + 2 * N + 30` with `L = l + T`, which bounds the lookup in the
table, the set of used answers and the enumerations of the domain, since the table has length at
most `L` throughout the run. -/
def simRPTime (N l T : ℕ) : ℕ := T * ((l + T) ^ 2 + 10 * (l + T) + 2 * N + 30) + 1

/-- One node of the adversary with step cost `c` and overhead `o` at most `P`, followed by the
simulation of a continuation of time `T'` on a table of length `l' ≤ l + 1`, fits the bound at
time `T' + 1 + c`. -/
theorem simRPTime_step {N l l' T' c o : ℕ} (hl : l' ≤ l + 1)
    (ho : o ≤ (l + (T' + 1 + c)) ^ 2 + 10 * (l + (T' + 1 + c)) + 2 * N + 30) :
    o + c + simRPTime N l' T' ≤ simRPTime N l (T' + 1 + c) := by
  unfold simRPTime
  set P := (l + (T' + 1 + c)) ^ 2 + 10 * (l + (T' + 1 + c)) + 2 * N + 30
  have hP' : (l' + T') ^ 2 + 10 * (l' + T') + 2 * N + 30 ≤ P := by
    have h : l' + T' ≤ l + (T' + 1 + c) := by omega
    have := Nat.pow_le_pow_left h 2
    omega
  have h1 : T' * ((l' + T') ^ 2 + 10 * (l' + T') + 2 * N + 30) ≤ T' * P :=
    Nat.mul_le_mul_left _ hP'
  have h2 : c ≤ c * P := Nat.le_mul_of_pos_right c (by omega)
  have h3 : (T' + 1 + c) * P = T' * P + P + c * P := by ring
  omega

open CatCrypt.Crypto.OracleAdv.Timed in
/-- **Time of the simulated random injection.** On a table of length `l`, the simulation of an
adversary of time `T` runs in time at most `simRPTime N l T`, at most `T * (P + 1)` with
`P = (l + T) ^ 2 + 10 * (l + T) + 2 * N + 30` for a domain of `N` elements: cubic in the time
of the adversary on an empty table. -/
theorem simRP.timeBound {D : Type} [Fintype D] [Nonempty D] [DecidableEq D] {α : Type}
    (A : OracleAdv.Timed D D α) (t : List (D × D)) {T : ℕ} (hA : A.TimeBound T) :
    StepTimeBound (simRP.timed t A) (simRPTime (Fintype.card D) t.length T) := by
  induction A generalizing t T with
  | ret a =>
    rw [simRP.timed]; dsimp only
    exact ⟨by unfold simRPTime; omega, trivial⟩
  | rand p c k ih =>
    obtain ⟨hT, hk⟩ := hA
    have key : ∀ b, 4 + c b + simRPTime (Fintype.card D) t.length (T - 1 - c b) ≤
        simRPTime (Fintype.card D) t.length T := fun b => by
      have e : T = (T - 1 - c b) + 1 + c b := by have := (hk b).1; omega
      conv_rhs => rw [e]
      exact simRPTime_step (by omega) (by omega)
    rw [simRP.timed]; dsimp only
    have hb : ∃ b, b ∈ p.support := p.support_nonempty
    obtain ⟨b₀, -⟩ := hb
    have h₀ := key b₀
    refine ⟨by omega, by omega, fun b => ?_⟩
    obtain ⟨h1, h2⟩ := ih b t (hk b).2
    have := key b
    refine ⟨by dsimp only; omega, h2.mono ?_⟩
    dsimp only
    omega
  | query d c k ih =>
    obtain ⟨hT, hk⟩ := hA
    have hL := List.lookup.timedCost_le d t
    have hM := List.map.timedCost_le Prod.snd (fun _ => 0) (k := 0) (fun _ => le_rfl) t
    have hX : ∀ y, ∀ o ≤ t.length ^ 2 + 9 * t.length + 2 * Fintype.card D + 22,
        o + c y + simRPTime (Fintype.card D) (t.length + 1) (T - 1 - c y) ≤
          simRPTime (Fintype.card D) t.length T := fun y o ho => by
      have e : T = (T - 1 - c y) + 1 + c y := by have := (hk y).1; omega
      conv_rhs => rw [e]
      refine simRPTime_step le_rfl (ho.trans ?_)
      have := Nat.pow_le_pow_left (show t.length ≤ t.length + (T - 1 - c y + 1 + c y) by omega) 2
      omega
    have hS : ∀ y, ∀ o ≤ t.length ^ 2 + 9 * t.length + 2 * Fintype.card D + 21,
        o + c y + simRPTime (Fintype.card D) t.length (T - 1 - c y) ≤
          simRPTime (Fintype.card D) t.length T := fun y o ho => by
      have e : T = (T - 1 - c y) + 1 + c y := by have := (hk y).1; omega
      conv_rhs => rw [e]
      refine simRPTime_step (by omega) (ho.trans ?_)
      have := Nat.pow_le_pow_left (show t.length ≤ t.length + (T - 1 - c y + 1 + c y) by omega) 2
      omega
    obtain ⟨y₀⟩ := (inferInstance : Nonempty D)
    have hU : Finset.univ.timedCost D = Fintype.card D := by simp [Finset.univ.timedCost]
    have hF : List.toFinset.timedCost D (List.map Prod.snd t) = t.length ^ 2 + t.length + 1 := by
      simp only [List.toFinset.timedCost, List.length_map]
      ring
    have hI : (if h : (PRPPRF.usedAnswers t)ᶜ.Nonempty then 1 + (2 + Finset.univ.timedCost D + 1)
        else 0) ≤ Fintype.card D + 4 := by
      split <;> omega
    rw [simRP.timed]; dsimp only
    split
    · simp only [delay, StepTimeBound, OracleAdv.Timed.TimeBound]
      have := hS y₀ (6 + List.lookup.timedCost d t) (by omega)
      refine ⟨by omega, by omega, fun y => ?_⟩
      obtain ⟨h1, h2⟩ := ih y t (hk y).2
      have := hS y (6 + List.lookup.timedCost d t) (by omega)
      exact ⟨by omega, h2.mono (by omega)⟩
    · simp only [delay, StepTimeBound, OracleAdv.Timed.TimeBound]
      have := hX y₀ _ (le_refl (t.length ^ 2 + 9 * t.length + 2 * Fintype.card D + 22))
      refine ⟨by omega, by omega, fun r => ⟨by omega, by omega, fun y => ?_⟩⟩
      obtain ⟨h1, h2⟩ := ih y ((d, r) :: t) (hk y).2
      rw [List.length_cons] at h1 h2
      have := hX y _ (le_refl (t.length ^ 2 + 9 * t.length + 2 * Fintype.card D + 22))
      exact ⟨by omega, h2.mono (by omega)⟩

open CatCrypt.Crypto.OracleAdv.Timed in
/-- **Time of the outer cascade reduction.** An adversary of time `T` on a domain of `N`
elements gives a reduction of time at most `T * (T ^ 2 + 10 * T + 2 * N + 30) + 2`: the
simulated random injection starts from the empty table. -/
theorem cascadeRedOuter.timeBound {D : Type} [Fintype D] [Nonempty D] [DecidableEq D]
    (A : OracleAdv.Timed D D Bool) {T : ℕ} (hA : A.TimeBound T) :
    StepTimeBound (cascadeRedOuter.timed A)
      (T * (T ^ 2 + 10 * T + 2 * Fintype.card D + 30) + 2) := by
  rw [cascadeRedOuter.timed]
  refine (stepTimeBound_delay (c := 1) (simRP.timeBound A [] hA)).mono ?_
  simp only [simRPTime, List.length_nil, Nat.zero_add]
  omega

end CatCrypt.Examples.PRF
