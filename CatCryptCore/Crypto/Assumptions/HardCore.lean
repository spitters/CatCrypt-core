/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Advantage
public import CatCryptCore.Crypto.GeneralForkingLemma
public import CatCryptCore.Crypto.HybridArgument
public import CatCryptCore.Relational.DeadSample

/-!
# Hard-core functions of a trapdoor permutation

A trapdoor permutation family (`TDP`) with keys drawn from uniform coins `R` (`keyOf`),
evaluation keys `ek`, evaluation `eval`, inversion `inv` and a hard-core function `hc : D → M`
into a finite additive group `M`. The hard-core bit of Goldreich and Levin is the case
`M = ZMod 2`; IPDL's `HCBit.v` (Gancher, Sojakova, Fan, Shi and Morrisett, POPL 2023) states
the assumption in that case.

**The game.** `hcReal T` gives `(ek, eval ek w, hc w)` and `hcIdeal T` gives
`(ek, eval ek w, b)` for uniform coins of the key, a uniform preimage `w` and a uniform value
`b`; `HC_Advantage T A` is the distinguishing advantage of `A`.

**The game for `m` points.** `hcRealN T m` gives `(ek, (eval ek wⱼ, hc wⱼ)ⱼ)` and
`hcIdealN T m` gives `(ek, (eval ek wⱼ, bⱼ)ⱼ)` for uniform preimages `wⱼ` and values `bⱼ`,
under one evaluation key. IPDL's `HCBitPair_security` is the case `m = 2`.

**Bound.** For every distinguisher `A`, the advantage for `m` points is at most the sum over the
positions `i < m` of the hard-core advantages of the hop reductions `hcHybRed T A i`
(`HC_AdvantageN_le`). The hybrid `i` (`hybN`) carries uniform values below `i`; the reduction of
the hop `i` draws the preimages and values of the other positions, evaluates them with the key of
its challenge, and puts its challenge at the position `i`, so one challenge per hop suffices and
the shared key needs no trapdoor. The reduction draws one preimage and one value per position, a
vector of `m` samples. Its time certificate is in `HardCoreTimed.lean`.

## Main definitions

* `TDP`, `TDP.ekOf`: the trapdoor permutation family with a hard-core function.
* `hcReal`, `hcIdeal`, `HC_Advantage`: the hard-core game.
* `hcRealN`, `hcIdealN`, `HC_AdvantageN`: the game for `m` points.
* `hybPts`, `hybN`: the hybrids.
* `hcHybRed`: the reduction of the hop `i`.

## Main results

* `TDP.eval_injective`, `TDP.eval_inv`: evaluation with a trapdoor's key is a permutation.
* `hcReal_bind_hcHybRed`, `hcIdeal_bind_hcHybRed`: the hop `i` against the real and the ideal
  hard-core game is the hybrid `i` and `i + 1`.
* `HC_AdvantageN_le`: the advantage for `m` points is at most the sum of `m` hard-core
  advantages.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Assumptions.HardCore

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

/-! ## The trapdoor permutation and its hard-core function -/

/-- A trapdoor permutation family with a hard-core function: trapdoors from coins `R`, evaluation
keys `EK`, the domain `D` and the hard-core function `hc : D → M`. -/
structure TDP (R TK EK D M : Type) where
  /-- The trapdoor drawn from the coins. -/
  keyOf : R → TK
  /-- The evaluation key of a trapdoor. -/
  ek : TK → EK
  /-- Evaluation. -/
  eval : EK → D → D
  /-- Inversion with the trapdoor. -/
  inv : TK → D → D
  /-- Inversion cancels evaluation. -/
  inv_eval : ∀ tk x, inv tk (eval (ek tk) x) = x
  /-- The hard-core function. -/
  hc : D → M

variable {R TK EK D M : Type} [Fintype R] [Nonempty R] [Fintype D] [Nonempty D]
  [AddCommGroup M] [Fintype M]

namespace TDP

variable (T : TDP R TK EK D M)

/-- The evaluation key drawn from the coins `r`. -/
def ekOf (r : R) : EK := T.ek (T.keyOf r)

omit [Fintype R] [Nonempty R] [Fintype D] [Nonempty D] [AddCommGroup M] [Fintype M] in
/-- Evaluation with a trapdoor's key is injective. -/
theorem eval_injective (tk : TK) : Function.Injective (T.eval (T.ek tk)) := fun x y h => by
  rw [← T.inv_eval tk x, ← T.inv_eval tk y, h]

omit [Fintype R] [Nonempty R] [Nonempty D] [AddCommGroup M] [Fintype M] in
/-- Evaluation cancels inversion. -/
theorem eval_inv (tk : TK) (y : D) : T.eval (T.ek tk) (T.inv tk y) = y := by
  obtain ⟨x, rfl⟩ := (Finite.injective_iff_bijective.mp (T.eval_injective tk)).2 y
  rw [T.inv_eval]

end TDP

/-- The real challenge of the hard-core game drawn from the coins `r` and the preimage `w`. -/
def chReal (T : TDP R TK EK D M) (k : R × D) : EK × D × M :=
  (T.ekOf k.1, T.eval (T.ekOf k.1) k.2, T.hc k.2)

/-- The ideal challenge drawn from the coins `r`, the preimage `w` and the value `b`. -/
def chIdeal (T : TDP R TK EK D M) (k : R × D × M) : EK × D × M :=
  (T.ekOf k.1, T.eval (T.ekOf k.1) k.2.1, k.2.2)

/-- The real hard-core game: `(ek, eval ek w, hc w)` for a trapdoor and a uniform `w`. -/
noncomputable def hcReal (T : TDP R TK EK D M) : SPComp (EK × D × M) :=
  SPComp.bind (SPComp.sample (R × D)) fun k => SPComp.pure (chReal T k)

/-- The ideal hard-core game: `(ek, eval ek w, b)` for a uniform `b`. -/
noncomputable def hcIdeal (T : TDP R TK EK D M) : SPComp (EK × D × M) :=
  SPComp.bind (SPComp.sample (R × D × M)) fun k => SPComp.pure (chIdeal T k)

/-- The hard-core advantage of the distinguisher `A`. -/
noncomputable def HC_Advantage (T : TDP R TK EK D M) (A : EK × D × M → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (hcReal T) (hcIdeal T) A

variable {m : ℕ}

/-! ## The hard-core game for `m` points -/

/-- The real challenge for `m` points. -/
def chRealN (T : TDP R TK EK D M) (k : R × (Fin m → D)) : EK × (Fin m → D × M) :=
  (T.ekOf k.1, fun j => (T.eval (T.ekOf k.1) (k.2 j), T.hc (k.2 j)))

/-- The ideal challenge for `m` points. -/
def chIdealN (T : TDP R TK EK D M) (k : R × (Fin m → D) × (Fin m → M)) :
    EK × (Fin m → D × M) :=
  (T.ekOf k.1, fun j => (T.eval (T.ekOf k.1) (k.2.1 j), k.2.2 j))

/-- The real hard-core game for `m` points. -/
noncomputable def hcRealN (T : TDP R TK EK D M) (m : ℕ) : SPComp (EK × (Fin m → D × M)) :=
  SPComp.bind (SPComp.sample (R × (Fin m → D))) fun k => SPComp.pure (chRealN T k)

/-- The ideal hard-core game for `m` points. -/
noncomputable def hcIdealN (T : TDP R TK EK D M) (m : ℕ) : SPComp (EK × (Fin m → D × M)) :=
  SPComp.bind (SPComp.sample (R × (Fin m → D) × (Fin m → M))) fun k =>
    SPComp.pure (chIdealN T k)

/-- The hard-core advantage for `m` points of the distinguisher `A`. -/
noncomputable def HC_AdvantageN (T : TDP R TK EK D M) (A : EK × (Fin m → D × M) → SPComp Bool) :
    ℝ≥0∞ :=
  AdvantageA (hcRealN T m) (hcIdealN T m) A

/-- The points of the hybrid `i` with the key `e`: uniform values below `i`, hard-core values
from `i` on. -/
def hybPts (T : TDP R TK EK D M) (e : EK) (i : ℕ) (w : Fin m → D) (b : Fin m → M) :
    Fin m → D × M :=
  fun j => (T.eval e (w j), if j.val < i then b j else T.hc (w j))

/-- The hybrid game `i`. -/
noncomputable def hybN (T : TDP R TK EK D M) (A : EK × (Fin m → D × M) → SPComp Bool) (i : ℕ) :
    SPComp Bool :=
  SPComp.bind (SPComp.sample R) fun r => SPComp.bind (SPComp.sample (Fin m → D)) fun w =>
    SPComp.bind (SPComp.sample (Fin m → M)) fun b => A (T.ekOf r, hybPts T (T.ekOf r) i w b)

/-- **The reduction of the hop `i` to the hard-core game.** On a challenge `(e, y, β)`, draw the
preimages and values of the other positions, put `(y, β)` at the position `i` of the points of
the hybrid `i` under the key `e`, and run `A`. -/
noncomputable def hcHybRed (T : TDP R TK EK D M) (A : EK × (Fin m → D × M) → SPComp Bool)
    (i : Fin m) (ch : EK × D × M) : SPComp Bool :=
  SPComp.bind (SPComp.sample (Fin m → D)) fun w => SPComp.bind (SPComp.sample (Fin m → M)) fun b =>
    A (ch.1, Function.update (hybPts T ch.1 i w b) i (ch.2.1, ch.2.2))

omit [Fintype R] [Nonempty R] [Fintype D] [Nonempty D] [AddCommGroup M] [Fintype M] in
/-- A hard-core value at the position `i` of the hybrid `i` gives the hybrid `i` at the updated
preimages. -/
theorem update_hybPts_real (T : TDP R TK EK D M) (e : EK) (i : Fin m) (w : Fin m → D)
    (b : Fin m → M) (v : D) :
    Function.update (hybPts T e i w b) i (T.eval e v, T.hc v) =
      hybPts T e i (Function.update w i v) b := by
  funext j
  rcases eq_or_ne j i with rfl | h
  · simp [hybPts]
  · simp [hybPts, Function.update_of_ne h]

omit [Fintype R] [Nonempty R] [Fintype D] [Nonempty D] [AddCommGroup M] [Fintype M] in
/-- A uniform value at the position `i` of the hybrid `i` gives the hybrid `i + 1`. -/
theorem update_hybPts_ideal (T : TDP R TK EK D M) (e : EK) (i : Fin m) (w : Fin m → D)
    (b : Fin m → M) (v : D) (β : M) :
    Function.update (hybPts T e i w b) i (T.eval e v, β) =
      hybPts T e (i + 1) (Function.update w i v) (Function.update b i β) := by
  funext j
  rcases eq_or_ne j i with rfl | h
  · simp [hybPts]
  · have hv : j.val ≠ i.val := fun h' => h (Fin.ext h')
    by_cases hj : j.val < i.val
    · simp [hybPts, Function.update_of_ne h, hj, Nat.lt_succ_of_lt hj]
    · have hj' : ¬ j.val < i.val + 1 := by omega
      simp [hybPts, Function.update_of_ne h, hj, hj']

/-- The real game against the reduction of the hop `i` is the hybrid `i`. -/
theorem hcReal_bind_hcHybRed (T : TDP R TK EK D M) (A : EK × (Fin m → D × M) → SPComp Bool)
    (i : Fin m) : SPComp.bind (hcReal T) (hcHybRed T A i) = hybN T A i := by
  simp only [hcReal, hcHybRed, chReal, SPComp.bind_assoc, SPComp.pure_bind, update_hybPts_real,
    SPComp.sample_prod_eq]
  unfold hybN
  congr 1
  funext r
  rw [SPComp.isPure_bind_comm_left _ _ _ (SPComp.sample_isPure _)]
  exact GeneralForkingLemma.sample_update_eq_sample i fun w =>
    SPComp.bind (SPComp.sample (Fin m → M)) fun b => A (T.ekOf r, hybPts T (T.ekOf r) i w b)

/-- Drawing a value at the position `i` of two uniform families, in either order. -/
theorem sample_update₂ (i : Fin m) (G : (Fin m → D) → (Fin m → M) → SPComp Bool) :
    (SPComp.bind (SPComp.sample D) fun v => SPComp.bind (SPComp.sample M) fun β =>
      SPComp.bind (SPComp.sample (Fin m → D)) fun w =>
        SPComp.bind (SPComp.sample (Fin m → M)) fun b =>
          G (Function.update w i v) (Function.update b i β)) =
      SPComp.bind (SPComp.sample (Fin m → D)) fun w =>
        SPComp.bind (SPComp.sample (Fin m → M)) fun b => G w b := by
  have h1 : ∀ v : D, (SPComp.bind (SPComp.sample M) fun β =>
      SPComp.bind (SPComp.sample (Fin m → D)) fun w =>
        SPComp.bind (SPComp.sample (Fin m → M)) fun b =>
          G (Function.update w i v) (Function.update b i β)) =
      SPComp.bind (SPComp.sample (Fin m → D)) fun w =>
        SPComp.bind (SPComp.sample (Fin m → M)) fun b => G (Function.update w i v) b := by
    intro v
    rw [SPComp.isPure_bind_comm_left _ _ _ (SPComp.sample_isPure _)]
    congr 1
    funext w
    rw [SPComp.isPure_bind_comm_left _ _ _ (SPComp.sample_isPure _)]
    exact GeneralForkingLemma.sample_update_eq_sample i fun b => G (Function.update w i v) b
  simp only [h1]
  rw [SPComp.isPure_bind_comm_left _ _ _ (SPComp.sample_isPure _)]
  exact GeneralForkingLemma.sample_update_eq_sample i fun w =>
    SPComp.bind (SPComp.sample (Fin m → M)) fun b => G w b

/-- The ideal game against the reduction of the hop `i` is the hybrid `i + 1`. -/
theorem hcIdeal_bind_hcHybRed (T : TDP R TK EK D M) (A : EK × (Fin m → D × M) → SPComp Bool)
    (i : Fin m) : SPComp.bind (hcIdeal T) (hcHybRed T A i) = hybN T A (i + 1) := by
  simp only [hcIdeal, hcHybRed, chIdeal, SPComp.bind_assoc, SPComp.pure_bind,
    update_hybPts_ideal, SPComp.sample_prod_eq]
  unfold hybN
  congr 1
  funext r
  exact sample_update₂ i fun w b => A (T.ekOf r, hybPts T (T.ekOf r) (i + 1) w b)

omit [Fintype R] [Nonempty R] [Fintype D] [Nonempty D] [AddCommGroup M] [Fintype M] in
/-- The points of the hybrid `0` are hard-core values. -/
theorem hybPts_zero (T : TDP R TK EK D M) (e : EK) (w : Fin m → D) (b : Fin m → M) :
    hybPts T e 0 w b = fun j => (T.eval e (w j), T.hc (w j)) := by
  funext j
  simp [hybPts]

omit [Fintype R] [Nonempty R] [Fintype D] [Nonempty D] [AddCommGroup M] [Fintype M] in
/-- The points of the hybrid `m` are uniform values. -/
theorem hybPts_last (T : TDP R TK EK D M) (e : EK) (w : Fin m → D) (b : Fin m → M) :
    hybPts T e m w b = fun j => (T.eval e (w j), b j) := by
  funext j
  simp [hybPts, j.isLt]

/-- The hybrid `0` is the real game for `m` points. -/
theorem hybN_zero (T : TDP R TK EK D M) (A : EK × (Fin m → D × M) → SPComp Bool) :
    hybN T A 0 = SPComp.bind (hcRealN T m) A := by
  simp only [hybN, hcRealN, chRealN, hybPts_zero, SPComp.bind_assoc, SPComp.pure_bind,
    SPComp.sample_prod_eq]
  congr 1
  funext r
  congr 1
  funext w
  exact Relational.dead_sample (α := Fin m → M) _

/-- The hybrid `m` is the ideal game for `m` points. -/
theorem hybN_last (T : TDP R TK EK D M) (A : EK × (Fin m → D × M) → SPComp Bool) :
    hybN T A m = SPComp.bind (hcIdealN T m) A := by
  simp only [hybN, hcIdealN, chIdealN, hybPts_last, SPComp.bind_assoc, SPComp.pure_bind,
    SPComp.sample_prod_eq]

/-- **The hard-core game for `m` points from the hard-core game.** The advantage of `A` is at
most the sum over the positions `i` of the hard-core advantages of the hop reductions. -/
theorem HC_AdvantageN_le (T : TDP R TK EK D M) (A : EK × (Fin m → D × M) → SPComp Bool) :
    HC_AdvantageN T A ≤ ∑ i : Fin m, HC_Advantage T (hcHybRed T A i) := by
  have h := HybridArgument.advantage_hybrid_dep_bool (hybN T A) m
  rw [hybN_zero, hybN_last] at h
  refine h.trans (le_of_eq ?_)
  rw [← Fin.sum_univ_eq_sum_range (fun i => Advantage (hybN T A i) (hybN T A (i + 1))) m]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [HC_Advantage, AdvantageA, hcReal_bind_hcHybRed, hcIdeal_bind_hcHybRed]

end CatCrypt.Crypto.Assumptions.HardCore
