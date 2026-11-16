/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.CryptoVerif.Game
public import CatCryptCore.ForMathlib.PMFUniform

/-!
# CryptoVerif's `find` and tables

`find u <= N suchthat M then P else P'` chooses an index `u` that satisfies the condition `M`,
uniformly among the satisfying indices, and runs `P'` when none satisfies it. CryptoVerif allows
a distance `eps_find / 2` from the uniform choice; `cvFind` is exactly uniform (`eps_find = 0`).
A table is a list of entries; `get` chooses a matching entry in the same way.

## Main results

* `cvFind` — the uniform choice of a satisfying index, `none` if there is none.
* `cvFind_eq_uniform`, `cvFind_none_apply` — the probability of each index is the inverse of
  the number of satisfying indices, or 0; `none` has probability 1 exactly when no index
  satisfies the condition.
* `cvFind_of_unique`, `cvFind_of_none` — a `find` with exactly one satisfying index is that
  index; a `find` with none is `none`.
* `cvFind_map_isSome` — `find` succeeds with probability 1 exactly when some index satisfies the
  condition.
* `cvGet`, `cvGet_eq_find?` — `get` on a table, and, when the keys of the table are distinct,
  `get` at a key is the deterministic lookup `List.find?`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.CryptoVerifLogic

open scoped ENNReal

variable {ι : Type} [Fintype ι]

/-- CryptoVerif's `find`: an index satisfying `cond`, drawn uniformly among the satisfying
indices, or `none` when no index satisfies it. -/
noncomputable def cvFind (cond : ι → Bool) : PMF (Option ι) :=
  if h : ∃ i, cond i = true then
    haveI : Nonempty {i // cond i = true} := ⟨⟨h.choose, h.choose_spec⟩⟩
    (PMF.uniformFintype {i // cond i = true}).map fun j => some j.1
  else PMF.pure none

/-- **`find` is uniform.** The probability that `find` chooses the index `i` is the inverse of
the number of satisfying indices when `i` satisfies the condition, and 0 otherwise. -/
theorem cvFind_eq_uniform (cond : ι → Bool) (i : ι) :
    cvFind cond (some i) =
      if cond i = true then ((Fintype.card {j // cond j = true} : ℕ) : ℝ≥0∞)⁻¹ else 0 := by
  unfold cvFind
  split_ifs with hne hc hc
  · rw [PMF.map_apply, tsum_eq_single ⟨i, hc⟩ fun b hb => by
      simp only [Option.some.injEq, ite_eq_right_iff]
      intro h
      exact absurd (Subtype.ext h.symm) hb]
    simp [PMF.uniformFintype_apply]
  · rw [PMF.map_apply]
    exact ENNReal.tsum_eq_zero.mpr fun b => by
      rw [ite_eq_right fun h => hc (by rw [Option.some_injective _ h]; exact b.2)]
  · exact absurd ⟨i, hc⟩ hne
  · simp

/-- `find` returns `none` with probability 1 when no index satisfies the condition, and with
probability 0 otherwise. -/
theorem cvFind_none_apply (cond : ι → Bool) :
    cvFind cond none = if ∃ i, cond i = true then 0 else 1 := by
  unfold cvFind
  split_ifs with hne
  · rw [PMF.map_apply]
    simp
  · simp

/-- A `find` with exactly one satisfying index chooses it. -/
theorem cvFind_of_unique (cond : ι → Bool) (i : ι) (h : ∀ j, cond j = true ↔ j = i) :
    cvFind cond = PMF.pure (some i) := by
  have hcard : Fintype.card {j // cond j = true} = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨⟨i, (h i).mpr rfl⟩, fun j => Subtype.ext ((h j.1).mp j.2)⟩
  ext x
  cases x with
  | none =>
    have hex : ∃ j, cond j = true := ⟨i, (h i).mpr rfl⟩
    simp [cvFind_none_apply, hex]
  | some j =>
    rw [cvFind_eq_uniform, hcard, PMF.pure_apply]
    by_cases hj : j = i
    · simp [hj, (h i).mpr rfl]
    · simp [hj, (h j).not.mpr hj]

/-- A `find` with no satisfying index returns `none`. -/
theorem cvFind_of_none (cond : ι → Bool) (h : ∀ j, cond j = false) :
    cvFind cond = PMF.pure none := by
  simp [cvFind, h]

/-- **A `find` whose result is not used.** The success of CryptoVerif's `find` is certain when
some index satisfies the condition, and impossible otherwise. -/
theorem cvFind_map_isSome (cond : ι → Bool) :
    (cvFind cond).map Option.isSome = PMF.pure (decide (∃ i, cond i = true)) := by
  unfold cvFind
  split_ifs with h
  · rw [PMF.map_comp]
    rw [decide_eq_true h]
    exact PMF.map_const _ _
  · rw [PMF.pure_map]
    simp [h]

/-- Two satisfying indices out of three: `find` chooses each with probability `1/2`. -/
example : cvFind (fun i : Fin 3 => decide (i ≠ 2)) (some 0) = 2⁻¹ := by
  rw [cvFind_eq_uniform]
  simp only [ne_eq, decide_not, Fin.reduceEq, decide_false, Bool.not_false, ↓reduceIte]
  congr

/-- CryptoVerif's `get` on a table: a matching entry, drawn uniformly among the matching
positions, or `none`. -/
noncomputable def cvGet {α : Type} (tbl : List α) (p : α → Bool) : PMF (Option α) :=
  (cvFind fun i : Fin tbl.length => p tbl[i]).map (Option.map fun i => tbl[i])

/-- **Tables with distinct keys.** When the keys of the entries are distinct, `get` at a key is
the deterministic lookup of that key. -/
theorem cvGet_eq_find? {α κ : Type} [DecidableEq κ] (tbl : List α) (key : α → κ) (k : κ)
    (hdistinct : (tbl.map key).Nodup) :
    cvGet tbl (fun x => decide (key x = k)) = PMF.pure (tbl.find? fun x => decide (key x = k)) := by
  unfold cvGet
  by_cases hex : ∃ i : Fin tbl.length, key tbl[i] = k
  · obtain ⟨i, hi⟩ := hex
    have huniq : ∀ j : Fin tbl.length, decide (key tbl[j] = k) = true ↔ j = i := by
      intro j
      refine ⟨fun hj => ?_, fun hj => by subst hj; simpa using hi⟩
      have hji : (tbl.map key)[j.1]'(by simp) = (tbl.map key)[i.1]'(by simp) := by
        simp only [List.getElem_map]
        exact (of_decide_eq_true hj).trans hi.symm
      exact Fin.ext ((hdistinct.getElem_inj_iff).mp hji)
    rw [cvFind_of_unique _ i huniq, PMF.pure_map]
    congr 1
    symm
    rw [Option.map_some, List.find?_eq_some_iff_getElem]
    refine ⟨by simpa using hi, i.1, i.2, rfl, fun j hj => ?_⟩
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    intro hk
    have := (huniq ⟨j, by omega⟩).mp (by simpa using hk)
    exact absurd (congrArg Fin.val this) (by simp; omega)
  · push Not at hex
    rw [cvFind_of_none _ fun j => by simpa using hex j, PMF.pure_map]
    congr 1
    symm
    rw [Option.map_none, List.find?_eq_none]
    intro x hx
    obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hx
    simpa using hex ⟨n, hn⟩

end CatCrypt.Crypto.CryptoVerifLogic
