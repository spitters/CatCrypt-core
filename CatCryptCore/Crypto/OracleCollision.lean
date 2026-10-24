/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleEval
public import CatCryptCore.Crypto.Constructions.ECBCPRFFlag
public import CatCryptCore.ForMathlib.PMFSupport
public import CatCryptCore.Prob.BirthdayBound

/-!
# Collisions among the queries of a randomised adaptive oracle adversary

An adversary `A : OracleAdv D R α` runs against a function `f : D → R` drawn uniformly from all
functions from a finite domain `D` to a finite range `R`: its `rand` nodes sample their coins,
each query `d` is answered by `f d`, and the oracle `logOracle f` records the queried points.
`OracleAdv.collisionGame A` is the joint distribution of `f`, the output and the list of
queried points.

## Main definitions

* `OracleAdv.QueryCollision f L` — two distinct points of `L` have the same value under `f`
* `OracleAdv.collisionGame A` — a uniform function and the run of `A` against it, with the
  list of queried points
* `OracleAdv.tableExt t g` — the function equal to the partial table `t` where it is defined
  and to `g` elsewhere
* `OracleAdv.tableGame t A l` — the run of `A` from the log `l` against a uniform extension of
  the table `t`
* `OracleAdv.ofQuerier next t n` — the adversary without coins asking `n` queries, each chosen
  by `next` from the transcript of queries and answers so far

## Main results

* `OracleAdv.uniform_bind_eq_bind_update` — a uniform function is a uniform function updated
  at `d` by an independent uniform value
* `OracleAdv.tableGame_collision_le` — from a collision-free table with at most `i` entries
  containing the log, a run with at most `q` queries ends with a collision among the table
  and the queried points with probability at most `∑ j < q, (i + j) / |R|`
* `OracleAdv.prob_oracleCollision_le` (**birthday bound**) — for every adversary with at
  most `q` queries on every path, two distinct queried points have the same value with
  probability at most `q (q - 1) / 2 / |R|`
* `OracleAdv.prob_evalOn_collision_le` — the same bound for an adversary without `rand` nodes,
  over the queries of `evalOn f A`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto

namespace OracleAdv

open scoped ENNReal

variable {D R α : Type}

/-- Two distinct points of `L` have the same value under `f`. -/
def QueryCollision (f : D → R) (L : List D) : Prop :=
  ∃ x ∈ L, ∃ y ∈ L, x ≠ y ∧ f x = f y

/-- The function equal to the partial table `t` where it is defined and to `g` elsewhere. -/
def tableExt (t : D → Option R) (g : D → R) : D → R :=
  fun x => (t x).getD (g x)

/-- Two distinct points, each in the domain of the table `t` or in `L`, have the same value
under `f`. -/
def TableCollision (t : D → Option R) (f : D → R) (L : List D) : Prop :=
  ∃ x, ((t x).isSome ∨ x ∈ L) ∧ ∃ y, ((t y).isSome ∨ y ∈ L) ∧ x ≠ y ∧ f x = f y

/-- The adversary without coins asking `n` queries from the transcript `t`, each query chosen
by `next` from the transcript of the previous queries and their answers. -/
def ofQuerier (next : List (D × R) → D) : List (D × R) → ℕ → OracleAdv D R Unit
  | _, 0 => ret ()
  | t, n + 1 => query (next t) fun r => ofQuerier next (t ++ [(next t, r)]) n

/-- The adversary `ofQuerier next t n` has no `rand` node. -/
theorem ofQuerier_noRand (next : List (D × R) → D) (t : List (D × R)) (n : ℕ) :
    (ofQuerier next t n).NoRand := by
  induction n generalizing t with
  | zero => trivial
  | succ n ih => exact fun r => ih _

/-- The adversary `ofQuerier next t n` asks at most `n` queries on every path. -/
theorem ofQuerier_isQueryBound (next : List (D × R) → D) (t : List (D × R)) (n : ℕ) :
    (ofQuerier next t n).IsQueryBound n := by
  induction n generalizing t with
  | zero => trivial
  | succ n ih => exact fun r => ih _

section Game

variable [Fintype D] [DecidableEq D] [Fintype R] [Nonempty R]

/-- A uniform function `f : D → R`, the output of `A` against `f` and the list of the points
`A` queries, in order. -/
noncomputable def collisionGame (A : OracleAdv D R α) : PMF ((D → R) × α × List D) :=
  (PMF.uniformFintype (D → R)).bind fun f => (run (logOracle f) A []).map fun r => (f, r)

/-- The run of `A` from the log `l` against `tableExt t g` for a uniform `g`, together with
the function `tableExt t g`. -/
noncomputable def tableGame (t : D → Option R) (A : OracleAdv D R α) (l : List D) :
    PMF ((D → R) × α × List D) :=
  (PMF.uniformFintype (D → R)).bind fun g =>
    (run (logOracle (tableExt t g)) A l).map fun r => (tableExt t g, r)

/-- A uniform function is a uniform function updated at `d` by an independent uniform
value. -/
theorem uniform_bind_eq_bind_update {β : Type} (d : D) (F : (D → R) → PMF β) :
    (PMF.uniformFintype (D → R)).bind F =
      (PMF.uniformFintype R).bind fun r =>
        (PMF.uniformFintype (D → R)).bind fun g => F (Function.update g d r) := by
  conv_lhs => rw [← Constructions.ECBCPRF.uniform_bind_update d]
  rw [PMF.bind_bind]
  simp only [PMF.bind_map]
  rw [PMF.bind_comm]
  rfl

omit [Fintype D] [DecidableEq D] [Fintype R] [Nonempty R] in
private theorem toOuterMeasure_bind_le' {β γ : Type} (p : PMF β) (f : β → PMF γ) (S : Set γ)
    (c : ℝ≥0∞) (h : ∀ b, (f b).toOuterMeasure S ≤ c) : (p.bind f).toOuterMeasure S ≤ c := by
  simpa using PMF.toOuterMeasure_bind_le_add p f ∅ S c fun b _ => h b

/-- From a collision-free table `t` with at most `i` entries whose domain contains the log `l`,
a run of `A` with at most `q` queries on every path ends with two distinct points of the
table's domain or the log having the same value with probability at most
`∑ j < q, (i + j) / |R|`. -/
theorem tableGame_collision_le (A : OracleAdv D R α) (q i : ℕ) (hA : A.IsQueryBound q)
    (t : D → Option R) (l : List D) (hl : ∀ x ∈ l, (t x).isSome)
    (ht : ∀ x y r, t x = some r → t y = some r → x = y)
    (hi : (Finset.univ.filter fun x => (t x).isSome).card ≤ i) :
    (tableGame t A l).toOuterMeasure {p | TableCollision t p.1 p.2.2} ≤
      ∑ j ∈ Finset.range q, ((i + j : ℕ) : ℝ≥0∞) / Fintype.card R := by
  classical
  induction A generalizing q i t l with
  | ret a =>
    refine (toOuterMeasure_bind_le' _ _ _ 0 fun g => ?_).trans zero_le
    rw [run_ret, PMF.pure_map, PMF.toOuterMeasure_pure_apply, ite_eq_right]
    rintro ⟨x, hx, y, hy, hxy, hf⟩
    have hx' : (t x).isSome := hx.elim id (hl x)
    have hy' : (t y).isSome := hy.elim id (hl y)
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hx'
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hy'
    simp only [tableExt, hu, hv, Option.getD_some] at hf
    exact hxy (ht x y u hu (hf ▸ hv))
  | rand p k ih =>
    have he : tableGame t (rand p k) l = p.bind fun b => tableGame t (k b) l := by
      simp only [tableGame, run_rand, PMF.map_bind]
      exact PMF.bind_comm _ _ _
    rw [he]
    exact toOuterMeasure_bind_le' _ _ _ _ fun b => ih b q i (hA b) t l hl ht hi
  | query d k ih =>
    cases q with
    | zero => exact hA.elim
    | succ q =>
    have hrun : ∀ g, run (logOracle (tableExt t g)) (query d k) l =
        run (logOracle (tableExt t g)) (k (tableExt t g d)) (l ++ [d]) := by
      intro g
      rw [run_query, logOracle, PMF.pure_bind]
    cases htd : t d with
    | some r =>
      have he : tableGame t (query d k) l = tableGame t (k r) (l ++ [d]) := by
        simp only [tableGame, hrun, tableExt, htd, Option.getD_some]
      rw [he]
      refine (ih r q i (hA r) t (l ++ [d]) ?_ ht hi).trans ?_
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hl x hx
        · rw [List.mem_singleton.1 hx, htd]; rfl
      · exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (Nat.le_succ q))
    | none =>
      set t' : R → D → Option R := fun r => Function.update t d (some r) with ht'
      have hext : ∀ r g, tableExt t (Function.update g d r) = tableExt (t' r) g := by
        intro r g
        funext x
        by_cases hx : x = d
        · subst hx; simp [tableExt, ht', htd]
        · simp [tableExt, ht', Function.update_of_ne hx]
      have he : tableGame t (query d k) l =
          (PMF.uniformFintype R).bind fun r => tableGame (t' r) (k r) (l ++ [d]) := by
        rw [tableGame, uniform_bind_eq_bind_update d]
        congr 1
        funext r
        simp only [hrun]
        simp only [hext, tableGame]
        have hd : ∀ g, tableExt (t' r) g d = r := fun g => by simp [tableExt, ht']
        simp only [hd]
      rw [he]
      set B : Finset R :=
        (Finset.univ.filter fun x => (t x).isSome).image fun x => (t x).getD (Classical.arbitrary R)
      have hB : ∀ r ∉ B, ∀ x, t x ≠ some r := by
        intro r hr x hx
        exact hr (Finset.mem_image.2
          ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [hx]; rfl⟩, by rw [hx]; rfl⟩)
      have hsome : ∀ r x, (t x).isSome → (t' r x).isSome := by
        intro r x hx
        by_cases hxd : x = d
        · subst hxd; simp [htd] at hx
        · simpa [ht', Function.update_of_ne hxd] using hx
      refine (PMF.toOuterMeasure_bind_le_add _ _ (↑B) _
        (∑ j ∈ Finset.range q, ((i + 1 + j : ℕ) : ℝ≥0∞) / Fintype.card R) fun r hr => ?_).trans ?_
      · refine le_trans (MeasureTheory.measure_mono ?_)
          (ih r q (i + 1) (hA r) (t' r) (l ++ [d]) ?_ ?_ ?_)
        · rintro p ⟨x, hx, y, hy, hxy, hf⟩
          exact ⟨x, hx.imp_left (hsome r x), y, hy.imp_left (hsome r y), hxy, hf⟩
        · intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact hsome r x (hl x hx)
          · rw [List.mem_singleton.1 hx]; simp [ht']
        · intro x y r' hx hy
          by_cases hxd : x = d <;> by_cases hyd : y = d
          · rw [hxd, hyd]
          · subst hxd
            simp only [ht', Function.update_self, Option.some.injEq] at hx
            simp only [ht', Function.update_of_ne hyd] at hy
            exact (hB r hr y (hx ▸ hy)).elim
          · subst hyd
            simp only [ht', Function.update_self, Option.some.injEq] at hy
            simp only [ht', Function.update_of_ne hxd] at hx
            exact (hB r hr x (hy ▸ hx)).elim
          · simp only [ht', Function.update_of_ne hxd, Function.update_of_ne hyd] at hx hy
            exact ht x y r' hx hy
        · refine le_trans (Finset.card_le_card (t := insert d
            (Finset.univ.filter fun x => (t x).isSome)) ?_) ((Finset.card_insert_le _ _).trans
              (Nat.succ_le_succ hi))
          intro x hx
          by_cases hxd : x = d
          · rw [hxd]; exact Finset.mem_insert_self _ _
          · refine Finset.mem_insert_of_mem ?_
            simpa [ht', Function.update_of_ne hxd] using hx
      · rw [Finset.sum_range_succ', PMF.toOuterMeasure_uniformFintype_apply, add_comm]
        have h1 : ∀ j, ((i + 1 + j : ℕ) : ℝ≥0∞) = ((i + (j + 1) : ℕ) : ℝ≥0∞) := fun j => by
          congr 1; omega
        simp only [h1]
        gcongr
        simp only [add_zero, Finset.coe_sort_coe, Fintype.card_coe]
        exact Finset.card_image_le.trans hi

/-- **Birthday bound for a randomised adaptive adversary.** For a uniformly random function
`f : D → R` and every adversary `A` asking at most `q` queries on every path, the probability
over `f` and the coins of `A` that two distinct points queried by `A` have the same value
under `f` is at most `q (q - 1) / 2 / |R|`. -/
theorem prob_oracleCollision_le (A : OracleAdv D R α) (q : ℕ) (hA : A.IsQueryBound q) :
    (collisionGame A).toOuterMeasure {p | QueryCollision p.1 p.2.2} ≤
      ((q * (q - 1) / 2 : ℕ) : ℝ≥0∞) / Fintype.card R := by
  have hg : collisionGame A = tableGame (fun _ => none) A [] := rfl
  have hev : {p : (D → R) × α × List D | QueryCollision p.1 p.2.2} =
      {p | TableCollision (fun _ => none) p.1 p.2.2} := by
    ext p
    simp [QueryCollision, TableCollision]
  rw [hg, hev, ← CatCrypt.Prob.BirthdayBound.gauss_sum_ennreal]
  simpa using tableGame_collision_le A q 0 hA (fun _ => none) [] (by simp)
    (by simp) (by simp)

/-- **Birthday bound without coins.** For an adversary without `rand` nodes asking at most
`q` queries on every path, the probability over a uniform `f : D → R` that two distinct
points among the queries of `evalOn f A` have the same value is at most
`q (q - 1) / 2 / |R|`. -/
theorem prob_evalOn_collision_le (A : OracleAdv D R α) (hA₀ : A.NoRand) (q : ℕ)
    (hA : A.IsQueryBound q) :
    (PMF.uniformFintype (D → R)).toOuterMeasure {f | QueryCollision f (evalOn f A).2} ≤
      ((q * (q - 1) / 2 : ℕ) : ℝ≥0∞) / Fintype.card R := by
  have hg : collisionGame A = (PMF.uniformFintype (D → R)).map
      fun f => (f, (evalOn f A).1, (evalOn f A).2) := by
    simp only [collisionGame, run_logOracle_eq_evalOn _ hA₀, PMF.pure_map, List.nil_append]
    rfl
  have h := prob_oracleCollision_le A q hA
  rw [hg, PMF.toOuterMeasure_map_apply] at h
  exact h

end Game

end OracleAdv

end CatCrypt.Crypto
