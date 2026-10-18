/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Prob.BirthdayBound
public import CatCryptCore.Consensus.PoSNSB.Prob.Slots

/-!
# PoS-NSB: collisions of a random oracle queried adaptively

The hash function of the PoS-NSB model is modelled as a random oracle: a function
`f : D → R` drawn uniformly from all functions from a finite domain `D` to a finite range `R`
with `N = |R|` elements. An adaptive oracle algorithm is a `Querier`: the next query as a
function of the transcript of the previous queries and their answers. Its `k`-th query is
`query next f k`.

## Main results

* `transcript_congr`: the first `k` queries depend only on the values of `f` at those queries.
* `card_resample`: double counting over the value of `f` at one point.
* `prob_freshCollision_le`: the probability that the `k`-th query is a new point whose answer
  equals an earlier answer is at most `k / N`.
* `prob_ROCollision_le` (**birthday bound**): the probability that two distinct points among
  the first `q` queries have the same answer is at most `q (q - 1) / 2 / N`, obtained from
  `CatCrypt.Prob.BirthdayBound.birthday_bound_sum_nat`.

A keyed hash family (`HashFam D R`) has a finite nonempty key space and a hash function under
each key; the random oracle is the family `HashFam.randomFun D R` whose keys are the functions.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace CatCryptCore.Consensus.PoSNSB

open scoped ENNReal

variable {D R : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

/-- An adaptive oracle algorithm: the next query, as a function of the list of the previous
queries and their answers. -/
abbrev Querier (D R : Type) := List (D × R) → D

/-- The transcript of the first `k` queries of `next` to `f`. -/
def transcript (next : Querier D R) (f : D → R) : ℕ → List (D × R)
  | 0 => []
  | k + 1 => transcript next f k ++
      [(next (transcript next f k), f (next (transcript next f k)))]

/-- The `k`-th query of `next` to `f` (counting from `0`). -/
def query (next : Querier D R) (f : D → R) (k : ℕ) : D := next (transcript next f k)

/-- The first `q` queries. -/
def queries (next : Querier D R) (f : D → R) (q : ℕ) : List D :=
  (List.range q).map (query next f)

theorem transcript_eq (next : Querier D R) (f : D → R) (k : ℕ) :
    transcript next f k = (List.range k).map fun j => (query next f j, f (query next f j)) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [transcript, List.range_succ, List.map_append, ← ih]; rfl

/-- The first `k` queries are determined by the values of `f` at those queries. -/
theorem transcript_congr (next : Querier D R) (f g : D → R) (k : ℕ)
    (h : ∀ j < k, g (query next f j) = f (query next f j)) :
    transcript next g k = transcript next f k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have ih := ih fun j hj => h j (by omega)
    simp only [transcript, ih]
    have := h k (by omega)
    simp only [query] at this
    rw [this]

/-- The first `k` queries and their answers are unchanged when `f` is changed at a point that
is not among them. -/
theorem transcript_update (next : Querier D R) (f : D → R) (k : ℕ) (x : D) (y : R)
    (hx : ∀ j < k, query next f j ≠ x) :
    transcript next (Function.update f x y) k = transcript next f k :=
  transcript_congr next f _ k fun j hj => Function.update_of_ne (hx j hj) _ _

/-- The first `k + 1` queries are unchanged when `f` is changed at a point that is not among
the first `k` queries. -/
theorem query_update (next : Querier D R) (f : D → R) (k : ℕ) (x : D) (y : R)
    (hx : ∀ j < k, query next f j ≠ x) :
    ∀ j ≤ k, query next (Function.update f x y) j = query next f j := by
  intro j hj
  simp only [query]
  rw [transcript_update next f j x y fun i hi => hx i (by omega)]

/-- The `k`-th query is a new point whose answer equals the answer of an earlier query. -/
def FreshCollision (next : Querier D R) (k : ℕ) (f : D → R) : Prop :=
  (∀ j < k, query next f j ≠ query next f k) ∧
    ∃ j < k, f (query next f j) = f (query next f k)

/-- Two distinct points among the first `q` queries have the same answer. -/
def ROCollision (next : Querier D R) (q : ℕ) (f : D → R) : Prop :=
  ∃ a < q, ∃ b < q, query next f a ≠ query next f b ∧ f (query next f a) = f (query next f b)

/-- A collision among the first `q` queries yields a query `k < q` that is a new point colliding
with an earlier answer. -/
theorem exists_fresh_of_collision (next : Querier D R) (q : ℕ) (f : D → R)
    (h : ROCollision next q f) : ∃ k < q, FreshCollision next k f := by
  have key : ∀ b, ∀ a < b, query next f a ≠ query next f b →
      f (query next f a) = f (query next f b) → ∃ k ≤ b, FreshCollision next k f := by
    intro b
    induction b using Nat.strong_induction_on with
    | _ b ih =>
      intro a hab hne hf
      by_cases hnew : ∀ j < b, query next f j ≠ query next f b
      · exact ⟨b, le_rfl, hnew, a, hab, hf⟩
      · push Not at hnew
        obtain ⟨c, hcb, hc⟩ := hnew
        have hac : a ≠ c := by rintro rfl; exact hne hc
        rcases Nat.lt_or_gt_of_ne hac with h1 | h1
        · obtain ⟨k, hk, hk'⟩ := ih c hcb a h1 (hc ▸ hne) (hc ▸ hf)
          exact ⟨k, by omega, hk'⟩
        · obtain ⟨k, hk, hk'⟩ := ih a hab c h1 (fun h' => hne (h'.symm.trans hc))
            (by rw [hc, hf])
          exact ⟨k, by omega, hk'⟩
  obtain ⟨a, ha, b, hb, hne, hf⟩ := h
  rcases Nat.lt_or_gt_of_ne (fun h' : a = b => hne (h' ▸ rfl)) with h1 | h1
  · obtain ⟨k, hk, hk'⟩ := key b a h1 hne hf
    exact ⟨k, by omega, hk'⟩
  · obtain ⟨k, hk, hk'⟩ := key a b h1 (Ne.symm hne) hf.symm
    exact ⟨k, by omega, hk'⟩

/-! ## Double counting over the value at one point -/

/-- Summing over all functions and all values at `x` counts every function `|R|` times. -/
theorem sum_update (x : D) (h : (D → R) → ℕ) :
    (∑ f, h f) * Fintype.card R = ∑ f, ∑ y, h (Function.update f x y) := by
  set e := Equiv.piSplitAt x (fun _ : D => R)
  have hupd : ∀ (z y : R) (r : {j // j ≠ x} → R),
      Function.update (e.symm (z, r)) x y = e.symm (y, r) := by
    intro z y r
    ext j
    by_cases hj : j = x
    · subst hj; simp [e, Equiv.piSplitAt]
    · simp [e, Equiv.piSplitAt, hj]
  rw [Finset.sum_comm]
  have hy : ∀ y : R, ∑ f, h (Function.update f x y) =
      Fintype.card R * ∑ r : {j // j ≠ x} → R, h (e.symm (y, r)) := by
    intro y
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
    simp only [hupd, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  simp only [hy, ← Finset.mul_sum]
  rw [mul_comm, ← Fintype.sum_prod_type (f := fun p => h (e.symm p)), e.symm.sum_comp]

/-- **Resampling at one point.** Let `P` and `S` not depend on the value of `f` at `x`, with
`|S f| ≤ k`. The functions satisfying `P` whose value at `x` lies in `S f` are at most a
fraction `k / |R|` of the functions satisfying `P`. -/
theorem card_resample (x : D) (P : (D → R) → Prop) [DecidablePred P] (S : (D → R) → Finset R)
    (k : ℕ) (hP : ∀ f y, P (Function.update f x y) ↔ P f)
    (hS : ∀ f y, P f → S (Function.update f x y) = S f) (hk : ∀ f, (S f).card ≤ k) :
    (Finset.univ.filter fun f => P f ∧ f x ∈ S f).card * Fintype.card R ≤
      k * (Finset.univ.filter P).card := by
  rw [Finset.card_filter, sum_update x, Finset.card_filter, Finset.mul_sum]
  refine Finset.sum_le_sum fun f _ => ?_
  by_cases hf : P f
  · have : ∀ y, (if P (Function.update f x y) ∧ (Function.update f x y) x ∈
        S (Function.update f x y) then 1 else 0) = if y ∈ S f then 1 else 0 := by
      intro y
      simp only [Function.update_self, hS f y hf, (hP f y).2 hf, true_and]
    simp only [this, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, hf,
      if_true, mul_one]
    exact hk f
  · simp [hP, hf]

/-! ## The birthday bound -/

/-- The uniform distribution on the functions from `D` to `R`. -/
noncomputable def uniformFun (D R : Type) [Fintype D] [DecidableEq D] [Fintype R] [Nonempty R] :
    PMF (D → R) :=
  PMF.uniformOfFintype (D → R)

/-- The probability that the `k`-th query is a new point whose answer equals an earlier answer
is at most `k / |R|`. -/
theorem prob_freshCollision_le [Nonempty R] (next : Querier D R) (k : ℕ) :
    (uniformFun D R).toOuterMeasure {f | FreshCollision next k f} ≤
      (k : ℝ≥0∞) / Fintype.card R := by
  classical
  set P : D → (D → R) → Prop := fun x f => query next f k = x ∧ ∀ j < k, query next f j ≠ x
  set S : (D → R) → Finset R := fun f => ((List.range k).map fun j => f (query next f j)).toFinset
  have hP : ∀ x f y, P x (Function.update f x y) ↔ P x f := by
    intro x f y
    constructor
    · intro hf
      have hq := query_update next (Function.update f x y) k x (f x) hf.2
      rw [Function.update_idem, Function.update_eq_self] at hq
      exact ⟨(hq k le_rfl).trans hf.1, fun j hj => (hq j hj.le) ▸ hf.2 j hj⟩
    · intro hf
      have hq := query_update next f k x y hf.2
      exact ⟨(hq k le_rfl).trans hf.1, fun j hj => (hq j hj.le).symm ▸ hf.2 j hj⟩
  have hS : ∀ x f y, P x f → S (Function.update f x y) = S f := by
    intro x f y hf
    have hq := query_update next f k x y hf.2
    simp only [S]
    congr 1
    refine List.map_congr_left fun j hj => ?_
    have hj : j < k := List.mem_range.1 hj
    rw [hq j hj.le, Function.update_of_ne (hf.2 j hj)]
  have hk : ∀ f, (S f).card ≤ k := fun f =>
    (List.toFinset_card_le _).trans (by simp)
  have hfib : ∀ x, (Finset.univ.filter fun f => FreshCollision next k f ∧ query next f k = x) =
      Finset.univ.filter fun f => P x f ∧ f x ∈ S f := by
    intro x
    ext f
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, FreshCollision, P, S, List.mem_toFinset, List.mem_map,
      List.mem_range]
    constructor
    · rintro ⟨⟨h1, j, hj, hf⟩, rfl⟩
      exact ⟨⟨rfl, h1⟩, j, hj, hf⟩
    · rintro ⟨⟨rfl, h1⟩, j, hj, hf⟩
      exact ⟨⟨h1, j, hj, hf⟩, rfl⟩
  have hcard : (Finset.univ.filter fun f => FreshCollision next k f).card * Fintype.card R ≤
      k * Fintype.card (D → R) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun f => query next f k) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _), Finset.sum_mul]
    simp only [Finset.filter_filter]
    calc ∑ x, (Finset.univ.filter fun f => FreshCollision next k f ∧ query next f k = x).card *
          Fintype.card R
        ≤ ∑ x, k * (Finset.univ.filter (P x)).card := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [hfib x]
          exact card_resample x (P x) S k (hP x) (hS x) hk
      _ ≤ ∑ x, k * (Finset.univ.filter fun f => query next f k = x).card := by
          refine Finset.sum_le_sum fun x _ => Nat.mul_le_mul_left _ (Finset.card_le_card ?_)
          intro f; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact fun h => h.1
      _ = k * Fintype.card (D → R) := by
          rw [← Finset.mul_sum, ← Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _),
            Finset.card_univ]
  rw [uniformFun, PMF.toOuterMeasure_uniformOfFintype_apply]
  have hc : Fintype.card ↑{f | FreshCollision next k f} =
      (Finset.univ.filter fun f => FreshCollision next k f).card := by
    rw [← Set.toFinset_card]; congr 1; ext f; simp
  rw [hc]
  have hF : (0 : ℝ≥0∞) < Fintype.card (D → R) := by exact_mod_cast Fintype.card_pos
  have hN : (0 : ℝ≥0∞) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  rw [ENNReal.div_le_iff hF.ne' (ENNReal.natCast_ne_top _), mul_comm, ← mul_div_assoc,
    ENNReal.le_div_iff_mul_le (Or.inl hN.ne') (Or.inl (ENNReal.natCast_ne_top _))]
  exact_mod_cast (mul_comm (Fintype.card (D → R)) k ▸ hcard)

/-- **Birthday bound for an adaptive querier (part 2).** For a uniformly random function
`f : D → R` and any adaptive querier `next`, the probability that two distinct points among the
first `q` queries have the same value is at most `q (q - 1) / 2 / |R|`. -/
theorem prob_ROCollision_le [Nonempty R] (next : Querier D R) (q : ℕ) :
    (uniformFun D R).toOuterMeasure {f | ROCollision next q f} ≤
      ((q * (q - 1) / 2 : ℕ) : ℝ≥0∞) / Fintype.card R := by
  have hsub : {f | ROCollision next q f} ⊆
      ⋃ k ∈ Finset.range q, {f | FreshCollision next k f} := by
    intro f hf
    obtain ⟨k, hk, hk'⟩ := exists_fresh_of_collision next q f hf
    simp only [Set.mem_iUnion, Finset.mem_range]
    exact ⟨k, hk, hk'⟩
  refine (MeasureTheory.OuterMeasure.mono _ hsub).trans ?_
  refine (MeasureTheory.measure_biUnion_finset_le (μ := (uniformFun D R).toOuterMeasure)
    _ _).trans ?_
  exact CatCrypt.Prob.BirthdayBound.birthday_bound_sum_nat q (Fintype.card R) _
    fun k _ => prob_freshCollision_le next k

/-! ## Keyed hash families -/

/-- A keyed hash family from `D` to `R`: a finite nonempty key space and the hash function
under each key. -/
structure HashFam (D R : Type) where
  /-- The key space. -/
  Key : Type
  /-- The key space is finite. -/
  [instFintypeKey : Fintype Key]
  /-- The key space is nonempty. -/
  [instNonemptyKey : Nonempty Key]
  /-- The hash function under a key. -/
  hash : Key → D → R

attribute [instance] HashFam.instFintypeKey HashFam.instNonemptyKey

/-- The random oracle as a keyed hash family: the keys are the functions from `D` to `R`, and
the hash function under the key `f` is `f`. A uniformly random key is a draw from
`uniformFun D R`. -/
abbrev HashFam.randomFun (D R : Type) [Fintype D] [DecidableEq D] [Fintype R] [Nonempty R] :
    HashFam D R where
  Key := D → R
  hash := id

end CatCryptCore.Consensus.PoSNSB
