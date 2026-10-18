/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirROM.ProgFlag

/-!
# Multiplicity of fresh values in an oracle run

An adversary `A : OracleAdv D R α` runs against a stateful oracle
`O : S → D → PMF (R × S)`. The state carries counts `cnt s : V → ℕ` of points per
value. Each call adds at most one point, only at a positive query cost, and a point
of a given value with probability at most `p` given the state before the call
(`OracleAdv.FreshMult`). A run whose queries cost at most `N` in total ends with more
than `K` points of one value with probability at most `C(N, K + 1) · p^K`
(`OracleAdv.run_not_multB_le`).

The proof bounds the expected number of `(K + 1)`-sets of points sharing a value.
The layer `j + 1` of the counts is `Σ_v C(cnt v, j + 1)` (`OracleAdv.multLayer`); one
call raises its expectation by at most `p` times layer `j` (by at most `1` for
`j = 0`). The layered potential `OracleAdv.layerPot` sums these increments over the
remaining budget, and at zero counts it is `C(n, j + 1) · p^j` by the hockey-stick
identity.

## Main definitions

* `OracleAdv.layerPot a w` — the layered potential of the layers `a` with the
  weights `w`
* `OracleAdv.MultB K c` — the counts `c` are at most `K` each
* `OracleAdv.multLayer c` — the multiplicity layers of the counts `c`
* `OracleAdv.FreshMult O cost cnt p` — each call adds at most one point, at a
  positive cost, of a given value with probability at most `p`

## Main results

* `OracleAdv.run_potential_le` — a potential whose expectation does not increase
  over one call bounds the expected value of a function below it at the end of a run
* `OracleAdv.run_layerPot_le` — the layered potential bounds the expected layer at
  the end of a run
* `OracleAdv.layerPot_multLayer_zero` — the layered multiplicity potential at zero
  counts is `C(n, j + 1) · p^j`
* `OracleAdv.run_not_multB_le` — a run violates the multiplicity bound `K` with
  probability at most `C(N, K + 1) · p^K`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OracleAdv

open CatCrypt.Crypto.Constructions.ECBCPRF (tsum_bind_mul tsum_pure_mul)
open scoped ENNReal

variable {D R α : Type}

/-! ## Potentials over a run -/

/-- **Potential bound.** Let `Ψ n` be a potential on oracle states indexed by a
remaining query budget `n`, above `Φ` at every budget, whose expectation after one
call `O s d` at the budget `n - cost d` is at most its value at `s` and the budget
`n`. A run of an adversary whose queries cost at most `n` in total on every path,
started from `s`, has expected `Φ` of its final state at most `Ψ n s`. -/
theorem run_potential_le {S : Type} (O : S → D → PMF (R × S)) (cost : D → ℕ)
    (Φ : S → ℝ≥0∞) (Ψ : ℕ → S → ℝ≥0∞) (hret : ∀ n s, Φ s ≤ Ψ n s)
    (hstep : ∀ n s d, cost d ≤ n → ∑' x, O s d x * Ψ (n - cost d) x.2 ≤ Ψ n s)
    (A : OracleAdv D R α) (n : ℕ) (hA : A.IsQueryBoundBy cost n) (s : S) :
    ∑' y, run O A s y * Φ y.2 ≤ Ψ n s := by
  induction A generalizing n s with
  | ret a => rw [run_ret, tsum_pure_mul]; exact hret n s
  | rand p k ih =>
    rw [run_rand, tsum_bind_mul]
    calc ∑' b, p b * ∑' y, run O (k b) s y * Φ y.2 ≤ ∑' b, p b * Ψ n s :=
          ENNReal.tsum_le_tsum fun b => by gcongr; exact ih b n (hA b) s
      _ = Ψ n s := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | query d k ih =>
    obtain ⟨hle, hk⟩ := hA
    rw [run_query, tsum_bind_mul]
    calc ∑' x, O s d x * ∑' y, run O (k x.1) x.2 y * Φ y.2
        ≤ ∑' x, O s d x * Ψ (n - cost d) x.2 :=
          ENNReal.tsum_le_tsum fun x => by gcongr; exact ih x.1 _ (hk x.1) x.2
      _ ≤ Ψ n s := hstep n s d hle

/-! ## Layered potentials -/

/-- **Layered potential** of the layers `a` with the weights `w`: layer `0` is `a 0`,
and layer `j + 1` at the budget `n` is `a (j + 1)` plus `w (j + 1)` times the sum of
layer `j` over the budgets below `n`. -/
noncomputable def layerPot {S : Type} (a : ℕ → S → ℝ≥0∞) (w : ℕ → ℝ≥0∞) :
    ℕ → ℕ → S → ℝ≥0∞
  | 0, _, s => a 0 s
  | j + 1, n, s => a (j + 1) s + w (j + 1) * ∑ u ∈ Finset.range n, layerPot a w j u s

section Layer

variable {S : Type} (a : ℕ → S → ℝ≥0∞) (w : ℕ → ℝ≥0∞)

/-- Every layer of the layered potential is above its layer of `a`. -/
theorem le_layerPot (j n : ℕ) (s : S) : a j s ≤ layerPot a w j n s := by
  cases j with
  | zero => exact le_rfl
  | succ j => exact le_self_add

/-- **One step of a layered potential.** Let one call `O s d` keep the expectation of
`a 0` below its value at `s`, and raise the expectation of `a (j + 1)` by at most
`cost d · w (j + 1) · a j s`. Then the expectation of layer `j` at the budget `t`
after the call is at most layer `j` at the budget `t + cost d` before it. -/
theorem layerPot_step (O : S → D → PMF (R × S)) (cost : D → ℕ)
    (h0 : ∀ s d, ∑' x, O s d x * a 0 x.2 ≤ a 0 s)
    (hinc : ∀ j s d, ∑' x, O s d x * a (j + 1) x.2 ≤ a (j + 1) s + cost d * w (j + 1) * a j s)
    (j t : ℕ) (s : S) (d : D) :
    ∑' x, O s d x * layerPot a w j t x.2 ≤ layerPot a w j (t + cost d) s := by
  induction j generalizing t with
  | zero => exact h0 s d
  | succ j ih =>
    simp only [layerPot]
    calc ∑' x, O s d x * (a (j + 1) x.2 + w (j + 1) * ∑ u ∈ Finset.range t, layerPot a w j u x.2)
        = ∑' x, O s d x * a (j + 1) x.2 +
            w (j + 1) * ∑ u ∈ Finset.range t, ∑' x, O s d x * layerPot a w j u x.2 := by
          simp only [mul_add, Finset.mul_sum]
          rw [ENNReal.tsum_add, Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
          congr 1
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr fun x => by ring
      _ ≤ a (j + 1) s + cost d * w (j + 1) * a j s +
            w (j + 1) * ∑ u ∈ Finset.range t, layerPot a w j (u + cost d) s := by
          gcongr with u
          · exact hinc j s d
          · exact ih u
      _ ≤ a (j + 1) s + w (j + 1) * ∑ u ∈ Finset.range (t + cost d), layerPot a w j u s := by
          have hc : (cost d : ℝ≥0∞) * a j s ≤
              ∑ u ∈ Finset.range (cost d), layerPot a w j u s :=
            calc (cost d : ℝ≥0∞) * a j s = ∑ _u ∈ Finset.range (cost d), a j s := by
                  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              _ ≤ _ := Finset.sum_le_sum fun u _ => le_layerPot a w j u s
          have ht : ∑ u ∈ Finset.range t, layerPot a w j (u + cost d) s =
              ∑ u ∈ Finset.range t, layerPot a w j (cost d + u) s :=
            Finset.sum_congr rfl fun u _ => by rw [add_comm]
          rw [add_comm t, Finset.sum_range_add, mul_add, ← add_assoc, ht,
            mul_comm (cost d : ℝ≥0∞), mul_assoc]
          exact add_le_add_left (add_le_add_right (mul_le_mul_right hc _) _) _

/-- **Layered potential bound for a run.** Under the step hypotheses of
`layerPot_step`, a run of an adversary whose queries cost at most `n` in total on
every path, started from `s`, has expected `a j` of its final state at most layer `j`
of the layered potential at the budget `n` and the state `s`. -/
theorem run_layerPot_le (O : S → D → PMF (R × S)) (cost : D → ℕ)
    (h0 : ∀ s d, ∑' x, O s d x * a 0 x.2 ≤ a 0 s)
    (hinc : ∀ j s d, ∑' x, O s d x * a (j + 1) x.2 ≤ a (j + 1) s + cost d * w (j + 1) * a j s)
    (j : ℕ) (A : OracleAdv D R α) (n : ℕ) (hA : A.IsQueryBoundBy cost n) (s : S) :
    ∑' y, run O A s y * a j y.2 ≤ layerPot a w j n s :=
  run_potential_le O cost (a j) (layerPot a w j) (fun n s => le_layerPot a w j n s)
    (fun n s d hle => by
      simpa [Nat.sub_add_cancel hle] using layerPot_step a w O cost h0 hinc j (n - cost d) s d)
    A n hA s

end Layer

/-! ## Multiplicities of fresh values -/

section Mult

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Multiplicity bound.** The counts `c` of the values are at most `K` each. -/
def MultB (K : ℕ) (c : V → ℕ) : Prop := ∀ v, c v ≤ K

/-- The multiplicity layers of the counts `c`: layer `0` is `1`, and layer `j + 1`
is the number of `(j + 1)`-sets of counted points sharing a value,
`Σ_v C(c v, j + 1)`. -/
noncomputable def multLayer (c : V → ℕ) : ℕ → ℝ≥0∞
  | 0 => 1
  | j + 1 => ∑ v, ((c v).choose (j + 1) : ℝ≥0∞)

/-- The weights of the multiplicity layers for the point probability `p`: `1` up to
layer `1`, and `p` above. -/
def multW (p : ℝ≥0∞) (j : ℕ) : ℝ≥0∞ := if j ≤ 1 then 1 else p

/-- The counts `c` with one more point of value `v`. -/
def addCnt (c : V → ℕ) (v : V) : V → ℕ := Function.update c v (c v + 1)

/-- One more point of value `v` adds `C(c v, j)` sets of size `j + 1` sharing a
value. -/
theorem sum_choose_addCnt (c : V → ℕ) (v : V) (j : ℕ) :
    ∑ u, (addCnt c v u).choose (j + 1) = ∑ u, (c u).choose (j + 1) + (c v).choose j := by
  rw [Fintype.sum_eq_add_sum_compl v, Fintype.sum_eq_add_sum_compl v (fun u => (c u).choose _)]
  have hr : ∑ u ∈ ({v}ᶜ : Finset V), (addCnt c v u).choose (j + 1) =
      ∑ u ∈ ({v}ᶜ : Finset V), (c u).choose (j + 1) :=
    Finset.sum_congr rfl fun u hu => by
      rw [addCnt, Function.update_of_ne (by simpa using hu)]
  rw [hr, addCnt, Function.update_self, Nat.choose_succ_succ']
  ring

/-- Layer `j + 1` after one more point of value `v`. -/
theorem multLayer_addCnt (c : V → ℕ) (v : V) (j : ℕ) :
    multLayer (addCnt c v) (j + 1) = multLayer c (j + 1) + ((c v).choose j : ℝ≥0∞) := by
  simp only [multLayer]
  exact_mod_cast sum_choose_addCnt c v j

omit [DecidableEq V] in
/-- Counts that violate the multiplicity bound `K` have layer `K + 1` at least `1`. -/
theorem one_le_multLayer_of_not_multB {K : ℕ} {c : V → ℕ} (h : ¬ MultB K c) :
    1 ≤ multLayer c (K + 1) := by
  obtain ⟨v, hv⟩ : ∃ v, K < c v := by simpa [MultB] using h
  simp only [multLayer]
  calc (1 : ℝ≥0∞) ≤ ((c v).choose (K + 1) : ℝ≥0∞) := by
        exact_mod_cast Nat.choose_pos hv
    _ ≤ _ := Finset.single_le_sum (f := fun u => ((c u).choose (K + 1) : ℝ≥0∞))
        (fun _ _ => zero_le) (Finset.mem_univ v)

/-- Hockey stick: `Σ_{u < n} C(u, k) = C(n, k + 1)`. -/
private theorem sum_range_choose_succ (n k : ℕ) :
    ∑ u ∈ Finset.range n, u.choose k = n.choose (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ' n k, add_comm]

omit [DecidableEq V] in
/-- The layered multiplicity potential at zero counts: layer `j + 1` at the budget
`n` is `C(n, j + 1) · p^j`. -/
theorem layerPot_multLayer_zero {S : Type} (cnt : S → V → ℕ) (p : ℝ≥0∞) (s : S)
    (hs : cnt s = 0) (j n : ℕ) :
    layerPot (fun j s => multLayer (cnt s) j) (multW p) (j + 1) n s = n.choose (j + 1) * p ^ j := by
  induction j generalizing n with
  | zero => simp [layerPot, multLayer, multW, hs]
  | succ j ih =>
    rw [layerPot, show multLayer (cnt s) (j + 1 + 1) = 0 by simp [multLayer, hs]]
    simp only [ih, zero_add, multW, show ¬ j + 1 + 1 ≤ 1 by omega, if_false]
    rw [← Finset.sum_mul, ← Nat.cast_sum, sum_range_choose_succ, pow_succ]
    ring

/-- **Fresh values, one per call.** A call `O s d` either keeps the counts `cnt` or,
when it costs at least `1`, adds one point of some value; and it adds a point of a
given value `v` with probability at most `p`. -/
structure FreshMult {S : Type} (O : S → D → PMF (R × S)) (cost : D → ℕ) (cnt : S → V → ℕ)
    (p : ℝ≥0∞) : Prop where
  /-- Every outcome keeps the counts or, at a positive cost, adds one point. -/
  supp : ∀ s d x, x ∈ (O s d).support →
    cnt x.2 = cnt s ∨ (1 ≤ cost d ∧ ∃ v, cnt x.2 = addCnt (cnt s) v)
  /-- A point of the value `v` is added with probability at most `p`. -/
  point : ∀ s d v, (O s d).toOuterMeasure {x | cnt x.2 = addCnt (cnt s) v} ≤ p

omit [Fintype V] in
/-- Adding a point changes the counts. -/
theorem addCnt_ne (c : V → ℕ) (v : V) : addCnt c v ≠ c := fun h => by
  have := congrFun h v
  simp [addCnt] at this

/-- The expectation of a constant on an event is its probability times the constant. -/
private theorem tsum_mul_indicator_const {β : Type} (q : PMF β) (E : Set β) (k : ℝ≥0∞) :
    ∑' x, q x * E.indicator (fun _ => k) x = q.toOuterMeasure E * k := by
  rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ E <;> simp [hx]

section Fresh

variable {S : Type} {O : S → D → PMF (R × S)} {cost : D → ℕ} {cnt : S → V → ℕ} {p : ℝ≥0∞}

omit [Fintype V] in
/-- A call adds a point of the value `v` with probability at most `cost d · p`. -/
theorem FreshMult.point_le_cost (hO : FreshMult O cost cnt p) (s : S) (d : D) (v : V) :
    (O s d).toOuterMeasure {x | cnt x.2 = addCnt (cnt s) v} ≤ cost d * p := by
  rcases Nat.eq_zero_or_pos (cost d) with h | h
  · refine le_of_eq_of_le ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr ?_) zero_le
    refine Set.disjoint_left.mpr fun x hx hE => ?_
    rcases hO.supp s d x hx with h' | ⟨h1, _⟩
    · exact addCnt_ne (cnt s) v (hE.symm.trans h')
    · omega
  · exact (hO.point s d v).trans (le_mul_of_one_le_left zero_le (by exact_mod_cast h))

/-- Layer `j + 1` of an outcome of a call is at most layer `j + 1` before the call plus
`C(cnt s v, j)` on the event that the call adds a point of the value `v`. -/
theorem FreshMult.multLayer_le (hO : FreshMult O cost cnt p) (s : S) (d : D) (j : ℕ)
    (x : R × S) (hx : x ∈ (O s d).support) :
    multLayer (cnt x.2) (j + 1) ≤ multLayer (cnt s) (j + 1) +
      ∑ v, {x : R × S | cnt x.2 = addCnt (cnt s) v}.indicator
        (fun _ => ((cnt s v).choose j : ℝ≥0∞)) x := by
  rcases hO.supp s d x hx with h | ⟨_, v, hv⟩
  · rw [h]; exact le_self_add
  · rw [hv, multLayer_addCnt]
    gcongr
    refine le_of_eq_of_le ?_ (Finset.single_le_sum (f := fun u => {x : R × S |
      cnt x.2 = addCnt (cnt s) u}.indicator (fun _ => ((cnt s u).choose j : ℝ≥0∞)) x)
      (fun _ _ => zero_le) (Finset.mem_univ v))
    rw [Set.indicator_of_mem (show x ∈ {x : R × S | cnt x.2 = addCnt (cnt s) v} from hv)]

/-- **Expected increment of the multiplicity layers.** For fresh values, one call
raises the expectation of layer `j + 1` by at most `cost d · multW p (j + 1)` times
layer `j` before the call. -/
theorem FreshMult.multLayer_inc (hO : FreshMult O cost cnt p) (j : ℕ) (s : S) (d : D) :
    ∑' x, O s d x * multLayer (cnt x.2) (j + 1) ≤
      multLayer (cnt s) (j + 1) + cost d * multW p (j + 1) * multLayer (cnt s) j := by
  cases j with
  | zero =>
    calc ∑' x, O s d x * multLayer (cnt x.2) 1
        ≤ ∑' x, O s d x * (multLayer (cnt s) 1 + cost d) := by
          refine ENNReal.tsum_le_tsum fun x => ?_
          by_cases hx : O s d x = 0
          · simp [hx]
          · gcongr
            rcases hO.supp s d x ((PMF.mem_support_iff _ _).mpr hx) with h | ⟨h1, v, hv⟩
            · rw [h]; exact le_self_add
            · rw [hv, multLayer_addCnt]
              gcongr
              simpa using (show (1 : ℝ≥0∞) ≤ cost d by exact_mod_cast h1)
      _ = multLayer (cnt s) 1 + cost d * multW p 1 * multLayer (cnt s) 0 := by
          rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
          simp [multW, multLayer]
  | succ j =>
    calc ∑' x, O s d x * multLayer (cnt x.2) (j + 1 + 1)
        ≤ ∑' x, O s d x * (multLayer (cnt s) (j + 1 + 1) +
            ∑ v, {x : R × S | cnt x.2 = addCnt (cnt s) v}.indicator
              (fun _ => ((cnt s v).choose (j + 1) : ℝ≥0∞)) x) := by
          refine ENNReal.tsum_le_tsum fun x => ?_
          by_cases hx : O s d x = 0
          · simp [hx]
          · gcongr
            exact hO.multLayer_le s d (j + 1) x ((PMF.mem_support_iff _ _).mpr hx)
      _ = multLayer (cnt s) (j + 1 + 1) + ∑ v, (O s d).toOuterMeasure
            {x : R × S | cnt x.2 = addCnt (cnt s) v} * ((cnt s v).choose (j + 1) : ℝ≥0∞) := by
          simp only [mul_add, Finset.mul_sum]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
            Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
          simp only [tsum_mul_indicator_const]
      _ ≤ multLayer (cnt s) (j + 1 + 1) +
            ∑ v, cost d * p * ((cnt s v).choose (j + 1) : ℝ≥0∞) := by
          gcongr with v
          exact hO.point_le_cost s d v
      _ = _ := by
          rw [← Finset.mul_sum]
          simp [multW, multLayer]

end Fresh

/-- **Multiplicity bound for fresh values.** Let every call of `O` add at most one
point, at a positive cost, with each value hit with probability at most `p`
(`FreshMult`). A run of an adversary whose queries cost at most `N` in total on
every path, started from a state with no points, ends with more than `K` points of
some value with probability at most `C(N, K + 1) · p^K`. -/
theorem run_not_multB_le {S : Type} {O : S → D → PMF (R × S)} {cost : D → ℕ}
    {cnt : S → V → ℕ} {p : ℝ≥0∞} (hO : FreshMult O cost cnt p) (K : ℕ)
    (A : OracleAdv D R α) (N : ℕ) (hA : A.IsQueryBoundBy cost N) (s : S) (hs : cnt s = 0) :
    (run O A s).toOuterMeasure {y | ¬ MultB K (cnt y.2)} ≤ N.choose (K + 1) * p ^ K := by
  calc (run O A s).toOuterMeasure {y | ¬ MultB K (cnt y.2)}
      ≤ ∑' y, run O A s y * multLayer (cnt y.2) (K + 1) := by
        rw [PMF.toOuterMeasure_apply]
        refine ENNReal.tsum_le_tsum fun y => ?_
        by_cases hy : ¬ MultB K (cnt y.2)
        · rw [Set.indicator_of_mem (show y ∈ {y : α × S | ¬ MultB K (cnt y.2)} from hy)]
          exact le_mul_of_one_le_right zero_le (one_le_multLayer_of_not_multB hy)
        · rw [Set.indicator_of_notMem (show y ∉ {y : α × S | ¬ MultB K (cnt y.2)} from hy)]
          exact zero_le
    _ ≤ layerPot (fun j s => multLayer (cnt s) j) (multW p) (K + 1) N s :=
        run_layerPot_le (fun j s => multLayer (cnt s) j) (multW p) O cost
          (fun s d => by simp [multLayer]) (fun j s d => hO.multLayer_inc j s d) (K + 1) A N hA s
    _ = N.choose (K + 1) * p ^ K := layerPot_multLayer_zero cnt p s hs K N

end Mult

end CatCrypt.Crypto.OracleAdv
