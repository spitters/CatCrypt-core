/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.CompressedOracleLocal

/-!
# The collision bound for the compressed oracle

Zhandry's collision bound (CRYPTO 2019, ePrint 2018/276, Section 5) in its
database form: after `q` queries of an adversary `A : QAdv m n w q` to the
compressed oracle of a uniformly random function `Fin m → Fin n`, started from
the empty database, measuring the database register finds two distinct inputs
with the same non-`⊥` entry with probability at most `8 q³ / n`.

The proof follows Zhandry's progress measure. Let `P` be the projector onto the
databases holding a collision. A call of the per-query oracle `cmpLocal` on a
state supported on databases with at most `j` non-`⊥` entries
(`runCmp_database_le`) moves amplitude `‖P O (1 - P) v‖ ≤ 2 √(2 (j + 1) / n) ‖v‖`
from the collision-free part into `P`: decompressing the queried entry `x`
puts it in the uniform superposition, whose overlap with the at most `j` values
held by the other entries has squared norm `j / n`. The adversary's unitaries
commute with `P`, so the norm of the projection grows by at most this amount at
each query.

## Main definitions

* `dbColl k` — the database `k` holds a collision
* `collDbProj m n`, `collProj m n d` — the projector onto the databases holding
  a collision, on the database register and on the total register
* `SuppLe s v` — the vector `v` is supported on databases with at most `s`
  non-`⊥` entries
* `prDbColl A` — the probability that measuring the database register after the
  `q`-query compressed run of `A` finds a collision

## Main results

* `nrm_collProj_cmpLocal_le` — one query moves at most `2 √(2 (j + 1) / n) ‖v‖`
  into the collision subspace
* `nrm_proj_chainOp_le` — the progress bound along a query chain
* `prDbColl_le` — `prDbColl A ≤ 8 q³ / n`

## References

* [Zhandry — How to Record Quantum Queries, and Applications to Quantum
  Indifferentiability, CRYPTO 2019, ePrint 2018/276]
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct
  CatCrypt.Quantum.UnitaryChannel CatCrypt.Quantum.Measurement

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Collisions in the database -/

section Coll

variable {m n : ℕ}

/-- The database `k` holds a collision: two distinct inputs with the same
    non-`⊥` entry. -/
def dbColl (k : Fin ((n + 1) ^ m)) : Prop :=
  ∃ x x', x ≠ x' ∧ (dbIndex m n).symm k x ≠ Fin.last n ∧
    (dbIndex m n).symm k x = (dbIndex m n).symm k x'

variable (m n) in
open Classical in
/-- The projector onto the databases holding a collision. -/
def collDbProj : Matrix (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) ℂ :=
  Matrix.diagonal fun k => if dbColl (m := m) (n := n) k then 1 else 0

variable (m n) in
/-- The projector onto the databases holding a collision, tensored with the
    identity on the other registers. -/
def collProj (d : ℕ) : Matrix (Fin (d * (n + 1) ^ m)) (Fin (d * (n + 1) ^ m)) ℂ :=
  (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ collDbProj m n

/-- The vector `v` is supported on databases with at most `s` non-`⊥` entries. -/
def SuppLe {d : ℕ} (s : ℕ) (v : Fin (d * (n + 1) ^ m) → ℂ) : Prop :=
  ∀ K, s < totWeight (m := m) (n := n) K → v K = 0

variable {d : ℕ}

theorem collDbProj_mul_self : collDbProj m n * collDbProj m n = collDbProj m n := by
  rw [collDbProj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  split_ifs <;> simp

theorem collDbProj_conjTranspose : (collDbProj m n)ᴴ = collDbProj m n := by
  rw [collDbProj, Matrix.diagonal_conjTranspose]
  congr 1
  funext k
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem collProj_mul_self : collProj m n d * collProj m n d = collProj m n d := by
  rw [collProj, kronecker_mul_kronecker, Matrix.one_mul, collDbProj_mul_self]

theorem collProj_conjTranspose : (collProj m n d)ᴴ = collProj m n d := by
  rw [collProj, conjTranspose_kronecker, conjTranspose_one, collDbProj_conjTranspose]

/-- A matrix whose nonzero entries lie on the diagonal adds no entry. -/
theorem weightBound_of_apply_ne_zero_eq {M : Matrix (Fin (d * (n + 1) ^ m)) _ ℂ}
    (h : ∀ K L, M K L ≠ 0 → K = L) : WeightBound (m := m) (n := n) M 0 := by
  intro K L hKL
  rw [h K L hKL]
  omega

theorem suppLe_mulVec_of_weightBound {M : Matrix (Fin (d * (n + 1) ^ m)) _ ℂ} {s k : ℕ}
    (hM : WeightBound (m := m) (n := n) M s) {v : Fin (d * (n + 1) ^ m) → ℂ}
    (hv : SuppLe (m := m) (n := n) k v) : SuppLe (m := m) (n := n) (k + s) (M *ᵥ v) := by
  intro K hK
  rw [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun L _ => ?_
  by_cases hML : M K L = 0
  · rw [hML, zero_mul]
  · have := hM K L hML
    rw [hv L (by omega), mul_zero]

/-- A database with at most one non-`⊥` entry holds no collision. -/
theorem not_dbColl_of_dbWeight_le_one (k : Fin ((n + 1) ^ m))
    (hk : dbWeight (m := m) (n := n) k ≤ 1) : ¬ dbColl (m := m) (n := n) k := by
  rintro ⟨x, x', hxx, hx, hxe⟩
  have h2 : ({x, x'} : Finset (Fin m)) ⊆
      Finset.univ.filter fun y => (dbIndex m n).symm k y ≠ Fin.last n := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · simpa using hx
    · simpa [← hxe] using hx
  have := Finset.card_le_card h2
  rw [Finset.card_pair hxx] at this
  unfold dbWeight at hk
  omega

open Classical in
theorem collProj_apply (K L : Fin (d * (n + 1) ^ m)) :
    collProj m n d K L = if K = L then
      (if dbColl (m := m) (n := n) ((finProdEquiv d ((n + 1) ^ m)).symm K).2 then 1 else 0)
      else 0 := by
  rw [collProj, TensorProduct.kronecker_apply, Matrix.one_apply, collDbProj, Matrix.diagonal_apply]
  by_cases h : K = L
  · subst h; simp
  · have : ¬(((finProdEquiv d ((n + 1) ^ m)).symm K).1 = ((finProdEquiv d ((n + 1) ^ m)).symm L).1 ∧
        ((finProdEquiv d ((n + 1) ^ m)).symm K).2 = ((finProdEquiv d ((n + 1) ^ m)).symm L).2) :=
      fun ⟨h1, h2⟩ => h ((finProdEquiv d ((n + 1) ^ m)).symm.injective (Prod.ext h1 h2))
    rcases not_and_or.mp this with h1 | h2
    · simp [h, h1]
    · simp [h, h2]

theorem collProj_mulVec_eq_zero_of_suppLe {v : Fin (d * (n + 1) ^ m) → ℂ}
    (hv : SuppLe (m := m) (n := n) 0 v) : collProj m n d *ᵥ v = 0 := by
  funext K
  rw [Matrix.mulVec, dotProduct, Pi.zero_apply]
  refine Finset.sum_eq_zero fun L _ => ?_
  rw [collProj_apply]
  by_cases hKL : K = L
  · subst hKL
    by_cases hw : totWeight (m := m) (n := n) K = 0
    · have hc := not_dbColl_of_dbWeight_le_one (m := m) (n := n)
        ((finProdEquiv d ((n + 1) ^ m)).symm K).2 (by unfold totWeight at hw; omega)
      simp [hc]
    · rw [hv K (by omega), mul_zero]
  · simp [hKL]

end Coll

/-! ## The progress bound along a chain -/

section Chain

variable {m n d : ℕ}

/-- Zhandry's progress measure: if every query moves at most `ε j ‖y‖` from the
    complement of `P` into `P` on vectors supported on databases with at most
    `j` entries, the adversary's unitaries commute with `P` and add no entry,
    then after `q` queries from a vector with at most `k` entries the projection
    onto `P` has grown by at most `∑_{i < q} ε (k + i)` times the norm. -/
theorem nrm_proj_chainOp_le (P O : Matrix (Fin (d * (n + 1) ^ m)) (Fin (d * (n + 1) ^ m)) ℂ)
    (hPI : P * P = P) (hPH : Pᴴ = P) (hO : O ∈ Matrix.unitaryGroup _ ℂ)
    (hOw : WeightBound (m := m) (n := n) O 1) (ε : ℕ → ℝ)
    (hstep : ∀ j y, SuppLe (m := m) (n := n) j y →
      nrm (P *ᵥ (O *ᵥ ((1 - P) *ᵥ y))) ≤ ε j * nrm y) :
    ∀ (q : ℕ) (U : Fin (q + 1) → Matrix.unitaryGroup (Fin (d * (n + 1) ^ m)) ℂ),
      (∀ i, WeightBound (m := m) (n := n)
        ((U i : Matrix.unitaryGroup _ ℂ) : Matrix (Fin (d * (n + 1) ^ m)) _ ℂ) 0) →
      (∀ i, P * ((U i : Matrix.unitaryGroup _ ℂ) : Matrix (Fin (d * (n + 1) ^ m)) _ ℂ) =
        ((U i : Matrix.unitaryGroup _ ℂ) : Matrix (Fin (d * (n + 1) ^ m)) _ ℂ) * P) →
      ∀ (k : ℕ) (v : Fin (d * (n + 1) ^ m) → ℂ), SuppLe (m := m) (n := n) k v →
        nrm (P *ᵥ (chainOp O q U *ᵥ v)) ≤
          nrm (P *ᵥ v) + (∑ i ∈ Finset.range q, ε (k + i)) * nrm v := by
  intro q
  induction q with
  | zero =>
    intro U _ hPU k v _
    simp only [chainOp, Finset.range_zero, Finset.sum_empty, zero_mul, add_zero]
    rw [mulVec_mulVec, hPU 0, ← mulVec_mulVec, nrm_mulVec_of_mem_unitaryGroup (U 0).prop]
  | succ q ih =>
    intro U hUw hPU k v hv
    rw [chainOp_succ_mulVec]
    set A0 : Matrix (Fin (d * (n + 1) ^ m)) (Fin (d * (n + 1) ^ m)) ℂ := (U 0).val with hA0
    have hA0m : A0 ∈ Matrix.unitaryGroup _ ℂ := (U 0).prop
    have hPA : P * A0 = A0 * P := hPU 0
    have hu0s : SuppLe (m := m) (n := n) k (A0 *ᵥ v) := by
      simpa using suppLe_mulVec_of_weightBound (hUw 0) hv
    have hv1 := suppLe_mulVec_of_weightBound hOw hu0s
    have hn0 : nrm (A0 *ᵥ v) = nrm v := nrm_mulVec_of_mem_unitaryGroup hA0m v
    have hn1 : nrm (O *ᵥ (A0 *ᵥ v)) = nrm v := by
      rw [nrm_mulVec_of_mem_unitaryGroup hO, hn0]
    have hP0 : nrm (P *ᵥ (A0 *ᵥ v)) = nrm (P *ᵥ v) := by
      rw [mulVec_mulVec, hPA, ← mulVec_mulVec, nrm_mulVec_of_mem_unitaryGroup hA0m]
    have hsplit : ∀ u : Fin (d * (n + 1) ^ m) → ℂ,
        P *ᵥ (O *ᵥ u) = P *ᵥ (O *ᵥ (P *ᵥ u)) + P *ᵥ (O *ᵥ ((1 - P) *ᵥ u)) := by
      intro u
      rw [← mulVec_add, ← mulVec_add, ← add_mulVec, add_sub_cancel, one_mulVec]
    have h1 : nrm (P *ᵥ (O *ᵥ (A0 *ᵥ v))) ≤ nrm (P *ᵥ v) + ε k * nrm v := by
      rw [hsplit]
      refine (nrm_add_le _ _).trans (add_le_add ?_ ?_)
      · exact ((nrm_proj_mulVec_le hPI hPH _).trans
          (nrm_mulVec_of_mem_unitaryGroup hO _).le).trans hP0.le
      · rw [← hn0]; exact hstep k _ hu0s
    have h2 := ih (Fin.tail U) (fun i => hUw i.succ) (fun i => hPU i.succ) (k + 1) _ hv1
    rw [hn1] at h2
    have hs : ∑ i ∈ Finset.range q, ε (k + 1 + i) = ∑ i ∈ Finset.range q, ε (k + (i + 1)) :=
      Finset.sum_congr rfl fun i _ => by rw [add_assoc, add_comm 1 i]
    rw [hs] at h2
    rw [Finset.sum_range_succ', add_zero]
    nlinarith [nrm_nonneg v]

end Chain

/-! ## One query -/

section DbOps

variable {m n : ℕ}

variable (m n) in
/-- The operator `|u⟩⟨u|` on the database entry `x`, for
    `u = |⊥⟩ - entryUniform n`, and the identity on the other entries. -/
def rDb (x : Fin m) : Matrix (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) ℂ :=
  dbOp m n (Function.update 1 x (vecMulVec (entryDiff n) (star (entryDiff n))))

/-- The entries of the database `k` other than `x` hold a collision. -/
def offColl (x : Fin m) (k : Fin ((n + 1) ^ m)) : Prop :=
  ∃ y y', y ≠ x ∧ y' ≠ x ∧ y ≠ y' ∧ (dbIndex m n).symm k y ≠ Fin.last n ∧
    (dbIndex m n).symm k y = (dbIndex m n).symm k y'

variable (m n) in
open Classical in
/-- The projector onto the databases whose entries other than `x` hold no
    collision. -/
def offFreeDb (x : Fin m) : Matrix (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) ℂ :=
  Matrix.diagonal fun k => if offColl (m := m) (n := n) x k then 0 else 1

theorem dbOp_one : dbOp m n (1 : Fin m → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = 1 := by
  ext i j
  rw [dbOp_apply]
  by_cases h : i = j
  · subst h; simp
  · have hne : ∃ x', (dbIndex m n).symm i x' ≠ (dbIndex m n).symm j x' := by
      by_contra hc
      exact h ((dbIndex m n).symm.injective
        (funext fun x' => not_not.mp fun hx => hc ⟨x', hx⟩))
    obtain ⟨x', hx'⟩ := hne
    rw [Finset.prod_eq_zero (Finset.mem_univ x') (by simp [Matrix.one_apply_ne hx']),
      Matrix.one_apply_ne h]

theorem dbOp_update_apply (F : Fin m → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (x : Fin m)
    (Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i j : Fin ((n + 1) ^ m)) :
    dbOp m n (Function.update F x Z) i j =
      Z ((dbIndex m n).symm i x) ((dbIndex m n).symm j x) *
        ∏ y ∈ Finset.univ.erase x, F y ((dbIndex m n).symm i y) ((dbIndex m n).symm j y) := by
  rw [dbOp_apply, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x),
    Function.update_self]
  congr 1
  exact Finset.prod_congr rfl fun y hy => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hy)]

theorem decompAt_eq_one_sub (x : Fin m) : decompAt m n x = 1 - rDb m n x := by
  ext i j
  rw [decompAt, rDb, Matrix.sub_apply, dbOp_update_apply, dbOp_update_apply, decompEntry,
    Matrix.sub_apply, sub_mul]
  congr 1
  have h := dbOp_update_apply (m := m) (n := n)
    (1 : Fin m → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) x 1 i j
  rw [show Function.update (1 : Fin m → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) x 1 = 1 from
    Function.update_eq_self x 1, dbOp_one] at h
  exact h.symm

/-- A diagonal operator whose entries depend only on the entries other than `x`
    commutes with an operator acting on the entry `x` alone. -/
theorem diagonal_mul_dbOp_update_comm (x : Fin m) (g : Fin ((n + 1) ^ m) → ℂ)
    (hg : ∀ i j, (∀ y, y ≠ x → (dbIndex m n).symm i y = (dbIndex m n).symm j y) → g i = g j)
    (Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Matrix.diagonal g * dbOp m n (Function.update 1 x Z) =
      dbOp m n (Function.update 1 x Z) * Matrix.diagonal g := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : dbOp m n (Function.update 1 x Z) i j = 0
  · rw [h, mul_zero, zero_mul]
  · rw [hg i j fun y hy => dbOp_update_apply_ne_zero m n x Z i j h y hy, mul_comm]

theorem nrm_sq_eq_sum_norm_sq {N : ℕ} (v : Fin N → ℂ) : nrm v ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  unfold nrm
  rw [EuclideanSpace.norm_sq_eq]

/-- The slice of a total-register vector at the index `a` of the first factor. -/
def dbSlice {d : ℕ} (v : Fin (d * (n + 1) ^ m) → ℂ) (a : Fin d) : Fin ((n + 1) ^ m) → ℂ :=
  fun i => v (finProdEquiv d ((n + 1) ^ m) (a, i))

theorem nrm_sq_eq_sum_dbSlice {d : ℕ} (v : Fin (d * (n + 1) ^ m) → ℂ) :
    nrm v ^ 2 = ∑ a, nrm (dbSlice v a) ^ 2 := by
  simp only [nrm_sq_eq_sum_norm_sq, dbSlice]
  rw [← (finProdEquiv d ((n + 1) ^ m)).sum_comp, Fintype.sum_prod_type]

theorem one_kronecker_mulVec_dbSlice {d : ℕ}
    (M : Matrix (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) ℂ) (v : Fin (d * (n + 1) ^ m) → ℂ)
    (a : Fin d) :
    dbSlice (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ M) *ᵥ v) a = M *ᵥ dbSlice v a := by
  funext i
  simp only [dbSlice, Matrix.mulVec, dotProduct]
  rw [← (finProdEquiv d ((n + 1) ^ m)).sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · have he := (finProdEquiv d ((n + 1) ^ m)).symm_apply_apply
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [TensorProduct.kronecker_apply, he, he]
    simp
  · intro b _ hb
    have he := (finProdEquiv d ((n + 1) ^ m)).symm_apply_apply
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [TensorProduct.kronecker_apply, he, he]
    simp [Matrix.one_apply_ne (Ne.symm hb)]
  · simp

/-- The slice reduction: a bound of `M` on every slice bounds `1 ⊗ₖ M`. -/
theorem nrm_one_kronecker_mulVec_le {d : ℕ}
    (M : Matrix (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) ℂ) (c : ℝ) (hc : 0 ≤ c)
    (v : Fin (d * (n + 1) ^ m) → ℂ)
    (h : ∀ a, nrm (M *ᵥ dbSlice v a) ^ 2 ≤ c ^ 2 * nrm (dbSlice v a) ^ 2) :
    nrm (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ M) *ᵥ v) ≤ c * nrm v := by
  have hsq : nrm (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ M) *ᵥ v) ^ 2 ≤ (c * nrm v) ^ 2 := by
    rw [nrm_sq_eq_sum_dbSlice, mul_pow, nrm_sq_eq_sum_dbSlice v, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [one_kronecker_mulVec_dbSlice]
    exact h a
  exact (pow_le_pow_iff_left₀ (nrm_nonneg _) (mul_nonneg hc (nrm_nonneg _)) two_ne_zero).mp hsq

/-- `rDb x` applied to `z`: the entry `x` is projected onto `u`. -/
theorem rDb_mulVec_apply (x : Fin m) (z : Fin ((n + 1) ^ m) → ℂ) (i : Fin ((n + 1) ^ m)) :
    (rDb m n x *ᵥ z) i = entryDiff n ((dbIndex m n).symm i x) *
      ∑ e, star (entryDiff n e) * z (dbIndex m n (Function.update ((dbIndex m n).symm i) x e)) := by
  rw [Matrix.mulVec, dotProduct, ← (dbIndex m n).sum_comp, Finset.mul_sum]
  symm
  refine Fintype.sum_of_injective (fun e => Function.update ((dbIndex m n).symm i) x e)
    (Function.update_injective ((dbIndex m n).symm i) x) _ _ ?_ ?_
  · intro G hG
    have hex : ∃ y, y ≠ x ∧ (dbIndex m n).symm i y ≠ G y := by
      by_contra hc
      apply hG
      refine ⟨G x, funext fun y => ?_⟩
      by_cases hy : y = x
      · subst hy; simp
      · beta_reduce
        rw [Function.update_of_ne hy]
        by_contra h'
        exact hc ⟨y, hy, h'⟩
    obtain ⟨y, hy, hne⟩ := hex
    rw [rDb, dbOp_update_apply, Equiv.symm_apply_apply,
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hy, Finset.mem_univ y⟩)
        (by simp [Matrix.one_apply_ne hne]), mul_zero, zero_mul]
  · intro e
    rw [rDb, dbOp_update_apply, Equiv.symm_apply_apply, Finset.prod_eq_one, mul_one,
      Function.update_self, vecMulVec_apply]
    · simp only [Pi.star_apply]
      ring
    · intro y hy
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hy)]
      simp

/-- Cauchy–Schwarz against `u`, whose squared norm is `2`. -/
theorem norm_sum_star_entryDiff_mul_sq_le [NeZero n] (f : Fin (n + 1) → ℂ) :
    ‖∑ e, star (entryDiff n e) * f e‖ ^ 2 ≤ 2 * ∑ e, ‖f e‖ ^ 2 := by
  have hu : ∑ e, ‖entryDiff n e‖ ^ 2 = 2 := by
    have h := star_entryDiff_dotProduct (n := n)
    rw [dotProduct] at h
    have h' : ((∑ e, ‖entryDiff n e‖ ^ 2 : ℝ) : ℂ) = 2 := by
      rw [← h, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Pi.star_apply, Complex.star_def, Complex.conj_mul']
      push_cast; rfl
    exact_mod_cast h'
  have h1 : ‖∑ e, star (entryDiff n e) * f e‖ ≤ ∑ e, ‖entryDiff n e‖ * ‖f e‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun e _ => by
      rw [norm_mul, norm_star]))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun e => ‖entryDiff n e‖)
    (fun e => ‖f e‖)
  rw [hu] at h2
  calc ‖∑ e, star (entryDiff n e) * f e‖ ^ 2 ≤ (∑ e, ‖entryDiff n e‖ * ‖f e‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ 2 * ∑ e, ‖f e‖ ^ 2 := h2

theorem norm_entryDiff_sq_of_ne (y : Fin (n + 1)) (hy : y ≠ Fin.last n) :
    ‖entryDiff n y‖ ^ 2 = 1 / n := by
  have hlt : (y : ℕ) < n := Fin.val_lt_last hy
  rw [entryDiff, Pi.sub_apply, Pi.single_eq_of_ne hy, entryUniform, ite_eq_left hlt, zero_sub,
    norm_neg, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg n), one_div]

/-- A database with a collision and none off `x` has its entry `x` non-`⊥` and
    equal to another entry. -/
theorem hit_of_dbColl_not_offColl (x : Fin m) (i : Fin ((n + 1) ^ m))
    (hc : dbColl (m := m) (n := n) i) (ho : ¬ offColl (m := m) (n := n) x i) :
    (dbIndex m n).symm i x ≠ Fin.last n ∧
      ∃ y, y ≠ x ∧ (dbIndex m n).symm i y = (dbIndex m n).symm i x := by
  obtain ⟨y1, y2, h12, h1, he⟩ := hc
  by_cases hx1 : y1 = x
  · subst hx1
    exact ⟨h1, y2, Ne.symm h12, he.symm⟩
  · by_cases hx2 : y2 = x
    · subst hx2
      exact ⟨he ▸ h1, y1, hx1, he⟩
    · exact absurd ⟨y1, y2, hx1, hx2, h12, h1, he⟩ ho

open Classical in
/-- The weight of the database `G` in the bound: the collision-and-none-off-`x`
    indicator times `|u(G x)|²`. -/
def hitWeight (x : Fin m) (G : Fin m → Fin (n + 1)) : ℝ :=
  (if dbColl (m := m) (n := n) (dbIndex m n G) ∧ ¬ offColl (m := m) (n := n) x (dbIndex m n G)
    then 1 else 0) * ‖entryDiff n (G x)‖ ^ 2

/-- The counting step: over the values of the entry `x`, the hit weight sums to
    at most `j / n` when the database holds at most `j` non-`⊥` entries. -/
theorem sum_hitWeight_update_le (x : Fin m) (j : ℕ) (F : Fin m → Fin (n + 1))
    (hF : dbWeight (m := m) (n := n) (dbIndex m n F) ≤ j) :
    ∑ e, hitWeight x (Function.update F x e) ≤ j / n := by
  classical
  set S := (Finset.univ.filter fun y => y ≠ x ∧ F y ≠ Fin.last n).image F with hS
  have hzero : ∀ e ∉ S, hitWeight x (Function.update F x e) = 0 := by
    intro e he
    have hnot : ¬ (dbColl (m := m) (n := n) (dbIndex m n (Function.update F x e)) ∧
        ¬ offColl (m := m) (n := n) x (dbIndex m n (Function.update F x e))) := by
      rintro ⟨hc, ho⟩
      obtain ⟨h1, y, hy, hyx⟩ := hit_of_dbColl_not_offColl x _ hc ho
      rw [Equiv.symm_apply_apply, Function.update_self] at h1 hyx
      rw [Function.update_of_ne hy] at hyx
      exact he (Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hy, by rw [hyx]; exact h1⟩, hyx⟩)
    simp [hitWeight, hnot]
  have hle : ∀ e ∈ S, hitWeight x (Function.update F x e) ≤ 1 / n := by
    intro e he
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp he
    have hne : F y ≠ Fin.last n := (Finset.mem_filter.mp hy).2.2
    unfold hitWeight
    rw [Function.update_self, norm_entryDiff_sq_of_ne _ hne]
    split_ifs
    · rw [one_mul]
    · rw [zero_mul]; positivity
  have hcard : S.card ≤ j := by
    refine Finset.card_image_le.trans ((Finset.card_le_card ?_).trans hF)
    intro y hy
    rw [Finset.mem_filter] at hy ⊢
    exact ⟨hy.1, by rw [Equiv.symm_apply_apply]; exact hy.2.2⟩
  calc ∑ e, hitWeight x (Function.update F x e)
      = ∑ e ∈ S, hitWeight x (Function.update F x e) :=
        (Finset.sum_subset (Finset.subset_univ S) fun e _ he => hzero e he).symm
    _ ≤ ∑ _e ∈ S, (1 / n : ℝ) := Finset.sum_le_sum hle
    _ = S.card * (1 / n : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ j * (1 / n : ℝ) := by gcongr
    _ = j / n := by ring

/-- Reindexing `(D, e) ↦ (D[x := e], D x)`. -/
theorem sum_sum_update_comm (x : Fin m) (w h : (Fin m → Fin (n + 1)) → ℝ) :
    ∑ F, ∑ e, w F * h (Function.update F x e) = ∑ G, ∑ e, w (Function.update G x e) * h G := by
  let σ : (Fin m → Fin (n + 1)) × Fin (n + 1) ≃ (Fin m → Fin (n + 1)) × Fin (n + 1) :=
    { toFun := fun p => (Function.update p.1 x p.2, p.1 x)
      invFun := fun p => (Function.update p.1 x p.2, p.1 x)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv σ _ _ fun p => by simp [σ]

/-- The database-level bound. -/
theorem nrm_sq_collDb_rDb_le [NeZero n] (x : Fin m) (j : ℕ) (z : Fin ((n + 1) ^ m) → ℂ)
    (hz : ∀ i, j < dbWeight (m := m) (n := n) i → z i = 0) :
    nrm ((collDbProj m n * offFreeDb m n x * rDb m n x) *ᵥ z) ^ 2 ≤
      (2 * j / n) * nrm z ^ 2 := by
  classical
  have hM : collDbProj m n * offFreeDb m n x = Matrix.diagonal fun k =>
      (if dbColl (m := m) (n := n) k then (1 : ℂ) else 0) *
        (if offColl (m := m) (n := n) x k then 0 else 1) := by
    rw [collDbProj, offFreeDb, Matrix.diagonal_mul_diagonal]
  have hw0 : ∀ F : Fin m → Fin (n + 1), 0 ≤ hitWeight x F := fun F => by
    unfold hitWeight
    split_ifs <;> positivity
  have hstep : nrm ((collDbProj m n * offFreeDb m n x * rDb m n x) *ᵥ z) ^ 2 ≤
      ∑ F, ∑ e, 2 * (hitWeight x F *
        ‖z (dbIndex m n (Function.update F x e))‖ ^ 2) := by
    rw [nrm_sq_eq_sum_norm_sq, ← (dbIndex m n).sum_comp]
    refine Finset.sum_le_sum fun F _ => ?_
    rw [hM, ← mulVec_mulVec, mulVec_diagonal, rDb_mulVec_apply, Equiv.symm_apply_apply]
    have hcs := norm_sum_star_entryDiff_mul_sq_le
      (fun e => z (dbIndex m n (Function.update F x e)))
    have hind : ‖(if dbColl (m := m) (n := n) (dbIndex m n F) then (1 : ℂ) else 0) *
        (if offColl (m := m) (n := n) x (dbIndex m n F) then 0 else 1)‖ ^ 2 *
          ‖entryDiff n (F x)‖ ^ 2 = hitWeight x F := by
      unfold hitWeight
      congr 1
      split_ifs <;> simp_all
    calc _ = hitWeight x F * ‖∑ e, star (entryDiff n e) *
          z (dbIndex m n (Function.update F x e))‖ ^ 2 := by
          rw [← hind]
          simp only [norm_mul, mul_pow]
          ring
      _ ≤ hitWeight x F * (2 * ∑ e, ‖z (dbIndex m n (Function.update F x e))‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (hw0 F)
      _ = ∑ e, 2 * (hitWeight x F * ‖z (dbIndex m n (Function.update F x e))‖ ^ 2) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun e _ => by ring
  have hnz : nrm z ^ 2 = ∑ G, ‖z (dbIndex m n G)‖ ^ 2 := by
    rw [nrm_sq_eq_sum_norm_sq, ← (dbIndex m n).sum_comp]
  refine hstep.trans ?_
  have key := sum_sum_update_comm x (hitWeight x) (fun G => ‖z (dbIndex m n G)‖ ^ 2)
  simp only at key
  have hre : ∑ F, ∑ e, 2 * (hitWeight x F * ‖z (dbIndex m n (Function.update F x e))‖ ^ 2) =
      ∑ G, 2 * ((∑ e, hitWeight x (Function.update G x e)) * ‖z (dbIndex m n G)‖ ^ 2) := by
    calc ∑ F, ∑ e, 2 * (hitWeight x F * ‖z (dbIndex m n (Function.update F x e))‖ ^ 2)
        = 2 * ∑ F, ∑ e, hitWeight x F * ‖z (dbIndex m n (Function.update F x e))‖ ^ 2 := by
          simp only [Finset.mul_sum]
      _ = 2 * ∑ G, ∑ e, hitWeight x (Function.update G x e) * ‖z (dbIndex m n G)‖ ^ 2 := by
          rw [key]
      _ = _ := by simp only [Finset.mul_sum, Finset.sum_mul]
  rw [hre, hnz, Finset.mul_sum]
  refine Finset.sum_le_sum fun G _ => ?_
  by_cases hG : dbWeight (m := m) (n := n) (dbIndex m n G) ≤ j
  · have h1 := sum_hitWeight_update_le x j G hG
    have h2 : 0 ≤ ‖z (dbIndex m n G)‖ ^ 2 := sq_nonneg _
    calc 2 * ((∑ e, hitWeight x (Function.update G x e)) * ‖z (dbIndex m n G)‖ ^ 2)
        ≤ 2 * ((j / n : ℝ) * ‖z (dbIndex m n G)‖ ^ 2) := by gcongr
      _ = 2 * j / n * ‖z (dbIndex m n G)‖ ^ 2 := by ring
  · rw [hz _ (by omega)]
    simp

/-- After `rDb x`, the projector onto the databases with a collision and none
    off `x` moves at most `√(2 j / n)` of the norm, on vectors supported on
    databases with at most `j` entries. -/
theorem nrm_collProj_offFree_rDb_le [NeZero n] {d : ℕ} (x : Fin m) (j : ℕ)
    (v : Fin (d * (n + 1) ^ m) → ℂ) (hv : SuppLe (m := m) (n := n) j v) :
    nrm (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (collDbProj m n * offFreeDb m n x * rDb m n x)) *ᵥ
      v) ≤ Real.sqrt (2 * j / n) * nrm v := by
  refine nrm_one_kronecker_mulVec_le _ _ (Real.sqrt_nonneg _) v fun a => ?_
  rw [Real.sq_sqrt (by positivity)]
  refine nrm_sq_collDb_rDb_le x j _ fun i hi => ?_
  exact hv _ (by rw [totWeight, Equiv.symm_apply_apply]; exact hi)

end DbOps

section Step

variable {m n w : ℕ} [NeZero n]

variable (m n w) in
/-- The query projector `Π_{x}` on the total register. -/
abbrev projX (x : Fin m) :
    Matrix (Fin (m * n * w * (n + 1) ^ m)) (Fin (m * n * w * (n + 1) ^ m)) ℂ :=
  projS m n w {x} ⊗ₖ (1 : Matrix (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) ℂ)

variable (m n w) in
/-- Decompression of the entry `x` on the total register. -/
abbrev decompX (x : Fin m) :
    Matrix (Fin (m * n * w * (n + 1) ^ m)) (Fin (m * n * w * (n + 1) ^ m)) ℂ :=
  (1 : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) ⊗ₖ decompAt m n x

theorem stdDbU_comm_one_kronecker_diagonal (g : Fin ((n + 1) ^ m) → ℂ) :
    (stdDbU m n w : Matrix _ _ ℂ) *
        ((1 : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) ⊗ₖ Matrix.diagonal g) =
      ((1 : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) ⊗ₖ Matrix.diagonal g) *
        (stdDbU m n w : Matrix _ _ ℂ) := by
  rw [stdDbU, tableOracleU, blockU_val, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [kronecker_mul_kronecker, kronecker_mul_kronecker, Matrix.mul_one, Matrix.one_mul]
  congr 1
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : k = a ∧ k = b
  · obtain ⟨rfl, rfl⟩ := h
    ring
  · simp [h]

theorem stdDbU_comm_projX (x : Fin m) :
    (stdDbU m n w : Matrix _ _ ℂ) * projX m n w x =
      projX m n w x * (stdDbU m n w : Matrix _ _ ℂ) := by
  rw [stdDbU, tableOracleU, blockU_val, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [kronecker_mul_kronecker, kronecker_mul_kronecker, Matrix.mul_one, Matrix.one_mul,
    projS_mul_oracleU_comm]

omit [NeZero n] in
theorem ctrlDecomp_mul_projX (x : Fin m) :
    ctrlDecomp m n w * projX m n w x = projS m n w {x} ⊗ₖ decompAt m n x := by
  rw [ctrlDecomp, ctrlDb, Finset.sum_mul, Finset.sum_eq_single x]
  · rw [kronecker_mul_kronecker, projS_mul_self, Matrix.mul_one]
  · intro x' _ hx'
    rw [kronecker_mul_kronecker, projS_singleton_mul]
    ext a b
    simp [hx', TensorProduct.kronecker_apply]
  · simp

omit [NeZero n] in
theorem projX_mul_ctrlDecomp (x : Fin m) :
    projX m n w x * ctrlDecomp m n w = projS m n w {x} ⊗ₖ decompAt m n x := by
  rw [ctrlDecomp, ctrlDb, Finset.mul_sum, Finset.sum_eq_single x]
  · rw [kronecker_mul_kronecker, projS_mul_self, Matrix.one_mul]
  · intro x' _ hx'
    rw [kronecker_mul_kronecker, projS_singleton_mul]
    ext a b
    simp [Ne.symm hx', TensorProduct.kronecker_apply]
  · simp

omit [NeZero n] in
theorem projX_mul_decompX (x : Fin m) :
    projX m n w x * decompX m n w x = projS m n w {x} ⊗ₖ decompAt m n x := by
  rw [kronecker_mul_kronecker, Matrix.mul_one, Matrix.one_mul]

theorem cmpLocal_mul_projX (x : Fin m) :
    cmpLocal m n w * projX m n w x =
      projX m n w x * (decompX m n w x * (stdDbU m n w : Matrix _ _ ℂ) * decompX m n w x) := by
  rw [cmpLocal, Matrix.mul_assoc, ctrlDecomp_mul_projX, ← projX_mul_decompX,
    ← Matrix.mul_assoc, Matrix.mul_assoc (ctrlDecomp m n w), stdDbU_comm_projX,
    ← Matrix.mul_assoc (ctrlDecomp m n w), ctrlDecomp_mul_projX, ← projX_mul_decompX]
  simp only [Matrix.mul_assoc]

theorem projX_mul_cmpLocal (x : Fin m) :
    projX m n w x * cmpLocal m n w =
      projX m n w x * (decompX m n w x * (stdDbU m n w : Matrix _ _ ℂ) * decompX m n w x) := by
  have hC : projX m n w x * ctrlDecomp m n w = ctrlDecomp m n w * projX m n w x := by
    rw [projX_mul_ctrlDecomp, ctrlDecomp_mul_projX]
  rw [← cmpLocal_mul_projX, cmpLocal, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hC,
    Matrix.mul_assoc (ctrlDecomp m n w), ← stdDbU_comm_projX, ← Matrix.mul_assoc,
    Matrix.mul_assoc _ (projX m n w x), hC]
  simp only [Matrix.mul_assoc]

omit [NeZero n] in
theorem sum_nrm_sq_projX (y : Fin (m * n * w * (n + 1) ^ m) → ℂ) :
    ∑ x, nrm (projX m n w x *ᵥ y) ^ 2 = nrm y ^ 2 := by
  have hsq : ∀ v : Fin (m * n * w * (n + 1) ^ m) → ℂ, nrm v ^ 2 = ∑ i, ‖v i‖ ^ 2 := fun v => by
    unfold nrm
    rw [EuclideanSpace.norm_sq_eq]
  have hX : ∀ x K, (projX m n w x *ᵥ y) K =
      indS m {x} (xPart m n w ((finProdEquiv _ _).symm K).1) * y K := by
    intro x K
    rw [projX, projS_eq_diagonal, Matrix.mulVec, dotProduct, Finset.sum_eq_single K]
    · rw [TensorProduct.kronecker_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq, mul_one]
    · intro L _ hL
      rw [TensorProduct.kronecker_apply]
      by_cases h1 : ((finProdEquiv (m * n * w) ((n + 1) ^ m)).symm K).1 =
          ((finProdEquiv (m * n * w) ((n + 1) ^ m)).symm L).1
      · have h2 : ((finProdEquiv (m * n * w) ((n + 1) ^ m)).symm K).2 ≠
            ((finProdEquiv (m * n * w) ((n + 1) ^ m)).symm L).2 := fun h2 =>
          Ne.symm hL ((finProdEquiv (m * n * w) ((n + 1) ^ m)).symm.injective (Prod.ext h1 h2))
        rw [Matrix.one_apply_ne h2, mul_zero, zero_mul]
      · rw [Matrix.diagonal_apply_ne _ h1, zero_mul, zero_mul]
    · simp
  rw [hsq]
  simp only [hsq, hX, norm_mul, mul_pow]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [← Finset.sum_mul, Finset.sum_eq_single (xPart m n w ((finProdEquiv _ _).symm K).1)]
  · simp [indS]
  · intro x _ hx
    simp [indS, Ne.symm hx]
  · simp

theorem decompAt_mul_self (x : Fin m) : decompAt m n x * decompAt m n x = 1 := by
  rw [decompAt, dbOp_mul, ← dbOp_one (m := m) (n := n)]
  congr 1
  funext y
  by_cases h : y = x
  · subst h
    rw [Function.update_self, decompEntry_mul_self]
    rfl
  · rw [Function.update_of_ne h, Pi.one_apply, Matrix.one_mul]

theorem decompX_mem_unitaryGroup (x : Fin m) :
    decompX m n w x ∈ Matrix.unitaryGroup _ ℂ := by
  have hH : (decompAt m n x)ᴴ = decompAt m n x := by
    rw [decompAt, dbOp_conjTranspose]
    congr 1
    funext y
    by_cases h : y = x
    · subst h; rw [Function.update_self, decompEntry_conjTranspose]
    · rw [Function.update_of_ne h, Pi.one_apply, conjTranspose_one]
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, decompX, conjTranspose_kronecker,
    conjTranspose_one, hH, kronecker_mul_kronecker, Matrix.one_mul, decompAt_mul_self,
    kronecker_one_one]

/-- The amplitude moved into the collision subspace by decompress, standard
    oracle, compress on the entry `x`. -/
theorem nrm_collProj_decompX_le (x : Fin m) (j : ℕ) (z : Fin (m * n * w * (n + 1) ^ m) → ℂ)
    (hz : SuppLe (m := m) (n := n) j z) :
    nrm (collProj m n (m * n * w) *ᵥ ((decompX m n w x * (stdDbU m n w : Matrix _ _ ℂ) *
      decompX m n w x) *ᵥ ((1 - collProj m n (m * n * w)) *ᵥ z))) ≤
      2 * Real.sqrt (2 * (j + 1) / n) * nrm z := by
  set P := collProj m n (m * n * w) with hP
  set S := ((stdDbU m n w : Matrix.unitaryGroup _ ℂ) :
    Matrix (Fin (m * n * w * (n + 1) ^ m)) (Fin (m * n * w * (n + 1) ^ m)) ℂ) with hS
  set D := decompX m n w x with hD
  set R := (1 : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) ⊗ₖ rDb m n x with hR
  set E := (1 : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) ⊗ₖ offFreeDb m n x with hE
  set T := (1 : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) ⊗ₖ
    (collDbProj m n * offFreeDb m n x * rDb m n x) with hT
  have hsub : ∀ A B : Matrix (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) ℂ,
      (1 : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) ⊗ₖ (A - B) =
        (1 : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) ⊗ₖ A - 1 ⊗ₖ B := fun A B => by
    ext a b
    simp only [TensorProduct.kronecker_apply, Matrix.sub_apply, mul_sub]
  have hDR : D = 1 - R := by
    rw [hD, decompX, decompAt_eq_one_sub, hsub, kronecker_one_one]
  have hoc : ∀ k, offColl (m := m) (n := n) x k → dbColl (m := m) (n := n) k :=
    fun k ⟨y, y', _, _, hyy, h1, h2⟩ => ⟨y, y', hyy, h1, h2⟩
  have hPS : P * S = S * P := (stdDbU_comm_one_kronecker_diagonal _).symm
  have hES : E * S = S * E := (stdDbU_comm_one_kronecker_diagonal _).symm
  have hER : E * R = R * E := by
    rw [hE, hR, kronecker_mul_kronecker, kronecker_mul_kronecker, offFreeDb, rDb,
      diagonal_mul_dbOp_update_comm]
    intro i j hij
    have hiff : offColl (m := m) (n := n) x i ↔ offColl (m := m) (n := n) x j := by
      constructor
      · rintro ⟨y, y', hy, hy', hyy, h1, h2⟩
        exact ⟨y, y', hy, hy', hyy, by rwa [← hij y hy], by rw [← hij y hy, ← hij y' hy']; exact h2⟩
      · rintro ⟨y, y', hy, hy', hyy, h1, h2⟩
        exact ⟨y, y', hy, hy', hyy, by rwa [hij y hy], by rw [hij y hy, hij y' hy']; exact h2⟩
    by_cases hi : offColl (m := m) (n := n) x i
    · simp [hi, hiff.mp hi]
    · have hj : ¬ offColl (m := m) (n := n) x j := fun h => hi (hiff.mpr h)
      simp [hi, hj]
  have hED : E * D = D * E := by
    rw [hDR, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hER]
  have hTe : T = P * E * R := by
    rw [hT, hP, hE, hR, collProj, kronecker_mul_kronecker, kronecker_mul_kronecker,
      Matrix.one_mul, Matrix.one_mul]
  have hPE : P * E = E * P := by
    rw [hP, hE, collProj, kronecker_mul_kronecker, kronecker_mul_kronecker, Matrix.one_mul,
      collDbProj, offFreeDb, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 2
    funext k
    ring
  have hdb : offFreeDb m n x * (1 - collDbProj m n) = 1 - collDbProj m n := by
    rw [offFreeDb, collDbProj, ← Matrix.diagonal_one, Matrix.diagonal_sub,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    by_cases h : dbColl (m := m) (n := n) k
    · simp [h]
    · have hk : ¬ offColl (m := m) (n := n) x k := fun hk => h (hoc k hk)
      simp [h, hk]
  have hXk : 1 - P = (1 : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) ⊗ₖ
      (1 - collDbProj m n) := by
    rw [hsub, kronecker_one_one, hP, collProj]
  have hEX : E * (1 - P) = 1 - P := by
    rw [hXk, hE, kronecker_mul_kronecker, Matrix.one_mul, hdb]
  have hPX : P * (1 - P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hP, collProj_mul_self, sub_self]
  have hexp : D * S * D = S - S * R - R * S * D := by
    rw [hDR]
    noncomm_ring
  have h1 : P * (R * S * D) * (1 - P) = T * S * D * (1 - P) := by
    rw [hTe]
    conv_lhs => rw [← hEX]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc D E, ← hED, Matrix.mul_assoc E D, ← Matrix.mul_assoc S E, ← hES,
      Matrix.mul_assoc E S, ← Matrix.mul_assoc R E, ← hER, Matrix.mul_assoc E R]
  have h2 : P * (S * R) * (1 - P) = S * T * (1 - P) := by
    rw [hTe]
    conv_lhs => rw [← hEX]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P S, hPS, Matrix.mul_assoc S P, ← Matrix.mul_assoc R E, ← hER,
      Matrix.mul_assoc E R]
  have h3 : P * S * (1 - P) = 0 := by
    rw [hPS, Matrix.mul_assoc, hPX, Matrix.mul_zero]
  have hid : P * (D * S * D) * (1 - P) = -(T * S * D * (1 - P) + S * T * (1 - P)) := by
    rw [hexp, Matrix.mul_sub P (S - S * R) (R * S * D), Matrix.mul_sub P S (S * R),
      Matrix.sub_mul, Matrix.sub_mul, h1, h2, h3]
    abel
  have hneg : ∀ v : Fin (m * n * w * (n + 1) ^ m) → ℂ, nrm (-v) = nrm v := fun v => by
    unfold nrm
    rw [WithLp.toLp_neg, norm_neg]
  have hXI : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, hPX, sub_zero]
  have hXH : (1 - P)ᴴ = 1 - P := by
    rw [conjTranspose_sub, conjTranspose_one, hP, collProj_conjTranspose]
  have hz' : SuppLe (m := m) (n := n) j ((1 - P) *ᵥ z) := by
    have hw : WeightBound (m := m) (n := n) (1 - P) 0 :=
      weightBound_of_apply_ne_zero_eq fun K L h => by
        by_contra hKL
        rw [Matrix.sub_apply, Matrix.one_apply_ne hKL, hP, collProj_apply, ite_eq_right hKL,
          sub_zero] at h
        exact h rfl
    simpa using suppLe_mulVec_of_weightBound hw hz
  have hnz : nrm ((1 - P) *ᵥ z) ≤ nrm z := nrm_proj_mulVec_le hXI hXH z
  have hSw : WeightBound (m := m) (n := n) S 0 := by
    rw [hS, stdDbU, tableOracleU, blockU_val]
    refine WeightBound.sum fun k => weightBound_kronecker _ _ 0 fun a b hab => ?_
    rw [Matrix.single_apply] at hab
    have : k = a ∧ k = b := by by_contra hc; exact hab (ite_eq_right hc)
    rw [← this.1, ← this.2]
    omega
  have hDw : WeightBound (m := m) (n := n) D 1 :=
    weightBound_kronecker _ _ 1 fun a b hab => dbWeight_le_of_dbOp_update x _ a b hab
  have hSD : SuppLe (m := m) (n := n) (j + 1) (S *ᵥ (D *ᵥ ((1 - P) *ᵥ z))) := by
    simpa using suppLe_mulVec_of_weightBound hSw (suppLe_mulVec_of_weightBound hDw hz')
  have hnSD : nrm (S *ᵥ (D *ᵥ ((1 - P) *ᵥ z))) = nrm ((1 - P) *ᵥ z) := by
    rw [nrm_mulVec_of_mem_unitaryGroup (stdDbU m n w).prop,
      nrm_mulVec_of_mem_unitaryGroup (decompX_mem_unitaryGroup x)]
  have hb1 := nrm_collProj_offFree_rDb_le (d := m * n * w) x (j + 1) _ hSD
  have hb2 := nrm_collProj_offFree_rDb_le (d := m * n * w) x j _ hz'
  have hsq : Real.sqrt (2 * (j : ℕ) / n) ≤ Real.sqrt (2 * (j + 1) / n) := by
    gcongr
    linarith
  have hsq' : Real.sqrt (2 * ((j + 1 : ℕ) : ℝ) / n) = Real.sqrt (2 * (j + 1) / n) := by
    push_cast; rfl
  rw [hsq', hnSD] at hb1
  have hlhs : P *ᵥ ((D * S * D) *ᵥ ((1 - P) *ᵥ z)) = (P * (D * S * D) * (1 - P)) *ᵥ z := by
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc P (D * S * D)]
  rw [hlhs, hid, neg_mulVec, hneg, add_mulVec]
  refine (nrm_add_le _ _).trans ?_
  have e1 : (T * S * D * (1 - P)) *ᵥ z = T *ᵥ (S *ᵥ (D *ᵥ ((1 - P) *ᵥ z))) := by
    simp only [mulVec_mulVec, Matrix.mul_assoc]
  have e2 : nrm ((S * T * (1 - P)) *ᵥ z) = nrm (T *ᵥ ((1 - P) *ᵥ z)) := by
    rw [Matrix.mul_assoc, ← mulVec_mulVec, nrm_mulVec_of_mem_unitaryGroup (stdDbU m n w).prop,
      mulVec_mulVec]
  rw [e1, e2]
  have hs0 : 0 ≤ Real.sqrt (2 * (j + 1) / n) := Real.sqrt_nonneg _
  nlinarith [nrm_nonneg ((1 - P) *ᵥ z), nrm_nonneg z, Real.sqrt_nonneg (2 * (j : ℕ) / n)]

/-- One call of the per-query compressed oracle moves at most
    `2 √(2 (j + 1) / n) ‖y‖` into the collision subspace from a vector supported
    on databases with at most `j` entries. -/
theorem nrm_collProj_cmpLocal_le (j : ℕ) (y : Fin (m * n * w * (n + 1) ^ m) → ℂ)
    (hy : SuppLe (m := m) (n := n) j y) :
    nrm (collProj m n (m * n * w) *ᵥ (cmpLocal m n w *ᵥ
      ((1 - collProj m n (m * n * w)) *ᵥ y))) ≤
      2 * Real.sqrt (2 * (j + 1) / n) * nrm y := by
  set P := collProj m n (m * n * w) with hP
  set ε := 2 * Real.sqrt (2 * (j + 1) / n) with hε
  set M := P * cmpLocal m n w * (1 - P) with hM
  have hε0 : 0 ≤ ε := by positivity
  have hPX : ∀ x, P * projX m n w x = projX m n w x * P := fun x => by
    rw [hP, collProj, kronecker_mul_kronecker, kronecker_mul_kronecker, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
  have hXI : ∀ x, projX m n w x * projX m n w x = projX m n w x := fun x => by
    rw [kronecker_mul_kronecker, projS_mul_self, Matrix.one_mul]
  have hXH : ∀ x, (projX m n w x)ᴴ = projX m n w x := fun x => by
    rw [conjTranspose_kronecker, projS_conjTranspose, conjTranspose_one]
  have h1P : ∀ x, (1 - P) * projX m n w x = projX m n w x * (1 - P) := fun x => by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPX]
  set K := fun x => P * (decompX m n w x * (stdDbU m n w : Matrix _ _ ℂ) * decompX m n w x) *
    (1 - P) with hK
  have hMX : ∀ x, M * projX m n w x = projX m n w x * K x := fun x => by
    rw [hM, hK]
    simp only [Matrix.mul_assoc]
    rw [h1P, ← Matrix.mul_assoc (cmpLocal m n w), cmpLocal_mul_projX, Matrix.mul_assoc,
      ← Matrix.mul_assoc P, hPX]
    simp only [Matrix.mul_assoc]
  have hXM : ∀ x, projX m n w x * M = projX m n w x * K x := fun x => by
    rw [hM, hK]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (projX m n w x) P, ← hPX, Matrix.mul_assoc,
      ← Matrix.mul_assoc (projX m n w x) (cmpLocal m n w), projX_mul_cmpLocal]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P, hPX]
    simp only [Matrix.mul_assoc]
  have hstep : ∀ x, nrm (projX m n w x *ᵥ (M *ᵥ y)) ≤ ε * nrm (projX m n w x *ᵥ y) := by
    intro x
    have hXy : SuppLe (m := m) (n := n) j (projX m n w x *ᵥ y) := by
      simpa using suppLe_mulVec_of_weightBound (weightBound_kronecker_one _) hy
    have hMu : projX m n w x *ᵥ (M *ᵥ y) = projX m n w x *ᵥ (K x *ᵥ (projX m n w x *ᵥ y)) := by
      rw [mulVec_mulVec, hXM, mulVec_mulVec, mulVec_mulVec, ← hMX, Matrix.mul_assoc M, hXI]
    rw [hMu]
    refine (nrm_proj_mulVec_le (hXI x) (hXH x) _).trans ?_
    have := nrm_collProj_decompX_le x j _ hXy
    simpa only [hK, mulVec_mulVec, Matrix.mul_assoc] using this
  have hsq : nrm (M *ᵥ y) ^ 2 ≤ (ε * nrm y) ^ 2 := by
    rw [← sum_nrm_sq_projX (w := w) (M *ᵥ y), mul_pow, ← sum_nrm_sq_projX (w := w) y,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (nrm_nonneg _) (hstep x) 2
  have hfin : nrm (M *ᵥ y) ≤ ε * nrm y :=
    (pow_le_pow_iff_left₀ (nrm_nonneg _) (mul_nonneg hε0 (nrm_nonneg _)) two_ne_zero).mp hsq
  simpa only [hM, mulVec_mulVec, Matrix.mul_assoc] using hfin

end Step

/-! ## The collision bound -/

section Bound

variable {m n w q : ℕ} [NeZero n]

/-- The probability that measuring the database register after the `q`-query
    run of `A` against the per-query compressed oracle, from the empty
    database, finds a collision. -/
def prDbColl (A : QAdv m n w q) : ℝ :=
  (collProj m n (m * n * w) * (oracleChain (unitaryChannel (cmpLocalU m n w)) q
    (fun i => tableLiftU ((n + 1) ^ m) (A.U i))).branch () (initCmp A).val).trace.re

/-- Zhandry's collision bound: after `q` queries to the compressed oracle of a
    random function into `Fin n`, the database holds a collision with
    probability at most `8 q³ / n`. -/
theorem prDbColl_le (A : QAdv m n w q) : prDbColl A ≤ 8 * (q : ℝ) ^ 3 / n := by
  obtain ⟨ψ, hψ⟩ := exists_eq_sum_vecMulVec_of_posSemidef (initCmp A).psd
  set C := chainOp (cmpLocalU m n w : Matrix _ _ ℂ) q
    (fun i => tableLiftU ((n + 1) ^ m) (A.U i)) with hC
  set P := collProj m n (m * n * w) with hP
  set Q0 := projLe m n (m * n * w) 0 with hQ0
  set a : ℝ := 2 * q * Real.sqrt (2 * q / n) with ha
  have hQH : Q0ᴴ = Q0 := by
    rw [hQ0]
    ext K L
    rw [conjTranspose_apply, projLe_apply, projLe_apply]
    by_cases h : K = L
    · subst h; split_ifs <;> simp
    · simp [h, Ne.symm h]
  have hQI : Q0 * Q0 = Q0 := by
    rw [hQ0, projLe, kronecker_mul_kronecker, Matrix.one_mul, dbProjLe,
      Matrix.diagonal_mul_diagonal]
    congr 2
    funext k
    split_ifs <;> simp
  have hQρ : Q0 * (initCmp A).val = (initCmp A).val := by
    have h1 : WeightBound (m := m) (n := n)
        (1 : Matrix (Fin (m * n * w * (n + 1) ^ m)) (Fin (m * n * w * (n + 1) ^ m)) ℂ) 0 :=
      weightBound_of_apply_ne_zero_eq fun K L h => by
        by_contra hc
        exact h (Matrix.one_apply_ne hc)
    simpa using projLe_mul_of_weightBound h1 (initCmp_apply_ne_zero A)
  have hρH : ((initCmp A).val)ᴴ = (initCmp A).val := (initCmp A).psd.isHermitian
  have hρQ : (initCmp A).val * Q0 = (initCmp A).val := by
    have := congrArg conjTranspose hQρ
    rwa [conjTranspose_mul, hρH, hQH] at this
  have htr : (P * (C * (initCmp A).val * Cᴴ)).trace =
      ((P * C * Q0) * (initCmp A).val * (P * C * Q0)ᴴ).trace := by
    rw [conjTranspose_mul, conjTranspose_mul, hQH, hP, collProj_conjTranspose, ← hP]
    calc (P * (C * (initCmp A).val * Cᴴ)).trace
        = ((P * P) * (C * (initCmp A).val * Cᴴ)).trace := by rw [hP, collProj_mul_self]
      _ = (P * (C * (initCmp A).val * Cᴴ) * P).trace := by
        rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
      _ = _ := by
        conv_lhs => rw [← hρQ, ← hQρ]
        simp only [Matrix.mul_assoc]
  have hnorm : ∑ k, nrm (ψ k) ^ 2 = 1 := by
    have h := (initCmp A).tr_one
    have htr1 : (∑ k, vecMulVec (ψ k) (star (ψ k))).trace = ((∑ k, nrm (ψ k) ^ 2 : ℝ) : ℂ) := by
      rw [trace_sum, Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [trace_vecMulVec, dotProduct_star_self]
    rw [hψ, htr1] at h
    exact_mod_cast h
  have ha0 : 0 ≤ a := by positivity
  have hsum : ∑ i ∈ Finset.range q, 2 * Real.sqrt (2 * ((0 + i : ℕ) + 1 : ℝ) / n) ≤ a := by
    have := Finset.sum_le_card_nsmul (Finset.range q)
      (fun i => 2 * Real.sqrt (2 * ((0 + i : ℕ) + 1 : ℝ) / n)) (2 * Real.sqrt (2 * q / n))
      (fun i hi => by
        have hiq : ((0 + i : ℕ) + 1 : ℝ) ≤ q := by
          have := Finset.mem_range.mp hi
          rw [zero_add]
          exact_mod_cast this
        gcongr)
    rw [Finset.card_range, nsmul_eq_mul] at this
    rw [ha]
    linarith
  have hbound : ∀ v, nrm ((P * C * Q0) *ᵥ v) ≤ a * nrm v := by
    intro v
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    have hs : SuppLe (m := m) (n := n) 0 (Q0 *ᵥ v) := by
      intro K hK
      rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun L _ => ?_
      rw [hQ0, projLe_apply]
      by_cases hKL : K = L
      · simp [hKL, show ¬ totWeight (m := m) (n := n) L ≤ 0 by rw [← hKL]; omega]
      · simp [hKL]
    have h := nrm_proj_chainOp_le (m := m) (n := n) P (cmpLocalU m n w : Matrix _ _ ℂ)
      (by rw [hP]; exact collProj_mul_self) (by rw [hP]; exact collProj_conjTranspose)
      (cmpLocalU m n w).prop (by exact cmpLocal_weightBound)
      (fun j => 2 * Real.sqrt (2 * ((j : ℕ) + 1 : ℝ) / n))
      (fun j y hy => by exact nrm_collProj_cmpLocal_le j y hy) q
      (fun i => tableLiftU ((n + 1) ^ m) (A.U i)) (fun _ => weightBound_kronecker_one _)
      (fun _ => by
        rw [tableLiftU_val, hP, collProj, kronecker_mul_kronecker, kronecker_mul_kronecker,
          Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one])
      0 _ hs
    rw [hP, collProj_mulVec_eq_zero_of_suppLe hs, nrm_zero, zero_add, ← hP] at h
    refine h.trans ?_
    exact mul_le_mul hsum (nrm_proj_mulVec_le hQI hQH v) (nrm_nonneg _) ha0
  unfold prDbColl
  rw [oracleChain_unitaryChannel_branch, ← hC, ← hP, htr, hψ,
    trace_mul_sum_vecMulVec_mul_conjTranspose, Complex.ofReal_re]
  calc ∑ k, nrm ((P * C * Q0) *ᵥ ψ k) ^ 2 ≤ ∑ k, (a * nrm (ψ k)) ^ 2 :=
        Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (nrm_nonneg _) (hbound _) 2
    _ = a ^ 2 * ∑ k, nrm (ψ k) ^ 2 := by rw [Finset.mul_sum]; simp only [mul_pow]
    _ = 8 * (q : ℝ) ^ 3 / n := by
        rw [hnorm, mul_one, ha, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
        ring

end Bound

end CatCrypt.Quantum.QROM
