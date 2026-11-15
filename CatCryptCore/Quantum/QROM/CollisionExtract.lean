/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.CollisionBound

/-!
# Collision finding against a random oracle

A `q`-query adversary `A : QAdv m n w q` against a uniformly random function
`H : Fin m → Fin n` whose output is read from the computational basis of its
register by `out : Fin (m * n * w) → Fin m × Fin m` finds a collision when the
output `(x, x')` has `x ≠ x'` and `H x = H x'`. The probability `prColl A out`
of this event is at most `2 prDbColl A + 16 / n ≤ 16 (q³ + 1) / n`.

The proof relates the standard and the compressed oracle at the output points
(Zhandry, ePrint 2018/276, Lemma 5). In the purified standard run the oracle
register holds the decompressed database `φ`, and the compressed run ends in
`D φ` for the decompression `D`. Let `Q` test that the database entries at the
output points are equal and non-`⊥`. Decompression at the entries other than the
output points commutes with `Q`, and decompression `1 - |u⟩⟨u|` at an output
point moves at most `√(2 / n)` of the norm into `Q`, so
`‖Q φ‖ ≤ ‖Q D φ‖ + 2 √(2 / n) ‖φ‖`. The test `Q` on `D φ` implies a collision in
the database, whose probability `prDbColl A ≤ 8 q³ / n` is `prDbColl_le`.

## Main definitions

* `outDbColl p k`, `outDbProj p` — the database `k` holds equal non-`⊥` entries at
  the two distinct points of `p`, and the projector onto these databases
* `outCollProj out` — the same test on the total register, at the output `out a`
  of the first factor `a`
* `collTest out H`, `prCollAt A out H`, `prColl A out` — the collision test for
  the oracle `H`, the probability that the standard run for `H` outputs a
  collision of `H`, and its average over `H`

## Main results

* `nrm_outDbProj_le` — `‖Q z‖ ≤ ‖Q D z‖ + 2 √(2 / n) ‖z‖` on the database register
* `prColl_eq_trace` — `prColl A out` is the probability of `outCollProj out` in the
  purified standard run
* `prColl_le_two_mul_prDbColl_add` — `prColl A out ≤ 2 prDbColl A + 16 / n`
* `prColl_le` — `prColl A out ≤ 16 (q³ + 1) / n`

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

/-! ## The collision test at two points of the database -/

section Db

variable {m n : ℕ}

/-- The database `k` holds equal non-`⊥` entries at the two distinct points of `p`. -/
def outDbColl (p : Fin m × Fin m) (k : Fin ((n + 1) ^ m)) : Prop :=
  p.1 ≠ p.2 ∧ (dbIndex m n).symm k p.1 ≠ Fin.last n ∧
    (dbIndex m n).symm k p.1 = (dbIndex m n).symm k p.2

variable (m n) in
open Classical in
/-- The projector onto the databases holding equal non-`⊥` entries at the two
    distinct points of `p`. -/
def outDbProj (p : Fin m × Fin m) : Matrix (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) ℂ :=
  Matrix.diagonal fun k => if outDbColl (m := m) (n := n) p k then 1 else 0

/-- A database with equal non-`⊥` entries at two distinct points holds a collision. -/
theorem dbColl_of_outDbColl {p : Fin m × Fin m} {k : Fin ((n + 1) ^ m)}
    (h : outDbColl (m := m) (n := n) p k) : dbColl (m := m) (n := n) k :=
  ⟨p.1, p.2, h.1, h.2.1, h.2.2⟩

/-- An entrywise product operator is unitary when every factor is. -/
theorem dbOp_mem_unitaryGroup (F : Fin m → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hF : ∀ y, F y ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ) :
    dbOp m n F ∈ Matrix.unitaryGroup (Fin ((n + 1) ^ m)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, dbOp_conjTranspose, dbOp_mul,
    show (fun y => F y * (F y)ᴴ) = 1 from funext fun y => Matrix.mem_unitaryGroup_iff.mp (hF y),
    dbOp_one]

/-- A diagonal operator whose entries depend only on the entries `x` and `x'`
    commutes with an entrywise product operator that is the identity at `x`
    and `x'`. -/
theorem diagonal_mul_dbOp_comm (x x' : Fin m) (g : Fin ((n + 1) ^ m) → ℂ)
    (hg : ∀ i j, (dbIndex m n).symm i x = (dbIndex m n).symm j x →
      (dbIndex m n).symm i x' = (dbIndex m n).symm j x' → g i = g j)
    (F : Fin m → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hFx : F x = 1) (hFx' : F x' = 1) :
    Matrix.diagonal g * dbOp m n F = dbOp m n F * Matrix.diagonal g := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : dbOp m n F i j = 0
  · rw [h, mul_zero, zero_mul]
  · have hy : ∀ y, F y = 1 → (dbIndex m n).symm i y = (dbIndex m n).symm j y := by
      intro y hy
      by_contra hc
      simp only [dbOp_apply, Finset.prod_eq_zero_iff] at h
      exact h ⟨y, Finset.mem_univ y, by simp [hy, hc]⟩
    rw [hg i j (hy x hFx) (hy x' hFx'), mul_comm]

/-- `a² ≤ c b²` with `a, b ≥ 0` gives `a ≤ √c b`. -/
theorem le_sqrt_mul_of_sq_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ c * b ^ 2) :
    a ≤ Real.sqrt c * b := by
  rw [← Real.sqrt_sq ha, ← Real.sqrt_sq hb, ← Real.sqrt_mul' c (sq_nonneg b)]
  exact Real.sqrt_le_sqrt h

variable [NeZero n]

/-- `rDb x` followed by a diagonal operator `g`: when the weights
    `|g(F[x := e])|² |u(e)|²` sum to at most `c` over `e` for every `F`, the
    squared norm is at most `2 c` times the squared norm of the argument. -/
theorem nrm_sq_diagonal_rDb_le (x : Fin m) (g : Fin ((n + 1) ^ m) → ℂ) (c : ℝ)
    (hg : ∀ F : Fin m → Fin (n + 1),
      ∑ e, ‖g (dbIndex m n (Function.update F x e))‖ ^ 2 * ‖entryDiff n e‖ ^ 2 ≤ c)
    (z : Fin ((n + 1) ^ m) → ℂ) :
    nrm ((Matrix.diagonal g * rDb m n x) *ᵥ z) ^ 2 ≤ 2 * c * nrm z ^ 2 := by
  set wt : (Fin m → Fin (n + 1)) → ℝ :=
    fun F => ‖g (dbIndex m n F)‖ ^ 2 * ‖entryDiff n (F x)‖ ^ 2 with hwt
  have hw0 : ∀ F, 0 ≤ wt F := fun F => by positivity
  have hstep : nrm ((Matrix.diagonal g * rDb m n x) *ᵥ z) ^ 2 ≤
      ∑ F, ∑ e, 2 * (wt F * ‖z (dbIndex m n (Function.update F x e))‖ ^ 2) := by
    rw [nrm_sq_eq_sum_norm_sq, ← (dbIndex m n).sum_comp]
    refine Finset.sum_le_sum fun F _ => ?_
    rw [← mulVec_mulVec, mulVec_diagonal, rDb_mulVec_apply, Equiv.symm_apply_apply]
    have hcs := norm_sum_star_entryDiff_mul_sq_le
      (fun e => z (dbIndex m n (Function.update F x e)))
    calc _ = wt F * ‖∑ e, star (entryDiff n e) *
          z (dbIndex m n (Function.update F x e))‖ ^ 2 := by
          simp only [hwt, norm_mul, mul_pow]
          ring
      _ ≤ wt F * (2 * ∑ e, ‖z (dbIndex m n (Function.update F x e))‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (hw0 F)
      _ = ∑ e, 2 * (wt F * ‖z (dbIndex m n (Function.update F x e))‖ ^ 2) := by
          simp only [Finset.mul_sum, mul_left_comm]
  have hnz : nrm z ^ 2 = ∑ G, ‖z (dbIndex m n G)‖ ^ 2 := by
    rw [nrm_sq_eq_sum_norm_sq, ← (dbIndex m n).sum_comp]
  refine hstep.trans ?_
  have key := sum_sum_update_comm x wt (fun G => ‖z (dbIndex m n G)‖ ^ 2)
  have hre : ∑ F, ∑ e, 2 * (wt F * ‖z (dbIndex m n (Function.update F x e))‖ ^ 2) =
      ∑ G, 2 * ((∑ e, wt (Function.update G x e)) * ‖z (dbIndex m n G)‖ ^ 2) := by
    simpa only [Finset.mul_sum, Finset.sum_mul] using congrArg (HMul.hMul (2 : ℝ)) key
  rw [hre, hnz, Finset.mul_sum]
  refine Finset.sum_le_sum fun G _ => ?_
  have h1 : ∑ e, wt (Function.update G x e) ≤ c := by
    simpa only [hwt, Function.update_self] using hg G
  linarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖z (dbIndex m n G)‖)]

omit [NeZero n] in
open Classical in
/-- At an output point `x` of `p`, the weights of `outDbProj p` sum to at most `1 / n`:
    only the value of the other output point contributes. -/
theorem sum_outDbColl_update_le (p : Fin m × Fin m) (x : Fin m) (hx : x = p.1 ∨ x = p.2)
    (F : Fin m → Fin (n + 1)) :
    ∑ e, ‖(if outDbColl (m := m) (n := n) p (dbIndex m n (Function.update F x e))
      then (1 : ℂ) else 0)‖ ^ 2 * ‖entryDiff n e‖ ^ 2 ≤ 1 / n := by
  classical
  have hkey : ∃ e0, ∀ e, outDbColl (m := m) (n := n) p (dbIndex m n (Function.update F x e)) →
      e ≠ Fin.last n ∧ e = e0 := by
    rcases hx with rfl | rfl
    · exact ⟨F p.2, fun e ⟨hne, _, _⟩ => by simp_all [Function.update_of_ne (Ne.symm hne)]⟩
    · exact ⟨F p.1, fun e ⟨_, _, _⟩ => by simp_all⟩
  obtain ⟨e0, he0⟩ := hkey
  have hle : ∀ e, ‖(if outDbColl (m := m) (n := n) p (dbIndex m n (Function.update F x e))
      then (1 : ℂ) else 0)‖ ^ 2 * ‖entryDiff n e‖ ^ 2 ≤ if e = e0 then (1 / n : ℝ) else 0 := by
    intro e
    by_cases h : outDbColl (m := m) (n := n) p (dbIndex m n (Function.update F x e))
    · obtain ⟨hl, rfl⟩ := he0 e h
      rw [ite_eq_left h, ite_eq_left rfl, norm_one, one_pow, one_mul,
        norm_entryDiff_sq_of_ne _ hl]
    · simp [h, apply_ite]
  exact (Finset.sum_le_sum fun e _ => hle e).trans_eq (by simp)

/-- At an output point `x` of `p`, `rDb x` followed by `outDbProj p` moves at most
    `√(2 / n)` of the norm. -/
theorem nrm_outDbProj_rDb_le (p : Fin m × Fin m) (x : Fin m) (hx : x = p.1 ∨ x = p.2)
    (z : Fin ((n + 1) ^ m) → ℂ) :
    nrm ((outDbProj m n p * rDb m n x) *ᵥ z) ≤ Real.sqrt (2 / n) * nrm z := by
  classical
  refine le_sqrt_mul_of_sq_le (nrm_nonneg _) (nrm_nonneg _) ?_
  have h := nrm_sq_diagonal_rDb_le x
    (fun k => if outDbColl (m := m) (n := n) p k then (1 : ℂ) else 0) (1 / n)
    (sum_outDbColl_update_le p x hx) z
  rwa [outDbProj, ← mul_one_div]

/-- Decompression of the entry `x` is unitary. -/
theorem decompAt_mem_unitaryGroup (x : Fin m) :
    decompAt m n x ∈ Matrix.unitaryGroup (Fin ((n + 1) ^ m)) ℂ := by
  refine dbOp_mem_unitaryGroup _ fun y => ?_
  rcases eq_or_ne y x with rfl | h <;> simp [*, decompEntry_mem_unitaryGroup]

omit [NeZero n] in
/-- Decompression of the database is decompression at `x` and `x'`, followed by
    decompression of the other entries. -/
theorem decompDB_eq_dbOp_mul_decompAt (x x' : Fin m) (hxx' : x ≠ x') :
    decompDB m n = dbOp m n (Function.update (Function.update (fun _ => decompEntry n) x 1) x' 1) *
      (decompAt m n x * decompAt m n x') := by
  rw [decompAt, decompAt, dbOp_mul, dbOp_mul, decompDB_eq_dbOp]
  congr 1
  funext y
  by_cases hy : y = x <;> by_cases hy' : y = x' <;> simp_all

/-- The standard and compressed oracle at two output points (Zhandry, Lemma 5): the
    test `outDbProj p` of the decompressed state `z` exceeds the test of the
    compressed state `decompDB z` by at most `2 √(2 / n) ‖z‖`. -/
theorem nrm_outDbProj_le (p : Fin m × Fin m) (z : Fin ((n + 1) ^ m) → ℂ) :
    nrm (outDbProj m n p *ᵥ z) ≤
      nrm (outDbProj m n p *ᵥ (decompDB m n *ᵥ z)) + 2 * Real.sqrt (2 / n) * nrm z := by
  classical
  obtain ⟨x, x'⟩ := p
  by_cases hp : x = x'
  · have h0 : outDbProj m n (x, x') = 0 := by
      ext i j
      simp [outDbProj, outDbColl, hp, Matrix.diagonal_apply]
    simpa [h0] using mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt (2 / n)) (nrm_nonneg z)
  obtain ⟨R, hRu, hQR, hdec⟩ : ∃ R : Matrix (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) ℂ,
      R ∈ Matrix.unitaryGroup (Fin ((n + 1) ^ m)) ℂ ∧
      outDbProj m n (x, x') * R = R * outDbProj m n (x, x') ∧
      decompDB m n = R * (decompAt m n x * decompAt m n x') := by
    refine ⟨_, dbOp_mem_unitaryGroup _ fun y => ?_,
      diagonal_mul_dbOp_comm x x' _ ?_ _ ?_ ?_, decompDB_eq_dbOp_mul_decompAt x x' hp⟩
    · simp only [Function.update_apply]
      split_ifs <;> simp [one_mem, decompEntry_mem_unitaryGroup]
    · intro i j h1 h2
      simp only [outDbColl, h1, h2]
      congr
    · simp [hp]
    · simp
  have hsplit : z = decompAt m n x *ᵥ (decompAt m n x' *ᵥ z) +
      rDb m n x *ᵥ (decompAt m n x' *ᵥ z) + rDb m n x' *ᵥ z := by
    rw [decompAt_eq_one_sub, decompAt_eq_one_sub]
    simp only [sub_mulVec, one_mulVec]
    abel
  have hmain : nrm (outDbProj m n (x, x') *ᵥ (decompAt m n x *ᵥ (decompAt m n x' *ᵥ z))) =
      nrm (outDbProj m n (x, x') *ᵥ (decompDB m n *ᵥ z)) := by
    rw [hdec, ← mulVec_mulVec, mulVec_mulVec _ (outDbProj m n (x, x')) R, hQR,
      ← mulVec_mulVec, nrm_mulVec_of_mem_unitaryGroup hRu, ← mulVec_mulVec]
  have h1 := nrm_outDbProj_rDb_le (x, x') x (Or.inl rfl) (decompAt m n x' *ᵥ z)
  have h2 := nrm_outDbProj_rDb_le (x, x') x' (Or.inr rfl) z
  rw [nrm_mulVec_of_mem_unitaryGroup (decompAt_mem_unitaryGroup x')] at h1
  have hsum : outDbProj m n (x, x') *ᵥ z =
      outDbProj m n (x, x') *ᵥ (decompAt m n x *ᵥ (decompAt m n x' *ᵥ z)) +
        (outDbProj m n (x, x') * rDb m n x) *ᵥ (decompAt m n x' *ᵥ z) +
        (outDbProj m n (x, x') * rDb m n x') *ᵥ z := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_add, ← mulVec_add, ← hsplit]
  rw [hsum]
  have h3 := nrm_add_le
    (outDbProj m n (x, x') *ᵥ (decompAt m n x *ᵥ (decompAt m n x' *ᵥ z)) +
      (outDbProj m n (x, x') * rDb m n x) *ᵥ (decompAt m n x' *ᵥ z))
    ((outDbProj m n (x, x') * rDb m n x') *ᵥ z)
  have h4 := nrm_add_le
    (outDbProj m n (x, x') *ᵥ (decompAt m n x *ᵥ (decompAt m n x' *ᵥ z)))
    ((outDbProj m n (x, x') * rDb m n x) *ᵥ (decompAt m n x' *ᵥ z))
  rw [hmain] at h4
  linarith

/-- The squared form of `nrm_outDbProj_le`. -/
theorem nrm_sq_outDbProj_le (p : Fin m × Fin m) (z : Fin ((n + 1) ^ m) → ℂ) :
    nrm (outDbProj m n p *ᵥ z) ^ 2 ≤
      2 * nrm (outDbProj m n p *ᵥ (decompDB m n *ᵥ z)) ^ 2 + 16 / n * nrm z ^ 2 := by
  have h := nrm_outDbProj_le p z
  have hs : Real.sqrt (2 / n) ^ 2 = 2 / n := Real.sq_sqrt (by positivity)
  have h0 := nrm_nonneg (outDbProj m n p *ᵥ z)
  have h1 := nrm_nonneg (outDbProj m n p *ᵥ (decompDB m n *ᵥ z))
  have h2 : 0 ≤ Real.sqrt (2 / n) * nrm z := mul_nonneg (Real.sqrt_nonneg _) (nrm_nonneg _)
  have hsq : nrm (outDbProj m n p *ᵥ z) ^ 2 ≤
      (nrm (outDbProj m n p *ᵥ (decompDB m n *ᵥ z)) + 2 * (Real.sqrt (2 / n) * nrm z)) ^ 2 := by
    rw [← mul_assoc]
    exact pow_le_pow_left₀ h0 h 2
  have hk : (Real.sqrt (2 / n) * nrm z) ^ 2 = 2 / n * nrm z ^ 2 := by rw [mul_pow, hs]
  have hab : (nrm (outDbProj m n p *ᵥ (decompDB m n *ᵥ z)) +
      2 * (Real.sqrt (2 / n) * nrm z)) ^ 2 ≤
      2 * nrm (outDbProj m n p *ᵥ (decompDB m n *ᵥ z)) ^ 2 +
        8 * (Real.sqrt (2 / n) * nrm z) ^ 2 := by
    nlinarith [sq_nonneg (nrm (outDbProj m n p *ᵥ (decompDB m n *ᵥ z)) -
      2 * (Real.sqrt (2 / n) * nrm z))]
  rw [hk] at hab
  have h16 : 8 * (2 / (n : ℝ) * nrm z ^ 2) = 16 / n * nrm z ^ 2 := by ring
  linarith

end Db

/-! ## The collision test at the output on the total register -/

section Total

variable {m n d : ℕ}

/-- The total-register index `K = (a, k)` holds equal non-`⊥` database entries at the
    two distinct points of the output `out a`. -/
def outColl (out : Fin d → Fin m × Fin m) (K : Fin (d * (n + 1) ^ m)) : Prop :=
  outDbColl (m := m) (n := n) (out ((finProdEquiv d ((n + 1) ^ m)).symm K).1)
    ((finProdEquiv d ((n + 1) ^ m)).symm K).2

variable (m n) in
open Classical in
/-- The projector onto the total-register indices `(a, k)` whose database `k` holds
    equal non-`⊥` entries at the two distinct points of the output `out a`. -/
def outCollProj (out : Fin d → Fin m × Fin m) :
    Matrix (Fin (d * (n + 1) ^ m)) (Fin (d * (n + 1) ^ m)) ℂ :=
  Matrix.diagonal fun K => if outColl (m := m) (n := n) out K then 1 else 0

/-- The test `outColl` at the index `(a, k)`. -/
theorem outColl_finProdEquiv (out : Fin d → Fin m × Fin m) (a : Fin d) (k : Fin ((n + 1) ^ m)) :
    outColl (m := m) (n := n) out (finProdEquiv d ((n + 1) ^ m) (a, k)) ↔
      outDbColl (m := m) (n := n) (out a) k := by
  simp only [outColl, Equiv.symm_apply_apply]

/-- On the slice `a`, `outCollProj out` is the database test at `out a`. -/
theorem dbSlice_outCollProj_mulVec (out : Fin d → Fin m × Fin m)
    (v : Fin (d * (n + 1) ^ m) → ℂ) (a : Fin d) :
    dbSlice (outCollProj m n out *ᵥ v) a = outDbProj m n (out a) *ᵥ dbSlice v a := by
  classical
  funext i
  simp only [dbSlice, outCollProj, outDbProj, mulVec_diagonal, outColl_finProdEquiv]

/-- The test at the output is part of the collision projector. -/
theorem nrm_sq_outCollProj_le_collProj (out : Fin d → Fin m × Fin m)
    (v : Fin (d * (n + 1) ^ m) → ℂ) :
    nrm (outCollProj m n out *ᵥ v) ^ 2 ≤ nrm (collProj m n d *ᵥ v) ^ 2 := by
  classical
  rw [nrm_sq_eq_sum_dbSlice, nrm_sq_eq_sum_dbSlice (collProj m n d *ᵥ v)]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [dbSlice_outCollProj_mulVec, collProj, one_kronecker_mulVec_dbSlice, nrm_sq_eq_sum_norm_sq,
    nrm_sq_eq_sum_norm_sq]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [outDbProj, collDbProj, mulVec_diagonal, mulVec_diagonal]
  by_cases h : outDbColl (m := m) (n := n) (out a) k
  · simp [h, dbColl_of_outDbColl h]
  · simp [h]

/-- The standard and compressed oracle at the output on the total register, squared:
    `‖Π φ‖² ≤ 2 ‖Π D φ‖² + (16 / n) ‖φ‖²` for the decompression `D` of the database. -/
theorem nrm_sq_outCollProj_le [NeZero n] (out : Fin d → Fin m × Fin m)
    (φ : Fin (d * (n + 1) ^ m) → ℂ) :
    nrm (outCollProj m n out *ᵥ φ) ^ 2 ≤
      2 * nrm (outCollProj m n out *ᵥ
        (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ decompDB m n) *ᵥ φ)) ^ 2 + 16 / n * nrm φ ^ 2 := by
  rw [nrm_sq_eq_sum_dbSlice (outCollProj m n out *ᵥ φ),
    nrm_sq_eq_sum_dbSlice (outCollProj m n out *ᵥ _), nrm_sq_eq_sum_dbSlice φ, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [dbSlice_outCollProj_mulVec, dbSlice_outCollProj_mulVec, one_kronecker_mulVec_dbSlice]
  exact nrm_sq_outDbProj_le _ _

/-- A diagonal matrix on `Fin (d * t)` as a block sum over the second factor. -/
theorem diagonal_eq_sum_kronecker_single {t : ℕ} (g : Fin (d * t) → ℂ) :
    Matrix.diagonal g = ∑ k : Fin t,
      Matrix.diagonal (fun a => g (finProdEquiv d t (a, k))) ⊗ₖ Matrix.single k k (1 : ℂ) := by
  ext K L
  obtain ⟨⟨a, i⟩, rfl⟩ := (finProdEquiv d t).surjective K
  obtain ⟨⟨b, j⟩, rfl⟩ := (finProdEquiv d t).surjective L
  rw [Matrix.sum_apply]
  simp only [kronecker_apply, Equiv.symm_apply_apply, Matrix.diagonal_apply,
    Matrix.single_apply, (finProdEquiv d t).injective.eq_iff, Prod.mk.injEq]
  by_cases hab : a = b <;> by_cases hij : i = j <;> simp [hab, hij, ite_and]

/-- Against a block-diagonal oracle, a block-diagonal test `∑ₖ P k ⊗ |k⟩⟨k|` after the
    chain on `ρ ⊗ σ` has trace `∑ₖ σ k k` times the trace for the oracle `V k` and the
    test `P k`. -/
theorem trace_sum_kronecker_single_chainOp_blockU {t q : ℕ} (P : Fin t → Matrix (Fin d) (Fin d) ℂ)
    (V : Fin t → Matrix.unitaryGroup (Fin d) ℂ) (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (σ : Matrix (Fin t) (Fin t) ℂ) :
    (((∑ k, P k ⊗ₖ Matrix.single k k (1 : ℂ)) *
        chainOp (blockU V : Matrix _ _ ℂ) q (fun i => tableLiftU t (U i))) * (ρ ⊗ₖ σ) *
      ((∑ k, P k ⊗ₖ Matrix.single k k (1 : ℂ)) *
        chainOp (blockU V : Matrix _ _ ℂ) q (fun i => tableLiftU t (U i)))ᴴ).trace =
      ∑ k, σ k k * ((P k * chainOp (V k : Matrix _ _ ℂ) q U) * ρ *
        (P k * chainOp (V k : Matrix _ _ ℂ) q U)ᴴ).trace := by
  rw [chainOp_blockU, sum_kronecker_single_mul, conjTranspose_sum_kronecker_single,
    Finset.sum_mul, Finset.sum_mul, trace_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, trace_sum, Finset.sum_eq_single k] <;>
    simp +contextual [kronecker_mul_kronecker, TensorProduct.trace_kronecker, mul_comm, eq_comm]

end Total

/-! ## The collision probability against a random oracle -/

section Coll

variable {m n w q d : ℕ}

open Classical in
/-- The collision test for the oracle `H`: the output `out a` of the basis state `a`
    is a pair `(x, x')` with `x ≠ x'` and `H x = H x'`. -/
def collTest (out : Fin d → Fin m × Fin m) (H : Fin m → Fin n) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun a => if (out a).1 ≠ (out a).2 ∧ H (out a).1 = H (out a).2 then 1 else 0

variable [NeZero n]

/-- The probability that the standard run of `A` for the oracle `H`, measured in the
    computational basis and read by `out`, outputs a collision of `H`. -/
def prCollAt (A : QAdv m n w q) (out : Fin (m * n * w) → Fin m × Fin m)
    (H : Fin m → Fin n) : ℝ :=
  ((collTest out H * runOp A H) * A.init.val * (collTest out H * runOp A H)ᴴ).trace.re

/-- The probability that `A` outputs a collision of a uniformly random oracle. -/
def prColl (A : QAdv m n w q) (out : Fin (m * n * w) → Fin m × Fin m) : ℝ :=
  ((n : ℝ) ^ m)⁻¹ * ∑ H : Fin m → Fin n, prCollAt A out H

omit [NeZero n] in
/-- At a database without `⊥` entries, the test at two points is the collision test of
    the function it holds. -/
theorem outDbColl_castSucc_iff (p : Fin m × Fin m) (H : Fin m → Fin n) :
    outDbColl (m := m) (n := n) p (dbIndex m n fun x => (H x).castSucc) ↔
      p.1 ≠ p.2 ∧ H p.1 = H p.2 := by
  simp [outDbColl, Fin.castSucc_ne_last]

omit [NeZero n] in
open Classical in
/-- At a database without `⊥` entries, the block of `outCollProj out` is the
    collision test of the function the database holds. -/
theorem diagonal_outColl_castSucc_eq_collTest (out : Fin d → Fin m × Fin m)
    (H : Fin m → Fin n) :
    (Matrix.diagonal fun a => if outColl (m := m) (n := n) out
      (finProdEquiv d ((n + 1) ^ m) (a, dbIndex m n fun x => (H x).castSucc)) then (1 : ℂ)
        else 0) = collTest out H := by
  simp only [collTest, outColl_finProdEquiv, outDbColl_castSucc_iff]

/-- The collision probability is the probability of `outCollProj out` after the
    standard oracle on the database register, started from the decompressed empty
    database. -/
theorem prColl_eq_trace (A : QAdv m n w q) (out : Fin (m * n * w) → Fin m × Fin m) :
    prColl A out =
      ((outCollProj m n out *
          chainOp (stdDbU m n w : Matrix _ _ ℂ) q (fun i => tableLiftU ((n + 1) ^ m) (A.U i))) *
        (A.init.val ⊗ₖ (conjDM (decompDBU m n) (dbEmpty m n)).val) *
        (outCollProj m n out *
          chainOp (stdDbU m n w : Matrix _ _ ℂ) q
            (fun i => tableLiftU ((n + 1) ^ m) (A.U i)))ᴴ).trace.re := by
  rw [outCollProj, diagonal_eq_sum_kronecker_single, stdDbU, tableOracleU,
    trace_sum_kronecker_single_chainOp_blockU, Complex.re_sum]
  have hre : ∀ k (T : ℂ), ((conjDM (decompDBU m n) (dbEmpty m n)).val k k * T).re =
      ((conjDM (decompDBU m n) (dbEmpty m n)).val k k).re * T.re := by
    intro k T
    rw [Complex.mul_re, ← (Complex.nonneg_iff.mp
      ((conjDM (decompDBU m n) (dbEmpty m n)).psd.diag_nonneg (i := k))).2, zero_mul, sub_zero]
  simp only [hre, conjDM_dbEmpty_diag_re]
  simp only [← (dbIndex m n).sum_comp, Equiv.symm_apply_apply]
  unfold prColl
  rw [Finset.mul_sum]
  refine Fintype.sum_of_injective (fun (H : Fin m → Fin n) x => (H x).castSucc)
    (fun H H' h => funext fun x => Fin.castSucc_injective n (congrFun h x)) _ _ ?_ ?_
  · intro D hD
    obtain ⟨x, hx⟩ : ∃ x, ¬ (((D x : Fin (n + 1)) : ℕ) < n) := by
      by_contra hc
      exact hD ⟨fun x => ⟨D x, not_not.mp fun hx => hc ⟨x, hx⟩⟩, funext fun x => Fin.ext rfl⟩
    rw [Finset.prod_eq_zero (Finset.mem_univ x) (ite_eq_right hx), zero_mul]
  · intro H
    simp only [Fin.val_castSucc, Fin.is_lt, ite_true, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, diagonal_outColl_castSucc_eq_collTest]
    rw [show dbFun m n (dbIndex m n fun x => (H x).castSucc) = H from
      funext fun x => by simp [dbFun, truncEntry_castSucc], prCollAt, runOp, inv_pow]

/-- The collision bound from the database bound (Zhandry, Lemma 5, at the two output
    points): `prColl A out ≤ 2 prDbColl A + 16 / n`. -/
theorem prColl_le_two_mul_prDbColl_add (A : QAdv m n w q)
    (out : Fin (m * n * w) → Fin m × Fin m) :
    prColl A out ≤ 2 * prDbColl A + 16 / n := by
  obtain ⟨ψ, hψ⟩ := exists_eq_sum_vecMulVec_of_posSemidef (initCmp A).psd
  have hnorm : ∑ k, nrm (ψ k) ^ 2 = 1 := by
    have h := (initCmp A).tr_one
    have htr1 : (∑ k, vecMulVec (ψ k) (star (ψ k))).trace =
        ((∑ k, nrm (ψ k) ^ 2 : ℝ) : ℂ) := by
      rw [trace_sum, Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [trace_vecMulVec, dotProduct_star_self]
    rw [hψ, htr1] at h
    exact_mod_cast h
  obtain ⟨V, hV⟩ : ∃ V : Matrix (Fin (m * n * w * (n + 1) ^ m))
      (Fin (m * n * w * (n + 1) ^ m)) ℂ, V = ↑(decompU m n w) := ⟨_, rfl⟩
  have hVu : V ∈ Matrix.unitaryGroup (Fin (m * n * w * (n + 1) ^ m)) ℂ := hV ▸ (decompU m n w).prop
  have hDH : (decompDB m n)ᴴ = decompDB m n := by
    simp only [decompDB_eq_dbOp, dbOp_conjTranspose, decompEntry_conjTranspose]
  have hVH : Vᴴ =
      (1 : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) ⊗ₖ decompDB m n := by
    rw [hV, decompU, oneKronU_val, conjTranspose_kronecker, conjTranspose_one]
    exact congrArg _ hDH
  have hVV : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hVu
  have hVV' : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hVu
  have hW : ∀ i, V *
      (tableLiftU ((n + 1) ^ m) (A.U i) : Matrix _ _ ℂ) =
      (tableLiftU ((n + 1) ^ m) (A.U i) : Matrix _ _ ℂ) * V := by
    intro i
    rw [hV, decompU, oneKronU_val, tableLiftU_val, kronecker_mul_kronecker, kronecker_mul_kronecker,
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
  have hcmp : ((cmpLocalU m n w : Matrix.unitaryGroup _ ℂ) :
      Matrix (Fin (m * n * w * (n + 1) ^ m)) (Fin (m * n * w * (n + 1) ^ m)) ℂ) =
      Vᴴ * (stdDbU m n w : Matrix _ _ ℂ) * V := by
    rw [hV, cmpLocalU_eq_cmpOracleU, ← star_eq_conjTranspose]
    rfl
  have hX : V * (initCmp A).val * Vᴴ =
      A.init.val ⊗ₖ (conjDM (decompDBU m n) (dbEmpty m n)).val := by
    rw [hV, initCmp, kronDM_val, conjDM_val, decompU, oneKronU_val, conjTranspose_kronecker,
      conjTranspose_one, kronecker_mul_kronecker, kronecker_mul_kronecker, Matrix.one_mul,
      Matrix.mul_one]
  rw [prColl_eq_trace, ← hX]
  unfold prDbColl
  rw [oracleChain_unitaryChannel_branch, hcmp, chainOp_conj _ _ hVV hVV' q _ hW]
  set C := chainOp (stdDbU m n w : Matrix _ _ ℂ) q
    (fun i => tableLiftU ((n + 1) ^ m) (A.U i)) with hC
  set P := outCollProj m n out with hP
  set Q := collProj m n (m * n * w) with hQ
  set ρ := (initCmp A).val with hρ
  have h1 : (P * C) * (V * ρ * Vᴴ) * (P * C)ᴴ = (P * C * V) * ρ * (P * C * V)ᴴ := by
    rw [conjTranspose_mul (P * C) V]
    simp only [Matrix.mul_assoc]
  have h2 : (Q * ((Vᴴ * C * V) * ρ * (Vᴴ * C * V)ᴴ)).trace =
      ((Q * (Vᴴ * C * V)) * ρ * (Q * (Vᴴ * C * V))ᴴ).trace := by
    rw [conjTranspose_mul Q, hQ, collProj_conjTranspose, ← hQ]
    calc (Q * ((Vᴴ * C * V) * ρ * (Vᴴ * C * V)ᴴ)).trace
        = ((Q * Q) * ((Vᴴ * C * V) * ρ * (Vᴴ * C * V)ᴴ)).trace := by
          rw [hQ, collProj_mul_self]
      _ = (Q * ((Vᴴ * C * V) * ρ * (Vᴴ * C * V)ᴴ) * Q).trace := by
          rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [h1, h2, hψ, trace_mul_sum_vecMulVec_mul_conjTranspose,
    trace_mul_sum_vecMulVec_mul_conjTranspose, Complex.ofReal_re, Complex.ofReal_re]
  have hk : ∀ k, nrm ((P * C * V) *ᵥ ψ k) ^ 2 ≤
      2 * nrm ((Q * (Vᴴ * C * V)) *ᵥ ψ k) ^ 2 + 16 / n * nrm (ψ k) ^ 2 := by
    intro k
    have hφ : nrm ((C * V) *ᵥ ψ k) ≤ nrm (ψ k) := by
      rw [← mulVec_mulVec]
      refine (nrm_chainOp_mulVec_le _ (fun v =>
        (nrm_mulVec_of_mem_unitaryGroup (stdDbU m n w).prop v).le) q _ _).trans ?_
      exact (nrm_mulVec_of_mem_unitaryGroup hVu _).le
    have h3 := nrm_sq_outCollProj_le (n := n) out ((C * V) *ᵥ ψ k)
    have h4 := nrm_sq_outCollProj_le_collProj (n := n) out (Vᴴ *ᵥ ((C * V) *ᵥ ψ k))
    rw [← hVH] at h3
    have e1 : (P * C * V) *ᵥ ψ k = P *ᵥ ((C * V) *ᵥ ψ k) := by
      rw [mulVec_mulVec, Matrix.mul_assoc]
    have e2 : (Q * (Vᴴ * C * V)) *ᵥ ψ k = Q *ᵥ (Vᴴ *ᵥ ((C * V) *ᵥ ψ k)) := by
      simp only [mulVec_mulVec, Matrix.mul_assoc]
    have h5 : nrm ((C * V) *ᵥ ψ k) ^ 2 ≤ nrm (ψ k) ^ 2 := pow_le_pow_left₀ (nrm_nonneg _) hφ 2
    have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 16 / n)
    rw [e1, e2]
    linarith
  refine (Finset.sum_le_sum fun k _ => hk k).trans_eq ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hnorm, mul_one]

/-- The collision bound for a random oracle: a `q`-query adversary outputs a collision
    of a uniformly random `H : Fin m → Fin n` with probability at most
    `16 (q³ + 1) / n`. -/
theorem prColl_le (A : QAdv m n w q) (out : Fin (m * n * w) → Fin m × Fin m) :
    prColl A out ≤ 16 * ((q : ℝ) ^ 3 + 1) / n := by
  have h1 := prColl_le_two_mul_prDbColl_add A out
  have h2 := prDbColl_le A
  have e : 2 * (8 * (q : ℝ) ^ 3 / n) + 16 / n = 16 * ((q : ℝ) ^ 3 + 1) / n := by ring
  linarith

end Coll

end CatCrypt.Quantum.QROM
