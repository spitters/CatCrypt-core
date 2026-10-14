/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.CompressedOracle
public import CatCryptCore.Quantum.QROM.MeasureReprogram

/-!
# The per-query compressed oracle and the database bound

Zhandry's compressed oracle in its per-query form (CRYPTO 2019): on the query
input `x`, decompress the database entry `x`, apply the standard oracle (which
reads only the entry `x`), and compress the entry `x` again. It is equal to the
global form `cmpOracleU` of `CompressedOracle`, which decompresses every entry.
Since the per-query oracle changes only the queried entry, after `q` queries
from the empty database the state is supported on databases with at most `q`
entries different from `⊥`.

## Main definitions

* `dbOp m n F` — the entrywise product operator `⟨D|dbOp F|D'⟩ = ∏ₓ ⟨D x|F x|D' x⟩`
  on the database register
* `ctrlDb m n w A` — the operator `∑ₓ Π_{x} ⊗ₖ A x`, applying `A x` to the
  database register controlled on the query input `x`
* `decompAt m n x` — decompression of the database entry `x` alone
* `cmpLocal m n w`, `cmpLocalU m n w` — the per-query compressed oracle
  `ctrlDecomp * stdDbU * ctrlDecomp`
* `dbWeight`, `totWeight` — the number of non-`⊥` database entries
* `dbProjLe m n s`, `projLe d m n s` — the projector onto the databases with at
  most `s` non-`⊥` entries, on the database register and on the total register
* `WeightBound M s` — every nonzero entry `M K L` has `totWeight K ≤ totWeight L + s`

## Main results

* `dbOp_mul` — `dbOp F * dbOp G = dbOp (F * G)`
* `cmpOracle_eq_sum`, `cmpLocal_eq_sum` — both oracles equal
  `∑ₓ ∑_c (U_c Π_x) ⊗ₖ dbOp (update 1 x (Dec |c⟩⟨c| Dec))`
* `cmpLocalU_eq_cmpOracleU` — the per-query and the global compressed oracle are equal
* `runCmpLocal_eq_runCmp`, `prOutCmpLocal_eq_prOutPure` — the runs agree, and the
  per-query compressed oracle from the empty database gives the acceptance
  probability of the purified standard oracle
* `cmpLocal_weightBound` — one call of the per-query oracle adds at most one
  non-`⊥` entry
* `chainOp_weightBound` — the operator of a `q`-query chain adds at most `q`
* `runCmp_database_le` — `projLe q * C * (initCmp A) = C * (initCmp A)` for the
  `q`-query chain operator `C` of the per-query oracle
* `runCmp_state_le` — the state after the `q`-query chain from `initCmp A` is
  fixed by `projLe q` on both sides

## References

* [Zhandry — How to Record Quantum Queries, and Applications to Quantum
  Indifferentiability, CRYPTO 2019]
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix Classical CatCrypt.Quantum CatCrypt.Quantum.TensorProduct
  CatCrypt.Quantum.UnitaryChannel CatCrypt.Quantum.Measurement

noncomputable section

namespace CatCrypt.Quantum.QROM

private theorem zero_kronecker' {d t : ℕ} (Y : Matrix (Fin t) (Fin t) ℂ) :
    (0 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ Y = 0 := by
  ext i j
  simp [kronecker_apply]

/-! ## Entrywise product operators on the database register -/

section DbOp

variable (m n : ℕ)

/-- The entrywise product operator on the database register:
    `⟨D|dbOp F|D'⟩ = ∏ₓ ⟨D x|F x|D' x⟩`. -/
def dbOp (F : Fin m → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Matrix (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) ℂ :=
  Matrix.of fun i j => ∏ x, F x ((dbIndex m n).symm i x) ((dbIndex m n).symm j x)

theorem dbOp_apply (F : Fin m → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i j : Fin ((n + 1) ^ m)) :
    dbOp m n F i j = ∏ x, F x ((dbIndex m n).symm i x) ((dbIndex m n).symm j x) := rfl

theorem decompDB_eq_dbOp : decompDB m n = dbOp m n fun _ => decompEntry n := rfl

theorem dbOp_mul (F G : Fin m → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    dbOp m n F * dbOp m n G = dbOp m n fun x => F x * G x := by
  ext i j
  rw [Matrix.mul_apply, ← (dbIndex m n).sum_comp]
  simp only [dbOp, Matrix.of_apply, Equiv.symm_apply_apply, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun x y =>
    F x ((dbIndex m n).symm i x) y * G x y ((dbIndex m n).symm j x))]
  simp only [Matrix.mul_apply]

theorem dbOp_conjTranspose (F : Fin m → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    (dbOp m n F)ᴴ = dbOp m n fun x => (F x)ᴴ := by
  ext i j
  simp [dbOp, conjTranspose_apply, star_prod]

/-- The projector onto the databases whose entry `x` is `c`, written as an
    entrywise product operator. -/
theorem dbOp_update_single (x : Fin m) (c : Fin (n + 1)) :
    dbOp m n (Function.update 1 x (Matrix.single c c 1)) =
      ∑ k, if (dbIndex m n).symm k x = c then Matrix.single k k (1 : ℂ) else 0 := by
  ext i j
  rw [Matrix.sum_apply]
  by_cases hij : i = j
  · subst hij
    rw [dbOp_apply, Fintype.prod_eq_single x (fun x' hx' => by
      simp [hx']), Function.update_self,
      Finset.sum_eq_single i (fun k _ hk => by split_ifs <;> simp [hk]) (by simp)]
    split_ifs with h
    · simp [h]
    · simp [Ne.symm h]
  · have hne : ∃ x', (dbIndex m n).symm i x' ≠ (dbIndex m n).symm j x' := by
      by_contra hc
      exact hij ((dbIndex m n).symm.injective
        (funext fun x' => not_not.mp fun hx => hc ⟨x', hx⟩))
    obtain ⟨x', hx'⟩ := hne
    rw [dbOp_apply, Finset.prod_eq_zero (Finset.mem_univ x')]
    · symm
      refine Finset.sum_eq_zero fun k _ => ?_
      split_ifs
      · simp only [Matrix.single_apply]
        rw [if_neg]
        rintro ⟨rfl, rfl⟩
        exact hij rfl
      · rfl
    · by_cases hx : x' = x
      · subst hx
        simp only [Function.update_self, Matrix.single_apply]
        rw [if_neg]
        rintro ⟨h1, h2⟩
        exact hx' (h1.symm.trans h2)
      · simp [hx, hx']

/-- An entrywise product operator that is the identity off the entry `x` has
    nonzero entries only between databases that agree off `x`. -/
theorem dbOp_update_apply_ne_zero (x : Fin m) (Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i j : Fin ((n + 1) ^ m)) (h : dbOp m n (Function.update 1 x Z) i j ≠ 0)
    (x' : Fin m) (hx' : x' ≠ x) : (dbIndex m n).symm i x' = (dbIndex m n).symm j x' := by
  rw [dbOp_apply] at h
  have := Finset.prod_ne_zero_iff.mp h x' (Finset.mem_univ _)
  rw [Function.update_of_ne hx', Pi.one_apply, Matrix.one_apply] at this
  by_contra hc
  exact this (if_neg hc)

end DbOp

/-! ## The query projector and the standard oracle -/

section QueryProj

variable (m n w : ℕ)

private theorem xPart_finProdEquiv' (x : Fin m) (y : Fin n) (z : Fin w) :
    xPart m n w (finProdEquiv (m * n) w (fixedIndex m n (x, y), z)) = x := by
  simp [xPart, fixedIndex, finProdEquiv]

theorem projS_singleton_mul (x x' : Fin m) :
    projS m n w {x} * projS m n w {x'} = if x = x' then projS m n w {x} else 0 := by
  split_ifs with h
  · subst h; exact projS_mul_self m n w {x}
  · rw [projS_eq_diagonal, projS_eq_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_zero]
    congr 1; funext k
    simp only [indS, Finset.mem_singleton]
    split_ifs with h1 h2 <;> simp_all

variable [NeZero n]

/-- The query projector commutes with the oracle. -/
theorem projS_mul_oracleU_comm (S : Finset (Fin m)) (H : Fin m → Fin n) :
    projS m n w S * (oracleU m n w H : Matrix _ _ ℂ) =
      (oracleU m n w H : Matrix _ _ ℂ) * projS m n w S := by
  rw [projS_eq_diagonal]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  obtain ⟨⟨p, z⟩, rfl⟩ := (finProdEquiv (m * n) w).surjective j
  obtain ⟨⟨x, y⟩, rfl⟩ := (fixedIndex m n).surjective p
  obtain ⟨⟨p', z'⟩, rfl⟩ := (finProdEquiv (m * n) w).surjective i
  obtain ⟨⟨x', y'⟩, rfl⟩ := (fixedIndex m n).surjective p'
  simp only [oracleU_val, kronecker_apply, Equiv.symm_apply_apply, xPart_finProdEquiv',
    stdOracleFixedG_apply_fixedIndex_pair]
  by_cases hxy : (x', y') = stdOraclePerm H (x, y)
  · have hx : x' = x := congrArg Prod.fst hxy
    subst hx
    ring
  · simp only [if_neg hxy]
    ring

/-- On the query input `x`, the oracle for `H` depends on `H` only through `H x`. -/
theorem oracleU_mul_projS_singleton_congr (H H' : Fin m → Fin n) (x : Fin m)
    (h : H x = H' x) :
    (oracleU m n w H : Matrix _ _ ℂ) * projS m n w {x} =
      (oracleU m n w H' : Matrix _ _ ℂ) * projS m n w {x} := by
  have hP : projS m n w {x} = 1 - projS m n w (Finset.univ.erase x) := by
    rw [projS_eq_diagonal, projS_eq_diagonal, ← Matrix.diagonal_one, Matrix.diagonal_sub]
    congr 1; funext k
    simp only [indS, Finset.mem_singleton, Finset.mem_erase, Finset.mem_univ, and_true]
    split_ifs <;> simp_all
  rw [hP]
  exact oracleU_mul_one_sub_projS (w := w) H H' _ fun x' hx' => by
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, not_not] at hx'
    subst hx'; exact h

end QueryProj

/-! ## Controlled operators on the database register -/

section Ctrl

variable (m n w : ℕ)

/-- The operator `∑ₓ Π_{x} ⊗ₖ A x`: on the query input `x`, apply `A x` to the
    database register. -/
def ctrlDb (A : Fin m → Matrix (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) ℂ) :
    Matrix (Fin (m * n * w * (n + 1) ^ m)) (Fin (m * n * w * (n + 1) ^ m)) ℂ :=
  ∑ x, projS m n w {x} ⊗ₖ A x

theorem ctrlDb_const (B : Matrix (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) ℂ) :
    ctrlDb m n w (fun _ => B) = 1 ⊗ₖ B := by
  rw [ctrlDb, kronecker_finset_sum_left, sum_projS_singleton]

variable [NeZero n]

/-- The standard oracle on the database register, restricted to the query input
    `x`, is the sum over the values `c` of the entry `x` of the oracle for the
    constant function `truncEntry c` tensored with the projector onto the
    databases whose entry `x` is `c`. -/
theorem stdDbU_mul_projS_kronecker (x : Fin m) :
    (stdDbU m n w : Matrix _ _ ℂ) *
        (projS m n w {x} ⊗ₖ (1 : Matrix (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) ℂ)) =
      ∑ c : Fin (n + 1), ((oracleU m n w (fun _ => truncEntry n c) : Matrix _ _ ℂ) *
        projS m n w {x}) ⊗ₖ dbOp m n (Function.update 1 x (Matrix.single c c 1)) := by
  simp_rw [dbOp_update_single, ← kronecker_finset_sum_right]
  rw [Finset.sum_comm, stdDbU, tableOracleU, blockU_val, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [kronecker_mul_kronecker, Matrix.mul_one,
    Finset.sum_eq_single ((dbIndex m n).symm k x) (fun c _ hc => by
      rw [if_neg (Ne.symm hc), kronecker_zero_right]) (by simp), if_pos rfl]
  congr 1
  exact oracleU_mul_projS_singleton_congr m n w _ _ x rfl

/-- Normal form of `ctrlDb A * stdDbU * ctrlDb B`. -/
theorem ctrlDb_mul_stdDbU_mul_ctrlDb
    (A B : Fin m → Matrix (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) ℂ) :
    ctrlDb m n w A * (stdDbU m n w : Matrix _ _ ℂ) * ctrlDb m n w B =
      ∑ x, ∑ c : Fin (n + 1), ((oracleU m n w (fun _ => truncEntry n c) : Matrix _ _ ℂ) *
        projS m n w {x}) ⊗ₖ (A x * dbOp m n (Function.update 1 x (Matrix.single c c 1)) * B x) := by
  have hB : ctrlDb m n w B = ∑ x', (projS m n w {x'} ⊗ₖ
      (1 : Matrix (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) ℂ)) * (projS m n w {x'} ⊗ₖ B x') := by
    unfold ctrlDb
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [kronecker_mul_kronecker, projS_mul_self, Matrix.one_mul]
  have hterm : ∀ x x', (projS m n w {x} ⊗ₖ A x) * (stdDbU m n w : Matrix _ _ ℂ) *
      (projS m n w {x'} ⊗ₖ (1 : Matrix (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) ℂ)) *
        (projS m n w {x'} ⊗ₖ B x') =
      if x = x' then ∑ c : Fin (n + 1), ((oracleU m n w (fun _ => truncEntry n c) : Matrix _ _ ℂ) *
        projS m n w {x}) ⊗ₖ (A x * dbOp m n (Function.update 1 x (Matrix.single c c 1)) * B x)
      else 0 := by
    intro x x'
    rw [Matrix.mul_assoc (projS m n w {x} ⊗ₖ A x), stdDbU_mul_projS_kronecker, Finset.mul_sum,
      Finset.sum_mul]
    simp only [kronecker_mul_kronecker]
    split_ifs with h
    · subst h
      refine Finset.sum_congr rfl fun c _ => ?_
      congr 1
      simp only [← Matrix.mul_assoc, projS_mul_oracleU_comm]
      simp only [Matrix.mul_assoc, projS_mul_self]
    · refine Finset.sum_eq_zero fun c _ => ?_
      simp only [← Matrix.mul_assoc, projS_mul_oracleU_comm]
      simp [Matrix.mul_assoc, projS_singleton_mul, h, zero_kronecker']
  rw [hB, Finset.mul_sum]
  simp only [ctrlDb, Finset.sum_mul, ← Matrix.mul_assoc, hterm]
  rw [Finset.sum_comm]
  simp

end Ctrl

/-! ## The per-query compressed oracle -/

section Local

variable (m n w : ℕ) [NeZero n]

/-- Decompression of the database entry `x` alone. -/
def decompAt (x : Fin m) : Matrix (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) ℂ :=
  dbOp m n (Function.update 1 x (decompEntry n))

/-- Decompression of the queried entry: on the query input `x`, decompress the
    database entry `x`. -/
def ctrlDecomp : Matrix (Fin (m * n * w * (n + 1) ^ m)) (Fin (m * n * w * (n + 1) ^ m)) ℂ :=
  ctrlDb m n w (decompAt m n)

/-- The per-query compressed oracle: decompress the queried entry, apply the
    standard oracle on the database register, compress the queried entry. -/
def cmpLocal : Matrix (Fin (m * n * w * (n + 1) ^ m)) (Fin (m * n * w * (n + 1) ^ m)) ℂ :=
  ctrlDecomp m n w * (stdDbU m n w : Matrix _ _ ℂ) * ctrlDecomp m n w

/-- The global compressed oracle in normal form. -/
theorem cmpOracle_eq_sum :
    (cmpOracleU m n w : Matrix _ _ ℂ) =
      ∑ x, ∑ c : Fin (n + 1), ((oracleU m n w (fun _ => truncEntry n c) : Matrix _ _ ℂ) *
        projS m n w {x}) ⊗ₖ
          dbOp m n (Function.update 1 x (decompEntry n * Matrix.single c c 1 * decompEntry n)) := by
  have h1 : (cmpOracleU m n w : Matrix _ _ ℂ) = ctrlDb m n w (fun _ => decompDB m n) *
      (stdDbU m n w : Matrix _ _ ℂ) * ctrlDb m n w (fun _ => decompDB m n) := by
    rw [ctrlDb_const, cmpOracleU]
    rw [Submonoid.coe_mul, Submonoid.coe_mul]
    change star ((decompU m n w : Matrix.unitaryGroup (Fin (m * n * w * (n + 1) ^ m)) ℂ) :
      Matrix (Fin (m * n * w * (n + 1) ^ m)) (Fin (m * n * w * (n + 1) ^ m)) ℂ) * _ * _ = _
    rw [star_eq_conjTranspose, decompU, oneKronU_val, TensorProduct.conjTranspose_kronecker,
      conjTranspose_one]
    change (1 ⊗ₖ (decompDB m n)ᴴ) * _ * (1 ⊗ₖ decompDB m n) = _
    rw [decompDB_eq_dbOp, dbOp_conjTranspose]
    simp only [decompEntry_conjTranspose]
  rw [h1, ctrlDb_mul_stdDbU_mul_ctrlDb]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun c _ => ?_
  rw [decompDB_eq_dbOp, dbOp_mul, dbOp_mul]
  congr 2
  funext x'
  by_cases hx : x' = x
  · subst hx; simp
  · simp [Function.update_of_ne hx, decompEntry_mul_self]

/-- The per-query compressed oracle in normal form. -/
theorem cmpLocal_eq_sum :
    cmpLocal m n w =
      ∑ x, ∑ c : Fin (n + 1), ((oracleU m n w (fun _ => truncEntry n c) : Matrix _ _ ℂ) *
        projS m n w {x}) ⊗ₖ
          dbOp m n (Function.update 1 x (decompEntry n * Matrix.single c c 1 * decompEntry n)) := by
  rw [cmpLocal, ctrlDecomp, ctrlDb_mul_stdDbU_mul_ctrlDb]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun c _ => ?_
  rw [decompAt, dbOp_mul, dbOp_mul]
  congr 2
  funext x'
  by_cases hx : x' = x
  · subst hx; simp
  · simp [Function.update_of_ne hx]

theorem cmpLocal_eq_cmpOracle : cmpLocal m n w = (cmpOracleU m n w : Matrix _ _ ℂ) := by
  rw [cmpLocal_eq_sum, cmpOracle_eq_sum]

/-- The per-query compressed oracle as a unitary. -/
def cmpLocalU : Matrix.unitaryGroup (Fin (m * n * w * (n + 1) ^ m)) ℂ :=
  ⟨cmpLocal m n w, (cmpLocal_eq_cmpOracle m n w) ▸ (cmpOracleU m n w).prop⟩

/-- The per-query compressed oracle equals the global compressed oracle. -/
theorem cmpLocalU_eq_cmpOracleU : cmpLocalU m n w = cmpOracleU m n w :=
  Subtype.ext (cmpLocal_eq_cmpOracle m n w)

variable {m n w} {q : ℕ}

/-- The run of `A` against the per-query compressed oracle. -/
def runCmpLocal (A : QAdv m n w q) : QComp (m * n * w * (n + 1) ^ m) Bool :=
  runLift ((n + 1) ^ m) (cmpLocalU m n w) A

theorem runCmpLocal_eq_runCmp (A : QAdv m n w q) : runCmpLocal A = runCmp A := by
  rw [runCmpLocal, runCmp, cmpLocalU_eq_cmpOracleU]

/-- The per-query compressed oracle from the empty database and the purified
    standard oracle give the same acceptance probability. -/
theorem prOutCmpLocal_eq_prOutPure (A : QAdv m n w q) :
    prTrue_Q (runCmpLocal A) (initCmp A) = prOutPure A := by
  rw [runCmpLocal_eq_runCmp, ← prOut_compressed_eq]
  rfl

end Local

/-! ## The number of non-empty database entries -/

section Weight

variable {m n : ℕ}

/-- The number of entries of the database `k` different from `⊥`. -/
def dbWeight (k : Fin ((n + 1) ^ m)) : ℕ :=
  (Finset.univ.filter fun x => (dbIndex m n).symm k x ≠ Fin.last n).card

/-- The number of non-`⊥` database entries of a total-register index. -/
def totWeight {d : ℕ} (K : Fin (d * (n + 1) ^ m)) : ℕ :=
  dbWeight (m := m) (n := n) ((finProdEquiv d ((n + 1) ^ m)).symm K).2

/-- Every nonzero entry `M K L` has `totWeight K ≤ totWeight L + s`: `M` adds
    at most `s` non-`⊥` database entries. -/
def WeightBound {d : ℕ} (M : Matrix (Fin (d * (n + 1) ^ m)) (Fin (d * (n + 1) ^ m)) ℂ)
    (s : ℕ) : Prop :=
  ∀ K L, M K L ≠ 0 → totWeight (m := m) (n := n) K ≤ totWeight (m := m) (n := n) L + s

variable {d : ℕ}

theorem WeightBound.mono {M : Matrix (Fin (d * (n + 1) ^ m)) (Fin (d * (n + 1) ^ m)) ℂ}
    {s t : ℕ} (h : WeightBound M s) (hst : s ≤ t) : WeightBound M t :=
  fun K L hKL => (h K L hKL).trans (by omega)

theorem WeightBound.mul {M N : Matrix (Fin (d * (n + 1) ^ m)) (Fin (d * (n + 1) ^ m)) ℂ}
    {s t : ℕ} (hM : WeightBound M s) (hN : WeightBound N t) : WeightBound (M * N) (s + t) := by
  intro K L hKL
  rw [Matrix.mul_apply] at hKL
  obtain ⟨J, _, hJ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hKL
  have h1 := hM K J (left_ne_zero_of_mul hJ)
  have h2 := hN J L (right_ne_zero_of_mul hJ)
  omega

theorem WeightBound.sum {ι : Type} [Fintype ι]
    {M : ι → Matrix (Fin (d * (n + 1) ^ m)) (Fin (d * (n + 1) ^ m)) ℂ} {s : ℕ}
    (h : ∀ i, WeightBound (M i) s) : WeightBound (∑ i, M i) s := by
  intro K L hKL
  rw [Matrix.sum_apply] at hKL
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hKL
  exact h i K L hi

theorem weightBound_kronecker (X : Matrix (Fin d) (Fin d) ℂ)
    (Y : Matrix (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) ℂ) (s : ℕ)
    (hY : ∀ a b, Y a b ≠ 0 → dbWeight (m := m) (n := n) a ≤ dbWeight (m := m) (n := n) b + s) :
    WeightBound (m := m) (n := n) (X ⊗ₖ Y) s := by
  intro K L hKL
  rw [kronecker_apply] at hKL
  exact hY _ _ (right_ne_zero_of_mul hKL)

theorem weightBound_kronecker_one (X : Matrix (Fin d) (Fin d) ℂ) :
    WeightBound (m := m) (n := n) (X ⊗ₖ (1 : Matrix (Fin ((n + 1) ^ m)) _ ℂ)) 0 :=
  weightBound_kronecker X 1 0 fun a b hab => by
    rw [Matrix.one_apply] at hab
    by_cases h : a = b
    · subst h; omega
    · exact absurd (if_neg h) hab

/-- A database operator that is the identity off the entry `x` adds at most one
    non-`⊥` entry. -/
theorem dbWeight_le_of_dbOp_update (x : Fin m) (Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (a b : Fin ((n + 1) ^ m)) (h : dbOp m n (Function.update 1 x Z) a b ≠ 0) :
    dbWeight (m := m) (n := n) a ≤ dbWeight (m := m) (n := n) b + 1 := by
  unfold dbWeight
  refine (Finset.card_le_card (t := insert x (Finset.univ.filter fun x' =>
    (dbIndex m n).symm b x' ≠ Fin.last n)) ?_).trans (Finset.card_insert_le _ _)
  intro x' hx'
  rw [Finset.mem_insert, Finset.mem_filter]
  by_cases hxx : x' = x
  · exact Or.inl hxx
  · right
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← dbOp_update_apply_ne_zero m n x Z a b h x' hxx]
    exact (Finset.mem_filter.mp hx').2

end Weight

/-! ## The database bound -/

section Bound

variable {m n w : ℕ} [NeZero n]

/-- One call of the per-query compressed oracle adds at most one non-`⊥`
    database entry. -/
theorem cmpLocal_weightBound : WeightBound (m := m) (n := n) (cmpLocal m n w) 1 := by
  rw [cmpLocal_eq_sum]
  exact WeightBound.sum fun x => WeightBound.sum fun c =>
    weightBound_kronecker _ _ 1 fun a b hab => dbWeight_le_of_dbOp_update x _ a b hab

omit [NeZero n] in
/-- The operator of a `q`-query chain whose oracle adds at most one entry and
    whose other unitaries add none adds at most `q` entries. -/
theorem chainOp_weightBound {d : ℕ} (O : Matrix (Fin (d * (n + 1) ^ m)) (Fin (d * (n + 1) ^ m)) ℂ)
    (hO : WeightBound (m := m) (n := n) O 1) (q : ℕ)
    (U : Fin (q + 1) → Matrix.unitaryGroup (Fin (d * (n + 1) ^ m)) ℂ)
    (hU : ∀ i, WeightBound (m := m) (n := n)
      ((U i : Matrix.unitaryGroup _ ℂ) : Matrix (Fin (d * (n + 1) ^ m)) (Fin (d * (n + 1) ^ m)) ℂ) 0) :
    WeightBound (m := m) (n := n) (chainOp O q U) q := by
  induction q with
  | zero => exact hU 0
  | succ q ih =>
    exact (((ih (Fin.tail U) fun i => hU i.succ).mul hO).mul (hU 0)).mono (by omega)

variable (m n) in
/-- The projector onto the databases with at most `s` non-`⊥` entries. -/
def dbProjLe (s : ℕ) : Matrix (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) ℂ :=
  Matrix.diagonal fun k => if dbWeight (m := m) (n := n) k ≤ s then 1 else 0

variable (m n) in
/-- The projector onto the databases with at most `s` non-`⊥` entries,
    tensored with the identity on the other registers. -/
def projLe (d s : ℕ) : Matrix (Fin (d * (n + 1) ^ m)) (Fin (d * (n + 1) ^ m)) ℂ :=
  (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ dbProjLe m n s

omit [NeZero n] in
theorem projLe_apply {d : ℕ} (s : ℕ) (K L : Fin (d * (n + 1) ^ m)) :
    projLe m n d s K L =
      if K = L then (if totWeight (m := m) (n := n) K ≤ s then 1 else 0) else 0 := by
  rw [projLe, kronecker_apply, Matrix.one_apply, dbProjLe, Matrix.diagonal_apply, totWeight]
  by_cases h : K = L
  · subst h; simp
  · have : ¬(((finProdEquiv d ((n + 1) ^ m)).symm K).1 = ((finProdEquiv d ((n + 1) ^ m)).symm L).1 ∧
        ((finProdEquiv d ((n + 1) ^ m)).symm K).2 = ((finProdEquiv d ((n + 1) ^ m)).symm L).2) :=
      fun ⟨h1, h2⟩ => h ((finProdEquiv d ((n + 1) ^ m)).symm.injective (Prod.ext h1 h2))
    rcases not_and_or.mp this with h1 | h2
    · simp [h, h1]
    · simp [h, h2]

omit [NeZero n] in
/-- An operator adding at most `s` entries, applied to an operator whose rows
    lie on the empty database, lands in the range of `projLe s`. -/
theorem projLe_mul_of_weightBound {d : ℕ}
    {M N : Matrix (Fin (d * (n + 1) ^ m)) (Fin (d * (n + 1) ^ m)) ℂ} {s : ℕ}
    (hM : WeightBound (m := m) (n := n) M s)
    (hN : ∀ K L, N K L ≠ 0 → totWeight (m := m) (n := n) K = 0) :
    projLe m n d s * (M * N) = M * N := by
  ext K L
  rw [Matrix.mul_apply, Finset.sum_eq_single K (fun J _ hJ => by
    rw [projLe_apply, if_neg (Ne.symm hJ), zero_mul]) (by simp), projLe_apply, if_pos rfl]
  split_ifs with hK
  · rw [one_mul]
  · rw [zero_mul]
    by_contra hc
    rw [Matrix.mul_apply] at hc
    obtain ⟨J, _, hJ⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Ne.symm hc)
    have h1 := hM K J (left_ne_zero_of_mul hJ)
    have h2 := hN J L (right_ne_zero_of_mul hJ)
    omega

omit [NeZero n] in
theorem dbWeight_dbEmptyIdx : dbWeight (m := m) (n := n) (dbEmptyIdx m n) = 0 := by
  simp [dbWeight, dbEmptyIdx]

omit [NeZero n] in
/-- The rows of the initial compressed state lie on the empty database. -/
theorem initCmp_apply_ne_zero {q : ℕ} (A : QAdv m n w q) (K L : Fin (m * n * w * (n + 1) ^ m))
    (h : (initCmp A).val K L ≠ 0) : totWeight (m := m) (n := n) K = 0 := by
  rw [initCmp, kronDM_val, kronecker_apply] at h
  have h2 := right_ne_zero_of_mul h
  simp only [dbEmpty, vecMulVec_apply, Pi.single_apply] at h2
  have hK : ((finProdEquiv (m * n * w) ((n + 1) ^ m)).symm K).2 = dbEmptyIdx m n := by
    by_contra hc
    exact h2 (by simp [hc])
  rw [totWeight, hK, dbWeight_dbEmptyIdx]

/-- After `q` queries to the per-query compressed oracle from the empty database,
    the state lies in the range of the projector onto the databases with at most
    `q` non-`⊥` entries. -/
theorem runCmp_database_le {q : ℕ} (A : QAdv m n w q) :
    projLe m n (m * n * w) q *
        (chainOp (cmpLocalU m n w : Matrix _ _ ℂ) q (fun i => tableLiftU ((n + 1) ^ m) (A.U i)) *
          (initCmp A).val) =
      chainOp (cmpLocalU m n w : Matrix _ _ ℂ) q (fun i => tableLiftU ((n + 1) ^ m) (A.U i)) *
        (initCmp A).val :=
  projLe_mul_of_weightBound
    (chainOp_weightBound _ cmpLocal_weightBound q _ fun _ => weightBound_kronecker_one _)
    (initCmp_apply_ne_zero A)

/-- The state after the `q`-query chain of the per-query compressed oracle from
    `initCmp A` is fixed by `projLe q` on both sides. -/
theorem runCmp_state_le {q : ℕ} (A : QAdv m n w q) :
    let σ := (oracleChain (unitaryChannel (cmpLocalU m n w)) q
      (fun i => tableLiftU ((n + 1) ^ m) (A.U i))).branch () (initCmp A).val
    projLe m n (m * n * w) q * σ = σ ∧ σ * projLe m n (m * n * w) q = σ := by
  intro σ
  set C := chainOp (cmpLocalU m n w : Matrix _ _ ℂ) q (fun i => tableLiftU ((n + 1) ^ m) (A.U i))
  have hσ : σ = C * (initCmp A).val * Cᴴ := oracleChain_unitaryChannel_branch _ _ _ _
  have hP : (projLe m n (m * n * w) q)ᴴ = projLe m n (m * n * w) q := by
    ext K L
    rw [conjTranspose_apply, projLe_apply, projLe_apply]
    by_cases h : K = L
    · subst h; split_ifs <;> simp
    · simp [h, Ne.symm h]
  have hρ : ((initCmp A).val)ᴴ = (initCmp A).val := (initCmp A).psd.isHermitian
  have h1 : projLe m n (m * n * w) q * σ = σ := by
    rw [hσ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ C, runCmp_database_le]
  refine ⟨h1, ?_⟩
  have hσh : σᴴ = σ := by
    rw [hσ, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hρ,
      Matrix.mul_assoc]
  calc σ * projLe m n (m * n * w) q = (projLe m n (m * n * w) q * σ)ᴴ := by
        rw [conjTranspose_mul, hP, hσh]
    _ = σ := by rw [h1, hσh]

end Bound

end CatCrypt.Quantum.QROM
