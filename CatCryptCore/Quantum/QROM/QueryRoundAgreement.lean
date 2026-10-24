/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.QueryRoundPerms
public import CatCryptCore.Quantum.QROM.MultiRound

/-!
# The compiled query round as a unitary on the clean slice

The nine-factor index chain `roundPerm` of `QueryRoundPerms` becomes a unitary
of the extended register through `permUnitary`. On the slice whose two parked
query slots are `0` that unitary acts by the answer permutation selected by the
record slot, and returns the slice to itself.

## Main definitions

* `roundChainU` — the unitary of `roundPerm`
* `CleanReg`, `cleanIdx`, `cleanRec`, `cleanProj`, `IsClean` — the query, work
  and record registers, their index in the extended register, and the predicate
  cutting out the slice with both parked slots `0`
* `cleanLift` — the state of the extended register supported on the clean slice
  with a given block
* `roundAct` — the permutation of `CleanReg` applying the answer family,
  controlled on the record slot
* `queryFun` — the classical function `r ↦ φ r (H (ν₁ r)) (H (ν₂ r))`
* `parkLift` — an answer permutation of the query and work registers as a
  permutation of the extended register
* `cleanRecProj` — the projector onto the clean indices with record slot `y`
* `permRound` — the `ClassicalRound` on the extended register measuring the
  record slot and answering by `parkLift`

## Main results

* `roundChainU_eq_chain` — `roundChainU` is the product of the five
  oracle-independent step unitaries and four copies of the oracle unitary, in
  the order of the chain
* `roundPerm_cleanIdx` — the chain carries a clean index to the clean index of
  `roundAct`
* `roundChainU_conj_cleanLift` — conjugating a clean state by `roundChainU`
  gives the clean state of the block reindexed by `roundAct`
* `roundPerm_cleanIdx_eq_parkLift` — on a clean index with record `y`, the
  chain agrees with the answer permutation `A (queryFun … y)`
* `roundChainU_mul_cleanRecProj` — the matrix form of that agreement:
  `roundChainU` and the answer unitary of `permRound` at `queryFun … y` agree
  on the clean record-`y` slice

## Form of the statements

Every statement is about the unitary of a permutation of the extended
register's index set, at symbolic dimensions. The agreement with
`ClassicalRound` in `roundChainU_mul_cleanRecProj` is the agreement with its
answer unitary on the clean record-`y` slice; `runMRCoh_cleanLift` of
`Quantum/QROM/CoherentCleanRun.lean` lifts it to the runs of a multi-round
adversary.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Matrix
open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct

noncomputable section

namespace CatCrypt.Quantum.QROM

variable (m n w c : ℕ) [NeZero m] [NeZero n] [NeZero c]
variable (ν₁ ν₂ : Fin c → Fin m)
variable {a : ℕ}

/-! ## The unitary of the chain -/

/-- The unitary of the nine-factor index chain of a query round. -/
def roundChainU (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n) :
    Matrix.unitaryGroup (Fin (m * n * (w * ancDim m n c))) ℂ :=
  permUnitary (roundPerm m n w c ν₁ ν₂ φ A H)

theorem permUnitary_coe_mul {ι : Type} [Fintype ι] [DecidableEq ι] (σ τ : Equiv.Perm ι) :
    ((permUnitary (σ * τ) : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) =
      (permUnitary σ : Matrix ι ι ℂ) * (permUnitary τ : Matrix ι ι ℂ) := by
  rw [← permUnitary_mul]
  rfl

/-- The unitary of the chain is the product of the five oracle-independent step
    unitaries and four copies of the oracle unitary. -/
theorem roundChainU_eq_chain (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n) :
    (roundChainU m n w c ν₁ ν₂ φ A H :
        Matrix (Fin (m * n * (w * ancDim m n c))) (Fin (m * n * (w * ancDim m n c))) ℂ) =
      (permUnitary (stepFour m n w c ν₁) : Matrix _ _ ℂ) *
        (oracleU m n (w * ancDim m n c) H : Matrix _ _ ℂ) *
        (permUnitary (stepThree m n w c ν₂) : Matrix _ _ ℂ) *
        (oracleU m n (w * ancDim m n c) H : Matrix _ _ ℂ) *
        (permUnitary (stepTwo m n w c φ A) : Matrix _ _ ℂ) *
        (oracleU m n (w * ancDim m n c) H : Matrix _ _ ℂ) *
        (permUnitary (stepOne m n w c ν₂) : Matrix _ _ ℂ) *
        (oracleU m n (w * ancDim m n c) H : Matrix _ _ ℂ) *
        (permUnitary (stepZero m n w c ν₁) : Matrix _ _ ℂ) := by
  rw [roundChainU, roundPerm]
  simp only [permUnitary_coe_mul, oracleU_eq_permUnitary]

/-! ## The clean slice -/

/-- The query, work and record registers of a query round. -/
abbrev CleanReg : Type := ((Fin m × Fin n) × Fin w) × Fin c

/-- The index of a clean register state: both parked slots `0`. -/
def cleanIdx (s : CleanReg m n w c) : Fin (m * n * (w * ancDim m n c)) :=
  roundIndex m n w c (s.1.1, s.1.2, s.2, (0, 0), (0, 0))

/-- The record slot of an index of the extended register. -/
def cleanRec (i : Fin (m * n * (w * ancDim m n c))) : Fin c :=
  ((roundIndex m n w c).symm i).2.2.1

/-- The query, work and record registers read off an index of the extended
    register. -/
def cleanProj (i : Fin (m * n * (w * ancDim m n c))) : CleanReg m n w c :=
  ((((roundIndex m n w c).symm i).1, ((roundIndex m n w c).symm i).2.1),
    ((roundIndex m n w c).symm i).2.2.1)

/-- An index of the extended register whose two parked slots are `0`. -/
def IsClean (i : Fin (m * n * (w * ancDim m n c))) : Prop :=
  ((roundIndex m n w c).symm i).2.2.2 = ((0, 0), (0, 0))

instance instDecidableIsClean (i : Fin (m * n * (w * ancDim m n c))) :
    Decidable (IsClean m n w c i) := by
  unfold IsClean; infer_instance

@[simp]
theorem cleanProj_cleanIdx (s : CleanReg m n w c) :
    cleanProj m n w c (cleanIdx m n w c s) = s := by
  simp [cleanProj, cleanIdx]

@[simp]
theorem cleanRec_cleanIdx (s : CleanReg m n w c) :
    cleanRec m n w c (cleanIdx m n w c s) = s.2 := by
  simp [cleanRec, cleanIdx]

@[simp]
theorem isClean_cleanIdx (s : CleanReg m n w c) : IsClean m n w c (cleanIdx m n w c s) := by
  simp [IsClean, cleanIdx]

theorem cleanIdx_cleanProj {i : Fin (m * n * (w * ancDim m n c))} (h : IsClean m n w c i) :
    cleanIdx m n w c (cleanProj m n w c i) = i := by
  rw [IsClean] at h
  rw [cleanIdx, cleanProj]
  rw [← h]
  simp

/-! ## The action on the clean slice -/

/-- The classical function of a table-reading round. -/
def queryFun (φ : Fin c → Fin n → Fin n → Fin a) (H : Fin m → Fin n) : Fin c → Fin a :=
  fun r => φ r (H (ν₁ r)) (H (ν₂ r))

/-- The answer family applied to the query and work registers, controlled on
    the record slot. -/
def roundAct (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n) :
    Equiv.Perm (CleanReg m n w c) where
  toFun := fun (s, r) => (A (queryFun m n c ν₁ ν₂ φ H r) s, r)
  invFun := fun (s, r) => ((A (queryFun m n c ν₁ ν₂ φ H r)).symm s, r)
  left_inv := by rintro ⟨s, r⟩; simp
  right_inv := by rintro ⟨s, r⟩; simp

theorem roundAct_apply (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n)
    (s : (Fin m × Fin n) × Fin w) (r : Fin c) :
    roundAct m n w c ν₁ ν₂ φ A H (s, r) = (A (queryFun m n c ν₁ ν₂ φ H r) s, r) := rfl

/-- The chain carries a clean index to the clean index of `roundAct`. -/
theorem roundPerm_cleanIdx (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n)
    (s : CleanReg m n w c) :
    roundPerm m n w c ν₁ ν₂ φ A H (cleanIdx m n w c s) =
      cleanIdx m n w c (roundAct m n w c ν₁ ν₂ φ A H s) := by
  obtain ⟨⟨q, z⟩, r⟩ := s
  rw [cleanIdx, roundPerm_apply_clean, roundAct_apply, cleanIdx, queryFun]

theorem roundPerm_symm_cleanIdx (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n)
    (s : CleanReg m n w c) :
    (roundPerm m n w c ν₁ ν₂ φ A H).symm (cleanIdx m n w c s) =
      cleanIdx m n w c ((roundAct m n w c ν₁ ν₂ φ A H).symm s) := by
  rw [Equiv.symm_apply_eq, roundPerm_cleanIdx, Equiv.apply_symm_apply]

theorem isClean_roundPerm_symm_iff (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n)
    (i : Fin (m * n * (w * ancDim m n c))) :
    IsClean m n w c ((roundPerm m n w c ν₁ ν₂ φ A H).symm i) ↔ IsClean m n w c i := by
  constructor
  · intro h
    have := cleanIdx_cleanProj m n w c h
    have hi : i = roundPerm m n w c ν₁ ν₂ φ A H
        (cleanIdx m n w c (cleanProj m n w c ((roundPerm m n w c ν₁ ν₂ φ A H).symm i))) := by
      rw [this, Equiv.apply_symm_apply]
    rw [hi, roundPerm_cleanIdx]
    exact isClean_cleanIdx m n w c _
  · intro h
    rw [← cleanIdx_cleanProj m n w c h, roundPerm_symm_cleanIdx]
    exact isClean_cleanIdx m n w c _

theorem cleanProj_roundPerm_symm (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n)
    {i : Fin (m * n * (w * ancDim m n c))} (h : IsClean m n w c i) :
    cleanProj m n w c ((roundPerm m n w c ν₁ ν₂ φ A H).symm i) =
      (roundAct m n w c ν₁ ν₂ φ A H).symm (cleanProj m n w c i) := by
  conv_lhs => rw [← cleanIdx_cleanProj m n w c h, roundPerm_symm_cleanIdx]
  rw [cleanProj_cleanIdx]

/-- The state of the extended register supported on the clean slice with the
    block `ρ`. -/
def cleanLift (ρ : Matrix (CleanReg m n w c) (CleanReg m n w c) ℂ) :
    Matrix (Fin (m * n * (w * ancDim m n c))) (Fin (m * n * (w * ancDim m n c))) ℂ :=
  Matrix.of fun i j =>
    if IsClean m n w c i ∧ IsClean m n w c j then
      ρ (cleanProj m n w c i) (cleanProj m n w c j)
    else 0

/-- Conjugating a clean state by `roundChainU` gives the clean state of the
    block reindexed by `roundAct`. -/
theorem roundChainU_conj_cleanLift (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n)
    (ρ : Matrix (CleanReg m n w c) (CleanReg m n w c) ℂ) :
    (roundChainU m n w c ν₁ ν₂ φ A H : Matrix _ _ ℂ) * cleanLift m n w c ρ *
        (roundChainU m n w c ν₁ ν₂ φ A H : Matrix _ _ ℂ)ᴴ =
      cleanLift m n w c
        (ρ.submatrix (roundAct m n w c ν₁ ν₂ φ A H).symm
          (roundAct m n w c ν₁ ν₂ φ A H).symm) := by
  rw [roundChainU, permUnitary_conj]
  ext i j
  simp only [Matrix.submatrix_apply, cleanLift, Matrix.of_apply]
  by_cases hi : IsClean m n w c i <;> by_cases hj : IsClean m n w c j
  · rw [ite_eq_left ⟨(isClean_roundPerm_symm_iff m n w c ν₁ ν₂ φ A H i).2 hi,
      (isClean_roundPerm_symm_iff m n w c ν₁ ν₂ φ A H j).2 hj⟩, ite_eq_left ⟨hi, hj⟩,
      cleanProj_roundPerm_symm m n w c ν₁ ν₂ φ A H hi,
      cleanProj_roundPerm_symm m n w c ν₁ ν₂ φ A H hj]
  · rw [ite_eq_right (fun h => hj ((isClean_roundPerm_symm_iff m n w c ν₁ ν₂ φ A H j).1 h.2)),
      ite_eq_right (fun h => hj h.2)]
  · rw [ite_eq_right (fun h => hi ((isClean_roundPerm_symm_iff m n w c ν₁ ν₂ φ A H i).1 h.1)),
      ite_eq_right (fun h => hi h.1)]
  · rw [ite_eq_right (fun h => hi ((isClean_roundPerm_symm_iff m n w c ν₁ ν₂ φ A H i).1 h.1)),
      ite_eq_right (fun h => hi h.1)]

/-! ## The answer family of a classical round -/

/-- An answer permutation of the query and work registers as a permutation of
    the structured extended register. -/
def parkLiftReg (B : Equiv.Perm ((Fin m × Fin n) × Fin w)) : Equiv.Perm (RoundReg m n w c) where
  toFun := fun (q, z, e) => ((B (q, z)).1, (B (q, z)).2, e)
  invFun := fun (q, z, e) => ((B.symm (q, z)).1, (B.symm (q, z)).2, e)
  left_inv := by rintro ⟨q, z, e⟩; simp
  right_inv := by rintro ⟨q, z, e⟩; simp

/-- An answer permutation of the query and work registers as a permutation of
    the extended register's index set. -/
def parkLift (B : Equiv.Perm ((Fin m × Fin n) × Fin w)) :
    Equiv.Perm (Fin (m * n * (w * ancDim m n c))) :=
  (roundIndex m n w c).permCongr (parkLiftReg m n w c B)

theorem parkLift_cleanIdx (B : Equiv.Perm ((Fin m × Fin n) × Fin w)) (s : CleanReg m n w c) :
    parkLift m n w c B (cleanIdx m n w c s) = cleanIdx m n w c (B s.1, s.2) := by
  simp [parkLift, parkLiftReg, cleanIdx, Equiv.permCongr_apply]

/-- On a clean index the chain agrees with the answer permutation selected by
    the record slot. -/
theorem roundPerm_apply_of_clean (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n)
    {j : Fin (m * n * (w * ancDim m n c))} (hc : IsClean m n w c j) :
    roundPerm m n w c ν₁ ν₂ φ A H j =
      parkLift m n w c (A (queryFun m n c ν₁ ν₂ φ H (cleanRec m n w c j))) j := by
  obtain ⟨p, rfl⟩ : ∃ p, j = cleanIdx m n w c p :=
    ⟨cleanProj m n w c j, (cleanIdx_cleanProj m n w c hc).symm⟩
  obtain ⟨s, r⟩ := p
  rw [cleanRec_cleanIdx, roundPerm_cleanIdx, roundAct_apply, parkLift_cleanIdx]

/-- On a clean index with record slot `y` the chain agrees with the answer
    permutation `A (queryFun … y)`. -/
theorem roundPerm_cleanIdx_eq_parkLift (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n)
    (s : (Fin m × Fin n) × Fin w) (y : Fin c) :
    roundPerm m n w c ν₁ ν₂ φ A H (cleanIdx m n w c (s, y)) =
      parkLift m n w c (A (queryFun m n c ν₁ ν₂ φ H y)) (cleanIdx m n w c (s, y)) := by
  rw [roundPerm_apply_of_clean m n w c ν₁ ν₂ φ A H (isClean_cleanIdx m n w c (s, y)),
    cleanRec_cleanIdx]

/-! ## The classical round measuring the record slot -/

/-- The projector onto the indices whose record slot is `y`. -/
def recProj (y : Fin c) :
    Matrix (Fin (m * n * (w * ancDim m n c))) (Fin (m * n * (w * ancDim m n c))) ℂ :=
  Matrix.diagonal fun i => if cleanRec m n w c i = y then 1 else 0

/-- The projector onto the clean indices whose record slot is `y`. -/
def cleanRecProj (y : Fin c) :
    Matrix (Fin (m * n * (w * ancDim m n c))) (Fin (m * n * (w * ancDim m n c))) ℂ :=
  Matrix.diagonal fun i => if IsClean m n w c i ∧ cleanRec m n w c i = y then 1 else 0

/-- The classical round on the extended register that measures the record slot
    and answers by an answer permutation of the query and work registers. -/
def permRound (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) :
    ClassicalRound (m * n * (w * ancDim m n c)) c a where
  P := recProj m n w c
  P_conjTranspose := by
    intro y
    ext i j
    by_cases h : i = j
    · subst h; simp [recProj, Matrix.conjTranspose_apply]
    · simp [recProj, Matrix.conjTranspose_apply, h, Ne.symm h]
  P_mul_self := by
    intro y
    rw [recProj, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> simp
  P_orth := by
    intro y y' hy
    rw [recProj, recProj, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_zero]
    congr 1
    funext i
    split_ifs with h1 h2 <;> simp_all
  P_sum := by
    ext i j
    rw [Matrix.sum_apply]
    by_cases h : i = j
    · subst h
      simp [recProj]
    · simp [recProj, h]
  ans := fun k => permUnitary (parkLift m n w c (A k))

theorem permRound_P (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (y : Fin c) :
    (permRound m n w c A).P y = recProj m n w c y := rfl

theorem permRound_ans (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (k : Fin a) :
    (permRound m n w c A).ans k = permUnitary (parkLift m n w c (A k)) := rfl

/-! ## The agreement on the clean record slice -/

theorem permUnitary_mul_diagonal {ι : Type} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι)
    (g : ι → ℂ) :
    (permUnitary σ : Matrix ι ι ℂ) * Matrix.diagonal g =
      Matrix.of fun i j => if i = σ j then g j else 0 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [permUnitary_apply, Matrix.diagonal_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single j]
  · by_cases h : i = σ j <;> simp [h]
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- On the clean slice with record slot `y`, the unitary of the chain and the
    answer unitary of `permRound` at `queryFun … y` agree. -/
theorem roundChainU_mul_cleanRecProj (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n) (y : Fin c) :
    (roundChainU m n w c ν₁ ν₂ φ A H : Matrix _ _ ℂ) * cleanRecProj m n w c y =
      ((permRound m n w c A).ans (queryFun m n c ν₁ ν₂ φ H y) : Matrix _ _ ℂ) *
        cleanRecProj m n w c y := by
  rw [roundChainU, permRound_ans, cleanRecProj, permUnitary_mul_diagonal,
    permUnitary_mul_diagonal]
  ext i j
  simp only [Matrix.of_apply]
  by_cases hj : IsClean m n w c j ∧ cleanRec m n w c j = y
  · rw [roundPerm_apply_of_clean m n w c ν₁ ν₂ φ A H hj.1, hj.2]
  · rw [ite_eq_right hj]
    split_ifs <;> rfl

end CatCrypt.Quantum.QROM
