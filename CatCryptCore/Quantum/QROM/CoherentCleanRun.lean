/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.MultiRoundCoherent

/-!
# The run of a multi-round adversary on the clean slice

A state supported by a projector `P` is carried to a state supported by `P` by
every unitary commuting with `P`, and two unitaries agreeing after
multiplication by `P` conjugate such a state to the same matrix. On the clean
slice of a query round these two facts turn the per-round agreement
`roundCoh_permRoundCoh_mul_cleanRecProj` into an agreement of the whole run of a
multi-round adversary whose segments leave the record and parked slots alone.

## Main definitions

* `SupportedOn`, `PreservesSupport` — a matrix `ρ` with `P * ρ * P = ρ`, and a
  channel carrying such matrices to such matrices
* `mrChainW` — the chain `head ; (round ; segment)ᵏ` with an arbitrary family of
  round unitaries
* `cleanProjM` — the projector onto the clean indices of the extended register
* `runMRQuery` — the run of a multi-round adversary whose round is the unitary
  `roundChainU` of the compiled query round

## Main results

* `supportedOn_conj`, `conj_eq_of_mul_eq` — conjugation preserves the support of
  `P`, and two unitaries agreeing on `P` conjugate a supported state alike
* `oracleChain_preservesSupport`, `mrChainW_branch_congr` — a segment chain
  preserves the support, and two chains differing only in their round unitaries
  have the same branch at a supported state
* `oracleU_comm_cleanProjM`, `roundChainU_comm_cleanProjM`,
  `roundCoh_permRoundCoh_comm_cleanProjM` — the oracle unitary, the unitary of
  the compiled query round and the coherent round of the record slot commute
  with `cleanProjM`
* `roundCoh_permRoundCoh_mul_cleanProjM` — the coherent round and `roundChainU`
  agree after multiplication by `cleanProjM`
* `runMRCoh_cleanLift` — at a state supported by `cleanProjM` the compiled run
  and the coherent run have the same branches
* `prOutMRCoh_queryRound` — the output probability of the compiled run is that
  of a single `QAdv` with `flatQ q k q = q + k * q` queries

## The hypotheses

`runMRCoh_cleanLift` equates the branches of the two runs at a state supported
by `cleanProjM`. Its hypothesis `hseg` on the adversary's segments is that each
segment unitary commutes with `cleanProjM`; the oracle unitary and the round
unitary commute with it by `oracleU_comm_cleanProjM` and
`roundChainU_comm_cleanProjM`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Matrix ComplexOrder ENNReal
open Matrix Classical CatCrypt.Quantum CatCrypt.Quantum.UnitaryChannel
  CatCrypt.Quantum.Measurement

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## States supported by a projector -/

section Support

variable {d : ℕ}

/-- A matrix compressed to itself by the projector `P`. -/
def SupportedOn (P ρ : Matrix (Fin d) (Fin d) ℂ) : Prop := P * ρ * P = ρ

/-- A matrix commuting with a self-adjoint `P` commutes with it after
    conjugate transposition. -/
theorem conjTranspose_comm_of_comm {P U : Matrix (Fin d) (Fin d) ℂ} (hP : Pᴴ = P)
    (h : U * P = P * U) : Uᴴ * P = P * Uᴴ := by
  have h' := congrArg Matrix.conjTranspose h
  rw [conjTranspose_mul, conjTranspose_mul, hP] at h'
  exact h'.symm

/-- Conjugating a state supported by `P` by a unitary commuting with `P` gives
    a state supported by `P`. -/
theorem supportedOn_conj {P ρ U : Matrix (Fin d) (Fin d) ℂ} (hP : Pᴴ = P)
    (hU : U * P = P * U) (hρ : SupportedOn P ρ) : SupportedOn P (U * ρ * Uᴴ) := by
  have h2 := conjTranspose_comm_of_comm hP hU
  unfold SupportedOn at hρ ⊢
  calc P * (U * ρ * Uᴴ) * P = (P * U) * ρ * (Uᴴ * P) := by simp only [Matrix.mul_assoc]
    _ = (U * P) * ρ * (P * Uᴴ) := by rw [hU, h2]
    _ = U * (P * ρ * P) * Uᴴ := by simp only [Matrix.mul_assoc]
    _ = U * ρ * Uᴴ := by rw [hρ]

/-- Two matrices agreeing after multiplication by a self-adjoint `P` conjugate
    a state supported by `P` to the same matrix. -/
theorem conj_eq_of_mul_eq {P ρ U V : Matrix (Fin d) (Fin d) ℂ} (hP : Pᴴ = P)
    (h : U * P = V * P) (hρ : SupportedOn P ρ) : U * ρ * Uᴴ = V * ρ * Vᴴ := by
  unfold SupportedOn at hρ
  conv_lhs => rw [← hρ]
  conv_rhs => rw [← hρ]
  calc U * (P * ρ * P) * Uᴴ = (U * P) * ρ * (U * P)ᴴ := by
        rw [conjTranspose_mul, hP]; simp only [Matrix.mul_assoc]
    _ = (V * P) * ρ * (V * P)ᴴ := by rw [h]
    _ = V * (P * ρ * P) * Vᴴ := by rw [conjTranspose_mul, hP]; simp only [Matrix.mul_assoc]

/-- A `Unit`-valued channel carrying states supported by `P` to states supported
    by `P`. -/
def PreservesSupport (P : Matrix (Fin d) (Fin d) ℂ) (O : QComp d Unit) : Prop :=
  ∀ ρ, SupportedOn P ρ → SupportedOn P (O.branch () ρ)

theorem preservesSupport_unitaryChannel {P : Matrix (Fin d) (Fin d) ℂ} (hP : Pᴴ = P)
    {U : Matrix.unitaryGroup (Fin d) ℂ}
    (hU : (U : Matrix (Fin d) (Fin d) ℂ) * P = P * (U : Matrix (Fin d) (Fin d) ℂ)) :
    PreservesSupport P (unitaryChannel U) := by
  intro ρ hρ
  rw [unitaryChannel_branch_apply]
  exact supportedOn_conj hP hU hρ

/-- A segment chain of unitaries commuting with `P`, over an oracle preserving
    the support of `P`, preserves the support of `P`. -/
theorem oracleChain_preservesSupport {P : Matrix (Fin d) (Fin d) ℂ} (hP : Pᴴ = P)
    (O : QComp d Unit) (hO : PreservesSupport P O) :
    ∀ (q : ℕ) (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ),
      (∀ i, (U i : Matrix (Fin d) (Fin d) ℂ) * P = P * (U i : Matrix (Fin d) (Fin d) ℂ)) →
      PreservesSupport P (oracleChain O q U)
  | 0, U, hU => preservesSupport_unitaryChannel hP (hU 0)
  | q + 1, U, hU => by
    intro ρ hρ
    show SupportedOn P ((QComp.qbind (unitaryChannel (U 0)) fun _ =>
      QComp.qbind O fun _ => oracleChain O q (Fin.tail U)).branch () ρ)
    rw [qbind_unit_branch, qbind_unit_branch]
    exact oracleChain_preservesSupport hP O hO q (Fin.tail U) (fun i => hU i.succ) _
      (hO _ (preservesSupport_unitaryChannel hP (hU 0) ρ hρ))

end Support

/-! ## The chain with an arbitrary family of round unitaries -/

section ChainW

variable {d q : ℕ}

/-- `head ; (round ; segment)ᵏ` with the round unitaries given as a family. -/
def mrChainW (O : QComp d Unit) :
    (k : ℕ) → (q₀ : ℕ) → (Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ) →
      (Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) →
      (Fin k → Matrix.unitaryGroup (Fin d) ℂ) → QComp d Unit
  | 0, q₀, head, _, _ => oracleChain O q₀ head
  | k + 1, q₀, head, tail, W =>
    QComp.qbind (oracleChain O q₀ head) fun _ =>
      QComp.qbind (unitaryChannel (W 0)) fun _ =>
        mrChainW O k q (tail 0) (Fin.tail tail) (Fin.tail W)

variable {c a : ℕ}

/-- The chain of an adversary with coherent rounds is the chain with the round
    unitaries of those rounds. -/
theorem mrChainCoh_eq_mrChainW (O : QComp d Unit) (f : Fin c → Fin a) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (R : Fin k → CoherentRound d c a),
      mrChainCoh O f k q₀ head tail R = mrChainW O k q₀ head tail fun j => roundCoh (R j) f
  | 0, _, _, _, _ => rfl
  | k + 1, q₀, head, tail, R => by
    show QComp.qbind (oracleChain O q₀ head) _ = QComp.qbind (oracleChain O q₀ head) _
    rw [mrChainCoh_eq_mrChainW O f k q (tail 0) (Fin.tail tail) (Fin.tail R)]
    rfl

/-- Two chains differing only in their round unitaries have the same branch at a
    state supported by `P`, provided the round unitaries agree after
    multiplication by `P` and the segments commute with `P`. -/
theorem mrChainW_branch_congr {P : Matrix (Fin d) (Fin d) ℂ} (hP : Pᴴ = P)
    (O : QComp d Unit) (hO : PreservesSupport P O) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (W W' : Fin k → Matrix.unitaryGroup (Fin d) ℂ),
      (∀ i, (head i : Matrix (Fin d) (Fin d) ℂ) * P = P * (head i : Matrix (Fin d) (Fin d) ℂ)) →
      (∀ j i, (tail j i : Matrix (Fin d) (Fin d) ℂ) * P =
        P * (tail j i : Matrix (Fin d) (Fin d) ℂ)) →
      (∀ j, (W j : Matrix (Fin d) (Fin d) ℂ) * P = P * (W j : Matrix (Fin d) (Fin d) ℂ)) →
      (∀ j, (W j : Matrix (Fin d) (Fin d) ℂ) * P = (W' j : Matrix (Fin d) (Fin d) ℂ) * P) →
      ∀ ρ, SupportedOn P ρ →
        (mrChainW O k q₀ head tail W).branch () ρ = (mrChainW O k q₀ head tail W').branch () ρ
  | 0, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | k + 1, q₀, head, tail, W, W', hhead, htail, hWc, hW, ρ, hρ => by
    have hσ : SupportedOn P ((oracleChain O q₀ head).branch () ρ) :=
      oracleChain_preservesSupport hP O hO q₀ head hhead ρ hρ
    show ((QComp.qbind (oracleChain O q₀ head) fun _ =>
        QComp.qbind (unitaryChannel (W 0)) fun _ =>
          mrChainW O k q (tail 0) (Fin.tail tail) (Fin.tail W)).branch () ρ) =
      ((QComp.qbind (oracleChain O q₀ head) fun _ =>
        QComp.qbind (unitaryChannel (W' 0)) fun _ =>
          mrChainW O k q (tail 0) (Fin.tail tail) (Fin.tail W')).branch () ρ)
    have hstate := conj_eq_of_mul_eq hP (hW 0) hσ
    have hsup := supportedOn_conj hP (hWc 0) hσ
    rw [qbind_unit_branch, qbind_unit_branch, qbind_unit_branch, qbind_unit_branch,
      unitaryChannel_branch_apply, unitaryChannel_branch_apply, ← hstate]
    exact mrChainW_branch_congr hP O hO k q (tail 0) (Fin.tail tail) (Fin.tail W) (Fin.tail W')
      (htail 0) (fun j i => htail j.succ i) (fun j => hWc j.succ) (fun j => hW j.succ) _ hsup

end ChainW

/-! ## The projector onto the clean slice -/

section Clean

variable (m n w c : ℕ) [NeZero m] [NeZero n] [NeZero c]

/-- The projector onto the indices of the extended register whose two parked
    slots are `0`. -/
def cleanProjM :
    Matrix (Fin (m * n * (w * ancDim m n c))) (Fin (m * n * (w * ancDim m n c))) ℂ :=
  Matrix.diagonal fun i => if IsClean m n w c i then 1 else 0

theorem cleanProjM_conjTranspose : (cleanProjM m n w c)ᴴ = cleanProjM m n w c := by
  rw [cleanProjM, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  split_ifs <;> simp_all

theorem cleanProjM_mul_self : cleanProjM m n w c * cleanProjM m n w c = cleanProjM m n w c := by
  rw [cleanProjM, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

/-- The projectors onto the clean record-`y` slices sum to the projector onto
    the clean slice. -/
theorem sum_cleanRecProj : ∑ y, cleanRecProj m n w c y = cleanProjM m n w c := by
  ext i j
  rw [Matrix.sum_apply, cleanProjM]
  by_cases h : i = j
  · subst h
    simp only [cleanRecProj, Matrix.diagonal_apply_eq]
    by_cases hc : IsClean m n w c i
    · simp [hc, Finset.sum_ite_eq]
    · simp [hc]
  · simp [cleanRecProj, Matrix.diagonal_apply_ne, h]

/-- A state lifted from the clean slice is supported by `cleanProjM`. -/
theorem supportedOn_cleanLift (ρ : Matrix (CleanReg m n w c) (CleanReg m n w c) ℂ) :
    SupportedOn (cleanProjM m n w c) (cleanLift m n w c ρ) := by
  unfold SupportedOn
  ext i j
  rw [cleanProjM, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [cleanLift, Matrix.of_apply]
  by_cases hi : IsClean m n w c i <;> by_cases hj : IsClean m n w c j <;>
    simp [hi, hj]

/-- A permutation unitary commutes with a diagonal matrix invariant under the
    permutation. -/
theorem permUnitary_comm_diagonal {ι : Type} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι)
    (g : ι → ℂ) (h : ∀ i, g (σ i) = g i) :
    (permUnitary σ : Matrix ι ι ℂ) * Matrix.diagonal g =
      Matrix.diagonal g * (permUnitary σ : Matrix ι ι ℂ) := by
  rw [permUnitary_mul_diagonal, diagonal_mul_permUnitary]
  ext i j
  simp only [Matrix.of_apply]
  by_cases hij : i = σ j
  · rw [if_pos hij, if_pos hij, hij, h]
  · rw [if_neg hij, if_neg hij]

/-- The oracle permutation leaves the parked slots of an index alone. -/
theorem isClean_oraclePerm (H : Fin m → Fin n) (i : Fin (m * n * (w * ancDim m n c))) :
    IsClean m n w c (oraclePerm m n (w * ancDim m n c) H i) ↔ IsClean m n w c i := by
  rcases hs : (roundIndex m n w c).symm i with ⟨⟨x, y⟩, z, e⟩
  have hi : i = roundIndex m n w c ((x, y), z, e) := by rw [← hs, Equiv.apply_symm_apply]
  subst hi
  rw [oraclePerm_roundIndex]
  simp only [IsClean, Equiv.symm_apply_apply]

variable (ν₁ ν₂ : Fin c → Fin m)
variable {a : ℕ}

/-- The chain of a query round leaves the clean slice invariant. -/
theorem isClean_roundPerm (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n)
    (i : Fin (m * n * (w * ancDim m n c))) :
    IsClean m n w c (roundPerm m n w c ν₁ ν₂ φ A H i) ↔ IsClean m n w c i := by
  have h := isClean_roundPerm_symm_iff m n w c ν₁ ν₂ φ A H (roundPerm m n w c ν₁ ν₂ φ A H i)
  have e0 : ∀ (σ : Equiv.Perm (Fin (m * n * (w * ancDim m n c))))
      (x : Fin (m * n * (w * ancDim m n c))), σ.symm (σ x) = x := fun σ x => σ.symm_apply_apply x
  rw [e0] at h
  exact h.symm

/-- The oracle unitary commutes with the projector onto the clean slice. -/
theorem oracleU_comm_cleanProjM (H : Fin m → Fin n) :
    (oracleU m n (w * ancDim m n c) H : Matrix _ _ ℂ) * cleanProjM m n w c =
      cleanProjM m n w c * (oracleU m n (w * ancDim m n c) H : Matrix _ _ ℂ) := by
  rw [oracleU_eq_permUnitary, cleanProjM]
  refine permUnitary_comm_diagonal _ _ fun i => ?_
  by_cases hc : IsClean m n w c i
  · rw [if_pos ((isClean_oraclePerm m n w c H i).2 hc), if_pos hc]
  · rw [if_neg fun h => hc ((isClean_oraclePerm m n w c H i).1 h), if_neg hc]

/-- The unitary of the compiled query round commutes with the projector onto the
    clean slice. -/
theorem roundChainU_comm_cleanProjM (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n) :
    (roundChainU m n w c ν₁ ν₂ φ A H : Matrix _ _ ℂ) * cleanProjM m n w c =
      cleanProjM m n w c * (roundChainU m n w c ν₁ ν₂ φ A H : Matrix _ _ ℂ) := by
  rw [roundChainU, cleanProjM]
  refine permUnitary_comm_diagonal _ _ fun i => ?_
  by_cases hc : IsClean m n w c i
  · rw [if_pos ((isClean_roundPerm m n w c ν₁ ν₂ φ A H i).2 hc), if_pos hc]
  · rw [if_neg fun h => hc ((isClean_roundPerm m n w c ν₁ ν₂ φ A H i).1 h), if_neg hc]

/-- An answer permutation of the query and work registers leaves the parked
    slots of an index alone. -/
theorem isClean_parkLift (B : Equiv.Perm ((Fin m × Fin n) × Fin w))
    (i : Fin (m * n * (w * ancDim m n c))) :
    IsClean m n w c (parkLift m n w c B i) ↔ IsClean m n w c i := by
  simp [IsClean, parkLift, parkLiftReg, Equiv.permCongr_apply]

/-- The answer unitary of an answer permutation commutes with the projector onto
    the clean slice. -/
theorem permUnitary_parkLift_comm_cleanProjM (B : Equiv.Perm ((Fin m × Fin n) × Fin w)) :
    (permUnitary (parkLift m n w c B) : Matrix _ _ ℂ) * cleanProjM m n w c =
      cleanProjM m n w c * (permUnitary (parkLift m n w c B) : Matrix _ _ ℂ) := by
  rw [cleanProjM]
  refine permUnitary_comm_diagonal _ _ fun i => ?_
  by_cases hc : IsClean m n w c i
  · rw [if_pos ((isClean_parkLift m n w c B i).2 hc), if_pos hc]
  · rw [if_neg fun h => hc ((isClean_parkLift m n w c B i).1 h), if_neg hc]

/-- The projector onto the record-`y` indices commutes with the projector onto
    the clean slice. -/
theorem recProj_comm_cleanProjM (y : Fin c) :
    recProj m n w c y * cleanProjM m n w c = cleanProjM m n w c * recProj m n w c y := by
  rw [recProj, cleanProjM, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

/-- The coherent round of the record slot commutes with the projector onto the
    clean slice. -/
theorem roundCoh_permRoundCoh_comm_cleanProjM
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (f : Fin c → Fin a) :
    (roundCoh (permRoundCoh m n w c A) f : Matrix _ _ ℂ) * cleanProjM m n w c =
      cleanProjM m n w c * (roundCoh (permRoundCoh m n w c A) f : Matrix _ _ ℂ) := by
  rw [roundCoh_val, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [permRoundCoh_P, permRoundCoh_ans, Matrix.mul_assoc, recProj_comm_cleanProjM,
    ← Matrix.mul_assoc, permUnitary_parkLift_comm_cleanProjM, Matrix.mul_assoc]

/-- The coherent round of the record slot and the unitary of the compiled query
    round agree on the clean slice. -/
theorem roundCoh_permRoundCoh_mul_cleanProjM (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n) :
    (roundCoh (permRoundCoh m n w c A) (queryFun m n c ν₁ ν₂ φ H) : Matrix _ _ ℂ) *
        cleanProjM m n w c =
      (roundChainU m n w c ν₁ ν₂ φ A H : Matrix _ _ ℂ) * cleanProjM m n w c := by
  rw [← sum_cleanRecProj, Matrix.mul_sum, Matrix.mul_sum]
  exact Finset.sum_congr rfl fun y _ =>
    roundCoh_permRoundCoh_mul_cleanRecProj m n w c ν₁ ν₂ φ A H y

/-- The oracle channel preserves the support of the projector onto the clean
    slice. -/
theorem oracleQ_preservesSupport (H : Fin m → Fin n) :
    PreservesSupport (cleanProjM m n w c) (oracleQ m n (w * ancDim m n c) H) :=
  preservesSupport_unitaryChannel (cleanProjM_conjTranspose m n w c)
    (oracleU_comm_cleanProjM m n w c H)

end Clean

/-! ## The run with the compiled query round -/

section Run

variable (m n w c : ℕ) [NeZero m] [NeZero n] [NeZero c]
variable (ν₁ ν₂ : Fin c → Fin m)
variable {q k a : ℕ}

/-- The run of a multi-round adversary whose round is the unitary of the
    compiled query round. -/
def runMRQuery (A : QAdvMRCoh m n (w * ancDim m n c) q k c a)
    (φ : Fin c → Fin n → Fin n → Fin a)
    (Ans : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n) :
    QComp (m * n * (w * ancDim m n c)) Bool :=
  QComp.qbind (mrChainW (oracleQ m n (w * ancDim m n c) H) k q (A.seg 0) (Fin.tail A.seg)
    fun _ => roundChainU m n w c ν₁ ν₂ φ Ans H) fun _ => A.measure

/-- At a state supported by the projector onto the clean slice, the run with the
    compiled query round and the run with the coherent round of the record slot
    have the same branches. -/
theorem runMRCoh_cleanLift (A : QAdvMRCoh m n (w * ancDim m n c) q k c a)
    (φ : Fin c → Fin n → Fin n → Fin a)
    (Ans : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n)
    (hseg : ∀ j i, (A.seg j i : Matrix _ _ ℂ) * cleanProjM m n w c =
      cleanProjM m n w c * (A.seg j i : Matrix _ _ ℂ))
    (hrounds : ∀ j, A.rounds j = permRoundCoh m n w c Ans)
    (b : Bool) (ρ : Matrix (Fin (m * n * (w * ancDim m n c))) (Fin (m * n * (w * ancDim m n c))) ℂ)
    (hρ : SupportedOn (cleanProjM m n w c) ρ) :
    (runMRQuery m n w c ν₁ ν₂ A φ Ans H).branch b ρ =
      (runMRCoh A H (queryFun m n c ν₁ ν₂ φ H)).branch b ρ := by
  unfold runMRQuery runMRCoh
  rw [qbind_unit_branch, qbind_unit_branch,
    mrChainCoh_eq_mrChainW (oracleQ m n (w * ancDim m n c) H) (queryFun m n c ν₁ ν₂ φ H)
      k q (A.seg 0) (Fin.tail A.seg) A.rounds]
  refine congrArg _ ?_
  refine mrChainW_branch_congr (cleanProjM_conjTranspose m n w c) _
    (oracleQ_preservesSupport m n w c H) k q (A.seg 0) (Fin.tail A.seg) _ _
    (fun i => hseg 0 i) (fun j i => hseg j.succ i)
    (fun _ => roundChainU_comm_cleanProjM m n w c ν₁ ν₂ φ Ans H) (fun j => ?_) ρ hρ
  rw [hrounds j]
  exact (roundCoh_permRoundCoh_mul_cleanProjM m n w c ν₁ ν₂ φ Ans H).symm

/-- The output probability of the run with the compiled query round is the
    output probability of a single `QAdv` with `flatQ q k q = q + k * q`
    queries. -/
theorem prOutMRCoh_queryRound (A : QAdvMRCoh m n (w * ancDim m n c) q k c a)
    (φ : Fin c → Fin n → Fin n → Fin a)
    (Ans : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n)
    (hseg : ∀ j i, (A.seg j i : Matrix _ _ ℂ) * cleanProjM m n w c =
      cleanProjM m n w c * (A.seg j i : Matrix _ _ ℂ))
    (hrounds : ∀ j, A.rounds j = permRoundCoh m n w c Ans)
    (hinit : SupportedOn (cleanProjM m n w c) A.init.val) :
    prTrue_Q (runMRQuery m n w c ν₁ ν₂ A φ Ans H) A.init =
      prOut (toQAdvCoh A (queryFun m n c ν₁ ν₂ φ H)) H := by
  rw [← prOutMRCoh_eq A H (queryFun m n c ν₁ ν₂ φ H), prOutMRCoh, prTrue_Q, prTrue_Q,
    runMRCoh_cleanLift m n w c ν₁ ν₂ A φ Ans H hseg hrounds true A.init.val hinit]

/-- The query count of the flattened adversary. -/
theorem flatQ_self_eq : flatQ q k q = q + k * q := flatQ_eq q k q

end Run

end CatCrypt.Quantum.QROM
