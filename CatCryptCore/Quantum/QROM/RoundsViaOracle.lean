/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.MRGenFinalH

/-!
# Round functions that read the oracle, as oracle queries

A multi-round adversary `A : QAdvMRGen m n w q k c a` whose round function is
`y ↦ g y (H (π y))` reads the oracle `H` at the point `π y` of each round outcome `y`.
The adversary `A.viaOracle π g` computes these answers with one more oracle query per
segment and accepts with the same probability at every round function `f₀`
(`prOutMRGen_viaOracle_eq`).

The register of `A.viaOracle π g` is the register of `A` with an ancilla `Fin m × Fin n`
inside the work register, started at `(0, 0)`. Round `j` of `A.viaOracle π g` is the
projective measurement of round `j` of `A` with trivial answers. The first two local
operations of segment `j + 1` form the gadget of round `j`:

* the Kraus operators `W (P y ⊗ X_{(π y, 0)})`, where `W` exchanges the query register and
  the ancilla, move the query register into the ancilla and write `(π y, 0)` into it;
* the oracle query writes `H (π y)` into the value register;
* the Kraus operators `(ans (g y h) P y ⊗ |0⟩⟨(x, h)|) Wᴴ` read the value `h`, apply the
  answer of round `j` and move the query register back, resetting the ancilla to `(0, 0)`;
  the second of the two operations then runs the first operation of segment `j + 1` of `A`.

Segment `0` starts with the same gadget for the round with one outcome and no answer, so
that every segment has `q + 1` queries. All other operations are those of `A`, tensored
with `1` on the ancilla.

The exchange `W` is the permutation unitary of `exPerm`. Along the index equivalence
`swapE`, which places the ancilla in the query register and the query register of `A` in
the ancilla, the oracle is `1 ⊗ O_H` (`oracleU_eq_kr_swapE`), and the gadget becomes a
computation on tensor products.

## Main definitions

* `swapE m n w`, `exPerm m n w`, `exU m n w` — the index equivalence with the query
  register and the ancilla exchanged, the permutation relating it to `ancE`, and its unitary
* `krausCh M h` — the channel of the Kraus family `M` with its outcome discarded
* `trivR d` — the round with one outcome, the identity projector and the identity answer
* `dephR R` — the round `R` with every answer the identity
* `gadPre R pt`, `gadPost R g` — the two Kraus channels of the gadget
* `segOps R pt g U` — the local operations of a segment that starts with the gadget
* `QAdvMRGen.viaOracle A π g` — the adversary with one oracle query per round

## Main results

* `gadget_branch` — on `B ⊗ |0⟩⟨0|` the gadget computes the round on `B`
* `presQ_mrChainG` — the chain of `A.viaOracle π g` computes the chain of `A`
* `prOutMRGen_viaOracle_eq` — the acceptance probabilities agree
* `flatQ_succ_succ` — the flattened query count of `A.viaOracle π g` is that of `A` plus
  `k + 1`
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct CatCrypt.Quantum.UnitaryChannel

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Ancilla unit matrices -/

section Anc

variable {c : ℕ}

/-- The conjugate transpose of `|y⟩⟨y'|` is `|y'⟩⟨y|`. -/
theorem ancUnit_conjTranspose (y y' : Fin c) : (ancUnit y y')ᴴ = ancUnit y' y := by
  ext i j; simp [ancUnit, and_comm]

/-- The product `|y⟩⟨y'| |z⟩⟨z'|`. -/
theorem ancUnit_mul_ancUnit (y y' z z' : Fin c) :
    ancUnit y y' * ancUnit z z' = if y' = z then ancUnit y z' else 0 := by
  ext i j
  split_ifs with h <;> simp [Matrix.mul_apply, ancUnit, h, ite_and] <;> grind

/-- The shift is unitary. -/
theorem ancShift_conjTranspose_mul_self [NeZero c] (y : Fin c) :
    (ancShift y)ᴴ * ancShift y = 1 :=
  mul_eq_one_comm.mp (ancShift_mul_conjTranspose_self y)

end Anc

/-! ## The register with the query register and the ancilla exchanged -/

section Swap

variable (m n w : ℕ)

/-- `((p, z), a) ↦ (a, (z, p))`. -/
def swapAux : (Fin (m * n) × Fin w) × Fin (m * n) ≃ Fin (m * n) × (Fin w × Fin (m * n)) where
  toFun u := (u.2, (u.1.2, u.1.1))
  invFun v := ((v.2.2, v.2.1), v.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The index of `(p, z) ⊗ a` with the ancilla `a` in the query register and the query
    register `p` in the ancilla. -/
def swapE : Fin (m * n * w * (m * n)) ≃ Fin (m * n * (w * (m * n))) :=
  (finProdEquiv (m * n * w) (m * n)).symm.trans <|
    (((finProdEquiv (m * n) w).symm.prodCongr (Equiv.refl _)).trans (swapAux m n w)).trans <|
      ((Equiv.refl _).prodCongr (finProdEquiv w (m * n))).trans
        (finProdEquiv (m * n) (w * (m * n)))

/-- The inverse of `swapE` on an index of the extended register. -/
theorem swapE_symm_apply (a : Fin (m * n)) (z : Fin w) (p : Fin (m * n)) :
    (swapE m n w).symm (finProdEquiv (m * n) (w * (m * n)) (a, finProdEquiv w (m * n) (z, p))) =
      finProdEquiv (m * n * w) (m * n) (finProdEquiv (m * n) w (p, z), a) := by
  simp [swapE, swapAux]

/-- The permutation of the extended register taking the indices of `ancE` to those of
    `swapE`. -/
def exPerm : Equiv.Perm (Fin (m * n * (w * (m * n)))) :=
  (ancE m n w (m * n)).symm.trans (swapE m n w)

/-- The unitary of `exPerm`. -/
def exU : Matrix (Fin (m * n * (w * (m * n)))) (Fin (m * n * (w * (m * n)))) ℂ :=
  (permUnitary (exPerm m n w) : Matrix _ _ ℂ)

/-- `kr` along `swapE` is `kr` along `ancE` conjugated by `exU`. -/
theorem kr_swapE (A : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ)
    (B : Matrix (Fin (m * n)) (Fin (m * n)) ℂ) :
    kr (swapE m n w) A B = exU m n w * kr (ancE m n w (m * n)) A B * (exU m n w)ᴴ := by
  rw [exU, permUnitary_conj]; rfl

theorem exU_conjTranspose_mul_self : (exU m n w)ᴴ * exU m n w = 1 :=
  star_permUnitary_mul _

theorem exU_mul_conjTranspose_self : exU m n w * (exU m n w)ᴴ = 1 :=
  mul_eq_one_comm.mp (exU_conjTranspose_mul_self m n w)

/-- Along `swapE`, the identity on the register of `A` tensored with `X` on the ancilla is
    `X` on the query register. -/
theorem kr_swapE_one_left (X : Matrix (Fin (m * n)) (Fin (m * n)) ℂ) :
    kr (swapE m n w) (1 : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) X =
      X ⊗ₖ (1 : Matrix (Fin (w * (m * n))) (Fin (w * (m * n))) ℂ) := by
  ext i j
  obtain ⟨⟨a, t⟩, rfl⟩ := (finProdEquiv (m * n) (w * (m * n))).surjective i
  obtain ⟨⟨z, p⟩, rfl⟩ := (finProdEquiv w (m * n)).surjective t
  obtain ⟨⟨a', t'⟩, rfl⟩ := (finProdEquiv (m * n) (w * (m * n))).surjective j
  obtain ⟨⟨z', p'⟩, rfl⟩ := (finProdEquiv w (m * n)).surjective t'
  simp [kr, swapE_symm_apply, kronecker_apply, Matrix.one_apply, and_comm]

variable {m n w}

/-- Along `swapE` the oracle acts on the ancilla. -/
theorem oracleU_eq_kr_swapE [NeZero n] (H : Fin m → Fin n) :
    (oracleU m n (w * (m * n)) H : Matrix _ _ ℂ) =
      kr (swapE m n w) (1 : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ)
        (stdOracleFixedG m n H) := by
  rw [oracleU_val, kr_swapE_one_left]

/-- The oracle permutes the ancilla unit matrices. -/
theorem stdOracleFixedG_conj_ancUnit [NeZero n] (H : Fin m → Fin n) (x : Fin m) :
    stdOracleFixedG m n H * ancUnit (fixedIndex m n (x, 0)) (fixedIndex m n (x, 0)) *
        (stdOracleFixedG m n H)ᴴ =
      ancUnit (fixedIndex m n (x, H x)) (fixedIndex m n (x, H x)) := by
  rw [stdOracleFixedG, permUnitary_conj]
  ext i j
  simp only [Matrix.submatrix_apply, ancUnit, Matrix.of_apply, Equiv.symm_apply_eq,
    Equiv.permCongr_apply, stdOraclePerm_apply, Equiv.symm_apply_apply, zero_add]

end Swap

/-! ## Kraus channels -/

section Kraus

variable {D : ℕ}

/-- The branch of the Kraus channel `krausCh M h`. -/
theorem krausCh_branch {r : ℕ} (M : Fin r → Matrix (Fin D) (Fin D) ℂ)
    (h : ∑ i, (M i)ᴴ * M i = 1) (ρ : Matrix (Fin D) (Fin D) ℂ) :
    (krausCh M h).toQComp.branch () ρ = ∑ i, M i * ρ * (M i)ᴴ :=
  krausChQ_branch M h () ρ

/-- `X` followed by `Y`. -/
def compCh (X Y : CPComp D Unit) : CPComp D Unit := X.qbind fun _ => Y

theorem compCh_branch (X Y : CPComp D Unit) (ρ : Matrix (Fin D) (Fin D) ℂ) :
    (compCh X Y).toQComp.branch () ρ = Y.toQComp.branch () (X.toQComp.branch () ρ) := by
  rw [compCh, CPComp.toQComp_qbind, qbind_unit_branch]

theorem isTP_compCh {X Y : CPComp D Unit} (hX : IsTP (X.toQComp.branch ()))
    (hY : IsTP (Y.toQComp.branch ())) : IsTP ((compCh X Y).toQComp.branch ()) := fun ρ => by
  rw [compCh_branch, hY, hX]

end Kraus

/-! ## Rounds with trivial answers -/

section Rounds

variable {d c a : ℕ}

/-- The round with one outcome, the identity projector and the identity answer. -/
def trivR (d : ℕ) : ClassicalRound d 1 1 where
  P _ := 1
  P_conjTranspose _ := conjTranspose_one
  P_mul_self _ := one_mul 1
  P_orth y y' h := absurd (Subsingleton.elim y y') h
  P_sum := by simp
  ans _ := 1

theorem roundU_trivR (f : Fin 1 → Fin 1) : roundU (trivR d) f = QComp.qpure () := by
  refine QComp.ext_fun fun u ρ => ?_
  rw [roundU_branch, qpure_branch_apply]
  simp [trivR]

/-- The round `R` with every answer the identity: the projective measurement of `R`. -/
def dephR (R : ClassicalRound d c a) : ClassicalRound d c a :=
  { R with ans := fun _ => 1 }

/-- A round after the projective measurement of the same round is the round. -/
theorem qbind_roundU_dephR (R : ClassicalRound d c a) (f₀ f : Fin c → Fin a) :
    QComp.qbind (roundU (dephR R) f₀) (fun _ => roundU R f) = roundU R f := by
  refine QComp.ext_fun fun u ρ => ?_
  cases u
  rw [qbind_unit_branch, roundU_branch, roundU_branch, roundU_branch]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single y]
  · simp only [dephR, OneMemClass.coe_one, one_mul, conjTranspose_mul, R.P_conjTranspose,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (R.P y) (R.P y), R.P_mul_self, ← Matrix.mul_assoc (R.P y) (R.P y),
      R.P_mul_self]
  · intro y' _ hy'
    simp only [dephR, OneMemClass.coe_one, one_mul, conjTranspose_mul, R.P_conjTranspose,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (R.P y) (R.P y'), R.P_orth y y' (Ne.symm hy')]
    simp
  · simp

end Rounds

/-! ## The gadget -/

section Gadget

variable {m n w c a : ℕ} [NeZero m] [NeZero n]

/-- The Kraus operators `W (P y ⊗ X_{(pt y, 0)})` of the first operation of the gadget. -/
def preOp (R : ClassicalRound (m * n * w) c a) (pt : Fin c → Fin m) (y : Fin c) :
    Matrix (Fin (m * n * (w * (m * n)))) (Fin (m * n * (w * (m * n)))) ℂ :=
  exU m n w * kr (ancE m n w (m * n)) (R.P y) (ancShift (fixedIndex m n (pt y, 0)))

theorem preOp_complete (R : ClassicalRound (m * n * w) c a) (pt : Fin c → Fin m) :
    ∑ y, (preOp R pt y)ᴴ * preOp R pt y = 1 := by
  have h1 : ∀ y, (preOp R pt y)ᴴ * preOp R pt y = kr (ancE m n w (m * n)) (R.P y) 1 := by
    intro y
    simp only [preOp, conjTranspose_mul, kr_conjTranspose]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (exU m n w)ᴴ, exU_conjTranspose_mul_self,
      Matrix.one_mul, kr_mul, R.P_conjTranspose, R.P_mul_self, ancShift_conjTranspose_mul_self]
  rw [Finset.sum_congr rfl fun y _ => h1 y, ← kr_sum_left, R.P_sum, kr_one]

/-- The Kraus operators `(ans (g y h) P y ⊗ |0⟩⟨(x, h)|) Wᴴ` of the second operation of
    the gadget. -/
def postOpP (R : ClassicalRound (m * n * w) c a) (g : Fin c → Fin n → Fin a)
    (yj : Fin c × Fin (m * n)) :
    Matrix (Fin (m * n * (w * (m * n)))) (Fin (m * n * (w * (m * n)))) ℂ :=
  kr (ancE m n w (m * n))
      ((R.ans (g yj.1 ((fixedIndex m n).symm yj.2).2) : Matrix _ _ ℂ) * R.P yj.1)
      (ancUnit 0 yj.2) * (exU m n w)ᴴ

/-- `postOpP` indexed by `Fin (c * (m * n))`. -/
def postOp (R : ClassicalRound (m * n * w) c a) (g : Fin c → Fin n → Fin a)
    (i : Fin (c * (m * n))) :
    Matrix (Fin (m * n * (w * (m * n)))) (Fin (m * n * (w * (m * n)))) ℂ :=
  postOpP R g ((finProdEquiv c (m * n)).symm i)

theorem postOpP_complete (R : ClassicalRound (m * n * w) c a) (g : Fin c → Fin n → Fin a) :
    ∑ yj, (postOpP R g yj)ᴴ * postOpP R g yj = 1 := by
  have h1 : ∀ yj : Fin c × Fin (m * n), (postOpP R g yj)ᴴ * postOpP R g yj =
      exU m n w * kr (ancE m n w (m * n)) (R.P yj.1) (ancProj yj.2) * (exU m n w)ᴴ := by
    intro yj
    simp only [postOpP, conjTranspose_mul, kr_conjTranspose, conjTranspose_conjTranspose,
      ancUnit_conjTranspose]
    rw [← Matrix.mul_assoc, Matrix.mul_assoc (exU m n w), kr_mul,
      R.P_conjTranspose, Matrix.mul_assoc (R.P yj.1), ← Matrix.mul_assoc _ _ (R.P yj.1),
      ← star_eq_conjTranspose, UnitaryGroup.star_mul_self, Matrix.one_mul, R.P_mul_self]
    simp only [ancUnit_mul_ancUnit, ite_true, ancUnit_self]
  rw [Finset.sum_congr rfl fun yj _ => h1 yj, ← Finset.sum_mul, ← Finset.mul_sum,
    Fintype.sum_prod_type]
  simp_rw [← kr_sum_right, sum_ancProj]
  rw [← kr_sum_left, R.P_sum, kr_one, Matrix.mul_one, exU_mul_conjTranspose_self]

theorem postOp_complete (R : ClassicalRound (m * n * w) c a) (g : Fin c → Fin n → Fin a) :
    ∑ i, (postOp R g i)ᴴ * postOp R g i = 1 :=
  ((finProdEquiv c (m * n)).symm.sum_comp _).trans (postOpP_complete R g)

/-- The first operation of the gadget. -/
def gadPre (R : ClassicalRound (m * n * w) c a) (pt : Fin c → Fin m) :
    CPComp (m * n * (w * (m * n))) Unit :=
  krausCh (preOp R pt) (preOp_complete R pt)

/-- The second operation of the gadget, before the first operation of the segment. -/
def gadPost (R : ClassicalRound (m * n * w) c a) (g : Fin c → Fin n → Fin a) :
    CPComp (m * n * (w * (m * n))) Unit :=
  krausCh (postOp R g) (postOp_complete R g)

/-- The composite operator of the gadget along one Kraus path. -/
theorem postOp_mul_oracle_mul_preOp (R : ClassicalRound (m * n * w) c a) (pt : Fin c → Fin m)
    (g : Fin c → Fin n → Fin a) (H : Fin m → Fin n) (yj : Fin c × Fin (m * n)) (y : Fin c) :
    postOpP R g yj * (oracleU m n (w * (m * n)) H : Matrix _ _ ℂ) * preOp R pt y =
      kr (ancE m n w (m * n))
        ((R.ans (g yj.1 ((fixedIndex m n).symm yj.2).2) : Matrix _ _ ℂ) * R.P yj.1 * R.P y)
        (ancUnit 0 yj.2 * stdOracleFixedG m n H * ancShift (fixedIndex m n (pt y, 0))) := by
  rw [oracleU_eq_kr_swapE, kr_swapE, postOpP, preOp]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (exU m n w)ᴴ (exU m n w), exU_conjTranspose_mul_self,
    Matrix.one_mul, ← Matrix.mul_assoc (exU m n w)ᴴ (exU m n w),
    exU_conjTranspose_mul_self, Matrix.one_mul, ← Matrix.mul_assoc, kr_mul, kr_mul,
    Matrix.mul_one]
  simp only [Matrix.mul_assoc]

/-- The ancilla part of the composite operator on `|0⟩⟨0|`. -/
theorem gadget_anc (H : Fin m → Fin n) (x : Fin m) (j : Fin (m * n)) :
    (ancUnit 0 j * stdOracleFixedG m n H * ancShift (fixedIndex m n (x, 0))) * ancProj 0 *
        (ancUnit 0 j * stdOracleFixedG m n H * ancShift (fixedIndex m n (x, 0)))ᴴ =
      if j = fixedIndex m n (x, H x) then ancProj 0 else 0 := by
  have h : (ancUnit 0 j * stdOracleFixedG m n H * ancShift (fixedIndex m n (x, 0))) *
      ancProj 0 * (ancUnit 0 j * stdOracleFixedG m n H * ancShift (fixedIndex m n (x, 0)))ᴴ =
      ancUnit 0 j * (stdOracleFixedG m n H * (ancShift (fixedIndex m n (x, 0)) * ancProj 0 *
        (ancShift (fixedIndex m n (x, 0)))ᴴ) * (stdOracleFixedG m n H)ᴴ) * ancUnit j 0 := by
    simp only [conjTranspose_mul, ancUnit_conjTranspose, Matrix.mul_assoc]
  rw [h, ancShift_mul_ancProj_zero_mul_conjTranspose, stdOracleFixedG_conj_ancUnit,
    ancUnit_mul_ancUnit]
  split_ifs with hj <;> simp [ancUnit_mul_ancUnit, hj, ancUnit_self]

/-- On `B ⊗ |0⟩⟨0|` the gadget computes the round `R` with the round function
    `y ↦ g y (H (pt y))` on `B`. -/
theorem gadget_branch (R : ClassicalRound (m * n * w) c a) (pt : Fin c → Fin m)
    (g : Fin c → Fin n → Fin a) (H : Fin m → Fin n) (B : Matrix (Fin (m * n * w)) _ ℂ) :
    (QComp.qbind (gadPre R pt).toQComp fun _ =>
        QComp.qbind (oracleQ m n (w * (m * n)) H) fun _ => (gadPost R g).toQComp).branch ()
        (kr (ancE m n w (m * n)) B (ancProj 0)) =
      kr (ancE m n w (m * n)) ((roundU R fun y => g y (H (pt y))).branch () B) (ancProj 0) := by
  have hT : ∀ (p : Fin c × Fin (m * n)) (y : Fin c),
      postOpP R g p * ((oracleU m n (w * (m * n)) H : Matrix _ _ ℂ) *
          (preOp R pt y * kr (ancE m n w (m * n)) B (ancProj 0) * (preOp R pt y)ᴴ) *
          (oracleU m n (w * (m * n)) H : Matrix _ _ ℂ)ᴴ) * (postOpP R g p)ᴴ =
        if p = (y, fixedIndex m n (pt y, H (pt y))) then
          kr (ancE m n w (m * n)) ((R.ans (g y (H (pt y))) : Matrix _ _ ℂ) * R.P y * B *
            ((R.ans (g y (H (pt y))) : Matrix _ _ ℂ) * R.P y)ᴴ) (ancProj 0)
        else 0 := by
    intro p y
    have h0 : postOpP R g p * ((oracleU m n (w * (m * n)) H : Matrix _ _ ℂ) *
          (preOp R pt y * kr (ancE m n w (m * n)) B (ancProj 0) * (preOp R pt y)ᴴ) *
          (oracleU m n (w * (m * n)) H : Matrix _ _ ℂ)ᴴ) * (postOpP R g p)ᴴ =
        (postOpP R g p * (oracleU m n (w * (m * n)) H : Matrix _ _ ℂ) * preOp R pt y) *
          kr (ancE m n w (m * n)) B (ancProj 0) *
          (postOpP R g p * (oracleU m n (w * (m * n)) H : Matrix _ _ ℂ) * preOp R pt y)ᴴ := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [h0, postOp_mul_oracle_mul_preOp, kr_conjTranspose, kr_mul, kr_mul, gadget_anc]
    obtain ⟨y', j⟩ := p
    by_cases hj : j = fixedIndex m n (pt y, H (pt y)) <;> by_cases hy : y' = y <;>
      simp_all [R.P_mul_self, Matrix.mul_assoc, R.P_orth y' y, kr_zero_left, kr_zero_right]
  rw [qbind_unit_branch, qbind_unit_branch, gadPre, gadPost, krausCh_branch, oracleQ,
    unitaryChannel_branch_apply, krausCh_branch, roundU_branch, kr_sum_left,
    ← (finProdEquiv c (m * n)).sum_comp]
  simp only [postOp, Equiv.symm_apply_apply, Finset.mul_sum, Finset.sum_mul, hT]
  rw [Finset.sum_comm]; simp

end Gadget

/-! ## Instruments that keep the ancilla at `|0⟩⟨0|` -/

section Pres

variable {d c D : ℕ} [NeZero c]

/-- `O'` computes `O` on states `B ⊗ |0⟩⟨0|` and leaves the ancilla at `|0⟩⟨0|`. -/
def PresAncQ {β : Type} (e : Fin (d * c) ≃ Fin D) (O : QComp d β) (O' : QComp D β) : Prop :=
  ∀ b (B : Matrix (Fin d) (Fin d) ℂ),
    O'.branch b (kr e B (ancProj 0)) = kr e (O.branch b B) (ancProj 0)

theorem LiftsQ.presAncQ {β : Type} {e : Fin (d * c) ≃ Fin D} {O : QComp d β}
    {O' : QComp D β} (h : LiftsQ e O O') : PresAncQ e O O' := fun b B => h b B _

theorem presAncQ_qbind {α β : Type} [Finite α] {e : Fin (d * c) ≃ Fin D} {I : QComp d α}
    {I' : QComp D α} {g : α → QComp d β} {g' : α → QComp D β} (hI : PresAncQ e I I')
    (hg : ∀ x, PresAncQ e (g x) (g' x)) :
    PresAncQ e (QComp.qbind I g) (QComp.qbind I' g') := fun b B => by
  have := Fintype.ofFinite α
  rw [qbind_branch_apply, qbind_branch_apply, tsum_fintype, tsum_fintype, kr_sum_left]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hI, hg]

end Pres

/-! ## Segments that start with the gadget -/

section Chain

variable {m n w q k c a : ℕ} [NeZero m] [NeZero n]

/-- The operations `U` tensored with `1` on the ancilla `Fin (m * n)`. -/
def liftOps (U : Fin (q + 1) → CPComp (m * n * w) Unit)
    (hU : ∀ i, IsTP ((U i).toQComp.branch ())) :
    Fin (q + 1) → CPComp (m * n * (w * (m * n))) Unit :=
  fun i => liftCh (ancE m n w (m * n)) (U i) (hU i)

/-- The `q + 2` operations of a segment that starts with the gadget of the round `R`: the
    first operation of the gadget, the second one followed by `U 0`, then `U 1, …, U q`. -/
def segOps {c' a' : ℕ} (R : ClassicalRound (m * n * w) c' a') (pt : Fin c' → Fin m)
    (g : Fin c' → Fin n → Fin a') (U : Fin (q + 1) → CPComp (m * n * (w * (m * n))) Unit) :
    Fin (q + 1 + 1) → CPComp (m * n * (w * (m * n))) Unit :=
  Fin.cons (gadPre R pt) (Fin.cons (compCh (gadPost R g) (U 0)) fun i => U i.succ)

theorem isTP_segOps {c' a' : ℕ} (R : ClassicalRound (m * n * w) c' a') (pt : Fin c' → Fin m)
    (g : Fin c' → Fin n → Fin a') (U : Fin (q + 1) → CPComp (m * n * (w * (m * n))) Unit)
    (hU : ∀ i, IsTP ((U i).toQComp.branch ())) (i : Fin (q + 1 + 1)) :
    IsTP ((segOps R pt g U i).toQComp.branch ()) :=
  Fin.cases (isTP_krausCh _ _) (Fin.cases (isTP_compCh (isTP_krausCh _ _) (hU 0)) fun i =>
    hU i.succ) i

/-- A chain whose first operation is `X` followed by `Y` is `X` followed by the chain with
    first operation `Y`. -/
theorem chainG_cons_compCh {D : ℕ} (O : QComp D Unit) :
    ∀ (q : ℕ) (X Y : CPComp D Unit) (V : Fin q → CPComp D Unit),
      chainG O q (fun i => (Fin.cons (α := fun _ => CPComp D Unit) (compCh X Y) V i).toQComp) =
        QComp.qbind X.toQComp fun _ =>
          chainG O q (fun i => (Fin.cons (α := fun _ => CPComp D Unit) Y V i).toQComp)
  | 0, X, Y, V => by
    simp only [chainG, Fin.cons_zero, compCh, CPComp.toQComp_qbind]
  | q + 1, X, Y, V => by
    simp only [chainG, Fin.cons_zero, compCh, CPComp.toQComp_qbind, QComp.qbind_assoc]
    rfl

/-- A round followed by a chain is computed by the chain of `segOps`, on `B ⊗ |0⟩⟨0|`. -/
theorem presAncQ_seg {c' a' : ℕ} (H : Fin m → Fin n) (R : ClassicalRound (m * n * w) c' a')
    (pt : Fin c' → Fin m) (g : Fin c' → Fin n → Fin a') (U : Fin (q + 1) → CPComp (m * n * w) Unit)
    (U' : Fin (q + 1) → CPComp (m * n * (w * (m * n))) Unit)
    (hU : ∀ i, LiftsQ (ancE m n w (m * n)) (U i).toQComp (U' i).toQComp) :
    PresAncQ (ancE m n w (m * n))
      (QComp.qbind (roundU R fun y => g y (H (pt y))) fun _ =>
        chainG (oracleQ m n w H) q fun i => (U i).toQComp)
      (chainG (oracleQ m n (w * (m * n)) H) (q + 1) fun i => (segOps R pt g U' i).toQComp) := by
  have hsplit : (chainG (oracleQ m n (w * (m * n)) H) (q + 1)
      fun i => (segOps R pt g U' i).toQComp) =
      QComp.qbind (QComp.qbind (gadPre R pt).toQComp fun _ =>
          QComp.qbind (oracleQ m n (w * (m * n)) H) fun _ => (gadPost R g).toQComp) fun _ =>
        chainG (oracleQ m n (w * (m * n)) H) q fun i => (U' i).toQComp := by
    have hU' : (fun i => (Fin.cons (α := fun _ => CPComp (m * n * (w * (m * n))) Unit) (U' 0)
        (fun i => U' i.succ) i).toQComp) = fun i => (U' i).toQComp :=
      funext fun i => congrArg CPComp.toQComp (congrFun (Fin.cons_self_tail U') i)
    simp only [QComp.qbind_assoc]
    change QComp.qbind (gadPre R pt).toQComp (fun _ =>
      QComp.qbind (oracleQ m n (w * (m * n)) H) fun _ =>
        chainG (oracleQ m n (w * (m * n)) H) q fun i =>
          (Fin.cons (α := fun _ => CPComp (m * n * (w * (m * n))) Unit)
            (compCh (gadPost R g) (U' 0)) (fun i => U' i.succ) i).toQComp) = _
    rw [chainG_cons_compCh, hU']
  rw [hsplit]
  exact presAncQ_qbind (fun b B => by cases b; exact gadget_branch R pt g H B) fun _ =>
    (liftsQ_chainG _ (liftsQ_oracleQ_padE rfl H) q _ _ hU).presAncQ

/-- The chain of the adversary with the oracle queries computes, on `B ⊗ |0⟩⟨0|`, the round
    `Rp` followed by the chain of the adversary with the round function
    `y ↦ g y (H (π y))`. -/
theorem presAncQ_mrChainG (H : Fin m → Fin n) (π : Fin c → Fin m) (g : Fin c → Fin n → Fin a)
    (f₀ : Fin c → Fin a) :
    ∀ (k : ℕ) {c' a' : ℕ} (Rp : ClassicalRound (m * n * w) c' a') (pt : Fin c' → Fin m)
      (gp : Fin c' → Fin n → Fin a') (head : Fin (q + 1) → CPComp (m * n * w) Unit)
      (hh : ∀ i, IsTP ((head i).toQComp.branch ()))
      (tail : Fin k → Fin (q + 1) → CPComp (m * n * w) Unit)
      (ht : ∀ j i, IsTP ((tail j i).toQComp.branch ()))
      (R : Fin k → ClassicalRound (m * n * w) c a),
      PresAncQ (ancE m n w (m * n))
        (QComp.qbind (roundU Rp fun y => gp y (H (pt y))) fun _ =>
          mrChainG (oracleQ m n w H) (fun y => g y (H (π y))) k q
            (fun i => (head i).toQComp) (fun j i => (tail j i).toQComp) R)
        (mrChainG (oracleQ m n (w * (m * n)) H) f₀ k (q + 1)
          (fun i => (segOps Rp pt gp (liftOps head hh) i).toQComp)
          (fun j i => (segOps (R j) π g (liftOps (tail j) (ht j)) i).toQComp)
          fun j => liftRA (ancE m n w (m * n)) (dephR (R j)))
  | 0, _, _, Rp, pt, gp, head, hh, _, _, _ =>
    presAncQ_seg H Rp pt gp head (liftOps head hh) fun i => liftsQ_liftCh _ _ _
  | k + 1, _, _, Rp, pt, gp, head, hh, tail, ht, R => by
    simp only [mrChainG]
    rw [← QComp.qbind_assoc]
    refine presAncQ_qbind (presAncQ_seg H Rp pt gp head (liftOps head hh)
      fun i => liftsQ_liftCh _ _ _) fun _ => ?_
    rw [← qbind_roundU_dephR (R 0) f₀ (fun y => g y (H (π y))), QComp.qbind_assoc]
    exact presAncQ_qbind (liftsQ_roundU_liftRA _ (dephR (R 0)) f₀).presAncQ fun _ =>
      presAncQ_mrChainG H π g f₀ k (R 0) π g (tail 0) (ht 0) (Fin.tail tail)
        (fun j => ht j.succ) (Fin.tail R)

end Chain

/-! ## The adversary with one oracle query per round -/

section ViaOracle

variable {m n w q k c a : ℕ} [NeZero m] [NeZero n]

/-- A round function that reads the oracle at one point per round input is one more
    oracle query per round: the rounds keep their outcomes, and their answers are computed
    by `g` from the value of `H` at `π y`. Segment `0` starts with the gadget of the round
    with one outcome, segment `j + 1` with the gadget of round `j`, and round `j` is the
    projective measurement of round `j` of `A`. -/
def QAdvMRGen.viaOracle (A : QAdvMRGen m n w q k c a) (π : Fin c → Fin m)
    (g : Fin c → Fin n → Fin a) : QAdvMRGen m n (w * (m * n)) (q + 1) k c a where
  seg := Fin.cons (segOps (trivR (m * n * w)) (fun _ => 0) (fun _ _ => 0)
      (liftOps (A.seg 0) (A.seg_tp 0)))
    fun j => segOps (A.rounds j) π g (liftOps (A.seg j.succ) (A.seg_tp j.succ))
  seg_tp j i := by
    cases j using Fin.cases <;> exact isTP_segOps _ _ _ _ (fun i => isTP_liftCh _ _ _) i
  rounds j := liftRA (ancE m n w (m * n)) (dephR (A.rounds j))
  init := liftInit A.init
  final := kr (ancE m n w (m * n)) A.final 1
  final_conjTranspose := by rw [kr_conjTranspose, A.final_conjTranspose, conjTranspose_one]
  final_mul_self := by rw [kr_mul, A.final_mul_self, Matrix.one_mul]

/-- The adversary with one oracle query per round accepts, at every round function `f₀`,
    with the probability of `A` at the round function `y ↦ g y (H (π y))`. -/
theorem prOutMRGen_viaOracle_eq (A : QAdvMRGen m n w q k c a) (π : Fin c → Fin m)
    (g : Fin c → Fin n → Fin a) (H : Fin m → Fin n) (f₀ : Fin c → Fin a) :
    prOutMRGen (A.viaOracle π g) H f₀ = prOutMRGen A H (fun y => g y (H (π y))) := by
  have h0 := presAncQ_mrChainG H π g f₀ k (trivR (m * n * w)) (fun _ => 0) (fun _ _ => 0)
    (A.seg 0) (A.seg_tp 0) (Fin.tail A.seg) (fun j => A.seg_tp j.succ) A.rounds
  rw [roundU_trivR, QComp.qpure_qbind] at h0
  have hrun : PresAncQ (ancE m n w (m * n)) (runMRGen A H fun y => g y (H (π y)))
      (runMRGen (A.viaOracle π g) H f₀) :=
    presAncQ_qbind h0 fun _ => (liftsQ_measProj _ _ _ _ _ _).presAncQ
  unfold prOutMRGen prTrue_Q
  change ENNReal.ofReal (((runMRGen (A.viaOracle π g) H f₀).branch true
    (kr (ancE m n w (m * n)) A.init.val (ancProj 0))).trace.re) = _
  rw [hrun, trace_kr, trace_ancProj, mul_one]

/-- The flattened query count of `A.viaOracle π g` is that of `A` plus `k + 1`. -/
theorem flatQ_succ_succ (q k : ℕ) : flatQ (q + 1) k (q + 1) = flatQ q k q + (k + 1) := by
  grind [flatQ_eq]

end ViaOracle

end CatCrypt.Quantum.QROM
