/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.SigGame
public import CatCryptCore.Quantum.QROM.SparseResampleGentle

/-!
# A final test that reads the oracle, as one more oracle query

A final test `g k (H (p k))` of an adversary `F : QAdv m n w q` reads the oracle `H` at the
point `p k` of the final basis state `k`. The adversary `finalQAdv F p g` computes this value
with one more query: after the last unitary of `F` a permutation unitary moves the query
register `(x, y)` into an ancilla `Fin m × Fin n` started at `(0, 0)` and writes `(p k, 0)`
into the query register; the extra query writes `H (p k)` into the value register; the final
projector is the diagonal projector onto the basis states on which `g` holds of the index
`k` recovered from the ancilla and the work register and of the value register. Its final
projector does not depend on `H`, and its acceptance probability is the one of the test
(`prOut_withFinalB_eq_prOut_finalQAdv`).

A `QAdv` is a multi-round adversary without rounds (`QAdv.toMR`) and so a general
multi-round adversary (`QAdvMR.toGen`). At the forgery test of the EUF-CMA game this gives
`prForge_eq_prOutMRGen`: the winning probability at the oracle `H` is `prOutMRGen` at `H` of
a general adversary with `flatQ q k q + 1` queries and no rounds, the signing table being part
of the adversary. When the table is random, `prOutMRGen_resample_gentle_fiber_le` applies the
resampling bound `prOutMRGen_resample_gentle_le` on each fibre of the table and sums the fibres.

## Main definitions

* `finalRegIdx m n w` — the index of `(((x, y), z), (x₀, y₀))` on the register with the
  ancilla `Fin m × Fin n` inside the work register
* `finalPermAux p`, `finalPerm p` — the permutation
  `(((x, y), z), (x₀, y₀)) ↦ (((x₀ + p k, y₀), z), (x, y))` with `k` the index of
  `((x, y), z)`
* `finalAcc g` — the predicate `g k Y` of a basis state with value register `Y`, `k`
  recovered from the ancilla and the work register
* `finalQAdv F p g` — `F`, the permutation, one more query, and the projector of `finalAcc g`
* `QAdv.toMR B` — `B` as a multi-round adversary without rounds
* `forgeAdvAt S eX eY eQ A pk f` — `finalQAdv` of the flattened adversary at the round
  table `f` at the forgery point and the forgery test

## Main results

* `runOp_finalQAdv` — the run operator of `finalQAdv F p g` is a permutation unitary after
  the lifted run operator of `F`
* `prOut_withFinalB_eq_prOut_finalQAdv` — the acceptance probability of the final test that
  reads the oracle is the acceptance probability of `finalQAdv`
* `prOutMRGen_toMR_toGen` — the embedding of a `QAdv` preserves the acceptance probability
* `prOutMRGen_resample_gentle_fiber_le` — the resampling bound `2 Q λ^(1/2)` for an adversary
  chosen by a random index, the set being sparse conditionally on the index as well
* `prForge_eq_prOut_forgeAdvAt`, `prForge_eq_prOutMRGen` — the winning probability of the
  EUF-CMA game as `prOut` of `forgeAdvAt` and as `prOutMRGen` of its embedding
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct CatCrypt.Core CatCrypt.Prob
  CatCrypt.Crypto.Signatures

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## The register with the query register saved in an ancilla -/

section Reg

variable (m n w : ℕ)

/-- The index of `(((x, y), z), a)` on the register with the ancilla `Fin m × Fin n` inside
    the work register: the oracle index of `((x, y), (z, a))`. -/
def finalRegIdx : ((Fin m × Fin n) × Fin w) × (Fin m × Fin n) ≃ Fin (m * n * (w * (m * n))) :=
  (Equiv.prodAssoc _ _ _).trans <|
    ((Equiv.refl _).prodCongr ((Equiv.refl (Fin w)).prodCongr (finProdEquiv m n))).trans <|
      ((Equiv.refl _).prodCongr (finProdEquiv w (m * n))).trans (oracleIndex m n (w * (m * n)))

variable {m n w}

/-- The unfolding equation of `finalRegIdx`. -/
theorem finalRegIdx_apply (t : (Fin m × Fin n) × Fin w) (a : Fin m × Fin n) :
    finalRegIdx m n w (t, a) =
      oracleIndex m n (w * (m * n)) (t.1, finProdEquiv w (m * n) (t.2, finProdEquiv m n a)) :=
  rfl

/-- The index `finalRegIdx` read through the ancilla equivalence `ancE` is the pair of the
    oracle index of the register and the ancilla index. -/
theorem ancE_symm_finalRegIdx (t : (Fin m × Fin n) × Fin w) (a : Fin m × Fin n) :
    (ancE m n w (m * n)).symm (finalRegIdx m n w (t, a)) =
      finProdEquiv (m * n * w) (m * n) (oracleIndex m n w t, finProdEquiv m n a) := by
  apply Fin.ext
  simp only [finalRegIdx_apply, ancE, oracleIndex, finProdEquiv, finCongr_symm, finCongr_apply,
    Fin.val_cast, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map,
    id_eq, finProdFinEquiv_apply_val]
  ring

/-- The entries of `kr` at the indices `finalRegIdx` are products of entries. -/
theorem kr_finalRegIdx_apply (A : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ)
    (B : Matrix (Fin (m * n)) (Fin (m * n)) ℂ) (t t' : (Fin m × Fin n) × Fin w)
    (a a' : Fin m × Fin n) :
    kr (ancE m n w (m * n)) A B (finalRegIdx m n w (t, a)) (finalRegIdx m n w (t', a')) =
      A (oracleIndex m n w t) (oracleIndex m n w t') *
        B (finProdEquiv m n a) (finProdEquiv m n a') := by
  simp only [kr, Matrix.submatrix_apply, ancE_symm_finalRegIdx, kronecker_apply,
    Equiv.symm_apply_apply]

/-- The oracle on the extended register acts on the indices `finalRegIdx` as on the query
    register. -/
theorem oraclePerm_finalRegIdx [NeZero n] (H : Fin m → Fin n) (x : Fin m) (y : Fin n)
    (z : Fin w) (a : Fin m × Fin n) :
    oraclePerm m n (w * (m * n)) H (finalRegIdx m n w (((x, y), z), a)) =
      finalRegIdx m n w (((x, y + H x), z), a) := by
  simp only [finalRegIdx_apply, oraclePerm_apply]

/-- The index of `(0, 0)` is `0`. -/
theorem finProdEquiv_zero_zero [NeZero m] [NeZero n] :
    finProdEquiv m n (0, 0) = 0 := by
  apply Fin.ext
  simp [finProdEquiv]

end Reg

/-! ## The adversary with the final query -/

section Final

variable {m n w q : ℕ} [NeZero m] [NeZero n]

/-- The permutation `(((x, y), z), (x₀, y₀)) ↦ (((x₀ + p k, y₀), z), (x, y))` with `k` the
    index of `((x, y), z)`: the query register moves into the ancilla and the point `p k` is
    added into the query register. -/
def finalPermAux (p : Fin (m * n * w) → Fin m) :
    Equiv.Perm (((Fin m × Fin n) × Fin w) × (Fin m × Fin n)) where
  toFun u := (((u.2.1 + p (oracleIndex m n w u.1), u.2.2), u.1.2), u.1.1)
  invFun v := (((v.2), v.1.2), (v.1.1.1 - p (oracleIndex m n w (v.2, v.1.2)), v.1.1.2))
  left_inv u := by simp
  right_inv v := by simp

/-- `finalPermAux p` on the register indices. -/
def finalPerm (p : Fin (m * n * w) → Fin m) : Equiv.Perm (Fin (m * n * (w * (m * n)))) :=
  (finalRegIdx m n w).permCongr (finalPermAux p)

omit [NeZero n] in
/-- `finalPerm p` acts on the register indices as `finalPermAux p` on the coordinates. -/
theorem finalPerm_finalRegIdx (p : Fin (m * n * w) → Fin m)
    (u : ((Fin m × Fin n) × Fin w) × (Fin m × Fin n)) :
    finalPerm p (finalRegIdx m n w u) = finalRegIdx m n w (finalPermAux p u) := by
  simp [finalPerm, Equiv.permCongr_apply]

/-- The predicate of the final projector of `finalQAdv`: `g k Y` for the value register `Y`
    and the index `k` of the register before the move, recovered from the ancilla and the
    work register. -/
def finalAcc (g : Fin (m * n * w) → Fin n → Bool) (j : Fin (m * n * (w * (m * n)))) : Bool :=
  let u := (finalRegIdx m n w).symm j
  g (oracleIndex m n w (u.2, u.1.2)) u.1.1.2

/-- The adversary `F` on the register with the ancilla `Fin m × Fin n` started at `(0, 0)`,
    followed by the permutation unitary of `finalPerm p` and one more query, with the final
    projector onto `finalAcc g`. It has `q + 1` queries; its last query writes `H (p k)` into
    the value register. -/
def finalQAdv (F : QAdv m n w q) (p : Fin (m * n * w) → Fin m)
    (g : Fin (m * n * w) → Fin n → Bool) : QAdv m n (w * (m * n)) (q + 1) where
  U := Fin.snoc (postU (permUnitary (finalPerm p)) (liftU (ancE m n w (m * n)) ∘ F.U)) 1
  init := liftInit F.init
  final := diagB (finalAcc g)
  final_conjTranspose := diagB_conjTranspose _
  final_mul_self := diagB_mul_self _

/-- The run operator of `finalQAdv F p g` is the permutation unitary of the oracle after
    `finalPerm p`, after the lifted run operator of `F`. -/
theorem runOp_finalQAdv (F : QAdv m n w q) (p : Fin (m * n * w) → Fin m)
    (g : Fin (m * n * w) → Fin n → Bool) (H : Fin m → Fin n) :
    runOp (finalQAdv F p g) H =
      (permUnitary (oraclePerm m n (w * (m * n)) H * finalPerm p) : Matrix _ _ ℂ) *
        kr (ancE m n w (m * n)) (runOp F H) 1 := by
  have h1 : chainOp (oracleU m n (w * (m * n)) H : Matrix _ _ ℂ) q
      (liftU (ancE m n w (m * n)) ∘ F.U) = kr (ancE m n w (m * n)) (runOp F H) 1 := by
    rw [oracleU_lift]
    exact chainOp_liftU _ _ q F.U
  change chainOp (oracleU m n (w * (m * n)) H : Matrix _ _ ℂ) (q + 1)
    (Fin.snoc (postU (permUnitary (finalPerm p)) (liftU (ancE m n w (m * n)) ∘ F.U)) 1) = _
  rw [chainOp_snoc, OneMemClass.coe_one, Matrix.one_mul, chainOp_postU, h1,
    oracleU_eq_permUnitary, ← Matrix.mul_assoc, ← Submonoid.coe_mul, permUnitary_mul]

/-- A final test `g k (H (p k))` that reads the oracle at the point `p k` of the final basis
    state has the acceptance probability of `finalQAdv F p g`, whose final projector does not
    depend on the oracle and whose last query computes `H (p k)`. -/
theorem prOut_withFinalB_eq_prOut_finalQAdv (F : QAdv m n w q) (p : Fin (m * n * w) → Fin m)
    (g : Fin (m * n * w) → Fin n → Bool) (H : Fin m → Fin n) :
    prOut (F.withFinalB fun k => g k (H (p k))) H = prOut (finalQAdv F p g) H := by
  set N := runOp F H * F.init.val * (runOp F H)ᴴ with hN
  set M := runOp (finalQAdv F p g) H * (finalQAdv F p g).init.val *
    (runOp (finalQAdv F p g) H)ᴴ with hMdef
  have hL : prOut (F.withFinalB fun k => g k (H (p k))) H =
      ENNReal.ofReal (∑ k, if g k (H (p k)) then (N k k).re else 0) := by
    unfold prOut prTrue_Q
    rw [run_branch_true]
    have hc : (F.withFinalB fun k => g k (H (p k))).final *
        runOp (F.withFinalB fun k => g k (H (p k))) H *
        (F.withFinalB fun k => g k (H (p k))).init.val *
        ((F.withFinalB fun k => g k (H (p k))).final *
          runOp (F.withFinalB fun k => g k (H (p k))) H)ᴴ =
        diagB (fun k => g k (H (p k))) * N * (diagB fun k => g k (H (p k)))ᴴ := by
      simp only [hN, QAdv.withFinalB, runOp, conjTranspose_mul, Matrix.mul_assoc]
    rw [hc, trace_diagB_conj, Complex.re_sum]
    refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
    split_ifs <;> simp
  have hR : prOut (finalQAdv F p g) H =
      ENNReal.ofReal (∑ j, if finalAcc g j then (M j j).re else 0) := by
    unfold prOut prTrue_Q
    rw [run_branch_true]
    have hc : (finalQAdv F p g).final * runOp (finalQAdv F p g) H *
        (finalQAdv F p g).init.val * ((finalQAdv F p g).final * runOp (finalQAdv F p g) H)ᴴ =
        diagB (finalAcc g) * M * (diagB (finalAcc g))ᴴ := by
      simp only [hMdef, conjTranspose_mul, Matrix.mul_assoc]
      rfl
    rw [hc, trace_diagB_conj, Complex.re_sum]
    refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
    split_ifs <;> simp
  set σ := oraclePerm m n (w * (m * n)) H * finalPerm p with hσ
  have hM : ∀ j, M j j = kr (ancE m n w (m * n)) N (ancProj 0) (σ.symm j) (σ.symm j) := by
    have hkr : kr (ancE m n w (m * n)) (runOp F H) 1 *
        kr (ancE m n w (m * n)) F.init.val (ancProj 0) *
        (kr (ancE m n w (m * n)) (runOp F H) 1)ᴴ = kr (ancE m n w (m * n)) N (ancProj 0) := by
      rw [kr_conjTranspose, conjTranspose_one, kr_mul, kr_mul, one_mul, mul_one]
    have hMe : M = (kr (ancE m n w (m * n)) N (ancProj 0)).submatrix σ.symm σ.symm := by
      rw [hMdef, runOp_finalQAdv, ← permUnitary_conj, ← hkr]
      change _ * kr (ancE m n w (m * n)) F.init.val (ancProj 0) * _ = _
      simp only [conjTranspose_mul, Matrix.mul_assoc, hσ]
    intro j
    rw [hMe, Matrix.submatrix_apply]
  rw [hL, hR]
  congr 1
  simp_rw [hM]
  rw [← Equiv.sum_comp σ]
  simp only [Equiv.symm_apply_apply]
  rw [← (finalRegIdx m n w).sum_comp, Fintype.sum_prod_type, ← (oracleIndex m n w).sum_comp]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_eq_single (0, 0)]
  · obtain ⟨⟨x, y⟩, z⟩ := t
    simp [hσ, finalPerm_finalRegIdx, finalPermAux, oraclePerm_finalRegIdx, finalAcc,
      kr_finalRegIdx_apply, ancProj, finProdEquiv_zero_zero]
  · intro a _ ha
    have hne : finProdEquiv m n a ≠ 0 := by
      rw [← finProdEquiv_zero_zero]
      exact fun h => ha ((finProdEquiv m n).injective h)
    simp [kr_finalRegIdx_apply, ancProj, hne]
  · simp

end Final

/-! ## Adversaries without rounds -/

section NoRounds

variable {m n w q c a : ℕ}

/-- The adversary `B` as a multi-round adversary without rounds: one segment, the unitaries
    of `B`. -/
def QAdv.toMR (B : QAdv m n w q) : QAdvMR m n w q 0 c a where
  seg _ := B.U
  rounds j := j.elim0
  init := B.init
  final := B.final
  final_conjTranspose := B.final_conjTranspose
  final_mul_self := B.final_mul_self

variable [NeZero n]

/-- The general multi-round adversary of `B` has the acceptance probability of `B`. -/
theorem prOutMRGen_toMR_toGen (B : QAdv m n w q) (H : Fin m → Fin n) (f : Fin c → Fin a) :
    prOutMRGen (B.toMR (c := c) (a := a)).toGen H f = prOut B H := by
  rw [prOutMRGen_toGen]
  rfl

end NoRounds

/-! ## Resampling the oracle for an adversary chosen by a random index -/

section Fiber

variable {m n w q k c a : ℕ} [NeZero n] [NeZero c]

/-- Resampling the oracle on a set conditionally sparse given the second oracle, the round
function and the index of the adversary: the adversary `B (κ ω)` depends on `ω` through the
index `κ ω`, and for every index `j`, point `x`, oracle `h` and round function `g` the event
`κ ω = j ∧ H₂ ω = h ∧ f ω = g ∧ x ∈ D ω` has weight at most `λ` times that of
`κ ω = j ∧ H₂ ω = h ∧ f ω = g`. Then the averaged acceptance probabilities differ by at most
`2 Q λ^(1/2)` with `Q = flatQ q k q`. -/
theorem prOutMRGen_resample_gentle_fiber_le {Ω K : Type} [Fintype Ω] [Finite K]
    [DecidableEq K] (B : K → QAdvMRGen m n w q k c a) (κ : Ω → K) (μ : Ω → ℝ≥0∞)
    (hμ : ∑ ω, μ ω = 1) (H₁ H₂ : Ω → Fin m → Fin n) (f : Ω → Fin c → Fin a)
    (D : Ω → Finset (Fin m)) (lam : ℝ≥0∞) (hagree : ∀ ω x, x ∉ D ω → H₁ ω x = H₂ ω x)
    (hsparse : ∀ j x h g,
      ∑ ω, μ ω * (if κ ω = j ∧ H₂ ω = h ∧ f ω = g ∧ x ∈ D ω then 1 else 0) ≤
        lam * ∑ ω, μ ω * (if κ ω = j ∧ H₂ ω = h ∧ f ω = g then 1 else 0)) :
    absDiff (∑ ω, μ ω * prOutMRGen (B (κ ω)) (H₁ ω) (f ω))
        (∑ ω, μ ω * prOutMRGen (B (κ ω)) (H₂ ω) (f ω)) ≤
      2 * (flatQ q k q : ℝ≥0∞) * lam ^ (1 / 2 : ℝ) := by
  have := Fintype.ofFinite K
  set C := 2 * (flatQ q k q : ℝ≥0∞) * lam ^ (1 / 2 : ℝ) with hC
  set M : K → ℝ≥0∞ := fun j => ∑ ω, μ ω * (if κ ω = j then 1 else 0) with hM
  have hsplit : ∀ F : Ω → ℝ≥0∞, ∑ ω, μ ω * F ω =
      ∑ j, ∑ ω, μ ω * (if κ ω = j then 1 else 0) * F ω := by
    intro F
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ω _ => ?_
    simp [Finset.sum_ite_eq]
  have hMsum : ∑ j, M j = 1 := by
    have := hsplit fun _ => 1
    simp only [mul_one] at this
    rw [← hμ, this]
  have hfib : ∀ (j : K) (G : Ω → Fin m → Fin n),
      ∑ ω, μ ω * (if κ ω = j then 1 else 0) * prOutMRGen (B (κ ω)) (G ω) (f ω) =
        ∑ ω, μ ω * (if κ ω = j then 1 else 0) * prOutMRGen (B j) (G ω) (f ω) := by
    intro j G
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases h : κ ω = j
    · rw [h]
    · simp [h]
  have hstep : ∀ j, absDiff
      (∑ ω, μ ω * (if κ ω = j then 1 else 0) * prOutMRGen (B j) (H₁ ω) (f ω))
      (∑ ω, μ ω * (if κ ω = j then 1 else 0) * prOutMRGen (B j) (H₂ ω) (f ω)) ≤ M j * C := by
    intro j
    by_cases hM0 : M j = 0
    · have hz : ∀ ω, μ ω * (if κ ω = j then 1 else 0) = 0 := fun ω =>
        (Finset.sum_eq_zero_iff.mp hM0) ω (Finset.mem_univ _)
      simp only [hz, zero_mul, Finset.sum_const_zero]
      rw [absDiff_self]
      exact zero_le
    have hMle : M j ≤ 1 := by
      rw [← hμ]
      refine Finset.sum_le_sum fun ω _ => ?_
      split_ifs <;> simp
    have hMtop : M j ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hMle
    set ν : Ω → ℝ≥0∞ := fun ω => μ ω * (if κ ω = j then 1 else 0) * (M j)⁻¹ with hν
    have hνsum : ∑ ω, ν ω = 1 := by
      rw [hν, ← Finset.sum_mul]
      exact ENNReal.mul_inv_cancel hM0 hMtop
    have hνP : ∀ (P : Ω → Prop) [DecidablePred P],
        ∑ ω, ν ω * (if P ω then 1 else 0) =
          (M j)⁻¹ * ∑ ω, μ ω * (if κ ω = j ∧ P ω then 1 else 0) := by
      intro P _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ω _ => ?_
      simp only [hν]
      split_ifs <;> simp_all [mul_comm]
    have hsp : ∀ x h g, ∑ ω, ν ω * (if H₂ ω = h ∧ f ω = g ∧ x ∈ D ω then 1 else 0) ≤
        lam * ∑ ω, ν ω * (if H₂ ω = h ∧ f ω = g then 1 else 0) := by
      intro x h g
      rw [hνP, hνP, mul_left_comm]
      gcongr
      exact hsparse j x h g
    have key := prOutMRGen_resample_gentle_le (B j) ν hνsum H₁ H₂ f D lam hagree hsp
    have hX : ∀ G : Ω → Fin m → Fin n,
        ∑ ω, μ ω * (if κ ω = j then 1 else 0) * prOutMRGen (B j) (G ω) (f ω) =
          M j * ∑ ω, ν ω * prOutMRGen (B j) (G ω) (f ω) := by
      intro G
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ω _ => ?_
      simp only [hν]
      rw [← mul_assoc, ← mul_assoc, mul_comm (M j), mul_assoc (μ ω * _),
        ENNReal.mul_inv_cancel hM0 hMtop, mul_one]
    rw [hX, hX]
    exact (absDiff_mul_left_le _ _ _).trans (by gcongr)
  calc absDiff (∑ ω, μ ω * prOutMRGen (B (κ ω)) (H₁ ω) (f ω))
        (∑ ω, μ ω * prOutMRGen (B (κ ω)) (H₂ ω) (f ω))
      = absDiff (∑ j, ∑ ω, μ ω * (if κ ω = j then 1 else 0) * prOutMRGen (B j) (H₁ ω) (f ω))
          (∑ j, ∑ ω, μ ω * (if κ ω = j then 1 else 0) * prOutMRGen (B j) (H₂ ω) (f ω)) := by
        rw [hsplit, hsplit]
        simp only [hfib]
    _ ≤ ∑ j, M j * C := (absDiff_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hstep j)
    _ = C := by rw [← Finset.sum_mul, hMsum, one_mul]

end Fiber

/-! ## The forgery test of the EUF-CMA game -/

section Forge

variable {m n w q k c a T : ℕ} {Msg PK SK Sig X Y : Type} [NeZero m] [NeZero n] [NeZero c]

/-- The adversary of the forgery test at the public key `pk` and the round table `f`: the
    flattened run of `A` at `f`, followed by the move of its query register into an ancilla
    and one query at the verification point of its forgery, with the projector onto the basis
    states that pass the forgery test. It has `flatQ q k q + 1` queries. -/
def forgeAdvAt [DecidableEq Msg] (S : QROMSig Msg PK SK Sig X Y) (eX : X ≃ Fin m)
    (eY : Y ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c) (A : QSigAdv m n w q k c a T Msg PK Sig)
    (pk : PK) (f : Fin c → Fin a) :
    QAdv m n (ancW c k w * (m * n)) (flatQ q k q + 1) :=
  finalQAdv (toQAdv (A.run pk) f) (forgePoint S eX A pk) (forgeTest S eY eQ A pk)

/-- The winning probability of the EUF-CMA game is the acceptance probability of the
    adversary of the forgery test at the signing table. -/
theorem prForge_eq_prOut_forgeAdvAt [DecidableEq Msg] (S : QROMSig Msg PK SK Sig X Y)
    (eX : X ≃ Fin m) (eY : Y ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c) (eA : Option Sig ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK Sig) (ks : PK × SK) (H : Fin m → Fin n)
    (R : Msg × Fin T → S.Coins) :
    prForge S eX eY eQ eA A ks H R =
      prOut (forgeAdvAt S eX eY eQ A ks.1 (signTab S eQ eA ks.2 (hashOf eX eY H) R)) H :=
  prOut_withFinalB_eq_prOut_finalQAdv _ (forgePoint S eX A ks.1) (forgeTest S eY eQ A ks.1) H

/-- The winning probability of the EUF-CMA game is `prOutMRGen` at the oracle `H` of a
    general multi-round adversary with `flatQ q k q + 1` queries and no rounds, at any round
    function `f'`: the embedding of the adversary of the forgery test at the signing table. -/
theorem prForge_eq_prOutMRGen [DecidableEq Msg] {c' a' : ℕ} (S : QROMSig Msg PK SK Sig X Y)
    (eX : X ≃ Fin m) (eY : Y ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c) (eA : Option Sig ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK Sig) (ks : PK × SK) (H : Fin m → Fin n)
    (R : Msg × Fin T → S.Coins) (f' : Fin c' → Fin a') :
    prForge S eX eY eQ eA A ks H R =
      prOutMRGen ((forgeAdvAt S eX eY eQ A ks.1
        (signTab S eQ eA ks.2 (hashOf eX eY H) R)).toMR (c := c') (a := a')).toGen H f' := by
  rw [prOutMRGen_toMR_toGen, prForge_eq_prOut_forgeAdvAt]

end Forge

end CatCrypt.Quantum.QROM
